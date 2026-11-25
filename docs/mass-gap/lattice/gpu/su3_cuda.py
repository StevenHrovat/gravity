"""Fused CUDA kernels (compiled at run time by cupy / NVRTC) for pure-gauge SU(N) lattice gauge theory, N = 2 or 3.
Array layout: (B, Nx, Ny, Nz, Nt, N, N) complex128 for each of the four link directions; mu = 0,1,2 space, 3 = time.
"""
import numpy as np
import cupy as cp

SRC = r'''
#include <cupy/complex.cuh>
#ifndef REAL
#define REAL double
#endif
typedef complex<REAL> cd;
#define NN (NC*NC)

__device__ __forceinline__ int wrapi(int v, int n){ v %= n; if (v < 0) v += n; return v; }
__device__ __forceinline__ long lin(int b, int x, int y, int z, int t, int Nx, int Ny, int Nz, int Nt){
    return ((((long)b * Nx + x) * Ny + y) * Nz + z) * Nt + t;
}
// site index of c + delta (periodic)
__device__ __forceinline__ long nbd(int b, const int* c, const int* d, int Nx, int Ny, int Nz, int Nt){
    return lin(b, wrapi(c[0] + d[0], Nx), wrapi(c[1] + d[1], Ny), wrapi(c[2] + d[2], Nz), wrapi(c[3] + d[3], Nt), Nx, Ny, Nz, Nt);
}
__device__ __forceinline__ void ldm(const cd* p, int dg, cd* m){
    if (!dg) { for (int i = 0; i < NN; i++) m[i] = p[i]; }
    else { for (int i = 0; i < NC; i++) for (int j = 0; j < NC; j++) m[NC * i + j] = conj(p[NC * j + i]); }
}
__device__ __forceinline__ void mmul(const cd* A, const cd* B, cd* C){
    for (int i = 0; i < NC; i++) for (int j = 0; j < NC; j++) {
        cd s(0.0, 0.0);
        for (int k = 0; k < NC; k++) s += A[NC * i + k] * B[NC * k + j];
        C[NC * i + j] = s;
    }
}
__device__ __forceinline__ double rnd(unsigned long long* st){
    unsigned long long x = *st;
    x ^= x >> 12; x ^= x << 25; x ^= x >> 27; *st = x;
    unsigned long long r = x * 2685821657736338717ULL;
    return ((double)(r >> 11) + 0.5) * (1.0 / 9007199254740992.0);
}
__device__ double kp_x0(double alpha, unsigned long long* st){
    if (alpha < 0.3) {
        for (int it = 0; it < 100000; it++) {
            double xs = 2.0 * rnd(st) - 1.0, rr = rnd(st);
            if (rr <= sqrt(fmax(1.0 - xs * xs, 0.0)) * exp(alpha * (xs - 1.0))) return xs;
        }
        return 1.0;
    }
    for (int it = 0; it < 100000; it++) {
        double r1 = rnd(st), r2 = rnd(st), r3 = rnd(st), r4 = rnd(st);
        double x = -log(r1) / alpha, y = -log(r2) / alpha;
        double c = cos(6.283185307179586 * r3); c *= c;
        double delta = x + y * c;
        if (r4 * r4 <= 1.0 - delta / 2.0) return 1.0 - delta;
    }
    return 1.0;
}
__device__ __forceinline__ void qmul(const double* p, const double* q, double* o){
    o[0] = p[0]*q[0] - p[1]*q[1] - p[2]*q[2] - p[3]*q[3];
    o[1] = p[0]*q[1] + q[0]*p[1] - (p[2]*q[3] - p[3]*q[2]);
    o[2] = p[0]*q[2] + q[0]*p[2] - (p[3]*q[1] - p[1]*q[3]);
    o[3] = p[0]*q[3] + q[0]*p[3] - (p[1]*q[2] - p[2]*q[1]);
}
__device__ __forceinline__ void applyR(cd* M, int i, int j, const double* r){
    cd a(r[0], r[3]), b(r[2], r[1]), c(-r[2], r[1]), d(r[0], -r[3]);
    for (int k = 0; k < NC; k++) {
        cd mi = M[NC * i + k], mj = M[NC * j + k];
        M[NC * i + k] = a * mi + b * mj;
        M[NC * j + k] = c * mi + d * mj;
    }
}
// staple sum for link (c, mu); nmask selects the allowed transverse directions
__device__ void staple_dev(cd* const* Us, int b, const int* c, int mu, int nmask, int Nx, int Ny, int Nz, int Nt, cd* V){
    for (int k = 0; k < NN; k++) V[k] = cd(0.0, 0.0);
    cd A[NN], Bm[NN], C[NN], T1[NN], T2[NN];
    for (int nu = 0; nu < 4; nu++) {
        if (nu == mu || !((nmask >> nu) & 1)) continue;
        int d0[4] = {0,0,0,0}, dmu[4] = {0,0,0,0}, dnu[4] = {0,0,0,0}, dmn[4] = {0,0,0,0}, dn[4] = {0,0,0,0};
        dmu[mu] = 1; dnu[nu] = 1; dmn[mu] = 1; dmn[nu] = -1; dn[nu] = -1;
        long i0 = nbd(b, c, d0, Nx, Ny, Nz, Nt), imu = nbd(b, c, dmu, Nx, Ny, Nz, Nt), inu = nbd(b, c, dnu, Nx, Ny, Nz, Nt);
        long imn = nbd(b, c, dmn, Nx, Ny, Nz, Nt), in_ = nbd(b, c, dn, Nx, Ny, Nz, Nt);
        ldm(Us[nu] + imu * NN, 0, A); ldm(Us[mu] + inu * NN, 1, Bm); ldm(Us[nu] + i0 * NN, 1, C);
        mmul(A, Bm, T1); mmul(T1, C, T2);
        for (int k = 0; k < NN; k++) V[k] += T2[k];
        ldm(Us[nu] + imn * NN, 1, A); ldm(Us[mu] + in_ * NN, 1, Bm); ldm(Us[nu] + in_ * NN, 0, C);
        mmul(A, Bm, T1); mmul(T1, C, T2);
        for (int k = 0; k < NN; k++) V[k] += T2[k];
    }
}

extern "C" __global__ void upd(cd* U0, cd* U1, cd* U2, cd* U3, unsigned long long* state, const double* beta,
                               int mu, int parity, int mode, int B, int Nx, int Ny, int Nz, int Nt)
{
    long s = (long)blockIdx.x * blockDim.x + threadIdx.x;
    long vol = (long)Nx * Ny * Nz * Nt;
    if (s >= (long)B * vol) return;
    int b = (int)(s / vol); long r = s % vol;
    int t = r % Nt; r /= Nt; int z = r % Nz; r /= Nz; int y = r % Ny; int x = (int)(r / Ny);
    if (((x + y + z + t) & 1) != parity) return;
    int c[4] = {x, y, z, t};
    cd* Us[4] = {U0, U1, U2, U3};
    cd V[NN], W[NN], Ul[NN];
    staple_dev((cd* const*)Us, b, c, mu, 15, Nx, Ny, Nz, Nt, V);
    cd* Up = Us[mu] + s * NN;
    for (int k = 0; k < NN; k++) Ul[k] = Up[k];
    mmul(Ul, V, W);
    unsigned long long st = state[s];
    double bt = beta[b];
#if NC == 3
    const int ni = 3; const int pi_[3] = {0, 0, 1}; const int pj_[3] = {1, 2, 2};
#else
    const int ni = 1; const int pi_[1] = {0}; const int pj_[1] = {1};
#endif
    for (int sg = 0; sg < ni; sg++) {
        int i = pi_[sg], j = pj_[sg];
        cd A = W[NC * i + i], Bc = W[NC * i + j], Cc = W[NC * j + i], D = W[NC * j + j];
        double a0 = 0.5 * (A.real() + D.real()), a3 = 0.5 * (A.imag() - D.imag());
        double a2 = 0.5 * (Bc.real() - Cc.real()), a1 = 0.5 * (Bc.imag() + Cc.imag());
        double k = sqrt(a0*a0 + a1*a1 + a2*a2 + a3*a3);
        double kk = fmax(k, 1e-300);
        double ud[4] = {a0 / kk, -a1 / kk, -a2 / kk, -a3 / kk};
        double R[4];
        if (mode == 0) {
            double alpha = (2.0 / NC) * bt * k;
            double x0 = kp_x0(alpha, &st);
            double rs = sqrt(fmax(1.0 - x0 * x0, 0.0));
            double ct = 2.0 * rnd(&st) - 1.0, ph = 6.283185307179586 * rnd(&st);
            double sn = sqrt(fmax(1.0 - ct * ct, 0.0));
            double X[4] = {x0, rs * sn * cos(ph), rs * sn * sin(ph), rs * ct};
            qmul(X, ud, R);
        } else {
            qmul(ud, ud, R);
        }
        applyR(Ul, i, j, R);
        applyR(W, i, j, R);
    }
    state[s] = st;
    for (int k = 0; k < NN; k++) Up[k] = Ul[k];
}

extern "C" __global__ void reunit(cd* M, long n)
{
    long s = (long)blockIdx.x * blockDim.x + threadIdx.x;
    if (s >= n) return;
    cd* m = M + s * NN;
    double nr = 0.0;
    for (int k = 0; k < NC; k++) nr += norm(m[k]);
    nr = 1.0 / sqrt(nr);
    for (int k = 0; k < NC; k++) m[k] *= (REAL)nr;
#if NC == 2
    m[2] = -conj(m[1]); m[3] = conj(m[0]);
#else
    cd d(0.0, 0.0);
    for (int k = 0; k < 3; k++) d += conj(m[k]) * m[3 + k];
    for (int k = 0; k < 3; k++) m[3 + k] -= d * m[k];
    nr = 0.0;
    for (int k = 0; k < 3; k++) nr += norm(m[3 + k]);
    nr = 1.0 / sqrt(nr);
    for (int k = 0; k < 3; k++) m[3 + k] *= (REAL)nr;
    m[6] = conj(m[1] * m[5] - m[2] * m[4]);
    m[7] = conj(m[2] * m[3] - m[0] * m[5]);
    m[8] = conj(m[0] * m[4] - m[1] * m[3]);
#endif
}

// sum over selected planes of Re Tr(plaquette)/NC, per site.  pmask bit k: planes (0,1),(0,2),(0,3),(1,2),(1,3),(2,3)
extern "C" __global__ void plaq(const cd* U0, const cd* U1, const cd* U2, const cd* U3, double* out, int pmask, int B, int Nx, int Ny, int Nz, int Nt)
{
    long s = (long)blockIdx.x * blockDim.x + threadIdx.x;
    long vol = (long)Nx * Ny * Nz * Nt;
    if (s >= (long)B * vol) return;
    int b = (int)(s / vol); long r = s % vol;
    int t = r % Nt; r /= Nt; int z = r % Nz; r /= Nz; int y = r % Ny; int x = (int)(r / Ny);
    int c[4] = {x, y, z, t};
    const cd* Us[4] = {U0, U1, U2, U3};
    double tot = 0.0; int bit = 0;
    cd A[NN], Bm[NN], C[NN], D[NN], T1[NN], T2[NN];
    for (int mu = 0; mu < 4; mu++) for (int nu = mu + 1; nu < 4; nu++, bit++) {
        if (!((pmask >> bit) & 1)) continue;
        int d0[4] = {0,0,0,0}, dmu[4] = {0,0,0,0}, dnu[4] = {0,0,0,0};
        dmu[mu] = 1; dnu[nu] = 1;
        long i0 = s, imu = nbd(b, c, dmu, Nx, Ny, Nz, Nt), inu = nbd(b, c, dnu, Nx, Ny, Nz, Nt);
        ldm(Us[mu] + i0 * NN, 0, A); ldm(Us[nu] + imu * NN, 0, Bm); ldm(Us[mu] + inu * NN, 1, C); ldm(Us[nu] + i0 * NN, 1, D);
        mmul(A, Bm, T1); mmul(C, D, T2); mmul(T1, T2, A);
        for (int k = 0; k < NC; k++) tot += A[NC * k + k].real();
    }
    out[s] = tot / NC;
}

extern "C" __global__ void polyakov(const cd* U3, cd* out, int B, int Nx, int Ny, int Nz, int Nt)
{
    long s = (long)blockIdx.x * blockDim.x + threadIdx.x;
    long vs = (long)Nx * Ny * Nz;
    if (s >= (long)B * vs) return;
    int b = (int)(s / vs); long r = s % vs;
    int z = r % Nz; r /= Nz; int y = r % Ny; int x = (int)(r / Ny);
    cd P[NN], L[NN], T[NN];
    for (int i = 0; i < NN; i++) P[i] = cd((i % (NC + 1) == 0) ? 1.0 : 0.0, 0.0);
    for (int t = 0; t < Nt; t++) {
        long i0 = lin(b, x, y, z, t, Nx, Ny, Nz, Nt);
        ldm(U3 + i0 * NN, 0, L); mmul(P, L, T);
        for (int i = 0; i < NN; i++) P[i] = T[i];
    }
    cd tr(0.0, 0.0);
    for (int k = 0; k < NC; k++) tr += P[NC * k + k];
    out[s] = tr / (REAL)NC;
}

// APE smearing of the three spatial links (spatial staples only), polar projection back to SU(3)
extern "C" __global__ void ape(const cd* U0, const cd* U1, const cd* U2, cd* O0, cd* O1, cd* O2, double alpha, int niter, int B, int Nx, int Ny, int Nz, int Nt)
{
    long s = (long)blockIdx.x * blockDim.x + threadIdx.x;
    long vol = (long)Nx * Ny * Nz * Nt;
    if (s >= (long)B * vol) return;
    int b = (int)(s / vol); long r = s % vol;
    int t = r % Nt; r /= Nt; int z = r % Nz; r /= Nz; int y = r % Ny; int x = (int)(r / Ny);
    int c[4] = {x, y, z, t};
    cd* Us[4] = {(cd*)U0, (cd*)U1, (cd*)U2, (cd*)U2};
    cd* Os[3] = {O0, O1, O2};
    cd V[NN], M[NN], X[NN], Y[NN], Z[NN];
    for (int mu = 0; mu < 3; mu++) {
        staple_dev((cd* const*)Us, b, c, mu, 7, Nx, Ny, Nz, Nt, V);
        ldm(V, 1, Y);                       // staple from x to x+mu (Hermitian conjugate of the heat-bath staple)
        const cd* Ul = Us[mu] + s * NN;
        double sc = 0.0;
        for (int k = 0; k < NN; k++) { M[k] = (REAL)(1.0 - alpha) * Ul[k] + (REAL)(alpha / 4.0) * Y[k]; sc += norm(M[k]); }
        sc = sqrt(sc / NC);
        for (int k = 0; k < NN; k++) X[k] = M[k] / (REAL)sc;
        for (int it = 0; it < niter; it++) {
            // X <- X (3 - X^dag X)/2
            ldm(X, 1, Y); mmul(Y, X, Z);
            for (int k = 0; k < NN; k++) Z[k] = ((k % (NC + 1) == 0) ? cd(3.0, 0.0) : cd(0.0, 0.0)) - Z[k];
            mmul(X, Z, Y);
            for (int k = 0; k < NN; k++) X[k] = (REAL)0.5 * Y[k];
        }
#if NC == 3
        cd det = X[0] * (X[4] * X[8] - X[5] * X[7]) - X[1] * (X[3] * X[8] - X[5] * X[6]) + X[2] * (X[3] * X[7] - X[4] * X[6]);
        double ph = -atan2(det.imag(), det.real()) / 3.0;
        cd f(cos(ph), sin(ph));
        for (int k = 0; k < NN; k++) X[k] *= f;
#endif
        cd* Ou = Os[mu] + s * NN;
        for (int k = 0; k < NN; k++) Ou[k] = X[k];
    }
}

// C[x] = A[x] * op(Bm[x + dist*e_dir])
extern "C" __global__ void mshift(const cd* A, const cd* Bm, cd* C, int dir, int dist, int dagB, int B, int Nx, int Ny, int Nz, int Nt)
{
    long s = (long)blockIdx.x * blockDim.x + threadIdx.x;
    long vol = (long)Nx * Ny * Nz * Nt;
    if (s >= (long)B * vol) return;
    int b = (int)(s / vol); long r = s % vol;
    int t = r % Nt; r /= Nt; int z = r % Nz; r /= Nz; int y = r % Ny; int x = (int)(r / Ny);
    int c[4] = {x, y, z, t}; int d[4] = {0,0,0,0}; d[dir] = dist;
    long j = nbd(b, c, d, Nx, Ny, Nz, Nt);
    cd P[NN], Q[NN], R[NN];
    ldm(A + s * NN, 0, P); ldm(Bm + j * NN, dagB, Q); mmul(P, Q, R);
    for (int k = 0; k < NN; k++) C[s * NN + k] = R[k];
}

// out[x] = Re Tr[ P[x] T[x + r e_i] ( T[x] P[x + t e_3] )^dag ] / NC
extern "C" __global__ void wloop(const cd* P, const cd* T, double* out, int i, int rr, int tt, int B, int Nx, int Ny, int Nz, int Nt)
{
    long s = (long)blockIdx.x * blockDim.x + threadIdx.x;
    long vol = (long)Nx * Ny * Nz * Nt;
    if (s >= (long)B * vol) return;
    int b = (int)(s / vol); long r = s % vol;
    int t = r % Nt; r /= Nt; int z = r % Nz; r /= Nz; int y = r % Ny; int x = (int)(r / Ny);
    int c[4] = {x, y, z, t}; int d1[4] = {0,0,0,0}, d2[4] = {0,0,0,0}; d1[i] = rr; d2[3] = tt;
    long j1 = nbd(b, c, d1, Nx, Ny, Nz, Nt), j2 = nbd(b, c, d2, Nx, Ny, Nz, Nt);
    cd A[NN], Bm[NN], X[NN], Y[NN];
    ldm(P + s * NN, 0, A); ldm(T + j1 * NN, 0, Bm); mmul(A, Bm, X);
    ldm(T + s * NN, 0, A); ldm(P + j2 * NN, 0, Bm); mmul(A, Bm, Y);
    double tot = 0.0;
    for (int k = 0; k < NN; k++) tot += (X[k] * conj(Y[k])).real();
    out[s] = tot / NC;
}
'''

_mods = {}


def module(nc, single=False):
    key = (nc, single)
    if key not in _mods:
        _mods[key] = cp.RawModule(code=SRC, options=("-DNC=%d" % nc, "-DREAL=%s" % ("float" if single else "double"), "--std=c++17"))
    return _mods[key]


def _grid(n, bs=128):
    return ((int(n) + bs - 1) // bs,), (bs,)
