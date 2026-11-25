"""Fused GPU update for W2 (amendment A6): one CUDA kernel per colour-class update, SU(2) only.

The kernel does, per (pair, link of the class), exactly what PairSampler.update_class does in array code (constrained.py):
Wilson staples, the constraint fields with the normaliser linearised at the current state, the maximal coupling of the two
proposals, the full Metropolis-Hastings ratio with a shared uniform, and the write-back. Each thread handles both chains of
one pair for one link. Random numbers: a counter-based generator (splitmix64 of seed, launch counter, thread index), so the
stream differs from the reference path's; agreement with the reference is statistical for the sampled parts and to rounding
for the deterministic parts (the `debug` mode returns the proposal and target fields for comparison).

Bessel functions: I0, I1 (exponentially scaled) by the power series for a < 17 and the asymptotic series above, accurate to
about 1e-13 relative (checked against scipy in fused_selftest).
"""

import math
import time

import numpy as np

import constrained as C

KERNEL = r'''
struct q4 { double a, b, c, d; };

__device__ __forceinline__ q4 qm(const q4 x, const q4 y) {
    q4 r;
    r.a = x.a*y.a - x.b*y.b - x.c*y.c - x.d*y.d;
    r.b = x.a*y.b + y.a*x.b - (x.c*y.d - x.d*y.c);
    r.c = x.a*y.c + y.a*x.c - (x.d*y.b - x.b*y.d);
    r.d = x.a*y.d + y.a*x.d - (x.b*y.c - x.c*y.b);
    return r;
}
__device__ __forceinline__ q4 qcj(const q4 x) { q4 r; r.a = x.a; r.b = -x.b; r.c = -x.c; r.d = -x.d; return r; }
__device__ __forceinline__ q4 qadd(const q4 x, const q4 y) { q4 r; r.a = x.a+y.a; r.b = x.b+y.b; r.c = x.c+y.c; r.d = x.d+y.d; return r; }
__device__ __forceinline__ q4 qsub(const q4 x, const q4 y) { q4 r; r.a = x.a-y.a; r.b = x.b-y.b; r.c = x.c-y.c; r.d = x.d-y.d; return r; }
__device__ __forceinline__ q4 qsc(const q4 x, double s) { q4 r; r.a = s*x.a; r.b = s*x.b; r.c = s*x.c; r.d = s*x.d; return r; }
__device__ __forceinline__ double qdot(const q4 x, const q4 y) { return x.a*y.a + x.b*y.b + x.c*y.c + x.d*y.d; }
__device__ __forceinline__ double qnorm(const q4 x) { return sqrt(qdot(x, x)); }
__device__ __forceinline__ q4 qzero() { q4 r; r.a = 0; r.b = 0; r.c = 0; r.d = 0; return r; }
__device__ __forceinline__ q4 qone() { q4 r; r.a = 1; r.b = 0; r.c = 0; r.d = 0; return r; }

__device__ __forceinline__ q4 ld(const double* A, long long base, int lid, int dag) {
    const double* p = A + base + 4LL * lid;
    q4 r; r.a = p[0]; r.b = p[1]; r.c = p[2]; r.d = p[3];
    return dag ? qcj(r) : r;
}

// ---------------------------------------------------------------- random numbers
__device__ __forceinline__ unsigned long long smix(unsigned long long z) {
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}
struct rng { unsigned long long s; };
__device__ __forceinline__ double unif(rng& g) {
    g.s += 0x9E3779B97F4A7C15ULL;
    return ((smix(g.s) >> 11) + 0.5) * (1.0 / 9007199254740992.0);   // in (0, 1)
}

// ---------------------------------------------------------------- Bessel I0, I1, exponentially scaled
__device__ void bessel01e(double a, double& i0e, double& i1e) {
    if (a < 17.0) {
        double h = 0.5 * a, h2 = h * h, t0 = 1.0, s0 = 1.0, t1 = 1.0, s1 = 1.0;   // t1: h^{2k}/(k!(k+1)!)
        for (int k = 1; k < 80; ++k) {
            t0 *= h2 / ((double)k * k);
            t1 *= h2 / ((double)k * (k + 1));
            s0 += t0; s1 += t1;
            if (t0 < 1e-18 * s0 && t1 < 1e-18 * s1) break;
        }
        double e = exp(-a);
        i0e = s0 * e; i1e = h * s1 * e;
    } else {
        double c = 1.0 / sqrt(2.0 * 3.14159265358979323846 * a);
        double a0 = 1.0, s0 = 1.0, a1 = 1.0, s1 = 1.0;
        for (int k = 1; k < 40; ++k) {
            double m = (double)(2 * k - 1) * (2 * k - 1);
            double n0 = a0 * (m - 0.0) / (8.0 * k * a);
            double n1 = a1 * (m - 4.0) / (8.0 * k * a);
            if (fabs(n0) > fabs(a0) && k > 2) break;
            a0 = n0; a1 = n1; s0 += a0; s1 += a1;
            if (fabs(a0) < 1e-17 && fabs(a1) < 1e-17) break;
        }
        i0e = c * s0; i1e = c * s1;
    }
}
__device__ double log_z(double a) {            // log(2 I1(a)/a), log z(0) = 0
    a = fmax(a, 1e-8);
    double i0e, i1e; bessel01e(a, i0e, i1e);
    return 0.6931471805599453 + log(i1e) + a - log(a);
}
__device__ double dlog_z(double a) {           // I0/I1 - 2/a, -> a/4
    a = fmax(a, 1e-6);
    if (a < 1e-3) return 0.25 * a;
    double i0e, i1e; bessel01e(a, i0e, i1e);
    return i0e / i1e - 2.0 / a;
}

extern "C" __global__ void bessel_test(const double* a, double* out, const int n) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= n) return;
    out[2 * i] = log_z(a[i]); out[2 * i + 1] = dlog_z(a[i]);
}

// ---------------------------------------------------------------- von Mises-Fisher on S^3
__device__ double sample_x0(double alpha, rng& g) {
    for (int it = 0; it < 100000; ++it) {
        double u0 = unif(g), u1 = unif(g), u2 = unif(g), u3 = unif(g);
        if (alpha >= 0.3) {
            double cs = cos(2.0 * 3.14159265358979323846 * u1);
            double lam2 = -(log(u0) + cs * cs * log(u2)) / (2.0 * alpha);
            if (u3 * u3 <= 1.0 - lam2) return 1.0 - 2.0 * lam2;
        } else {
            double x = 2.0 * u0 - 1.0;
            if (u3 <= sqrt(fmax(0.0, 1.0 - x * x)) * exp(alpha * (x - 1.0))) return x;
        }
    }
    return 1.0;
}
__device__ q4 sample_vmf(const q4 F, rng& g) {
    double a = qnorm(F);
    double x0 = sample_x0(a, g);
    double z = 2.0 * unif(g) - 1.0, ph = 2.0 * 3.14159265358979323846 * unif(g);
    double rr = sqrt(fmax(0.0, 1.0 - z * z)), s = sqrt(fmax(0.0, 1.0 - x0 * x0));
    q4 X; X.a = x0; X.b = s * rr * cos(ph); X.c = s * rr * sin(ph); X.d = s * z;
    q4 n = (a > 1e-12) ? qsc(F, 1.0 / a) : qone();
    return qm(X, n);
}

// ---------------------------------------------------------------- the class update
extern "C" __global__ void class_update(
    double* U, const double* Y, const int P, const int n, const int E, const long long NL1, const long long NC1,
    const int* c_lid, const int* stp, const int* stpd,
    const int* e_l, const double* e_c, const int* e_pre, const int* e_pred, const int* e_suf, const int* e_sufd,
    const int* e_dag, const double* e_mask,
    const int* cl_paths, const int* cl_dag, const double* cl_coef,
    const double beta, const double kappa, const unsigned long long seed, const unsigned long long counter,
    double* stats, const int debug, double* dbg)
{
    long long t = (long long)blockIdx.x * blockDim.x + threadIdx.x;
    if (t >= (long long)P * n) return;
    int p = (int)(t / n), i = (int)(t % n);
    rng g; g.s = smix(seed ^ smix(counter * 0x632BE59BD9B4E019ULL + (unsigned long long)t));
    int lid = c_lid[i];
    const int EM = 8;                                   // Emax <= 8 (checked on the host)
    q4 Pre[2][EM], Suf[2][EM], Yl[2][EM], Pho[2][EM];
    q4 Fw[2], Flin[2], Fo[2];
    double lzo[2];
    for (int c = 0; c < 2; ++c) {
        long long ub = ((long long)p * 2 + c) * NL1 * 4;
        long long yb = ((long long)p * 2 + c) * NC1 * 4;
        q4 W = qzero();
        for (int s = 0; s < 6; ++s) {
            int o = (i * 6 + s) * 3;
            q4 x = ld(U, ub, stp[o], stpd[o]);
            x = qm(x, ld(U, ub, stp[o + 1], stpd[o + 1]));
            x = qm(x, ld(U, ub, stp[o + 2], stpd[o + 2]));
            W = qadd(W, x);
        }
        Fw[c] = qsc(qcj(W), beta);
        Flin[c] = Fw[c]; Fo[c] = Fw[c]; lzo[c] = 0.0;
        for (int e = 0; e < E; ++e) {
            int oe = i * E + e;
            if (e_mask[oe] == 0.0) { Pre[c][e] = qone(); Suf[c][e] = qone(); Yl[c][e] = qone(); Pho[c][e] = qzero(); continue; }
            q4 pr = qone(), su = qone();
            for (int k = 0; k < 3; ++k) {
                pr = qm(pr, ld(U, ub, e_pre[oe * 3 + k], e_pred[oe * 3 + k]));
                su = qm(su, ld(U, ub, e_suf[oe * 3 + k], e_sufd[oe * 3 + k]));
            }
            int l = e_l[oe];
            q4 y = ld(Y, yb, l, 0);
            q4 ph = qzero();
            for (int pp = 0; pp < 7; ++pp) {
                double cf = cl_coef[l * 7 + pp];
                if (cf == 0.0) continue;
                int ob = (l * 7 + pp) * 4;
                q4 x = ld(U, ub, cl_paths[ob], cl_dag[ob]);
                for (int k = 1; k < 4; ++k) x = qm(x, ld(U, ub, cl_paths[ob + k], cl_dag[ob + k]));
                ph = qadd(ph, qsc(x, cf));
            }
            Pre[c][e] = pr; Suf[c][e] = su; Yl[c][e] = y; Pho[c][e] = ph;
            double w = kappa * e_c[oe];
            int dg = e_dag[oe];
            q4 M = qm(qm(su, qcj(y)), pr);
            Flin[c] = qadd(Flin[c], qsc(dg ? M : qcj(M), w));
            double r = qnorm(ph);
            double lam = dlog_z(kappa * r);
            q4 Z = qsub(y, qsc(ph, lam / fmax(r, 1e-12)));
            q4 MZ = qm(qm(su, qcj(Z)), pr);
            Fo[c] = qadd(Fo[c], qsc(dg ? MZ : qcj(MZ), w));
            lzo[c] += log_z(kappa * r);
        }
    }
    if (debug) {
        double* d = dbg + t * 26;
        for (int c = 0; c < 2; ++c) {
            d[c*13+0] = Flin[c].a; d[c*13+1] = Flin[c].b; d[c*13+2] = Flin[c].c; d[c*13+3] = Flin[c].d;
            d[c*13+4] = Fo[c].a;   d[c*13+5] = Fo[c].b;   d[c*13+6] = Fo[c].c;   d[c*13+7] = Fo[c].d;
            d[c*13+8] = lzo[c];
            d[c*13+9] = Fw[c].a; d[c*13+10] = Fw[c].b; d[c*13+11] = Fw[c].c; d[c*13+12] = Fw[c].d;
        }
        return;
    }
    // coupled proposal: maximal coupling of exp(q . Fo0) and exp(q . Fo1)
    q4 q1 = sample_vmf(Fo[0], g), q2 = q1;
    {
        double a1 = qnorm(Fo[0]), a2 = qnorm(Fo[1]);
        double cc = log_z(a1) - log_z(a2);
        q4 D = qsub(Fo[1], Fo[0]);
        double L = qdot(q1, D) + cc;
        if (log(unif(g)) > L) {
            double amax = fmax(1.0 - exp(-qnorm(D) - cc), 1e-300);
            for (int it = 0; it < 1000000; ++it) {
                q4 V = sample_vmf(Fo[1], g);
                double lr = -qdot(V, D) - cc;                     // log p1/p2 at V
                double ar = fmax(1.0 - exp(lr), 0.0);
                if (unif(g) * amax <= ar) { q2 = V; break; }
            }
        }
    }
    double lu = log(unif(g));                              // shared Metropolis uniform
    for (int c = 0; c < 2; ++c) {
        long long ub = ((long long)p * 2 + c) * NL1 * 4;
        q4 qo = ld(U, ub, lid, 0);
        q4 qn = (c == 0) ? q1 : q2;
        q4 Fn = Fw[c];
        double lzn = 0.0;
        for (int e = 0; e < E; ++e) {
            int oe = i * E + e;
            if (e_mask[oe] == 0.0) continue;
            int dg = e_dag[oe];
            q4 dd = dg ? qsub(qcj(qn), qcj(qo)) : qsub(qn, qo);
            q4 phn = qadd(Pho[c][e], qsc(qm(qm(Pre[c][e], dd), Suf[c][e]), e_c[oe]));
            double r = qnorm(phn);
            lzn += log_z(kappa * r);
            double lam = dlog_z(kappa * r);
            q4 Z = qsub(Yl[c][e], qsc(phn, lam / fmax(r, 1e-12)));
            q4 MZ = qm(qm(Suf[c][e], qcj(Z)), Pre[c][e]);
            Fn = qadd(Fn, qsc(dg ? MZ : qcj(MZ), kappa * e_c[oe]));
        }
        double lt = qdot(qsub(qn, qo), Flin[c]) - (lzn - lzo[c]);
        double lf = qdot(qn, Fo[c]) - log_z(qnorm(Fo[c]));
        double lr = qdot(qo, Fn) - log_z(qnorm(Fn));
        bool acc = lu <= lt + lr - lf;
        q4 q = acc ? qn : qo;
        double nn = qnorm(q);
        double* dst = U + ub + 4LL * lid;
        dst[0] = q.a / nn; dst[1] = q.b / nn; dst[2] = q.c / nn; dst[3] = q.d / nn;
        if (stats != 0) { atomicAdd(stats, acc ? 1.0 : 0.0); atomicAdd(stats + 1, 1.0); }
    }
}
'''


class FusedSampler(C.PairSampler):
    """PairSampler with the fused class update (same state, same interface)."""

    _module = None

    def __init__(self, be, geo, beta, kappa, U, Y, seed=12345):
        super().__init__(be, geo, beta, kappa, U, Y)
        import cupy as cp
        self.cp = cp
        if FusedSampler._module is None:
            FusedSampler._module = cp.RawModule(code=KERNEL, options=("-std=c++14",))
        self.kern = FusedSampler._module.get_function("class_update")
        assert geo.Emax <= 8
        self.seed = np.uint64(seed)
        self.counter = 0
        self.stats = cp.zeros(2, dtype=cp.float64)
        if not hasattr(geo, "fused_tables"):
            tabs = []
            for c in geo.classes:
                tabs.append({k: (cp.ascontiguousarray(cp.asarray(v).astype(cp.int32)) if cp.asarray(v).dtype.kind in "iu"
                                 else cp.ascontiguousarray(cp.asarray(v).astype(cp.float64))) for k, v in c.items()})
            geo.fused_tables = tabs
            geo.fused_cl = (cp.ascontiguousarray(cp.asarray(geo.cl_paths).astype(cp.int32)),
                            cp.ascontiguousarray(cp.asarray(geo.cl_dag).astype(cp.int32)),
                            cp.ascontiguousarray(cp.asarray(geo.cl_coef).astype(cp.float64)))
        self.U = cp.ascontiguousarray(self.U)
        self.Y = cp.ascontiguousarray(self.Y)

    def _launch(self, ci, debug=False):
        cp = self.cp
        t = self.geo.fused_tables[ci]
        clp, cld, clc = self.geo.fused_cl
        P = self.U.shape[0]
        n = int(t["lid"].shape[0])
        E = int(t["e_l"].shape[1])
        NL1 = self.U.shape[2]
        NC1 = self.Y.shape[2]
        dbg = cp.zeros((P * n, 26)) if debug else cp.zeros(1)
        nt = P * n
        bs = 128
        self.counter += 1
        self.kern(((nt + bs - 1) // bs,), (bs,),
                  (self.U, self.Y, np.int32(P), np.int32(n), np.int32(E), np.int64(NL1), np.int64(NC1),
                   t["lid"], t["stp"], t["stpd"], t["e_l"], t["e_c"], t["e_pre"], t["e_pred"], t["e_suf"], t["e_sufd"],
                   t["e_dag"], t["e_mask"], clp, cld, clc, np.float64(self.beta), np.float64(self.kappa),
                   self.seed, np.uint64(self.counter), self.stats, np.int32(1 if debug else 0), dbg))
        return dbg.reshape(P, n, 2, 13) if debug else None

    def update_class(self, c):
        ci = self._index_of(c)
        self._launch(ci)

    def _index_of(self, c):
        if not hasattr(self, "_idmap"):
            self._idmap = {id(cc): k for k, cc in enumerate(self.geo.classes)}
        return self._idmap[id(c)]

    def sweep(self):
        for ci in range(len(self.geo.classes)):
            self._launch(ci)

    def acceptance(self):
        s = self.cp.asnumpy(self.stats)
        return s[0] / max(s[1], 1.0)


def reference_fields(S, c):
    """F_lin, F_o (proposal field), lz_o and F_w of the reference path for class c: (P, 2, n, 4) x 3 and (P, 2, n)."""
    be, xp = S.be, S.be.xp
    k = S.kappa
    W = xp.sum(S.prod(c["stp"], c["stpd"]), axis=-2)
    Fw = S.beta * W * be.conj
    Pre = S.prod(c["e_pre"], c["e_pred"])
    Suf = S.prod(c["e_suf"], c["e_sufd"])
    Yl = S.Y[:, :, c["e_l"]]
    dag = c["e_dag"][..., None].astype(bool)
    wgt = (k * c["e_c"] * c["e_mask"])[..., None]

    def field(Z):
        M = be.qmul(be.qmul(Suf, Z * be.conj), Pre)
        return xp.sum(xp.where(dag, M, M * be.conj) * wgt, axis=-2)

    Phi_o = S.phi(c["e_l"])
    r = xp.linalg.norm(Phi_o, axis=-1)
    lam = be.dlog_z(k * r)
    hat = Phi_o / xp.maximum(r, 1e-12)[..., None]
    F_lin = Fw + field(Yl)
    F_o = Fw + field(Yl - lam[..., None] * hat)
    lz_o = xp.sum(c["e_mask"] * be.log_z(k * r), axis=-1)
    return F_lin, F_o, lz_o, Fw
