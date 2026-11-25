"""SU(2) configurations and measurements on the GPU: the same physics, measurements and output file as run_su2.py, many times faster.

The update (Kennedy-Pendleton heat bath, overrelaxation, checkerboard, reunitarisation) and the APE smearing run in the fused CUDA kernels of
the GUID v7 lattice code (gpu/su3_cuda.py, gpu/gauge.py, copied unchanged; see gpu/README.md). The measurements (plaquette, the spatial
1x1 and 2x2 glueball operators, the torelons) are those of su2.py / run_su2.py, written here in cupy. CHAINS independent lattices are
updated together (one GPU launch for all of them); their measurements are stored one chain after another, so analyse.py reads the file
unchanged (its jackknife bins stay inside one chain when CHAINS divides 20).

Usage:
  python run_su2_gpu.py BETA L T N_THERM N_MEAS SEED OUT.npz [N_OR] [EVERY] [CHAINS] [LEVELS]
      LEVELS: APE smearing levels, comma separated (default 4,12, as run_su2.py); more levels = a larger operator basis
  python run_su2_gpu.py selftest     every GPU measurement against su2.py on the same configuration (must agree to 1e-10)
Needs cupy (pip install "cupy-cuda12x[ctk]") and an NVIDIA GPU.
"""

import os
import sys
import time

import numpy as np
import cupy as cp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "gpu"))
import gauge as G  # noqa: E402

SMEAR_LEVELS = (4, 12)  # APE steps with alpha = 0.5, as run_su2.py
ALPHA = 0.5


def shift(x, mu, s):
    """Field at site + s * mu-hat; arrays (B, x, y, z, t, 2, 2), mu 0..2 space, 3 time."""
    return cp.roll(x, -s, axis=1 + mu)


def dag(x):
    return cp.conj(cp.swapaxes(x, -1, -2))


def mm(a, b):
    """Product of 2x2 matrices on every site, as plain elementwise arithmetic (cp.matmul on millions of tiny matrices is slow)."""
    return a[..., :, 0, None] * b[..., None, 0, :] + a[..., :, 1, None] * b[..., None, 1, :]


def half_retr(x):
    return 0.5 * cp.real(x[..., 0, 0] + x[..., 1, 1])


def line(Vi, i, R):
    out = Vi
    for r in range(1, R):
        out = mm(out, shift(Vi, i, r))
    return out


def glueball_ops(V):
    """(B, 2, T): zero-momentum sums of the spatial 1x1 and 2x2 loops over the three spatial planes (su2.glueball_ops)."""
    ops = []
    for size in (1, 2):
        o = 0
        for i, j in ((0, 1), (0, 2), (1, 2)):
            a, b = line(V[i], i, size), line(V[j], j, size)
            loop = mm(mm(a, shift(b, i, size)), mm(dag(shift(a, j, size)), dag(b)))
            o = o + half_retr(loop).sum(axis=(1, 2, 3))
        ops.append(o)
    return cp.stack(ops, axis=1)


def torelon_ops(V, L):
    """(B, T): spatial Polyakov loops, each counted once (run_su2.torelon_ops)."""
    out = 0
    for i in (0, 1, 2):
        out = out + half_retr(line(V[i], i, L)).sum(axis=(1, 2, 3)) / L
    return out


def measure(g, L, levels=SMEAR_LEVELS):
    """Plaquette (B,), glueball ops (B, 2*levels, T), torelon ops (B, levels, T) on the current configuration."""
    V = [g.U[0], g.U[1], g.U[2]]
    glue, tor, done = [], [], 0
    for n in levels:
        V = g.ape(ALPHA, n - done, niter=0, U=V)
        done = n
        glue.append(glueball_ops(V))
        tor.append(torelon_ops(V, L))
    return g.plaquette(), cp.concatenate(glue, axis=1).get(), cp.stack(tor, axis=1).get()


def to_quaternions(U):
    """GPU links (4 x (B, x, y, z, t, 2, 2)), chain 0, to su2.py's layout (4, T, L, L, L, 4): U = a0 + i a.sigma."""
    out = []
    for mu in (3, 0, 1, 2):  # su2.py direction 0 is time
        u = cp.asnumpy(U[mu][0])
        u = np.moveaxis(u, 3, 0)  # (t, x, y, z, 2, 2)
        q = np.stack([u[..., 0, 0].real, u[..., 0, 1].imag, u[..., 0, 1].real, u[..., 0, 0].imag], axis=-1)
        out.append(q)
    return np.array(out)


def selftest():
    from su2 import Lattice
    import run_su2 as R
    L, T = 4, 6
    g = G.Gauge(L, T, 2.3, nc=2, B=2, seed=7, start="hot")
    for _ in range(5):
        g.sweep(3)
    q = to_quaternions(g.U)
    lat = Lattice(T, L, 2.3, 0)
    lat.U = q
    worst = 0.0
    p_gpu, glue_gpu, tor_gpu = measure(g, L)
    worst = max(worst, abs(lat.plaquette() - p_gpu[0]))
    V = lat.U
    done = 0
    for k, n in enumerate(SMEAR_LEVELS):
        V = R.lat_smear_more(lat, V, n - done)
        done = n
        worst = max(worst, np.max(np.abs(lat.glueball_ops(V) - glue_gpu[0, 2 * k:2 * k + 2])))
        worst = max(worst, np.max(np.abs(R.torelon_ops(lat, V) - tor_gpu[0, k])))
    print(f"selftest: largest difference GPU vs su2.py = {worst:.2e}")
    if worst > 1e-10:
        print("FAIL")
        sys.exit(1)
    print("OK")


def main():
    if sys.argv[1] == "selftest":
        return selftest()
    beta, L, T = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    n_therm, n_meas, seed, out = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), sys.argv[7]
    n_or = int(sys.argv[8]) if len(sys.argv) > 8 else 4
    every = int(sys.argv[9]) if len(sys.argv) > 9 else 2
    chains = int(sys.argv[10]) if len(sys.argv) > 10 else 1
    levels = tuple(int(x) for x in sys.argv[11].split(",")) if len(sys.argv) > 11 else SMEAR_LEVELS
    g = G.Gauge(L, T, beta, nc=2, B=chains, seed=seed, start="cold")
    t0 = time.time()
    for _ in range(n_therm):
        g.sweep(n_or)
    plaq = np.zeros((n_meas, chains))
    glue = np.zeros((n_meas, chains, 2 * len(levels), T))
    tor = np.zeros((n_meas, chains, len(levels), T))

    def save(m, partial):
        """Chain-major: all of chain 0's measurements, then chain 1's, ... (analyse.py reads it as one series)."""
        np.savez(out, beta=beta, L=L, T=T, seed=seed, n_therm=n_therm, n_or=n_or, every=every, chains=chains,
                 smear_levels=np.array(levels), plaq=plaq[:m].T.reshape(-1),
                 glue=glue[:m].transpose(1, 0, 2, 3).reshape(-1, glue.shape[2], T),
                 tor=tor[:m].transpose(1, 0, 2, 3).reshape(-1, tor.shape[2], T),
                 seconds=time.time() - t0, partial=int(partial), backend="gpu")

    for m in range(n_meas):
        for _ in range(every):
            g.sweep(n_or)
        plaq[m], glue[m], tor[m] = measure(g, L, levels)
        if m % 100 == 0:
            if m:
                save(m, True)
            print(f"beta={beta} L={L} chains={chains} meas {m}/{n_meas} plaq={plaq[:m + 1].mean():.5f} t={time.time() - t0:.0f}s",
                  flush=True)
    save(n_meas, False)
    print(f"done {out} plaq={plaq.mean():.5f} in {time.time() - t0:.0f}s", flush=True)


if __name__ == "__main__":
    sys.exit(main())
