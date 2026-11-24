"""Time the GPU SU(2) code: one sweep (1 heat bath + 3 overrelaxation) and one measurement, per lattice size and number of chains.

Usage: python gpu/bench.py [L,L,...] [B,B,...]     prints seconds per sweep and per measurement, and per chain
"""

import os
import sys
import time

import cupy as cp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))
import gauge as G  # noqa: E402
import run_su2_gpu as R  # noqa: E402


def timed(f, n):
    cp.cuda.Device().synchronize()
    t = time.perf_counter()
    for _ in range(n):
        f()
    cp.cuda.Device().synchronize()
    return (time.perf_counter() - t) / n


def main():
    Ls = [int(x) for x in (sys.argv[1] if len(sys.argv) > 1 else "10,14,16,20").split(",")]
    Bs = [int(x) for x in (sys.argv[2] if len(sys.argv) > 2 else "1,4,10,20").split(",")]
    for L in Ls:
        for B in Bs:
            try:
                g = G.Gauge(L, L, 2.4, nc=2, B=B, seed=1, start="cold")
                g.sweep(3)
                R.measure(g, L)
                ts = timed(lambda: g.sweep(3), 10)
                tm = timed(lambda: R.measure(g, L), 3)
                print(f"L={L:2d} chains={B:2d}  sweep {ts * 1e3:8.1f} ms ({ts / B * 1e3:7.2f} per chain)   "
                      f"measure {tm * 1e3:8.1f} ms ({tm / B * 1e3:7.2f} per chain)", flush=True)
                del g
                cp.get_default_memory_pool().free_all_blocks()
            except cp.cuda.memory.OutOfMemoryError:
                print(f"L={L:2d} chains={B:2d}  out of GPU memory", flush=True)
                cp.get_default_memory_pool().free_all_blocks()


if __name__ == "__main__":
    main()
