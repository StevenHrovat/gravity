"""CPU end-to-end pipeline test (pre-registered as a pipeline test only, PREREG.md "CPU pipeline test"): every run type of the plan at
tiny size (12^4, b = 2, 4, 2 chains x 24 measurements), then the photon-gate mode and the full analysis. One process, CPU only.
The numbers are not physics (b = 2, 4 at beta = 2.3 is L sqrt(sigma) = 0.70, 1.40, in a box of 4.2 / sqrt(sigma)).

Usage: python pipeline_test.py [OUTDIR]   (default cpu-test/)
"""
import argparse
import os
import sys
import time

os.environ["CUDA_VISIBLE_DEVICES"] = "-1"
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import goodblock as GB  # noqa: E402
import analyse_refit as AR  # noqa: E402

RUNS = [("u1_b1.1_N12", "u1", 1.1, 5901), ("z2_b0.6_N12", "z2", 0.6, 5902), ("su2_b2.3_N12", "su2", 2.3, 5903),
        ("su2_b2.5_N12", "su2", 2.5, 5904)]


def main():
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "cpu-test")
    os.makedirs(out, exist_ok=True)
    t0 = time.time()
    for name, g, beta, seed in RUNS:
        a = argparse.Namespace(group=g, beta=beta, N=12, blocks="2,4", n_therm=30, n_meas=24, seed=seed,
                               out=os.path.join(out, name + ".npz"), chains=2, every=2, n_or=3, w=GB.W_DEFAULT, cpu=True, hot=False)
        t = time.time()
        GB.run(a)
        print(f"PIPELINE {name} done in {time.time() - t:.0f}s", flush=True)
    print("\n##### photon-gate mode", flush=True)
    AR.main([os.path.join(out, "u1_b1.1_N12.npz"), "--photon-gate"])
    print("\n##### full analysis", flush=True)
    AR.main([os.path.join(out, "*.npz"), "--out", os.path.join(out, "summary.json"), "--scaling-pair", "2.3:4,2.5:4"])
    print(f"\nPIPELINE TEST DONE in {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
