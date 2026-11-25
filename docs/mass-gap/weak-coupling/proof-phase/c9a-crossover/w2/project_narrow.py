"""Projection of the narrow W2 run (amendment A6) from the one timed fused launch.

Narrow run per beta (2.3 and 3.5; kappa 16; ell 6; theta = pi; 80 pairs per job, 6 jobs per launch):
  sampled Y x 8 (equilibrium outside), A1-A4 with the equilibrium outside, A1-A4 with the worst of a pool of 8, A6 once
  = 17 jobs = 3 launches; the 4 pool jobs share the first launch, so only that launch has a pool phase (32 x 8 = 256 pairs,
  T/10 sweeps).
Cost per launch = set-up (geometry, build, start-1 heating; from the timed launch) + T(beta) x s_main (seconds per sweep of a
full fused launch, measurement overhead included) [+ T/10 x s_pool for the pool launch]. s_main and s_pool are taken
beta-independent (A4); T(2.3) = 300, T(3.5) = 600 from the pilot.

Usage: py project_narrow.py runs/timing_fused_b3.5.json [--T23 300] [--T35 600]
"""
import argparse
import json


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("timing")
    ap.add_argument("--T23", type=int, default=300)
    ap.add_argument("--T35", type=int, default=600)
    a = ap.parse_args()
    J = json.load(open(a.timing))
    s_main = J["sec_per_sweep_main"]
    setup = J["seconds_geometry"] + J["seconds_build"]
    pool_pairs_timed = max(J["pool_pairs"], 1)
    s_pool = J["seconds_pool"] / J["pool_T"] if J["pool_pairs"] else s_main
    rows, tot = [], 0.0
    for beta, T in ((2.3, a.T23), (3.5, a.T35)):
        launches = 3
        main = launches * (setup + T * s_main)
        pool = max(10, T // 10) * s_pool               # one pool launch per beta (256 pairs; launch-bound, ~ timed cost)
        rows.append(dict(beta=beta, T=T, launches=launches, main_s=main, pool_s=pool, total_h=(main + pool) / 3600))
        tot += main + pool
    out = dict(timing=a.timing, s_main=s_main, s_pool=s_pool, setup=setup, rows=rows, total_hours=tot / 3600,
               target_hours=3.0)
    json.dump(out, open("PROJECTION_narrow.json", "w"), indent=1)
    print(f"s_main {s_main:.3f} s/sweep (480 pairs), s_pool {s_pool:.3f} s/sweep ({pool_pairs_timed} pairs timed), "
          f"set-up {setup:.0f} s per launch")
    for r in rows:
        print(f"  beta {r['beta']}: T {r['T']}, {r['launches']} launches: main {r['main_s'] / 3600:.2f} h, pool "
              f"{r['pool_s'] / 60:.1f} min -> {r['total_h']:.2f} h")
    print(f"  TOTAL narrow run: {tot / 3600:.2f} GPU-hours (target < 3 h)")


if __name__ == "__main__":
    main()
