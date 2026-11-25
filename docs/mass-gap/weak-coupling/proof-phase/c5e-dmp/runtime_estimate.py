"""Runtime estimate for PREREG-JOINT.md (c5e-dmp). Rate model from the existing run_su2_gpu.py logs (lattice/runs-gpu/luscher_L*.log,
ttl_*.log): 0.47-0.59 us per site and sweep for 10 chains with 3 overrelaxation steps, measurements every 2 sweeps, 4 smearing levels;
we use 0.55 us (+-20 %), plus a 25 s start-up per run. No GPU is used here; arithmetic only."""
RATE = 0.55e-6
PLAN = [  # (beta, L, T, n_therm, n_meas, every, chains, a_sqrt_sigma, role)
    (2.3, 4, 32, 500, 2000, 2, 10, 0.350, "main"), (2.3, 6, 32, 500, 2000, 2, 10, 0.350, "main"),
    (2.3, 8, 32, 500, 2000, 2, 10, 0.350, "main"), (2.3, 12, 32, 500, 1500, 2, 10, 0.350, "main"),
    (2.4, 4, 32, 500, 2000, 2, 10, 0.258, "main"), (2.4, 6, 32, 500, 2000, 2, 10, 0.258, "main"),
    (2.4, 8, 32, 500, 2000, 2, 10, 0.258, "main"), (2.4, 12, 32, 500, 1500, 2, 10, 0.258, "main"),
    (2.4, 16, 32, 500, 1000, 2, 10, 0.258, "main"),
    (2.5, 6, 32, 500, 2000, 2, 10, 0.1825, "main"), (2.5, 8, 32, 500, 2000, 2, 10, 0.1825, "main"),
    (2.5, 12, 32, 500, 1500, 2, 10, 0.1825, "main"), (2.5, 16, 32, 500, 1000, 2, 10, 0.1825, "main"),
    (2.5, 24, 48, 500, 600, 2, 8, 0.1825, "optional"),
]
tot = {"main": 0.0, "optional": 0.0}
for b, L, T, th, nm, ev, ch, a, role in PLAN:
    s = L ** 3 * T * (th + nm * ev) * ch * RATE + 25
    tot[role] += s
    print(f"beta={b} L={L:2d} T={T} Lsqrt(sigma)={L * a:4.2f} sweeps={th + nm * ev} chains={ch}  {s / 60:6.1f} min  [{role}]")
print(f"main: {tot['main'] / 3600:.2f} h   optional: {tot['optional'] / 3600:.2f} h   (+-20 % rate, +-50 % overall as house rule)")
