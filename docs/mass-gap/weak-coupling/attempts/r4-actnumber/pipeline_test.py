"""CPU end-to-end pipeline test (PREREG.md "Pipeline test": a test of the pipeline only, not physics). One process, numpy only.

Runs a miniature version of every run type of the plan (U(1) photon gate, SU(2) in two planes and untwisted, Z2, 2I frozen and below
freezing) at tiny sizes, then the full analysis, into cpu-test/. About eight minutes on one core.

Usage: python pipeline_test.py       (sets CUDA_VISIBLE_DEVICES=-1 itself)
"""

import os
import sys
import time
import types

import numpy as np

os.environ["CUDA_VISIBLE_DEVICES"] = "-1"
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import actnumber as A  # noqa: E402
import analyse_actnumber as AA  # noqa: E402

OUT = os.path.join(HERE, "cpu-test")
MINI = [
    # name, group, beta, L, T, plane, twisted, chains, therm, meas, every, levels, seed
    ("u1_b1.1_L2", "u1", 1.1, 2, 16, "01", True, 4, 100, 200, 2, "0,2", 1),
    ("u1_b1.1_L4", "u1", 1.1, 4, 32, "01", True, 4, 100, 200, 2, "0,2", 2),
    ("u1_b1.1_L6", "u1", 1.1, 6, 32, "01", True, 4, 60, 120, 2, "0,2", 3),
    ("su2_b2.4_L2", "su2", 2.4, 2, 32, "01", True, 4, 100, 200, 2, "0,2", 4),
    ("su2_b2.4_L4", "su2", 2.4, 4, 24, "01", True, 4, 60, 150, 2, "0,2,6", 5),
    ("su2_b2.4_L4_p12", "su2", 2.4, 4, 24, "12", True, 4, 60, 150, 2, "0,2,6", 6),
    ("su2_b2.4_L4_per", "su2", 2.4, 4, 24, "01", False, 4, 60, 100, 2, "0,2,6", 7),
    ("z2_b0.5_L2", "z2", 0.5, 2, 16, "01", True, 4, 100, 200, 2, "0", 8),
    ("z2_b0.5_L4", "z2", 0.5, 4, 16, "01", True, 4, 100, 150, 2, "0", 9),
    ("2i_b8.0_L2", "2i", 8.0, 2, 16, "01", True, 4, 100, 200, 2, "0,2", 10),
    ("2i_b8.0_L4", "2i", 8.0, 4, 16, "01", True, 4, 60, 100, 2, "0,2", 11),
    ("2i_b2.4_L4", "2i", 2.4, 4, 24, "01", True, 4, 60, 100, 2, "0,2,6", 12),
    # the four-move addendum in miniature (cubes L = 2 and 4 above): boxes (2, 2, 4) and (4, 2, 4)
    ("su2_b2.4_box2x2x4", "su2", 2.4, 4, 32, "01", True, 4, 100, 200, 2, "0,2", 13, "2,2,4"),
    ("su2_b2.4_box4x2x4", "su2", 2.4, 4, 24, "01", True, 4, 60, 150, 2, "0,2", 14, "4,2,4"),
    ("u1_b1.1_box2x2x4", "u1", 1.1, 4, 32, "01", True, 4, 100, 200, 2, "0,2", 15, "2,2,4"),
    ("u1_b1.1_box4x2x4", "u1", 1.1, 4, 32, "01", True, 4, 100, 200, 2, "0,2", 16, "4,2,4"),
]


def synthetic_readings():
    """The combining readings on synthetic counted points with a known answer (the toy runs above have too few counted points to
    reach them): z(x) = x^3 / (x + 1.6), x = L sqrt(sigma), 3 % errors, at the plan's (beta, L); U(1) boxes E = c Lz / (Lx Ly).
    Known: z = 1 at x = 1.45, z = F* = 0.881 at x = 1.37, perfect collapse, growth everywhere, light l = 2, w = 1/2."""
    import math
    rng = np.random.default_rng(3)
    runs = []
    asq = {2.4: 0.2579, 2.5: 0.1822, 2.6: 0.1396}
    Ls = {2.4: (4, 6, 8, 10, 12, 14), 2.5: (4, 6, 8, 10, 12, 14, 16), 2.6: (4, 6, 8, 12)}
    for b, LL in Ls.items():
        for L in LL:
            x = L * asq[b]
            z = x ** 3 / (x + 1.6)
            dz = 0.03 * z
            runs.append({"file": f"syn_{b}_{L}", "group": "su2", "beta": b, "L": L, "Ls": [L, L, L], "cubic": True, "twisted": True,
                         "plane": [0, 1], "counted": True, "z": [z + dz * rng.standard_normal(), dz], "E": [z / L, dz / L],
                         "L_sqrt_sigma": [x, 0.01 * x], "verdict": "counted"})
    for (lx, ly, lz) in ((4, 4, 4), (4, 4, 8), (8, 4, 8), (8, 8, 8)):
        E = 0.35 * lz / (lx * ly)
        r = {"file": f"syn_u1_{lx}{ly}{lz}", "group": "u1", "beta": 1.1, "L": lz, "Ls": [lx, ly, lz], "cubic": lx == ly == lz,
             "twisted": True, "plane": [0, 1], "counted": True, "E": [E, 0.02 * E], "z": [E * lz, 0.02 * E * lz], "verdict": "counted"}
        runs.append(r)
    R = AA.readings(runs)
    print("SYNTHETIC crossing", {k: v.get("L_star_sqrt_sigma") for k, v in R["crossing"].items()}, "(true 1.45)", flush=True)
    print("SYNTHETIC inversion", {k: v.get("L_sqrt_sigma") for k, v in R["inversion_box_two_state"].items()}, "(true 1.37)", flush=True)
    print("SYNTHETIC growth", {k: (v["verdict"], v.get("g_min")) for k, v in R["growth"].items()}, flush=True)
    print("SYNTHETIC scaling", R["scaling_verdict"], "collapse", R["collapse"]["verdict"], R["collapse"].get("min_sigma_over_u_continuum"),
          flush=True)
    print("SYNTHETIC four moves U(1)", [(e["l"], e["w_x"], e["w_y"], e.get("control")) for e in R["four_moves"]], flush=True)
    print("SYNTHETIC large end", {k: [round(q["R_string"], 3) for q in v] for k, v in R["large_end"].items()}, flush=True)


def main():
    os.makedirs(OUT, exist_ok=True)
    t0 = time.time()
    files = []
    for e in MINI:
        (name, g, beta, L, T, plane, tw, ch, th, me, ev, lv, seed) = e[:13]
        a = types.SimpleNamespace(group=g, beta=beta, L=L, T=T, seed=seed, out=os.path.join(OUT, name + ".npz"), plane=plane,
                                  chains=ch, therm=th, meas=me, every=ev, n_or=3, levels=lv, alpha=0.5, path="array",
                                  start="mixed", hits=4, untwisted=not tw, cpu=True, box=e[13] if len(e) > 13 else None)
        t = time.time()
        A.run(a)
        print(f"PIPELINE {name}: {time.time() - t:.1f}s", flush=True)
        files.append(a.out)
    sys.argv = ["analyse_actnumber.py"] + files + ["--out", os.path.join(OUT, "summary.json")]
    AA.main()
    sys.argv = ["analyse_actnumber.py"] + [f for f in files if "u1_b1.1_L" in f] + ["--photon-gate"]
    AA.main()
    synthetic_readings()
    print(f"PIPELINE TEST DONE in {time.time() - t0:.0f}s", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
