"""W2 projection (W2-PREREG.md section 8, step 3, amendments A1-A5 in PIPELINE.md).

Cost model. The implementation is launch-bound: one sweep costs about the same for any number of pairs up to the batch
capacity (480 pairs at ell = 6, 960 at ell = 4, 160 pairs per job). So
  * a group = (theory, beta, kappa, ell); its jobs share T(beta) and run in launch batches of cap jobs (3 at ell = 6, 6 at
    ell = 4);
  * one batch costs  setup + T(beta) * s_ell  (+ T(beta)/10 * s_ell for a greedy pool, if the batch's class uses one);
  * s_6 and setup come from the timed job; s_4 = s_6 * r4 (r4 measured by profiling, 7.28 s / 6.64 s at full batch);
  * per-sweep cost is taken beta-independent (A4); T(beta) from the pilot, T(2.6) = T(3.0) = max(T(2.3), T(3.5)).
Per SU(2) group: sampled 16 jobs (pool 0); A1-A5 (A5 at three beta_A) x {equilibrium outside, worst of pool} = 14; A6 = 1.
Controls (U(1), 2I; not implemented) are costed like SU(2) groups at T(2.3) with 14 and 13 jobs.

Usage: py project.py TIMING.json T23 T35 [--r4 1.096] [--cap 20]   (writes PROJECTION.json, prints the tables)
"""
import argparse
import json
import math

BETAS = (2.3, 2.6, 3.0, 3.5)


def classes(nsampled):
    """(name, pool, njobs) per SU(2) group."""
    out = [("sampled", 0, nsampled)]
    for c in ("A1", "A2", "A3", "A4", "A5a", "A5b", "A5c"):
        out += [(c, 0, 1), (c, 8, 1)]
    out.append(("A6", 0, 1))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("timing")
    ap.add_argument("T23", type=int)
    ap.add_argument("T35", type=int)
    ap.add_argument("--r4", type=float, default=7.28 / 6.64)
    ap.add_argument("--cap", type=float, default=20.0)
    ap.add_argument("--mixed", action="store_true", help="pack jobs of different classes into one launch batch")
    ap.add_argument("--out", default="PROJECTION.json")
    a = ap.parse_args()
    J = json.load(open(a.timing))
    T = {2.3: a.T23, 3.5: a.T35}
    T[2.6] = T[3.0] = max(a.T23, a.T35)
    s6 = J["sec_per_sweep_main"]
    setup = J["seconds_geometry"] + J["seconds_build"]
    sp6 = J["sec_per_sweep_pool"] if J["pool"] > 0 else s6
    cap = {6: 3, 4: 6}

    def s(ell):
        return s6 if ell == 6 else s6 * a.r4

    def batch_seconds(ell, beta, pool):
        t = setup + T[beta] * s(ell)
        if pool:
            t += max(10, T[beta] // 10) * (sp6 if ell == 6 else sp6 * a.r4)
        return t

    def group(beta, ell, nsampled):
        tot, nb = 0.0, 0
        if a.mixed:
            cl = classes(nsampled)
            nj = sum(n for (_, _, n) in cl)
            npool = sum(n for (_, p, n) in cl if p)
            b = math.ceil(nj / cap[ell])
            bp = math.ceil(npool / cap[ell])
            tot = b * batch_seconds(ell, beta, False) + bp * (max(10, T[beta] // 10) * (sp6 if ell == 6 else sp6 * a.r4))
            return tot, b
        for (_, pool, nj) in classes(nsampled):
            b = math.ceil(nj / cap[ell])
            nb += b
            tot += b * batch_seconds(ell, beta, pool)
        return tot, nb

    def plan(bk, ells_of, nsampled):
        rows, tot = [], 0.0
        for (b, k) in bk:
            for ell in ells_of(b):
                t, nb = group(b, ell, nsampled)
                rows.append(dict(theory="SU(2)", beta=b, kappa=k, ell=ell, batches=nb, hours=t / 3600))
                tot += t
        for name, nj in (("U(1) (estimate)", 14), ("2I (estimate)", 13)):
            for k in (4, 16):
                for ell in (4, 6):
                    nb = math.ceil(nj / cap[ell])
                    t = nb * batch_seconds(ell, 2.3, False)
                    rows.append(dict(theory=name, beta=None, kappa=k, ell=ell, batches=nb, hours=t / 3600))
                    tot += t
        return rows, tot / 3600

    full = [(b, k) for b in BETAS for k in (4, 16)]
    red = [(b, 16) for b in BETAS] + [(2.3, 4), (3.5, 4)]
    plans = [
        ("full design (amended)", full, lambda b: (4, 6), 16),
        ("(i) kappa = 4 only at beta 2.3, 3.5", red, lambda b: (4, 6), 16),
        ("(ii) + ell = 4 only at beta 2.3", red, lambda b: (4, 6) if b == 2.3 else (6,), 16),
        ("(iii) + sampled Y 16 -> 8", red, lambda b: (4, 6) if b == 2.3 else (6,), 8),
    ]
    out = dict(timing=a.timing, T={str(b): T[b] for b in BETAS}, s6=s6, s4=s(4), setup=setup, ladder=[], ladder_hours=[],
               batch_seconds={str(ell): {str(b): batch_seconds(ell, b, False) for b in BETAS} for ell in (4, 6)})
    for name, bk, ells, ns in plans:
        rows, h = plan(bk, ells, ns)
        out["ladder"].append(dict(name=name, hours=h, rows=rows))
        out["ladder_hours"].append(round(h, 2))
        print(f"== {name}: {h:.1f} GPU-hours (cap {a.cap})")
        per_beta = {}
        for r in rows:
            key = r["beta"] if r["beta"] is not None else r["theory"]
            per_beta[key] = per_beta.get(key, 0.0) + r["hours"]
        for key, h2 in per_beta.items():
            print(f"     {str(key):18s} {h2:6.2f} h")
    # (iv) theta = pi only: 80 pairs per job, capacity doubles
    cap[6], cap[4] = 6, 12
    rows, h = plan(red, lambda b: (4, 6) if b == 2.3 else (6,), 8)
    out["ladder"].append(dict(name="(iv) + theta = pi only", hours=h, rows=rows))
    out["ladder_hours"].append(round(h, 2))
    print(f"== (iv) + theta = pi only: {h:.1f} GPU-hours")
    out["mixed"] = a.mixed
    json.dump(out, open(a.out, "w"), indent=1)


if __name__ == "__main__":
    main()
