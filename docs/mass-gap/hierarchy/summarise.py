"""Summarise the stored Migdal-Kadanoff trajectories (results/mk_*.json) into the table of README section 5: the steady per-layer flow
of SU(2), the stalled flow of U(1) and the fit of U(1)'s tail drift to A exp(-c beta). Prints markdown."""

import json
import math
import os

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, "..", "results")


def load(name):
    with open(os.path.join(RES, name)) as f:
        return json.load(f)


def main():
    b0 = 11 * 2 / (48 * math.pi ** 2)
    one_loop = 8 * b0 * math.log(2)  # SU(2), beta = 4/g^2, per halving of the resolution
    su2 = load("mk_su2_d4.json")["SU(2) d=4"]
    print("| SU(2), d = 4, start β | β per layer (after the reshaping step) | layers to β < 1 |")
    print("|---|---|---|")
    for b, rows in su2.items():
        drops = [float(r["drop"]) for r in rows[2:] if r["drop"] is not None]
        k = next((r["step"] for r in rows if r["beta_hk"] < 1.0), None)
        steady = drops[-1] if drops else float("nan")
        print(f"| {b} | {min(drops):.3f} to {max(drops):.3f} (last {steady:.4f}) | {k if k is not None else '> ' + str(rows[-1]['step'])} |")
    print(f"\nOne-loop asymptotic freedom, 8·b₀·ln 2 with b₀ = 11·2/(48π²): **{one_loop:.4f}** per layer.\n")
    tail = load("mk_u1_d4_tail.json")["U(1) d=4"]
    pts = []
    print("| U(1), d = 4, start β | β_hk where it stalls | drift per layer at the end (towards strong coupling) |")
    print("|---|---|---|")
    for b, rows in tail.items():
        last = rows[-1]
        d = float(last["drop"])
        pts.append((last["beta_hk"], d))
        print(f"| {b} | {last['beta_hk']:.4f} | {d:.3e} |")
    # least squares of ln(drift) against beta
    xs = [p[0] for p in pts if p[1] > 0]
    ys = [math.log(p[1]) for p in pts if p[1] > 0]
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    c = -sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
    A = math.exp(my + c * mx)
    local = [-(math.log(pts[i + 1][1]) - math.log(pts[i][1])) / (pts[i + 1][0] - pts[i][0]) for i in range(len(pts) - 1)]
    print(f"\nFit: drift ≈ {A:.3g} · exp(−{c:.2f} β); local slopes {', '.join(f'{s:.2f}' for s in local)} (still rising slowly).")
    b_end = pts[-2][0]
    layers = 1 / (c * pts[-2][1])
    print(f"Layers to drift from β ≈ {b_end:.2f} to β ≈ {b_end - 1:.2f}: about 1/(c · drift) ≈ {layers:.1e}.")
    for name, key in (("mk_su2_d3.json", "SU(2) d=3"), ("mk_u1_d3.json", "U(1) d=3")):
        tr = load(name)[key]
        print(f"\n{key}: " + "; ".join(f"from {b}: " + " → ".join(f"{r['beta_hk']:.2f}" for r in rows) for b, rows in tr.items()))


if __name__ == "__main__":
    main()
