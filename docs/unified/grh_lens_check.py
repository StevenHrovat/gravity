"""Third-layer check for docs/unified/GRH-LENS.md. CPU only, a few seconds, existing saved data only (read-only):
  docs/mass-gap/weak-coupling/proof-phase/c6b-flipdata/p_table.csv   (SU(2) flip probability p(L), a torelon proxy)
  docs/mass-gap/weak-coupling/proof-phase/c8a-saturation/z2_twist_4d.log  (4D Z2 gauge theory, L = 4, log(Z_tw/Z))
  docs/mass-gap/lattice/runs-gpu/ttl_summary.json   (SU(2) effective masses m_eff(t), glueball and torelon)

1. The two profiles on the data: c = Z_tw/Z = p/(1 - p); elec(c) = szego(c)/(1 + c)^2 (the Schur-Caratheodory identity);
   the one-box bound against (mu - 1)/(mu + 1).
2. Schur-parameter consistency is vacuous: any sequence in (-1, 1) (here the beta = 2.3 twist ratios, and random ones) is the
   reflection sequence of a positive Toeplitz form (inverse Levinson; smallest eigenvalue >= 0, round trip exact).
3. Positivity along the transfer chain: the effective mass m_eff(t) should not rise with t (log-convexity); count rises
   larger than 2 combined standard errors.
4. The half-turn and the hyperbolic ledger (no data): positions on the sphere (angle 2 arctan c from the lossless point),
   Poincare distances (= electric costs), k lossless hand-over steps composed in series, the loss per step that three
   steps can afford, and the series/parallel swap elec(a b) = elec(a) (+) elec(b).
"""
import csv
import json
import math
import os
import re

import numpy as np

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
PTAB = os.path.join(ROOT, "mass-gap/weak-coupling/proof-phase/c6b-flipdata/p_table.csv")
Z2LOG = os.path.join(ROOT, "mass-gap/weak-coupling/proof-phase/c8a-saturation/z2_twist_4d.log")
TTL = os.path.join(ROOT, "mass-gap/lattice/runs-gpu/ttl_summary.json")
MU4 = 6.7744
CSTAR = (MU4 - 1) / (MU4 + 1)


def elec(c):
    return (1 - c) / (1 + c)


def szego(c):
    return 1 - abs(c) ** 2


def part1():
    print("== 1. Twist ratios on the saved data (c = Z_tw/Z)")
    print(f"   O1 needs c > (mu_4 - 1)/(mu_4 + 1) = {CSTAR:.4f}; self-dual hand-over c = {math.sqrt(2) - 1:.4f}")
    worst = 0.0
    with open(PTAB) as f:
        for r in csv.DictReader(f):
            if r["group"] != "primary":
                continue
            p, plo = float(r["p"]), float(r["p_lo"])
            c, clo = p / (1 - p), plo / (1 - plo)
            worst = max(worst, abs(elec(c) - szego(c) / (1 + c) ** 2))
            print(f"   SU(2) proxy beta {r['beta']} L {r['L']:>2} x {float(r['x']):.2f}: c = {c:.6f} (c_lo {clo:.4f})"
                  f"  elec = {elec(c):.2e}  above O1 bound: {clo > CSTAR}")
    print(f"   max |elec(c) - szego(c)/(1+c)^2| = {worst:.1e}")
    txt = open(Z2LOG).read()
    for beta, lz, dlz in re.findall(r"beta = ([0-9.]+).*?log\(Z_tw/Z\) = ([-0-9.]+) \+- ([0-9.]+)", txt, re.S):
        c = math.exp(float(lz))
        print(f"   Z2 4D L=4 beta {beta}: c = {c:.4g} (log {lz} +- {dlz})  above O1 bound: {c > CSTAR}")


def toeplitz_from_reflections(ks):
    """Inverse Levinson (closure.py convention, T[i, j] = t(i - j), real coefficients): moments with these reflections."""
    t = [1.0]
    a = np.array([1.0])
    err = 1.0
    for k in ks:
        m = len(t)
        s = sum(a[i] * t[m - i] for i in range(1, m))
        t.append(-k * err - s)
        a_ext = np.concatenate([a, [0.0]])
        a = a_ext + k * a_ext[::-1]
        err *= 1 - k * k
    n = len(t)
    return np.array([[t[abs(i - j)] for j in range(n)] for i in range(n)])


def reflections(T):
    n = T.shape[0] - 1
    t = T[:, 0]
    a, err, ks = np.array([1.0]), t[0], []
    for m in range(1, n + 1):
        k = -sum(a[i] * t[m - i] for i in range(m)) / err
        ks.append(k)
        a_ext = np.concatenate([a, [0.0]])
        a = a_ext + k * a_ext[::-1]
        err *= 1 - k * k
    return ks


def part2():
    print("== 2. Schur-parameter consistency is vacuous (Verblunsky: the reflection sequence is free in the disk)")
    seqs = {}
    with open(PTAB) as f:
        rows = [r for r in csv.DictReader(f) if r["group"] == "primary" and r["beta"] == "2.3"]
    rows.sort(key=lambda r: int(r["L"]))
    seqs["beta 2.3 twist ratios, L = " + ",".join(r["L"] for r in rows[:2])] = \
        [float(r["p"]) / (1 - float(r["p"])) for r in rows[:2]]
    rng = np.random.default_rng(7)
    seqs["random, 8 values in (-0.95, 0.95)"] = list(rng.uniform(-0.95, 0.95, 8))
    seqs["the O1 sequence, 6 values equal to 0.743"] = [CSTAR] * 6
    for name, ks in seqs.items():
        T = toeplitz_from_reflections(ks)
        back = reflections(T)
        print(f"   {name}: smallest eigenvalue {np.linalg.eigvalsh(T).min():+.3e},"
              f" round trip error {max(abs(np.array(back) - np.array(ks))):.1e}")


def part3():
    print("== 3. Effective mass along the transfer chain (positivity: m_eff(t) does not rise)")
    data = json.load(open(TTL))
    for key in ("glueball_meff", "torelon_meff"):
        pairs = rises = 0
        biggest = 0.0
        for row in data:
            pts = [(m, e) for m, e in row[key] if m is not None and e is not None and not math.isnan(m) and not math.isnan(e)]
            for (m1, e1), (m2, e2) in zip(pts, pts[1:]):
                pairs += 1
                z = (m2 - m1) / math.hypot(e1, e2) if e1 or e2 else 0.0
                biggest = max(biggest, z)
                rises += z > 2
        print(f"   {key}: {pairs} consecutive pairs over {len(data)} runs, rises > 2 sigma: {rises},"
              f" largest rise {biggest:.2f} sigma")


def oplus(a, b):
    return (a + b) / (1 + a * b)


def part4():
    print("== 4. The half-turn and the hyperbolic ledger")
    s = math.sqrt(2) - 1
    for name, c in (("lossless", 0.0), ("self-dual hand-over", s), ("two hand-over steps", oplus(s, s)),
                    ("O1 bound (mu_4)", CSTAR), ("three hand-over steps", oplus(oplus(s, s), s)), ("closure", 1.0)):
        cost = math.inf if c >= 1 else math.log((1 + c) / (1 - c))
        print(f"   {name:22s} c = {c:.6f}  sphere angle {math.degrees(2 * math.atan(c)):7.3f} deg"
              f"  Poincare distance = electric cost {cost:.6f}")
    logmu = math.log(MU4)
    print(f"   one-box floor log mu_4 = {logmu:.6f}; hand-over step cost {-math.log(s):.6f}")
    for loss in (0.0, 0.1, 0.2, 0.244, 0.3, 0.4):
        k = math.ceil(logmu / (-math.log(s) - loss)) if -math.log(s) > loss else math.inf
        print(f"   loss {loss:.3f} per composition: steps needed {k}")
    print(f"   largest loss per step that three steps can afford: {-math.log(s) - logmu / 3:.6f}")
    worst = 0.0
    rng = np.random.default_rng(3)
    for _ in range(1000):
        a, b = rng.uniform(-0.99, 0.99, 2)
        worst = max(worst, abs(elec(a * b) - oplus(elec(a), elec(b))), abs(elec(oplus(a, b)) - elec(a) * elec(b)))
    print(f"   series/parallel swap: max error over 1000 random pairs {worst:.1e}")


if __name__ == "__main__":
    part1()
    part2()
    part3()
    part4()
