"""c9b-adjoint, check N1 (pre-registered in NOTE.md section 6).

(a)-(c): column arithmetic for the base fit at L sqrt(sigma) = 2.80 (couplings from ../c4d-certified/NOTE.md).
(d): randomised test of the tilt lemma (Lean: ProofPhase.Adjoint2.abs_tiltAvg_add_sub_le).
CPU only, numpy only.
"""
import math
import numpy as np

print("=== N1 (a)-(c): columns of the base fit ===")
fits = {
    "box": dict(Fts=0.0545, Fss=0.1725, Ats=0.0011, Ass=0.0020),
    "central(F); box(A)": dict(Fts=0.0540, Fss=0.1711, Ats=0.0011, Ass=0.0020),
}
links = {"spatial": dict(ts=6, ss=12, plaq_ts=2, plaq_ss=4), "temporal": dict(ts=18, ss=0, plaq_ts=6, plaq_ss=0)}
ok = {"P1": True, "P2": False, "P3": True, "P4": False}
for name, c in fits.items():
    for lt, n in links.items():
        c1 = n["ts"] * math.tanh(c["Fts"]) + n["ss"] * math.tanh(c["Fss"])
        c0 = n["ts"] * math.tanh(2 * c["Ats"] / 3) + n["ss"] * math.tanh(2 * c["Ass"] / 3)
        m0 = n["ts"] * 8 * c["Ats"] / 3 + n["ss"] * 8 * c["Ass"] / 3
        m1 = n["ts"] * 4 * c["Fts"] + n["ss"] * 4 * c["Fss"]
        be = 4 * c["Fts"] * n["plaq_ts"] + 4 * c["Fss"] * n["plaq_ss"]
        budget = math.log(3) - m0
        print(f"{name:20s} {lt:8s}  c0={c0:.4f}  c1={c1:.4f}  c0+c1={c0 + c1:.4f}  "
              f"m0={m0:.4f}  m1={m1:.3f}  budget(log3-m0)={budget:.4f}  BE row={be:.3f} (Ric=2)")
        ok["P1"] &= c0 < 0.05
        ok["P3"] &= (m0 < 0.15) and (budget > 0.9)
        if lt == "spatial":
            ok["P2"] |= (c0 + c1) > 1
            ok["P4"] |= be > 2
for k, v in ok.items():
    print(k, "PASS" if v else "FAIL")

print("=== N1 (d): tilt lemma, randomised ===")
rng = np.random.default_rng(20261123)
worst, worst_sharp, viol, viol_sharp = 0.0, 0.0, 0, 0
for t in range(20000):
    n = int(rng.integers(2, 51))
    nu = rng.dirichlet(np.ones(n) * rng.uniform(0.2, 3))
    f = rng.normal(0, rng.uniform(0, 3), n)
    delta = rng.uniform(0, 3)
    g = rng.uniform(0, 1, n)
    g = (g - g.min()) / max(g.max() - g.min(), 1e-12) * delta  # oscillation exactly delta
    F = rng.normal(0, 1, n)
    if rng.random() < 0.3:  # extremal +-1 test functions
        F = np.sign(rng.normal(0, 1, n))
    w1 = nu * np.exp(f)
    w2 = w1 * np.exp(g)
    e1 = (F * w1).sum() / w1.sum()
    e2 = (F * w2).sum() / w2.sum()
    c = (F.max() + F.min()) / 2
    M = np.abs(F - c).max()
    if M == 0:
        continue
    diff = abs(e2 - e1)
    bound = M * (math.exp(delta) - 1)
    sharp = 2 * M * math.tanh(delta / 4)
    if bound > 0:
        r = diff / bound
        worst = max(worst, r)
        viol += r > 1 + 1e-12
    if sharp > 0:
        rs = diff / sharp
        worst_sharp = max(worst_sharp, rs)
        viol_sharp += rs > 1 + 1e-12
print(f"max diff/(M(e^d-1)) = {worst:.4f}, violations = {viol}")
print(f"max diff/(osc F tanh(d/4)) = {worst_sharp:.4f}, violations = {viol_sharp}")
print("P5", "PASS" if viol == 0 and viol_sharp == 0 else "FAIL")
