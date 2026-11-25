"""REDESIGN.md derivation checks for KR_D (closed form and quadrature; no samples, no data). Seconds.
1. Linearisation: sqrt(d.M_mid d) against the exact nonlinear H^-1 split norm kr_upper(theta_0, theta_1), for the moves of the plan.
2. The ratio KR_D / TV at those moves (how conservative the W1 bound is relative to TV, for orientation)."""
import json, math
import numpy as np
import ir_condlaw as cl

cpl = cl.FIT280
e0 = np.array([1.0, 0, 0, 0])


def theta_for(staples):
    A = np.zeros(4); adj = []
    for cls, sv in staples:
        A += cpl["F_" + cls] * sv
        adj.append((cpl["A_" + cls], sv))
    return cl.exact_theta(A, adj)


def rot(delta):  # staple of the moved ss plaquette after moving the partner by geodesic delta about the k axis: s -> s e^{delta k}
    return np.array([math.cos(delta), 0, 0, math.sin(delta)])


rows = []
base = [("ss", e0)] * 4 + [("ts", e0)] * 2
for name, s_new in (("flip", -e0), ("rot90 (pi/4)", rot(math.pi / 4)), ("W1 move 0.5 rad", rot(0.5)), ("W1 move 0.2 rad", rot(0.2))):
    t0 = theta_for(base)
    t1 = theta_for([("ss", s_new)] + base[1:])
    d = t1 - t0
    Mm = (cl.h1_metric(t0) + cl.h1_metric(t1)) / 2
    lin = math.sqrt(d @ Mm @ d)
    exact = cl.kr_upper(t0, t1)
    rows.append({"move": name, "KR_upper_exact": exact, "KR_D_linear": lin, "rel_diff": (lin - exact) / exact, "TV": cl.tv(t0, t1),
                 "D_half": 0.5 * math.sqrt(cl.d2_exact(t0, t1))})
for r in rows:
    print(json.dumps({k: (round(v, 6) if isinstance(v, float) else v) for k, v in r.items()}))
