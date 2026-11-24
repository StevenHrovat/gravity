"""Arithmetic on Leg B's admissibility data (no simulation; r3-dmp NOTE section 3.4).

Per-plaquette fraction f(beta) of plaquettes with shortfall 2 - Re tr U above eps = 1.5 (Leg B, bulk), and our own a*sqrt(sigma)
from the TTL scan (results/ttl_summary.json). Reports the density of inadmissible plaquettes per physical volume,
f / (a sqrt(sigma))^4 (per plaquette orientation, in units of sigma^2), and the two exponential rates in beta.
"""
import json, math, os

here = os.path.dirname(os.path.abspath(__file__))
rows = json.load(open(os.path.join(here, "..", "..", "..", "results", "ttl_summary.json")))
asq = {round(r["beta"], 2): r["a_sqrt_sigma"] for r in rows if r.get("a_sqrt_sigma")}
frac = {2.3: 5.3e-3, 2.4: 3.3e-3, 2.5: 2.1e-3}
print("beta  f          a*sqrt(sigma)     density f/(a sqrt sigma)^4")
dens = {}
for b, f in frac.items():
    a, da = asq[b]
    d = f / a**4
    dd = d * 4 * da / a
    dens[b] = d
    print(f"{b:.1f}  {f:.2e}   {a:.4f} +- {da:.4f}   {d:.3f} +- {dd:.3f} (a-error only)")
bs = sorted(frac)
rf = math.log(frac[bs[0]] / frac[bs[-1]]) / (bs[-1] - bs[0])
ra = 4 * math.log(asq[bs[0]][0] / asq[bs[-1]][0]) / (bs[-1] - bs[0])
print(f"fraction falls like exp(-{rf:.2f} beta); (a sqrt sigma)^-4 grows like exp(+{ra:.2f} beta); net density grows like exp(+{ra-rf:.2f} beta)")
# one-loop SU(2) reference: log(1/a) ~ beta/(4 N b0), b0 = 11 N/(48 pi^2): 4 log(1/a) grows like 4 beta/(4 N b0)
N = 2; b0 = 11 * N / (48 * math.pi**2)
print(f"one-loop asymptotic rate for (a Lambda)^-4: exp(+{4/(4*N*b0):.2f} beta) (asymptotic scaling not reached at beta 2.3-2.5)")
