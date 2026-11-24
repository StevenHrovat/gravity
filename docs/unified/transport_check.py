"""Refute-only CPU check for the transport theorem (TRANSPORT.md, section 4).

Random and adversarial instances of the Lean statements; a failure would refute a statement (or a transcription of it).
    python transport_check.py > transport_check.log
"""
import math
import random

random.seed(20261123)
fails = 0


def check(name, ok):
    global fails
    if not ok:
        fails += 1
        print("FAIL", name)


# (a) bounded transport: e_{n+1} <= q e_n + r_n, r_n <= R  =>  e_n <= q^n e_0 + R/(1-q)
worst_a = 0.0
for _ in range(2000):
    q = random.uniform(0, 0.999)
    R = random.uniform(0, 2)
    e = e0 = random.uniform(0, 5)
    for n in range(1, 200):
        f = random.uniform(0, q)  # factor at most q (delta = 0)
        e = f * e + random.uniform(0, R)
        bound = q ** n * e0 + R / (1 - q)
        worst_a = max(worst_a, e / bound if bound > 0 else 0)
        check("bounded", e <= bound + 1e-12)
print(f"(a) bounded transport: worst e_n / bound = {worst_a:.6f} (<= 1)")

# (b) critical: e_{n+1} = e_n + r_n attains e_0 + sum r exactly; constant r grows without bound
e, s = 1.0, 1.0
for n in range(1000):
    r = 0.01
    e = 1.0 * e + r
    s += r
check("critical sharp", abs(e - s) < 1e-9)
print(f"(b) critical: after 1000 steps of r = 0.01, e = {e:.4f} = e_0 + sum r = {s:.4f}")

# GRH relative step: 1 + relUnc' <= (1 + relRem)(1 + relUnc), any real s, positive model factor
worst_g = 0.0
for _ in range(200000):
    E, Eh = random.uniform(-2, 2), random.uniform(1e-3, 2)
    s, sh = random.uniform(-1, 1.5), random.uniform(1e-3, 1)
    u = abs(E - Eh) / Eh
    eta = abs(s - sh) / sh
    u1 = abs(s * E - sh * Eh) / (sh * Eh)
    lhs, rhs = 1 + u1, (1 + eta) * (1 + u)
    worst_g = max(worst_g, lhs / rhs)
    check("grh rel step", lhs <= rhs * (1 + 1e-12))
print(f"GRH relative step: worst (1 + u') / ((1 + eta)(1 + u)) = {worst_g:.6f} (<= 1)")

# GRH sign: sum of log(1 + eta) < log 2 from equal start => E_n > 0 and E_n >= (1 - u_n) Eh_n
for _ in range(2000):
    E = Eh = 1.0
    budget = 0.0
    for n in range(100):
        sh = random.uniform(0.05, 1)
        eta = random.uniform(0, 0.02)
        if budget + math.log(1 + eta) >= math.log(2):
            break
        budget += math.log(1 + eta)
        s = sh * (1 + random.choice([-1, 1]) * eta)
        E, Eh = s * E, sh * Eh
        u = abs(E - Eh) / Eh
        check("grh sign", E > 0 and u < 1 and E >= (1 - u) * Eh - 1e-15)
print("GRH sign under the log-2 budget: checked on 2000 random scale chains")

# Doeblin example: rates 1/4, 1/4, adversarial perturbations of total size <= 1/10
lo, hi = 1.0, 0.0
for trial in range(4000):
    qv = 0.5
    for n in range(300):
        a = random.uniform(0, 0.1)
        sgn_a = random.choice([-1, 1]) if trial % 2 else 1
        sgn_b = random.choice([-1, 1]) if trial % 2 else -1
        ap = 0.25 + sgn_a * a
        bp = 0.25 + sgn_b * (0.1 - a)
        qv = (1 - qv) * ap + qv * (1 - bp)
        lo, hi = min(lo, qv), max(hi, qv)
check("doeblin", 0.3 - 1e-12 <= lo and hi <= 0.7 + 1e-12)
print(f"Doeblin example: perturbed law stayed in [{lo:.4f}, {hi:.4f}] (Lean bound [0.3, 0.7])")

# Identity chain (critical): P(state 0) = (1/2)(1 - rho)^n -> 0
rho, qv = 0.1, 0.5
for n in range(200):
    qv = (1 - qv) * rho + qv
check("ident", abs((1 - qv) - 0.5 * (1 - rho) ** 200) < 1e-12)
print(f"identity chain, rho = 0.1: P(state 0) after 200 steps = {1 - qv:.3e} (margin 0.5 lost)")

print("FAILURES:", fails)
