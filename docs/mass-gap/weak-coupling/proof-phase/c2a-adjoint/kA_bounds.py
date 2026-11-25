"""Bounds on k_A = ||h2 Haar||_KR on the unit 3-sphere (h2(u) = <u,a><u,b>, a ⊥ b unit), the linearised W1 constant of the
adjoint channel (r2-curvature/NOTE.md 2.3: bracket [0.0531, 0.0722]). NOTE.md section 2.3 here.

Upper bound (fibre transport, exact for that plan): in coordinates (y1, y2) = rho e^{i psi}, (y3, y4) = sqrt(1 - rho^2) e^{i chi}
(y = 45-degree rotated (u1, u2)), h2 = rho^2 cos(2 psi) / 2 and Haar has q = rho^2 ~ U[0, 1], psi, chi uniform. Transport inside
every circle {q, chi fixed} along psi costs at most the arc length rho |dpsi| (>= the S^3 geodesic), and the 1D optimum on that
circle is rho * int |G(psi)| dpsi with G the cumulative mass: rho q / (2 pi). Averaging over q: 1 / (5 pi).
Lower bounds: the 1-Lipschitz test function (arcsin|y1| - arcsin|y2|)/2 (C's), and the new test function
(|y1| - |y2|)/sqrt(2) (its spherical gradient has squared norm (2 - (s1 y1 - s2 y2)^2)/2 <= 1, s = signs), whose integral is
exactly 2 sqrt(2)/(15 pi): E|y1|^3 = 8/(15 pi), E|y1| y2^2 = 4/(15 pi) on S^3.
"""
import math
import numpy as np

rng = np.random.default_rng(1)
n = 4_000_000
u = rng.normal(size=(n, 4)); u /= np.linalg.norm(u, axis=1, keepdims=True)
h2 = u[:, 0] * u[:, 1]
y1, y2 = (u[:, 0] + u[:, 1]) / math.sqrt(2), (u[:, 0] - u[:, 1]) / math.sqrt(2)
phi = 0.5 * (np.arcsin(np.abs(y1)) - np.arcsin(np.abs(y2)))
lo = float(np.mean(phi * h2)); lo_err = float(np.std(phi * h2) / math.sqrt(n))
phi2 = (np.abs(y1) - np.abs(y2)) / math.sqrt(2)
lo2 = float(np.mean(phi2 * h2)); lo2_err = float(np.std(phi2 * h2) / math.sqrt(n))
# fibre transport cost, numerical check of the closed form
q = np.linspace(0, 1, 200001)
fib = np.sqrt(q) * q / (2 * np.pi)
up_num = float(np.trapezoid(fib, q))
print(f"k_A lower bound (C's test function, MC n={n}): {lo:.5f} +- {lo_err:.5f}")
print(f"k_A lower bound (new test function (|y1|-|y2|)/sqrt2, MC): {lo2:.5f} +- {lo2_err:.5f}; closed form 2 sqrt2/(15 pi) = "
      f"{2 * math.sqrt(2) / (15 * np.pi):.5f}")
print(f"k_A upper bound (fibre transport): numerical {up_num:.6f}, closed form 1/(5 pi) = {1 / (5 * np.pi):.6f}")
print(f"Poincare upper bound (C): {math.sqrt(1 / 192):.5f}")
for name, k in (("C upper 0.0722", 0.0722), ("fibre 1/(5pi)", 1 / (5 * np.pi)), ("LP estimate 1/16", 1 / 16),
                ("new lower 2sqrt2/(15pi)", 2 * math.sqrt(2) / (15 * np.pi)), ("C lower 0.0531", 0.0531)):
    print(f"pure adjoint linearised W1 window b_A* = 1/(48 k_A) with {name}: {1 / (48 * k):.4f}")
