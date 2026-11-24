"""Third-layer checks for OPEN-STEPS-DMP.md (CPU, seconds, no saved data needed).

Part A (Yang-Mills, O1 calibration): two-dimensional SU(2) Wilson theory on a torus of A plaquettes is exactly
solvable by the character expansion. There is no outside (the plaquettes are independent), so it is the control case
for the hyperbolic ledger of GRH-LENS 6.4: one encoder number c(A) = Z_tw/Z, electric cost F_e(A) = log(Z_e0/Z_e1),
and the loss per join l(A1, A2) = F_e(A1) + F_e(A2) - F_e(A1 + A2). Classical formulas:
    Z    = sum_n r_n^A,  Z_tw = sum_n (-1)^(n-1) r_n^A,  r_n = I_n(beta)/I_1(beta)  (n = 2j + 1),
    Z_e0 = sum over odd n (integer spin), Z_e1 = sum over even n (half-integer spin).

Part B (GRH, the finite model where the sign is a theorem): a genus-2 curve y^2 = f(x) over F_p. Its zeta function is
P(T)/((1 - T)(1 - pT)) with deg P = 2g = 4: a finite existence space with a tick log p. The moments of the four atoms
beta_i = alpha_i/sqrt(p) come from point counts alone (the prime side), the Szego recursion runs on their Toeplitz
form, and Weil's theorem says |k_m| < 1 for m < 4 and |k_4| = 1 (closure). A fake atom set with one quartet off the circle
is the control.

Run: python docs/unified/open_steps_check.py > docs/unified/open_steps_check.log
"""
import numpy as np
from scipy.special import iv

np.set_printoptions(precision=6, suppress=True)

# ---------------------------------------------------------------- Part A
print("== Part A: 2D SU(2) on a torus, the hyperbolic ledger without an outside [classical formulas, numerical]")
LOG_MU4 = np.log(6.77)          # 1.913, the one-box floor of ENCODER.md 6
C_O1 = (6.77 - 1) / (6.77 + 1)  # 0.743
NMAX = 60


def sectors(beta, A):
    n = np.arange(1, NMAX + 1)
    if beta == "continuum":  # heat kernel: r_n = exp(-(n^2 - 1) A / 8), A in units 1/sigma_leading (sigma = 3/8)
        r = np.exp(-(n * n - 1) / 8.0)
    else:
        r = iv(n, beta) / iv(1, beta)
    w = r ** A
    z_e0 = w[n % 2 == 1].sum()
    z_e1 = w[n % 2 == 0].sum()
    return z_e0, z_e1


def fe(beta, A):
    z0, z1 = sectors(beta, A)
    return np.log(z0 / z1)


def c_of(beta, A):
    z0, z1 = sectors(beta, A)
    return (z0 - z1) / (z0 + z1)


for beta in (1.0, 2.3, 4.0, 8.0, 32.0, "continuum"):
    sigma = 3 / 8.0 if beta == "continuum" else np.log(iv(1, beta) / iv(2, beta))  # string tension per plaquette (leading term)
    # area (real-valued) at the self-dual point and at the O1 floor, by bisection on F_e(A)
    def solve(target):
        lo, hi = 1e-6, 200.0
        for _ in range(200):
            mid = 0.5 * (lo + hi)
            if fe(beta, mid) < target:
                lo = mid
            else:
                hi = mid
        return 0.5 * (lo + hi)
    a_h = solve(np.log(1 + np.sqrt(2)))
    a_o1 = solve(LOG_MU4)
    print(f"beta={beta!s:>9}  sigma/plaq={sigma:.6f}  self-dual area A_h={a_h:.6f}  O1 area={a_o1:.6f}  ratio={a_o1/a_h:.6f}")
    for k in (1, 2, 3):
        Fk = fe(beta, k * a_h)
        print(f"    {k} hand-over box(es) in series: c={c_of(beta, k*a_h):.6f}  F_e={Fk:.6f}  "
              f"k*0.881={k*np.log(1+np.sqrt(2)):.6f}  loss per join={(k*np.log(1+np.sqrt(2)) - Fk)/max(k-1,1):+.3e}  "
              f"clears O1: {Fk > LOG_MU4}")
    # superadditivity defect over a grid of integer areas
    worst = -np.inf
    grid = a_h * np.linspace(0.05, 6.0, 120)
    for A1 in grid:
        for A2 in grid:
            worst = max(worst, fe(beta, A1) + fe(beta, A2) - fe(beta, A1 + A2))
    print(f"    max loss per join over areas 0.05..6 A_h: {worst:+.3e}  (threshold for three boxes: 0.244)")

# ---------------------------------------------------------------- Part B
print()
print("== Part B: genus-2 curve over F_p, Szego steps from point counts alone [Weil's theorem; numerical]")


class Fp2:
    """F_{p^2} = F_p[w]/(w^2 - nr), nr a non-residue."""
    def __init__(self, p):
        self.p = p
        self.nr = next(a for a in range(2, p) if pow(a, (p - 1) // 2, p) == p - 1)

    def mul(self, x, y):
        p = self.p
        return ((x[0] * y[0] + self.nr * x[1] * y[1]) % p, (x[0] * y[1] + x[1] * y[0]) % p)

    def add(self, x, y):
        return ((x[0] + y[0]) % self.p, (x[1] + y[1]) % self.p)

    def pw(self, x, e):
        r = (1, 0)
        while e:
            if e & 1:
                r = self.mul(r, x)
            x = self.mul(x, x)
            e >>= 1
        return r


def count_points(coeffs, p):
    """N_1, N_2 for y^2 = f(x), deg f = 5 (one point at infinity)."""
    def f1(x):
        return sum(c * pow(x, i, p) for i, c in enumerate(coeffs)) % p
    n1 = 1
    for x in range(p):
        v = f1(x)
        n1 += 1 if v == 0 else (2 if pow(v, (p - 1) // 2, p) == 1 else 0)
    F = Fp2(p)
    q = p * p
    n2 = 1
    for a in range(p):
        for b in range(p):
            x = (a, b)
            v = (0, 0)
            xp = (1, 0)
            for c in coeffs:
                v = F.add(v, F.mul((c % p, 0), xp))
                xp = F.mul(xp, x)
            if v == (0, 0):
                n2 += 1
            else:
                n2 += 2 if F.pw(v, (q - 1) // 2) == (1, 0) else 0
    return n1, n2


def szego(beta_atoms, mmax):
    t = np.array([np.mean(beta_atoms ** m) for m in range(mmax + 1)])  # Toeplitz moments t(m)
    a = np.array([1.0 + 0j])
    E = t[0].real
    ks = []
    for m in range(1, mmax + 1):
        acc = sum(a[j] * t[m - j] for j in range(m))
        k = -acc / E
        ks.append(k)
        a = np.concatenate([a, [0]]) + k * np.concatenate([[0], np.conj(a[::-1])])
        E = E * (1 - abs(k) ** 2)
        if abs(E) < 1e-13:
            break
    return ks


def atoms_from_counts(n1, n2, p):
    s1 = p + 1 - n1
    s2 = p * p + 1 - n2
    e1 = s1
    e2 = (s1 * s1 - s2) // 2
    # alpha_i are the roots of T^4 - e1 T^3 + e2 T^2 - p e1 T + p^2
    alphas = np.roots([1, -e1, e2, -p * e1, p * p])
    return alphas / np.sqrt(p), (s1, s2, e1, e2)


curves = [(7, [1, 2, 0, 3, 0, 1]), (11, [3, 1, 4, 1, 5, 1]), (13, [2, 7, 1, 8, 2, 1]), (31, [5, 0, 2, 0, 9, 1])]
for p, coeffs in curves:
    n1, n2 = count_points(coeffs, p)
    b, (s1, s2, e1, e2) = atoms_from_counts(n1, n2, p)
    ks = szego(b, 6)
    print(f"p={p:3d} f={coeffs} N1={n1} N2={n2} (a1={-s1}, e2={e2})  |atoms|={np.abs(b)}")
    print(f"    |k_m| (Szego on the atom moments) = {[round(float(abs(k)), 12) for k in ks]}")

print()
print("== Part B control: a fake atom set: one on-circle pair plus an off-circle quartet (|beta| = 1.15 and 1/1.15)")
p = 13
th = (0.7, 2.1)
r = 1.15
fake = np.array([np.exp(1j * th[0]), np.exp(-1j * th[0]),
                 r * np.exp(1j * th[1]), r * np.exp(-1j * th[1]),
                 np.exp(1j * th[1]) / r, np.exp(-1j * th[1]) / r])  # z, conj z, 1/conj z, 1/z: the off-line quartet
ks = szego(fake, 8)
print(f"    |k_m| = {[round(float(abs(k)), 6) for k in ks]}   (a step with |k| > 1 overdraws the margin)")
