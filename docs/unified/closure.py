"""Finite zero model: reflection (Verblunsky) coefficients of the Toeplitz form t(k) = sum_j w_j z_j^k.
Checks: all zeros on the line -> |k_m| < 1 until the atoms are exhausted, then |k| = 1 exactly (factor 1 - |k|^2 = 0);
one zero pair off the line -> some |k_m| > 1 (a negative factor: the margin is overdrawn)."""
import numpy as np

GAMMAS = [14.134725142, 21.022039639, 25.010857580, 30.424876126, 32.935061588]
EPS = 0.3


def moments(atoms, weights, n):
    return np.array([sum(w * z ** k for z, w in zip(atoms, weights)) for k in range(n + 1)])


def reflection(t, n):
    """Levinson-Durbin on the Hermitian Toeplitz matrix T[i,j] = t(i-j), t(-k) = conj t(k)."""
    a = np.array([1.0 + 0j])
    err = t[0].real
    ks, errs = [], [err]
    for m in range(1, n + 1):
        acc = sum(a[i] * t[m - i] for i in range(m))
        k = -acc / err
        ks.append(k)
        a_ext = np.concatenate([a, [0]])
        a = a_ext + k * np.conj(a_ext[::-1])
        err = err * (1 - abs(k) ** 2)
        errs.append(err)
        if abs(err) < 1e-12 * t[0].real:
            break
    return ks, errs


def model(offset=0.0, which=None):
    atoms, weights = [], []
    for i, g in enumerate(GAMMAS):
        w = 1.0 / (0.25 + g * g)
        for s in (+1, -1):
            if which == i and offset:
                z = np.exp(1j * s * g * EPS) * np.exp(offset * EPS)
                atoms += [z, 1 / np.conj(z)]   # beta and 1 - beta: the functional-equation pair
                weights += [w, w]
            else:
                atoms.append(np.exp(1j * s * g * EPS))
                weights.append(w)
    return atoms, weights


for label, off in (("all zeros on the line", 0.0), ("one zero pair off the line by 0.05", 0.05)):
    atoms, weights = model(off, which=0)
    t = moments(atoms, weights, len(atoms) + 1)
    ks, errs = reflection(t, len(atoms))
    print(f"{label}: {len(atoms)} atoms")
    for m, k in enumerate(ks, 1):
        print(f"  step {m:2d}  |k| = {abs(k):.12f}   factor 1-|k|^2 = {1 - abs(k)**2:+.3e}")
