"""Third-layer check of the encoder (docs/unified/ENCODER.md). CPU only, a few seconds.

1. GRH: in the finite zero model of closure.py, the Szego reflection coefficient k_m is the encoder's reflection
   coefficient: the overlap of u = z phi_{m-1} with its mirror image u* (degree-m reversal and conjugation), divided by
   <u, u>. The shared root <u*, u*> = <u, u> holds in both models (on and off the line); what fails off the line is
   positivity (a negative eigenvalue of a Toeplitz section), and with it |k| <= 1.
2. Yang-Mills: the electric profile elec(c) = (1 - c)/(1 + c) is the odd share over the even share under an involution
   (Z_{e=1}/Z_{e=0} for Z = Tr T, Z_tw = Tr U T); it is its own inverse; the self-dual point is sqrt 2 - 1 (cost 0.881);
   O1 needs Z_tw/Z above (mu - 1)/(mu + 1).
3. NP vs coNP: survival shares of lines under single restrictions (fix one variable to one value), by brute force:
   a clause of width w: 1 - w/(2n); the threshold line "at least k of B" (k >= 2): 1; the parity line over B (|B| >= 2): 1.
   The parity label of a fixed-parity boundary law has reflection coefficient 0 under a flip: lossless.
"""
import itertools
import numpy as np

GAMMAS = [14.134725142, 21.022039639, 25.010857580, 30.424876126, 32.935061588]
EPS = 0.3


def model(offset=0.0, which=None):
    atoms, weights = [], []
    for i, g in enumerate(GAMMAS):
        w = 1.0 / (0.25 + g * g)
        for s in (+1, -1):
            if which == i and offset:
                z = np.exp(1j * s * g * EPS) * np.exp(offset * EPS)
                atoms += [z, 1 / np.conj(z)]
                weights += [w, w]
            else:
                atoms.append(np.exp(1j * s * g * EPS))
                weights.append(w)
    return atoms, weights


def gram(atoms, weights, n):
    """G[i, j] = <z^i, z^j> = t(j - i), t(k) = sum_a w_a z_a^k, t(-k) = conj t(k) (the toepForm convention)."""
    t = {k: sum(w * z ** k for z, w in zip(atoms, weights)) for k in range(n + 1)}
    for k in range(1, n + 1):
        t[-k] = np.conj(t[k])
    return np.array([[t[j - i] for j in range(n + 1)] for i in range(n + 1)])


def form(G, p, q):
    return np.conj(p) @ G @ q


def levinson_k(G, n):
    """Reflection coefficients from the determinant ratios: 1 - |k_m|^2 = D_m D_{m-2} / D_{m-1}^2."""
    D = [1.0] + [np.linalg.det(G[: m + 1, : m + 1]).real for m in range(n + 1)]
    return [1 - D[m + 1] * D[m - 1] / D[m] ** 2 for m in range(1, n + 1)]  # this is |k_m|^2


def grh():
    print("== 1. GRH: Szego step = encoder (u, its mirror image u*)")
    for label, off in (("on the line", 0.0), ("one pair off the line by 0.05", 0.05)):
        atoms, weights = model(off, which=0)
        n = len(atoms)
        G = gram(atoms, weights, n)
        k2 = levinson_k(G, n)
        print(f"-- {label}: {n} atoms; smallest eigenvalue of the full section {np.linalg.eigvalsh(G).min():+.3e}")
        worst_root, worst_match = 0.0, 0.0
        for m in range(1, n + 1):
            # monic phi_{m-1}: coefficients b (degree m-1), orthogonal to 1 .. z^{m-2}
            if m == 1:
                phi = np.array([1.0 + 0j])
            else:
                A = G[: m - 1, : m - 1]
                rhs = -G[: m - 1, m - 1]
                phi = np.concatenate([np.linalg.solve(A, rhs), [1.0]])
            u = np.concatenate([[0.0], phi])            # z phi_{m-1}, degree m
            ustar = np.conj(u[::-1])                    # degree-m reversal and conjugation
            Gm = G[: m + 1, : m + 1]
            nu, nus = form(Gm, u, u).real, form(Gm, ustar, ustar).real
            c = form(Gm, u, ustar) / nu
            worst_root = max(worst_root, abs(nus - nu) / abs(nu))
            worst_match = max(worst_match, abs(abs(c) ** 2 - k2[m - 1]))
            if m in (1, 9, n - 1, n):
                print(f"   step {m:2d}  |c| = {abs(c):.9f}  |k| = {np.sqrt(abs(k2[m - 1])):.9f}"
                      f"  factor 1-|c|^2 = {1 - abs(c) ** 2:+.3e}")
        print(f"   max relative |<u*,u*> - <u,u>| (shared root): {worst_root:.1e}")
        print(f"   max | |c|^2 - |k|^2 | over all steps (encoder = Szego): {worst_match:.1e}")


def elec(c):
    return (1 - c) / (1 + c)


def ym():
    print("== 2. Yang-Mills: electric profile")
    rng = np.random.default_rng(1)
    d = 8
    Q, _ = np.linalg.qr(rng.normal(size=(d, d)))
    U = Q @ np.diag([1, 1, 1, 1, 1, -1, -1, -1]) @ Q.T      # the one rotation: an involution, U^2 = 1
    Pp, Pm = (np.eye(d) + U) / 2, (np.eye(d) - U) / 2
    A = rng.normal(size=(d, d))
    B = rng.normal(size=(d, d))
    T = Pp @ (A @ A.T) @ Pp + Pm @ (B @ B.T) @ Pm + 0.1 * np.eye(d)   # positive, commutes with U
    Z, Ztw = np.trace(T), np.trace(U @ T)
    print(f"   Z_(e=1)/Z_(e=0) = {np.trace(Pm @ T) / np.trace(Pp @ T):.12f}   elec(Z_tw/Z) = {elec(Ztw / Z):.12f}")
    psi = rng.normal(size=d)
    c = psi @ U @ psi / (psi @ psi)
    print(f"   |psi - U psi|^2 / |psi + U psi|^2 = "
          f"{np.sum((psi - U @ psi) ** 2) / np.sum((psi + U @ psi) ** 2):.12f}   elec(c) = {elec(c):.12f}")
    print(f"   duality elec(elec(0.3)) = {elec(elec(0.3)):.12f}")
    s = np.sqrt(2) - 1
    print(f"   self-dual point sqrt2 - 1 = {s:.9f}: elec = {elec(s):.9f}, cost -log = {-np.log(s):.9f}")
    for mu in (3.0, 6.7744):
        print(f"   O1 at mu = {mu}: needs Z_tw/Z > (mu-1)/(mu+1) = {(mu - 1) / (mu + 1):.6f}"
              f" (factor < 1/mu = {1 / mu:.6f}); hand-over has {s:.6f}")


def np_side(n=6):
    print(f"== 3. NP vs coNP: survival share under single restrictions, n = {n} variables")
    pts = list(itertools.product([False, True], repeat=n))
    restr = [(x, v) for x in range(n) for v in (False, True)]

    def share(line):
        alive = 0
        for x, v in restr:
            forced = all(line(a) for a in pts if a[x] == v)
            alive += not forced
        return alive / len(restr)

    for w in (1, 2, 3, 6):
        clause = lambda a, w=w: any(a[i] for i in range(w))
        print(f"   clause of width {w}: share {share(clause):.6f}   1 - w/2n = {1 - w / (2 * n):.6f}")
    B = range(n)
    for k in (2, 3, 4):
        thr = lambda a, k=k: sum(a[i] for i in B) >= k
        print(f"   threshold 'at least {k} of {n}': share {share(thr):.6f}")
    par = lambda a: sum(a) % 2 == 1
    print(f"   parity of all {n}: share {share(par):.6f}")
    # parity label: inside law uniform on even boundary configurations; R flips variable 0
    psi = np.array([1.0 if sum(a) % 2 == 0 else 0.0 for a in pts])
    flip = [pts.index(tuple((not a[0],) + a[1:])) for a in pts]
    Rpsi = psi[flip]
    print(f"   parity label: c = <psi, R psi>/<psi, psi> = {psi @ Rpsi / (psi @ psi):.6f} (Szego factor 1, elec factor 1)")


if __name__ == "__main__":
    grh()
    ym()
    np_side()
