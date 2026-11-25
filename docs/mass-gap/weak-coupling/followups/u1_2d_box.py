"""Follow-up experiment 2 (route (c)): 2D compact U(1), W-form box influence (GDS coefficient) of thin squares vs box size.

Pre-registered in PREREG-FOLLOWUPS.md (Experiment 2). CPU only, one process.

Exact structure: modulo the interior gauge group the thin square V_l is the 4l face links plus the l^2 inner plaquettes, i.e.
N = l^2 + 4l independent von Mises(beta) angles conditioned on their signed sum = Phi_b (total boundary flux). A parallel shell link
(type P, and the corner links) shifts the centre of one face variable; a dangling shell link (type D) is a boundary gauge rotation
that shifts the two face variables at its site rigidly and oppositely. Metric: sum |delta f| + earth mover cost (Manhattan) on the
l x l plaquette grid.

  lower bound (rigorous for k^W): test functions sum_gamma psi_gamma(Y_gamma) over link-disjoint sums of link angles
     P_i: f_i alone, every other face link alone, nested cuts around the plaquette at f_i (l1 balls B_r)
     D:   f_left, f_right, the 1-plaquette path through the inner link at the site
  upper bound (explicit coupling at the given Phi_b):
     D:   3 * E_u[ rigid-shift W1 rate of the two-variable conditional law ]   (<= 3 = rigid gauge rotation)
     P_i: Knothe-Rosenblatt flow, far variables first, f_i last, optimal 1D circle velocity per step, flux routed to f_i along
          Manhattan paths; expected cost by Monte Carlo over exact sequential samples (mean + 2 s.e.)

gamma(l) = [2 sum_i k(P_i) + 2 (l-1) k(D) + 4 k(P_0)] / (l (l+1))   (per direction; k(D) does not depend on the site)

Usage: py u1_2d_box.py lower  beta1,beta2,...  lmax            -> u1_2d_lower.json
       py u1_2d_box.py upper  beta  l1,l2,...  [S] [phis]      -> u1_2d_upper.json (merged)
       py u1_2d_box.py validate                                -> u1_2d_validate.json
"""
import json
import os
import sys
import time

os.environ.setdefault("CUDA_VISIBLE_DEVICES", "-1")
import numpy as np
from scipy.special import ive

HERE = os.path.dirname(os.path.abspath(__file__))
UPPER = None  # set in main
PHIS = [0.0, np.pi / 4, np.pi / 2, 3 * np.pi / 4, np.pi]


class Circle:
    """Fourier tools for sums of m iid von Mises(beta) angles on a grid of [-pi, pi)."""

    def __init__(self, beta):
        self.beta = beta
        width = 1 / np.sqrt(beta)
        G = 2048
        while 2 * np.pi / G > width / 16:
            G *= 2
        self.G = G
        self.x = -np.pi + 2 * np.pi * np.arange(G) / G
        self.dx = 2 * np.pi / G
        nmax = int(np.ceil(np.sqrt(2 * beta * 40))) + 10
        n = np.arange(1, nmax + 1)
        r = ive(n, beta) / ive(0, beta)
        keep = r > 1e-300
        self.n = n[keep]
        self.lr = np.log(r[keep])  # log r_n
        self.cos = np.cos(np.outer(self.n, self.x))
        self.sin = np.sin(np.outer(self.n, self.x))
        self.logp = beta * (np.cos(self.x) - 1)  # unnormalised log density of one variable

    def coef(self, m, eps=1e-17):
        c = np.exp(m * self.lr)
        k = np.searchsorted(-c, -eps)  # c is decreasing in n
        return c[:max(k, 1)], max(k, 1)

    def g(self, m, shift=0.0, deriv=False):
        """density (times 2 pi) of the sum of m variables evaluated at x + shift; deriv: d/dy."""
        c, k = self.coef(m)
        n = self.n[:k]
        if shift == 0.0:
            C, S = self.cos[:k], self.sin[:k]
        else:
            C, S = np.cos(np.outer(n, self.x + shift)), np.sin(np.outer(n, self.x + shift))
        if deriv:
            return -2 * (c * n) @ S
        return 1 + 2 * c @ C

    def g_at(self, m, y, deriv=False):
        c, k = self.coef(m)
        n = self.n[:k]
        if deriv:
            return float(-2 * (c * n) @ np.sin(n * y))
        return float(1 + 2 * c @ np.cos(n * y))

    def g_reflect(self, m, Phi, deriv=False):
        """g_m(Phi - x) on the grid (and its derivative w.r.t. its argument)."""
        c, k = self.coef(m)
        n = self.n[:k]
        arg = np.outer(n, Phi - self.x)
        if deriv:
            return -2 * (c * n) @ np.sin(arg)
        return 1 + 2 * c @ np.cos(arg)


def median_abs(F, dx):
    return float(np.abs(F - np.median(F)).sum() * dx)


def omega_in(C, m, N, Phi):
    """W1 rate of the law of Y = sum over a set of m variables containing the shifted one (all N conditioned on sum = Phi)."""
    if m >= N:
        return 0.0
    if m == 0:
        return 0.0
    gm, gmd = C.g(m), C.g(m, deriv=True)
    gr = C.g_reflect(N - m, Phi)
    A0 = gm * gr
    At = -gmd * gr
    Z, Zt = A0.sum() * C.dx, At.sum() * C.dx
    drho = At / Z - A0 * Zt / Z ** 2
    return median_abs(np.cumsum(drho) * C.dx, C.dx)


def omega_rigid(C, m, N, Phi):
    """W1 rate of a rigid shift of the law of Y = sum over m variables (all N conditioned on sum = Phi)."""
    rho = C.g(m) * C.g_reflect(N - m, Phi)
    rho = rho / (rho.sum() * C.dx)
    return median_abs(rho, C.dx)


def geometry(l, i):
    """Variables: inner plaquettes (a,b) and faces. Returns list of (kind, distance to plaquette (i,0)), perturbed = ('B', i)."""
    d = lambda a, b: abs(a - i) + b
    var = []
    for a in range(l):
        for b in range(l):
            var.append(("P", d(a, b)))
    for j in range(l):
        if j != i:
            var.append(("F", d(j, 0)))
        var.append(("F", d(j, l - 1)))
        var.append(("F", d(0, j)))
        var.append(("F", d(l - 1, j)))
    return var  # perturbed face excluded; len = N - 1


_CUT = {}


def cut_sizes(l, i):
    if (l, i) in _CUT:
        return _CUT[(l, i)]
    a_ = np.arange(l)
    A, B = np.meshgrid(a_, a_, indexing="ij")
    dP = np.sort((np.abs(A - i) + B).ravel())
    dF = np.sort(np.concatenate([np.abs(a_ - i), np.abs(a_ - i) + (l - 1), i + a_, (l - 1 - i) + a_]))
    out = []
    r = 0
    while True:
        nP = np.searchsorted(dP, r, side="right")
        nF = np.searchsorted(dF, r, side="right")
        out.append(int(nP + nF))
        if nP == l * l:
            break
        r += 1
    _CUT[(l, i)] = out
    return out


def _cut_sizes_slow(l, i):
    out = []
    r = 0
    while True:
        nP = sum(1 for a in range(l) for b in range(l) if abs(a - i) + b <= r)
        nF = sum(1 for j in range(l) if abs(j - i) <= r)  # bottom
        nF += sum(1 for j in range(l) if abs(j - i) + (l - 1) <= r)  # top
        nF += sum(1 for j in range(l) if i + j <= r)  # left
        nF += sum(1 for j in range(l) if (l - 1 - i) + j <= r)  # right
        out.append(nP + nF)
        if nP == l * l:
            break
        r += 1
    return out


def lower_bounds(C, l, Phi):
    N = l * l + 4 * l
    cache = {}

    def w(m):
        if m not in cache:
            cache[m] = omega_in(C, m, N, Phi)
        return cache[m]

    kP = []
    for i in range(l):
        k = w(1) + (4 * l - 1) * w(N - 1) + sum(w(m) for m in cut_sizes(l, i))
        kP.append(k)
    kD = 2 * omega_rigid(C, 1, N, Phi) + omega_rigid(C, 2, N, Phi)
    return kP, kD


def upper_D(C, l, Phi):
    """3 * E_u[min_c int |pi(x|u) - c|], u = x_l + x_r ~ g_2(u) g_{N-2}(Phi - u)."""
    N = l * l + 4 * l
    rho_u = C.g(2) * C.g_reflect(N - 2, Phi)
    rho_u = rho_u / (rho_u.sum() * C.dx)
    lp = C.logp
    tot = 0.0
    # pi(x|u) propto p(x) p(u - x): evaluate on the grid by circular shift (u on the grid)
    G = C.G
    idx = np.arange(G)
    sel = np.nonzero(rho_u * C.dx > 1e-14)[0]
    for k in sel:
        # p(u - x): u = x[k]; u - x[j] = x[k] - x[j] -> grid index (k - j + G/2) mod G (x[G/2] = 0)
        j2 = (k - idx + G // 2) % G
        a = lp + lp[j2]
        pi = np.exp(a - a.max())
        pi /= pi.sum() * C.dx
        tot += rho_u[k] * C.dx * median_abs(pi, C.dx)
    return 3 * tot


def upper_P(C, l, i, Phi, S, rng):
    var = geometry(l, i)
    var.sort(key=lambda v: -v[1])  # far first
    N = l * l + 4 * l
    beta = C.beta
    u = np.full(S, Phi)
    w = -np.ones(S)
    cost = np.zeros(S)
    p = np.exp(C.logp)
    for j, (kind, dist) in enumerate(var):
        m = N - j - 1  # variables remaining after this one (including the perturbed one)
        cj = dist + (1 if kind == "F" else 0)
        c, k = C.coef(m)
        if k <= 1 and c[0] < 1e-15:
            x = rng.vonmises(0.0, beta, S)  # remaining sum uniform: conditional = p, flow zero
            u = np.angle(np.exp(1j * (u - x)))
            continue
        n = C.n[:k]
        cu, su = np.cos(np.outer(u, n)), np.sin(np.outer(u, n))  # (S, k)
        cc, ss = C.cos[:k], C.sin[:k]  # (k, G)
        # g(u - x) = 1 + 2 sum c_n cos n(u - x); g'(u - x) = -2 sum n c_n sin n(u - x)
        gv = 1 + 2 * ((cu * c) @ cc + (su * c) @ ss)
        gd = -2 * ((su * (c * n)) @ cc - (cu * (c * n)) @ ss)
        A = p * gv
        Au = p * gd
        Z = A.sum(1, keepdims=True) * C.dx
        Zu = Au.sum(1, keepdims=True) * C.dx
        pi = A / Z
        dpi = Au / Z - pi * Zu / Z
        Fu = np.cumsum(dpi, 1) * C.dx
        med = np.median(Fu, 1, keepdims=True)
        cdf = np.cumsum(np.clip(pi, 0, None), 1)
        cdf /= cdf[:, -1:]
        U = rng.random(S)
        ix = np.array([np.searchsorted(cdf[s], U[s]) for s in range(S)])
        ix = np.clip(ix, 0, C.G - 1)
        lo = cdf[np.arange(S), ix - 1] * (ix > 0)
        frac = np.clip((U - lo) / np.maximum(cdf[np.arange(S), ix] - lo, 1e-300), 0, 1)
        x = C.x[ix] - C.dx + frac * C.dx  # cell (x[ix]-dx, x[ix]]
        x = np.angle(np.exp(1j * x))
        pix = np.maximum(pi[np.arange(S), ix], 1e-300)
        a = -(Fu[np.arange(S), ix] - med[:, 0]) / pix
        dxj = w * a
        cost += np.abs(dxj) * cj
        w = w * (1 - a)
        u = np.angle(np.exp(1j * (u - x)))
    cost += np.abs(w + 1)  # the perturbed face link itself
    return float(cost.mean()), float(cost.std(ddof=1) / np.sqrt(S))


def _kr_step(C, logdens, m_rem, u, S, rng):
    """One Knothe-Rosenblatt step: variable with log-density logdens (grid), remaining sum density g_{m_rem}(u - x).
    Returns sampled x and a = -(F_u(x) - median F_u)/pi(x) (velocity per unit change of u)."""
    dens = np.exp(logdens - logdens.max())
    c, k = C.coef(m_rem)
    n = C.n[:k]
    cu, su = np.cos(np.outer(u, n)), np.sin(np.outer(u, n))
    cc, ss = C.cos[:k], C.sin[:k]
    gv = 1 + 2 * ((cu * c) @ cc + (su * c) @ ss)
    gd = -2 * ((su * (c * n)) @ cc - (cu * (c * n)) @ ss)
    A = dens * gv
    Au = dens * gd
    Z = A.sum(1, keepdims=True) * C.dx
    Zu = Au.sum(1, keepdims=True) * C.dx
    pi = A / Z
    dpi = Au / Z - pi * Zu / Z
    Fu = np.cumsum(dpi, 1) * C.dx
    med = np.median(Fu, 1, keepdims=True)
    cdf = np.cumsum(np.clip(pi, 0, None), 1)
    cdf /= cdf[:, -1:]
    U = rng.random(S)
    ix = np.clip(np.array([np.searchsorted(cdf[s], U[s]) for s in range(S)]), 0, C.G - 1)
    rows = np.arange(S)
    lo = cdf[rows, ix - 1] * (ix > 0)
    frac = np.clip((U - lo) / np.maximum(cdf[rows, ix] - lo, 1e-300), 0, 1)
    x = np.angle(np.exp(1j * (C.x[ix] - C.dx + frac * C.dx)))
    a = -(Fu[rows, ix] - med[:, 0]) / np.maximum(pi[rows, ix], 1e-300)
    return x, a


def shells(l, i):
    """Shell r: list of routing costs of its variables (plaquettes at grid distance r: cost r; faces whose plaquette is at
    distance r: cost r + 1). The perturbed face f_i is excluded (own unit)."""
    sh = {}
    for a in range(l):
        for b in range(l):
            r = abs(a - i) + b
            sh.setdefault(r, []).append(r)
    faces = [abs(j - i) for j in range(l) if j != i] + [abs(j - i) + l - 1 for j in range(l)] +             [i + j for j in range(l)] + [(l - 1 - i) + j for j in range(l)]
    for r in faces:
        sh.setdefault(r, []).append(r + 1)
    return [sh[r] for r in sorted(sh)]


def upper_P2(C, l, i, Phi, S, rng):
    """Two-level Knothe-Rosenblatt coupling: shell sums (far first, f_i last), then each shell's interior given its sum."""
    sh = shells(l, i)
    N = l * l + 4 * l
    logp = C.logp
    u = np.full(S, Phi)
    w = -np.ones(S)
    m_rem = N
    Zs, dZs = [], []
    for costs in reversed(sh):
        m = len(costs)
        m_rem -= m
        lg = np.log(np.maximum(C.g(m), 1e-300))
        z, a = _kr_step(C, lg, m_rem, u, S, rng)
        Zs.append(z)
        dZs.append(w * a)
        w = w * (1 - a)
        u = np.angle(np.exp(1j * (u - z)))
    assert m_rem == 1
    cost = np.abs(w + 1)  # f_i itself (u is now x_i)
    for costs, z, dz in zip(reversed(sh), Zs, dZs):
        uu, du = z.copy(), dz.copy()
        m = len(costs)
        for k, ck in enumerate(costs[:-1]):
            x, a = _kr_step(C, logp, m - k - 1, uu, S, rng)
            dx = du * a
            cost += np.abs(dx) * ck
            du = du * (1 - a)
            uu = np.angle(np.exp(1j * (uu - x)))
        cost += np.abs(du) * costs[-1]
    return float(cost.mean()), float(cost.std(ddof=1) / np.sqrt(S))


def sigma(beta):
    return float(-np.log(ive(1, beta) / ive(0, beta)))


def gamma_from(kP, kD, l):
    return (2 * sum(kP) + 2 * (l - 1) * kD + 4 * kP[0]) / (l * (l + 1))


def main():
    global UPPER
    mode = sys.argv[1]
    UPPER = upper_P2 if os.environ.get("KR", "2") == "2" else upper_P
    if mode == "lower":
        betas = [float(b) for b in sys.argv[2].split(",")]
        lmax = int(sys.argv[3])
        path = os.path.join(HERE, "u1_2d_lower.json")
        res = json.load(open(path)) if os.path.exists(path) else {}
        for beta in betas:
            t0 = time.time()
            C = Circle(beta)
            rows = []
            for l in range(2, lmax + 1):
                best = None
                per = []
                for Phi in PHIS:
                    kP, kD = lower_bounds(C, l, Phi)
                    gam = gamma_from(kP, kD, l)
                    per.append(dict(Phi=Phi, gamma=gam, kP=kP, kD=kD))
                # supremum per link over the scan
                kPs = [max(e["kP"][i] for e in per) for i in range(l)]
                kDs = max(e["kD"] for e in per)
                rows.append(dict(l=l, gamma_lo=gamma_from(kPs, kDs, l), gamma_lo_phi0=per[0]["gamma"],
                                 gamma_lo_per_phi=[e["gamma"] for e in per], kP=kPs, kD=kDs))
                print("beta=%g l=%d gamma_lo=%.4f (Phi=0: %.4f) kP0=%.3f kPmid=%.3f kD=%.3f" % (
                    beta, l, rows[-1]["gamma_lo"], per[0]["gamma"], kPs[0], kPs[l // 2], kDs), flush=True)
            res[str(beta)] = dict(beta=beta, sigma=sigma(beta), rows=rows, secs=time.time() - t0)
            json.dump(res, open(path, "w"), indent=1)
    elif mode == "upper":
        beta = float(sys.argv[2])
        ls = [int(v) for v in sys.argv[3].split(",")]
        S = int(sys.argv[4]) if len(sys.argv) > 4 else 256
        phis = [PHIS[int(k)] for k in sys.argv[5].split(",")] if len(sys.argv) > 5 else PHIS
        path = os.path.join(HERE, "u1_2d_upper.json" if UPPER is upper_P2 else "u1_2d_upper_kr1.json")
        res = json.load(open(path)) if os.path.exists(path) else {}
        C = Circle(beta)
        rng = np.random.default_rng(12345)
        for l in ls:
            t0 = time.time()
            per = []
            for Phi in phis:
                kD = upper_D(C, l, Phi)
                kP, kPse = [], []
                for i in range((l + 1) // 2):  # mirror symmetry i <-> l-1-i
                    mval, se = UPPER(C, l, i, Phi, S, rng)
                    kP.append(mval + 2 * se)
                    kPse.append(se)
                kPfull = [kP[min(i, l - 1 - i)] for i in range(l)]
                per.append(dict(Phi=Phi, kP=kPfull, kPse=kPse, kD=min(kD, 3.0), gamma=gamma_from(kPfull, min(kD, 3.0), l)))
            kPs = [max(e["kP"][i] for e in per) for i in range(l)]
            kDs = max(e["kD"] for e in per)
            row = dict(beta=beta, l=l, S=S, phis=phis, gamma_hi=gamma_from(kPs, kDs, l), per=per, kP=kPs, kD=kDs,
                       secs=time.time() - t0)
            print("beta=%g l=%d gamma_hi=%.4f kP0=%.3f kPmid=%.3f kD=%.3f per-phi=%s (%.0fs)" % (
                beta, l, row["gamma_hi"], kPs[0], kPs[l // 2], kDs, ["%.3f" % e["gamma"] for e in per], row["secs"]),
                  flush=True)
            res["%g_%d" % (beta, l)] = row
            json.dump(res, open(path, "w"), indent=1)
    elif mode == "validate":
        out = {}
        for beta in (1000.0, 10000.0):
            C = Circle(beta)
            rng = np.random.default_rng(7)
            for l in (2, 3, 4):
                kP, kD = lower_bounds(C, l, 0.0)
                lo = gamma_from(kP, kD, l)
                kPh = []
                for i in range((l + 1) // 2):
                    mval, se = upper_P(C, l, i, 0.0, 256, rng)
                    kPh.append(mval + 2 * se)
                kPh = [kPh[min(i, l - 1 - i)] for i in range(l)]
                kDh = min(upper_D(C, l, 0.0), 3.0)
                hi = gamma_from(kPh, kDh, l)
                out["%g_%d" % (beta, l)] = dict(gamma_lo=lo, gamma_hi=hi, kP_lo=kP, kD_lo=kD, kP_hi=kPh, kD_hi=kDh)
                print("beta=%g l=%d gamma_lo=%.4f gamma_hi=%.4f kP_lo=%s kP_hi=%s kD=[%.3f, %.3f]" % (
                    beta, l, lo, hi, ["%.3f" % v for v in kP], ["%.3f" % v for v in kPh], kD, kDh), flush=True)
        json.dump(out, open(os.path.join(HERE, "u1_2d_validate.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
