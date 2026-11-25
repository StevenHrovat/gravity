"""c9b infrared pilot, part 2 of 2: the conditional law of one coarse link from samples (PREREG-PILOT.md, PREREG-GPU.md section 3).

Densities on SU(2) = S^3 (unit quaternions, Haar = uniform measure) are fitted in the exponential family
    log p(u) = theta . phi(u) - log Z(theta),   phi = the 13 harmonics of degree 1 and 2 on S^3
(degree 1: u_0..u_3; degree 2: u_i u_j for i < j and u_0^2 - u_1^2, u_1^2 - u_2^2, u_2^2 - u_3^2). The single-link conditional law of
any plaquette action with fundamental and adjoint (spin 1) terms lies exactly in this family, so the fitted coarse plaquette action is
an exact test case (`exact_theta`).

From fitted densities:
  tv(t1, t2)              total variation, quadrature on a fixed S^3 grid
  kr_upper(t1, t2)        an upper bound on the Kantorovich-Rubinstein (W1, geodesic) distance: the H^-1 norm of p1 - p2 with the
                          degree split of c4d (eigenvalues l(l + 2) = 3, 8, then >= 15)
  jbar(t_w, t_minus_w)    half the sup over v of the change of the centre log-odds log p(v)/p(-v) between the two laws
  fit(samples)            maximum likelihood (Newton), the normaliser by quadrature
  bootstrap               blocked bootstrap over chains and trajectory blocks

CLI
  py ir_condlaw.py selftest              seconds-scale smoke test of the functions (no result-bearing numbers)
  py ir_condlaw.py exactcheck [...]      PILOT CHECK E1 (pre-registered; needs the owner's OK): estimator against exact samples
  py ir_condlaw.py analyse A.npz B.npz   TV / KR / Jbar between two ensembles of ir_constrained.py, with bootstrap errors
numpy only; CPU.
"""
import argparse
import json
import math
import sys
import time

import numpy as np

NPAR = 13


# ------------------------------------------------------------------------------------------------------------ S^3 grid and basis
def s3_grid(nc=48, nt=24, nf=48):
    """Midpoint grid on S^3 (Hopf-type angles, all four coordinates) with Haar weights summing to 1."""
    chi = (np.arange(nc) + 0.5) * math.pi / nc
    th = (np.arange(nt) + 0.5) * math.pi / nt
    ph = (np.arange(nf) + 0.5) * 2 * math.pi / nf
    C, T, P = np.meshgrid(chi, th, ph, indexing="ij")
    u = np.stack([np.cos(C), np.sin(C) * np.cos(T), np.sin(C) * np.sin(T) * np.cos(P), np.sin(C) * np.sin(T) * np.sin(P)], -1)
    w = np.sin(C) ** 2 * np.sin(T)
    w = w / w.sum()
    return u.reshape(-1, 4), w.ravel()


GRID = None


def grid():
    global GRID
    if GRID is None:
        GRID = s3_grid()
    return GRID


def phi(u):
    """The 13 harmonics of degree 1 and 2 at points u (..., 4) -> (..., 13)."""
    u0, u1, u2, u3 = u[..., 0], u[..., 1], u[..., 2], u[..., 3]
    return np.stack([u0, u1, u2, u3,
                     u0 * u1, u0 * u2, u0 * u3, u1 * u2, u1 * u3, u2 * u3,
                     u0 ** 2 - u1 ** 2, u1 ** 2 - u2 ** 2, u2 ** 2 - u3 ** 2], -1)


DEG = np.array([1] * 4 + [2] * 9)


def density(theta, u=None, w=None):
    """Normalised density values (w.r.t. Haar) on the grid, and log Z."""
    if u is None:
        u, w = grid()
    h = phi(u) @ theta
    m = h.max()
    e = np.exp(h - m)
    Z = (w * e).sum()
    return e / Z, m + math.log(Z)


# ------------------------------------------------------------------------------------------------------------ exact law (fitted action)
def exact_theta(A, adj):
    """theta of rho(u) ~ exp(<A, u> + sum_p (alpha_p/3)(4 <u, s_p>^2 - 1)), adj = [(alpha_p, s_p)], s_p unit quaternions."""
    th = np.zeros(NPAR)
    th[:4] = A
    Q = np.zeros((4, 4))
    for a, s in adj:
        Q += (4 * a / 3) * np.outer(s, s)
    # quadratic form u^T Q u in the basis: off-diagonal u_i u_j with coefficient 2 Q_ij; diagonal part projected on the traceless span
    k = 4
    for i in range(4):
        for j in range(i + 1, 4):
            th[k] = 2 * Q[i, j]
            k += 1
    d = np.diag(Q) - np.trace(Q) / 4  # traceless diagonal (the trace is a constant on S^3)
    # d0 u0^2 + d1 u1^2 + d2 u2^2 + d3 u3^2 = c1 (u0^2 - u1^2) + c2 (u1^2 - u2^2) + c3 (u2^2 - u3^2) with sum d = 0
    th[10] = d[0]
    th[11] = d[0] + d[1]
    th[12] = d[0] + d[1] + d[2]
    return th


def sample_exact(theta, n, rng):
    """Exact samples from exp(theta . phi) by rejection from Haar (bound: sum |theta| over a basis bounded by 1 in absolute value)."""
    bound = np.abs(theta).sum()
    out = []
    need = n
    while need > 0:
        m = max(4 * need, 1024)
        g = rng.normal(size=(m, 4))
        u = g / np.linalg.norm(g, axis=1, keepdims=True)
        acc = rng.random(m) < np.exp(phi(u) @ theta - bound)
        out.append(u[acc][:need])
        need -= len(out[-1])
    return np.concatenate(out)


# ------------------------------------------------------------------------------------------------------------ fit
def fit(samples, iters=30, tol=1e-12):
    """Maximum likelihood theta (Newton; the Hessian is n times the model covariance of phi). Fewer than 50 samples: NaN (no fit)."""
    if len(samples) < 50:
        return np.full(NPAR, np.nan)
    u, w = grid()
    P = phi(u)
    mean_obs = phi(samples).mean(axis=0)
    th = np.zeros(NPAR)
    for _ in range(iters):
        p, _ = density(th, u, w)
        mu = (w * p) @ P
        C = ((w * p)[:, None] * (P - mu)).T @ (P - mu)
        try:
            step = np.linalg.solve(C, mean_obs - mu)
        except np.linalg.LinAlgError:
            step = np.linalg.lstsq(C, mean_obs - mu, rcond=None)[0]
        th = th + step
        if np.abs(step).max() < tol:
            break
    return th


# ------------------------------------------------------------------------------------------------------------ distances
def tv(t1, t2):
    u, w = grid()
    p1, _ = density(t1, u, w)
    p2, _ = density(t2, u, w)
    return 0.5 * (w * np.abs(p1 - p2)).sum()


_HB = None


def harmonic_basis():
    """Orthonormal (in L^2(Haar)) bases of the degree-1 and degree-2 harmonics on the grid."""
    global _HB
    if _HB is None:
        u, w = grid()
        P = phi(u)
        out = []
        for d in (1, 2):
            B = P[:, DEG == d]
            G = (w[:, None] * B).T @ B
            L = np.linalg.cholesky(G)
            out.append(B @ np.linalg.inv(L).T)
        _HB = out
    return _HB


def kr_upper(t1, t2):
    """||p1 - p2||_{H^-1} >= KR(p1, p2) for the geodesic cost (c4d tool (i)), with the degree split: degree 1 / 3, degree 2 / 8, rest / 15."""
    u, w = grid()
    g = density(t1, u, w)[0] - density(t2, u, w)[0]
    tot = (w * g * g).sum()
    B1, B2 = harmonic_basis()
    c1 = (w * g) @ B1
    c2 = (w * g) @ B2
    e1, e2 = (c1 ** 2).sum(), (c2 ** 2).sum()
    return math.sqrt(e1 / 3 + e2 / 8 + max(tot - e1 - e2, 0.0) / 15)


def jbar(t_w, t_mw):
    """Half the sup over v of the change of log p(v)/p(-v): the log-odds is 2 theta_lin . v (degree-2 terms are even), so the change is
    2 (a - a') . v and its half-sup is |a - a'|."""
    return float(np.linalg.norm(t_w[:4] - t_mw[:4]))


# ------------------------------------------------------------------------------------------------------------ bootstrap
def blocks_of(samples, chain, nblock):
    """Split each chain's time series into nblock contiguous blocks; returns a list of sample arrays (one per (chain, block))."""
    out = []
    for c in np.unique(chain):
        s = samples[chain == c]
        for part in np.array_split(s, nblock):
            if len(part):
                out.append(part)
    return out


def bootstrap(stat, blocksA, blocksB, nboot, rng):
    """stat(samplesA, samplesB) with a blocked bootstrap (blocks resampled with replacement, independently for A and B)."""
    vals = []
    for _ in range(nboot):
        a = np.concatenate([blocksA[i] for i in rng.integers(len(blocksA), size=len(blocksA))])
        b = np.concatenate([blocksB[i] for i in rng.integers(len(blocksB), size=len(blocksB))])
        vals.append(stat(a, b))
    sd = np.std(np.array(vals, float), axis=0, ddof=1)
    return float(sd) if np.ndim(sd) == 0 else [float(x) for x in sd]


def jackknife(stat, repA, repB):
    """Jackknife over the replicas of two INDEPENDENT ensembles (lists of independent sample arrays): each ensemble is jackknifed
    separately (delete one replica of it, keep the other ensemble whole) and the variances are added (amendment 2). Per component."""
    def part(reps, other, first):
        K = len(reps)
        th = []
        for i in range(K):
            r = np.concatenate([reps[j] for j in range(K) if j != i])
            th.append(stat(r, other) if first else stat(other, r))
        th = np.array(th, float)
        return (K - 1) / K * ((th - th.mean(axis=0)) ** 2).sum(axis=0)
    assert len(repA) >= 2 and len(repB) >= 2
    var = part(repA, np.concatenate(repB), True) + part(repB, np.concatenate(repA), False)
    sd = np.sqrt(var)
    return float(sd) if np.ndim(sd) == 0 else [float(x) for x in sd]


def tquant(K):
    """The 95.45 % two-sided quantile of Student's t with K - 1 degrees of freedom (the 'within 2 sigma' rule for a K-replica sigma)."""
    from scipy.stats import t
    return float(t.ppf(0.97725, K - 1))


def three_stats(x, y):
    fx, fy = fit(x), fit(y)
    return (tv(fx, fy), jbar(fx, fy), kr_upper(fx, fy))


def fisher(theta):
    """I(theta) = Cov_theta(phi) (13 x 13), quadrature."""
    u, w = grid()
    P = phi(u)
    p, _ = density(theta, u, w)
    mu = (w * p) @ P
    return ((w * p)[:, None] * (P - mu)).T @ (P - mu)


def d2_exact(t0, t1):
    """D^2 = Delta theta . I_mid Delta theta, I_mid = (I(t0) + I(t1))/2 (amendment 3)."""
    d = t1 - t0
    return float(d @ ((fisher(t0) + fisher(t1)) / 2) @ d)


def d2_cross(repA, repB):
    """The cross-replica U-statistic D^2_U = (1/(K(K-1))) sum_{r != s} Delta_r . I_mid Delta_s (replica r of A paired with replica r of
    B; I_mid from the pooled fits), its delete-one jackknife error over the K items Delta_r, and C_D = sqrt(max(0, D^2_U))/2."""
    K = len(repA)
    assert len(repB) == K and K >= 3
    tA, tB = fit(np.concatenate(repA)), fit(np.concatenate(repB))
    Im = (fisher(tA) + fisher(tB)) / 2
    Dl = np.array([fit(repB[r]) - fit(repA[r]) for r in range(K)])
    G = Dl @ Im @ Dl.T
    off = G.sum() - np.trace(G)

    def u_stat(idx):
        sub = G[np.ix_(idx, idx)]
        k = len(idx)
        return (sub.sum() - np.trace(sub)) / (k * (k - 1))
    d2 = off / (K * (K - 1))
    jk = np.array([u_stat([j for j in range(K) if j != i]) for i in range(K)])
    sd = float(np.sqrt((K - 1) / K * ((jk - jk.mean()) ** 2).sum()))
    return {"d2_U": float(d2), "sd_d2": sd, "C_D": 0.5 * math.sqrt(max(0.0, d2)), "K_d2": K, "t_d2": tquant(K),
            "theta_A": tA.tolist(), "theta_B": tB.tolist()}


def d2_floor(tA, tB, NA, NB, tauA, tauB):
    """Gaussian quadratic-form floor: Var(D^2_hat) >= 4 d.I Sigma I d + 2 tr((I Sigma)^2), Sigma = 2 tau (I_A^-1/N_A + I_B^-1/N_B)."""
    IA, IB = fisher(tA), fisher(tB)
    Im = (IA + IB) / 2
    Sig = 2 * tauA * np.linalg.inv(IA) / NA + 2 * tauB * np.linalg.inv(IB) / NB
    d = tB - tA
    M = Im @ Sig
    return float(math.sqrt(4 * d @ Im @ Sig @ Im @ d + 2 * np.trace(M @ M)))


def gamma_batch(vx, b=20):
    """Long-run covariance of the 13-component series phi(V_x(t)) by batch means (amendment 4): vx (T, chains, 4); each chain cut into
    batches of b trajectories; Gamma = b Cov(batch means), pooled over chains (centred at the pooled mean)."""
    means = []
    for c in range(vx.shape[1]):
        ph = phi(vx[:, c])
        nb = len(ph) // b
        if nb:
            means.append(ph[:nb * b].reshape(nb, b, NPAR).mean(axis=1))
    M = np.concatenate(means)
    return b * np.cov(M.T, ddof=1)


def d2_floor4(tA, tB, NA, NB, GA, GB, K):
    """Corrected floor (amendment 4): Var(D^2_U) = 4 d.I Sigma I d + (2K/(K-1)) tr((I Sigma)^2),
    Sigma = I_A^-1 Gamma_A I_A^-1/N_A + I_B^-1 Gamma_B I_B^-1/N_B (Gamma = I for i.i.d. data)."""
    IA, IB = fisher(tA), fisher(tB)
    Im = (IA + IB) / 2
    iA, iB = np.linalg.inv(IA), np.linalg.inv(IB)
    Sig = iA @ GA @ iA / NA + iB @ GB @ iB / NB
    d = tB - tA
    M = Im @ Sig
    return float(math.sqrt(4 * d @ Im @ Sig @ Im @ d + (2 * K / (K - 1)) * np.trace(M @ M)))


def calib1(a):
    """CALIBRATION C1 (PREREG-PILOT.md amendment 4): the null and true D^2_U on exact i.i.d. samples against the corrected floor."""
    if not a.go:
        print("calib1 is a pre-registered calibration; it runs only with --go (PREREG-PILOT.md, amendment 4).")
        return 2
    rng = np.random.default_rng(a.seed)
    t0, t1 = flat_background_theta(FIT280, False), flat_background_theta(FIT280, True)
    K, nr = a.K, a.nr
    out = {"K": K, "n_r": nr, "draws": a.draws}
    for name, tb in (("null", t0), ("true", t1)):
        vals, jks = [], []
        for _ in range(a.draws):
            A = [sample_exact(t0, nr, rng) for _ in range(K)]
            B = [sample_exact(tb, nr, rng) for _ in range(K)]
            r = d2_cross(A, B)
            vals.append(r["d2_U"])
            jks.append(r["sd_d2"])
        I0 = fisher(t0)
        floor = d2_floor4(t0, tb, K * nr, K * nr, fisher(t0), fisher(tb), K)
        out[name] = {"mean": float(np.mean(vals)), "sd": float(np.std(vals, ddof=1)), "floor": floor,
                     "ratio_sd_floor": float(np.std(vals, ddof=1) / floor), "mean_jk": float(np.mean(jks)),
                     "ratio_jk_sd": float(np.mean(jks) / np.std(vals, ddof=1)), "exact": d2_exact(t0, tb)}
        print(json.dumps({name: out[name]}), flush=True)
    json.dump(out, open(a.out, "w"), indent=1)
    return 0


def h1_metric(theta):
    """M(theta): the H^-1 Gram matrix (degree split of kr_upper: degree 1 / 3, degree 2 / 8, the rest / 15) of the first-order density
    changes g_i = p (phi_i - E_p phi_i), so that ||delta p||^2_{H^-1, split} = Delta theta . M Delta theta to first order (REDESIGN.md)."""
    u, w = grid()
    P = phi(u)
    p, _ = density(theta, u, w)
    G = p[:, None] * (P - (w * p) @ P)  # (grid, 13): the 13 first-order changes
    B1, B2 = harmonic_basis()
    c1 = (w[:, None] * G).T @ B1  # (13, 4)
    c2 = (w[:, None] * G).T @ B2  # (13, 9)
    tot = (w[:, None] * G).T @ G
    e1, e2 = c1 @ c1.T, c2 @ c2.T
    return e1 / 3 + e2 / 8 + (tot - e1 - e2) / 15


def krd_cross(repA, repB):
    """KR_D: the cross-replica U-statistic with the H^-1 metric (no-loss W1 estimator, REDESIGN.md): Q_U = (1/(K(K-1)))
    sum_{r != s} Delta_r . M_mid Delta_s, M_mid = (M(theta_A) + M(theta_B))/2 at the pooled fits; KR_D = sqrt(max(0, Q_U)); jackknife
    over the K items; also the corrected floor with M in the metric slot (needs Gamma: supplied by the caller)."""
    K = len(repA)
    tA, tB = fit(np.concatenate(repA)), fit(np.concatenate(repB))
    Mm = (h1_metric(tA) + h1_metric(tB)) / 2
    Dl = np.array([fit(repB[r]) - fit(repA[r]) for r in range(K)])
    G = Dl @ Mm @ Dl.T

    def u_stat(idx):
        sub = G[np.ix_(idx, idx)]
        k = len(idx)
        return (sub.sum() - np.trace(sub)) / (k * (k - 1))
    q = u_stat(list(range(K)))
    jk = np.array([u_stat([j for j in range(K) if j != i]) for i in range(K)])
    sd = float(np.sqrt((K - 1) / K * ((jk - jk.mean()) ** 2).sum()))
    return {"q_U": float(q), "sd_q": sd, "KR_D": math.sqrt(max(0.0, q)), "K_q": K, "theta_A": tA, "theta_B": tB, "M_mid": Mm}


def q_floor(tA, tB, NA, NB, GA, GB, K, Mm):
    """Floor of the U-statistic with metric Mm: Var = 4 d.Mm Sigma Mm d + (2K/(K-1)) tr((Mm Sigma)^2), Sigma as in d2_floor4."""
    IA, IB = fisher(tA), fisher(tB)
    iA, iB = np.linalg.inv(IA), np.linalg.inv(IB)
    Sig = iA @ GA @ iA / NA + iB @ GB @ iB / NB
    d = tB - tA
    X = Mm @ Sig
    return float(math.sqrt(4 * d @ Mm @ Sig @ Mm @ d + (2 * K / (K - 1)) * np.trace(X @ X)))


def null_quantile(theta, n, reps, q, rng):
    """q-quantile of the TV between two independent fitted samples of size n of one law (the simulated null, amendment 3)."""
    v = [tv(fit(sample_exact(theta, n, rng)), fit(sample_exact(theta, n, rng))) for _ in range(reps)]
    return float(np.quantile(v, q)), float(np.mean(v))


# ------------------------------------------------------------------------------------------------------------ fitted action at 2.80
FIT280 = dict(F_ts=0.054, F_ss=0.171, A_ts=-0.000595, A_ss=0.00149)  # c3b base fit, central (analysis.log)


def flat_background_theta(cpl, flip_y):
    """Exact theta for a spatial coarse link x on the block-flat background (all other links = 1): its 4 ss and 2 ts plaquettes have
    staple 1; with flip_y the staple of one ss plaquette is -1 (the partner y flipped to -1)."""
    e0 = np.array([1.0, 0, 0, 0])
    staples = [("ss", -e0 if (flip_y and k == 0) else e0) for k in range(4)] + [("ts", e0), ("ts", e0)]
    A = np.zeros(4)
    adj = []
    for cls, s in staples:
        A += cpl["F_" + cls] * s
        adj.append((cpl["A_" + cls], s))
    return exact_theta(A, adj)


# ------------------------------------------------------------------------------------------------------------ CLI
def selftest(_a):
    rng = np.random.default_rng(1)
    ok = True
    # exact_theta reproduces the log-density up to a constant
    A = rng.normal(size=4) * 0.3
    adj = [(0.1, (lambda v: v / np.linalg.norm(v))(rng.normal(size=4))) for _ in range(3)]
    th = exact_theta(A, adj)
    u = rng.normal(size=(50, 4))
    u /= np.linalg.norm(u, axis=1, keepdims=True)
    direct = u @ A + sum((a / 3) * (4 * (u @ s) ** 2 - 1) for a, s in adj)
    diff = phi(u) @ th - direct
    e1 = float(np.ptp(diff))
    print(f"exact_theta: log-density differs from the direct formula by a constant (spread {e1:.1e})")
    ok &= e1 < 1e-12
    # quadrature normalisation and the fit on a few thousand exact samples (smoke only: tiny n)
    s = sample_exact(th, 3000, rng)
    tf = fit(s)
    print(f"fit converges on 3000 samples: max |theta_hat - theta| = {np.abs(tf - th).max():.3f} (smoke; no precision claim)")
    ok &= np.all(np.isfinite(tf))
    # distances: zero on equal laws, symmetric, KR bound >= 0
    t2 = th.copy()
    t2[:4] *= -1
    print(f"tv(th, th) = {tv(th, th):.1e}; tv symmetric: {abs(tv(th, t2) - tv(t2, th)):.1e}; kr_upper(th, th) = {kr_upper(th, th):.1e}")
    ok &= tv(th, th) < 1e-14 and abs(tv(th, t2) - tv(t2, th)) < 1e-14 and kr_upper(th, th) < 1e-12
    # small-coupling TV of an antipodal flip: 4/(3 pi) beta (the N2 control (ii))
    b = 1e-3
    r = tv(np.r_[b, 0, 0, 0, np.zeros(9)], np.r_[-b, 0, 0, 0, np.zeros(9)]) / b
    print(f"small-coupling flip TV / beta = {r:.4f} (4/(3 pi) = {4 / (3 * math.pi):.4f})")
    ok &= abs(r - 4 / (3 * math.pi)) < 2e-3
    # harmonic basis orthonormal
    B1, B2 = harmonic_basis()
    _, w = grid()
    G = (w[:, None] * np.c_[B1, B2]).T @ np.c_[B1, B2]
    print(f"harmonic basis orthonormal: max |G - I| = {np.abs(G - np.eye(NPAR)).max():.1e}")
    ok &= np.abs(G - np.eye(NPAR)).max() < 1e-8
    # bootstrap runs
    ch = np.repeat(np.arange(4), 750)
    sd = bootstrap(lambda a, b: tv(fit(a), fit(b)), blocks_of(s, ch, 4), blocks_of(s, ch, 4), 5, rng)
    print(f"bootstrap runs (5 resamples, smoke): sd = {sd:.3f}")
    ok &= np.isfinite(sd)
    # jackknife over replicas: for the difference of means of two i.i.d. samples it equals the exact standard error formula
    xa, xb = rng.normal(size=(400, 4)), rng.normal(size=(400, 4))
    sdj = jackknife(lambda x, y: x[:, 0].mean() - y[:, 0].mean(), np.array_split(xa, 20), np.array_split(xb, 20))
    ref = math.sqrt(sum(np.var([r[:, 0].mean() for r in np.array_split(z, 20)], ddof=1) / 20 for z in (xa, xb)))
    print(f"jackknife (K = 20, each ensemble separately) of a difference of means vs the replica-mean standard error: {sdj:.5f} vs {ref:.5f}")
    ok &= abs(sdj - ref) < 1e-12
    print(f"t quantiles (95.45 %): K = 20 {tquant(20):.3f}, 16 {tquant(16):.3f}, 5 {tquant(5):.3f}")
    # D^2_U smoke: the U-statistic of identical replica differences reduces to the plain quadratic form
    Dl = np.tile(np.r_[0.1, np.zeros(12)], (4, 1))
    Im = fisher(np.zeros(NPAR))
    G = Dl @ Im @ Dl.T
    u = (G.sum() - np.trace(G)) / 12
    print(f"U-statistic of identical items = quadratic form: {u:.6f} vs {0.01 * Im[0, 0]:.6f}")
    ok &= abs(u - 0.01 * Im[0, 0]) < 1e-14
    t0, t1 = flat_background_theta(FIT280, False), flat_background_theta(FIT280, True)
    print(f"D^2 exact (fitted law, flat, flip) = {d2_exact(t0, t1):.5f}; C_D = {0.5 * math.sqrt(d2_exact(t0, t1)):.4f}")
    ok &= abs(d2_exact(t0, t1) - 0.027843) < 1e-5
    th0 = np.zeros(NPAR)
    G = gamma_batch(np.stack([sample_exact(th0, 4000, rng) for _ in range(10)], axis=1))
    rel = float(np.abs(G - fisher(th0)).max() / np.abs(fisher(th0)).max())
    print(f"batch-means Gamma of i.i.d. samples vs I (10 chains x 4000, b = 20): max relative difference {rel:.2f} (smoke; noise ~0.2)")
    ok &= rel < 0.5
    f4 = d2_floor4(t0, t1, 7840, 7840, fisher(t0), fisher(t1), 8)
    print(f"corrected floor at the true pair, i.i.d., N = 7840, K = 8: {f4:.5f}")
    ok &= abs(tquant(20) - 2.140) < 1e-3 and abs(tquant(16) - 2.181) < 1e-3 and abs(tquant(5) - 2.869) < 1e-3
    print("SELFTEST", "OK" if ok else "FAIL")
    return 0 if ok else 1


def exactcheck(a):
    """PILOT CHECK E1 (PREREG-PILOT.md): estimator against exact samples of the fitted plaquette law. Needs the owner's OK."""
    if not a.go:
        print("exactcheck is a pre-registered pilot check; it runs only with --go after the owner's OK (PREREG-PILOT.md).")
        return 2
    rng = np.random.default_rng(a.seed)
    out = {"n": a.n, "rows": []}
    th0 = flat_background_theta(FIT280, False)
    th1 = flat_background_theta(FIT280, True)
    exact = {"tv": tv(th0, th1), "kr_upper": kr_upper(th0, th1), "jbar": jbar(th0, th1)}
    for rep in range(a.reps):
        s0, s1 = sample_exact(th0, a.n, rng), sample_exact(th1, a.n, rng)
        ch = np.repeat(np.arange(8), a.n // 8 + 1)[:a.n]
        f0, f1 = fit(s0), fit(s1)
        est = {"tv": tv(f0, f1), "kr_upper": kr_upper(f0, f1), "jbar": jbar(f0, f1)}
        row = {"est": est}
        if a.error == "replica":
            # K independent replicas: contiguous slices of the i.i.d. exact samples
            sd = jackknife(three_stats, np.array_split(s0, a.K), np.array_split(s1, a.K), )
            row.update({"sd_tv": sd[0], "sd_jbar": sd[1], "sd_kr": sd[2], "K": a.K, "t": tquant(a.K), "error": "replica"})
        else:
            row.update({"sd_tv": bootstrap(lambda x, y: tv(fit(x), fit(y)), blocks_of(s0, ch, 8), blocks_of(s1, ch, 8), a.nboot, rng),
                        "error": "bootstrap"})
        row["null_tv"] = tv(fit(sample_exact(th0, a.n, rng)), f0)
        out["rows"].append(row)
        print(json.dumps(dict(rep=rep, exact=exact, **row)))
    out["exact"] = exact
    json.dump(out, open(a.out, "w"), indent=1)
    return 0


def tauint(x, c=6.0):
    """Integrated autocorrelation time of a 1D series (Sokal's automatic window, factor c)."""
    x = np.asarray(x, float) - np.mean(x)
    n = len(x)
    if n < 8 or np.var(x) == 0:
        return float("nan")
    f = np.fft.rfft(x, 2 * n)
    acf = np.fft.irfft(f * np.conj(f))[:n] / (np.var(x) * np.arange(n, 0, -1))
    tau = 0.5
    for W in range(1, n):
        tau += acf[W]
        if W >= c * tau:
            break
    return float(tau)


def exact_flat():
    """Closed-form values for check E2 (block-flat background, fitted couplings, flip of one ss partner)."""
    t0, t1 = flat_background_theta(FIT280, False), flat_background_theta(FIT280, True)
    return {"tv": tv(t0, t1), "kr_upper": kr_upper(t0, t1), "jbar": jbar(t0, t1)}


def analyse(a):
    A, B = np.load(a.A), np.load(a.B)
    sa, sb = A["vx"].reshape(-1, 4), B["vx"].reshape(-1, 4)
    ca = np.repeat(np.arange(A["vx"].shape[1]), A["vx"].shape[0]).reshape(A["vx"].shape[1], -1).T.ravel()
    cb = np.repeat(np.arange(B["vx"].shape[1]), B["vx"].shape[0]).reshape(B["vx"].shape[1], -1).T.ravel()
    fa, fb = fit(sa), fit(sb)
    res = {"tv": tv(fa, fb), "kr_upper": kr_upper(fa, fb), "jbar": jbar(fa, fb), "n": [len(sa), len(sb)]}
    if a.error == "replica":
        nA, nB = A["vx"].shape[1], B["vx"].shape[1]
        if nA > 1 and nB > 1:
            assert nA == nB
            repA = [A["vx"][:, c] for c in range(nA)]  # one replica per independent chain
            repB = [B["vx"][:, c] for c in range(nB)]
            mode = "chains"
        else:
            repA = np.array_split(A["vx"][:, 0], a.nblock)  # single chain: consecutive time blocks (amendment 2, check P)
            repB = np.array_split(B["vx"][:, 0], a.nblock)
            mode = "time blocks"
        sd = jackknife(three_stats, repA, repB)
        res.update({"sd_tv": sd[0], "sd_jbar": sd[1], "sd_kr": sd[2], "K": len(repA), "t": tquant(len(repA)), "error": mode})
    else:
        rng = np.random.default_rng(0)

        def both(x, y):
            fx, fy = fit(x), fit(y)
            return (tv(fx, fy), jbar(fx, fy))
        sd_tv, sd_jbar = bootstrap(both, blocks_of(sa, ca, a.nblock), blocks_of(sb, cb, a.nblock), a.nboot, rng)
        res.update({"sd_tv": sd_tv, "sd_jbar": sd_jbar, "error": "bootstrap"})
    res["tauint"] = {k: float(np.nanmax([tauint(X["vx"][:, c, i]) for c in range(X["vx"].shape[1]) for i in range(4)]))
                     for k, X in (("A", A), ("B", B))}
    if a.d2:
        def groups(X, K):
            nc = X["vx"].shape[1]
            if nc >= K:
                return [X["vx"][:, list(g)].reshape(-1, 4) for g in np.array_split(np.arange(nc), K)]
            return np.array_split(X["vx"][:, 0], K)  # one chain: consecutive time blocks
        Kd = a.Kd2 if A["vx"].shape[1] > 1 else a.nblock
        dd = d2_cross(groups(A, Kd), groups(B, Kd))
        tA, tB = np.array(dd.pop("theta_A")), np.array(dd.pop("theta_B"))
        dd["d2_floor_old"] = d2_floor(tA, tB, len(sa), len(sb), res["tauint"]["A"], res["tauint"]["B"])  # defective (amendment 4)
        dd["d2_floor"] = d2_floor4(tA, tB, len(sa), len(sb), gamma_batch(A["vx"]), gamma_batch(B["vx"]), dd["K_d2"])
        res.update(dd)
        if a.null_q:
            n_eff = int(min(len(sa) / (2 * res["tauint"]["A"]), len(sb) / (2 * res["tauint"]["B"])))
            q95, mean = null_quantile(tA, n_eff, 200, 0.95, np.random.default_rng(a.null_seed))
            res.update({"null_n_eff": n_eff, "null_q95": q95, "null_mean_sim": mean})
        if a.exact_flat:
            res["d2_exact"] = d2_exact(flat_background_theta(FIT280, False), flat_background_theta(FIT280, True))
    res["acc"] = [float(np.mean(A["acc"])), float(np.mean(B["acc"]))]
    res["resid"] = [float(np.mean(A["resid"])), float(np.mean(B["resid"]))]
    if a.exact_flat:
        res["exact"] = exact_flat()
    print(json.dumps(res))
    return 0


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest="cmd", required=True)
    sp.add_parser("selftest")
    e = sp.add_parser("exactcheck")
    e.add_argument("--go", action="store_true")
    e.add_argument("--n", type=int, default=250000)
    e.add_argument("--reps", type=int, default=10)
    e.add_argument("--nboot", type=int, default=50)
    e.add_argument("--error", choices=["replica", "bootstrap"], default="replica")
    e.add_argument("--K", type=int, default=20)
    e.add_argument("--seed", type=int, default=20261124)
    e.add_argument("--out", default="pilot_E1.json")
    an = sp.add_parser("analyse")
    an.add_argument("A")
    an.add_argument("B")
    an.add_argument("--nblock", type=int, default=10)
    an.add_argument("--nboot", type=int, default=100)
    an.add_argument("--error", choices=["replica", "bootstrap"], default="replica")
    an.add_argument("--d2", action="store_true", help="also the debiased D^2_U, C_D and the D^2 floor (amendment 3)")
    an.add_argument("--Kd2", type=int, default=8)
    an.add_argument("--null-q", action="store_true", help="also the 95 %% quantile of the simulated null TV at N/(2 tau)")
    an.add_argument("--null-seed", type=int, default=4242)
    an.add_argument("--exact-flat", action="store_true", help="also print the closed-form values of check E2")
    sp.add_parser("expected")
    c1 = sp.add_parser("calib1")
    c1.add_argument("--go", action="store_true")
    c1.add_argument("--draws", type=int, default=200)
    c1.add_argument("--K", type=int, default=8)
    c1.add_argument("--nr", type=int, default=980)
    c1.add_argument("--seed", type=int, default=20261127)
    c1.add_argument("--out", default="pilot_C1.json")
    a = ap.parse_args()
    return {"selftest": selftest, "exactcheck": exactcheck, "analyse": analyse, "calib1": calib1,
            "expected": lambda _a: print(json.dumps(exact_flat())) or 0}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
