"""The statistical floor of the pilot's estimators (owner's question: derive the minimum error bar from the measurement itself).

For n i.i.d. samples of each of two independent laws theta_0, theta_1 in the 13-parameter exponential family of ir_condlaw.py, the
maximum likelihood estimates are asymptotically normal with covariance I(theta)^-1 / n, I = Cov_theta(phi) (Cramer-Rao bound, attained
asymptotically by the MLE). For a smooth statistic g(theta_0, theta_1) the delta method gives
    Var g_hat = ( grad_0 g . I_0^-1 grad_0 g + grad_1 g . I_1^-1 grad_1 g ) / n.
TV: grad_0 TV = (1/2) E_0[ sign(p_0 - p_1) (phi - E_0 phi) ] (smooth here: the set p_0 = p_1 has measure zero and TV = 0.07 >> 0).
Jbar = |a_0 - a_1| (a = linear coefficients): grad = +-u on the linear block, u the unit vector of a_0 - a_1.
KR_upper: gradients by central finite differences.
For Markov-chain data: floor x sqrt(2 tau_int) with tau_int measured.
    py floor.py   (seconds)
"""
import json
import math

import numpy as np

import ir_condlaw as cl


def fisher(theta):
    u, w = cl.grid()
    P = cl.phi(u)
    p, _ = cl.density(theta, u, w)
    mu = (w * p) @ P
    return ((w * p)[:, None] * (P - mu)).T @ (P - mu)


def grad_tv(t0, t1):
    u, w = cl.grid()
    P = cl.phi(u)
    p0, _ = cl.density(t0, u, w)
    p1, _ = cl.density(t1, u, w)
    s = np.sign(p0 - p1)
    g0 = 0.5 * (w * p0 * s) @ (P - (w * p0) @ P)
    g1 = -0.5 * (w * p1 * s) @ (P - (w * p1) @ P)
    return g0, g1


def grad_fd(f, t0, t1, h=1e-5):
    g0, g1 = np.zeros(cl.NPAR), np.zeros(cl.NPAR)
    for k in range(cl.NPAR):
        e = np.zeros(cl.NPAR)
        e[k] = h
        g0[k] = (f(t0 + e, t1) - f(t0 - e, t1)) / (2 * h)
        g1[k] = (f(t0, t1 + e) - f(t0, t1 - e)) / (2 * h)
    return g0, g1


def sd(g0, g1, I0inv, I1inv, n):
    return math.sqrt((g0 @ I0inv @ g0 + g1 @ I1inv @ g1) / n)


def main():
    n = 250000
    t0 = cl.flat_background_theta(cl.FIT280, False)
    t1 = cl.flat_background_theta(cl.FIT280, True)
    I0inv, I1inv = np.linalg.inv(fisher(t0)), np.linalg.inv(fisher(t1))
    gt0, gt1 = grad_tv(t0, t1)
    fd0, fd1 = grad_fd(cl.tv, t0, t1)
    u = (t0[:4] - t1[:4]) / np.linalg.norm(t0[:4] - t1[:4])
    gj0, gj1 = np.r_[u, np.zeros(9)], np.r_[-u, np.zeros(9)]
    gk0, gk1 = grad_fd(cl.kr_upper, t0, t1)
    res = {
        "n": n,
        "grad_tv_check_max_abs_diff_analytic_vs_fd": float(max(np.abs(gt0 - fd0).max(), np.abs(gt1 - fd1).max())),
        "dTV_da0_per_ensemble": [float(gt0[0]), float(gt1[0])],
        "Iinv_a0a0": [float(I0inv[0, 0]), float(I1inv[0, 0])],
        "floor_tv": sd(gt0, gt1, I0inv, I1inv, n),
        "floor_jbar": sd(gj0, gj1, I0inv, I1inv, n),
        "floor_kr_upper": sd(gk0, gk1, I0inv, I1inv, n),
        "old_prediction_tv": 0.424 * math.sqrt(8 / n),
        "corrected_simple_tv": 0.212 * math.sqrt(8 / n),
    }
    # observed spread over repetitions, E1 runs 1-3 (same n, same laws)
    obs = {}
    for f in ("pilot_E1.json", "pilot_E1_run2.json", "pilot_E1_run3.json"):
        R = json.load(open(f))["rows"]
        obs[f] = {k: float(np.std([r["est"][k] for r in R], ddof=1)) for k in ("tv", "jbar", "kr_upper")}
    allr = [r for f in obs for r in json.load(open(f))["rows"]]
    pooled = {k: float(np.std([r["est"][k] for r in allr], ddof=1)) for k in ("tv", "jbar", "kr_upper")}
    res["observed_sd_per_run"] = obs
    res["observed_sd_pooled_30"] = pooled
    res["ratio_pooled_to_floor"] = {k: pooled[k] / res["floor_" + k] for k in ("tv", "jbar", "kr_upper")}
    # the chi distribution of a 29-dof sample sd: 95 % band of sd/sigma
    from scipy.stats import chi2
    res["sd_ratio_95_band_29dof"] = [math.sqrt(chi2.ppf(0.025, 29) / 29), math.sqrt(chi2.ppf(0.975, 29) / 29)]
    print(json.dumps(res, indent=1))


if __name__ == "__main__":
    main()
