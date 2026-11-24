"""Independent check (PREREG step 2): Monte Carlo simulation of the caterpillar tree flow against the deterministic recursion.

The flow is the one of tree_float.py (shape "single"): root (x_i, Rest), Rest a caterpillar over its variables sorted by routing
cost, far first; at each node the leaf's velocity a = (G_S(y) + c(S)) / rho_S(y) with the c(S) chosen by the recursion.
The simulation samples the leaves sequentially from their exact conditional laws (grid inverse CDF), composes the rates down the
caterpillar (rate into the rest = w (1 - a)) and accumulates the link cost |rate into leaf| * routing cost, plus |1 - a_root| for
f_i. Its mean must equal the deterministic h_root(Phi) up to Monte Carlo error.

Usage: py mc_check.py   (beta = 2, l = 6, i in {0, 2}, Phi in {0, pi}, G = 256, S = 20000)
"""
import json
import os

os.environ.setdefault("CUDA_VISIBLE_DEVICES", "-1")
import numpy as np

import tree_float as T


def node_arrays(F, mA, hA, mB, hB):
    """As tree_float.node_cost, also returning rho, G_S(y) and c (grid arrays indexed [S, y])."""
    G, w = F.G, F.w
    gA, _ = F.g(mA)
    gB, gBd = F.g(mB)
    gm, gmd = F.g(mA + mB)
    k = np.arange(G)
    idx = (k[:, None] - k[None, :]) % G
    rho = gA[None, :] * gB[idx] / gm[:, None]
    drho = gA[None, :] * gBd[idx] / gm[:, None] - rho * (gmd / gm)[:, None]
    cum = np.concatenate([np.zeros((G, 1)), np.cumsum(0.5 * (drho[:, 1:] + drho[:, :-1]) * w, axis=1)], axis=1)
    h, c = T.node_cost(F, mA, hA, mB, hB)
    return rho, -cum, c, h


def main():
    beta, l, Gn, S = 2.0, 6, 256, 20000
    F = T.Fourier(beta, Gn)
    rng = np.random.default_rng(2026)
    zero = np.zeros(Gn)
    out = {}
    for i in (0, 2):
        costs = sorted(sum(T.shells(l, i), []), reverse=True)
        # build bottom-up, keep node arrays; nodes[k] splits off leaf costs[k] from the set costs[k:]
        nodes = [None] * len(costs)
        acc_m, acc_h = 1, zero + costs[-1]
        for k in range(len(costs) - 2, -1, -1):
            rho, Gs, c, h = node_arrays(F, 1, zero + costs[k], acc_m, acc_h)
            nodes[k] = (rho, Gs, c)
            acc_m, acc_h = acc_m + 1, h
        rho0, G0, c0, h0 = node_arrays(F, 1, zero, acc_m, 1 + acc_h)
        for Phi_idx in (0, Gn // 2):
            cost = np.zeros(S)
            # root: sample x_i
            def step(rho, Gs, c, sidx):
                pr = rho[sidx]  # (S, G)
                cdf = np.cumsum(pr, axis=1)
                cdf /= cdf[:, -1:]
                U = rng.random(len(sidx))
                y = np.minimum((cdf < U[:, None]).sum(1), Gn - 1)
                a = (Gs[sidx, y] + c[sidx]) / pr[np.arange(len(sidx)), y]
                return y, a
            sidx = np.full(S, Phi_idx)
            y, a = step(rho0, G0, c0, sidx)
            cost += np.abs(1 - a)  # f_i
            wrate = 1 - a
            sidx = (sidx - y) % Gn
            for k in range(len(costs) - 1):
                rho, Gs, c = nodes[k]
                y, a = step(rho, Gs, c, sidx)
                cost += np.abs(wrate * a) * costs[k]
                wrate = wrate * (1 - a)
                sidx = (sidx - y) % Gn
            cost += np.abs(wrate) * costs[-1]
            m, se = cost.mean(), cost.std(ddof=1) / np.sqrt(S)
            det = h0[Phi_idx]
            ok = abs(m - det) <= 3 * se
            print("i=%d Phi=%.3f deterministic=%.4f MC=%.4f +- %.4f  %s" % (i, F.x[Phi_idx], det, m, se,
                                                                          "OK" if ok else "FAIL"), flush=True)
            out["i%d_phi%d" % (i, Phi_idx)] = dict(det=float(det), mc=float(m), se=float(se), ok=bool(ok))
    json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "mc_check.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
