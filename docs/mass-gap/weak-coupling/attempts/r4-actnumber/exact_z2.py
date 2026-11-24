"""Exact flux energy of 4D Z2 gauge theory on the twisted 2^3 box, by the transfer matrix (instrument validation; PREREG.md, "Changes
before data (after the round-4 review)", item 3). CPU, numpy, one process.

Temporal gauge: the 24 spatial links of the periodic 2^3 box are the state (2^24 basis states, spins sigma = +-1). The Wilson action
S = -beta sum_p c_p sigma_p (the Monte Carlo's Z2 weight exp(beta sum_p c_p cos theta_p)) gives the symmetric transfer matrix
  T = V^{1/2} K V^{1/2},  V = exp(beta sum_{spatial p} c_p sigma_p) (diagonal),  K = prod_l (e^beta 1 + e^{-beta} sigma^x_l),
with the twist c_p = -1 on the xy-plaquettes at (x, y) = (1, 1) (L - 1 = 1). The temporal links fixed to 1 leave Gauss's law, imposed by
the projector P_G = prod_x (1 + G_x)/2 (G_x flips the six links at site x); the electric flux sectors are the eigenspaces of the centre
transformation Omega_z (flip the four z-links of the slice z = 0), e_z = 0 (+1) and 1 (-1). Then aE = log(lambda_0 / lambda_1) with
lambda_e the largest eigenvalue of P_G P_e T P_e P_G (scipy eigsh, Lanczos). This is exactly the quantity the Monte Carlo estimates on the
L = 2 Z2 runs (same geometry, same sign sheet).

Usage: python exact_z2.py BETA [BETA ...] [--out exact_z2.json]
"""

import argparse
import json
import os
import sys
import time

import numpy as np
from scipy.sparse.linalg import LinearOperator, eigsh

L = 2
NL = 3 * L ** 3  # 24 spatial links
N = 1 << NL


def link(x, y, z, mu):
    return ((x % L) * L * L + (y % L) * L + (z % L)) * 3 + mu


def masks():
    plaq = []  # (bitmask of the 4 links, sign)
    for x in range(L):
        for y in range(L):
            for z in range(L):
                s = (x, y, z)
                for mu in range(3):
                    for nu in range(mu + 1, 3):
                        e = [0, 0, 0]
                        e[mu] = 1
                        f = [0, 0, 0]
                        f[nu] = 1
                        ls = [link(*s, mu), link(s[0] + e[0], s[1] + e[1], s[2] + e[2], nu),
                              link(s[0] + f[0], s[1] + f[1], s[2] + f[2], mu), link(*s, nu)]
                        assert len(set(ls)) == 4
                        m = 0
                        for b in ls:
                            m |= 1 << b
                        sign = -1.0 if (mu, nu) == (0, 1) and x == L - 1 and y == L - 1 else 1.0
                        plaq.append((m, sign))
    gauge = []
    for x in range(L):
        for y in range(L):
            for z in range(L):
                m = 0
                for mu in range(3):
                    m |= 1 << link(x, y, z, mu)
                    e = [0, 0, 0]
                    e[mu] = -1
                    m |= 1 << link(x + e[0], y + e[1], z + e[2], mu)
                gauge.append(m)
    omega = 0
    for x in range(L):
        for y in range(L):
            omega |= 1 << link(x, y, 0, 2)
    return plaq, gauge, omega


def parity(v):
    """popcount parity of uint32 array."""
    v = v ^ (v >> 16)
    v = v ^ (v >> 8)
    v = v ^ (v >> 4)
    v = v ^ (v >> 2)
    v = v ^ (v >> 1)
    return (v & 1).astype(np.int8)


def flux_energy(beta, plaq, gauge, omega, tol=1e-11):
    idx = np.arange(N, dtype=np.uint32)
    S = np.zeros(N)
    for m, sign in plaq:
        S += sign * (1 - 2 * parity(idx & np.uint32(m)).astype(np.float64))
    vhalf = np.exp(0.5 * beta * S)
    del S
    ep, em = np.exp(beta), np.exp(-beta)
    perm_g = [idx ^ np.uint32(m) for m in gauge]
    perm_o = idx ^ np.uint32(omega)
    del idx

    def proj(v, sector):
        for p in perm_g:
            v = 0.5 * (v + v[p])
        return 0.5 * (v + (1 if sector == 0 else -1) * v[perm_o])

    def kin(v):
        for l in range(NL):
            w = v.reshape(-1, 2, 1 << l)
            v = (ep * w + em * w[:, ::-1, :]).reshape(-1)
        return v

    out = {}
    for sector in (0, 1):
        def mv(v, sector=sector):
            v = proj(np.asarray(v).reshape(-1), sector)
            v = vhalf * kin(vhalf * v)
            return proj(v, sector)
        op = LinearOperator((N, N), matvec=mv, dtype=np.float64)
        rng = np.random.default_rng(1 + sector)
        v0 = proj(rng.random(N), sector)
        w = eigsh(op, k=1, which="LA", v0=v0, ncv=8, tol=tol, return_eigenvectors=False)
        out[sector] = float(w[0])
    # normalise to avoid overflow concerns: only the ratio matters
    aE = float(np.log(out[0] / out[1]))
    return aE, out


def main():
    p = argparse.ArgumentParser()
    p.add_argument("betas", nargs="+", type=float)
    p.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "exact_z2.json"))
    a = p.parse_args()
    plaq, gauge, omega = masks()
    res = {}
    if os.path.exists(a.out):
        res = json.load(open(a.out))
    for b in a.betas:
        t = time.time()
        aE, lam = flux_energy(b, plaq, gauge, omega)
        res[f"{b:g}"] = {"beta": b, "L": L, "aE": aE, "z": L * aE, "log_lambda0": float(np.log(lam[0])),
                         "log_lambda1": float(np.log(lam[1])), "seconds": time.time() - t}
        print(f"Z2 exact, twisted 2^3 box, beta = {b}: aE = {aE:.6f}, z = {L * aE:.6f}  ({time.time() - t:.0f} s)", flush=True)
        json.dump(res, open(a.out, "w"), indent=1)
    return 0


if __name__ == "__main__":
    sys.exit(main())
