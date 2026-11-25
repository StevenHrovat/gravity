"""Route (d), self-charge: at which scale does the diamagnetic deficit act? (small CPU check, 2026-11-21)

Question tested (new, not an established number we re-verify): the exact deficit identity of NOTE.md section 3 says that a
covariant random walk in a representation rho pays, against the free walk, the summed loop shortfall dim - Re chi_rho(loop).
For the gauge field's own disturbance rho is the adjoint: trivial for U(1) (photon: no deficit, massless), non-trivial for SU(2).
Claim of the note: this deficit acts at the LATTICE scale (lowest eigenvalue of the covariant Laplacian ~ g^2 in lattice units),
for every charged probe (SU(2) adjoint and fundamental, and also U(1) charge 1), so it cannot be the physical reach.

Observable: lambda_min of -Delta_U = sum_mu (2 - T_mu - T_mu^dag), (T_mu psi)(x) = rho(U_mu(x)) psi(x + mu), on thermalised
Wilson configurations on the periodic L^4 lattice. Prediction: lambda_min / g^2 roughly constant in beta (g^2 = 4/beta for SU(2),
e^2 = 1/beta for U(1)); neutral probe (U(1) adjoint): lambda_min = 0 exactly (constant mode).

Resources: CPU only, one process, a few minutes. Usage (from docs/mass-gap/):
  py weak-coupling/attempts/selfcharge/charged_probe.py
Writes weak-coupling/attempts/selfcharge/charged_probe.json.
"""

import json
import os
import sys
import time

os.environ.setdefault("CUDA_VISIBLE_DEVICES", "-1")

import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as sla

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "lattice"))
from su2 import Lattice  # noqa: E402  (our validated SU(2) heat bath)
from u1 import U1Lattice  # noqa: E402  (our validated U(1) heat bath)

PAULI = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]], dtype=complex)


def fund(q):
    """Quaternion (..., 4) -> 2x2 SU(2) matrix a0 + i a.sigma."""
    M = q[..., 0, None, None] * np.eye(2) + 1j * np.einsum("...k,kij->...ij", q[..., 1:], PAULI)
    return M


def adj(q):
    """Adjoint 3x3 real rotation R_ij = 1/2 Re tr(sigma_i U sigma_j U^dag)."""
    U = fund(q)
    Ud = np.conj(np.swapaxes(U, -1, -2))
    R = 0.5 * np.einsum("aij,...jk,bkl,...li->...ab", PAULI, U, PAULI, Ud).real
    return R


def cov_laplacian(shape, links, n):
    """-Delta_U as a sparse (V n) x (V n) matrix; links[mu] has shape shape + (n, n) (rho(U_mu(x)))."""
    V = int(np.prod(shape))
    idx = np.arange(V).reshape(shape)
    rows, cols, vals = [], [], []
    for mu in range(4):
        nb = np.roll(idx, -1, axis=mu).ravel()  # x + mu
        M = links[mu].reshape(V, n, n)
        # -T_mu block (x, x+mu) = -rho(U_mu(x)); -T_mu^dag block (x+mu, x) = -rho(U_mu(x))^dag
        for a in range(n):
            for b in range(n):
                rows.append(idx.ravel() * n + a); cols.append(nb * n + b); vals.append(-M[:, a, b])
                rows.append(nb * n + b); cols.append(idx.ravel() * n + a); vals.append(-np.conj(M[:, a, b]))
    H = sp.coo_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))), shape=(V * n, V * n)).tocsr()
    H = H + 8.0 * sp.identity(V * n, format="csr")
    return H


def lam_min(H):
    # Note: Lanczos "SA" missed the exact constant zero mode of the free (neutral) Laplacian on 8^4 (returned 2 - 2cos(2pi/8));
    # shift-invert gives 0. For the charged probes SA and shift-invert agree (checked at beta 16, L 8). See NOTE.md section 7.
    w = sla.eigsh(H, k=1, which="SA", return_eigenvectors=False, tol=1e-8)
    return float(np.real(w[0]))


def main():
    out = dict(note="lambda_min of covariant Laplacians on thermalised Wilson configurations", rows=[])
    t0 = time.time()
    for L in (6, 8):
        shape = (L, L, L, L)
        for beta in (4.0, 16.0, 64.0):
            lat = Lattice(L, L, beta, seed=1000 + int(beta) + L)
            for _ in range(50):
                lat.heatbath(); lat.overrelax(); lat.overrelax(); lat.reunitarise()
            la, lf = [], []
            for c in range(3):
                for _ in range(10):
                    lat.heatbath(); lat.overrelax(); lat.reunitarise()
                la.append(lam_min(cov_laplacian(shape, [adj(lat.U[m]) for m in range(4)], 3)))
                lf.append(lam_min(cov_laplacian(shape, [fund(lat.U[m]) for m in range(4)], 2)))
            g2 = 4.0 / beta
            row = dict(group="SU(2)", L=L, beta=beta, g2=g2, plaq=lat.plaquette(), adj=la, fund=lf,
                       adj_over_g2=float(np.mean(la) / g2), fund_over_g2=float(np.mean(lf) / g2))
            out["rows"].append(row)
            print(row, f"t={time.time() - t0:.0f}s", flush=True)
        for beta in (2.0, 8.0, 32.0):
            lat = U1Lattice(L, L, beta, seed=2000 + int(beta) + L)
            for _ in range(50):
                lat.heatbath(); lat.overrelax(); lat.overrelax()
            lc, ln = [], []
            for c in range(3):
                for _ in range(10):
                    lat.heatbath(); lat.overrelax()
                ph = np.exp(1j * lat.th)[..., None, None]
                lc.append(lam_min(cov_laplacian(shape, [ph[m] for m in range(4)], 1)))
                ln.append(lam_min(cov_laplacian(shape, [np.ones_like(ph[m]) for m in range(4)], 1)))
            e2 = 1.0 / beta
            row = dict(group="U(1)", L=L, beta=beta, e2=e2, plaq=float(lat.plaquette()), charge1=lc, neutral=ln,
                       charge1_over_e2=float(np.mean(lc) / e2))
            out["rows"].append(row)
            print(row, f"t={time.time() - t0:.0f}s", flush=True)
    with open(os.path.join(HERE, "charged_probe.json"), "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
