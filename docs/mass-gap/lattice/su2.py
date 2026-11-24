"""Pure SU(2) lattice gauge theory in four dimensions: Wilson action, heat bath and overrelaxation, measured with smeared operators.

Written for docs/mass-gap/ (Gravity). It reproduces established numbers; it proves nothing. What it shows is the shape of the mass-gap
question: on a lattice a gap is always there in lattice units, and the question is whether it stays when the grid is made finer.

Conventions
-----------
- A link is an SU(2) matrix stored as a unit quaternion (a0, a1, a2, a3) meaning a0 + i(a1 s1 + a2 s2 + a3 s3), s the Pauli matrices.
  Then (1/2) tr U = a0, and the product of two links is the quaternion product below.
- Action S = beta * sum_p (1 - (1/2) tr U_p): the Wilson action, beta = 4/g^2.
- Lattice shape (T, L, L, L); direction 0 is time. Links U[mu] have shape (T, L, L, L, 4).
- Updates: Kennedy-Pendleton heat bath (Phys. Lett. B 156 (1985) 393) and microcanonical overrelaxation, on a checkerboard so that the
  links updated together never share a staple.
- Every random number comes from one numpy Generator seeded from the command line: a run is reproducible bit for bit on one platform.
"""

import numpy as np

# ---------------------------------------------------------------------------------------------------------------------------- algebra


def qmul(a, b):
    """Quaternion product of SU(2) elements (arrays with last axis 4)."""
    a0, a1, a2, a3 = a[..., 0], a[..., 1], a[..., 2], a[..., 3]
    b0, b1, b2, b3 = b[..., 0], b[..., 1], b[..., 2], b[..., 3]
    out = np.empty(np.broadcast_shapes(a.shape, b.shape))
    out[..., 0] = a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3
    # vector part: a0 b + b0 a - a x b
    out[..., 1] = a0 * b1 + b0 * a1 - (a2 * b3 - a3 * b2)
    out[..., 2] = a0 * b2 + b0 * a2 - (a3 * b1 - a1 * b3)
    out[..., 3] = a0 * b3 + b0 * a3 - (a1 * b2 - a2 * b1)
    return out


def qdag(a):
    """Hermitian conjugate (the inverse, for SU(2))."""
    out = -a.copy()
    out[..., 0] = a[..., 0]
    return out


def qnorm(a):
    return np.sqrt(np.sum(a * a, axis=-1))


def shift(x, mu, s):
    """The field at site x + s * mu-hat (periodic)."""
    return np.roll(x, -s, axis=mu)


# ---------------------------------------------------------------------------------------------------------------------------- lattice


class Lattice:
    def __init__(self, T, L, beta, seed):
        self.shape = (T, L, L, L)
        self.beta = beta
        self.rng = np.random.default_rng(seed)
        self.U = np.zeros((4,) + self.shape + (4,))
        self.U[..., 0] = 1.0  # cold start
        t, x, y, z = np.indices(self.shape)
        self.parity = [((t + x + y + z) % 2) == p for p in (0, 1)]

    # The sum of the six staples around link (x, mu): the local action is -(beta/2) Re tr(U_mu(x) A) with A this sum.
    def staple(self, mu):
        U = self.U
        A = np.zeros(self.shape + (4,))
        for nu in range(4):
            if nu == mu:
                continue
            # forward: U_nu(x+mu) U_mu(x+nu)^dag U_nu(x)^dag
            A += qmul(qmul(shift(U[nu], mu, 1), qdag(shift(U[mu], nu, 1))), qdag(U[nu]))
            # backward: U_nu(x+mu-nu)^dag U_mu(x-nu)^dag U_nu(x-nu)
            Unu_m = shift(U[nu], nu, -1)
            A += qmul(qmul(qdag(shift(Unu_m, mu, 1)), qdag(shift(U[mu], nu, -1))), Unu_m)
        return A

    def _kp_x0(self, alpha):
        """Kennedy-Pendleton: draw x0 in [-1, 1] with density sqrt(1 - x0^2) exp(alpha x0), vectorised with rejection."""
        rng = self.rng
        n = alpha.shape[0]
        x0 = np.empty(n)
        todo = np.arange(n)
        while todo.size:
            a = alpha[todo]
            r1 = 1.0 - rng.random(todo.size)
            r2 = rng.random(todo.size)
            r3 = 1.0 - rng.random(todo.size)
            r4 = rng.random(todo.size)
            lam2 = -(np.log(r1) + np.cos(2 * np.pi * r2) ** 2 * np.log(r3)) / (2 * a)
            ok = r4 * r4 <= 1.0 - lam2
            x0[todo[ok]] = 1.0 - 2.0 * lam2[ok]
            todo = todo[~ok]
        return x0

    def heatbath(self):
        rng = self.rng
        for mu in range(4):
            for p in (0, 1):
                m = self.parity[p]
                A = self.staple(mu)[m]
                k = qnorm(A)
                Ahat = A / k[:, None]
                x0 = self._kp_x0(self.beta * k)
                # random direction for the vector part
                v = rng.normal(size=(x0.size, 3))
                v /= np.linalg.norm(v, axis=1)[:, None]
                X = np.empty((x0.size, 4))
                X[:, 0] = x0
                X[:, 1:] = v * np.sqrt(np.maximum(0.0, 1.0 - x0 * x0))[:, None]
                # X = U Ahat is distributed as exp(beta k X0) dHaar, so U = X Ahat^dag
                Um = self.U[mu]
                Um[m] = qmul(X, qdag(Ahat))

    def overrelax(self):
        for mu in range(4):
            for p in (0, 1):
                m = self.parity[p]
                A = self.staple(mu)[m]
                Ahat = A / qnorm(A)[:, None]
                Ad = qdag(Ahat)
                Um = self.U[mu]
                # U' = Ahat^dag U^dag Ahat^dag keeps Re tr(U A) and is its own inverse map: microcanonical
                Um[m] = qmul(qmul(Ad, qdag(Um[m])), Ad)

    def reunitarise(self):
        self.U /= qnorm(self.U)[..., None]

    # ------------------------------------------------------------------------------------------------------------------ observables

    def plaquette_field(self, mu, nu, U=None):
        U = self.U if U is None else U
        return qmul(qmul(U[mu], shift(U[nu], mu, 1)), qmul(qdag(shift(U[mu], nu, 1)), qdag(U[nu])))

    def plaquette(self):
        s = 0.0
        for mu in range(4):
            for nu in range(mu + 1, 4):
                s += self.plaquette_field(mu, nu)[..., 0].mean()
        return s / 6.0

    def ape_smear_spatial(self, alpha=0.5, n=10):
        """APE smearing of the spatial links only (directions 1..3), within each time slice; projection back to SU(2) by normalising."""
        V = self.U.copy()
        for _ in range(n):
            W = V.copy()
            for i in (1, 2, 3):
                S = np.zeros(self.shape + (4,))
                for j in (1, 2, 3):
                    if j == i:
                        continue
                    S += qmul(qmul(V[j], shift(V[i], j, 1)), qdag(shift(V[j], i, 1)))
                    Vj_m = shift(V[j], j, -1)
                    S += qmul(qmul(qdag(Vj_m), shift(V[i], j, -1)), shift(Vj_m, i, 1))
                Wi = (1.0 - alpha) * V[i] + (alpha / 4.0) * S
                W[i] = Wi / qnorm(Wi)[..., None]
            V = W
        return V

    def line(self, V, mu, R, start=None):
        """The product of R links in direction mu starting at every site."""
        out = V[mu].copy()
        for r in range(1, R):
            out = qmul(out, shift(V[mu], mu, r))
        return out

    def wilson_loops(self, V, Rmax, Tmax):
        """W(R, T): spatial sides from the smeared links V, temporal sides from the unsmeared links, averaged over sites and the three
        spatial directions."""
        W = np.zeros((Rmax + 1, Tmax + 1))
        Ut = self.U[0]
        tl = {}
        for Tt in range(1, Tmax + 1):
            tl[Tt] = self.line(self.U, 0, Tt)
        for i in (1, 2, 3):
            for R in range(1, Rmax + 1):
                S = self.line(V, i, R)
                for Tt in range(1, Tmax + 1):
                    # S(x) T(x+R i) S(x+T 0)^dag T(x)^dag
                    loop = qmul(qmul(S, shift(tl[Tt], i, R)), qmul(qdag(shift(S, 0, Tt)), qdag(tl[Tt])))
                    W[R, Tt] += loop[..., 0].mean() / 3.0
        return W

    def glueball_ops(self, V):
        """Per time slice: the zero-momentum sums of the spatial 1x1 and 2x2 loops of the smeared links (A1++ projection: the sum over
        the three spatial planes)."""
        T = self.shape[0]
        ops = []
        for size in (1, 2):
            o = np.zeros(T)
            for i, j in ((1, 2), (1, 3), (2, 3)):
                a = self.line(V, i, size)
                b = self.line(V, j, size)
                loop = qmul(qmul(a, shift(b, i, size)), qmul(qdag(shift(a, j, size)), qdag(b)))
                o += loop[..., 0].sum(axis=(1, 2, 3))
            ops.append(o)
        return np.array(ops)  # shape (n_ops, T)
