"""Compact U(1) lattice gauge theory in four dimensions (the lattice theory of light): Wilson action, exact heat bath (von Mises) and
overrelaxation, and the photon correlator at the smallest non-zero momentum.

Why it is here (docs/mass-gap/README.md, "The photon test"): every argument for a mass gap must fail for light, which is massless.
Four-dimensional U(1) has two phases: at strong coupling (beta below about 1.01) it confines and is gapped; at weak coupling it is the
Coulomb phase with a massless photon (Guth 1980, Froehlich and Spencer 1982, both rigorous). In the Coulomb phase the lightest state at
momentum p has energy that goes to zero with p, so in a box of side L it falls like 2 pi / L: no gap.

Conventions: link angles theta[mu] of shape (T, L, L, L), plaquette angle theta_mu(x) + theta_nu(x+mu) - theta_mu(x+nu) - theta_nu(x),
action S = beta * sum_p (1 - cos theta_p).
"""

import numpy as np


def shift(x, mu, s):
    return np.roll(x, -s, axis=mu)


class U1Lattice:
    def __init__(self, T, L, beta, seed):
        self.shape = (T, L, L, L)
        self.beta = beta
        self.rng = np.random.default_rng(seed)
        self.th = np.zeros((4,) + self.shape)  # cold start (ordered), so the Coulomb phase is reached without tunnelling
        t, x, y, z = np.indices(self.shape)
        self.parity = [((t + x + y + z) % 2) == p for p in (0, 1)]

    def staple(self, mu):
        """Complex staple sum A with local action -beta Re(e^{i theta_mu(x)} A)."""
        th = self.th
        A = np.zeros(self.shape, dtype=complex)
        for nu in range(4):
            if nu == mu:
                continue
            A += np.exp(1j * (shift(th[nu], mu, 1) - shift(th[mu], nu, 1) - th[nu]))
            tn_m = shift(th[nu], nu, -1)
            A += np.exp(1j * (-shift(tn_m, mu, 1) - shift(th[mu], nu, -1) + tn_m))
        return A

    def heatbath(self):
        for mu in range(4):
            for p in (0, 1):
                m = self.parity[p]
                A = self.staple(mu)[m]
                k, phi = np.abs(A), np.angle(A)
                # weight exp(beta k cos(theta + phi)): theta = -phi + von Mises(0, beta k)
                new = -phi + self.rng.vonmises(0.0, self.beta * k)
                tm = self.th[mu]
                tm[m] = np.angle(np.exp(1j * new))

    def overrelax(self):
        for mu in range(4):
            for p in (0, 1):
                m = self.parity[p]
                phi = np.angle(self.staple(mu)[m])
                tm = self.th[mu]
                tm[m] = np.angle(np.exp(1j * (-2 * phi - tm[m])))

    def plaq_angle(self, mu, nu):
        th = self.th
        return th[mu] + shift(th[nu], mu, 1) - shift(th[mu], nu, 1) - th[nu]

    def plaquette(self):
        return np.mean([np.cos(self.plaq_angle(mu, nu)).mean() for mu in range(4) for nu in range(mu + 1, 4)])

    def ape_smear_spatial(self, th, alpha=0.5, n=5):
        """APE smearing of the spatial link angles within each time slice: z = (1 - alpha) e^{i theta} + (alpha / 4) * staples."""
        th = th.copy()
        for _ in range(n):
            new = th.copy()
            for i in (1, 2, 3):
                S = np.zeros(self.shape, dtype=complex)
                for j in (1, 2, 3):
                    if j == i:
                        continue
                    S += np.exp(1j * (th[j] + shift(th[i], j, 1) - shift(th[j], i, 1)))
                    tj_m = shift(th[j], j, -1)
                    S += np.exp(1j * (-tj_m + shift(th[i], j, -1) + shift(tj_m, i, 1)))
                new[i] = np.angle((1 - alpha) * np.exp(1j * th[i]) + (alpha / 4) * S)
            th = new
        return th

    def loop_angle(self, th, i, j, size):
        """The angle of the size x size spatial loop in plane (i, j) at every site."""
        def line(mu, n):
            out = th[mu].copy()
            for r in range(1, n):
                out = out + shift(th[mu], mu, r)
            return out
        a, b = line(i, size), line(j, size)
        return a + shift(b, i, size) - shift(a, j, size) - b

    def photon_ops(self, nmom=(1, 2), levels=((4, 1), (12, 1), (12, 2))):
        """Per time slice: sin of a smeared spatial loop in plane (i, j) (the magnetic field component normal to the plane),
        Fourier-projected to momentum n * 2 pi / L along i, which lies in the plane, so the field is transverse to the momentum (a
        field along its own momentum is zero for light: magnetic field lines have no ends). Three planes, and each (smearing steps,
        loop size) in levels. Returns complex array (len(nmom), len(levels), 3, T)."""
        T, L = self.shape[0], self.shape[1]
        out = np.zeros((len(nmom), len(levels), 3, T), dtype=complex)
        planes = ((1, 2, 1), (2, 3, 2), (3, 1, 3))  # (i, j, momentum direction)
        coords = np.arange(L)
        th, done = self.th, 0
        for o, (ns, size) in enumerate(levels):
            if ns > done:
                th = self.ape_smear_spatial(th, n=ns - done)
                done = ns
            for c, (i, j, k) in enumerate(planes):
                b = np.sin(self.loop_angle(th, i, j, size))
                for a, n in enumerate(nmom):
                    phase = np.exp(2j * np.pi * n * coords / L)
                    shape = [1, 1, 1, 1]
                    shape[k] = L
                    out[a, o, c] = (b * phase.reshape(shape)).sum(axis=(1, 2, 3))
        return out
