# R1 (OFFCENTRE.md): Balaban's average (0.4) on a perturbation supported on the star of one fine site x, at every
# position of x in its block (centre and off-centre). Claim: the part of every averaging loop inside the block B(y)
# has the same law for all coarse bonds at y, so it is a coarse gauge shift and cancels in coarse loops; only the
# straight segments transmit the perturbation, with weight <= L^{1-d} per bond: the change of every coarse plaquette
# is <= 2 * (2 L^{1-d}) * max|a| for a star (two bonds per direction). Printed: max over positions of
# (max coarse plaquette angle) / (max |a|), against the bound 4 L^{1-d}; also the coarse bonds that moved.
# Usage: python -I offcentre_cancel.py      (d = 4, L = 3; one level; about a minute)
import sys, itertools
import numpy as np
sys.argv = [sys.argv[0], '4', '3', '1', '0.0']
src = open(__file__.replace('offcentre_cancel.py', 'lattice_twist.py')).read()
d, L = 4, 3; h = (L - 1) // 2
ns = {'np': np, 'itertools': itertools, 'd': d, 'L': L, 'h': h}
exec(src.split('# ---------- quaternions (SU(2)) ----------')[1].split('def decimate_labels')[0], ns)
qexp, qmul, plaquettes, block_04, angle = (ns[k] for k in ['qexp', 'qmul', 'plaquettes', 'block_04', 'angle'])

N = 9; rng = np.random.default_rng(3); delta = 1e-4
U0 = np.zeros((d,) + (N,) * d + (4,)); U0[..., 0] = 1.0
V0 = block_04(U0)
worst = 0.0; rows = []
for r in itertools.product(range(-h, h + 1), repeat=d):
    if any(r[i] < 0 for i in range(d)) or list(r) != sorted(r, reverse=True):
        continue                                          # one representative per symmetry class
    x = tuple(L + h + r[i] for i in range(d))             # site in the block of coarse site (1,1,1,1)
    U = U0.copy(); amax = 0.0
    for mu in range(d):
        for sgn in (0, -1):                               # bond x -> x+e_mu and bond x-e_mu -> x
            b = list(x); b[mu] += sgn
            a = rng.normal(size=3); a *= delta / np.linalg.norm(a)
            U[mu][tuple(b)] = qmul(qexp(a), U[mu][tuple(b)]); amax = max(amax, np.linalg.norm(a))
    V = block_04(U)
    pmax = max(angle(plaquettes(V, m, n)).max() for m in range(d) for n in range(m + 1, d))
    moved = sum(int(np.sum(np.linalg.norm(V[m][..., 1:] - V0[m][..., 1:], axis=-1) > 1e-12)) for m in range(d))
    ratio = pmax / amax; worst = max(worst, ratio)
    rows.append((r, ratio, moved))
for r, ratio, moved in rows:
    print(f'offset {r}: max coarse plaquette / max|a| = {ratio:.4f}   coarse bonds moved: {moved}')
print(f'worst ratio {worst:.4f}; bound 4 L^(1-d) = {4 * L ** (1 - d):.4f}')
