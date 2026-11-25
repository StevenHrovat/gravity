# Linear (abelian) weights of Balaban's bond average [I] (0.3)-(0.4) on the star of a fine site.
# For a coarse bond c = (y, y + L e_c) the average is over x in B(y) (weight L^-d), over the shortest-path
# family G(y, x) (all orders of the nonzero directions, equal weight), then the straight fine segment from x
# to x + L e_c, then a contour inside B(y + L e_c) (which never touches B(y)).  Linearised around the trivial
# field, the coarse bond variable is the weighted sum of the fine bond variables along the paths.  This script
# computes, for a fine site z in B(y), the coefficient F_z(c, b) of each fine star bond b = (z, z + s e_mu) of z
# (signed: +1 per traversal z -> z + s e_mu, -1 per traversal back).
# Usage:  python -I star_weights.py [L] [d]      (CPU only, seconds; default L = 13, d = 4)
import itertools, sys
from fractions import Fraction

L = int(sys.argv[1]) if len(sys.argv) > 1 else 13
d = int(sys.argv[2]) if len(sys.argv) > 2 else 4
h = (L - 1) // 2
dirs = [(mu, s) for mu in range(d) for s in (1, -1)]


def path_sites(y, x, perm, cdir):
    """Sites visited by: shortest path y -> x in direction order perm, then L steps along +e_cdir."""
    pts = [tuple(y)]
    cur = list(y)
    for mu in perm:
        step = 1 if x[mu] > cur[mu] else -1
        while cur[mu] != x[mu]:
            cur[mu] += step
            pts.append(tuple(cur))
    for _ in range(L):
        cur[cdir] += 1
        pts.append(tuple(cur))
    return pts


def coeffs(z, cdir):
    """F_z(c, b) for c = +e_cdir out of y = 0, b over the 2d star bonds of z (exact fractions)."""
    y = (0,) * d
    F = {b: Fraction(0) for b in dirs}
    wx = Fraction(1, L ** d)
    rng = range(-h, h + 1)
    for x in itertools.product(rng, repeat=d):
        nz = [mu for mu in range(d) if x[mu] != 0]
        perms = list(itertools.permutations(nz)) or [()]
        wp = wx / len(perms)
        for perm in perms:
            pts = path_sites(y, x, perm, cdir)
            for p, q in zip(pts, pts[1:]):
                if p == z or q == z:
                    mu = next(i for i in range(d) if p[i] != q[i])
                    if p == z:
                        F[(mu, q[mu] - p[mu])] += wp
                    else:
                        F[(mu, p[mu] - q[mu])] -= wp
    return F


def tv(F1, F2):
    return sum(abs(F1[b] - F2[b]) for b in dirs) / 2


if __name__ == "__main__":
    z0 = (0,) * d
    Fc = {c: coeffs(z0, c) for c in range(d)}
    F = Fc[0]
    e1 = Fraction(L + 1, 2 * L ** d)
    e2 = Fraction(L - 1, 2 * L ** d)
    q = F[(1, 1)] if d > 1 else None
    print(f"L={L} d={d}: centre star, coarse bond +e0")
    for b in dirs:
        print("  b =", b, "coefficient", F[b], float(F[b]))
    print("  row sum", sum(F.values()))
    ok = all(F[b] == q for b in dirs if b[0] != 0) and F[(0, 1)] == q + e1 and F[(0, -1)] == q - e2
    print("  matches q + e1[b=c] - e2[b=-c] with e1=(L+1)/(2L^d), e2=(L-1)/(2L^d):", ok, " q =", q)
    print("  Dobrushin coefficient +e0 vs +e1:", tv(Fc[0], Fc[1]), " L^(1-d) =", Fraction(1, L ** (d - 1)))
    # off-centre sites: fraction of the coarse bond's paths through z (rows sum to zero there)
    if len(sys.argv) > 3:
        worst = Fraction(0)
        for z in itertools.product(range(-h, h + 1), repeat=d):
            if z == z0:
                continue
            for c in range(d):
                s = sum(abs(v) for v in coeffs(z, c).values()) / 2
                worst = max(worst, s)
        print("  max over off-centre z, c of (1/2) sum_b |F_z(c,b)|:", worst, float(worst))
