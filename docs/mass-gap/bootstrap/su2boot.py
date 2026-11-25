"""Positivity bootstrap for SU(2) lattice Yang-Mills: loops, loop equations, positivity matrices, symmetry reduction.

Written from scratch for docs/mass-gap/bootstrap (Gravity). Method after Kazakov and Zheng (arXiv:2404.16925); see PREREG-BOOTSTRAP.md.

Conventions
-----------
- A path is a tuple of steps; a step is +a or -a for an axis a in 1..d (a move by +-e_a). Paths start at the origin.
- A loop is a closed path. w(C) = < (1/2) tr U_C >, real for SU(2); w(C^-1) = w(C); w(trivial) = 1.
- Loop classes: free reduction, cyclic rotation, orientation reversal, the hypercubic group (axis permutations and reflections) and
  translations. The canonical key is a tuple of codes (0 = +e1, 1 = -e1, 2 = +e2, ...) that is lexicographically smallest over all
  images; the empty tuple is the trivial loop.
- Wilson action S = -(beta/2) sum_p tr U_p. Loop equation coefficients are pairs (c0, c1) meaning c0 + c1 * beta (Fractions).
"""

import os
os.environ['CUDA_VISIBLE_DEVICES'] = '-1'  # never touch the GPU (it runs other jobs); set before any other import


from fractions import Fraction
import itertools
import numpy as np

# ---------------------------------------------------------------------------------------------------------------------------- paths


def inv(p):
    """The reversed path (the inverse group element)."""
    return tuple(-s for s in reversed(p))


def reduce_path(p):
    """Free reduction: remove adjacent s, -s pairs."""
    out = []
    for s in p:
        if out and out[-1] == -s:
            out.pop()
        else:
            out.append(s)
    return tuple(out)


def cyc_reduce(p):
    p = list(reduce_path(p))
    i, j = 0, len(p) - 1
    while i < j and p[i] == -p[j]:
        i += 1
        j -= 1
    return tuple(p[i:j + 1])


def endpoint(p, d):
    x = [0] * d
    for s in p:
        x[abs(s) - 1] += 1 if s > 0 else -1
    return tuple(x)


def sites(p, d):
    """Sites visited, including start and end."""
    x = [0] * d
    out = [tuple(x)]
    for s in p:
        x[abs(s) - 1] += 1 if s > 0 else -1
        out.append(tuple(x))
    return out


def unit(s, d):
    x = [0] * d
    x[abs(s) - 1] = 1 if s > 0 else -1
    return tuple(x)


# ---------------------------------------------------------------------------------------------------------------------------- canonical form

_CANON = {}


def _relabel(seq):
    """Greedy relabelling: the lexicographically smallest image of seq under axis permutations and reflections."""
    amap = {}
    out = []
    nxt = 0
    for s in seq:
        a = s if s > 0 else -s
        if a not in amap:
            amap[a] = (nxt, 1 if s > 0 else -1)
            nxt += 1
        na, sg = amap[a]
        out.append(2 * na + (0 if (sg > 0) == (s > 0) else 1))
    return tuple(out)


def canon(p):
    """Canonical key of the loop class of the closed path p."""
    c = cyc_reduce(p)
    r = _CANON.get(c)
    if r is not None:
        return r
    n = len(c)
    if n == 0:
        _CANON[c] = ()
        return ()
    best = None
    ci = inv(c)
    for q in (c, ci):
        for k in range(n):
            img = _relabel(q[k:] + q[:k])
            if best is None or img < best:
                best = img
    _CANON[c] = best
    return best


def key_to_path(key):
    return tuple((c // 2 + 1) * (1 if c % 2 == 0 else -1) for c in key)


def rect(R, T):
    """The R x T rectangle in the (1, 2) plane as a path."""
    return (1,) * R + (2,) * T + (-1,) * R + (-2,) * T


# ---------------------------------------------------------------------------------------------------------------------------- enumeration


def based_closed_paths(d, lmax, accept=None):
    """All reduced (non-backtracking) closed paths of length <= lmax starting at the origin, including the empty path.
    accept(site) -> bool restricts the visited sites (e.g. a half space)."""
    out = [()]
    steps = [s for a in range(1, d + 1) for s in (a, -a)]

    def rec(path, pos):
        L = len(path)
        if L >= lmax:
            return
        dist = sum(abs(c) for c in pos)
        for s in steps:
            if path and path[-1] == -s:
                continue
            np_ = list(pos)
            np_[abs(s) - 1] += 1 if s > 0 else -1
            np_ = tuple(np_)
            nd = sum(abs(c) for c in np_)
            if nd > lmax - L - 1:
                continue
            if accept is not None and not accept(np_):
                continue
            q = path + (s,)
            if nd == 0:
                out.append(q)
            rec(q, np_)

    rec((), tuple([0] * d))
    return out


def cyclic_loops(d, lmax):
    """Canonical keys of all loop classes (cyclically reduced) of length 1..lmax."""
    keys = set()
    for p in based_closed_paths(d, lmax):
        c = cyc_reduce(p)
        if len(c) == len(p) and p:
            keys.add(canon(p))
    return sorted(keys, key=lambda k: (len(k), k))


# ---------------------------------------------------------------------------------------------------------------------------- loop equations


def _add(eq, key, c0, c1=Fraction(0)):
    a, b = eq.get(key, (Fraction(0), Fraction(0)))
    eq[key] = (a + c0, b + c1)


def loop_equation(W, v, d):
    """Schwinger-Dyson equation for the closed path W based at the origin and the link V leaving the origin in direction v.
    Returns {key: (c0, c1)} meaning sum_key (c0 + c1 beta) w(key) = 0 (w of the trivial key () is 1)."""
    eq = {}
    pos = sites(W, d)
    origin = pos[0]
    ev = unit(v, d)
    q = Fraction(1, 4)
    h = Fraction(1, 2)
    for k, s in enumerate(W):
        if s == v and pos[k] == origin:  # W = A V B
            A, VB = W[:k], W[k:]
            _add(eq, canon(W), q)
            _add(eq, canon(A + inv(VB)), h)
        elif s == -v and pos[k] == ev:  # W = A V^-1 B
            AV, B = W[:k + 1], W[k + 1:]
            _add(eq, canon(W), -q)
            _add(eq, canon(AV + inv(B)), -h)
    b8 = Fraction(1, 8)
    for a in range(1, d + 1):
        if a == abs(v):
            continue
        for rho in (a, -a):
            S = (rho, -v, -rho)  # staple from e_v back to the origin
            _add(eq, canon(W + (v,) + S), Fraction(0), b8)
            _add(eq, canon(W + inv(S) + (-v,)), Fraction(0), -b8)
    return {k: c for k, c in eq.items() if c[0] != 0 or c[1] != 0}


def eq_signature(eq):
    """Normalised form for deduplication (scale by the first coefficient)."""
    items = sorted(eq.items())
    k0, (a0, b0) = items[0]
    s = a0 if a0 != 0 else b0
    return tuple((k, a / s, b / s) for k, (a, b) in items)


def all_loop_equations(d, Lmax, Wmax=None, loops=None, tails=True, sub_d=None):
    """Loop equations from every cyclically reduced loop class W with |W| <= Wmax (default Lmax - 4), rotated to each vertex, and
    every link leaving that vertex; kept if every loop in it has length <= Lmax. Also the equations from the trivial path."""
    if Wmax is None:
        Wmax = Lmax - 4
    if tails:
        # complete family: every reduced closed path W based at the origin (tails allowed), V = +e1 (all V are equivalent under the
        # point group once W runs over all based paths)
        eqs = {}
        for W in based_closed_paths(d if sub_d is None else sub_d, Wmax):
            eq = loop_equation(W, 1, d)
            if not eq or max(len(k) for k in eq) > Lmax:
                continue
            sig = eq_signature(eq)
            if sig not in eqs:
                eqs[sig] = eq
        return list(eqs.values())
    if loops is None:
        loops = cyclic_loops(d, Wmax)
    eqs = {}
    steps = [s for a in range(1, d + 1) for s in (a, -a)]
    bases = [()] + [key_to_path(k) for k in loops if len(k) <= Wmax]
    for P in bases:
        n = len(P)
        rots = set()
        for k in range(max(n, 1)):
            for Q in (P[k:] + P[:k], inv(P[k:] + P[:k])):
                rots.add(Q)
        for Q in rots:
            for v in steps:
                eq = loop_equation(Q, v, d)
                if not eq:
                    continue
                if max(len(k) for k in eq) > Lmax:
                    continue
                sig = eq_signature(eq)
                if sig not in eqs:
                    eqs[sig] = eq
    return list(eqs.values())


# ---------------------------------------------------------------------------------------------------------------------------- positivity


def _reflect_axis(p, a):
    return tuple(-s if abs(s) == a else s for s in p)


def _swap_axes(p, a, b):
    out = []
    for s in p:
        if abs(s) == a:
            out.append(b if s > 0 else -b)
        elif abs(s) == b:
            out.append(a if s > 0 else -a)
        else:
            out.append(s)
    return tuple(out)


def _words(kind, Ai, Aj):
    """The (M, N) loop words of a positivity family for the basis paths Ai, Aj."""
    if kind == 'G':
        return inv(Ai) + Aj, Ai + Aj
    if kind == 'RS':
        r = _reflect_axis(Ai, 1)
        return inv(r) + Aj, r + Aj
    if kind == 'RD':
        r = _swap_axes(Ai, 1, 2)
        return inv(r) + Aj, r + Aj
    if kind == 'RL':
        # loop: (+1) A_j (-1) followed by r(A_i)^-1 (or r(A_i)), A_i the inner part; r maps x1 -> 1 - x1 (negates axis-1 steps)
        r = _reflect_axis(Ai[1:-1], 1)
        return Aj + inv(r), Aj + r
    raise ValueError(kind)


def _key_rows(args):
    kind, basis, i0, i1 = args
    n = len(basis)
    out = []
    for i in range(i0, i1):
        rowM, rowN = [], []
        for j in range(i, n):
            wm, wn = _words(kind, basis[i], basis[j])
            rowM.append(canon(wm))
            rowN.append(canon(wn))
        out.append((rowM, rowN))
    return out


def positivity_family(kind, d, lpos, sub_d=None, prod=None, procs=12):
    """Basis and the (M, N) key matrices of one positivity family.
    kind: 'G' (Hermitian), 'RS' (site reflection x1 -> -x1), 'RD' (diagonal x1 <-> x2), 'RL' (link reflection x1 -> 1 - x1).
    sub_d: restrict basis paths to the first sub_d axes (dimensional truncation).
    prod: also include the reduced products A B of two basis paths of length <= prod (KZ-like 'level 2' lines; not for RL).
    Returns dict with basis (list of paths), Mkey, Nkey (n x n object arrays of canonical keys)."""
    dd = d if sub_d is None else sub_d
    acc = {'G': None, 'RS': (lambda x: x[0] >= 0), 'RD': (lambda x: x[0] >= x[1]), 'RL': (lambda x: x[0] >= 0)}[kind]
    if kind == 'RL':
        inner = based_closed_paths(dd, max(lpos - 2, 0), accept=acc)
        basis = [(1,) + A + (-1,) for A in inner]
    else:
        basis = based_closed_paths(dd, lpos, accept=acc)
        if prod:
            short = based_closed_paths(dd, prod, accept=acc)
            seen = set(basis)
            for A in short:
                for B in short:
                    P = reduce_path(A + B)
                    if P not in seen:
                        seen.add(P)
                        basis.append(P)
    n = len(basis)
    Mkey = np.empty((n, n), dtype=object)
    Nkey = np.empty((n, n), dtype=object)
    if n > 1500 and procs > 1:
        from multiprocessing import Pool
        chunks = []
        step = max(1, n // (procs * 8))
        for i0 in range(0, n, step):
            chunks.append((kind, basis, i0, min(n, i0 + step)))
        with Pool(procs) as pool:
            res = pool.map(_key_rows, chunks)
        rows = [r for part in res for r in part]
    else:
        rows = _key_rows((kind, basis, 0, n))
    for i, (rowM, rowN) in enumerate(rows):
        for jj, (km, kn) in enumerate(zip(rowM, rowN)):
            j = i + jj
            Mkey[i, j] = Mkey[j, i] = km
            Nkey[i, j] = Nkey[j, i] = kn
    return dict(kind=kind, basis=basis, Mkey=Mkey, Nkey=Nkey)


def check_symmetric(fam):
    """M and N must be symmetric as key matrices (built symmetric above; this checks the claim w(word(i,j)) = w(word(j,i)))."""
    kind, basis = fam['kind'], fam['basis']
    bad = 0
    import random
    rnd = random.Random(1)
    n = len(basis)
    for _ in range(min(2000, n * n)):
        i, j = rnd.randrange(n), rnd.randrange(n)
        if kind == 'G':
            a, b = canon(inv(basis[i]) + basis[j]), canon(inv(basis[j]) + basis[i])
            c, e = canon(basis[i] + basis[j]), canon(basis[j] + basis[i])
        elif kind == 'RS':
            r = lambda p: _reflect_axis(p, 1)
            a, b = canon(inv(r(basis[i])) + basis[j]), canon(inv(r(basis[j])) + basis[i])
            c, e = canon(r(basis[i]) + basis[j]), canon(r(basis[j]) + basis[i])
        elif kind == 'RD':
            r = lambda p: _swap_axes(p, 1, 2)
            a, b = canon(inv(r(basis[i])) + basis[j]), canon(inv(r(basis[j])) + basis[i])
            c, e = canon(r(basis[i]) + basis[j]), canon(r(basis[j]) + basis[i])
        else:
            r = lambda p: _reflect_axis(p, 1)
            a, b = canon(basis[j] + inv(r(basis[i][1:-1]))), canon(basis[i] + inv(r(basis[j][1:-1])))
            c, e = canon(basis[j] + r(basis[i][1:-1])), canon(basis[i] + r(basis[j][1:-1]))
        bad += (a != b) + (c != e)
    return bad


# ---------------------------------------------------------------------------------------------------------------------------- symmetry


def _group_perms(fam, d, sub_d=None):
    """Permutations of the basis induced by the symmetries of the family: signed axis permutations that preserve the half space
    (and the reflection), and path inversion. Returns list of index arrays (generators suffice for averaging? no: full group)."""
    kind, basis = fam['kind'], fam['basis']
    dd = d if sub_d is None else sub_d
    idx = {p: i for i, p in enumerate(basis)}
    elems = []
    for perm in itertools.permutations(range(1, dd + 1)):
        for signs in itertools.product((1, -1), repeat=dd):
            m = {a: perm[a - 1] * signs[a - 1] for a in range(1, dd + 1)}
            if kind in ('RS', 'RL'):
                if m[1] != 1:
                    continue
            elif kind == 'RD':
                if not (m[1] == 1 and m[2] == 2) and not (m[1] == -2 and m[2] == -1):
                    continue
            elems.append(m)

    def apply(m, p):
        return tuple(m[abs(s)] * (1 if s > 0 else -1) for s in p)

    perms = []
    for m in elems:
        for inversion in (False, True):
            pm = np.empty(len(basis), dtype=np.int64)
            ok = True
            for i, p in enumerate(basis):
                if kind == 'RL':
                    A = apply(m, p[1:-1])
                    q = (1,) + (inv(A) if inversion else A) + (-1,)
                else:
                    q = apply(m, p)
                    if inversion:
                        q = inv(q)
                j = idx.get(q)
                if j is None:
                    ok = False
                    break
                pm[i] = j
            if ok:
                perms.append(pm)
    return perms


def symmetry_blocks(fam, d, sub_d=None, seed=0, tol=1e-9):
    """Numerical block-diagonalisation of the commutant of the family's symmetry group.
    Returns list of blocks; each block is an n x m matrix E whose columns are orthonormal vectors (first basis vector of each copy of
    one irreducible representation), so that E^T X E is the reduced block of any invariant matrix X; and the multiplicity d_rho."""
    n = len(fam['basis'])
    perms = _group_perms(fam, d, sub_d)
    Mk = fam['Mkey']
    # verify invariance of the key matrices
    rng = np.random.default_rng(seed)
    for pm in perms[:: max(1, len(perms) // 8)]:
        ii = rng.integers(0, n, 200)
        jj = rng.integers(0, n, 200)
        for i, j in zip(ii, jj):
            assert Mk[pm[i], pm[j]] == Mk[i, j], 'family not invariant'
    R = rng.standard_normal((n, n))
    R = R + R.T
    R2 = rng.standard_normal((n, n))
    R2 = R2 + R2.T
    C = np.zeros((n, n))
    C2 = np.zeros((n, n))
    for pm in perms:
        C += R[np.ix_(pm, pm)]
        C2 += R2[np.ix_(pm, pm)]
    C /= len(perms)
    C2 /= len(perms)
    # unpermute: C[i,j] = mean_g R[g i, g j] is invariant
    lam, V = np.linalg.eigh(C)
    # cluster eigenvalues
    groups = []
    start = 0
    scale = max(1.0, np.abs(lam).max())
    for k in range(1, n + 1):
        if k == n or lam[k] - lam[k - 1] > tol * scale:
            groups.append(list(range(start, k)))
            start = k
    spaces = [V[:, g] for g in groups]
    # isotypic types: spaces linked by C2
    nsp = len(spaces)
    parent = list(range(nsp))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    dims = [s.shape[1] for s in spaces]
    for a in range(nsp):
        for b in range(a + 1, nsp):
            if dims[a] != dims[b]:
                continue
            X = spaces[a].T @ C2 @ spaces[b]
            if np.abs(X).max() > 1e-7:
                parent[find(a)] = find(b)
    types = {}
    for a in range(nsp):
        types.setdefault(find(a), []).append(a)
    blocks = []
    for t, members in types.items():
        V1 = spaces[members[0]]
        dr = V1.shape[1]
        cols = [V1[:, 0]]
        for b in members[1:]:
            X = spaces[b].T @ C2 @ V1  # intertwiner, alpha * orthogonal
            alpha = np.sqrt(np.abs(np.linalg.det(X.T @ X)) ** (1.0 / dr)) if dr > 0 else 1.0
            e = spaces[b] @ (X[:, 0] / np.linalg.norm(X[:, 0]))
            cols.append(e)
        E = np.array(cols).T
        blocks.append(dict(E=E, d_rho=dr))
    return blocks, len(perms)


def reduce_family(fam, d, sub_d=None, check=True, seed=1):
    """Reduced block coefficient matrices for the two channels M + N and M - N.
    Returns list of blocks: dict(E, d_rho, chan (+1/-1)), plus the used keys per entry for assembly."""
    blocks, gsize = symmetry_blocks(fam, d, sub_d)
    if check:
        rng = np.random.default_rng(seed)
        keys = set(fam['Mkey'].ravel()) | set(fam['Nkey'].ravel())
        val = {k: rng.standard_normal() for k in keys}
        val[()] = 1.0
        vf = np.vectorize(lambda k: val[k], otypes=[float])
        X = vf(fam['Mkey']) + vf(fam['Nkey'])
        Eall = np.hstack([b['E'] for b in blocks])
        # off-block test on the first copies: E_a^T X E_b should vanish between different blocks
        off = 0.0
        tot = 0.0
        ofs = np.cumsum([0] + [b['E'].shape[1] for b in blocks])
        Y = Eall.T @ X @ Eall
        for a in range(len(blocks)):
            for b in range(len(blocks)):
                blk = Y[ofs[a]:ofs[a + 1], ofs[b]:ofs[b + 1]]
                if a == b:
                    tot += (blk ** 2).sum()
                else:
                    off += (blk ** 2).sum()
        assert off <= 1e-12 * max(tot, 1.0), ('block-diagonalisation failed', off, tot)
        # dimension count
        assert sum(b['E'].shape[1] * b['d_rho'] for b in blocks) == len(fam['basis'])
    return blocks, gsize
