"""SDP assembly, Clarabel solve and exact-arithmetic certificate for the SU(2) lattice bootstrap (see su2boot.py, PREREG-BOOTSTRAP.md).

Standard form (Clarabel): min q.x  s.t.  A x + s = b,  s in K = {0}^neq x R+^(2 nvar) x PSD blocks.
Dual: z in K*, stationarity q + A^T z = 0. For any feasible x and any z = (y, lambda, Z) with Z >= 0:
    q.x = -b.z + z.s + rho.x >= -b_eq.y - sum_k <Z_k, B0_k> + rho.x,   rho = q + A^T z (lambda dropped),
and |x_c| <= 1 gives the rigorous bound q.x >= -b_eq.y - <Z, B0> - ||rho||_1.
"""

import os
os.environ['CUDA_VISIBLE_DEVICES'] = '-1'  # never touch the GPU (it runs other jobs); set before any other import


import os
import pickle
import time
from fractions import Fraction

import numpy as np
import scipy.sparse as sp

import su2boot as sb

CACHE = os.environ.get('SU2BOOT_CACHE', os.path.join(os.environ.get('TEMP', '.'), 'su2boot_cache'))


def _svec_index(m):
    """(i, j) of the upper triangle in Clarabel's column-major order, and the sqrt(2) scales of the off-diagonal entries."""
    ii, jj, sc = [], [], []
    for j in range(m):
        for i in range(j + 1):
            ii.append(i)
            jj.append(j)
            sc.append(1.0 if i == j else np.sqrt(2.0))
    return np.array(ii), np.array(jj), np.array(sc)


def build_family(kind, d, lpos, sub_d=None, verbose=True, prod=None):
    """Family key matrices and symmetry blocks (cached on disk)."""
    os.makedirs(CACHE, exist_ok=True)
    fn = os.path.join(CACHE, f'fam_{kind}_d{d}_l{lpos}_s{sub_d}' + (f'_p{prod}' if prod else '') + '.pkl')
    if os.path.exists(fn):
        with open(fn, 'rb') as f:
            return pickle.load(f)
    t0 = time.time()
    fam = sb.positivity_family(kind, d, lpos, sub_d, prod)
    bad = sb.check_symmetric(fam)
    assert bad == 0, f'{kind}: asymmetric key matrix ({bad})'
    if len(fam['basis']) > 1:
        blocks, gsize = sb.reduce_family(fam, d, sub_d)
    else:
        blocks, gsize = [dict(E=np.ones((1, 1)), d_rho=1)], 1
    fam['blocks'] = blocks
    fam['group_order'] = gsize
    fam['seconds'] = time.time() - t0
    if verbose:
        print(f'  family {kind} d={d} l={lpos} sub={sub_d} prod={prod}: n={len(fam["basis"])}, group {gsize}, '
              f'{len(blocks)} blocks (max {max(b["E"].shape[1] for b in blocks)}), {fam["seconds"]:.0f}s', flush=True)
    with open(fn, 'wb') as f:
        pickle.dump(fam, f)
    return fam


def build_equations(d, Lmax, Wmax=None, verbose=True, sub_d=None):
    os.makedirs(CACHE, exist_ok=True)
    fn = os.path.join(CACHE, f'eqs_d{d}_L{Lmax}_W{Wmax}_tails' + (f'_s{sub_d}' if sub_d else '') + '.pkl')
    if os.path.exists(fn):
        with open(fn, 'rb') as f:
            return pickle.load(f)
    t0 = time.time()
    eqs = sb.all_loop_equations(d, Lmax, Wmax, sub_d=sub_d)
    if verbose:
        print(f'  equations d={d} L={Lmax} W={Wmax} sub={sub_d}: {len(eqs)} ({time.time()-t0:.0f}s)', flush=True)
    with open(fn, 'wb') as f:
        pickle.dump(eqs, f)
    return eqs


class Problem:
    """The bootstrap problem for one (d, L_max, l_pos, families) setting; beta enters only the equation coefficients.

    Variables: loop keys (the trivial key () is the constant 1, column 0).
    PSD blocks: per family, channel s = +1 (M + N) and -1 (M - N), per symmetry block a matrix E (n x m); the block is
    E^T (M + s N) E, stored as a coefficient tensor T ((m*m) x (1 + nvar))."""

    def __init__(self, d, Lmax, lpos=None, kinds=('G', 'RS', 'RD', 'RL'), sub_d=None, Wmax=None, extra_keys=(), verbose=True,
                 extra_fams=(), extra_eqs=()):
        """extra_fams: further (kind, lpos, sub_d) families (e.g. longer paths in a 2D sublattice);
        extra_eqs: further (Wmax, sub_d) equation sets (W restricted to a sublattice, staples in all d directions)."""
        t0 = time.time()
        self.d, self.Lmax = d, Lmax
        self.lpos = Lmax // 2 if lpos is None else lpos
        self.kinds, self.sub_d, self.Wmax = tuple(kinds), sub_d, Wmax
        specs = [(k, self.lpos, sub_d) for k in kinds] + [tuple(x) for x in extra_fams]
        self.fam_specs = specs
        self.fams = [build_family(sp_[0], d, sp_[1], sp_[2], verbose, sp_[3] if len(sp_) > 3 else None) for sp_ in specs]
        eqs = build_equations(d, Lmax, Wmax, verbose)
        seen = {sb.eq_signature(e) for e in eqs}
        for wm, sdd in extra_eqs:
            for e in build_equations(d, Lmax, wm, verbose, sub_d=sdd):
                sg = sb.eq_signature(e)
                if sg not in seen:
                    seen.add(sg)
                    eqs.append(e)
        self.eq_specs = [(Wmax, None)] + [tuple(x) for x in extra_eqs]
        self.n_eqs_generated = len(eqs)
        pos_keys = set()
        for f in self.fams:
            pos_keys |= set(f['Mkey'].ravel()) | set(f['Nkey'].ravel())
        pos_keys |= set(extra_keys)
        pos_keys.discard(())
        # no pruning: a loop that appears in one equation only is still bounded by |w| <= 1 (box constraint), which can make that
        # equation informative (e.g. it excludes U_P = +-1 in 2D)
        self.eqs = eqs
        other = set()
        for e in eqs:
            other |= set(e)
        other -= pos_keys
        other.discard(())
        srt = lambda ks: sorted(ks, key=lambda k: (len(k), k))
        self.keys = srt(pos_keys) + srt(other)  # positivity keys first: PSD coefficient tensors use columns 0..npos only
        self.npos = len(pos_keys)
        self.kidx = {k: i + 1 for i, k in enumerate(self.keys)}
        self.kidx[()] = 0
        self.nvar = len(self.keys)
        rows, cols, v0, v1 = [], [], [], []
        for r, e in enumerate(eqs):
            for k, (a, b) in e.items():
                rows.append(r)
                cols.append(self.kidx[k])
                v0.append(a)
                v1.append(b)
        self.eq_rows, self.eq_cols = np.array(rows, dtype=np.int64), np.array(cols, dtype=np.int64)
        self.eq_c0, self.eq_c1 = v0, v1
        self.blocks = []
        self._groups = {}
        for fi, f in enumerate(self.fams):
            self._groups = {}  # per family: the grouping cache is keyed by id() of this family's index arrays
            Mi = np.vectorize(lambda k: self.kidx[k], otypes=[np.int64])(f['Mkey'])
            Ni = np.vectorize(lambda k: self.kidx[k], otypes=[np.int64])(f['Nkey'])
            f = {k: v for k, v in f.items() if k not in ('Mkey', 'Nkey')}  # the object key matrices are not needed after this
            f['Midx'], f['Nidx'] = Mi.astype(np.int32), Ni.astype(np.int32)
            self.fams[fi] = f
            for s in (1, -1):
                for b in f['blocks']:
                    E = b['E']
                    T = self._block_tensor(Mi, Ni, s, E)
                    m = E.shape[1]
                    Ts = T.reshape(m, m, -1)
                    G = np.einsum('abk,cbk->ac', Ts, Ts)
                    lam, U = np.linalg.eigh(G)
                    keep = lam > 1e-10 * max(lam.max(), 1e-300)
                    if not keep.any():
                        continue
                    if not keep.all():
                        E = E @ U[:, keep]
                        T = self._block_tensor(Mi, Ni, s, E)
                    self.blocks.append(dict(fam=fi, chan=s, E=E, d_rho=b['d_rho'], T=sp.csr_matrix(T)))  # sparse: a family touches few keys
        self._groups = {}
        self.seconds_build = time.time() - t0
        ms = [b['E'].shape[1] for b in self.blocks]
        self.summary = dict(d=d, Lmax=Lmax, lpos=self.lpos, kinds=list(self.kinds), sub_d=sub_d, Wmax=Wmax,
                            family_specs=[list(x) for x in self.fam_specs], equation_specs=[list(x) for x in self.eq_specs],
                            n_var=self.nvar, n_eq=len(self.eqs), n_eq_generated=self.n_eqs_generated,
                            basis_sizes=[len(f['basis']) for f in self.fams],
                            n_blocks=len(self.blocks), max_block=max(ms), svec_total=int(sum(m * (m + 1) // 2 for m in ms)),
                            seconds_build=self.seconds_build)
        if verbose:
            print(f'  problem: {self.nvar} variables, {len(self.eqs)} equations, {len(self.blocks)} PSD blocks '
                  f'(max {max(ms)}, svec total {self.summary["svec_total"]}), {self.seconds_build:.0f}s', flush=True)

    def _block_tensor(self, Mi, Ni, s, E):
        """T[(a,b), c] = sum over entries (i,j) with key c of E_ia E_jb, channel M + s N. Per key one small GEMM over the entries of
        that key (entries grouped once per family)."""
        n, m = E.shape
        out = np.zeros((self.npos + 1, m, m))
        for idx, sg in ((Mi, 1.0), (Ni, float(s))):
            key = id(idx)
            if key not in self._groups:
                flat = idx.ravel()
                order = np.argsort(flat, kind='stable')
                fs = flat[order]
                cuts = np.flatnonzero(np.diff(fs)) + 1
                starts = np.concatenate([[0], cuts])
                ends = np.concatenate([cuts, [fs.size]])
                self._groups[key] = (order, fs[starts], starts, ends)
            order, keys, starts, ends = self._groups[key]
            for c, st, en in zip(keys, starts, ends):
                seg = order[st:en]
                I = seg // n
                J = seg - I * n
                out[c] += sg * (E[I].T @ E[J])
        return out.reshape(self.npos + 1, m * m).T.copy()

    def eq_matrix(self, beta):
        vals = np.array([float(a) + float(b) * beta for a, b in zip(self.eq_c0, self.eq_c1)])
        return sp.csr_matrix((vals, (self.eq_rows, self.eq_cols)), shape=(len(self.eqs), self.nvar + 1))

    def solve(self, beta, target, sense, verbose=False, settings=None):
        """min (sense = +1) or max (sense = -1) of w(target)."""
        import clarabel
        t0 = time.time()
        Afull = self.eq_matrix(beta)
        A_eq = Afull[:, 1:].tocsc()
        b_eq = -Afull[:, 0].toarray().ravel()
        nv = self.nvar
        As, bs = [A_eq], [b_eq]
        cones = [clarabel.ZeroConeT(A_eq.shape[0])]
        I = sp.identity(nv, format='csc')
        As.append(sp.vstack([I, -I]).tocsc())
        bs.append(np.ones(2 * nv))
        cones.append(clarabel.NonnegativeConeT(2 * nv))
        for b in self.blocks:
            m = b['E'].shape[1]
            ii, jj, sc = _svec_index(m)
            T = sp.csr_matrix(b['T'][ii * m + jj].multiply(sc[:, None]))
            As.append(sp.hstack([-T[:, 1:], sp.csc_matrix((T.shape[0], nv - self.npos))]).tocsc())
            bs.append(T[:, 0].toarray().ravel())
            cones.append(clarabel.PSDTriangleConeT(m))
        A = sp.vstack(As).tocsc()
        A.eliminate_zeros()
        bvec = np.concatenate(bs)
        q = np.zeros(nv)
        obj = target if isinstance(target, dict) else {target: 1.0}
        for k, cf in obj.items():
            q[self.kidx[k] - 1] += sense * float(cf)
        st = clarabel.DefaultSettings()
        st.verbose = verbose
        st.tol_gap_abs = 1e-10
        st.tol_gap_rel = 1e-10
        st.tol_feas = 1e-10
        st.max_iter = 500
        if settings:
            for k, v in settings.items():
                setattr(st, k, v)
        solver = clarabel.DefaultSolver(sp.csc_matrix((nv, nv)), q, A, bvec, cones, st)
        sol = solver.solve()
        z = np.array(sol.z)
        neq = A_eq.shape[0]
        y = z[:neq]
        Zs = []
        off = neq + 2 * nv
        for b in self.blocks:
            m = b['E'].shape[1]
            ii, jj, sc = _svec_index(m)
            v = z[off: off + len(ii)] / sc
            off += len(ii)
            Z = np.zeros((m, m))
            Z[ii, jj] = v
            Z[jj, ii] = v
            Zs.append(Z)
        return dict(value=sense * sol.obj_val, dual_value=sense * sol.obj_val_dual, status=str(sol.status),
                    iterations=int(sol.iterations), seconds=time.time() - t0, x=np.array(sol.x), y=y, Z=Zs,
                    beta=beta, target=target, sense=sense)


# ---------------------------------------------------------------------------------------------------------------------------- certificate

def _limbs(R, nlimb=3, w=21):
    """R rounded to integers at an adaptive scale 2^-sbits so that |R_int| < 2^(w*nlimb - 1); split
    R_int = sum_t L_t 2^(w t) with 0 <= L_t < 2^w for t < nlimb-1 and a signed top limb (|L| < 2^w). Returns (limbs, sbits)."""
    mx = float(np.abs(R).max())
    e = int(np.ceil(np.log2(mx))) if mx > 0 else 0
    sbits = w * nlimb - 2 - e
    Ri = np.rint(R * 2.0 ** sbits)
    assert np.abs(Ri).max() < 2.0 ** (w * nlimb - 1)
    Ri = Ri.astype(np.int64)
    limbs = []
    for t in range(nlimb - 1):
        limbs.append(Ri & ((1 << w) - 1))
        Ri = Ri >> w
    limbs.append(Ri)
    assert np.abs(limbs[-1]).max() < 2 ** w
    return limbs, sbits


def _exact_gram(limbs, w=21):
    """Exact R_int R_int^T as a list of (int64 matrix, shift) terms, using float64 BLAS on integer limbs: products < 2^42 and at most
    2048 columns per chunk, so every partial sum is an integer below 2^53 and the float computation is exact."""
    k = len(limbs)
    r = limbs[0].shape[1]
    terms = []
    for t in range(k):
        for u in range(t, k):
            acc = np.zeros((limbs[0].shape[0],) * 2, dtype=np.int64)
            for c0 in range(0, r, 2048):
                a = limbs[t][:, c0:c0 + 2048].astype(np.float64)
                b = limbs[u][:, c0:c0 + 2048].astype(np.float64)
                P = a @ b.T
                assert np.abs(P).max() < 2.0 ** 53
                acc += P.astype(np.int64)
            if u != t:
                acc = acc + acc.T
            terms.append((acc, w * (t + u)))
    return terms


def _class_sums(Zl, idx, nclass):
    """Exact per-class sums of an int64 matrix (entries < 2^62) grouped by idx; Python ints."""
    v = Zl.ravel()
    lo = v & ((1 << 27) - 1)
    hi = v >> 27
    out_lo = np.zeros(nclass, dtype=np.int64)
    out_hi = np.zeros(nclass, dtype=np.int64)
    np.add.at(out_lo, idx.ravel(), lo)
    np.add.at(out_hi, idx.ravel(), hi)
    return [int(h) * (1 << 27) + int(l) for h, l in zip(out_hi, out_lo)]


def certify(prob, res, beta_str, scale_bits=40, refine_y=True):
    """Rigorous bound on w(target) from the dual solution, in exact integer arithmetic.

    sense = +1: rigorous lower bound; sense = -1: rigorous upper bound. The PSD multiplier is rebuilt in the unreduced basis as
    Z = R R^T with R the dyadic rounding of [E_k L_k] (exactly PSD), so the floating symmetry reduction plays no role in the proof;
    beta is the exact decimal rational beta_str; y is rounded to 2^-scale_bits; the residual rho is exact."""
    t0 = time.time()
    beta = Fraction(beta_str)
    nv = prob.nvar
    sense = res['sense']
    obj = res['target'] if isinstance(res['target'], dict) else {res['target']: 1}
    qcols = {}
    for k, cf in obj.items():
        qcols[prob.kidx[k]] = qcols.get(prob.kidx[k], 0) + sense * Fraction(cf)
    assert all(Fraction(v) * 1024 == int(Fraction(v) * 1024) for v in qcols.values()), 'objective coefficients must be dyadic'
    per = {}
    for b, Z in zip(prob.blocks, res['Z']):
        lam, V = np.linalg.eigh((Z + Z.T) / 2)
        L = V * np.sqrt(np.clip(lam, 0, None))[None, :]
        per.setdefault((b['fam'], b['chan']), []).append(b['E'] @ L)
    gfr = [Fraction(0)] * (nv + 1)
    for (fi, s), Rs in per.items():
        R = np.hstack(Rs)
        f = prob.fams[fi]
        limbs, sbits = _limbs(R)
        terms = _exact_gram(limbs)
        for idx, sg in ((f['Midx'], 1), (f['Nidx'], s)):
            tot = [0] * (prob.npos + 1)
            for P, shift in terms:
                cs = _class_sums(P, idx, prob.npos + 1)
                for c in range(prob.npos + 1):
                    if cs[c]:
                        tot[c] += cs[c] << shift
            for c in range(prob.npos + 1):
                if tot[c]:
                    gfr[c] += Fraction(sg * tot[c], 1 << (2 * sbits))
    # common denominator 2^(2 scale_bits) for g: exact
    den_g = max((v.denominator for v in gfr), default=1)
    scale_bits = max(scale_bits, (den_g.bit_length() + 1) // 2)
    g = [int(v * (1 << (2 * scale_bits))) for v in gfr]
    assert all(Fraction(gi, 1 << (2 * scale_bits)) == v for gi, v in zip(g, gfr))
    A = prob.eq_matrix(float(beta))
    gf = np.array([float(Fraction(v, 1 << (2 * scale_bits))) for v in g])
    qv = np.zeros(nv + 1)
    for c, v in qcols.items():
        qv[c] = float(v)
    y = np.array(res['y'], dtype=float)
    if refine_y and A.shape[0] > 0:
        from scipy.sparse.linalg import lsqr
        At = A[:, 1:].T.tocsr()
        r0 = qv[1:] + At @ y - gf[1:]
        dy = lsqr(At, -r0, atol=1e-16, btol=1e-16, iter_lim=50000)[0]
        r1 = qv[1:] + At @ (y + dy) - gf[1:]
        if np.abs(r1).sum() < np.abs(r0).sum():
            y = y + dy
    yi = [int(v) for v in np.rint(y * 2.0 ** scale_bits)]
    D_eq = 8 * beta.denominator
    aty = [0] * (nv + 1)
    for r, c, a, bb in zip(prob.eq_rows, prob.eq_cols, prob.eq_c0, prob.eq_c1):
        coef = a * D_eq + bb * D_eq * beta
        assert coef.denominator == 1
        aty[c] += yi[r] * int(coef)
    S2 = 1 << (2 * scale_bits)
    S1 = 1 << scale_bits
    num = [int(qcols.get(c, 0) * S2 * D_eq) + S1 * aty[c] - g[c] * D_eq for c in range(nv + 1)]
    den = S2 * D_eq
    # q.x = rho.x + y.A_0 - <Z, F_0> + <Z, B(x)> - y.(A x + A_0 x_0 ... ) : with A_full [1; x] = 0 and x_0 = 1:
    # q.x >= sum_{c>=1} rho_c x_c + (y.A_0 - g_0) >= -||rho||_1 + (y.A_0 - g_0)
    l1 = sum(abs(v) for v in num[1:])
    bound_q = Fraction(S1 * aty[0] - g[0] * D_eq - l1, den)
    rig = sense * bound_q
    s = str(rig)
    return dict(rigorous=float(rig), rigorous_exact=s if len(s) < 300 else f'{float(rig):.17g} (exact rational, {len(s)} chars)',
                residual_l1=float(Fraction(l1, den)), seconds=time.time() - t0)
