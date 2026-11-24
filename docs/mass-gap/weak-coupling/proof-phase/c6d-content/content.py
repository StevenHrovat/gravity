"""c6d-content (amendment of c5b-content, see PREREG-AMEND.md): the explained variance R^2(F; b) = Var(E[F | Phi_b]) / Var(F) of local glueball-type observables F of the fine field,
given the block field Phi_b of the good blocking (spatial staple smearing w = 2 + temporal decimation, projection to SU(2); b = 2, 4, 8),
CPU only. What is computed here is a LOWER BOUND by held-out regression (never an upper bound, never the conditional expectation).

Why it is a lower bound: E[F|Phi] is the best L^2 predictor of F from Phi, so for ANY fixed function h of Phi, trained on other data,
  Var(F) - E(F - h(Phi))^2  <=  Var(F) - E(F - E[F|Phi])^2  =  Var(E[F|Phi]).
The code fits h on a training phase, picks the model class on a validation phase, and evaluates on a later, strictly held-out test phase of
the same Markov chain (a gap of decorrelating sweeps in between). R2_LB = 1 - MSE_test / Var(F). Jackknife over test configurations.

Alignment (the point that makes the pooling legitimate): the Wilson measure and the blocking commute with even translations, so the pair
(F at fixed position relative to the block cell, Phi_b) has the same joint law for every origin o of the block lattice and every cell. The
code pools all (origin, cell) pairs. Features are gauge-invariant loops of the block lattice (traces of plaquettes and 1x2 rectangles, the
adjoint traces), summed over orbits of positions relative to the cell centre (|d_t|, spatial radius^2, loop class).

Usage
  python content.py selftest
  python content.py run GROUP BETA N SEED N_TRAIN N_VAL N_TEST EVERY N_THERM M OUT.json [--maxminutes X]
"""

import argparse
import json
import os
import sys
import time

for _v in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "4")
os.environ["CUDA_VISIBLE_DEVICES"] = "-1"

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "c3b-refit"))
CM_NEW_ENABLED = True
import goodblock as GB  # noqa: E402  (read-only use of the c3b instrument)

BL = GB.BL
BD = GB.BD
TIME = 0


# ---------------------------------------------------------------------------------------------------------------------------- updater
# The stock checkerboard heat bath + overrelaxation of the c3b/c4 generator (blocked.py -> boundary.py), unchanged. (A first attempt to
# update all links of one direction at once was wrong: the two mu links of a plaquette sit at x and x + nu; caught by the plaquette
# check against the stock updater, discarded.)

def make_fast(group, N, beta, seed):
    return BL.make_updater(group, BL.PeriodicBox(N), beta, 1, seed, False, False)


# ---------------------------------------------------------------------------------------------------------------------------- loops

def lines_of(ops, W):
    out = []
    for mu in range(4):
        d = {1: W[mu]}
        d[2] = ops.mul(W[mu], BL.sh(ops, W[mu], mu, 1))
        out.append(d)
    return out


def loop_field(ops, lines, mu, nu, R, T):
    """(fundamental trace, adjoint trace) of the R x T loop (R along mu, T along nu) with lower corner at x, every x; shape (batch, X0..X3)."""
    a = ops.mul(lines[mu][R], BL.sh(ops, lines[nu][T], mu, R))
    b = ops.mul(lines[nu][T], BL.sh(ops, lines[mu][R], nu, T))
    if ops.group == "su2":
        t = ops.dot(a, b)
        return t, (4 * t * t - 1) / 3
    ang = a - b
    return np.cos(ang), np.cos(2 * ang)


PLANES = [(mu, nu) for mu in range(4) for nu in range(mu + 1, 4)]
SHAPES = ((1, 1), (2, 1), (1, 2))


def window_mean(A, s):
    """Mean over the hypercube x + [0, s)^4 (lower corner x), periodic."""
    out = A
    for ax in range(4):
        if s > 1:
            out = sum(np.roll(out, -j, axis=ax) for j in range(s)) / s
    return out


def ape_step(ops, F, a):
    """One step of spatial APE smearing from the field F (all links at once): proj(link + a * sum of the spatial staples, both signs)."""
    mul, dag, sh = ops.mul, ops.dag, BL.sh
    out = []
    for mu in range(4):
        acc = GB.to_acc(ops, F[mu])
        for nu in GB.transverse(mu):
            up = mul(mul(F[nu], sh(ops, F[mu], nu, 1)), dag(sh(ops, F[nu], mu, 1)))
            unu = sh(ops, F[nu], nu, -1)
            dn = mul(mul(dag(unu), sh(ops, F[mu], nu, -1)), sh(ops, unu, mu, 1))
            acc = acc + a * (GB.to_acc(ops, up) + GB.to_acc(ops, dn))
        out.append(GB.proj(ops, acc))
    return out


APE_STEPS = 3
APE_A = 0.5


def fine_targets(ops, U, N):
    """Fine scalar densities (arrays N^4, lower-corner convention): S = sum over the 6 planes of the fundamental plaquette trace;
    Q = sum over the 3 spatial planes of the plaquette trace of the APE-smeared links (3 steps, weight 0.5)."""
    lines = lines_of(ops, U)
    S = 0
    for mu, nu in PLANES:
        S = S + loop_field(ops, lines, mu, nu, 1, 1)[0]
    V = U
    for _ in range(APE_STEPS):
        V = ape_step(ops, V, APE_A)
    lq = lines_of(ops, V)
    Q = 0
    for mu, nu in PLANES:
        if mu != TIME:
            Q = Q + loop_field(ops, lq, mu, nu, 1, 1)[0]
    return {"S": np.asarray(S[0]).reshape(N, N, N, N), "Q": np.asarray(Q[0]).reshape(N, N, N, N)}


TARGETS = ("P2", "P4", "P8", "Q4", "Q8")  # P: plaquette scalar, Q: smeared spatial 0++ operator; digit = window side in fine units
TARGET_S = {"P2": 2, "P4": 4, "P8": 8, "Q4": 4, "Q8": 8}


def target_arrays(Sd, b, N):
    """For block size b: the targets at the cell-centre placement, as arrays (nO, Nc, Nc, Nc, Nc) aligned with the block lattices of
    GB.coarse (batch = origins o in {0..b/2-1}^4 row-major, fine position 2 o + b X + q, q = b/2 - s/2 per axis, modulo N)."""
    s_ = b // 2
    Nc = N // b
    wins = {}
    out = {}
    for name in TARGETS:
        s = TARGET_S[name]
        base = Sd["S"] if name[0] == "P" else Sd["Q"]
        key = (name[0], s)
        if key not in wins:
            wins[key] = window_mean(base, s)
        q = b // 2 - s // 2
        idx = [np.array([(2 * o + b * X + q) % N for o in range(s_) for X in range(Nc)]) for _ in range(4)]
        T = wins[key][np.ix_(*idx)].reshape((s_, Nc) * 4)
        T = T.transpose([0, 2, 4, 6, 1, 3, 5, 7]).reshape((s_ ** 4,) + (Nc,) * 4)
        out[name] = T
    return out


# ---------------------------------------------------------------------------------------------------------------------------- block features

# Loop fields of a block lattice V: per plane (mu < nu): P_f, P_a (1x1 fundamental / adjoint), R21_f, R12_f, R21_a, R12_a.
# Class of a loop (orbit label): kind (P_f, P_a, R_f, R_a) x geometry (ts / ss; for a ts rectangle: long axis time or space).
CLASSES = ("Pf_ts", "Pf_ss", "Pa_ts", "Pa_ss", "Rf_tsT", "Rf_tsS", "Rf_ss", "Ra_tsT", "Ra_tsS", "Ra_ss")


def block_fields(ops, V):
    """List of (class index, (len_mu, len_nu), mu, nu, array (nO, Nc^4)) for the lattice V (batch axis = origins)."""
    lines = lines_of(ops, V)
    fl = []
    for mu, nu in PLANES:
        ts = (mu == TIME)
        f11, a11 = loop_field(ops, lines, mu, nu, 1, 1)
        fl.append((0 if ts else 1, (1, 1), mu, nu, f11))
        fl.append((2 if ts else 3, (1, 1), mu, nu, a11))
        for (R, T) in ((2, 1), (1, 2)):
            f, a = loop_field(ops, lines, mu, nu, R, T)
            if ts:
                cf, ca = (4, 7) if R == 2 else (5, 8)  # R along mu = time: long axis time
            else:
                cf, ca = 6, 9
            fl.append((cf, (R, T), mu, nu, f))
            fl.append((ca, (R, T), mu, nu, a))
    return fl


_KEYCACHE = {}


def key_table():
    """Static plan: for every (field slot, offset delta of the loop's lower-corner site from the cell's lower corner) with the loop centre
    within |2 d_i| <= 3 of the cell centre: its orbit key. Returns (plan, nkeys, key names); plan entries (slot, delta tuple, key index)."""
    if "t" in _KEYCACHE:
        return _KEYCACHE["t"]
    slots = []
    for mu, nu in PLANES:
        ts = (mu == TIME)
        slots.append((0 if ts else 1, (1, 1), mu, nu))
        slots.append((2 if ts else 3, (1, 1), mu, nu))
        for (R, T) in ((2, 1), (1, 2)):
            for rep in (0, 1):
                if ts:
                    c = (4 if R == 2 else 5) + 3 * rep
                else:
                    c = 6 + 3 * rep
                slots.append((c, (R, T), mu, nu))
    keys = {}
    plan = []
    grid = (-1, 0, 1, 2)
    import itertools
    for slot, (cls, ln, mu, nu) in enumerate(slots):
        for delta in itertools.product(grid, repeat=4):
            twod = [2 * delta[i] - 1 for i in range(4)]  # 2 * (delta - 1/2)
            twod[mu] += ln[0]
            twod[nu] += ln[1]
            if max(abs(x) for x in twod) > 3:
                continue
            r4 = sum(twod[i] ** 2 for i in range(1, 4))
            k = (cls, abs(twod[0]), r4)
            if k not in keys:
                keys[k] = len(keys)
            plan.append((slot, delta, keys[k]))
    names = sorted(keys, key=lambda k: keys[k])
    _KEYCACHE["t"] = (plan, len(keys), names)
    return _KEYCACHE["t"]


def block_features(ops, V):
    """Orbit-summed features for every (origin, cell): array (nkeys, nO * Nc^4) float32, each key summed over its loops and normalised by
    its multiplicity (a mean), so that the features are O(1) whatever the orbit size."""
    plan, nk, _ = key_table()
    fl = block_fields(ops, V)
    shape = fl[0][4].shape
    acc = np.zeros((nk,) + shape)
    cnt = np.zeros(nk)
    arrs = [np.asarray(f[4]) for f in fl]
    for slot, delta, k in plan:
        acc[k] += np.roll(arrs[slot], shift=tuple(-d for d in delta), axis=(1, 2, 3, 4))
        cnt[k] += 1
    acc /= cnt.reshape((nk,) + (1,) * len(shape))
    return acc.reshape(nk, -1).astype(np.float32)


# ---------------------------------------------------------------------------------------------------------------------------- v2 features
# (PREREG-AMEND.md section 1) (L) plane- and orientation-resolved loops R x T, R, T in 1..3; (P) neighbouring plaquette pair traces f+-.

import itertools  # noqa: E402

SHAPES3 = tuple((R, T) for R in (1, 2, 3) for T in (1, 2, 3))
GRID2 = tuple(range(-2, 3))
_PLAN2 = {}


def _loop_key(mu, nu, R, T, tw):
    if mu == TIME:
        outs = tuple(sorted(abs(tw[a]) for a in (1, 2, 3) if a != nu))
        return ("L", "ts", R, T, abs(tw[0]), abs(tw[nu]), outs)
    inpl = tuple(sorted(((R, abs(tw[mu])), (T, abs(tw[nu])))))
    out = [a for a in (1, 2, 3) if a not in (mu, nu)][0]
    return ("L", "ss", inpl, abs(tw[0]), abs(tw[out]))


def _pair_key(sign, p1, p2, dax, tw):
    """p1, p2 = planes (mu, nu); dax = step axis or None; tw = doubled midpoint offset from the cell centre (4,)."""
    ax = []
    for i in range(4):
        sg = 1 if tw[i] >= 0 else -1
        ds = (sg if dax == i else 0)
        ax.append((int(i in p1), int(i in p2), ds, abs(tw[i])))
    return ("P", sign, ax[0], tuple(sorted(ax[1:])))


def plan2():
    """Static plan of the v2 extra features: slots (kind, params), keys, and per (slot, key) the array of lower-corner offsets.
    Returns (slots, plan, nkeys, names) with plan = list of (slot index, key index, int array (nd, 4))."""
    if "p" in _PLAN2:
        return _PLAN2["p"]
    slots = []
    for (mu, nu) in PLANES:
        for (R, T) in SHAPES3:
            slots.append(("L", mu, nu, R, T))
    for sign in (0, 1):  # 0: f+, 1: f-
        for i1, p1 in enumerate(PLANES):
            for i2, p2 in enumerate(PLANES):
                if i1 < i2:
                    slots.append(("P", sign, p1, p2, None))
                if i1 == i2:  # neighbour pairs of the same plane only (a cap on the number of features, see PREREG-AMEND.md section 1)
                    for dax in range(4):
                        slots.append(("P", sign, p1, p2, dax))
    keys = {}
    grouped = {}
    for si, sl in enumerate(slots):
        for delta in itertools.product(GRID2, repeat=4):
            if sl[0] == "L":
                _, mu, nu, R, T = sl
                tw = [2 * delta[i] - 1 for i in range(4)]
                tw[mu] += R
                tw[nu] += T
                if max(abs(x) for x in tw) > 3:
                    continue
                k = _loop_key(mu, nu, R, T, tw)
            else:
                _, sign, p1, p2, dax = sl
                tw = [2 * delta[i] - 1 + (1 if i in p1 else 0) for i in range(4)]
                if dax is not None:
                    tw[dax] += 1
                if max(abs(x) for x in tw) > 3:
                    continue
                k = _pair_key(sign, p1, p2, dax, tw)
            if k not in keys:
                keys[k] = len(keys)
            grouped.setdefault((si, keys[k]), []).append(delta)
    plan = [(si, ki, np.array(d, dtype=np.int64)) for (si, ki), d in grouped.items()]
    names = sorted(keys, key=lambda k: keys[k])
    _PLAN2["p"] = (slots, plan, len(keys), names)
    return _PLAN2["p"]


def plaq_elem(ops, W, mu, nu):
    """Plaquette group element with base point x (SU(2): quaternion, U(1): angle)."""
    a = ops.mul(W[mu], BL.sh(ops, W[nu], mu, 1))
    b = ops.mul(W[nu], BL.sh(ops, W[mu], nu, 1))
    return ops.mul(a, ops.dag(b))


def pair_traces(ops, X, Y):
    """(f+, f-) = ((1/2) Re tr(X Y), (1/2) Re tr(X Y^dag))."""
    if ops.group == "su2":
        return ops.mul(X, Y)[0], (X * Y).sum(axis=0)
    return np.cos(X + Y), np.cos(X - Y)


def lines_of3(ops, W):
    out = []
    for mu in range(4):
        d = {1: W[mu]}
        d[2] = ops.mul(W[mu], BL.sh(ops, W[mu], mu, 1))
        d[3] = ops.mul(d[2], BL.sh(ops, W[mu], mu, 2))
        out.append(d)
    return out


def v2_fields(ops, V):
    """Arrays (nO, Nc^4) for every slot of plan2()."""
    slots = plan2()[0]
    lines = lines_of3(ops, V)
    Pel = {pl: plaq_elem(ops, V, *pl) for pl in PLANES}
    cache = {}
    out = []
    for sl in slots:
        if sl[0] == "L":
            _, mu, nu, R, T = sl
            out.append(np.asarray(loop_field(ops, lines, mu, nu, R, T)[0]))
        else:
            _, sign, p1, p2, dax = sl
            if (p1, p2, dax) not in cache:
                X = Pel[p1]
                if dax is None:
                    Y = Pel[p2]
                else:
                    L = V[dax]
                    Y = ops.mul(ops.mul(L, BL.sh(ops, Pel[p2], dax, 1)), ops.dag(L))
                cache[(p1, p2, dax)] = pair_traces(ops, X, Y)
            out.append(np.asarray(cache[(p1, p2, dax)][sign]))
    return out


_DH = {}


def _kernel_hat(Nc, si, ki, deltas):
    """conj(FFT) of the offset-count kernel D of a (slot, key): the sum over the offsets of A[c + delta] is the correlation D * A."""
    key = (Nc, si, ki)
    if key not in _DH:
        D = np.zeros((Nc,) * 4)
        np.add.at(D, tuple((deltas % Nc).T), 1.0)
        _DH[key] = np.conj(np.fft.fftn(D))
    return _DH[key]


def v2_features(ops, V, explicit=False):
    """Orbit-mean features of PREREG-AMEND.md section 1: array (nkeys2, nO * Nc^4) float32. The orbit sums of shifted fields are done as
    correlations in Fourier space (exact up to rounding); explicit=True is the slow reference with np.roll (used by the selftest)."""
    slots, plan, nk, _ = plan2()
    arrs = v2_fields(ops, V)
    shape = arrs[0].shape
    nO, Nc = shape[0], shape[1]
    cnt = np.zeros(nk)
    if explicit:
        acc = np.zeros((nk, nO, Nc ** 4))
        for si, ki, deltas in plan:
            for d in deltas:
                acc[ki] += np.roll(arrs[si], shift=tuple(-int(x) for x in d), axis=(1, 2, 3, 4)).reshape(nO, -1)
            cnt[ki] += len(deltas)
    else:
        ahat = {}
        acch = np.zeros((nk, nO) + (Nc,) * 4, dtype=complex)
        for si, ki, deltas in plan:
            if si not in ahat:
                ahat[si] = np.fft.fftn(arrs[si], axes=(1, 2, 3, 4))
            acch[ki] += ahat[si] * _kernel_hat(Nc, si, ki, deltas)
            cnt[ki] += len(deltas)
        acc = np.fft.ifftn(acch, axes=(2, 3, 4, 5)).real.reshape(nk, nO, -1)
    acc /= cnt.reshape(nk, 1, 1)
    return acc.reshape(nk, -1).astype(np.float32)


N_V1 = 108  # columns of v1 (c5b)


def all_features(ops, V):
    """v1 (108 orbit keys) followed by v2 extras: (nfeat, ncells) float32."""
    return np.concatenate([block_features(ops, V), v2_features(ops, V)], axis=0)


# ---------------------------------------------------------------------------------------------------------------------------- regression

class Reg:
    """Ridge regression in three model classes on standardised features (A linear, B + pairwise products of the 14 most correlated
    features, C + 600 random tanh features of the 40 most correlated ones). Targets: columns of Y."""

    LAM = (1e-5, 1e-4, 1e-3, 1e-2, 1e-1, 1.0, 10.0)

    def __init__(self, seed=0):
        self.rng = np.random.default_rng(seed)

    def fit(self, X, Y, Xv, Yv):
        X = np.asarray(X, dtype=np.float64)
        Xv = np.asarray(Xv, dtype=np.float64)
        n, p = X.shape
        self.mu = X.mean(0)
        sd = X.std(0)
        self.sd = np.where(sd > 1e-12, sd, 1.0)
        Z = (X - self.mu) / self.sd
        Zv = (Xv - self.mu) / self.sd
        self.ym = Y.mean(0)
        Yc = Y - self.ym
        c = np.maximum(np.abs(Z.T @ Yc), np.abs((Z * Z - 1).T @ Yc)) / n  # (p, T): linear and even dependence, per feature
        order = np.argsort(-c.max(1))
        self.topB = order[:14]
        self.topC = order[:40]
        self.W = self.rng.standard_normal((len(self.topC), 600)) / np.sqrt(len(self.topC))
        self.bias = self.rng.uniform(-1, 1, 600)
        self.models = {}
        for tier in "ABC":
            D = self._design(Z, tier)
            Dv = self._design(Zv, tier)
            dm = D.mean(0)
            dsd = D.std(0)
            dsd = np.where(dsd > 1e-12, dsd, 1.0)
            D = (D - dm) / dsd
            Dv = (Dv - dm) / dsd
            G = D.T @ D
            ev, Q = np.linalg.eigh(G)
            QtB = Q.T @ (D.T @ Yc)
            best = None
            for lam in self.LAM:
                w = Q @ (QtB / (ev + lam * n)[:, None])
                err = ((Yv - self.ym - Dv @ w) ** 2).mean(0)  # per target
                if best is None:
                    best = (err.copy(), [lam] * Y.shape[1], [w[:, t].copy() for t in range(Y.shape[1])])
                else:
                    for t in range(Y.shape[1]):
                        if err[t] < best[0][t]:
                            best[0][t] = err[t]
                            best[1][t] = lam
                            best[2][t] = w[:, t].copy()
            self.models[tier] = dict(dm=dm, dsd=dsd, val_mse=best[0], lam=best[1], w=best[2])
        self.choice = [min("ABC", key=lambda tr: self.models[tr]["val_mse"][t]) for t in range(Y.shape[1])]
        return self

    def _design(self, Z, tier):
        parts = [Z]
        if tier == "B":
            T = Z[:, self.topB]
            k = T.shape[1]
            parts.append(np.stack([T[:, i] * T[:, j] for i in range(k) for j in range(i, k)], axis=1))
        if tier == "C":
            parts.append(np.tanh(Z[:, self.topC] @ self.W + self.bias))
        return np.concatenate(parts, axis=1)

    def predict(self, X, tiers=None):
        """Predictions (n, T) with the tier chosen on validation for each target (or forced)."""
        Z = (np.asarray(X, dtype=np.float64) - self.mu) / self.sd
        T = len(self.choice)
        out = np.zeros((X.shape[0], T))
        cache = {}
        for t in range(T):
            tier = self.choice[t] if tiers is None else tiers
            if tier not in cache:
                D = self._design(Z, tier)
                cache[tier] = (D - self.models[tier]["dm"]) / self.models[tier]["dsd"]
            out[:, t] = self.ym[t] + cache[tier] @ self.models[tier]["w"][t]
        return out


# ---------------------------------------------------------------------------------------------------------------------------- measurement

BLOCKS = tuple(int(x) for x in os.environ.get("CM_BLOCKS", "2,4,8").split(","))
WS = (2.0, 0.0)


def config_arrays(group, ops, U, N, rng, M, want_all):
    """For one configuration: per (w, b): features, targets (all cells if want_all, else a random subsample of M cells)."""
    Sd = fine_targets(ops, U, N)
    res = {}
    for w in WS:
        H = GB.good_levels(ops, U, 3, w)
        for b in BLOCKS:
            n = int(np.log2(b))
            V = GB.coarse(ops, H, U, n)
            X = all_features(ops, V)
            Tg = target_arrays(Sd, b, N)
            Y = np.stack([Tg[t].reshape(-1) for t in TARGETS], axis=1)
            if not want_all:
                idx = rng.choice(Y.shape[0], size=min(M, Y.shape[0]), replace=False)
                X = X[:, idx]
                Y = Y[idx]
                res[(w, b)] = (X.T.copy(), Y, None)
            else:
                res[(w, b)] = (X.T, Y, (b, N // b, b // 2))
            del V
    return res


def plaq_mean(ops, U):
    lines = lines_of(ops, U)
    return float(np.mean([loop_field(ops, lines, mu, nu, 1, 1)[0].mean() for mu, nu in PLANES]))


def jackknife_ratio(num, den):
    """num, den: arrays (n_cfg,) of per-config sums (same weights); ratio of means with jackknife error."""
    n = len(num)
    r = num.sum() / den.sum()
    jk = np.array([(num.sum() - num[i]) / (den.sum() - den[i]) for i in range(n)])
    return float(r), float(np.sqrt((n - 1) / n * ((jk - jk.mean()) ** 2).sum()))


def run(a):
    group = a.group
    N = a.N
    t0 = time.time()
    upd = make_fast(group, N, a.beta, a.seed)
    ops = BL.make_ops(group, np)
    rng = np.random.default_rng(a.seed + 77)
    log = open(a.out.replace(".json", ".log"), "a")

    def P(*x):
        s = " ".join(str(y) for y in x)
        print(s, flush=True)
        log.write(s + "\n")
        log.flush()

    P(f"content run {group} beta={a.beta} N={N} seed={a.seed} train={a.n_train} val={a.n_val} test={a.n_test} every={a.every} therm={a.n_therm} M={a.M}")
    for i in range(a.n_therm):
        upd.sweep(1)
        if i % 20 == 19:
            U = BL.chain_config(group, np, upd.links(), 0)
            P(f"  therm {i + 1} plaq {plaq_mean(ops, U):.5f} t={time.time() - t0:.0f}s")
    # phase 1: train + validation samples
    Xs = {k: [] for k in [(w, b) for w in WS for b in BLOCKS]}
    Ys = {k: [] for k in Xs}
    cfg_of = {k: [] for k in Xs}
    plaqs = []
    for c in range(a.n_train + a.n_val):
        for _ in range(a.every):
            upd.sweep(1)
        U = BL.chain_config(group, np, upd.links(), 0)
        plaqs.append(plaq_mean(ops, U))
        res = config_arrays(group, ops, U, N, rng, a.M, False)
        for k, (X, Y, _) in res.items():
            Xs[k].append(X)
            Ys[k].append(Y)
            cfg_of[k].append(np.full(len(Y), c))
        if c % 10 == 9:
            P(f"  collect {c + 1}/{a.n_train + a.n_val} plaq {np.mean(plaqs[-10:]):.5f} t={time.time() - t0:.0f}s")
    # fit: the same data, twice: feature set v1 (c5b's 108 columns, ablation) and v2 (all columns, the instrument)
    models = {}
    info = {}
    FS = {"v1": slice(0, N_V1), "v2": slice(0, None)}
    for k in list(Xs):
        X = np.concatenate(Xs[k])
        Y = np.concatenate(Ys[k])
        cf = np.concatenate(cfg_of[k])
        tr = cf < a.n_train
        va = ~tr
        for fs, cols in FS.items():
            Xf = X[:, cols]
            reg = Reg(seed=1).fit(Xf[tr], Y[tr], Xf[va], Y[va])
            kk = (fs,) + k
            models[kk] = reg
            vv = Y[va].var(0)
            info[kk] = dict(n_train=int(tr.sum()), n_val=int(va.sum()), choice=reg.choice,
                            val_R2={tt: [float(1 - reg.models[tt]["val_mse"][j] / vv[j]) for j in range(len(TARGETS))] for tt in "ABC"})
            P(f"  fit {fs} w={k[0]} b={k[1]}: n_train={tr.sum()} val R2 (A/B/C best) "
              + " ".join(f"{TARGETS[j]}:{max(info[kk]['val_R2'][tt][j] for tt in 'ABC'):.3f}({reg.choice[j]})" for j in range(len(TARGETS)))
              + f" t={time.time() - t0:.0f}s")
        del X, Y
        Xs[k] = None
    del Xs, Ys, cfg_of
    for _ in range(20):  # gap of decorrelating sweeps
        upd.sweep(1)
    # phase 2: held-out test, all cells of every configuration
    acc = {k: [] for k in models}
    for c in range(a.n_test):
        for _ in range(a.every):
            upd.sweep(1)
        U = BL.chain_config(group, np, upd.links(), 0)
        res = config_arrays(group, ops, U, N, rng, a.M, True)
        for k0, (X0, Y, (b, Nc, s_)) in res.items():
            for fs, cols in FS.items():
                k = (fs,) + k0
                reg = models[k]
                pred = reg.predict(X0[:, cols])
                r = Y - pred
                n = Y.shape[0]
                rec = dict(n=n, sumF=Y.sum(0), sumF2=(Y * Y).sum(0), sse=(r * r).sum(0), sumr=r.sum(0))
                # time-lag covariances at D = j * b, j = 1, 2 (same origin, cells shifted along time): residual-residual and F-F
                shp = (s_ ** 4, Nc, Nc, Nc, Nc, Y.shape[1])
                Y5 = Y.reshape(shp)
                r5 = r.reshape(shp)
                lagd = {}
                for j in (1, 2):
                    if j > Nc // 2:
                        continue
                    lagd[j] = dict(FF=(Y5 * np.roll(Y5, -j, axis=1)).sum((0, 1, 2, 3, 4)), rr=(r5 * np.roll(r5, -j, axis=1)).sum((0, 1, 2, 3, 4)))
                rec["lag"] = lagd
                acc[k].append(rec)
        if c % 10 == 9:
            P(f"  test {c + 1}/{a.n_test} t={time.time() - t0:.0f}s")
    out = dict(group=group, beta=a.beta, N=N, seed=a.seed, n_train=a.n_train, n_val=a.n_val, n_test=a.n_test, every=a.every, M=a.M,
               plaq_collect=[float(x) for x in plaqs], targets=list(TARGETS), seconds=time.time() - t0, results={})
    for k, recs in acc.items():
        b = k[2]
        n = np.array([r["n"] for r in recs], float)
        sumF = np.array([r["sumF"] for r in recs])
        sumF2 = np.array([r["sumF2"] for r in recs])
        sse = np.array([r["sse"] for r in recs])
        sumr = np.array([r["sumr"] for r in recs])
        entry = dict(info=info[k], per_target={})
        for j, tname in enumerate(TARGETS):
            def r2_of(idx):
                nn = n[idx].sum()
                mean = sumF[idx, j].sum() / nn
                varF = sumF2[idx, j].sum() / nn - mean ** 2
                mse = sse[idx, j].sum() / nn  # E (F - h)^2, includes any bias of h
                return 1 - mse / varF, varF
            allidx = np.arange(len(recs))
            r2, varF = r2_of(allidx)
            jk = np.array([r2_of(np.delete(allidx, i))[0] for i in range(len(recs))])
            err = float(np.sqrt((len(recs) - 1) / len(recs) * ((jk - jk.mean()) ** 2).sum()))
            pt = dict(R2_LB=float(max(r2, 0.0)), R2_raw=float(r2), R2_LB_err=err, varF=float(varF), tier=models[k].choice[j])
            # lag covariances
            for lag in (1, 2):
                if all(lag in r["lag"] for r in recs):
                    FF = np.array([r["lag"][lag]["FF"][j] for r in recs])
                    rr = np.array([r["lag"][lag]["rr"][j] for r in recs])
                    cnt = n.copy()
                    # centred covariances: subtract the pooled mean (product of means); small correction
                    mF = sumF[:, j].sum() / n.sum()
                    mr = sumr[:, j].sum() / n.sum()
                    covFF = FF / cnt - mF ** 2
                    covrr = rr / cnt - mr ** 2
                    num = covrr
                    den = covFF
                    S, Se = jackknife_ratio(num, den)
                    pt[f"lag{lag}"] = dict(D_fine=lag * b, cov_FF=float(den.mean()), cov_FF_err=float(den.std(ddof=1) / np.sqrt(len(den))),
                                           cov_rr=float(num.mean()), cov_rr_err=float(num.std(ddof=1) / np.sqrt(len(num))), S=S, S_err=Se,
                                           rho_FF=float(den.mean() / varF))
            entry["per_target"][tname] = pt
        out["results"][f"{k[0]}_w{k[1]:g}_b{k[2]}"] = entry
    json.dump(out, open(a.out, "w"), indent=1)
    P(f"done {a.out} in {time.time() - t0:.0f}s")
    for key, e in out["results"].items():
        P(key, " ".join(f"{t}: R2_LB={e['per_target'][t]['R2_LB']:.4f}+-{e['per_target'][t]['R2_LB_err']:.4f}" for t in TARGETS))
    return 0


# ---------------------------------------------------------------------------------------------------------------------------- selftest

def selftest(a):
    ok = True

    def rep(name, good, detail=""):
        nonlocal ok
        ok = ok and good
        print(("PASS " if good else "FAIL ") + name + (" : " + detail if detail else ""), flush=True)

    # 1. generator sanity: mean plaquette of the stock updater at 6^4 (SU(2) beta 2.3 about 0.60 on this small torus; U(1) 1.1 about 0.72)
    for group, beta, lo, hi in (("su2", 2.3, 0.55, 0.66), ("u1", 1.1, 0.68, 0.76)):
        ops = BL.make_ops(group, np)
        upd = make_fast(group, 6, beta, 12)
        ps = []
        for i in range(120):
            upd.sweep(2)
            if i >= 40:
                ps.append(plaq_mean(ops, BL.chain_config(group, np, upd.links(), 0)))
        rep(f"{group} generator mean plaquette in [{lo}, {hi}]", lo < np.mean(ps) < hi, f"{np.mean(ps):.4f}")
    # 2. alignment: decimation b = 2: the block plaquette at (o, X) is the fine 2x2 loop at fine position 2 o + 2 X (here o = 0 only)
    N = 8
    upd = make_fast("su2", N, 2.3, 5)
    for _ in range(5):
        upd.sweep(1)
    ops = BL.make_ops("su2", np)
    U = BL.chain_config("su2", np, upd.links(), 0)
    H = GB.good_levels(ops, U, 3, 0.0)
    for b in (2, 4):
        V = GB.coarse(ops, H, U, int(np.log2(b)))
        fl = block_fields(ops, V)
        cp = np.asarray(fl[0][4])  # (nO, Nc^4): plane (0,1) fundamental plaquette
        # fine loop of b x b in plane (0,1) with lower corner at the fine position
        lines = lines_of(ops, U)
        # general b x b loop from decimated lines: product of b links
        def fine_line(mu, L):
            acc = U[mu]
            for j in range(1, L):
                acc = ops.mul(acc, BL.sh(ops, U[mu], mu, j))
            return acc
        la, lb = fine_line(0, b), fine_line(1, b)
        a_ = ops.mul(la, BL.sh(ops, lb, 0, b))
        b_ = ops.mul(lb, BL.sh(ops, la, 1, b))
        t = np.asarray(ops.dot(a_, b_))[0]
        Nc = N // b
        s_ = b // 2
        idx = [np.array([(2 * o + b * X) % N for o in range(s_) for X in range(Nc)]) for _ in range(4)]
        T = t[np.ix_(*idx)].reshape((s_, Nc) * 4).transpose([0, 2, 4, 6, 1, 3, 5, 7]).reshape((s_ ** 4,) + (Nc,) * 4)
        rep(f"alignment b={b} (w=0 block plaquette = fine {b}x{b} loop at 2o+bX)", np.abs(cp - T).max() < 1e-10, f"max diff {np.abs(cp - T).max():.2e}")
    # 3. regression: planted target (known R2 = 0.30) and null target
    rng = np.random.default_rng(3)
    n, p = 40000, 60
    Xp = rng.standard_normal((n, p)).astype(np.float32)
    sig = Xp[:, 0] + 0.5 * Xp[:, 1] ** 2 - 0.4 * Xp[:, 2] ** 2 + 0.4 * Xp[:, 4]
    sig = sig - sig.mean()
    noise = rng.standard_normal(n)
    Yp = (sig + noise * np.sqrt(sig.var() * (1 - 0.3) / 0.3))[:, None]
    ntr, nva = 20000, 10000
    reg = Reg(1).fit(Xp[:ntr], Yp[:ntr], Xp[ntr:ntr + nva], Yp[ntr:ntr + nva])
    pr = reg.predict(Xp[ntr + nva:])
    te = Yp[ntr + nva:]
    r2 = 1 - ((te - pr) ** 2).mean() / te.var()
    rep("planted target (true R2 0.30): held-out LB below truth and close", 0.22 < r2 < 0.305, f"LB {r2:.4f} tier {reg.choice}")
    Yn = rng.standard_normal((n, 1))
    reg = Reg(1).fit(Xp[:ntr], Yn[:ntr], Xp[ntr:ntr + nva], Yn[ntr:ntr + nva])
    pr = reg.predict(Xp[ntr + nva:])
    te = Yn[ntr + nva:]
    r2 = 1 - ((te - pr) ** 2).mean() / te.var()
    rep("null target: held-out R2 <= 0.003", r2 < 0.003, f"{r2:.5f}")
    # 4. window_mean and the feature plan
    A = np.random.default_rng(1).standard_normal((8, 8, 8, 8))
    wm = window_mean(A, 2)
    rep("window_mean s=2", abs(wm[1, 2, 3, 4] - A[1:3, 2:4, 3:5, 4:6].mean()) < 1e-12)
    plan, nk, names = key_table()
    print(f"feature plan v1: {len(plan)} (slot, offset) terms, {nk} orbit keys")
    s2, plan2_, nk2, _ = plan2()
    print(f"feature plan v2 extras: {len(s2)} slots, {len(plan2_)} (slot, key) groups, {nk2} orbit keys; total columns {nk + nk2 - (nk - N_V1)}")
    rep("v1 column count is the registered 108", nk == N_V1, str(nk))

    # 5. new checks (PREREG-AMEND.md section 4): gauge invariance, fast orbit sums vs explicit shifts, targets
    def rand_links(group, n, seed):
        r = np.random.default_rng(seed)
        o = BL.make_ops(group, np)
        if group == "su2":
            q = r.standard_normal((4, 4, 1, n, n, n, n))
            return o, list(q / np.sqrt((q * q).sum(axis=1, keepdims=True)).transpose(1, 0, 2, 3, 4, 5, 6))
        return o, [r.uniform(-1, 1, (1, n, n, n, n)) for _ in range(4)]

    def gauge_transform(o, W, seed):
        r = np.random.default_rng(seed)
        n = W[0].shape[-1]
        if o.group == "su2":
            q = r.standard_normal((4, 1, n, n, n, n))
            g = q / np.sqrt((q * q).sum(axis=0, keepdims=True))
            return [o.mul(o.mul(g, W[mu]), o.dag(BL.sh(o, g, mu, 1))) for mu in range(4)]
        al = r.uniform(-3, 3, (1, n, n, n, n))
        return [W[mu] + al - BL.sh(o, al, mu, 1) for mu in range(4)]

    for group in ("su2", "u1"):
        o, V = rand_links(group, 4, 7)
        W = gauge_transform(o, V, 8)
        d = np.abs(all_features(o, V) - all_features(o, W)).max()
        rep(f"{group}: all v1+v2 features gauge invariant (random 4^4 lattice)", d < 1e-5, f"max diff {d:.2e}")
        f_fast = v2_features(o, V)
        f_ref = v2_features(o, V, explicit=True)
        d = np.abs(f_fast - f_ref).max()
        rep(f"{group}: v2 orbit sums (Fourier) equal the explicit shift sums", d < 1e-5, f"max diff {d:.2e}")
        sd = fine_targets(o, V, 4)
        sd2 = fine_targets(o, W, 4)
        d = max(np.abs(sd[k] - sd2[k]).max() for k in sd)
        rep(f"{group}: S and smeared Q targets gauge invariant", d < 1e-9, f"max diff {d:.2e}")
    # smeared target with no smearing = spatial plaquette scalar; window targets against explicit means
    global APE_STEPS
    o, V = rand_links("su2", 8, 9)
    keep = APE_STEPS
    APE_STEPS = 0
    sd0 = fine_targets(o, V, 8)
    APE_STEPS = keep
    lines = lines_of(o, V)
    Qd = sum(np.asarray(loop_field(o, lines, mu, nu, 1, 1)[0][0]) for mu, nu in PLANES if mu != TIME)
    rep("Q with 0 smearing steps = spatial plaquette scalar", np.abs(sd0["Q"] - Qd).max() < 1e-12)
    sdq = fine_targets(o, V, 8)
    Tg = target_arrays(sdq, 2, 8)
    # P4 at b = 2, origin 0, cell X: window of side 4 at fine position 2 X + (1 - 2) per axis
    X = (1, 2, 3, 0)
    pos = [(2 * X[i] - 1) % 8 for i in range(4)]
    man = np.mean([sdq["S"][(pos[0] + a_) % 8, (pos[1] + b_) % 8, (pos[2] + c_) % 8, (pos[3] + d_) % 8]
                   for a_ in range(4) for b_ in range(4) for c_ in range(4) for d_ in range(4)])
    rep("target_arrays P4 at b=2 equals the explicit window mean", abs(Tg["P4"][(0,) + X] - man) < 1e-12)
    Tg8 = target_arrays(sdq, 4, 8)  # P8 at b = 4: whole lattice, window 8 = mean over everything
    rep("P8 at N=8 is the lattice mean", abs(Tg8["P8"][0, 0, 0, 0, 0] - sdq["S"].mean()) < 1e-12)
    print("SELFTEST " + ("PASSED" if ok else "FAILED"))
    return 0 if ok else 1


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd")
    sub.add_parser("selftest")
    r = sub.add_parser("run")
    r.add_argument("group")
    r.add_argument("beta", type=float)
    r.add_argument("N", type=int)
    r.add_argument("seed", type=int)
    r.add_argument("n_train", type=int)
    r.add_argument("n_val", type=int)
    r.add_argument("n_test", type=int)
    r.add_argument("every", type=int)
    r.add_argument("n_therm", type=int)
    r.add_argument("M", type=int)
    r.add_argument("out")
    a = ap.parse_args()
    if a.cmd == "selftest":
        return selftest(a)
    if a.cmd == "run":
        return run(a)
    ap.print_help()
    return 1


if __name__ == "__main__":
    sys.exit(main())
