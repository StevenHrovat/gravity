"""GUID v6: Our theory as simulated. Workstream H: the holographic code of Section 9 at scale, by stabilizer methods.

Run:  python3 docs/simulation/holographic_code.py      (numpy and stim 1.16; deterministic, fixed seeds)
Writes docs/simulation/results/holographic_code.json with every number the paper may quote. Each check prints OK or FAIL with what
was got and what was expected; the last line counts them; the exit code is 0 only if every check passes. A miss is a finding: the
script prints it and the JSON keeps it; nothing is tuned to pass.

Construction (scaling docs/qg-verdict/assembly.py). A tile is the six-leg perfect tensor T of the five-qubit code [[5,1,3]]:
T[b, q1..q5] = <q1..q5|ENC|b>/sqrt 2, b the logical leg. A layer of depth D is a rooted tree of tiles: the root has its bulk leg and
five legs to five children; every other tile has a bulk leg, one leg to its parent and four legs to its own children; the leaves'
four child legs are the boundary, 5*4^D qubits in ring order (D=5: 5120 boundary qubits, 1706 tiles). The root's bulk is its logical
leg b. A child tile has two orientations: orientation A (assembly.py's: the parent edge on the logical leg b, the bulk on the
physical leg q1, children on q2..q5) and orientation H (the HaPPY reading of "each tile's logical leg the information sitting there":
the bulk on b, the parent edge on q1, children on q2..q5). A is the main construction; H is reported beside it. Setting (a): every
bulk leg in |0>, a pure state on the boundary. Setting (b): every bulk leg maximally entangled with its own reference qubit R_t.

Method. Each tile map is an isometry that is Clifford; it is synthesised as a stim Tableau from the dense tensor and checked against
it. The network state is composed tile by tile; its stabilizer generators are pushed through the tree as sparse signed Pauli strings
(Aaronson and Gottesman 2004) and checked, generator by generator with its sign, against stim's composition of the same Cliffords.
Entropies come from S(A) = rank(G restricted to A) - |A| bits (Fattal et al. 2004; Hamma et al. 2005), computed with exact GF(2)
elimination on Python integers; the D=1 networks and a 3x3 toric code are checked against dense state vectors.

  [H0] the tile: perfect tensor (all 20 three-leg cuts carry 3 bits); root and child maps as Clifford tableaux equal to the dense maps
  [H1] the network for D = 1..5, both settings, both orientations: n independent generators, every one a +1 stabilizer of stim's
       state; entropies from the stabilizer group equal dense state-vector entropies at D = 1
  [H2] Ryu-Takayanagi on the tree: S(A) against the minimal cut (tree dynamic programming, unit capacity per leg) for all 2^20
       regions at D = 1 and for contiguous intervals, random subsets and unions of intervals at D = 2..5; exceptions characterised
  [H3] entanglement-wedge reconstruction in setting (b): I(R_t : A) for every bulk qubit t against the greedy wedge, the tree
       recursion and the min-cut prediction; recoverable fraction by depth of t and region size
  [H4] erasure threshold of the hierarchy: the exact recursion, its fixed point p_c = (5 - sqrt 13)/6, the exact D = 1 polynomial
       from all 2^20 erasure patterns, and Monte Carlo for D = 1..5 checked sample by sample against the recursion
  [H5] the two witnesses: at scale (D = 5, 5120 qubits, 1706 contents) the syndrome does not depend on the content and two
       independently coded extractions agree; reading the content disturbs it; on one tile, all 1024 Pauli errors, both witnesses,
       lookup correction, and the exact logical failure probability against the closed form for a distance-3 code
  [H6] toric code on L x L tori up to L = 45 (4050 qubits): topological entanglement entropy by Kitaev-Preskill and Levin-Wen,
       gamma = 1 bit (ln 2) for every region size
"""

import os

# One BLAS thread: the machine is shared, and multi-threaded OpenBLAS eigensolvers stall badly when cores are contended.
for _v in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")

import itertools  # noqa: E402
import json  # noqa: E402
import math  # noqa: E402
import random  # noqa: E402
import sys  # noqa: E402
import time  # noqa: E402

import numpy as np  # noqa: E402
import stim  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "results", "holographic_code.json")
T_START = time.perf_counter()
results = []
J = {"meta": {"script": "docs/simulation/holographic_code.py", "numpy": np.__version__, "stim": stim.__version__,
              "python": sys.version.split()[0], "units": "entropies and mutual informations in bits (log base 2)"}}
RUNTIME = {}


def check(label, got, want, tol=0.0):
    got, want = float(got), float(want)
    ok = abs(got - want) <= tol
    print(f"{'OK  ' if ok else 'FAIL'} {label}: {got:.6g} (expected {want:.6g}{f' +- {tol:.3g}' if tol else ''})")
    results.append(ok)
    return ok


def check_true(label, cond):
    print(f"{'OK  ' if cond else 'FAIL'} {label}")
    results.append(bool(cond))
    return bool(cond)


def section(name):
    print(f"\n{name}")
    sys.stdout.flush()


def jsonable(x):
    if isinstance(x, dict):
        return {str(k): jsonable(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [jsonable(v) for v in x]
    if isinstance(x, (np.integer,)):
        return int(x)
    if isinstance(x, (np.floating,)):
        return float(x)
    if isinstance(x, np.ndarray):
        return jsonable(x.tolist())
    if isinstance(x, (np.bool_,)):
        return bool(x)
    return x


# =====================================================================================================================
# The tile
# =====================================================================================================================
I2 = np.eye(2)
PX = np.array([[0, 1], [1, 0]], dtype=complex)
PZ = np.diag([1.0, -1.0]).astype(complex)
PY = 1j * PX @ PZ
PM = {"I": I2, "X": PX, "Y": PY, "Z": PZ}


def kron(*ops):
    out = np.array([[1.0 + 0j]])
    for op in ops:
        out = np.kron(out, op)
    return out


def pauli(word):
    return kron(*[PM[c] for c in word])


STAB5 = ["XZZXI", "IXZZX", "XIXZZ", "ZXIXZ"]  # Laflamme et al. 1996; Bennett et al. 1996
P_CODE = np.eye(32, dtype=complex)
for _w in STAB5:
    P_CODE = P_CODE @ (np.eye(32) + pauli(_w)) / 2
_z = np.zeros(32, dtype=complex)
_z[0] = 1
L0 = P_CODE @ _z
L0 /= np.linalg.norm(L0)
L1 = pauli("XXXXX") @ L0
ENC = np.stack([L0, L1], axis=1)  # 32 x 2: logical qubit -> five physical qubits
T6 = (ENC.T / np.sqrt(2)).reshape([2] * 6)  # legs (b, q1..q5)

# Tile maps. Root: bulk (logical leg b) -> five legs, V_root = ENC. Child, inputs (parent edge e, bulk y), outputs q2..q5:
#   orientation H: V_H|e,y> = sqrt2 (<e|_q1 (x) 1) ENC|y>        (bulk on the logical leg, edge on q1)
#   orientation A: V_A|e,y> = sqrt2 (<y|_q1 (x) 1) ENC|e>        (edge on the logical leg, bulk on q1; assembly.py's CHILD_MAP = 2T)
E5 = ENC.reshape(2, 16, 2)  # (q1, q2..q5, logical)
V_H = np.zeros((16, 4), dtype=complex)
V_A = np.zeros((16, 4), dtype=complex)
for _e in range(2):
    for _y in range(2):
        V_H[:, 2 * _e + _y] = np.sqrt(2) * E5[_e, :, _y]
        V_A[:, 2 * _e + _y] = np.sqrt(2) * E5[_y, :, _e]


def entropy_dense(psi, keep, n):
    """Von Neumann entropy (bits) of the qubits `keep` of a pure state psi on n qubits (dense, eigenvalues of the smaller side)."""
    keep = list(keep)
    rest = [q for q in range(n) if q not in keep]
    m = np.transpose(psi.reshape([2] * n), keep + rest).reshape(2 ** len(keep), -1)
    if m.shape[0] > m.shape[1]:
        m = m.T
    ev = np.linalg.eigvalsh(m @ m.conj().T)
    ev = ev[ev > 1e-12]
    return float(-(ev * np.log2(ev)).sum())


def find_image(V, P_in, n_out):
    """Signed Pauli Q on the outputs with Q V = V P_in (dense search)."""
    target = V @ P_in
    for w in itertools.product("IXYZ", repeat=n_out):
        QV = pauli("".join(w)) @ V
        for s in (1, -1):
            if np.abs(s * QV - target).max() < 1e-9:
                p = stim.PauliString("".join(w).replace("I", "_"))
                return p if s == 1 else -p
    raise RuntimeError("no Pauli image: the map is not Clifford")


def stabilizers_of_image(V, n_out):
    out = []
    for w in itertools.product("IXYZ", repeat=n_out):
        if set(w) == {"I"}:
            continue
        for s in (1, -1):
            if np.abs(s * pauli("".join(w)) @ V - V).max() < 1e-9:
                p = stim.PauliString("".join(w).replace("I", "_"))
                out.append(p if s == 1 else -p)
    return out


def unsigned_key(p):
    return tuple(p[i] for i in range(len(p)))


def group_unsigned(gens, n):
    grp = {unsigned_key(stim.PauliString(n))}
    for g in gens:
        grp |= {unsigned_key(stim.PauliString("".join("_XYZ"[c] for c in h)) * g) for h in grp}
    return grp


def clifford_for(V, k, n):
    """A Clifford tableau U on n qubits with U|v, 0..0> = V|v> for the 2^k inputs v (inputs are the first k qubits)."""
    xs, zs = [], []
    for j in range(k):
        for lst, c in ((xs, "X"), (zs, "Z")):
            w = ["I"] * k
            w[j] = c
            lst.append(find_image(V, pauli("".join(w)), n))
    gens = []
    for s in stabilizers_of_image(V, n):
        if len(gens) < n - k and unsigned_key(s) not in group_unsigned(gens, n):
            gens.append(s)
    D = []
    for j in range(n - k):
        for w in itertools.product("_XYZ", repeat=n):
            p = stim.PauliString("".join(w))
            if p.weight and all(p.commutes(g) for g in xs + zs + D) and all(
                    p.commutes(gens[i]) != (i == j) for i in range(n - k)):
                D.append(p)
                break
    tab = stim.Tableau.from_conjugated_generators(xs=xs + D, zs=zs + gens)
    U = tab.to_unitary_matrix(endian="big")
    W = np.stack([U[:, v << (n - k)] for v in range(2 ** k)], axis=1)
    phase = np.vdot(W[:, 0], V[:, 0])
    return tab, float(np.abs(W * phase - V).max())


# =====================================================================================================================
# The network: sparse signed Pauli generators pushed through the tree
# =====================================================================================================================
def tile_tables(tabC, tabR, setting):
    """Generators each tile adds, and the image of a Pauli on the parent leg e, as signed stim Pauli strings on the tile's
    local qubits. Child local qubits: (e, b, a1, a2[, R]); root local qubits: (b, a1..a4[, R])."""

    def img(tab, word, n):
        p = tab(stim.PauliString(word))
        q = stim.PauliString(n)
        for i in range(len(p)):
            q[i] = p[i]
        return q if p.sign == 1 else -q

    def best(p, gens):
        cands = [p]
        for g in gens:
            cands = cands + [c * g for c in cands]
        return min(cands, key=lambda c: (c.weight, str(c)))

    nC = 5 if setting == "b" else 4
    newC = []
    if setting == "a":
        newC.append(("bulk", img(tabC, "_Z__", 4)))
    else:
        newC.append(("logX", img(tabC, "_X__", 5) * stim.PauliString("____X")))
        newC.append(("logZ", img(tabC, "_Z__", 5) * stim.PauliString("____Z")))
    newC.append(("stab", img(tabC, "__Z_", nC)))
    newC.append(("stab", img(tabC, "___Z", nC)))
    pushC = {c: best(img(tabC, c + "___", nC), [g for _, g in newC]) for c in "XYZ"}
    nR = 6 if setting == "b" else 5
    newR = []
    if setting == "a":
        newR.append(("bulk", img(tabR, "Z____", 5)))
    else:
        newR.append(("logX", img(tabR, "X____", 6) * stim.PauliString("_____X")))
        newR.append(("logZ", img(tabR, "Z____", 6) * stim.PauliString("_____Z")))
    for j in range(1, 5):
        w = ["_"] * 5
        w[j] = "Z"
        newR.append(("stab", img(tabR, "".join(w), nR)))
    return newC, pushC, newR


def build(D, setting, orient):
    """Stabilizer generators of the depth-D network. Physical qubits are numbered as in the stim composition (`ops`)."""
    tabC = TAB_CHILD[orient]
    newC, pushC, newR = tile_tables(tabC, TAB_ROOT, setting)
    gens, touch, ref = [], {}, {}

    def add(p, loc, kind, tile):
        d = {loc[i]: "_XYZ"[p[i]] for i in range(len(p)) if p[i]}
        gid = len(gens)
        gens.append([int(p.sign.real), d, kind, tile])
        for q in d:
            touch.setdefault(q, set()).add(gid)

    loc = list(range(5))
    nq = 5
    if setting == "b":
        loc.append(nq)
        ref[0] = nq
        nq += 1
    for kind, p in newR:
        add(p, loc, kind, 0)
    ops = [("R", loc)]
    depth, parent = [0], [-1]
    queue = [(0, q) for q in range(5)]
    tid = 1
    for d in range(1, D + 1):
        nxt = []
        for par, e in queue:
            t = tid
            tid += 1
            depth.append(d)
            parent.append(par)
            loc = [e, nq, nq + 1, nq + 2]
            nq += 3
            if setting == "b":
                loc.append(nq)
                ref[t] = nq
                nq += 1
            ops.append(("C", loc))
            for gid in sorted(touch.get(e, ())):
                g = gens[gid]
                img = pushC[g[1].pop(e)]
                g[0] *= int(img.sign.real)
                for i, q in enumerate(loc):
                    if img[i]:
                        g[1][q] = "_XYZ"[img[i]]
                        touch.setdefault(q, set()).add(gid)
                if e not in g[1]:
                    touch[e].discard(gid)
            for kind, p in newC:
                add(p, loc, kind, t)
            nxt += [(t, q) for q in loc[:4]]
        queue = nxt
    boundary = [q for _, q in queue]
    code = {"X": 1, "Z": 2, "Y": 3}
    gl = [[(q, code[c]) for q, c in sorted(g[1].items())] for g in gens]
    tch = {}
    for i, g in enumerate(gl):
        for q, _ in g:
            tch.setdefault(q, []).append(i)
    return {"D": D, "setting": setting, "orient": orient, "gens": gens, "gl": gl, "touch": tch, "nq": nq,
            "boundary": boundary, "ref": ref, "ops": ops, "ntiles": tid, "depth": depth, "parent": parent}


def stim_compose(net, content=None, tabs=None):
    """stim's own composition of the network Cliffords. content: None (setting a: bulk |0>; setting b: Bell pair with R_t) or a
    list of single-qubit preparations for every bulk qubit (used for the witnesses)."""
    tabC = TAB_CHILD[net["orient"]]
    sim = stim.TableauSimulator(seed=7)
    sim.set_num_qubits(net["nq"])
    for t, (kind, loc) in enumerate(net["ops"]):
        b = loc[0] if kind == "R" else loc[1]
        if content is not None:
            prepare(sim, b, content[t])
        elif net["setting"] == "b":
            R = loc[-1]
            sim.h(R)
            sim.cx(R, b)
        if kind == "R":
            sim.do_tableau(TAB_ROOT, loc[:5])
        else:
            sim.do_tableau(tabC, loc[:4])
    return sim


def prepare(sim, q, c):
    """Prepare qubit q (in |0>) in cardinal state c: 0:+Z 1:-Z 2:+X 3:-X 4:+Y 5:-Y."""
    if c in (1, 3, 5):
        sim.x(q)
    if c >= 2:
        sim.h(q)
    if c >= 4:
        sim.s(q)


def to_stim(sign, d, n):
    p = stim.PauliString(n)
    for q, c in d.items():
        p[q] = c
    return p if sign > 0 else -p


def stim_verify(net):
    """Every generator, with its sign, is a +1 stabilizer of stim's composed state: C^dag P C is a +Z string."""
    inv = stim_compose(net).current_inverse_tableau()
    bad = 0
    for sign, d, kind, tile in net["gens"]:
        r = inv(to_stim(sign, d, net["nq"]))
        xs, _ = r.to_numpy()
        bad += bool(xs.any() or r.sign != 1)
    return bad


# =====================================================================================================================
# GF(2) linear algebra on Python integers (bit 2k = X part, bit 2k+1 = Z part of column k)
# =====================================================================================================================
def echelon(rows):
    """Lowest-bit echelon basis {lowest bit: vector}; its size is the rank."""
    basis = {}
    for v in rows:
        while v:
            lb = (v & -v).bit_length() - 1
            b = basis.get(lb)
            if b is None:
                basis[lb] = v
                break
            v ^= b
    return basis


def rows_for(gl, order, subset=None):
    pos = {q: k for k, q in enumerate(order)}
    out = []
    for i in (range(len(gl)) if subset is None else subset):
        v = 0
        for q, c in gl[i]:
            k = pos.get(q)
            if k is not None:
                v |= c << (2 * k)
        out.append(v)
    return out


def entropy(net, region):
    """S(A) = rank(generators restricted to A) - |A|, bits. Only generators touching A contribute."""
    touch = net["touch"]
    idx = set()
    for q in region:
        idx.update(touch.get(q, ()))
    return len(echelon(rows_for(net["gl"], region, sorted(idx)))) - len(region)


def recoverability(net, A_set):
    """Setting (b): I(R_t : A) for every tile t, and S(A). Column order [E | R | A] with E the rest of the boundary; vectors whose
    lowest bit lies in R or A span the stabilizers supported on A u R; their R parts span V; I(R_t:A) = dim(V n <X_t, Z_t>)."""
    B = net["boundary"]
    refs = [net["ref"][t] for t in range(net["ntiles"])]
    E = [q for q in B if q not in A_set]
    A = [q for q in B if q in A_set]
    order = E + refs + A
    basis = echelon(rows_for(net["gl"], order))
    lo, hi = 2 * len(E), 2 * (len(E) + len(refs))
    maskR = ((1 << hi) - 1) ^ ((1 << lo) - 1)
    bR = {lb: v & maskR for lb, v in basis.items() if lo <= lb < hi}
    dimSA = sum(1 for lb in basis if lb >= hi)

    def member(v):
        while v:
            b = bR.get((v & -v).bit_length() - 1)
            if b is None:
                return False
            v ^= b
        return True

    I = np.zeros(len(refs), dtype=np.int8)
    for t in range(len(refs)):
        k = lo // 2 + t
        x, z, y = member(1 << (2 * k)), member(2 << (2 * k)), member(3 << (2 * k))
        I[t] = 2 if (x and z) else (1 if (x or y or z) else 0)
    return I, len(A) - dimSA


def subgroup_masks(gl, drop, keep):
    """Support masks (bit i = keep[i]) of all elements of the subgroup supported away from the qubits `drop`."""
    basis = echelon(rows_for(gl, drop + keep))
    vecs = [v >> (2 * len(drop)) for lb, v in basis.items() if lb >= 2 * len(drop)]
    xs = np.zeros(1, dtype=np.int64)
    zs = np.zeros(1, dtype=np.int64)
    for v in vecs:
        gx = sum(1 << i for i in range(len(keep)) if (v >> (2 * i)) & 1)
        gz = sum(1 << i for i in range(len(keep)) if (v >> (2 * i + 1)) & 1)
        xs = np.concatenate([xs, xs ^ gx])
        zs = np.concatenate([zs, zs ^ gz])
    return xs | zs, len(vecs)


def subset_counts(masks, nbits):
    """cnt[A] = number of group elements with support inside A, for every A (fast zeta transform)."""
    cnt = np.bincount(masks, minlength=1 << nbits).astype(np.int64)
    for i in range(nbits):
        v = cnt.reshape(-1, 2, 1 << i)
        v[:, 1, :] += v[:, 0, :]
    return cnt


def log2i(a):
    return np.round(np.log2(a)).astype(np.int64)


# =====================================================================================================================
# Tree algorithms, vectorised over many boundary regions (M: regions x boundary, 0/1 in ring order)
# =====================================================================================================================
def level_sizes(D):
    return [1] + [5 * 4 ** (d - 1) for d in range(1, D + 1)]


def flat(levels):
    """Concatenate per-depth arrays (R x m_d) into BFS tile order (R x ntiles)."""
    return np.concatenate([levels[d] for d in sorted(levels)], axis=1)


def tree_cut(M, D, own):
    """Minimal cut through the tree, unit capacity per leg. own = 0: bulk legs fixed (setting a); own = 1: every bulk leg is cut
    when its tile sits on A's side (its reference is in the complement, setting b). Returns mc, the number of optimal tile-side
    assignments (saturated at 2), and F[s] = the least total cut with tile t on side s (rerooting), in BFS order."""
    R = M.shape[0]
    cin = M.reshape(R, -1, 4).sum(2).astype(np.int32)
    D0, D1 = {D: cin}, {D: 4 - cin + own}
    W0, W1 = {D: np.ones_like(cin)}, {D: np.ones_like(cin)}
    C0, C1 = {}, {}
    for d in range(D, 0, -1):
        k = 5 if d == 1 else 4
        c0 = np.minimum(D0[d], 1 + D1[d])
        c1 = np.minimum(D1[d], 1 + D0[d])
        w0 = np.minimum((D0[d] == c0) * W0[d] + (1 + D1[d] == c0) * W1[d], 2)
        w1 = np.minimum((D1[d] == c1) * W1[d] + (1 + D0[d] == c1) * W0[d], 2)
        C0[d], C1[d] = c0, c1
        D0[d - 1] = c0.reshape(R, -1, k).sum(2)
        D1[d - 1] = c1.reshape(R, -1, k).sum(2) + own
        W0[d - 1] = np.minimum(np.prod(w0.reshape(R, -1, k), axis=2), 2)
        W1[d - 1] = np.minimum(np.prod(w1.reshape(R, -1, k), axis=2), 2)
    mc = np.minimum(D0[0][:, 0], D1[0][:, 0])
    nopt = np.minimum((D0[0][:, 0] == mc) * W0[0][:, 0] + (D1[0][:, 0] == mc) * W1[0][:, 0], 2)
    U0, U1 = {0: np.zeros((R, 1), np.int32)}, {0: np.zeros((R, 1), np.int32)}
    for d in range(1, D + 1):
        k = 5 if d == 1 else 4
        r0 = np.repeat(U0[d - 1] + D0[d - 1], k, axis=1) - C0[d]
        r1 = np.repeat(U1[d - 1] + D1[d - 1], k, axis=1) - C1[d]
        U0[d] = np.minimum(r0, 1 + r1)
        U1[d] = np.minimum(r1, 1 + r0)
    F0 = flat({d: D0[d] + U0[d] for d in D0})
    F1 = flat({d: D1[d] + U1[d] for d in D1})
    return mc, nopt, F0, F1


def tree_recursion(M, D):
    """The recursion of [H4], sample by sample: an edge is available from below when >= 3 of the 4 legs under it are; from above
    when >= 3 of the parent's other 4 non-bulk legs are; a bulk qubit is recoverable when >= 3 of its tile's 5 non-bulk legs are
    available (the root: >= 3 of its 5 children). Returns recoverable (R x ntiles, BFS order)."""
    R = M.shape[0]
    cin = M.reshape(R, -1, 4).sum(2).astype(np.int32)
    cnt, ad = {D: cin}, {D: cin >= 3}
    for d in range(D - 1, 0, -1):
        cnt[d] = ad[d + 1].reshape(R, -1, 4).sum(2)
        ad[d] = cnt[d] >= 3
    root_cnt = ad[1].sum(1)
    rec = {0: (root_cnt >= 3)[:, None]}
    au = {1: (root_cnt[:, None] - ad[1]) >= 3}
    for d in range(2, D + 1):
        au[d] = (np.repeat(cnt[d - 1] + au[d - 1], 4, axis=1) - ad[d]) >= 3
    for d in range(1, D + 1):
        rec[d] = (au[d] + cnt[d]) >= 3
    return flat(rec)


def tree_greedy(M, D):
    """The greedy algorithm of Pastawski et al. (2015) to its fixed point: a tile is absorbed into the wedge when at least 3 of
    its 5 non-bulk legs lie in the region; its legs then join the region. Returns absorbed (R x ntiles, BFS order)."""
    R = M.shape[0]
    m = level_sizes(D)
    cin = M.reshape(R, -1, 4).sum(2).astype(np.int32)
    edge = {d: np.zeros((R, m[d]), bool) for d in range(1, D + 1)}
    absd = {d: np.zeros((R, m[d]), bool) for d in range(0, D + 1)}
    while True:
        changed = False
        for d in range(0, D + 1):
            k = 5 if d == 0 else 4
            below = cin if d == D else edge[d + 1].reshape(R, -1, k).sum(2)
            count = below + (edge[d] if d >= 1 else 0)
            new = (count >= 3) & ~absd[d]
            if new.any():
                absd[d] |= new
                changed = True
        for d in range(1, D + 1):
            k = 5 if d == 1 else 4
            upd = absd[d] | np.repeat(absd[d - 1], k, axis=1)
            if (upd & ~edge[d]).any():
                edge[d] |= upd
                changed = True
        if not changed:
            return flat(absd)


def region_matrix(regions, n):
    M = np.zeros((len(regions), n), np.uint8)
    for i, reg in enumerate(regions):
        M[i, reg] = 1
    return M


def interval(st, L, n):
    return [(st + i) % n for i in range(L)]


# =====================================================================================================================
print("GUID v6, workstream H: the holographic code of Section 9 at scale (stabilizer methods)")
section("[H0] The tile: the six-leg perfect tensor of [[5,1,3]], and its maps as Clifford tableaux")
_t = time.perf_counter()
psi6 = T6.reshape(-1)
check("norm of the six-leg state", np.linalg.norm(psi6), 1.0, 1e-12)
cut_min = {k: min(entropy_dense(psi6, c, 6) for c in itertools.combinations(range(6), k)) for k in (1, 2, 3)}
check("min over all 6 one-leg cuts of S (bits)", cut_min[1], 1.0, 1e-9)
check("min over all 15 two-leg cuts of S (bits)", cut_min[2], 2.0, 1e-9)
check("min over all 20 three-leg cuts of S (bits): a perfect tensor", cut_min[3], 3.0, 1e-9)
check("assembly.py's CHILD_MAP = 2T is orientation A's child map (max deviation)",
      np.abs((2 * T6).reshape(4, 16).T - V_A).max(), 0.0, 1e-12)
TAB_ROOT, err_root = clifford_for(ENC, 1, 5)
check("root map: |U_root|y,0000> - ENC|y>| for the stim tableau (complex64)", err_root, 0.0, 1e-6)
TAB_CHILD = {}
J["H0"] = {"perfect_tensor_min_cut_entropy_bits": cut_min}
for _o, _V in (("A", V_A), ("H", V_H)):
    check(f"child map, orientation {_o}, is an isometry: |V^dag V - 1|", np.abs(_V.conj().T @ _V - np.eye(4)).max(), 0.0, 1e-12)
    TAB_CHILD[_o], _err = clifford_for(_V, 2, 4)
    check(f"child map, orientation {_o}: |U|e,y,00> - V|e,y>| for the stim tableau", _err, 0.0, 1e-6)
# The five-leg tile of setting (a) (bulk fixed to |0>) is an AME(5,2) state: any two legs carry 2 bits. Its parent edge e then
# shares 1 bit with every pair of child legs; with the bulk leg open (setting b, six legs) it shares nothing with any pair.
_mi = {}
for _o, _V in (("A", V_A), ("H", V_H)):
    five = (_V.reshape(16, 2, 2)[:, :, 0].T / np.sqrt(2)).reshape(-1)  # legs (e, c1..c4), bulk in |0>
    six = (_V.reshape(16, 2, 2).transpose(1, 2, 0) / 2).reshape(-1)  # legs (e, R_bulk, c1..c4), bulk Bell-paired with R
    i5 = [1 + 2 - entropy_dense(five, [0, 1 + a, 1 + b], 5) for a, b in itertools.combinations(range(4), 2)]
    i6 = [1 + 2 - entropy_dense(six, [0, 2 + a, 2 + b], 6) for a, b in itertools.combinations(range(4), 2)]
    _mi[_o] = {"I_e_pair_bulk_fixed": i5, "I_e_pair_bulk_open": i6}
    check(f"orientation {_o}, bulk fixed: I(parent edge : any 2 of the 4 child legs), min = max (bits)", min(i5) + max(i5), 2.0, 1e-9)
    check(f"orientation {_o}, bulk open: I(parent edge : any 2 of the 4 child legs), max (bits)", max(i6), 0.0, 1e-9)
J["H0"]["mutual_information_edge_pair"] = _mi
RUNTIME["H0"] = time.perf_counter() - _t

# =====================================================================================================================
section("[H1] The network: generators pushed through the tree, checked against stim and against dense state vectors")
_t = time.perf_counter()
NETS = {}
H1 = {}
all_indep, all_signed = True, True
for _o in ("A", "H"):
    for _D in range(1, 6):
        for _s in "ab":
            net = build(_D, _s, _o)
            NETS[(_o, _D, _s)] = net
            n = len(net["boundary"])
            want = n + (net["ntiles"] if _s == "b" else 0)
            rank = len(echelon(rows_for(net["gl"], list(range(net["nq"])))))
            bad = stim_verify(net)
            all_indep &= (len(net["gl"]) == want == rank == net["nq"])
            all_signed &= bad == 0
            H1[f"{_o}_D{_D}_{_s}"] = {"boundary_qubits": n, "tiles": net["ntiles"], "qubits": net["nq"], "generators": len(net["gl"]),
                                      "gf2_rank": rank, "not_plus_one_stabilizers_in_stim": bad,
                                      "total_weight": sum(len(g) for g in net["gl"]), "max_weight": max(len(g) for g in net["gl"])}
            if _D == 5 and _o == "A":
                print(f"     D=5, setting ({_s}): {n} boundary qubits, {net['ntiles']} tiles, {net['nq']} qubits, "
                      f"{len(net['gl'])} generators, GF(2) rank {rank}, total weight {H1[f'{_o}_D{_D}_{_s}']['total_weight']}")
check_true("20 networks (D = 1..5, settings a and b, orientations A and H): n independent generators on n qubits (GF(2) rank)",
           all_indep)
check_true("every generator, sign included, is a +1 stabilizer of stim's own composition of the tile Cliffords (C^dag P C = +Z..Z)",
           all_signed)
check("boundary qubits at D = 5", len(NETS[("A", 5, "a")]["boundary"]), 5120)
check("tiles (bulk qubits) at D = 5", NETS[("A", 5, "a")]["ntiles"], 1706)
# Independent route: contract the dense tensors directly (numpy einsum, as assembly.py does) for D = 1, setting (a).
dense_dev = {}
_rng = random.Random(11)
_regions = [interval(st, L, 20) for st, L in [(0, 10), (2, 8), (1, 9), (0, 5), (3, 7), (5, 10), (17, 6), (6, 4)]]
_regions += [sorted(_rng.sample(range(20), _rng.randint(1, 10))) for _ in range(24)]
for _o, _V in (("A", V_A), ("H", V_H)):
    child = _V.reshape(16, 2, 2)[:, :, 0].T.reshape([2] * 5)
    root = ENC[:, 0].reshape([2] * 5)
    psi = np.einsum("jklmn,jabcd,kefgh,liopq,mstuv,nwxyz->abcdefghiopqstuvwxyz", root, child, child, child, child, child,
                    optimize=True).reshape(-1)
    net = NETS[(_o, 1, "a")]
    B = net["boundary"]
    dense_dev[_o] = max(abs(entropy_dense(psi, reg, 20) - entropy(net, [B[i] for i in reg])) for reg in _regions)
    check(f"D=1, orientation {_o}: max |S_dense - S_stabilizer| over {len(_regions)} regions (bits)", dense_dev[_o], 0.0, 1e-9)
J["H1"] = {"networks": H1, "dense_check_D1_max_abs_dev_bits": dense_dev, "dense_check_regions": _regions}
RUNTIME["H1"] = time.perf_counter() - _t

# =====================================================================================================================
section("[H2] Ryu-Takayanagi on the tree: S(A) from the stabilizer group against the minimal cut")
_t = time.perf_counter()


def residual_tiles(M, D):
    """Tiles in neither greedy wedge: absorbed neither from A nor from its boundary complement (the residual region)."""
    return (~tree_greedy(M, D) & ~tree_greedy(1 - M, D)).sum(1)


def rt_stats(S, mc, nopt, resid):
    S, mc, nopt, resid = np.asarray(S), np.asarray(mc), np.asarray(nopt), np.asarray(resid)
    deficit = mc - S
    ex = deficit != 0
    return {"regions": int(len(S)), "S_equals_mincut": int((deficit == 0).sum()), "exceptions": int(ex.sum()),
            "exception_fraction": float(ex.mean()), "S_above_mincut": int((deficit < 0).sum()),
            "max_deficit_bits": int(deficit.max()), "deficit_histogram": {int(k): int((deficit == k).sum()) for k in np.unique(deficit)},
            "degenerate_mincut": int((nopt >= 2).sum()), "exceptions_with_unique_mincut": int((ex & (nopt < 2)).sum()),
            "regions_with_residual": int((resid > 0).sum()), "exceptions_with_empty_residual": int((ex & (resid == 0)).sum()),
            "max_of_deficit_minus_floor_half_residual": int((deficit - resid // 2).max())}


H2 = {"D1_exhaustive": {}, "sampled": {}}
MASKS20 = np.arange(1 << 20, dtype=np.int64)
M1 = ((MASKS20[:, None] >> np.arange(20)) & 1).astype(np.uint8)  # all 2^20 boundary regions at D = 1
PC20 = M1.sum(1).astype(np.int64)
IV20 = np.array(sorted({sum(1 << ((st + i) % 20) for i in range(L)) for st in range(20) for L in range(1, 20)}))
MC1 = {own: tree_cut(M1, 1, own) for own in (0, 1)}
RES1 = residual_tiles(M1, 1)
S1 = {}
for _o in ("A", "H"):
    na, nb = NETS[(_o, 1, "a")], NETS[(_o, 1, "b")]
    sup, _ = subgroup_masks(na["gl"], [], na["boundary"])
    S1[(_o, "a")] = PC20 - log2i(subset_counts(sup, 20))
    sup, _ = subgroup_masks(nb["gl"], [nb["ref"][t] for t in range(6)], nb["boundary"])
    S1[(_o, "b")] = PC20 - log2i(subset_counts(sup, 20))
    for _s, own in (("a", 0), ("b", 1)):
        mc, nopt = MC1[own][0], MC1[own][1]
        H2["D1_exhaustive"][f"{_o}_{_s}"] = {"all_regions": rt_stats(S1[(_o, _s)], mc, nopt, RES1),
                                            "intervals": rt_stats(S1[(_o, _s)][IV20], mc[IV20], nopt[IV20], RES1[IV20])}


def region_sets(D, rng):
    n = 5 * 4 ** D
    if D == 2:
        iv = [(st, L) for st in range(n) for L in range(1, n // 2 + 1)]
    elif D == 3:
        iv = [(st, L) for st in range(n) for L in range(1, 65)]
        iv += [(st, L) for st in sorted(rng.sample(range(n), 40)) for L in range(65, n // 2 + 1)]
    else:
        starts = sorted(rng.sample(range(n), 48 if D == 4 else 32))
        iv = [(st, L) for st in starts for L in list(range(1, 129)) + list(range(129, n // 2 + 1, 8 if D == 4 else 64))]
    nr = 1500
    rnd = []
    for i in range(nr):
        size = int(math.exp(rng.uniform(0, math.log(n / 2)))) if i % 2 == 0 else rng.randint(1, n - 1)
        rnd.append(sorted(rng.sample(range(n), size)))
    multi = []
    for _ in range(nr):
        k = rng.randint(2, 6)
        reg = set()
        for _ in range(k):
            reg.update(interval(rng.randrange(n), int(math.exp(rng.uniform(0, math.log(n / (2 * k))))), n))
        multi.append(sorted(reg))
    return {"intervals": [interval(st, L, n) for st, L in iv], "random_subsets": rnd, "unions_of_2_to_6_intervals": multi}


_rng = random.Random(2026)
for _D in range(2, 6):
    regsets = region_sets(_D, _rng)
    n = 5 * 4 ** _D
    for cls, regs in regsets.items():
        M = region_matrix(regs, n)
        cuts = {own: tree_cut(M, _D, own)[:2] for own in (0, 1)}
        resid = residual_tiles(M, _D)
        for _o in ("A", "H"):
            for _s, own in (("a", 0), ("b", 1)):
                net = NETS[(_o, _D, _s)]
                B = net["boundary"]
                S = [entropy(net, [B[i] for i in reg]) for reg in regs]
                H2["sampled"][f"{_o}_{_s}_D{_D}_{cls}"] = rt_stats(S, cuts[own][0], cuts[own][1], resid)
    print(f"     D={_D}: {sum(len(v) for v in regsets.values())} regions per network "
          f"({', '.join(f'{len(v)} {k}' for k, v in regsets.items())}), {time.perf_counter() - _t:.0f} s")

ALL_H2 = list(H2["D1_exhaustive"].items())
ALL_H2 = [(f"D1_{k}_{c}", v[c]) for k, v in ALL_H2 for c in ("all_regions", "intervals")] + list(H2["sampled"].items())
print("     exceptions to S(A) = min cut, as exceptions/regions (max deficit in bits):")
print("       class                          A_a                 A_b          H_a                 H_b")
_rows = [("D=1 all 2^20 regions", lambda o, s: H2["D1_exhaustive"][f"{o}_{s}"]["all_regions"]),
         ("D=1 all 380 intervals", lambda o, s: H2["D1_exhaustive"][f"{o}_{s}"]["intervals"])]
for _D in range(2, 6):
    for cls in ("intervals", "random_subsets", "unions_of_2_to_6_intervals"):
        _rows.append((f"D={_D} {cls}", lambda o, s, _D=_D, cls=cls: H2["sampled"][f"{o}_{s}_D{_D}_{cls}"]))
for name, get in _rows:
    cells = [f"{get(o, s)['exceptions']}/{get(o, s)['regions']} ({get(o, s)['max_deficit_bits']})" for o in "AH" for s in "ab"]
    print(f"       {name:30s} " + "  ".join(f"{c:18s}" for c in cells))
_b = [v for k, v in ALL_H2 if "_b" in k]
_a = [v for k, v in ALL_H2 if "_a" in k]
n_b = sum(v["regions"] for v in _b)
check("setting (b), every bulk leg open: regions with S(A) != min cut, over all depths, classes and both orientations",
      sum(v["exceptions"] for v in _b), 0)
check("setting (a): regions with S(A) above the min cut (a tensor network never exceeds its cut)", sum(v["S_above_mincut"] for v in _a), 0)
check("setting (a), orientation A (assembly.py's): contiguous intervals with S(A) != min cut, D = 1..5",
      sum(v["exceptions"] for k, v in ALL_H2 if k.startswith("A_a") and "intervals" in k and "unions" not in k)
      + H2["D1_exhaustive"]["A_a"]["intervals"]["exceptions"], 0)
check("setting (a): exceptions whose residual region is empty (every tile in the greedy wedge of A or of its complement)",
      sum(v["exceptions_with_empty_residual"] for v in _a), 0)
check("setting (a): largest (deficit - floor(residual tiles / 2)) over all regions; <= 0 means deficit <= residual/2",
      max(v["max_of_deficit_minus_floor_half_residual"] for v in _a), 0)
H2["summary"] = {"setting_b_regions_tested": n_b, "setting_a_regions_tested": sum(v["regions"] for v in _a),
                 "setting_a_exceptions_with_unique_mincut": sum(v["exceptions_with_unique_mincut"] for v in _a)}
J["H2"] = H2
RUNTIME["H2"] = time.perf_counter() - _t
