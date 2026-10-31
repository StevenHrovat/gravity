"""GUID v6: Our theory as simulated. Workstream H: the holographic code of Section 9 at scale, by stabilizer methods.

Run:  python3 docs/simulation/holographic_code.py      (numpy and stim 1.16; deterministic, fixed seeds; about 10 minutes on one
      core, peak memory under 1 GB)
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
  [H4] erasure threshold of the hierarchy: the exact recursion, its fixed point p_c = (5 - sqrt 13)/6 (against 1/2 for a plain
       concatenation of the five-qubit code), the exact D = 1 polynomial from all 2^20 erasure patterns, and Monte Carlo for
       D = 1..5 checked sample by sample against the recursion
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
    # The image of a parent-leg Pauli is shortened only by reference-free generators, so that a reference-free generator stays
    # reference-free (the code stabilizers) and a logical generator keeps only its own reference.
    pushC = {c: best(img(tabC, c + "___", nC), [g for kind, g in newC if kind in ("stab", "bulk")]) for c in "XYZ"}
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
    check(f"orientation {_o}, bulk fixed: I(parent edge : any 2 of the 4 child legs), min over the 6 pairs (bits)", min(i5), 1.0, 1e-9)
    check(f"orientation {_o}, bulk fixed: I(parent edge : any 2 of the 4 child legs), max over the 6 pairs (bits)", max(i5), 1.0, 1e-9)
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
_clean = True
for (_o, _D, _s), net in NETS.items():
    if _s == "b":
        refq = {q: t for t, q in net["ref"].items()}
        for sign, d, kind, tile in net["gens"]:
            rs = [refq[q] for q in d if q in refq]
            _clean &= (rs == []) if kind == "stab" else (rs == [tile])
check_true("setting (b): every code-stabilizer generator is reference-free and every logical generator touches only its own "
           "reference qubit", _clean)
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
    if _o == "H":  # an exception to RT found in [H2], confirmed here by the dense contraction alone
        check("D=1, orientation H, dense: S of the interval of boundary qubits 0..9 (its minimal cut is 4)",
              entropy_dense(psi, interval(0, 10, 20), 20), 3.0, 1e-9)
        check("D=1: the minimal cut of that interval (tree dynamic programming)",
              tree_cut(region_matrix([interval(0, 10, 20)], 20), 1, 0)[0][0], 4)
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

# =====================================================================================================================
section("[H3] Entanglement-wedge reconstruction in setting (b): I(R_t : A) for every bulk qubit t")
_t = time.perf_counter()


def wedge_compare(I, greedy, rec, Icut):
    I, greedy, rec, Icut = (np.asarray(x) for x in (I, greedy, rec, Icut))
    ex = I == 2
    return {"pairs": int(I.size), "I_values": sorted(int(v) for v in np.unique(I)), "I_equals_1": int((I == 1).sum()),
            "exact_vs_greedy_mismatch": int((ex != greedy).sum()), "greedy_vs_recursion_mismatch": int((greedy != rec).sum()),
            "mincut_prediction_equal": int((Icut == I).sum()), "mincut_prediction_is_1_tie": int((Icut == 1).sum()),
            "mincut_mismatch_not_tie": int(((Icut != I) & (Icut != 1)).sum())}


def icut_of(M, D):
    mc, _, F0, F1 = tree_cut(M, D, 1)
    return 1 + np.minimum(F0, F1) - np.minimum(F1 - 1, F0 + 1), mc


H3 = {"D1_exhaustive": {}, "sampled": {}, "recoverable_fraction_by_depth": {}}
I1 = {}
_icut1 = 1 + np.minimum(MC1[1][2], MC1[1][3]) - np.minimum(MC1[1][3] - 1, MC1[1][2] + 1)
_gr1, _rec1 = tree_greedy(M1, 1), tree_recursion(M1, 1)
for _o in ("A", "H"):
    nb = NETS[(_o, 1, "b")]
    refs = [nb["ref"][t] for t in range(6)]
    I1[_o] = np.zeros((1 << 20, 6), np.int8)
    for t in range(6):
        sup, _ = subgroup_masks(nb["gl"], [r for r in refs if r != refs[t]], nb["boundary"] + [refs[t]])
        cnt = subset_counts(sup, 21)
        I1[_o][:, t] = log2i(cnt[MASKS20 | (1 << 20)]) - log2i(cnt[MASKS20])
    H3["D1_exhaustive"][_o] = wedge_compare(I1[_o], _gr1, _rec1, _icut1)

FRACS = [0.05, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 0.95]
_rng = random.Random(77)
for _D in range(2, 6):
    n = 5 * 4 ** _D
    nper = {2: 12, 3: 10, 4: 8, 5: 6}[_D]
    regs = {"intervals": [], "random_subsets": []}
    for f in FRACS:
        size = int(round(f * n))
        for _ in range(nper):
            regs["intervals"].append((f, interval(_rng.randrange(n), size, n)))
            regs["random_subsets"].append((f, sorted(_rng.sample(range(n), size))))
    depth = np.array(NETS[("A", _D, "b")]["depth"])
    for _o in ("A", "H"):
        net = NETS[(_o, _D, "b")]
        B = net["boundary"]
        for cls, rl in regs.items():
            M = region_matrix([r for _, r in rl], n)
            I = np.zeros((len(rl), net["ntiles"]), np.int8)
            Sb = np.zeros(len(rl), np.int64)
            for i, (_, r) in enumerate(rl):
                I[i], Sb[i] = recoverability(net, {B[j] for j in r})
            Icut, mcb = icut_of(M, _D)
            st = wedge_compare(I, tree_greedy(M, _D), tree_recursion(M, _D), Icut)
            st["S_b_equals_mincut_b"] = int((Sb == mcb).sum())
            st["regions"] = len(rl)
            H3["sampled"][f"{_o}_D{_D}_{cls}"] = st
            fr = np.array([f for f, _ in rl])
            H3["recoverable_fraction_by_depth"][f"{_o}_D{_D}_{cls}"] = {
                f"{f:.2f}": [float((I[fr == f][:, depth == d] == 2).mean()) for d in range(_D + 1)] for f in FRACS}
    print(f"     D={_D}: {len(FRACS) * nper} intervals and {len(FRACS) * nper} random subsets per orientation, "
          f"{time.perf_counter() - _t:.0f} s")
_w = list(H3["D1_exhaustive"].values()) + list(H3["sampled"].values())
_pairs = sum(v["pairs"] for v in _w)
print(f"     (region, bulk qubit) pairs compared: {_pairs} (D = 1: all 2^20 regions x 6 tiles x 2 orientations)")
check("pairs with I(R_t : A) = 1 bit (partial recovery); expected none: I is 0 or 2", sum(v["I_equals_1"] for v in _w), 0)
check("pairs where the exact wedge (I = 2) differs from the greedy wedge", sum(v["exact_vs_greedy_mismatch"] for v in _w), 0)
check("pairs where the greedy wedge differs from the tree recursion of [H4]", sum(v["greedy_vs_recursion_mismatch"] for v in _w), 0)
check("setting (b): sampled regions with S(A) != min cut (RT, recomputed by the column-ordered elimination)",
      sum(v["regions"] - v["S_b_equals_mincut_b"] for v in H3["sampled"].values()), 0)
_mm = sum(v["mincut_mismatch_not_tie"] for v in _w)
_tie = sum(v["mincut_prediction_is_1_tie"] for v in _w)
_eq = sum(v["mincut_prediction_equal"] for v in _w)
print(f"     min-cut wedge prediction I_cut = 1 + mc(A) - mc(A u R_t): equal to I in {_eq} of {_pairs} pairs; "
      f"tie (I_cut = 1) in {_tie}; other mismatches {_mm}")
check("pairs where the min-cut prediction is decided (not a tie) and wrong", _mm, 0)
H3["summary"] = {"pairs": _pairs, "mincut_prediction_equal": _eq, "mincut_ties": _tie, "mincut_wrong_not_tie": _mm}
print("     orientation A, D = 5: fraction of bulk qubits recoverable, by depth (0 = root) and region size |A|/n")
for cls in ("intervals", "random_subsets"):
    tab = H3["recoverable_fraction_by_depth"][f"A_D5_{cls}"]
    print(f"       {cls}:  |A|/n " + " ".join(f"{f:>5}" for f in tab))
    for d in range(6):
        print(f"         depth {d}:      " + " ".join(f"{tab[f][d]:5.2f}" for f in tab))
J["H3"] = H3
RUNTIME["H3"] = time.perf_counter() - _t

# =====================================================================================================================
section("[H4] Erasure threshold of the hierarchy: exact recursion, its fixed point, and Monte Carlo for D = 1..5")
_t = time.perf_counter()


def binom_ge(n, k, a):
    return sum(math.comb(n, j) * a ** j * (1 - a) ** (n - j) for j in range(k, n + 1))


def analytic(D, p):
    """Probability that a bulk qubit at depth d = 0..D is recoverable from the surviving boundary, setting (b).
    a_h: an edge above a tile of height h (leaf: h = 1) is available from below; a_0 = 1 - p is a surviving boundary qubit.
    beta_d: the edge into a depth-d tile is available from above."""
    a = [1 - p]
    for _ in range(D):
        a.append(binom_ge(4, 3, a[-1]))
    P = [binom_ge(5, 3, a[D])]
    beta = None
    for d in range(1, D + 1):
        if d == 1:
            beta = binom_ge(4, 3, a[D])
        else:
            s = a[D - d + 1]
            beta = beta * binom_ge(3, 2, s) + (1 - beta) * binom_ge(3, 3, s)
        c = a[D - d]
        P.append(beta * binom_ge(4, 2, c) + (1 - beta) * binom_ge(4, 3, c))
    return P


A_STAR = (1 + math.sqrt(13)) / 6
P_C = (5 - math.sqrt(13)) / 6
f_map = lambda a: 4 * a ** 3 - 3 * a ** 4  # noqa: E731
check("fixed point of a -> 4a^3 - 3a^4 at a* = (1 + sqrt 13)/6: |f(a*) - a*|", abs(f_map(A_STAR) - A_STAR), 0.0, 1e-15)
LAMBDA = 12 * A_STAR ** 2 * (1 - A_STAR)
check("slope f'(a*) = 12 a*^2 (1 - a*) (> 1: the fixed point is unstable, a threshold)", LAMBDA, 1.6432, 1e-4)
check("erasure threshold p_c = 1 - a* = (5 - sqrt 13)/6", P_C, 0.232408, 1e-6)
P_ROOT_C = binom_ge(5, 3, A_STAR)
check("at p_c every depth gives the same root recovery probability P(Bin(5, a*) >= 3) (max spread over D = 1..12)",
      max(analytic(D, P_C)[0] for D in range(1, 13)) - min(analytic(D, P_C)[0] for D in range(1, 13)), 0.0, 1e-12)
print(f"     root recovery probability at the crossing: {P_ROOT_C:.6f}")
# For comparison: a plain concatenation of the five-qubit code (no bulk qubit in the inner tiles, five children per tile) needs
# 3 of 5 children, a -> P(Bin(5, a) >= 3); its fixed point is 1/2, the no-cloning bound of the erasure channel.
G_CONC = lambda a: binom_ge(5, 3, a)  # noqa: E731
check("plain concatenated [[5,1,3]] (no inner bulk qubits): fixed point of a -> P(Bin(5,a) >= 3) at a = 1/2", G_CONC(0.5), 0.5, 1e-15)
check("its slope there (central difference; 30 a^2 (1-a)^2 = 15/8 > 1, so p_c = 1/2)", (G_CONC(0.5 + 1e-6) - G_CONC(0.5 - 1e-6)) / 2e-6, 1.875, 1e-6)
# D = 1 exactly: the 2^20 regions of [H3] are the 2^20 erasure patterns.
P_GRID = [0.05, 0.10, 0.15, 0.20, 0.22, round(P_C, 6), 0.25, 0.28, 0.32, 0.40, 0.50]
_k = PC20
H4 = {"a_star": A_STAR, "p_c": P_C, "slope_at_fixed_point": LAMBDA, "root_probability_at_p_c": P_ROOT_C, "p_grid": P_GRID,
      "D1_exact": {}, "analytic": {}, "monte_carlo": {}}
for _o in ("A", "H"):
    rec_root = I1[_o][:, 0] == 2
    rec_d1 = (I1[_o][:, 1:] == 2).mean(1)
    cnt_root = np.bincount(_k[rec_root], minlength=21)
    cnt_d1 = np.bincount(_k, weights=rec_d1, minlength=21)
    dev = 0.0
    for p in np.linspace(0.0, 1.0, 101):
        w = np.array([p ** (20 - k) * (1 - p) ** k for k in range(21)])
        an = analytic(1, p)
        dev = max(dev, abs(float(cnt_root @ w) - an[0]), abs(float(cnt_d1 @ w) - an[1]))
    H4["D1_exact"][_o] = {"recoverable_root_patterns_by_surviving_count": cnt_root.tolist(), "max_dev_from_recursion": dev}
    check(f"D=1, orientation {_o}: exact recovery polynomial from all 2^20 erasure patterns vs the recursion, max |diff| on 101 p",
          dev, 0.0, 1e-11)
for _D in range(1, 9):
    H4["analytic"][f"D{_D}"] = {f"{p:.4f}": analytic(_D, p) for p in P_GRID}
NSAMP = {1: 4000, 2: 2000, 3: 1500, 4: 1000, 5: 400}
_nrng = np.random.default_rng(20261031)
mism, ione, zmax, nsamples = 0, 0, 0.0, 0
print("     Monte Carlo, orientation A: fraction of samples with the root recoverable (analytic in brackets)")
print("       p       " + "  ".join(f"D={D}            " for D in range(1, 6)))
mc_root = {}
for p in P_GRID:
    for _D in range(1, 6):
        net = NETS[("A", _D, "b")]
        B = net["boundary"]
        n = len(B)
        N = NSAMP[_D]
        M = (_nrng.random((N, n)) >= p).astype(np.uint8)  # 1 = survives
        I = np.array([recoverability(net, {B[j] for j in np.nonzero(M[i])[0]})[0] for i in range(N)])
        rec = tree_recursion(M, _D)
        mism += int(((I == 2) != rec).sum())
        ione += int((I == 1).sum())
        nsamples += N
        depth = np.array(net["depth"])
        an = analytic(_D, p)
        frac = [float((I[:, depth == d] == 2).mean()) for d in range(_D + 1)]
        # z-score of the per-depth fractions; tiles at one depth share a sample, so use the per-sample mean's spread
        for d in range(_D + 1):
            per_sample = (I[:, depth == d] == 2).mean(1)
            se = per_sample.std(ddof=1) / math.sqrt(N) if per_sample.std() > 0 else math.sqrt(max(an[d] * (1 - an[d]), 1e-12) / N)
            zmax = max(zmax, abs(frac[d] - an[d]) / max(se, 1.0 / N))
        H4["monte_carlo"][f"D{_D}_p{p:.4f}"] = {"samples": N, "recoverable_fraction_by_depth": frac, "analytic_by_depth": an}
        mc_root[(_D, p)] = frac[0]
    print(f"       {p:.4f}  " + "  ".join(f"{mc_root[(D, p)]:.3f} ({analytic(D, p)[0]:.3f})" for D in range(1, 6)))
check(f"Monte Carlo: (sample, bulk qubit) pairs where the stabilizer group and the recursion disagree, over {nsamples} samples",
      mism, 0)
check("Monte Carlo: pairs with I(R_t : surviving) = 1 bit (partial recovery)", ione, 0)
check("Monte Carlo against the analytic probabilities: largest |z| over all (D, p, depth) points (honest bound 4.5)", zmax, 0.0, 4.5)
# Orientation H: the same per-sample agreement at D = 5.
mism_h = 0
for p in (0.15, P_C, 0.35):
    net = NETS[("H", 5, "b")]
    B = net["boundary"]
    M = (_nrng.random((30, len(B))) >= p).astype(np.uint8)
    I = np.array([recoverability(net, {B[j] for j in np.nonzero(M[i])[0]})[0] for i in range(30)])
    mism_h += int(((I == 2) != tree_recursion(M, 5)).sum())
check("orientation H, D = 5, 90 samples at p = 0.15, p_c, 0.35: pairs where the stabilizer group and the recursion disagree",
      mism_h, 0)
# Where do the D = 4 and D = 5 Monte Carlo root curves cross? (linear interpolation of their difference on the grid)
diffs = [(p, mc_root[(5, p)] - mc_root[(4, p)]) for p in P_GRID]
cross = None
for (p1, d1), (p2, d2) in zip(diffs, diffs[1:]):
    if d1 > 0 >= d2 and 0.1 <= p1 <= 0.4:
        cross = p1 + (p2 - p1) * d1 / (d1 - d2)
        break
print(f"     Monte Carlo crossing of the D = 4 and D = 5 root curves: p = {cross} (analytic crossing of every pair of depths: "
      f"p_c = {P_C:.6f}; Monte Carlo noise is about +-{math.sqrt(0.08 / NSAMP[5]):.3f} per point at D = 5)")
H4["monte_carlo_crossing_D4_D5"] = cross
H4["monte_carlo_summary"] = {"samples": nsamples, "pair_mismatches": mism, "partial_recoveries": ione, "max_abs_z": zmax}
J["H4"] = H4
RUNTIME["H4"] = time.perf_counter() - _t

# =====================================================================================================================
section("[H5] The two witnesses: the syndrome says that content exists, never what it is")
_t = time.perf_counter()
H5 = {}
TGT = {"X": stim.target_x, "Y": stim.target_y, "Z": stim.target_z}


def mpp_circuit(paulis):
    """Witness T (the trust half): measures each signed Pauli directly (stim MPP); returns the circuit and the signs."""
    c = stim.Circuit()
    for p in paulis:
        tg = []
        for q in p.pauli_indices():
            if tg:
                tg.append(stim.target_combiner())
            tg.append(TGT["_XYZ"[p[q]]](q))
        c.append("MPP", tg)
    return c


def hadamard_test_circuit(paulis, anc):
    """Witness I (the information half), coded independently: one ancilla, H, controlled Paulis, H, measure, reset."""
    c = stim.Circuit()
    gate = {1: "CX", 2: "CY", 3: "CZ"}
    for p in paulis:
        c.append("H", [anc])
        for q in p.pauli_indices():
            c.append(gate[p[q]], [anc, q])
        c.append("H", [anc])
        c.append("M", [anc])
        c.append("R", [anc])
    return c


def run_witnesses(sim, gens, cT, cI, chain):
    """Both witnesses read the syndrome. Witness T measures the generators g_i; witness I measures g_1, g_1 g_2, g_2 g_3, ...
    (a different basis of the same group) and decodes. Returns the two syndromes as 0/1 arrays."""
    m = len(gens)
    sim.do_circuit(cT)
    rT = np.array(sim.current_measurement_record()[-m:], dtype=np.int8) ^ np.array([g.sign == -1 for g in gens], np.int8)
    sim.do_circuit(cI)
    rI = np.array(sim.current_measurement_record()[-m:], dtype=np.int8) ^ np.array([c.sign == -1 for c in chain], np.int8)
    sI = np.cumsum(rI) % 2  # s_1 = r_1, s_i = r_i + s_(i-1)
    return rT, sI.astype(np.int8)


def expectation(inv, p):
    r = inv(p)
    xs, _ = r.to_numpy()
    return 0 if xs.any() else int(r.sign.real)


# ---- (i) at scale: D = 5, orientation A, 5120 boundary qubits, 1706 bulk contents, 3414 stabilizer generators ----------------
netS = NETS[("A", 5, "b")]
NQ = netS["nq"] + 1
ANC = netS["nq"]
refset = set(netS["ref"].values())
GEN = [to_stim(s, d, NQ) for s, d, kind, t in netS["gens"] if kind == "stab"]
LOGX, LOGZ = {}, {}
for s, d, kind, t in netS["gens"]:
    if kind in ("logX", "logZ"):
        dd = {q: c for q, c in d.items() if q not in refset}
        (LOGX if kind == "logX" else LOGZ)[t] = to_stim(s, dd, NQ)
CHAIN = [GEN[0]] + [GEN[i - 1] * GEN[i] for i in range(1, len(GEN))]
cT, cI = mpp_circuit(GEN), hadamard_test_circuit(CHAIN, ANC)
print(f"     code: {len(netS['boundary'])} boundary qubits, {len(GEN)} stabilizer generators, {len(LOGX)} logical qubits; "
      f"witness T: {len(GEN)} direct Pauli measurements; witness I: {len(CHAIN)} ancilla circuits on another basis")


def content_state(net, content, pairs):
    """Encode a bulk content: every bulk qubit in a cardinal state, then the given pairs turned into Bell pairs, then the tiles."""
    sim = stim.TableauSimulator(seed=11)
    sim.set_num_qubits(NQ)
    bulk = {t: (loc[0] if kind == "R" else loc[1]) for t, (kind, loc) in enumerate(net["ops"])}
    for t, q in bulk.items():
        prepare(sim, q, content[t])
    for t1, t2 in pairs:
        sim.cx(bulk[t1], bulk[t2])
    for kind, loc in net["ops"]:
        sim.do_tableau(TAB_ROOT if kind == "R" else TAB_CHILD[net["orient"]], loc[:5] if kind == "R" else loc[:4])
    return sim


def content_observables(content, pairs):
    """+1 observables of the encoded content: the cardinal axis of every unpaired bulk qubit, XX and ZZ of every Bell pair."""
    paired = {t for pr in pairs for t in pr}
    obs = []
    for t in range(netS["ntiles"]):
        if t in paired:
            continue
        c = content[t]
        P = LOGZ[t] if c < 2 else (LOGX[t] if c < 4 else 1j * LOGX[t] * LOGZ[t])
        obs.append(P if c % 2 == 0 else -P)
    for t1, t2 in pairs:
        obs += [LOGX[t1] * LOGX[t2], LOGZ[t1] * LOGZ[t2]]
    return obs


_crng = random.Random(5)
CONTENTS = []
for i in range(6):
    content = [_crng.randrange(6) for _ in range(netS["ntiles"])]
    pairs = []
    if i == 5:  # entangled content: 400 random bulk pairs, each in a Bell state (content qubits first set to |+>, partner |0>)
        tiles = list(range(netS["ntiles"]))
        _crng.shuffle(tiles)
        pairs = [(tiles[2 * k], tiles[2 * k + 1]) for k in range(400)]
        for t1, t2 in pairs:
            content[t1], content[t2] = 2, 0
    CONTENTS.append((content, pairs))
# error realizations, the same for every content
_erng = np.random.default_rng(99)
ERRORS = [("none", 0.0, stim.PauliString(NQ))]
for p in (0.0005, 0.002, 0.01):
    for r in range(2):
        e = stim.PauliString(NQ)
        for q in netS["boundary"]:
            if _erng.random() < p:
                e[q] = "XYZ"[_erng.integers(3)]
        ERRORS.append((f"p={p} #{r}", p, e))


def predicted_syndrome(e):
    return np.array([0 if e.commutes(g) else 1 for g in GEN], np.int8)


syn = {}
agree_TI, match_pred, intact_after_reads, n_obs = True, True, True, 0
for ci, (content, pairs) in enumerate(CONTENTS):
    base = content_state(netS, content, pairs)
    obs = content_observables(content, pairs)
    inv0 = base.current_inverse_tableau()
    intact_before = all(expectation(inv0, P) == 1 for P in obs)
    for name, p, e in ERRORS:
        sim = base.copy()
        sim.do_pauli_string(e)
        sT, sI = run_witnesses(sim, GEN, cT, cI, CHAIN)
        agree_TI &= bool((sT == sI).all())
        match_pred &= bool((sT == predicted_syndrome(e)).all())
        syn[(ci, name)] = sT
        if name == "none":
            inv1 = sim.current_inverse_tableau()
            intact_after_reads &= intact_before and all(expectation(inv1, P) == 1 for P in obs)
            n_obs += len(obs)
same_across_contents = all((syn[(ci, name)] == syn[(0, name)]).all() for ci in range(len(CONTENTS)) for name, _, _ in ERRORS)
zero_noiseless = all(not syn[(ci, "none")].any() for ci in range(len(CONTENTS)))
check_true(f"noiseless: both witnesses read the trivial syndrome on all {len(GEN)} generators for 6 contents (5 random "
           f"product contents, 1 with 400 bulk Bell pairs): the gate passes", zero_noiseless)
check_true(f"witness T (direct) and witness I (ancilla circuits, other basis) read the same syndrome in all "
           f"{len(CONTENTS) * len(ERRORS)} runs", agree_TI)
check_true(f"for every error realization ({len(ERRORS) - 1} noisy, p = 0.0005..0.01) the syndrome is identical for all 6 contents",
           same_across_contents)
check_true("the syndrome equals the commutation pattern of the error with the generators (independent symplectic prediction)",
           match_pred)
check_true(f"every content observable ({n_obs} in all) still reads +1 after both witnesses' full syndrome reads: fidelity 1",
           intact_after_reads)
refused = {name: int(syn[(0, name)].any()) for name, _, _ in ERRORS}
H5["at_scale"] = {"boundary_qubits": len(netS["boundary"]), "generators": len(GEN), "logical_qubits": len(LOGX),
                  "contents": len(CONTENTS), "error_realizations": [{"name": n, "p": p, "weight": e.weight,
                                                                     "syndrome_weight": int(syn[(0, n)].sum()),
                                                                     "gate_refuses": bool(refused[n])} for n, p, e in ERRORS]}
# Reading the content instead: the witnesses measure logical Z, then logical X, of a stratified sample of bulk qubits.
content, pairs = CONTENTS[0]
sim = content_state(netS, content, pairs)
depth = netS["depth"]
_srng = random.Random(8)
sample = [0] + [t for d in range(1, netS["D"] + 1) for t in sorted(_srng.sample([u for u in range(netS["ntiles"]) if depth[u] == d], min(20, 5 * 4 ** (d - 1))))]
for t in sample:
    sim.measure_observable(LOGZ[t])
    sim.measure_observable(LOGX[t])
inv2 = sim.current_inverse_tableau()
obs0 = content_observables(content, [])
fid = [(1 + expectation(inv2, obs0[t])) / 2 for t in sample]
untouched = [(1 + expectation(inv2, obs0[t])) / 2 for t in range(netS["ntiles"]) if t not in set(sample)]
check(f"mean content fidelity of {len(sample)} bulk qubits after the witnesses read logical Z then X (expected 1/2)",
      float(np.mean(fid)), 0.5, 0.12)
check("mean content fidelity of the other bulk qubits (reading one content leaves the others intact)", float(np.mean(untouched)), 1.0)
sT2, sI2 = run_witnesses(sim, GEN, cT, cI, CHAIN)
check_true("after the content reads, both witnesses still read the trivial syndrome: the gate cannot see that content was read",
           not sT2.any() and not sI2.any())
H5["content_read"] = {"qubits_read": len(sample), "mean_fidelity_read": float(np.mean(fid)),
                      "mean_fidelity_unread": float(np.mean(untouched)), "fidelity_by_content_axis": {
                          ax: float(np.mean([f for t, f in zip(sample, fid) if content[t] // 2 == k])) for k, ax in enumerate("ZXY")}}
print(f"     at scale: {time.perf_counter() - _t:.0f} s")

# ---- (ii) one tile: all 4^5 Pauli errors on the five physical qubits ---------------------------------------------------------
S5 = [stim.PauliString(w.replace("I", "_")) for w in STAB5]
XL5, ZL5 = stim.PauliString("XXXXX"), stim.PauliString("ZZZZZ")
CH5 = [S5[0]] + [S5[i - 1] * S5[i] for i in range(1, 4)]
cT5, cI5 = mpp_circuit(S5), hadamard_test_circuit(CH5, 5)
def tile_state(c):
    sim = stim.TableauSimulator(seed=3)
    sim.set_num_qubits(6)
    prepare(sim, 0, c)
    sim.do_tableau(TAB_ROOT, list(range(5)))
    return sim


def cardinal_logical(c):
    P = ZL5 if c < 2 else (XL5 if c < 4 else 1j * XL5 * ZL5)
    return P if c % 2 == 0 else -P


def syn5(e):
    return tuple(0 if e.commutes(s) else 1 for s in S5)


LOOKUP = {(0, 0, 0, 0): stim.PauliString(5)}
for q in range(5):
    for c in "XYZ":
        e = stim.PauliString(5)
        e[q] = c
        LOOKUP[syn5(e)] = e
check("distinct syndromes of the identity and the 15 single-qubit errors (a perfect code: all 16 syndromes used)", len(LOOKUP), 16)
BASE5 = [tile_state(c) for c in range(6)]
check_true("the root tableau encodes each of the 6 cardinal contents as the +1 eigenstate of its logical XXXXX / YYYYY-type / ZZZZZ observable",
           all(BASE5[c].peek_observable_expectation(cardinal_logical(c)) == 1 for c in range(6)))
agree5, indep5, cls_match, single_ok = True, True, True, True
n_ref, n_pass, n_harmless, n_logical = 0, 0, 0, 0
fail = {}
for w in itertools.product("_XYZ", repeat=5):
    e = stim.PauliString("".join(w))
    syns, fails = [], []
    for c in range(6):
        sim = BASE5[c].copy()
        sim.do_pauli_string(e)
        sT, sI = run_witnesses(sim, S5, cT5, cI5, CH5)
        agree5 &= bool((sT == sI).all())
        syns.append(tuple(int(v) for v in sT))
        sim.do_pauli_string(LOOKUP[syns[-1]])  # refuse-and-restore by lookup
        fails.append(sim.peek_observable_expectation(cardinal_logical(c)) != 1)
    indep5 &= len(set(syns)) == 1
    resid = e * LOOKUP[syns[0]]
    is_logical = not (resid.commutes(XL5) and resid.commutes(ZL5))
    cls_match &= any(fails) == is_logical
    fail["".join(w)] = is_logical
    if e.weight == 1:
        single_ok &= not any(fails) and syns[0] != (0, 0, 0, 0)
    if syns[0] != (0, 0, 0, 0):
        n_ref += 1
    else:
        n_pass += 1
        n_harmless += not is_logical
        n_logical += is_logical
check_true("all 1024 Pauli errors x 6 cardinal contents: witness T and witness I read the same syndrome", agree5)
check_true("for every error the syndrome is the same for all 6 contents (it depends on the error, never on the content)", indep5)
check("errors on which both witnesses refuse (nonzero syndrome)", n_ref, 960)
check("errors that pass the gate and are harmless (stabilizers, content intact)", n_harmless, 16)
check("errors that pass the gate and change the content (undetectable logical errors, weight >= 3)", n_logical, 48)
check_true("every one of the 15 single-qubit errors is refused by both and restored by lookup for all 6 contents", single_ok)
check_true("stim's content check after correction agrees with the symplectic classification (residual commutes with X_L, Z_L)",
           cls_match)
wt = {k: 0 for k in range(6)}
for w, f in fail.items():
    if not f:
        wt[5 - w.count("_")] += 1
check_true("weight distribution of correctable errors (0..5): 1, 15, 0, 60, 135, 45 (C s with C a coset leader, s a stabilizer)",
           [wt[k] for k in range(6)] == [1, 15, 0, 60, 135, 45])
# Dense checks with Haar-random (non-stabilizer) contents.
_hrng = np.random.default_rng(31)
SPROJ = [(np.eye(32) + pauli(w)) / 2 for w in STAB5]


def haar_qubit():
    v = _hrng.normal(size=2) + 1j * _hrng.normal(size=2)
    return v / np.linalg.norm(v)


def syndrome_projector(bits):
    P = np.eye(32, dtype=complex)
    for b, Pp in zip(bits, SPROJ):
        P = P @ (Pp if b == 0 else np.eye(32) - Pp)
    return P


ERR_DENSE = {w: pauli("".join("I" if c == "_" else c for c in w)) for w in fail}
pdep = 0.1
prob = {w: (pdep / 3) ** (5 - w.count("_")) * (1 - pdep) ** w.count("_") for w in fail}
SYN_PROJ = {b: syndrome_projector(b) for b in itertools.product((0, 1), repeat=4)}
dists, fids, readf = [], [], []
for _ in range(40):
    v = haar_qubit()
    psi = ENC @ v
    rho = sum(prob[w] * np.outer(ERR_DENSE[w] @ psi, (ERR_DENSE[w] @ psi).conj()) for w in fail)
    dists.append([float(np.trace(Pp @ rho).real) for Pp in SYN_PROJ.values()])
    for w, E in ERR_DENSE.items():
        if w.count("_") == 4:
            st = E @ psi
            b = tuple(int(round(float(np.vdot(st, (np.eye(32) - Pp) @ st).real))) for Pp in SPROJ)
            corr = ERR_DENSE["".join("_XYZ"[LOOKUP[b][q]] for q in range(5))]
            fids.append(abs(np.vdot(psi, corr @ st)) ** 2)
    # reading the content: projective logical Z then logical X, averaged exactly over outcomes
    ZLd, XLd = pauli("ZZZZZ"), pauli("XXXXX")
    rr = np.outer(psi, psi.conj())
    for L in (ZLd, XLd):
        Pp = (np.eye(32) + L) / 2
        rr = Pp @ rr @ Pp + (np.eye(32) - Pp) @ rr @ (np.eye(32) - Pp)
    readf.append(float(np.vdot(psi, rr @ psi).real))
dists = np.array(dists)
check("40 Haar-random contents under depolarizing noise p = 0.1: largest spread of the 16 syndrome probabilities across contents",
      float((dists.max(0) - dists.min(0)).max()), 0.0, 1e-12)
check("Haar-random contents: smallest fidelity after refuse-and-restore over 40 contents x 15 single-qubit errors", min(fids), 1.0, 1e-12)
check("Haar-random contents: content fidelity after the witnesses read logical Z then X, exact average over outcomes (all 40)",
      max(abs(f - 0.5) for f in readf) + 0.5, 0.5, 1e-12)


def p_fail_enum(p):
    return sum((p / 3) ** (5 - w.count("_")) * (1 - p) ** w.count("_") for w, f in fail.items() if f)


def p_fail_exact(p):
    """1 - P(correctable): N_w = 1, 15, 0, 60, 135, 45 correctable errors of weight w, each of probability (p/3)^w (1-p)^(5-w)."""
    return 1 - ((1 - p) ** 5 + 5 * p * (1 - p) ** 4 + 60 * (p / 3) ** 3 * (1 - p) ** 2 + 135 * (p / 3) ** 4 * (1 - p)
                + 45 * (p / 3) ** 5)


def p_fail_bound(p):
    """The closed form for any distance-3 code that corrects every weight-1 error and nothing else: 1 - (1-p)^5 - 5p(1-p)^4."""
    return 1 - (1 - p) ** 5 - 5 * p * (1 - p) ** 4


PGRID5 = [1e-4, 1e-3, 3e-3, 0.01, 0.03, 0.05, 0.1, 0.2, 0.3]
dev5 = max(abs(p_fail_enum(p) - p_fail_exact(p)) for p in np.linspace(0, 1, 201))
check("logical failure probability: enumeration of all 1024 errors vs the exact polynomial, max |diff| on 201 p", dev5, 0.0, 1e-13)
check("leading order: P_fail(p) / p^2 at p = 1e-4 (C(5,2) = 10 weight-2 error pairs, all fatal)", p_fail_enum(1e-4) / 1e-8, 10.0, 0.01)
lo, hi = 0.01, 0.5
for _ in range(80):
    mid = (lo + hi) / 2
    lo, hi = (mid, hi) if p_fail_enum(mid) < mid else (lo, mid)
PSEUDO = (lo + hi) / 2
print("     one tile, depolarizing noise p on each of the 5 qubits, lookup decoder:")
print("       p         P_fail exact   closed-form bound   bound - exact")
for p in PGRID5:
    print(f"       {p:<8.4g}  {p_fail_enum(p):.6e}   {p_fail_bound(p):.6e}      {p_fail_bound(p) - p_fail_enum(p):.3e}")
print(f"     pseudo-threshold (P_fail = p): p = {PSEUDO:.5f}")
H5["tile"] = {"refused": n_ref, "passed_harmless": n_harmless, "passed_logical": n_logical,
              "correctable_weight_distribution": [wt[k] for k in range(6)],
              "p_fail": {f"{p:g}": {"exact": p_fail_enum(p), "closed_form_bound": p_fail_bound(p)} for p in PGRID5},
              "pseudo_threshold": PSEUDO, "leading_coefficient": p_fail_enum(1e-4) / 1e-8,
              "exact_polynomial": "1 - [(1-p)^5 + 5p(1-p)^4 + (20/9)p^3(1-p)^2 + (5/3)p^4(1-p) + (5/27)p^5]"}
J["H5"] = H5
RUNTIME["H5"] = time.perf_counter() - _t

# =====================================================================================================================
section("[H6] Toric code on an L x L torus: topological entanglement entropy (Kitaev-Preskill and Levin-Wen)")
_t = time.perf_counter()


def toric(L):
    """Ground state of the toric code (Kitaev 2003): star X^4 and plaquette Z^4 on the 2 L^2 edges, plus the two
    non-contractible Z loops that fix one ground state. Qubit 2(yL+x) is the edge (x,y)-(x+1,y), 2(yL+x)+1 the edge (x,y)-(x,y+1)."""
    h = lambda x, y: 2 * ((y % L) * L + (x % L))  # noqa: E731
    v = lambda x, y: h(x, y) + 1  # noqa: E731
    gl = []
    for y in range(L):
        for x in range(L):
            gl.append([(h(x, y), 1), (h(x - 1, y), 1), (v(x, y), 1), (v(x, y - 1), 1)])
            gl.append([(h(x, y), 2), (h(x, y + 1), 2), (v(x, y), 2), (v(x + 1, y), 2)])
    gl.append([(h(x, 0), 2) for x in range(L)])
    gl.append([(v(0, y), 2) for y in range(L)])
    gl = [sorted(g) for g in gl]
    touch = {}
    for i, g in enumerate(gl):
        for q, _ in g:
            touch.setdefault(q, []).append(i)
    pos = np.zeros((2 * L * L, 2))
    for y in range(L):
        for x in range(L):
            pos[h(x, y)] = (x + 0.5, y)
            pos[v(x, y)] = (x, y + 0.5)
    return {"gl": gl, "touch": touch, "nq": 2 * L * L, "pos": pos, "L": L}


def geometry(tc):
    c = np.array([tc["L"] / 2 + 0.31, tc["L"] / 2 + 0.17])
    d = tc["pos"] - c
    return np.hypot(d[:, 0], d[:, 1]), np.arctan2(d[:, 1], d[:, 0]), d


def S_of(tc, mask):
    return entropy(tc, [int(q) for q in np.nonzero(mask)[0]])


def kitaev_preskill(tc, r):
    dist, ang, _ = geometry(tc)
    disk = dist < r
    sector = np.floor(((ang - 0.4) % (2 * np.pi)) / (2 * np.pi / 3)).astype(int)
    A, B, C = (disk & (sector == k) for k in range(3))
    s = S_of(tc, A) + S_of(tc, B) + S_of(tc, C) - S_of(tc, A | B) - S_of(tc, B | C) - S_of(tc, A | C) + S_of(tc, A | B | C)
    return -s, int(disk.sum()), S_of(tc, disk)


def levin_wen(tc, r_in, r_out):
    dist, _, d = geometry(tc)
    ann = (dist >= r_in) & (dist < r_out)
    g = 1.5 + 0.1 * r_in
    top = ann & (np.abs(d[:, 0]) < g) & (d[:, 1] > 0)
    bot = ann & (np.abs(d[:, 0]) < g) & (d[:, 1] < 0)
    S1, S2, S3, S4 = S_of(tc, ann), S_of(tc, ann & ~top), S_of(tc, ann & ~bot), S_of(tc, ann & ~top & ~bot)
    return -((S1 - S2) - (S3 - S4)) / 2, int(ann.sum())


# Dense check of the entropy formula on the 3 x 3 torus (18 qubits): stim's state vector of the same stabilizer group.
tc3 = toric(3)
st3 = [stim.PauliString("".join("_XZY"[dict(g).get(q, 0)] for q in range(18))) for g in tc3["gl"]]
psi3 = stim.Tableau.from_stabilizers(st3, allow_redundant=True).to_state_vector(endian="big")
_trng = random.Random(4)
dev3 = max(abs(entropy_dense(psi3, reg, 18) - entropy(tc3, reg)) for reg in
           [sorted(_trng.sample(range(18), _trng.randint(1, 9))) for _ in range(30)])
check("toric code 3x3: max |S_dense - S_stabilizer| over 30 random regions (bits)", dev3, 0.0, 1e-9)
H6 = {"kitaev_preskill": [], "levin_wen": []}
ranks_ok = True
for L in (8, 16, 24, 32, 40, 45):
    tc = toric(L)
    ranks_ok &= len(echelon(rows_for(tc["gl"], list(range(tc["nq"]))))) == tc["nq"]
    for r in (2, 3, 4, 6, 8, 11, 14, 18):
        if r <= L / 2 - 2:
            g, nq, Sd = kitaev_preskill(tc, r)
            H6["kitaev_preskill"].append({"L": L, "qubits": tc["nq"], "radius": r, "disk_qubits": nq, "S_disk": Sd, "gamma_bits": g})
    for r_in, r_out in ((2, 4.5), (3, 6.5), (4, 8.5), (6, 11.5), (8, 15.5), (10, 19.5)):
        if r_out <= L / 2 - 1.5:
            g, nq = levin_wen(tc, r_in, r_out)
            H6["levin_wen"].append({"L": L, "qubits": tc["nq"], "r_in": r_in, "r_out": r_out, "annulus_qubits": nq, "gamma_bits": g})
check_true("toric codes L = 8..45: 2L^2 + 2 generators of GF(2) rank 2L^2 (a pure state; 4050 qubits at L = 45)", ranks_ok)
kp = [e["gamma_bits"] for e in H6["kitaev_preskill"]]
lw = [e["gamma_bits"] for e in H6["levin_wen"]]
print("     Kitaev-Preskill gamma (bits): " + ", ".join(f"L={e['L']} r={e['radius']}: {e['gamma_bits']:g}" for e in H6["kitaev_preskill"]))
print("     Levin-Wen gamma (bits):       " + ", ".join(f"L={e['L']} {e['r_in']}-{e['r_out']}: {e['gamma_bits']:g}"
                                                   for e in H6["levin_wen"]))
check(f"Kitaev-Preskill: gamma for all {len(kp)} (L, radius) pairs, min (bits; ln 2 nats = 1 bit)", min(kp), 1.0)
check(f"Kitaev-Preskill: gamma for all {len(kp)} (L, radius) pairs, max (bits)", max(kp), 1.0)
check(f"Levin-Wen: gamma for all {len(lw)} (L, annulus) pairs, min (bits)", min(lw), 1.0)
check(f"Levin-Wen: gamma for all {len(lw)} (L, annulus) pairs, max (bits)", max(lw), 1.0)
J["H6"] = H6
RUNTIME["H6"] = time.perf_counter() - _t

# =====================================================================================================================
RUNTIME["total"] = time.perf_counter() - T_START
J["runtime_seconds_machine_dependent"] = RUNTIME
J["checks"] = {"passed": int(sum(results)), "total": len(results)}
os.makedirs(os.path.dirname(OUT), exist_ok=True)
with open(OUT, "w") as fh:
    json.dump(jsonable(J), fh, indent=1)
print(f"\nruntime {RUNTIME['total']:.0f} s; results written to {os.path.relpath(OUT, os.path.dirname(os.path.dirname(HERE)))}")
print(f"\n{sum(results)} of {len(results)} checks passed")
raise SystemExit(0 if all(results) else 1)
