"""The constructive assembly: DMP parts arranged as a holographic code, run numerically.

Read with docs/qg-verdict.md. Needs only numpy. Runs in about a minute. Every printed line is a check with its expected value.

The arrangement (section 2 of the verdict):
  - a part is one block of the five-qubit code [[5,1,3]] (Laflamme et al. 1996); the six-leg perfect tensor of that code
    (Pastawski, Yoshida, Harlow, Preskill 2015) is the tile of the network;
  - a layer is a rooted tree of tiles (Axiom 3: "every layer is a tree rooted there"): one root tile, five child tiles,
    twenty boundary legs; every tile has one bulk leg (the information that sits there);
  - the two halves are two independent witnesses that each read the stabilizer syndrome themselves (Axiom 2), the trust
    half and the information half; the gate passes only when both read the trivial syndrome (Axiom 1);
  - the content (the logical qubit) is never read by the gate: from trust only its existence (Axiom 3).
"""

import itertools
import numpy as np

rng = np.random.default_rng(20261027)

I2 = np.eye(2)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Z = np.diag([1.0, -1.0]).astype(complex)
Y = 1j * X @ Z


def kron(*ops):
    out = np.array([[1.0 + 0j]])
    for op in ops:
        out = np.kron(out, op)
    return out


def pauli(word):
    table = {"I": I2, "X": X, "Y": Y, "Z": Z}
    return kron(*[table[c] for c in word])


# The five-qubit code: stabilizers XZZXI and its cyclic shifts; logical X = XXXXX, logical Z = ZZZZZ.
STAB = ["XZZXI", "IXZZX", "XIXZZ", "ZXIXZ"]
S_OPS = [pauli(w) for w in STAB]
XL, ZL = pauli("XXXXX"), pauli("ZZZZZ")
P_CODE = np.eye(32, dtype=complex)
for s in S_OPS:
    P_CODE = P_CODE @ (np.eye(32) + s) / 2
zero = np.zeros(32, dtype=complex)
zero[0] = 1
L0 = P_CODE @ zero
L0 /= np.linalg.norm(L0)
L1 = XL @ L0
ENC = np.stack([L0, L1], axis=1)  # 32 x 2 isometry: logical qubit -> five physical qubits

# The six-leg perfect tensor T[b, q1..q5] = <q1..q5|ENC|b> / sqrt(2) (an absolutely maximally entangled state).
T = (ENC.T / np.sqrt(2)).reshape([2] * 6)


def entropy_bits(psi, keep, n):
    """Von Neumann entropy (bits) of the qubits in `keep` for a pure state psi on n qubits."""
    keep = list(keep)
    rest = [q for q in range(n) if q not in keep]
    m = np.transpose(psi.reshape([2] * n), keep + rest).reshape(2 ** len(keep), -1)
    sv = np.linalg.svd(m, compute_uv=False) ** 2
    sv = sv[sv > 1e-12]
    return float(-(sv * np.log2(sv)).sum())


def check(label, got, want, tol=1e-6):
    ok = abs(got - want) < tol
    print(f"{'OK  ' if ok else 'FAIL'} {label}: {got:.6f} (expected {want:.6f})")
    return ok


results = []

# ---------------------------------------------------------------------------------------------------------------------
print("\n[1] Perfect tensor: any three of the six legs are maximally entangled with the other three")
psi6 = T.reshape(-1)
results.append(check("norm of the six-leg state", np.linalg.norm(psi6), 1.0))
worst = min(entropy_bits(psi6, c, 6) for c in itertools.combinations(range(6), 3))
results.append(check("min over all 20 three-leg cuts of S (bits)", worst, 3.0))

# ---------------------------------------------------------------------------------------------------------------------
print("\n[2] A layer as a rooted tree of parts; Ryu-Takayanagi as the minimal cut through the tree")
# Root tile: leg 0 = root bulk, legs 1..5 = edges to children. Child k: leg 0 = edge from root, leg 1 = child bulk,
# legs 2..5 = four boundary qubits. Boundary qubits are ordered child 1 legs 2..5, child 2 legs 2..5, ... (a ring of 20).
# Wave function index order: [R, B0, B1..B5, boundary 0..19]; R is a reference purifying the root bulk.
ROOT_MAP = np.sqrt(2) * T  # as a map from leg 0 to legs 1..5, an isometry
CHILD_MAP = 2 * T  # as a map from legs 0,1 to legs 2..5, an isometry
results.append(check("root map is an isometry", np.linalg.norm(
    ROOT_MAP.reshape(2, 32).conj() @ ROOT_MAP.reshape(2, 32).T - np.eye(2)), 0.0))
results.append(check("child map is an isometry", np.linalg.norm(
    CHILD_MAP.reshape(4, 16).conj() @ CHILD_MAP.reshape(4, 16).T - np.eye(4)), 0.0))


def layer_state(root_bulk_entangled_with_reference):
    """Returns the pure state on [R] + 20 boundary qubits; child bulk legs are in |0> (a product bulk)."""
    if root_bulk_entangled_with_reference:
        rb = np.array([[1, 0], [0, 1]], dtype=complex) / np.sqrt(2)  # R x B0 Bell pair
    else:
        rb = np.array([[1, 0], [0, 0]], dtype=complex)  # R=|0>, B0=|0>
    # root: (R, B0) -> (R, e1..e5)
    st = np.einsum("rb,bjklmn->rjklmn", rb, ROOT_MAP)
    child = CHILD_MAP[:, 0]  # child bulk fixed to |0>: map edge -> four boundary qubits, shape (2, 2,2,2,2)
    st = np.einsum("rjklmn,jabcd,kefgh,liopq,mstuv,nwxyz->rabcdefghiopqstuvwxyz",
                   st, child, child, child, child, child)
    return st.reshape(-1)


psi = layer_state(root_bulk_entangled_with_reference=False)
N = 21  # R + 20 boundary qubits; R is in a product state here
results.append(check("norm of the layer state", np.linalg.norm(psi), 1.0))

# Minimal cut on the tree: nodes root, c1..c5; edges root-ck (one bit each), ck-boundary legs (one bit each).
def min_cut_bits(region):
    region = set(region)
    best = 10 ** 9
    for assign in itertools.product([0, 1], repeat=6):  # 1 = node on the region's side
        root, kids = assign[0], assign[1:]
        cut = sum(1 for k in range(5) if kids[k] != root)
        for k in range(5):
            for leg in range(4):
                q = 4 * k + leg
                cut += int((q in region) != bool(kids[k]))
        best = min(best, cut)
    return best


rt_ok = True
for length in range(1, 11):
    for start in range(0, 20, 3):
        region = [(start + i) % 20 for i in range(length)]
        s = entropy_bits(psi, [1 + q for q in region], N)
        rt_ok &= abs(s - min_cut_bits(region)) < 1e-6
print(f"{'OK  ' if rt_ok else 'FAIL'} S(A) equals the minimal cut through the tree for every contiguous boundary region tested")
results.append(rt_ok)

# ---------------------------------------------------------------------------------------------------------------------
print("\n[3] Majority within a layer: the root's information is recoverable from any 3 of the 5 child parts, from no 2")
psi_r = layer_state(root_bulk_entangled_with_reference=True)


def mutual_info_with_reference(kids):
    region = [1 + 4 * k + leg for k in kids for leg in range(4)]
    return entropy_bits(psi_r, [0], N) + entropy_bits(psi_r, region, N) - entropy_bits(psi_r, [0] + region, N)


results.append(check("max over all 10 pairs of children of I(R : pair) (bits), 0 = nothing of the content",
                     max(mutual_info_with_reference(c) for c in itertools.combinations(range(5), 2)), 0.0))
results.append(check("min over all 10 triples of children of I(R : triple) (bits), 2 = all of it",
                     min(mutual_info_with_reference(c) for c in itertools.combinations(range(5), 3)), 2.0))

# ---------------------------------------------------------------------------------------------------------------------
print("\n[4] The dual gate on one part: two independent witnesses read the syndrome, never the content")


def random_qubit():
    v = rng.normal(size=2) + 1j * rng.normal(size=2)
    return v / np.linalg.norm(v)


def read_syndrome(state):
    """A witness reads the four stabilizers itself (projective, live). Returns the syndrome and the post-read state."""
    bits = []
    for s in S_OPS:
        p_plus = (np.eye(32) + s) / 2
        prob = np.vdot(state, p_plus @ state).real
        bit = 0 if rng.random() < prob else 1
        proj = p_plus if bit == 0 else np.eye(32) - p_plus
        state = proj @ state
        state /= np.linalg.norm(state)
        bits.append(bit)
    return tuple(bits), state


fids, agree = [], True
for _ in range(200):
    v = random_qubit()
    part = ENC @ v
    syn_trust, part = read_syndrome(part)  # the trust half
    syn_info, part = read_syndrome(part)  # the information half, on its own, after
    agree &= syn_trust == syn_info == (0, 0, 0, 0)
    fids.append(abs(np.vdot(ENC @ v, part)) ** 2)
print(f"{'OK  ' if agree else 'FAIL'} both witnesses read the same trivial syndrome on 200 random contents: the gate passes")
results.append(agree)
results.append(check("content fidelity after both full syndrome reads (mean of 200)", float(np.mean(fids)), 1.0))

# A single-qubit fault: both witnesses read the same nonzero syndrome, the gate refuses, the balance restores.
corrections = {}
for q in range(5):
    for name in "XYZ":
        word = "I" * q + name + "I" * (4 - q)
        e = pauli(word)
        syn = tuple(0 if np.vdot(L0, e.conj().T @ s @ e @ L0).real > 0 else 1 for s in S_OPS)
        corrections[syn] = e
results.append(check("distinct syndromes for the 15 single-qubit faults", len(corrections), 15, tol=0.5))
fids = []
for _ in range(200):
    v = random_qubit()
    q = rng.integers(5)
    name = "XYZ"[rng.integers(3)]
    fault = pauli("I" * q + name + "I" * (4 - q))
    part = fault @ (ENC @ v)
    syn_t, part = read_syndrome(part)
    syn_i, part = read_syndrome(part)
    assert syn_t == syn_i != (0, 0, 0, 0)  # both refuse, for the same reason
    part = corrections[syn_t] @ part  # restored by evidence (Axiom 1's balance)
    fids.append(abs(np.vdot(ENC @ v, part)) ** 2)
results.append(check("content fidelity after refuse-and-restore on 200 random single faults", float(np.mean(fids)), 1.0))

# The same two witnesses cannot both read the content in full: reading Z then X (non-commuting) costs half the content.
fids = []
for _ in range(4000):
    v = random_qubit()
    part = ENC @ v
    for logical in (ZL, XL):
        p_plus = (np.eye(32) + logical) / 2
        prob = np.vdot(part, p_plus @ part).real
        proj = p_plus if rng.random() < prob else np.eye(32) - p_plus
        part = proj @ part
        part /= np.linalg.norm(part)
    fids.append(abs(np.vdot(ENC @ v, part)) ** 2)
results.append(check("content fidelity when the two witnesses read the content itself (Haar mean, ~0.5)",
                     float(np.mean(fids)), 0.5, tol=0.02))

# ---------------------------------------------------------------------------------------------------------------------
print("\n[5] Isolated gate, entangled content, at the same time: CHSH on two parts")
bell = (np.kron(L0, L0) + np.kron(L1, L1)) / np.sqrt(2)
A0, A1 = ZL, XL
B0, B1 = (ZL + XL) / np.sqrt(2), (ZL - XL) / np.sqrt(2)


def corr(a, b, state):
    return np.vdot(state, np.kron(a, b) @ state).real


S_content = corr(A0, B0, bell) + corr(A0, B1, bell) + corr(A1, B0, bell) - corr(A1, B1, bell)
results.append(check("CHSH of the two parts' content", S_content, 2 * np.sqrt(2)))
# The gate's verdicts are the stabilizer readings: deterministic +1 on both parts, so their CHSH is the constant 2.
verdicts = [corr(sa, sb, bell) for sa in S_OPS[:2] for sb in S_OPS[:2]]
S_gate = verdicts[0] + verdicts[1] + verdicts[2] - verdicts[3]
results.append(check("CHSH of the two gates' verdicts (classical bound)", S_gate, 2.0))
# The gate reads first, the content is untouched: stabilizers commute with the logical operators.
comm = max(np.linalg.norm(s @ L - L @ s) for s in S_OPS for L in (XL, ZL))
results.append(check("largest commutator between a syndrome read and a content observable", comm, 0.0))

# ---------------------------------------------------------------------------------------------------------------------
print("\n[6] Geometry held by both halves cannot entangle (the Bose / Marletto-Vedral logic, LOCC)")
# A and B are two masses in superposition; M is the mediator (the geometry). A couples to M, M couples to B, then A
# uncouples. If M stays coherent, A and B end entangled. If M is held in full by two witnesses (broadcast, hence read
# in its pointer basis, Barnum et al. 1996), it is dephased, and A and B stay separable.
plus = np.array([1, 1], dtype=complex) / np.sqrt(2)
CNOT_AM = np.zeros((8, 8))
for a, m, b in itertools.product([0, 1], repeat=3):
    CNOT_AM[(a << 2) | ((m ^ a) << 1) | b, (a << 2) | (m << 1) | b] = 1
CZ_MB = np.diag([(-1) ** (m & b) for a, m, b in itertools.product([0, 1], repeat=3)]).astype(complex)


def negativity_AB(rho):
    r = rho.reshape(2, 2, 2, 2, 2, 2)  # a m b, a' m' b'
    r_ab = np.einsum("ambcmd->abcd", r).reshape(4, 4)  # trace out M
    pt = r_ab.reshape(2, 2, 2, 2).transpose(0, 3, 2, 1).reshape(4, 4)  # partial transpose on B
    ev = np.linalg.eigvalsh(pt)
    return float(-ev[ev < 0].sum())


psi0 = np.kron(np.kron(plus, np.array([1, 0])), plus)
rho = np.outer(psi0, psi0.conj())
U = CNOT_AM @ CZ_MB @ CNOT_AM
rho_coherent = U @ rho @ U.conj().T
results.append(check("A-B negativity, mediator coherent (quantum geometry)", negativity_AB(rho_coherent), 0.5))
dephase = [np.diag([1 if ((i >> 1) & 1) == m else 0 for i in range(8)]).astype(complex) for m in (0, 1)]
rho1 = CNOT_AM @ rho @ CNOT_AM.T
rho1 = sum(p @ rho1 @ p for p in dephase)  # both halves hold the mediator: it is read
rho1 = CNOT_AM @ CZ_MB @ rho1 @ CZ_MB.conj().T @ CNOT_AM.T
results.append(check("A-B negativity, mediator held by both halves (classical geometry)", negativity_AB(rho1), 0.0))

print(f"\n{sum(bool(r) for r in results)} of {len(results)} checks passed")
raise SystemExit(0 if all(results) else 1)
