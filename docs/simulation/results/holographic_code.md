# The holographic code of Section 9 at scale

Workstream H of *GUID v6: Our theory as simulated*. Script: `docs/simulation/holographic_code.py` (77 of 77 checks pass). Every
number below is in `holographic_code.json` next to this file. Entropies and mutual informations are in bits.

## In one paragraph

The one-layer assembly of Section 9 (`docs/qg-verdict/assembly.py`, 25 qubits) was scaled to a five-level tree: 1706 tiles,
5120 boundary qubits, and 6826 qubits once every bulk qubit has its own reference. The state is handled exactly as a stabilizer
state. Five results:

- **Ryu-Takayanagi on the tree (H2).** With every bulk leg open (setting b), S(A) equals the minimal cut for every region tested.
  That is all 2^20 regions at D = 1, and 2.2 million region-network cases in all. With every bulk leg fixed to |0> (setting a),
  S(A) never exceeds the cut. In assembly.py's orientation it equals the cut for every contiguous interval at every depth. It
  falls below the cut for many non-contiguous regions, and, in the HaPPY orientation, for 10 to 32 % of intervals. Every
  exception has a non-empty residual region.
- **Entanglement wedge (H3).** In 13.2 million (region, bulk qubit) pairs, I(R_t : A) is always 0 or 2 bits. Four predictions of
  the wedge agree in every pair: the exact value from the stabilizer group, the greedy wedge, the tree recursion and the min-cut
  prediction.
- **Erasure threshold (H4).** The root survives random erasure below p_c = (5 − √13)/6 = 0.232408. That is the fixed point of
  the exact recursion a → 4a³ − 3a⁴. At p_c every depth has the same recovery probability, 0.914162. Monte Carlo over 97 900
  samples agrees with the recursion sample by sample.
- **The two witnesses (H5).** At D = 5 the syndrome is the same bit for bit for every content, and two independently coded
  extractions agree. Reading the content instead halves its fidelity. On one tile the exact logical failure probability is
  10p² − O(p³), below the generic distance-3 closed form.
- **Toric code (H6).** The topological entanglement entropy is γ = 1 bit (ln 2) for every region size and every torus up to
  L = 45 (4050 qubits), by both Kitaev-Preskill and Levin-Wen.

## Construction

| | |
|---|---|
| tile | six-leg perfect tensor T[b, q1..q5] = ⟨q1..q5\|ENC\|b⟩/√2 of [[5,1,3]] (stabilizers XZZXI and cyclic shifts; X_L = XXXXX, Z_L = ZZZZZ); b is the logical leg |
| root | bulk = logical leg b; legs q1..q5 to five children |
| child, orientation A (main; assembly.py's CHILD_MAP = 2T) | parent edge on the logical leg b, bulk on physical leg q1, children on q2..q5 |
| child, orientation H (HaPPY reading of "each tile's logical leg the information sitting there") | bulk on b, parent edge on q1, children on q2..q5 |
| boundary | the leaves' child legs in ring order; depth D gives 5·4^D qubits and 1 + 5(4^D − 1)/3 tiles |
| setting (a) | every bulk leg in \|0⟩: a pure state on the boundary |
| setting (b) | every bulk leg maximally entangled with its own reference qubit R_t |

| D | boundary qubits | tiles = bulk qubits | qubits, setting (b) |
|---|---|---|---|
| 1 | 20 | 6 | 26 |
| 2 | 80 | 26 | 106 |
| 3 | 320 | 106 | 426 |
| 4 | 1280 | 426 | 1706 |
| 5 | 5120 | 1706 | 6826 |

## Method

- Each tile map is an isometry that is Clifford: U\|v,0..0⟩ = V\|v⟩. It is synthesised as a stim Tableau from the dense tensor
  (signed Pauli images found by search) and checked against the dense map (deviation 1.2·10⁻⁸, complex64).
- The network's stabilizer generators are pushed through the tree tile by tile as sparse signed Pauli strings. They are n
  independent generators on n qubits (GF(2) rank). Every generator, sign included, is a +1 stabilizer of stim's own composition
  of the same tableaux: C†PC is a +Z string. This holds for all 20 networks (D = 1..5, both settings, both orientations).
- Entropies come from S(A) = rank(G restricted to A) − \|A\| [Fattal et al. 2004; Hamma, Ionicioiu, Zanardi 2005]. The rank is
  computed by exact GF(2) elimination on Python integers, using only the generators that touch A. At D = 1 the stabilizer
  entropies equal dense state-vector entropies (independent numpy contraction) to 2·10⁻¹⁵. The same holds for a 3×3 toric code.
- All 2^20 regions at D = 1 are handled at once by enumerating the stabilizer group and running a zeta transform over subsets.
- I(R_t : A) for all 1706 bulk qubits at once: one elimination with columns ordered [complement \| references \| A]. The
  vectors whose leading bit lies in the reference block span V, the reference part of the stabilizers on A ∪ R. Then
  I(R_t : A) = dim(V ∩ ⟨X_Rt, Z_Rt⟩).
- The minimal cut is a tree dynamic program with unit capacity per leg, plus a rerooting pass. In setting (b) a bulk leg is cut
  when its tile lies on A's side. The greedy wedge [Pastawski et al. 2015] absorbs a tile when ≥ 3 of its 5 non-bulk legs lie in
  the region, and is run to its fixed point.

## H2. Ryu-Takayanagi on the tree

Each cell gives the number of regions with S(A) ≠ min cut, out of the regions tested, then the share of exceptions and the
largest deficit min cut − S(A) in bits.

| D | regions | orientation A, setting (a) | orientation H, setting (a) | setting (b), both orientations |
|---|---|---|---|---|
| 1 | all 2^20 subsets | 139052/1048576 (13.3 %, max 2) | 139052/1048576 (13.3 %, max 2) | 0 of 2097152 |
| 1 | all 380 intervals | 0/380 | 40/380 (10.5 %, max 1) | 0 of 760 |
| 2 | 3200 intervals (all) | 0/3200 | 695/3200 (21.7 %, max 2) | 0 of 6400 |
| 2 | 1500 random subsets | 112 (7.5 %, max 3) | 117 (7.8 %, max 2) | 0 of 3000 |
| 2 | 1500 unions of 2–6 intervals | 27 (1.8 %, max 1) | 125 (8.3 %, max 2) | 0 of 3000 |
| 3 | 24320 intervals | 0/24320 | 5531 (22.7 %, max 3) | 0 of 48640 |
| 3 | 1500 random subsets | 282 (18.8 %, max 6) | 293 (19.5 %, max 6) | 0 of 3000 |
| 3 | 1500 unions | 39 (2.6 %, max 2) | 355 (23.7 %, max 4) | 0 of 3000 |
| 4 | 9216 intervals | 0/9216 | 2697 (29.3 %, max 4) | 0 of 18432 |
| 4 | 1500 random subsets | 446 (29.7 %, max 18) | 441 (29.4 %, max 18) | 0 of 3000 |
| 4 | 1500 unions | 28 (1.9 %, max 2) | 600 (40.0 %, max 4) | 0 of 3000 |
| 5 | 5312 intervals | 0/5312 | 1701 (32.0 %, max 4) | 0 of 10624 |
| 5 | 1500 random subsets | 559 (37.3 %, max 53) | 573 (38.2 %, max 51) | 0 of 3000 |
| 5 | 1500 unions | 22 (1.5 %, max 1) | 826 (55.1 %, max 4) | 0 of 3000 |

How the regions were chosen:

- **Intervals.** At D = 2 these are all intervals up to half the ring. At D = 3 they are all starts with lengths 1–64, plus 40
  starts with lengths 65–160. At D = 4 and 5 they are 48 and 32 random starts, with lengths 1–128 and then every 8th (D = 4) or
  64th (D = 5) length up to n/2.
- **Random subsets.** Half have log-uniform sizes from 1 to n/2, half have uniform sizes from 1 to n − 1.
- **Unions.** Each is a union of 2–6 intervals with log-uniform lengths.

**Characterisation of the exceptions.** All of them are in setting (a).

1. S(A) is never above the cut (4 303 160 region-network cases).
2. Every exception has a non-empty residual region, the set of tiles in neither greedy wedge (of A, or of its boundary
   complement). In setting (b) this greedy wedge is the exact entanglement wedge, as shown in H3. Where the residual region is
   empty, S(A) equals the cut, in every case tested. The deficit never exceeded ⌊(residual tiles)/2⌋. This is an observed bound,
   not a proof.
3. The exceptions are not only degenerate cuts: 95 735 of them have a unique minimal cut.
4. Mechanism, checked on one tile in H0. A tile with its bulk fixed is a five-leg AME state. Its parent edge shares exactly 1 bit
   with every pair of its child legs. With the bulk leg open (six-leg perfect tensor) the edge shares 0 bits with every pair. A
   tile whose legs the cut splits 2|2 therefore passes one classical bit around the cut. Whether those bits line up between
   tiles depends on how the tile is oriented. In orientation A they never line up for an interval. In orientation H they do,
   for 10–32 % of intervals. One such interval (qubits 0..9 at D = 1, S = 3, cut 4) is confirmed by dense contraction alone.
5. HaPPY's argument that RT holds for connected regions rests on the greedy cuts from both sides meeting, that is, on there being no residual region [Pastawski et al. 2015]. On
   this tree with fixed bulk legs they need not meet.

**For the paper.** assembly.py's check A2 extends to D = 5 in assembly.py's orientation: zero interval exceptions in 42 428
intervals. The paper's text puts the bulk on the logical leg ("each tile's logical leg the information sitting there"). That is
orientation H, where RT fails for intervals. The statement "S(R) = minimal cut" is exact in both orientations only with the
bulk legs open (setting b).

## H3. Entanglement-wedge reconstruction (setting b)

- **Regions compared.** All 2^20 regions × 6 bulk qubits × 2 orientations at D = 1. At D = 2..5, 11 region sizes × 6–12 starts,
  both as intervals and as random subsets, in both orientations. In all, 13 243 616 (region, bulk qubit) pairs.
- **No partial recovery.** I(R_t : A) is 0 or 2 bits in every pair; 1 bit never occurs.
- **Four predictions agree.** These are I(R_t : A) = 2 from the stabilizer group, the greedy wedge, the tree recursion of H4 and
  the min-cut prediction I_cut = 1 + mc(A) − mc(A ∪ R_t). The min-cut prediction never ties (I_cut = 1 occurs 0 times).

Recoverable fraction of bulk qubits at D = 5, orientation A, by depth (rows; 0 = root) and region size \|A\|/n (columns). The
intervals use 6 starts per size; the random subsets use 6 samples per size.

Intervals:

| depth | 0.05 | 0.10 | 0.20 | 0.30 | 0.40 | 0.50 | 0.60 | 0.70 | 0.80 | 0.90 | 0.95 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 0.00 | 0.00 | 0.00 | 0.00 | 0.00 | 0.17 | 0.67 | 1.00 | 1.00 | 1.00 | 1.00 |
| 1 | 0.00 | 0.00 | 0.03 | 0.27 | 0.37 | 0.43 | 0.53 | 0.77 | 0.83 | 0.97 | 1.00 |
| 2 | 0.03 | 0.10 | 0.17 | 0.28 | 0.39 | 0.50 | 0.58 | 0.69 | 0.79 | 0.89 | 0.95 |
| 3 | 0.05 | 0.10 | 0.19 | 0.29 | 0.40 | 0.50 | 0.60 | 0.70 | 0.80 | 0.90 | 0.95 |
| 4 | 0.05 | 0.10 | 0.20 | 0.30 | 0.40 | 0.50 | 0.60 | 0.70 | 0.80 | 0.90 | 0.95 |
| 5 | 0.05 | 0.10 | 0.20 | 0.30 | 0.40 | 0.50 | 0.60 | 0.70 | 0.80 | 0.90 | 0.95 |

Random subsets (the same as erasure at p = 1 − \|A\|/n):

| depth | 0.05 | 0.10 | 0.20 | 0.30 | 0.40 | 0.50 | 0.60 | 0.70 | 0.80 | 0.90 | 0.95 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 0.00 | 0.00 | 0.00 | 0.00 | 0.00 | 0.00 | 0.00 | 0.00 | 1.00 | 1.00 | 1.00 |
| 1 | 0.00 | 0.00 | 0.00 | 0.00 | 0.00 | 0.00 | 0.00 | 0.03 | 1.00 | 1.00 | 1.00 |
| 2 | 0.00 | 0.00 | 0.00 | 0.00 | 0.00 | 0.00 | 0.00 | 0.21 | 1.00 | 1.00 | 1.00 |
| 3 | 0.00 | 0.00 | 0.00 | 0.00 | 0.00 | 0.00 | 0.07 | 0.44 | 0.99 | 1.00 | 1.00 |
| 4 | 0.00 | 0.00 | 0.00 | 0.01 | 0.02 | 0.09 | 0.28 | 0.64 | 0.97 | 1.00 | 1.00 |
| 5 | 0.00 | 0.00 | 0.03 | 0.09 | 0.18 | 0.32 | 0.52 | 0.75 | 0.96 | 1.00 | 1.00 |

An interval holds the bulk geometrically: a deep qubit is in its wedge when its own subtree lies inside the interval. The root
needs more than half the ring. A random subset holds nothing until about 77 % of the boundary survives, and then holds
everything. This is the erasure threshold of H4.

## H4. Erasure threshold of the hierarchy

**The recursion.** This is derived for setting (b), where every bulk qubit is unknown.

1. Look at an edge from below, as the input of the isometry formed by its subtree.
   - If ≥ 3 of the tile's 4 child legs are available, the ≤ 3 remaining legs (the edge, the bulk leg and at most one child) are
     recovered from them. Any 3 legs of a perfect tensor are a unitary image of the other 3.
   - If ≤ 2 are available, I(edge : those legs) = 1 + 2 − 3 = 0, because any 3 legs of a perfect tensor are maximally mixed.
     The channel from the edge to that part of the boundary is then constant, and its region carries nothing about anything
     above it.
   - So by induction every edge is either fully available or fully decoupled. This is the all-or-nothing property, and it is the
     reason I = 1 never occurs.
2. The same argument applies from above, using the parent tile's other legs.
3. A bulk qubit is recoverable when ≥ 3 of its tile's 5 non-bulk legs are available. For the root, that means ≥ 3 of its 5
   children.

With independent erasure at rate p:

- a₀ = 1 − p, and a_h = P(Bin(4, a_{h−1}) ≥ 3) = 4a³ − 3a⁴. This is the chance that the edge above a tile of height h is
  available from below.
- P_root(D) = P(Bin(5, a_D) ≥ 3).
- For a bulk qubit at depth d ≥ 1, with β the chance its parent edge is available from above:
  - β₁ = P(Bin(4, a_D) ≥ 3);
  - β_d = β_{d−1}·P(Bin(3, a_{D−d+1}) ≥ 2) + (1 − β_{d−1})·a_{D−d+1}³;
  - P_d = β_d·P(Bin(4, a_{D−d}) ≥ 2) + (1 − β_d)·P(Bin(4, a_{D−d}) ≥ 3).

**The threshold.** The map has fixed points a = 0, a = 1 and a* = (1 + √13)/6 = 0.767592. The slope there is
f′(a*) = 12a*²(1 − a*) = 1.6432 > 1, so a* is unstable. This gives:

- **p_c = 1 − a* = (5 − √13)/6 = 0.232408.**
- At p = p_c, a_h = a* and β_d = a* at every level. Every bulk qubit at every depth, for every D, is then recovered with the same
  probability P(Bin(5, a*) ≥ 3) = 0.914162. The curves for different D cross exactly at p_c, and the window around p_c narrows
  as 1.643^(−D).
- For comparison, a plain concatenation of the five-qubit code (no bulk qubit in the inner tiles) has fixed point 1/2, so
  p_c = 1/2, the no-cloning bound of the erasure channel [Bennett, DiVincenzo, Smolin 1997]. Each tile's own bulk qubit costs the
  hierarchy more than half of that margin.

**Checks.**

- D = 1 is exact: the recovery polynomial from all 2^20 erasure patterns equals the recursion to 3·10⁻¹³.
- Monte Carlo used 4000, 2000, 1500, 1000 and 400 samples per p at D = 1..5 (97 900 samples in all). The stabilizer group and
  the recursion agree in every (sample, bulk qubit) pair, with 0 mismatches.
- The Monte Carlo fractions agree with the analytic probabilities at every (D, p, depth) point (largest \|z\| = 2.55).
- Orientation H at D = 5 gives the same sample-by-sample agreement.

Root recoverable, Monte Carlo (analytic in brackets):

| p | D=1 | D=2 | D=3 | D=4 | D=5 |
|---|---|---|---|---|---|
| 0.05 | 1.000 (1.000) | 1.000 (1.000) | 1.000 (1.000) | 1.000 (1.000) | 1.000 (1.000) |
| 0.10 | 0.999 (0.999) | 1.000 (1.000) | 1.000 (1.000) | 1.000 (1.000) | 1.000 (1.000) |
| 0.15 | 0.987 (0.989) | 0.997 (0.998) | 1.000 (1.000) | 1.000 (1.000) | 1.000 (1.000) |
| 0.20 | 0.958 (0.956) | 0.969 (0.972) | 0.989 (0.988) | 1.000 (0.998) | 1.000 (1.000) |
| 0.22 | 0.938 (0.932) | 0.946 (0.942) | 0.958 (0.956) | 0.976 (0.973) | 0.990 (0.988) |
| 0.232408 | 0.913 (0.914) | 0.909 (0.914) | 0.907 (0.914) | 0.905 (0.914) | 0.912 (0.914) |
| 0.25 | 0.886 (0.884) | 0.854 (0.860) | 0.821 (0.815) | 0.704 (0.722) | 0.517 (0.529) |
| 0.28 | 0.818 (0.819) | 0.713 (0.730) | 0.549 (0.546) | 0.247 (0.236) | 0.020 (0.017) |
| 0.32 | 0.698 (0.710) | 0.488 (0.507) | 0.181 (0.187) | 0.012 (0.008) | 0.000 (0.000) |
| 0.40 | 0.464 (0.454) | 0.135 (0.133) | 0.002 (0.003) | 0.000 (0.000) | 0.000 (0.000) |
| 0.50 | 0.178 (0.180) | 0.009 (0.007) | 0.000 (0.000) | 0.000 (0.000) | 0.000 (0.000) |

Per depth at D = 5, Monte Carlo/analytic for depths 0..5:

- p = 0.25: 0.517/0.529, 0.609/0.627, 0.727/0.733, 0.801/0.805, 0.848/0.850, 0.875/0.876.
- p = p_c: all six depths 0.912–0.916, against 0.914.

The Monte Carlo curves for D = 4 and D = 5 cross at p = 0.2331, against the analytic 0.2324, with noise of about ±0.014 per
point.

## H5. The two witnesses

**At scale.** This uses D = 5 in orientation A: 5120 boundary qubits, 3414 stabilizer generators and 1706 logical qubits.

- **Contents.** Six were tested: five random product contents, with each bulk qubit in a random one of the 6 cardinal states,
  and one with 400 bulk Bell pairs.
- **The two witnesses.** Witness T measures the 3414 generators directly (stim MPP). Witness I is coded independently. It
  measures the different basis g₁, g₁g₂, g₂g₃, … with one ancilla (H, controlled Paulis, H, measure, reset), then decodes.
- **Noiseless.** Both witnesses read the trivial syndrome for all six contents, so the gate passes. All 10 236 content
  observables still read +1 after both full reads, so the fidelity is 1.
- **Noisy.** There were six Pauli-noise realizations at p = 0.0005, 0.002 and 0.01, with error weights 1–58 and syndrome
  weights 9–184.
  - The syndrome is identical bit for bit across all six contents.
  - Witness T and witness I agree in all 42 runs.
  - Both equal the error's commutation pattern with the generators, computed separately. Both refuse.
- **Reading the content.** The witnesses then read the content itself, measuring logical Z and then X, on 86 bulk qubits spread
  over all depths.
  - The fidelity of those qubits drops to 0.517 (expected ½).
  - The other 1620 qubits keep fidelity 1.
  - Both witnesses still read the trivial syndrome afterwards. The gate cannot see that the content was read.

**One tile, all 4^5 = 1024 Pauli errors × 6 cardinal contents.**

- **Syndromes.** The 15 single-qubit errors give 15 distinct syndromes; the code is perfect, using all 16. The two witnesses
  agree on every error, and every syndrome is independent of the content.
- **The gate.** It refuses 960 errors. It passes 64: 16 are harmless (stabilizers) and 48 are undetectable logical errors, all of
  weight ≥ 3.
- **Correction.** Lookup correction restores every single-qubit error for every content. Stim's content check and the symplectic
  classification agree. Correctable errors by weight 0..5 number 1, 15, 0, 60, 135 and 45, which is 256 = 16 coset leaders × 16
  stabilizers.
- **Haar-random contents (dense).** Under depolarizing noise at p = 0.1, the 16 syndrome probabilities are the same for 40
  contents to 3·10⁻¹⁵. Refuse-and-restore has fidelity 1. Reading logical Z and then X gives fidelity exactly ½ for every
  content.

Logical failure probability per tile, depolarizing rate p per qubit, lookup decoder. The exact value is
P_fail = 1 − [(1−p)⁵ + 5p(1−p)⁴ + (20/9)p³(1−p)² + (5/3)p⁴(1−p) + (5/27)p⁵]. Enumeration matches it to 1.3·10⁻¹⁴. The closed form
for a distance-3 code that corrects exactly the weight-1 errors is 1 − (1−p)⁵ − 5p(1−p)⁴.

| p | P_fail (exact) | closed form | closed form − exact |
|---|---|---|---|
| 1e-4 | 9.99778e-08 | 9.99800e-08 | 2.2e-12 |
| 1e-3 | 9.97780e-06 | 9.98001e-06 | 2.2e-09 |
| 0.01 | 9.77955e-04 | 9.80150e-04 | 2.2e-06 |
| 0.03 | 8.41428e-03 | 8.47205e-03 | 5.8e-05 |
| 0.05 | 2.23319e-02 | 2.25925e-02 | 2.6e-04 |
| 0.1 | 7.95081e-02 | 8.14600e-02 | 2.0e-03 |
| 0.2 | 0.249150 | 0.262720 | 1.4e-02 |
| 0.3 | 0.432480 | 0.471780 | 3.9e-02 |

The leading term is 10p², one for each of the C(5,2) weight-2 pairs, all of which are fatal. The difference is O(p³) and comes
from the weight-3, 4 and 5 errors that equal a correctable error times a stabilizer. The pseudo-threshold, where P_fail = p, is
p = 0.13763.

## H6. Toric code

The toric code ground state [Kitaev 2003] is built on L × L tori for L = 8, 16, 24, 32, 40 and 45 (up to 4050 qubits). The
generators are the stars, the plaquettes and two non-contractible Z loops, with GF(2) rank 2L² (a pure state). Regions are sets
of edges whose midpoints lie in a shape centred at a generic point (L/2 + 0.31, L/2 + 0.17).

| construction | regions | γ (bits) |
|---|---|---|
| Kitaev-Preskill: −γ = S_A + S_B + S_C − S_AB − S_BC − S_CA + S_ABC; a disk of radius r split into three 120° sectors | 33 (L, r) pairs, r = 2..18, disks up to 2042 qubits | 1 in every case |
| Levin-Wen: −2γ = (S₁ − S₂) − (S₃ − S₄); 1 = annulus r_in..r_out, 2 and 3 = annulus with a top or bottom gap, 4 = both gaps | 20 (L, annulus) pairs, from 2–4.5 to 10–19.5, annuli up to 1762 qubits | 1 in every case |

γ = 1 bit = ln 2, the known value for Z₂ topological order [Kitaev, Preskill 2006; Levin, Wen 2006]. It is independent of
region size and of L. The entropies themselves grow with the boundary; for example S = 101 bits for the r = 18 disk at L = 45.

## Caveats

- **What is simulated.**
  - These are kinematics on a fixed background, like Section 9. There is no dynamics and no superposition of geometries.
  - All states are stabilizer states. At scale the contents are cardinal or Bell (stabilizer) states; non-stabilizer
    (Haar-random) contents are tested only on one tile, densely.
  - The noise models are Pauli noise and erasure. Syndrome extraction is noiseless; the noise acts on the data before both
    witnesses read it.
- **RT in setting (a).** The setting-(a) RT results depend on orientation. The ⌊residual/2⌋ bound on the deficit is observed
  on 4.3 million cases, not proved. The intervals at D = 4 and 5 and the random subsets are samples, not exhaustive. D = 1 is
  exhaustive.
- **The erasure recursion.** It is exact for setting (b), where every bulk qubit is unknown, and was verified sample by sample.
  It is not a statement about setting (a). Monte Carlo fractions carry binomial noise; the per-sample agreement does not.
- **Runtime.** Runtimes are for this machine (4 shared cores, one BLAS thread) and are not results. The full script ran in about
  503 s with peak memory 1.4 GB: H2 99 s, H4 376 s, everything else under 15 s. Two runs gave identical JSON apart from the
  runtime field.
- **The tree is not space.** It is a tree, which is not our space (Section 9, "The tree is not our space").

## Reproduce

```
cd /home/user/gravity
python3 docs/simulation/holographic_code.py     # numpy, stim 1.16; prints 77 checks; writes results/holographic_code.json
```

## References

Each reference is marked "verified" if its bibliographic data was checked by web search for this work, or "standard, not
re-checked" if not.

- S. Aaronson, D. Gottesman, Improved simulation of stabilizer circuits, Phys. Rev. A 70, 052328 (2004), arXiv:quant-ph/0406196. *Verified.*
- A. Almheiri, X. Dong, D. Harlow, Bulk locality and quantum error correction in AdS/CFT, JHEP 04 (2015) 163, arXiv:1411.7041. *Verified.*
- C. H. Bennett, D. P. DiVincenzo, J. A. Smolin, Capacities of quantum erasure channels, Phys. Rev. Lett. 78, 3217 (1997), arXiv:quant-ph/9701015. *Verified.*
- C. H. Bennett, D. P. DiVincenzo, J. A. Smolin, W. K. Wootters, Mixed-state entanglement and quantum error correction, Phys. Rev. A 54, 3824 (1996), arXiv:quant-ph/9604024. *Verified.*
- R. Cleve, D. Gottesman, H.-K. Lo, How to share a quantum secret, Phys. Rev. Lett. 83, 648 (1999), arXiv:quant-ph/9901025. *Verified.*
- X. Dong, D. Harlow, A. C. Wall, Reconstruction of bulk operators within the entanglement wedge in gauge-gravity duality, Phys. Rev. Lett. 117, 021601 (2016), arXiv:1601.05416. *Verified.*
- D. Fattal, T. S. Cubitt, Y. Yamamoto, S. Bravyi, I. L. Chuang, Entanglement in the stabilizer formalism, arXiv:quant-ph/0406168 (2004). *Verified* (preprint; journal version not checked).
- C. Gidney, Stim: a fast stabilizer circuit simulator, Quantum 5, 497 (2021), arXiv:2103.02202. *Verified.*
- A. Hamma, R. Ionicioiu, P. Zanardi, Bipartite entanglement and entropic boundary law in lattice spin systems, Phys. Rev. A 71, 022315 (2005), arXiv:quant-ph/0409073. *Verified.*
- D. Harlow, The Ryu-Takayanagi formula from quantum error correction, Commun. Math. Phys. 354, 865 (2017), arXiv:1607.03901. *Verified.*
- A. Yu. Kitaev, Fault-tolerant quantum computation by anyons, Ann. Phys. 303, 2 (2003), arXiv:quant-ph/9707021. *Verified.*
- A. Kitaev, J. Preskill, Topological entanglement entropy, Phys. Rev. Lett. 96, 110404 (2006), arXiv:hep-th/0510092. *Verified.*
- R. Laflamme, C. Miquel, J. P. Paz, W. H. Zurek, Perfect quantum error correcting code, Phys. Rev. Lett. 77, 198 (1996), arXiv:quant-ph/9602019. *Verified.*
- M. Levin, X.-G. Wen, Detecting topological order in a ground state wave function, Phys. Rev. Lett. 96, 110405 (2006), arXiv:cond-mat/0510613. *Verified.* The combination (S₁ − S₂) − (S₃ − S₄) = −2 log D was checked by search; the region labels are as implemented above.
- F. Pastawski, B. Yoshida, D. Harlow, J. Preskill, Holographic quantum error-correcting codes: toy models for the bulk/boundary correspondence, JHEP 06 (2015) 149, arXiv:1503.06237. *Verified.*
- S. Ryu, T. Takayanagi, Holographic derivation of entanglement entropy from AdS/CFT, Phys. Rev. Lett. 96, 181602 (2006), arXiv:hep-th/0603001. *Verified.*
