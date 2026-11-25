# NP vs coNP: the crossing cost for lifted formulas, and what a constant-width version would need

Status: 2026-11-23. Exploratory round with Lean. **Nothing here proves a lower bound or NP vs coNP.** The lower bound for
lifted formulas is a theorem of others (Garg, Goos, Kamath, Sokolov), used as a named hypothesis. What is proved here is
the tie: how that theorem fills the `CrossingCost` slot of the ledger, and the exact statement a constant-size-gadget
version would have to meet.

Files: `ProofPhase/Proof/Lifting.lean`, `ProofPhase/Proof/LiftingNP.lean` (Lean, standard axioms only, no sorry),
`lifting-axioms.sh` / `lifting-axioms.log`, `np_lifting_check.py` / `np_lifting_check.log`.

Status marks as in `OPEN-STEPS-DMP.md`, plus **read** (the source text was read in this round, so it is not merely
recalled).

---

## 0. In plain words

**The idea.** The ledger's NP column asks for a *crossing cost*: a strong proof system should pay a price at each
restriction step, so refutations are exponentially long. Earlier rounds found that a one-boundary step is lossless (a
cutting-planes line names a crossing for free) and that every cutting-planes refutation of a formula with a fractional
solution must contain a rounding of a combination of two lines. So the price, if any, is paid at a two-line step.

**What lifting is.** Lifting is a known theorem with exactly that two-party shape. Take a formula `F`. Replace each
variable by a small gadget whose value depends on two halves, one held by each party. Alone, one half tells you (almost)
nothing about the variable. The theorem: if `F` needs resolution width `w`, then every cutting-planes refutation of the
lifted formula has at least `n^(c w)` lines. Resolution width is something the ledger already understands; the theorem
turns it into a cutting-planes size bound.

**What is new in this round.**
1. The theorem is read exactly (section 1): the proof-system model, the gadget (Index, polynomial size), and the bound.
2. In Lean (section 2): the composition `F o g` as a CNF, with a proof that it is the right formula; the statement of the
   theorem as the named hypothesis `LiftCP` (and `GGKS` for the Index gadget); and the instance: under it, `CrossingCost`
   and `np_instance` hold for every lifted width-hard formula, with `theta * b` of order `w log n`. So the NP column is
   inhabited by a class where the step is a theorem from others' work plus our tie.
3. A Lean theorem, unconditional, that every lifted formula still meets the creative pair: the lifting does not remove
   the rounding step, it prices it.
4. The exact Lean statement a constant-gadget version would have to meet (`LiftCPConst`), and the gadget-free one
   (`WidthToCP`).
5. Brute force on tiny cases: the composition is correct, the all-1/2 point lifts, each half alone hides the variables
   (for XOR from both sides, for Index from the pointer side only).

**What it does not do.** It covers cutting planes on formulas of the special form `F o g` with a polynomially large gadget.
It says nothing about unlifted constant-width formulas (random 3-CNF), nothing about Frege, and nothing about NP vs coNP
itself. Two honest cautions about the instance:
- A `CrossingCost` chain is, up to constants in the exponent, the same thing as an exponential size bound
  (`crossingCost_of_size` below). So "inhabited" means "an exponential lower bound is available", not "a new structural
  picture of where the cost sits". The structural picture is in the proof of lifting (section 1.4), not in the Lean chain.
- Hiding is not enough for lifting. XOR hides perfectly and is a bad lifting gadget (section 5).

---

## 1. The lifting theorem, read

Source (**read**): A. Garg, M. Goos, P. Kamath, D. Sokolov, *Monotone circuit lower bounds from resolution*, STOC 2018,
Theory of Computing 16 (2020). The text read in this round is the ECCC report of November 2017 (the version
before the journal's "discussion of applications"): Sections 2, 3, 8, 9. The journal version was **not** read; its
theorem numbers and constants should be audited before the paper cites exact numbers.

### 1.1 The proof-system model

Search problems and dags. A search problem is a relation `S` in `I x O`. An `F`-dag solving `S` is a directed acyclic graph
of fan-out at most 2 whose nodes carry functions from a family `F`, with a root `f = 1`, non-leaves whose feasible set is
contained in the union of the children's, and leaves labelled by outputs. Size is the number of nodes. In the bottom-up
(proof) reading: a refutation of a CNF is a dag whose lines are functions of the family, root `0`, each node implied by
its two children, leaves clauses of the formula.
- **Resolution** is the family of conjunctions (negations of clauses); `w(S)` is the least width of a conjunction-dag;
  for a CNF search problem it is the resolution width of Ben-Sasson and Wigderson.
- **Cutting planes** is the family of linear threshold functions with arbitrary real coefficients: `sum a_i x_i > a_{n+1}`.
  Dags over it are *semantic* (each node follows semantically from its children), so the model contains every syntactic
  cutting-planes refutation of any coefficient size. These are called triangle-dags: a threshold function is a "triangle"
  `{(x, y) : a(x) < b(y)}` in the bipartition.
- **Communication.** Rectangle-dags are dag-like protocols; any `F_c`-dag (lines computed by communication-`c` protocols)
  is simulated by a rectangle-dag with a `2^c` blow-up.

### 1.2 The gadget and its size

The index gadget `Ind_m : [m] x {0,1}^m -> {0,1}`, `(x, y) -> y_x`: Alice holds a pointer `x`, Bob a table `y`. For `n`
variables: `g^n(x, y) = (g(x_1, y_1), ..., g(x_n, y_n))`, and the lifted search problem `S o g^n` has Alice holding
`x in [m]^n`, Bob `y in ({0,1}^m)^n`, the goal being any `o in S(g^n(x, y))`.

**Gadget size in the theorem: `m = n^delta` for a large enough constant `delta`.** The text itself calls this a
disadvantage ("stemming from the large gadget size `m = poly(n)`"): with width `Theta(n)` the lifted formula has `N`
variables and the bound is only `exp(N^eps)`, and it states it as "an important open problem to develop a lifting theory
for gadgets of size `m = O(1)`", which would give the optimal `2^(Omega(N))`.

### 1.3 The bound

**Theorem 1** (rectangle-dags) and **Theorem 2** (triangle-dags, so cutting planes), verbatim in substance:
for any search problem `S` in `{0,1}^n x O`, with `m = n^delta`,

    tri-dag(S o Ind_m^n) = n^(Theta(w(S))).

The upper bound is the general simulation (a conjunction-dag of width `w` has at most `n^(O(w))` conjunctions); the lower
bound is the theorem. For `S = S_F` the CNF search problem of an unsatisfiable `F`, `w(S)` is the resolution width and
`tri-dag` of the lifted problem lower-bounds the cutting-planes refutation size of the CNF `F'` that encodes the
composition.

**The CNF, as the source builds it (Section 8, read).** With `x` written as an `m`-bit string of Hamming weight one, a
`k`-CNF `F` gives a `2k`-CNF contradiction `F'` on `O(m n)` variables (a total version needs extra width-3 clauses). With
`x` written as a `log m`-bit string the certificate complexity is `k (log m + 1)`. So **the lifted formula has constant width
`2k`** in the first encoding. What is not constant is the gadget (`m = n^delta`) and so the number of variables
`N = n^(1 + delta)`. This corrects a sentence of `OPEN-STEPS-DMP.md` 3(c) ("a lifted 3-CNF has width about 3 x gadget
size"): that holds only for the full-certificate encoding that `Lifting.lean` uses.

### 1.4 Why it is the project's picture (reading)

The proof goes through the *query* side: from a rectangle- or triangle-dag of size `s` for `S o g^n` it extracts a
conjunction-dag (resolution) for `S` of width `O(log s / log n)`. The "costly lines" of the cutting-planes refutation are
the ones whose rectangles are not structured, and what they must carry is a wide conjunction of `F`. So the crossing is
paid in the resolution width of `F`, through the gadget's hiding: a structured rectangle fixes few blocks, an unstructured
one is pseudorandom on the rest. In the project's words: the pair `(Alice's half, Bob's half)` is the handshake; one half
alone sees nothing (check 3 below); the cost is at the shared root.

### 1.5 Later gadget-size improvements

| source | what | status |
|---|---|---|
| Mertz and Pitassi, *Lifting: as easy as 1,2,3*, ECCC 2020 (first version) | simplified proof via the sunflower lemma; Index gadget `m = n^(1+eps)` for any `eps > 0`; `m = Theta(n log n)` for a weaker lifting factor; dag-like lifting (Section 5) with the same improvements (their footnote 5); "extends to the real communication setting" | **read** (intro, Sections 1, 4, 5) |
| Lovett, Meka, Mertz, Pitassi, Zhang, *Lifting with sunflowers*, ITCS 2022 | same tradeoff, `O~(n log^2 n)` at one end, `n^(1+eps)` at the other (as described in Mertz-Pitassi) | recalled via Mertz-Pitassi; not read directly |
| Goos, Koroth, Mertz, Pitassi, *Automating cutting planes is NP-hard*, STOC 2020 | dag-like lifting with multi-output gadgets, measure block-width; the authors write that they "do not know how to do this with only two parties" | reported by a reading assistant, not verified |
| Beame and Koroth, ITCS 2023 | a disperser-type conjecture of Lovett et al. for Index fails for gadget size below about `log N`; "dream range" is constant size; a positive result for Index of size 4 and up only for a restricted protocol class (one player sends parities) | abstract-level, not verified |
| Chattopadhyay, Mande, Sanyal, Sherif, ITCS 2023 (parity decision trees, stifling) | constant-size gadgets (Index on a 1-bit pointer, 3 bits) lift tree-like **resolution over parities** size, not cutting planes, not dag-like; "reducing the gadget size to a constant is an important open problem" | abstract-level, not verified |

**What is known about constant-size gadgets for cutting planes (as far as found):** nothing positive. Every dag-like
cutting-planes lifting theorem found needs a gadget of size at least `n^(1+eps)` (Index) or a multi-output gadget; both
the original authors and Beame-Koroth name constant size as open. The search was limited (one pass over abstracts and
the two papers read); **a newer result may exist** (to be checked before the paper says "open").

---

## 2. The Lean part

All in `ProofPhase.Proof.Lifting`. `#print axioms`: propext, Classical.choice, Quot.sound only, on all 52 declarations
(`lifting-axioms.log`); no sorry, admit, native_decide or axiom.

### 2.1 The composition (`Lifting.lean`)

| declaration | content | status |
|---|---|---|
| `Gadget`, `LV`, `certClause`, `comp` | a gadget on bit blocks; the CNF `F o g` (one clause per clause of `F` and per choice of block values falsifying its literals) | definition |
| `comp_falsified_iff` | an assignment falsifies a clause of `F o g` iff the decoded assignment falsifies a clause of `F` | **Lean** |
| `comp_unsat`, `unsat_of_comp_unsat` | `F o g` unsatisfiable iff `F` is (gadget taking both values) | **Lean** |
| `card_comp_le`, `two_le_card_comp`, `card_LV` | width at most `k (a + b)`; at least 2; `n (a + b)` variables | **Lean** |
| `CPR`, `CPRefutes`, `CPR.toCPD` | cutting-planes derivation with all lines in a finite set `P` (size `P.card`); it is a `CPD` | definition, **Lean** |
| `holds_clauseLine`, `clauseLine_unit`, `half_satisfies_cnfAx` | clause as a line; the all-1/2 point satisfies every axiom of a CNF with clauses of width at least 2 | **Lean** |
| `lifted_needs_pair` | for every `F` without empty clause and every gadget with a bit on each side: every cutting-planes refutation of `F o g` contains a rounding of a combination of at least two lines (`refutation_needs_pair` applied to the lifted formula) | **Lean**, unconditional |
| `xorGadget`, `indGadget`, `AliceBalanced`, `BobBalanced`, `xor_balanced`, `ind1_aliceBalanced`, `ind1_not_bobBalanced` | hiding: XOR hides against both parties; Index (checked for a 1-bit pointer) against the pointer holder only | **Lean** (small cases by `decide`) |

Note on the definition: the clauses use the full block value `(x, y)` as certificate, so width is `k (a + b)`. The source's
smaller certificates give the same unsatisfiable formula with narrower clauses; the lower bound transfers by the one
reduction "a falsified clause names a falsified clause of `F`" (`comp_falsified_iff` is exactly that statement). This
transfer, and "syntactic cutting planes is a triangle-dag of the same size", are the two steps **not formalised**.

### 2.2 The hypothesis and the instance (`LiftingNP.lean`)

- **`LiftCP gad c n0`** (external). For every CNF `F` on `n >= n0` variables without empty clause with resolution width
  above `w` (`not WD F w empty`), every cutting-planes refutation `P` of `F o (gad n)` satisfies
  `exp (c (w + 1) log n) <= P.card`.
- **`GGKS`** (external, named): `LiftCP` for the Index family with pointer length `ceil(log2 (n^delta))`, for some constant
  `delta` and `c > 0`, from some `n0`. Reading of the source: Theorems 1 and 2 with `m = n^delta`; Lean takes
  `m = 2^ceil(log2 (n^delta))`, between `n^delta` and `2 n^delta` (power of two so that the pointer is a bit string). That a
  slightly larger Index gadget does no better for the adversary is standard (set the extra pointer values and table entries
  aside) but is a reading step, flagged.
- **`crossingCost_of_size`** (Lean): if every refutation has at least `2^b` lines, `CrossingCost Refutes (1/2) b`
  (halve the line set `b` times). With `np_instance` this shows `CrossingCost` is, up to constants in the exponent,
  exactly an exponential size bound (`size_of_crossingCost_half` is the other direction).
- **`lifted_crossingCost`, `lifted_np_instance`** (Lean, from `LiftCP`): every `b` with `b log 2 <= c (w + 1) log n` is a
  number of steps; `np_instance` then gives `exp (b/2) <= P.card`.
- **`lifted_theta_b`** (Lean, from `LiftCP`): the largest such `b` has `theta b = b/2 >= c (w + 1) log n / (2 log 2) - 1/2`.
  So `theta b` is of order `w log n`, as asked.
- **`lifted_pair_and_cost`** (Lean): both facts at once: every refutation of the lifted formula has `>= exp (theta b)` lines
  and contains the creative pair.

**Reading of the result.** The NP column of the ledger is inhabited by the class "`F o g` with `F` width-hard and `g` an
Index gadget of polynomial size", under the hypothesis `GGKS`. The step is a theorem of others plus our tie. The ledger's
`CrossingCost` is the same hypothesis in chain form; the content is the size bound.

### 2.3 The interface of a constant-width version

Three statements, all in `LiftingNP.lean`; none is proved, and `LiftCPConst` for a fixed gadget is the open one.

1. **`LiftCPConst G c`**: one fixed gadget `G` (sizes `a`, `b` constants). For every CNF `F` without empty clause with
   resolution width above `w`, every cutting-planes refutation of `F o G` has at least `exp (c (w + 1))` lines. This is
   `LiftCP` with `log n` removed. `constGadget_interface` (Lean) shows its shape: a `k`-CNF `F` gives a lifted formula of
   width at most `k (a + b)` (constant) on `n (a + b)` variables (linear), and the bound is `exp (Omega (w))`, so
   `exp (Omega (N))` for linear width: the "optimal" bound of the source's Section 8. `constGadget_crossingCost`: the same
   in ledger form, with `b = floor (c (w + 1) / log 2)`.
2. **`WidthToCP K c`**: the gadget-free version for a class `K`: every formula of `K` without empty clause and with
   width above `w` has all cutting-planes refutations of size at least `exp (c (w + 1))`. `widthToCP_crossingCost`: ledger
   form. **For `K` = all CNFs it is false** (pigeonhole formulas have width linear in the number of variables and
   polynomial-size cutting-planes refutations; Cook, Coullard, Turan 1987, recalled), so any gadget-free statement must
   restrict the class. The project's question is `K` = random 3-CNF at the threshold density.
3. **The relation** (reading, not formalised): a gadget `G` in which one party's input alone fixes the output makes
   `F o G` a copy of `F` plus dummy variables, so `LiftCPConst G c` would give `WidthToCP` for all CNFs, which is false.
   So the gadget must hide; section 5 says why hiding is not sufficient.

---

## 3. The brute-force checks (`np_lifting_check.py`, `np_lifting_check.log`)

Standard-library Python, exact rational arithmetic, about one minute. Formulas: pigeonhole 3 into 2 (6 variables, 9
clauses of width 2, resolution width 2) and Tseitin on `K_4` with one odd charge (6 edge variables, 16 clauses of width 3,
resolution width 4), each composed with the 2-bit XOR gadget (12 bits) and the Index gadget on a 1-bit pointer and 2-bit
table (18 bits). All as expected (`all checks as expected: True`).

| check | result [numerical] |
|---|---|
| 1. the composition is right (`comp_falsified_iff`): over all `2^12` (XOR) and `2^18` (Index) assignments, a lifted clause is falsified iff the decoded assignment falsifies a clause of `F`; the lifted formula is unsatisfiable | 0 mismatches, all four cases |
| 2. the all-1/2 point: satisfies every clause inequality of `F` (least value 1 for pigeonhole, 3/2 for Tseitin) and of `F o g` (least value 2 and 3 for XOR, 3 and 9/2 for Index); the multilinear XOR at `(1/2, 1/2)` is `1/2`, so the point of `F` lifts to the point of `F o XOR`. So `refutation_needs_pair` applies to the lifted formula | holds |
| 2'. control: `F = {x, not x}` (width 1): `F`'s all-1/2 point **fails** (value 1/2), the lifted formula's point holds (width 2, value 1) | as expected |
| 3. hiding, under the uniform distribution on all lifted assignments: the decoded `z` given Alice's half alone, and given Bob's half alone | **XOR: exactly uniform on all `2^6` values from both sides** (deviation 0). **Index: exactly uniform given the pointer holder's half; given the table holder's half it is not** (deviation 1/2: a table of all zeros fixes the output) |

Two readings:
- The all-1/2 point lifts, but the lift is almost free: every lifted clause has width at least 2, so the point holds
  whatever `F` does (control). So `lifted_needs_pair` carries no information about `F`'s own linear relaxation; it says the
  lifted formula has the same two-line step as any formula with a fractional point, and the price of that step is what
  lifting supplies.
- The lossless one-boundary encoder (the project's `c = 0`) is exactly the XOR case. In Index it holds from the pointer
  side only. "One party alone sees nothing" is therefore exact for XOR and one-sided for Index (uniform only on average over
  tables). The lifting proof uses the pseudorandomness of large *sets* of tables, not the single table.

---

## 4. What `CrossingCost` is, after this

`crossingCost_of_size` and `np_instance` together say: a `CrossingCost` with parameters `(theta, b)` yields
`|P| >= exp (theta b)`, and an exponential size bound `2^b` yields a `CrossingCost` with `theta = 1/2` and `b` steps. So
the ledger's NP slot is equivalent, up to constants in the exponent, to "every refutation is exponentially long". This is
not a defect (the ledger's job is to record the cost as a sum of per-step prices), but it means the Lean chain adds no
evidence beyond the size bound. Where the evidence for a per-step price would sit: in the extraction in the lifting proof
(section 1.4), which turns a short refutation into a narrow resolution refutation of `F`. A structural `CrossingCost`
witness (costly lines tracked step by step along restrictions) would have to be built from that extraction. Not done.

---

## 5. The gap, plainly

**What lifting does not cover.**

1. **Constant-width random 3-CNF without a gadget** (the project's interface question). Lifting produces cutting-planes
   hardness only for formulas of the special form `F o g`; a random 3-CNF is not of that form, and no step of lifting
   transfers to it. A cutting-planes size lower bound for random 3-CNF at constant density is, as far as I recall,
   **open** (the known cutting-planes lower bounds are for specific formulas and for random `k`-CNF with `k` of order
   `log n`; recalled, in-project in `CP-DUALITY.md`). The Lean interface for it is `WidthToCP K c` with `K` = that
   class; it is not implied by `LiftCP`, and not by `LiftCPConst` either (those are about `F o G`).
2. **A constant-size gadget.** `LiftCPConst G c` is the statement needed for a lifted formula to have constant width and
   `exp (Omega (N))` hardness. Open for cutting planes (section 1.5). Even a positive result would give hardness of
   `F o G` for gadget-composed `F`, still not of unlifted formulas.
3. **Frege.** Lifting theorems apply to systems whose *lines* have efficient communication protocols. A Frege line is an
   arbitrary formula; a formula of size `O(n)` such as Equality (`and_i (x_i = y_i)`) has deterministic communication
   complexity `Omega(n)` for the natural split. So no cheap-protocol property holds, and no lifting statement for Frege
   follows from this route. Feasible interpolation also fails for Frege under cryptographic assumptions (Krajicek and
   Pudlak; Bonet, Pitassi, Raz; recalled).
4. **NP vs coNP.** Cutting planes is one proof system. NP vs coNP needs every proof system (Cook and Reckhow).

**Hiding is not enough (reading, classical fact).** XOR hides perfectly (section 3, check 3) yet is the wrong gadget for
resolution-width lifting: `PARITY_n o XOR` has deterministic communication complexity 2 (each side sends the parity of its
bits), while the decision-tree depth of `PARITY_n` is `n`. The query model that matches XOR is the parity decision
tree, not the decision tree (compare the stifling paper of section 1.5). So the one-boundary encoder being lossless (`c = 0`) is necessary for a gadget but not what makes
lifting work; what is needed in addition is that large sets of one party's inputs are pseudorandom for the other (Index with
`m = n^(1+eps)`), which is where the gadget size comes from.

**Not claimed.** No bound on any unlifted formula; no cutting-planes lower bound beyond the hypothesis; no statement
about Frege or about NP vs coNP.

---

## 6. Status table

| item | status |
|---|---|
| lifting theorem for `F o Ind_m`, `m = n^delta`: `tri-dag(S o Ind_m^n) = n^(Theta(w(S)))` (GGKS Theorems 1, 2) | **external, read** (ECCC version; journal version not read) |
| Index gadget `n^(1+eps)` for deterministic and dag-like lifting | **external, read** (Mertz-Pitassi 2020) |
| constant-size gadget for dag-like cutting-planes lifting | **open** (named open by the authors; newer results not excluded) |
| the lifted CNF has constant width `2k` (Hamming-weight pointer) | **read** (GGKS Section 8) |
| `comp_falsified_iff`, `comp_unsat`, widths, `lifted_needs_pair` | **Lean** |
| `crossingCost_of_size`, `size_of_crossingCost_half` | **Lean** |
| `LiftCP`, `GGKS` (the hypothesis) | **external**, named; two reductions (clause to solution, syntactic to semantic dag) not formalised |
| `lifted_crossingCost`, `lifted_np_instance`, `lifted_theta_b`, `lifted_pair_and_cost` (the instance) | **Lean**, conditional on `LiftCP` |
| `LiftCPConst`, `WidthToCP` (the interfaces), `constGadget_interface`, `constGadget_crossingCost`, `widthToCP_crossingCost` | statements and ledger forms **Lean**; the hypotheses **open** (`WidthToCP` for all CNFs is **false**, pigeonhole, classical) |
| composition correct, all-1/2 point lifts, XOR hides from both sides, Index from the pointer side only, on pigeonhole 3 into 2 and Tseitin `K_4` | **numerical** (exact) |
| XOR hides but does not lift decision trees (`PARITY o XOR`) | **classical** |
| unlifted constant-width random 3-CNF; Frege; NP vs coNP | **open**; not covered |

## 7. Corrections for earlier notes

- `OPEN-STEPS-DMP.md` 3(c): the lifted 3-CNF has constant width `2k` in the source's Hamming-weight encoding (section 1.3);
  the non-constant quantity is the number of variables `n^(1+delta)`, not the width. The conclusion (lifting does not give
  constant-size gadgets) stands. The gadget is polynomial, `n^delta`, in the original theorem, `n^(1+eps)` in Mertz-Pitassi.
- `OPEN-STEPS-DMP.md` 3(b): "the gadget is a handshake ... one party alone sees a uniformly random value" is exact for XOR
  and for the pointer side of Index only (section 3, check 3).

## 8. Literature

- A. Garg, M. Goos, P. Kamath, D. Sokolov, Monotone circuit lower bounds from resolution, STOC 2018; Theory of Computing 16
  (2020). ECCC report of November 2017 read; journal version not read.
- I. Mertz, T. Pitassi, Lifting: as easy as 1,2,3, ECCC 2020 (first version read, introduction and Sections 1, 4, 5).
- S. Lovett, R. Meka, I. Mertz, T. Pitassi, J. Zhang, Lifting with sunflowers, ITCS 2022 (not read directly).
- M. Goos, S. Koroth, I. Mertz, T. Pitassi, Automating cutting planes is NP-hard, STOC 2020 (reported, not verified).
- P. Beame, S. Koroth, On disperser/lifting properties of the Index and Inner-Product functions, ITCS 2023 (abstract level).
- A. Chattopadhyay, N. Mande, S. Sanyal, S. Sherif, Lifting to parity decision trees via stifling, ITCS 2023 (abstract level).
- S. de Rezende, J. Goos, R. Robere, Proofs, circuits, and communication, SIGACT News 2022 (survey; Theorem 3.7 states the
  GGKS lifting of resolution width to monotone circuits and cutting planes; abstract level).
- W. Cook, C. Coullard, G. Turan, On the complexity of cutting-plane proofs, 1987 (recalled).
- E. Ben-Sasson, A. Wigderson, Short proofs are narrow (2001); J. Krajicek, P. Pudlak, A. Bonet, T. Pitassi, R. Raz
  (feasible interpolation and its failure; recalled, in-project in `CP-DUALITY.md`).
