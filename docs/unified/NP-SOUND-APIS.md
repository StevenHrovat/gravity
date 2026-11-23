# NP vs coNP: sound APIs, the composition-theorem landscape, and the route to a constant-size gadget

Status: 2026-11-23. Exploratory round, with a small Lean file. **Nothing here proves a lower bound or NP vs coNP.** The lower
bounds quoted are theorems of others, read from the sources (marked). What is proved here (Lean): the exact interface a
constant-gadget lifting proof has to deliver, and that this interface is equivalent to `LiftCPConst`.

Files: `ProofPhase/Proof/SoundAPI.lean` (Lean, standard axioms only, no sorry), `soundapi-axioms.sh` / `soundapi-axioms.log`.
Builds on `NP-LIFTING.md` (read that first for `LiftCP`, `LiftCPConst`, `WidthToCP`) and `TRANSPORT.md` 3.3.

Status marks: **classical** (textbook, recalled), **external, read** (source text read in this round; "statement only" when the
proof was not read), **external, recalled** (not read), **Lean**, **reading** (my interpretation, not a theorem), **open**.

---

## 0. In plain words

**The owner's route.** Treat a proved lower bound for a simple model as a trusted interface (an "API"), a root, and compose it
with a gadget into a lower bound for a stronger model. That is exactly what lifting does: the root is "resolution width
`w`" (a proved quantity), the gadget is Index, the output is "cutting planes needs `n^(c w)` lines". The open step is the same
composition with a **constant-size** gadget (`LiftCPConst`).

**What the literature says (section 1).** I read the main sources. Every dag-like cutting-planes lifting theorem needs a gadget
whose size grows with `n`: polynomial in the original (`n^delta`), `n^(1+eps)` since 2022, and the tightest-loss version of 2024
needs `m` of order `n^(2/eps)`. Constant-size gadgets are known to work only for *weaker target models*: parity decision trees
and tree-like resolution over parities, dag-like **resolution**, and algebraic measures (degree to rank). For cutting planes with a constant gadget there is
no positive result I could find, and the authors of the tree-like and dag-like papers all call it open.

**What blocks it (section 3).** In the known proofs the gadget size is spent in one place: a lemma saying that a large set of
pointers hits every unfixed block ("blockwise robust sunflower"), which needs `log m` to beat `log n`, the number of blocks.
A conjecture that would have pushed this below polynomial size is now **refuted for Index and Inner Product below `log N`**
(Beame and Koroth 2023). So the entropy-and-disperser way of proving lifting stops at logarithmic size; a constant gadget would
need a different notion of structure.

**The interface at the DB (section 1.3).** In the owner's terms the API at the DB is the interpolant, the inversion that proves the link
to the shared root. The monotone interpolant and the two-party protocol of lifting are the same object (a monotone real circuit read
as a dag of protocol steps), and section 1.3 says, theorem by theorem, how the size of what crosses is controlled; the one place
where control fails for a constant gadget is bounding the leak of the interface by something other than entropy.

**What would suffice (section 2).** Every lifting proof ends the same way: from a small refutation it builds, for each line, a
set of narrow clauses of the original formula. This is now a Lean statement (`ExtractAPI`), proved **equivalent** to
`LiftCPConst`. So the precise new "sound API" is: *a constant gadget whose hiding lets one build the narrow clause labeling,
with error exponentially small in the width, uniformly in `n`*. Section 3.3 spells out the three properties it needs.

**The walls (section 4).** Relativization, natural proofs and algebrization are barriers for *complexity classes and circuit
lower bounds*. They do not apply to a lower bound for one specific proof system on explicit formulas (those exist
unconditionally: resolution, cutting planes). They bite at the other end, the "all proof systems" statement, where an argument
must look inside each system's lines. The wall that actually stops this route is different and concrete: lifting needs lines with
cheap two-party protocols, and Frege lines do not have them.

**Not claimed.** No lower bound beyond the cited theorems; nothing for Frege; nothing for unlifted formulas; no progress on NP vs coNP.

---

## 1. The catalogue of "APIs"

Reading of the columns: **G0** = the proved interface consumed; **gadget** = its size in the theorem; **reaches** = the model
the bound is for; **relativizes?** = see the note after the table (the BGS sense does not literally apply to these; the useful
question is whether the argument opens the target model).

### 1.1 Lifting theorems (a lower bound for a simple model, composed with a gadget)

| # | theorem (source, status) | G0 consumed | gadget size | reaches | opens the target model? |
|---|---|---|---|---|---|
| 1 | Raz-McKenzie 1999; Goos-Pitassi-Watson 2015/18; de Rezende-Nordstrom-Vinyals 2016 (**external, recalled**; the size demand is quoted in GKMP section 2.2, **read**) | decision-tree depth (tree-resolution depth) | Index with `m = poly(n)`; GKMP: "a gadget that can be computed by a decision tree of depth Theta(log n)" | deterministic communication, tree-like | yes: rectangles |
| 2 | Garg-Goos-Kamath-Sokolov 2018 (TOC 2020), Thms 1, 2 (**external, read**, ECCC version) | resolution width `w(S)` (conjunction-dag width) | Index, `m = n^delta` | **dag-like**: rectangle-dags, triangle-dags: monotone (real) circuits, semantic cutting planes; `tri-dag = n^(Theta(w))` | yes: lines are triangles `{a(x) < b(y)}` |
| 3 | Goos-Koroth-Mertz-Pitassi 2020 (arXiv 2004.08037), Thm 4, Thm 8 (**external, read**, sections 1 to 6.1) | resolution **block-width** | multi-output gadget, `m = (n l)^Theta(1)` (Thm 8: `(n l)^5`) | dag-like cutting planes, via `k`-party "simplex-dags" | yes |
| 4 | same, Thm 13, 14 "small gadget lifting" (**external, read**) | decision-tree depth `d(F)` | `Ind_m`, **`m` free**; bound `m^(Theta(min(d(F), m^(1/1000))))` | **tree-like** cutting planes and real protocols | yes |
| 5 | Lovett-Meka-Mertz-Pitassi-Zhang, "Lifting with sunflowers", ITCS 2022 (**external, read**, ITCS version) | decision-tree depth / resolution width | Index, `m = n^(1+eps)` for every `eps > 0`; `m = O(n log n)` with a weaker lifting factor; before it "at least a quadratic gadget size" | deterministic communication, tree-like **and dag-like**; "(almost) all results extend to real communication"; Thm 19: tree-like with `m` of order `(max(d, log n))^(1+eps)` | yes |
| 6 | de Rezende-Fleming-Janett-Nordstrom, "Truly supercritical trade-offs", arXiv 2411.14267, Thm 2.11 (**external, read**: statement and proof outline; Triangle Lemma proof not read) | resolution width and depth | `Ind_m`, `m >= (50 n / eps)^(2/eps)`; a triangle-dag of size `(1/2) m^((1-eps) w)` gives a resolution refutation of width `w`, depth `d w` | dag-like triangle-dags (monotone real circuits, cutting planes); loss is "tight" | yes |
| 7 | Beame-Koroth, ITCS 2023 (arXiv 2211.17211) (**external, read**, abstract and introduction) | decision-tree size | Index of size **at least 4**, but only for protocols where one player sends parities; also DT size to parity-DT size | restricted protocol class; tree-resolution size to tree-like Res(+) | partly (parity side) |
| 8 | Chattopadhyay-Mande-Sanyal-Sherif, ITCS 2023 (arXiv 2211.17214) (**external, read**, abstract and introduction) | decision-tree depth | **constant**: "stifled" gadgets: Index on 3 bits, Inner Product on 4 bits, Majority on 3 bits, random functions | parity decision-tree size; tree-like Res(+) for constant-width CNFs; **not cutting planes, tree-like only** | yes (parities) |
| 9 | Alekseev-Filmus-Smal, "Lifting dichotomies", CCC 2024 (ECCC TR24-037), Comput. Complexity 2025 (**external, read**: Thms 4.1 to 4.3 statements; the proof of 4.1 is one paragraph, "random projection", **not checked**) | resolution (conjunction-dag) width | **constant**: any "resistant" gadget (fixing any input to either value leaves it non-constant), e.g. XOR; AND is not | **dag-like resolution** size: a conjunction dag of size `S` for `f o g` gives one of width `O(log S)` for `f`; and a dichotomy: for each gadget polynomial lifting or none (four settings) | yes |
| 10 | Algebraic-measure lifting: Sherstov (degree to rank); Pitassi-Robere 2018; de Rezende-Meir-Nordstrom-Pitassi-Robere-Vinyals, FOCS 2020 (arXiv 2001.02144), Thm 1 (**external, read**, introduction) | Nullstellensatz degree `NS(C)` | any gadget of rank `r >= c n / NS(C)`: **constant** when the degree is linear | deterministic communication and Razborov rank; monotone span programs; cutting planes with polynomially bounded vs unbounded coefficients (length-space separation) | yes |
| 11 | Iyer, "Lifting for arbitrary gadgets", ECCC TR25-036 (**abstract only**) | sensitivity | any gadget, loss in `D(g)` and `log rank(g)` | deterministic communication; no proof-system statement seen | n/a |

### 1.2 Other composition theorems

| # | theorem (status) | G0 consumed | gadget | reaches | notes |
|---|---|---|---|---|---|
| 12 | Razborov, hardness condensation (2016) (**external**, mentioned in the 2024 supercritical paper, introduction 1.4, **read**; not read itself) | a hard formula | substituting variables by XOR over a smaller variable set | resolution trade-offs | amplification by substitution, not lifting |
| 13 | Feasible (monotone) interpolation: Krajicek 1997; Pudlak 1997 (**classical, recalled**; use quoted in the 2020 simple-gadgets paper, **read**) | a monotone (real) circuit lower bound | none | cutting planes; any system with feasible interpolation | fails for Frege and Extended Frege under cryptographic assumptions (Krajicek-Pudlak; Bonet-Pitassi-Raz, as quoted in the 2019 Pich-Santhanam paper, **read**) |
| 14 | Size-width: Ben-Sasson-Wigderson 2001 (**classical**; in-project **Lean**: `size_width_exp`, `resolution_meets_form`) | resolution width | none | resolution (and the width-based `CrossingCost` slot) | the template of "width is the root" |
| 15 | Direct sum, XOR lemma, hard-core lemma (**classical, recalled** for circuits and communication) | a hardness bound for one instance | none | circuits, communication | **I found no composition theorem of this kind for cutting-planes proof size**; not searched beyond the sources above |

**Note on "relativizes".** Baker-Gill-Solovay (1975) is about arguments (simulation, diagonalization) that stay valid when all
machines get an oracle (**classical**; the statement and the oracles for P = NP and P != NP are in the Pich-Santhanam
introduction, **read**). None of the theorems in the tables involves machines or oracles, so the BGS notion does not
apply literally. The useful distinction is **reading**: all of them are *black-box in the source bound* (the width, depth or
degree is used only as a number) and *white-box in the target* (they open what a line is: a rectangle, a triangle, a parity
line). Section 4 returns to this.

---

### 1.3 The API at the DB: what crosses the split, and how each theorem controls its size

The owner's framing (last `PREP.md` entry, relayed by the coordinator): NP is what can be certified locally, inside a DB
(everything that shares a G0); the coNP side localises to the shared part only through the **interpolant**, the inversion that
proves the link to G0, and its size is the cost. Exact classical counterparts: Cook-Levin and PCP (NP certificates are locally
checkable); Craig interpolation and **feasible interpolation** (a short refutation of `A(x,z) and B(x,y)` gives a small circuit
for the interpolant on the shared variables `x`) (**classical**). In the tables above this interface is the **two-party split**:
Alice holds one half, Bob the other, and what crosses is the communication. **Reading** (supported by the 2024 paper, introduction
and section 2, **read**, where "a monotone circuit computes `f` iff a dag-like rectangle (real: triangle) protocol solves the monotone
Karchmer-Wigderson game `mKW(f)`, with the same size"): the monotone interpolant of row 13 and the two-party protocol of the lifting
rows are **the same object**, a monotone (real) circuit read as a dag of protocol steps. So "API at the DB" = interpolant = lifting's
protocol, and the question for each theorem is how it bounds the *size of what crosses*.

| # | what crosses the split | how the theorem controls its size | status |
|---|---|---|---|
| 1 | bits of a deterministic (tree-like) protocol for `F o g` | each query of the outer function costs at least `log m` bits through an Index gadget (Index has a protocol of cost `log m + 1`, Beame-Koroth intro, **read**); a protocol of `c` bits gives a decision tree of depth `O(c / log m)`: the crossing cost is *converted back* into queries | **external**, recalled (RM, GPW), size demand **read** |
| 2 | one real comparison `a(x) < b(y)` per line (a triangle; "real communication", Krajicek 1998, named in GKMP section 6, **read**); the dag size `s` is `2^(crossing)` | a dag of size `s` gives resolution width `O(log s / log n)`: crossing `log s` bits forces `w` hidden variables to be resolved, each costing `Theta(log m) = Theta(log n)` bits; this is the "crossing cost per hidden variable" of `TRANSPORT.md` 3.3 | **external, read** |
| 3 | `l` bits per block, `k` parties | the gadget size `m = (n l)^(Theta(1))` makes a block's `l`-bit interface hide itself; block-width counts blocks, not variables | **external, read** |
| 4 | a real protocol of depth `d`, tree-like | `m` free: the interface per variable is `log m` bits, and the bound `m^(min(d, m^(1/1000)))` says `d` crossings of `log m` bits each are forced | **external, read** |
| 5 | as row 2 (and deterministic dag-like protocols) | the sunflower lemma is the statement that a set of rows leaking less than `(1-eps) log m` bits per block (blockwise min-entropy) still reaches every value of every unfixed block: it bounds the **leak** of the interface; the size of the interface is the `log m` per block | **external, read** |
| 6 | as row 2 | tight: crossing `(1-eps) w log m` bits is necessary and sufficient (`m^((1-eps) w)`, upper bound by simulation) | **external, read** |
| 7 | parities sent by one player | the interface is restricted to parities; below `log N` the entropy-deficiency accounting of the interface fails for Index and Inner Product (Conjecture 11 refuted): **the leak of a small gadget cannot be bounded by entropy** | **external, read** |
| 8 | parities of arbitrary subsets of variables (parity decision tree size) | stifling: for any `k` variables there is a setting of the rest that fixes the output, so `k` crossed parities reveal nothing: **size of the interface = number of parities, controlled by `k`-stifling of a constant gadget** | **external, read** |
| 9 | a conjunction (certificate) per node | a node whose certificate is wide dies under a random projection; interface size = certificate width, and size `S` gives width `O(log S)`; resistant gadgets keep the width visible | **external, read** (statement; proof not checked) |
| 10 | the rank of the communication matrix (Razborov rank, `log rank` bits) | the theorem needs the gadget's rank `r >= c n / NS(C)` and bounds the communication below by `NS(C)` (Razborov rank): the interface is controlled by an **algebraic** rank, which is why a constant gadget suffices when the degree is linear (how the rank accumulates over blocks was not read) | **external, read** |
| 11 | communication of the gadget `D(g)` | loss in `D(g)` and `log rank(g)` | abstract only |
| 12 | the shared variables after substitution | the number of variables of the substituted instance, traded against hardness | external, mentioned, not read |
| 13 | **the interpolant**: a monotone (real) circuit on the shared variables | size of the circuit is at most polynomial in the proof size (cutting planes: Pudlak; resolution: Krajicek); so a proof-size lower bound follows from a circuit lower bound, which is a G0 | **classical**, recalled |
| 14 | a clause: the boundary between decided and undecided variables | its width; size-width says a short refutation has a narrow one: the **local** certificate, nothing crosses a split because there is none | **classical**; in-project **Lean** |
| 15 | per-copy cost, summed | would multiply the interface size by the number of copies; not read | recalled |

**Where control is lost, in these terms.** (i) A constant gadget makes the interface per variable `O(1)` bits; the proofs of rows 2 to 6
control the leak by entropy, which row 7 shows cannot work below `log N`: this is the open step, restated as "bound the leak of a
constant-size interface by something other than entropy". (ii) For Frege the interface is not small: there is no feasible interpolation
under cryptographic assumptions (Krajicek-Pudlak; Bonet-Pitassi-Raz, **read** in the Pich-Santhanam introduction), and Frege lines
do not have cheap protocols (section 4), so the interpolant cannot be localised to the shared part. This is the same wall as section 4,
seen from the interface. (iii) In the owner's terms the open statement `LiftCPConst` says: **the inversion at the DB, for one
variable, costs a constant fraction of a constant**; `TRANSPORT.md` 3.3 `liftCPConst_hiddenTransport` is its Lean form.

---

## 2. What every lifting proof delivers, as a Lean interface

All dag-like proofs above (rows 2, 3, 5, 6) have the same second step (GGKS "Step 2", 2018; the 2024 paper restates it in its
proof overview, **read**): for each node of the refutation dag construct a set of clauses of width at most `w`, such that the
clauses at the root include the empty clause, the clauses at the leaves are weakenings of clauses of `F`, and the clauses at
a node follow from those of its children within resolution of width `w` (and depth `d w`). The gadget and the size of the
refutation are used only to construct these sets.

`SoundAPI.lean` makes that statement exact.

| declaration | content | status |
|---|---|---|
| `Labeling G F w P Γ` | `Γ` assigns to each line of `P` a set of clauses of `F`: width at most `w`; at an axiom line each clause contains a clause derivable from `F` in width `w`; at an add, scale or round step inside `P` each clause contains a clause derivable in width `w` from the labels of the premises; the root carries the empty clause | definition, **Lean** |
| `Labeling.derivable`, `labeling_refutes` | a labeling gives a resolution refutation of `F` of width `w` (induction over the cutting-planes derivation; axioms replaced by derivations with `WD.trans`) | **Lean** |
| `ExtractAPI G c` | **the sound API**: every cutting-planes refutation of `F o G` with fewer than `exp (c (w + 1))` lines admits a labeling at width `w` | definition; **open** for every constant `G`, `c > 0` |
| `extract_to_lift`, `lift_to_extract`, `liftCPConst_iff_extract` | `ExtractAPI G c` and `LiftCPConst G c` are **equivalent** | **Lean** |
| `width_of_small_refutation` | under `LiftCPConst`, a refutation of `F o G` with fewer than `exp (c (w + 1))` lines gives a width-`w` resolution refutation of `F` | **Lean** |
| `liftCPConst_mono`, `liftCPConst_zero` | smaller `c` is easier; `c = 0` is trivial (a refutation has a line), so the content is `c > 0` | **Lean** |

**Reading of the equivalence.** It is an honest implication, and it shows two things. (1) Nothing is lost by working with the
labeling form: it is `LiftCPConst`, in the shape in which proofs establish it. (2) The labeling form is not *easier*:
the Lean proof of `lift_to_extract` labels every line with the empty clause once `F` has a width-`w` refutation, so the whole
difficulty is the case where it has none, and there the labeling has to be built from the refutation. That construction is the
open mathematics.

---

## 3. The route to `LiftCPConst`

### 3.1 Which known API comes closest

- **In gadget size, for dag-like cutting planes:** Lovett et al. (row 5): Index `n^(1+eps)`, or `O(n log n)` for a weaker
  factor. Polynomial.
- **In loss:** the 2024 theorem (row 6) is tight in the exponent but needs `m >= (50n/eps)^(2/eps)`.
- **In smallness of gadget, but for a weaker model:** constant gadgets lift to parity decision trees (rows 7, 8), to
  dag-like **resolution** (row 9, resistant gadgets such as XOR), and to algebraic measures (row 10, constant rank when the
  degree is linear). None reaches cutting planes.
- **For tree-like cutting planes:** row 4: the gadget depends on the *depth* `d`, not on `n`: size about `d^1000`, improved by
  Lovett et al. Theorem 19 to about `(max(d, log n))^(1+eps)`. For the width-linear formulas the project cares about this is
  again polynomial in `n`. GKMP state "it is an important open problem whether tree-like lifting is possible with a
  constant-size gadget" (section 2.2, **read**).
- **For the multi-output gadgets of row 3:** GKMP write that considering many parties "is what allows us to analyze
  multi-output gadgets; we do not know how to do this with only two parties" (section 2.1, **read**).

So the closest is row 5 for dag-like cutting planes; the nearest constant-gadget results are rows 9 and 8 for the models just
below and beside cutting planes.

### 3.2 What exactly blocks it (read from the sources)

1. **One lemma carries the whole gadget size.** Lovett et al. state it themselves: their union bound over the removed sets
   "does not require a large gadget size", which "consolidates all issues of the choice of `m` to Lemma 7" (footnote 9,
   **read**). Lemma 7 is a blockwise robust sunflower lemma, applied with set size `n` (the number of blocks); the condition
   they check is `0.95 log m - O(1) >= log(K n log m)` (the section on improved gadget size), which gives `m = n^1.1`, and `n^(1+eps)` after
   changing the entropy threshold from `0.95` to `1 - eps`. In the 2024 proof the same place appears as the **Full Image
   Lemma**: a rectangle whose pointer side has blockwise min-entropy `eps log m` per block and whose table side has
   entropy deficiency at most `m / (8n)` has a row whose image under Index is the whole cube; the lemma needs `m` of order
   `n` (the exact constant could not be read from the extracted text; the paper says it does not optimise gadget size).
   For `m = O(1)` the allowed table deficiency `m/(8n)` is less than one bit.
2. **The entropy route is closed below logarithmic size.** Lovett et al. isolate what that route needs, Conjecture 11:
   entropy-deficient distributions on pointers and tables hit a subcube of codimension `O(deficiency)`. Beame and Koroth
   (abstract and introduction, **read**) prove it **false when the Index gadget has size below `log N`**, and the same for Inner
   Product ("known to satisfy the disperser property at size `O(log N)`"). So no proof that keeps an entropy-deficiency
   invariant can reach a constant gadget.
3. **A second union bound, over the lines, is separate and harmless in principle.** The 2024 proof bounds the accumulated
   error at the root by `m^(-(1-eps) w) * |dag| <= m^(-(1-eps) w) * m^((1-eps) w / 2) = 1/2` (equation 7.8, **read**). For a
   constant `m` this needs each line's error to be exponentially small in `w` with a base independent of `n`. This is the
   quantitative requirement in section 3.3 (S2).
4. **A counting check on the form of the statement** (**classical**, not formalised): every unsatisfiable CNF on `N` variables has a
   resolution, hence cutting-planes, refutation with `2^(O(N))` lines (the full decision tree). A statement `exp (c (w+1) log n)`
   with a *constant* gadget would, for width `w` of order `n`, exceed that. So `LiftCP` with `log n` cannot hold for any
   constant gadget; the constant version must read `exp (c (w+1))`, which is exactly `LiftCPConst`, and is the largest bound
   this check allows.
5. **Direction of reductions.** If `G'` is obtained from `G` by fixing some of its input bits, a refutation of `F o G`
   restricts to a refutation of `F o G'`, so hardness of `F o G'` gives hardness of `F o G`, not conversely (**reading**,
   restriction of a refutation; not formalised). So the poly-size Index theorem does not give a constant-size one by
   restriction. In the other direction Beame and Koroth observe that, by universality of Index, a lifting theorem for any
   constant-size gadget gives one for a constant-size Index gadget (**read**, introduction), so Index is the one to treat.

### 3.3 The new sound API that would suffice

Stated in Lean as `ExtractAPI G c` (section 2). The mathematical content to be proved, for a **fixed** gadget `G` (Index on a
constant number of pointer bits is enough, by 3.2.5), uniformly in `n`, is the following (**reading**: this is my
abstraction of the common structure of the proofs in rows 2, 5, 6, not a statement from a source):

- **(S0) a notion of structured rectangle** `R = X x Y` (rows `X` held by Alice, columns `Y` by Bob) with a set `fix(R)` of at
  most `w` blocks, that does **not** rest on the total entropy deficiency of `Y` (point 3.2.2).
- **(S1) full image.** A structured rectangle has every assignment of the unfixed blocks in the image of the gadget. This is
  what makes the leaves weakenings of clauses of `F` (`comp_falsified_iff` is the Lean form of that step) and the root carry the empty clause.
- **(S2) cover with exponentially small error.** Every threshold set `T = {(x, y) : a(x) < b(y)}` (a cutting-planes line is a triangle in the two-party split, because each side contributes a separate sum; classical, not stated in Lean here) is covered
  by structured rectangles, up to an error set whose density is at most `exp (-kappa w)`, with `kappa` independent of `n`
  and larger than the constant in the size bound. Then `|P| < exp (kappa' w)` makes the union bound at the root work.
- **(S3) local simulation.** The clauses read off the rectangles at a node follow from those at its two children within
  width `w`.

(S0) to (S3) give `ExtractAPI` by the constructions already in the proofs of rows 2, 5, 6; I have not formalised that and do not
claim the implication, only that this is the part of those proofs that would have to be redone for a constant gadget.

**One idea, unchecked.** Rows 7, 8 (parity lines) work with constant gadgets because the line class is closed under the
structure the proof uses. A cutting-planes line has an extra structure that the entropy proofs do not use: it is a *staircase*, rows and
columns totally ordered by `a(x)` and `b(y)`, and the proofs treat a triangle only through a cover by rectangles. Whether
(S0) can be built from the total order instead of from entropy is **open** and I know of no source that tries it.

### 3.4 What the round supports, in one paragraph

The honest statement of progress is: the route is correct in shape (an API consumed as a root, composed with a gadget); the
interface is now exact and Lean-checked (`ExtractAPI`, equivalent to `LiftCPConst`); the closest known results are
polynomial-gadget lifting for cutting planes and constant-gadget lifting for resolution, parities and degree-to-rank; and the
specific obstruction is a disperser-type lemma that is false below logarithmic size for the entropy method. No constant-gadget
cutting-planes lifting theorem is known or claimed.

---

## 4. The walls: which of them apply to proof-system lower bounds

| wall | what it says | applies to a lower bound for a specific proof system on explicit formulas? | where it does apply |
|---|---|---|---|
| **Relativization** (Baker-Gill-Solovay 1975; **classical**, statement read in Pich-Santhanam intro) | arguments that stay valid with any oracle cannot settle P vs NP: oracles exist for both outcomes | **No.** No machines or oracles are involved; such bounds are unconditional and known (Haken 1985 for resolution, Pudlak 1997 for cutting planes, GGKS 2018 for lifted cutting planes) | the **all-systems** end: NP vs coNP needs a lower bound for every proof system (Cook-Reckhow, **read** in the Pich-Santhanam intro); an argument that never looks inside the systems' lines would relativize and cannot work. **Reading:** lifting is not of that kind, because it opens the target (lines are triangles). Using a proved bound as a root is therefore not barred; what is barred is an argument opaque in the *target*. |
| **Natural proofs** (Razborov-Rudich 1997; **classical, recalled**; constructive and large properties, under pseudorandom functions; summary from secondary sources) | combinatorial properties of truth tables that are easy to test and hold for many functions cannot prove super-polynomial circuit lower bounds against P/poly | **No.** It concerns circuit lower bounds against strong classes. Monotone and restricted classes are not covered (the definition is awkward for them: a random function is not monotone; that remark is from lecture notes, an inference, not a theorem I read) | **proof-complexity analogue** (Pich-Santhanam, FOCS 2019, abstract and introduction **read**): no proof system efficiently proves that truth tables of random functions lack polynomial-size non-uniform proofs; under Rudich's conjecture, the same for random `k`-CNF of linear density. This is about lower bounds against *all* (non-uniform) proofs and about their *feasible formal provability*, not about cutting-planes size bounds by lifting. Related older fact (Razborov, **read** in the same introduction): systems with feasible interpolation cannot efficiently prove circuit lower bounds, which limits what cutting planes can prove, not what can be proved about it. |
| **Algebrization** (Aaronson-Wigderson, STOC 2008; abstract **read**) | relativization strengthened to oracles that also supply low-degree extensions; P vs NP needs non-algebrizing techniques | **No** by definition (class separations with oracles). I found no source applying it to proof-system lower bounds. Lower bounds for the algebraic systems (Nullstellensatz degree) are unconditional and are used as roots (row 10). | class separations only |
| **The wall that does bind this route: lines without cheap protocols** (**reading**, with the classical facts below) | lifting needs lines of the target system to have efficient two-party protocols (a rectangle or triangle structure). A Frege line can be an arbitrary formula; Equality `and_i (x_i = y_i)` has deterministic communication complexity `Omega(n)` | **yes**, and it is the reason the route stops at cutting planes | Frege and Extended Frege have no feasible interpolation under cryptographic assumptions (Krajicek-Pudlak; Bonet-Pitassi-Raz; quoted in Pich-Santhanam, **read**), so interpolation-type APIs (row 13) are closed there too |

**Plainly:** relativization, natural proofs and algebrization do not stand between this project and a constant-gadget cutting-planes
lifting theorem: that statement is about one explicit proof system. They would matter if the argument were stretched to "every proof
system", where the obstacle is the Frege wall, and where the Pich-Santhanam results say that a *feasibly formalised* hardness proof
for strong systems cannot exist under their hypotheses (a statement about short propositional proofs, not about Lean).

---

## 5. Status table

| item | status |
|---|---|
| dag-like cutting-planes lifting with Index `n^delta`, `n^(1+eps)`, `m >= (50n/eps)^(2/eps)` | **external, read** |
| tree-like cutting planes lifting with gadget depending on depth `d` (GKMP Thm 13) | **external, read** |
| constant gadgets for parity decision trees, tree-like Res(+), dag-like resolution (resistant), degree-to-rank | **external, read** (resolution proof of row 9 not checked) |
| constant-size gadget for dag-like (or tree-like) cutting-planes lifting | **open** (named open by GKMP, LMMPZ, Beame-Koroth, CMSS) |
| LMMPZ Conjecture 11 false for Index and Inner Product below `log N` | **external, read** (abstract and introduction) |
| every dag-like lifting proof has the clause-labeling form | **reading** of the proofs (statement of GGKS "Step 2" and the 2024 overview **read**) |
| `Labeling`, `labeling_refutes`, `liftCPConst_iff_extract`, `width_of_small_refutation`, `liftCPConst_mono`, `liftCPConst_zero` | **Lean** |
| `ExtractAPI G c` for a constant `G`, `c > 0` | **open** (equivalent to `LiftCPConst G c`) |
| (S0) to (S3) suffice for `ExtractAPI` | **reading**, not formalised |
| a cutting-planes line is a triangle in the two-party split | **classical** (GGKS, **read**); not stated in Lean here |
| `LiftCP` with `log n` impossible for a constant gadget (`2^(O(N))` upper bound) | **classical** counting, not formalised |
| relativization, natural proofs, algebrization do not apply to specific-system lower bounds | **reading**, with the sources above |
| Frege: no cheap-protocol lines; no feasible interpolation under cryptographic assumptions | **classical** |
| interpolant = two-party protocol at the split (monotone Karchmer-Wigderson game) | **classical** (read in the 2024 paper, section 2); the per-theorem control table in 1.3 is a **reading** |
| NP vs coNP | **open**; no progress claimed |

## 6. Corrections and upgrades for earlier notes

- `TRANSPORT.md` 3.3, item 2 ("why known proofs need a growing gadget": a per-block error added by a union bound over the `n`
  blocks, `n epsilon < margin`). The sources say something more specific. The growth of `m` comes from the **blockwise
  robust sunflower / full-image lemma**, where `log m` must exceed `log` of the number of blocks (point 3.2.1); the union bound
  over the *lines* of the dag is a separate bound and, by Lovett et al. footnote 9, does not force a large gadget. So the
  critical-case picture ("no damping between blocks") is a fair image of the sunflower step, but the sentence should say
  "union over blocks in the disperser lemma", not "union bound of per-block hiding errors". The statement that a constant
  quantum needs a different mechanism, not an entropy bound, is supported by Beame-Koroth.
- `NP-LIFTING.md` 1.5: the rows for Lovett et al. (now **read**, ITCS version), Goos-Koroth-Mertz-Pitassi (now **read**,
  sections 1 to 6.1: the "two parties" sentence is verbatim in section 2.1), Beame-Koroth and Chattopadhyay et al.
  (now **read**, abstract and introduction) can be upgraded from "reported". New rows: the 2024 triangle-dag theorem, the
  dichotomy paper, the algebraic-measure paper. Beame-Koroth's "dream range" sentence is: by universality of Index, a lifting
  theorem for any constant-size gadget gives one for constant-size Index. The statement "nothing positive for cutting planes with a
  constant gadget" survives this round's search (one more pass on the abstracts and the sources above; still limited).
- `NP-LIFTING.md` 2.3 item 3 and 1.5: the constant-gadget results that do exist (resolution, parities) are the nearest rungs
  below `LiftCPConst`; mention them next to the open statement.

## 7. What was read and what was not

Read in full or in the parts named: GKMP (arXiv 2004.08037, text of sections 1 to 6.1 and Theorem statements);
Lovett-Meka-Mertz-Pitassi-Zhang (ITCS 2022: abstract, introduction, section 3 to 6 passages on gadget size, footnote 9,
Conjecture 11, Theorem 19); de Rezende-Fleming-Janett-Nordstrom (arXiv 2411.14267: introduction, section 2.11, section 7
statements and the root bound 7.8); Beame-Koroth (abstract, introduction, Conjecture 1.1); Chattopadhyay et al. (abstract,
introduction); Alekseev-Filmus-Smal (abstract, section 1.1, Theorems 3.x, 4.1 to 4.3); de Rezende et al. FOCS 2020
(abstract, introduction, Theorem 1); Pich-Santhanam (abstract, introduction). Abstract only: Iyer (ECCC TR25-036), Aaronson-Wigderson
(search-result abstract). Not read: Razborov hardness condensation, Razborov-Rudich, Krajicek, Pudlak, Bonet-Pitassi-Raz, the proofs
of the Full Image Lemma and the Triangle Lemma, the proof of AFS Theorem 4.1. The search for newer constant-gadget cutting-planes
results (two web searches, 2024 and 2025 titles) found none; "none exists" is **not** established.

## 8. Literature

- A. Garg, M. Goos, P. Kamath, D. Sokolov, Monotone circuit lower bounds from resolution, STOC 2018; Theory of Computing 16 (2020).
- M. Goos, S. Koroth, I. Mertz, T. Pitassi, Automating cutting planes is NP-hard, STOC 2020 (arXiv 2004.08037).
- S. Lovett, R. Meka, I. Mertz, T. Pitassi, J. Zhang, Lifting with sunflowers, ITCS 2022 (ECCC TR20-111).
- S. de Rezende, N. Fleming, D. A. Janett, J. Nordstrom (and coauthors), Truly supercritical trade-offs for resolution, cutting
  planes, monotone circuits, and Weisfeiler-Leman, arXiv 2411.14267 (2024).
- P. Beame, S. Koroth, On disperser/lifting properties of the Index and Inner-Product functions, ITCS 2023 (arXiv 2211.17211).
- A. Chattopadhyay, N. Mande, S. Sanyal, S. Sherif, Lifting to parity decision trees via stifling, ITCS 2023 (arXiv 2211.17214).
- Y. Alekseev, Y. Filmus, A. Smal, Lifting dichotomies, CCC 2024 (ECCC TR24-037); Computational Complexity 34(2), 2025.
- S. de Rezende, O. Meir, J. Nordstrom, T. Pitassi, R. Robere, M. Vinyals, Lifting with simple gadgets and applications to circuit and
  proof complexity, FOCS 2020 (arXiv 2001.02144).
- S. Iyer, Lifting for arbitrary gadgets, ECCC TR25-036 (abstract only).
- J. Pich, R. Santhanam, Why are proof complexity lower bounds hard?, FOCS 2019.
- T. Baker, J. Gill, R. Solovay, Relativizations of the P =? NP question, 1975; A. Razborov, S. Rudich, Natural proofs, 1997;
  S. Aaronson, A. Wigderson, Algebrization, STOC 2008 (ECCC TR08-005); S. Cook, R. Reckhow, 1979 (recalled).
- Earlier-round sources are listed in `NP-LIFTING.md` section 8.
