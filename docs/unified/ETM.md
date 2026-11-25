# DMP as the Existence Turing Machine

2026-11-23. Lean: `docs/mass-gap/formal/ProofPhase/ETM/` (5 modules, 154 declarations, standard axioms only,
`etm-axioms.log`). Background: the ETM paragraph of `docs/guid/guid.tex` (section "Host, not model"), the preface, the
PREP entries "DMP as an Existence Turing Machine", "Subsets save the day", "Anything that establishes itself as a subset
can be run", "A theorem proven inside a DB is true everywhere ... every meaning of running goes through DMP", "U(1)
failing the handshake ... make DMP into the ETM", "The thesis restated: ... the root G0" and "The tautology is the
feature", `UNIFIED.md` (the ledger), `ENCODER.md` and `GRH-LENS.md` section 6.

**Two layers.** Read every result below in one of two layers, never across them.
- **The form layer** is DMP's general theorems: the ledger, the encoder, the half-turn, the universal property
  (section 3), "every rooted system is an instance" (section 6) and the halting edge (section 5). They hold for every
  content because they say nothing about content. That is the design, not a defect: it is what lets one theorem apply
  to every instance (the owner: "It says nothing about it's content").
- **The content layer** is the instances (sections 4 and 6). Each carries its own content and its own named open step:
  O1 for Yang-Mills, the sign for GRH, the crossing cost for NP vs coNP. The checks that make the form layer non-vacuous
  live here: the universal object is not a point (section 3), the known systems are rooted in G0, and G0 is not trivial
  (section 6).

A form theorem is never a claim about content. It transports what an instance proves; it cannot settle an instance's
open step.

**The top theorem as the certification of existence.** The owner's construction principle (PREP, last entry): proofs are
well-understood tools arranged in a DMP-wise state, tied together by the right top theorems through their shared
properties, with content left to the best existing solutions and DMP "making sure the certification of existence is
absolute for every existence describable". In this round the tie is two theorems, and together they are that
certification:
- **Universal property** (`univIsTerminal`, `trace_unique`, section 3): every running system has exactly one map into
  the ledger space. Its ledger is its certificate, the same for every system and unique for each.
- **Soundness** (`RunSys.carry`, `RunSys.contract`, `RunSys.decay_cost`, section 3; `Rooted.good`, section 6): every
  bound proved once on the ledger space holds at every traced point, and every system derived from G0 obeys the law.

Both hold in every instance because they use only the shared properties: a positive weight (the mass), a transfer step,
a mirror and its encoder (the factor in [0, 1]), and the ledger (the law with its floor). They use nothing particular to
any instance. "Absolute" means exactly this, and no more: the certificate is valid for every instance by form alone.
Whether a given instance's certificate is the one it needs (O1, the sign, the crossing cost) is content, left to that
instance's own mathematics.

**Status marks.** **[Lean]** = proved in Lean, standard axioms only (`propext`, `Classical.choice`, `Quot.sound`);
**[classical]** = known mathematics, recalled, not re-proved here; **[numerical]** = computed, not proved;
**[reading]** = interpretation, including every DMP identification; **[open]** = not proved by anyone. Nothing marked
[open] is used as proved: each open step enters the Lean as an explicit argument.

---

## 1. In plain words

**What a running system is.** Something is carried from step to step: an influence, a margin, a distance between two
probability laws, a number of proof lines, the size of a shrinking sphere. At every step the carried amount crosses a
boundary, and the boundary has a price: a factor between 0 and 1 (the encoder). The amount after the step is at most the
amount before, times the factor, times one fixed allowance per step (the floor). That is all a running system is: a
step, a factor in [0, 1] at each state, a nonnegative amount, and that one inequality. Maps between running systems must
respect all four. Restricting to a subset that the run never leaves is such a map; so is coarse-graining by a relation
the run respects.

**The universal property.** There is one running system that every other maps into, in exactly one way: the space of
all ledgers. A ledger is the full record of a run: the list of factors paid and the list of amounts carried, step by
step. The one map sends each state to its own ledger. So every running system factors through the ledger, uniquely.
**[Lean]**

**Why this is not empty.** In many categories the system everything maps into is a single point, and then the statement
says nothing. Here it is not a point: the ledger space holds every possible list of factors and every starting amount,
and the floor matters (raising it lets in ledgers the lower floor forbids). If the maps were allowed to forget the
factor and the amount, the single point would take over. Keeping them is what puts the content (factor, cost, floor)
into the universal object. **[Lean]**

**The instances.** Markov chains with a Dobrushin coefficient, lattice Yang-Mills boxes for every SU(N), the Szego
chain of GRH, proof systems read by size, and the Ricci-flow shrinker are running systems, each with its map into the
ledger space. **[Lean]** For Yang-Mills, GRH and NP vs coNP the step that would make the run physically or arithmetically
meaningful is exactly the open step of `UNIFIED.md`; it enters as an explicit argument. **[open]**

**The Existence Turing Machine.** One running system, the ETM, runs every computation: given a program and an input it
runs, and it reaches balance exactly when the program halts, reading off the program's value. **[Lean]**, from Mathlib's
Kleene codes. Halting splits cleanly:
- **cost above the floor** (every factor at most some theta with e^delta theta < 1): every run reaches balance within any
  epsilon, by an explicit step count `ceil(M q / (epsilon (1 - q))) + 1`. Deciding is trivial and the bound is
  computable. **[Lean]**
- **cost equal to the floor** (lossless, factor 1): this is where the ETM itself lives. Balance still has a binary truth
  for every content (classical logic: a total yes/no exists, but it cannot be run), and no machine computes it for all
  content (Turing). **[Lean]**, the second from Mathlib's `ComputablePred.halting_problem`.

So the owner's sentence "it can run any existence as content and predetermine if it halts by seeing that it does not
produce a balanced state" holds in two exact halves: it can run any computable content; it can predetermine balance on
the class whose cost exceeds the floor, and only there.

**Rooted systems.** The owner restated the thesis: every meaning of existence in accordance with the root G0, from which
the whole chain derives, with no infinite regress. Rooted means well-founded: a system is rooted when it is built from G0
by finitely many of the ledger's and the encoder's own operations (reflection, composition of steps, restriction to a
subset). G0 is a positive weight carried by a positive kernel; its simplest case is the tick, one unit of binary
existence that persists. By induction over the derivation, every rooted system is a DMP instance. **[Lean]** That is the
form layer. The content layer is checked separately: Markov chains, the SU(N) box chains, the Szego chains, the proof
certificates and the shrinker's metric are rooted, and G0 is not trivial (it carries a persisting unit of existence,
and not every running system is rooted: the shrinker's curvature is not). **[Lean]**

**What stays a thesis.** That every possible meaning of "running" is a rooted running system. Like the Church-Turing
thesis, it is about an informal notion, so it cannot be proved. What is proved is each formal notion, one by one, the
universal property, and the induction for the stated definition of "rooted".

---

## 2. The definition (`ETM/RunSys.lean`)

**Running system** (`RunSys δ`, Lean). Data, with a floor `delta` fixed for the category:

| field | meaning | from |
|---|---|---|
| `X`, `step : X → X` | states and the transfer step | the positive kernel, read as a map on what it carries (laws, weights, certificates) |
| `fac : X → ℝ`, `0 ≤ fac ≤ 1` | the encoder factor of the boundary the next step crosses | `Encoder.lean`: reflection positivity puts the factor in `[0, 1]` (`szego_mem`, `elec_mem`) |
| `mass : X → ℝ`, `mass ≥ 0` | the size of the positive weight carried (the certificate) | the positive weight or measure |
| `pays`: `mass (step x) ≤ e^δ · fac x · mass x` | the ledger law: each step pays its factor up to the floor | `Ledger.lean` (`Pays`, `Carries`) |

**Morphisms** (`Hom`, Lean): maps of states with `φ ∘ step = step ∘ φ`, `fac ∘ φ = fac`, `mass ∘ φ = mass`.
- *Subsets* (`sub`, `subIncl`, injective): an invariant subset of states. This is the owner's "subsets save the day":
  conditioning only on what the system itself defines, never on external content.
- *Factor maps* (`quot`, `toQuot`, surjective): the quotient by a relation the step, the factor and the mass respect
  (coarse-graining).
- Identity and composition make `RunSys δ` a category (`category`, Mathlib's `CategoryTheory.Category`).

**Why this is the right notion.** It is the smallest structure the five instance families share. Each family has a
step, a carried nonnegative amount, a factor in [0, 1] and a ledger inequality; nothing more is common to all five (see
"What it leaves out"). With exactly these, the universal object is the ledger itself (section 3), so the unified ledger
theorem of `UNIFIED.md` becomes one theorem on one object, pulled back to every system. With less (no factor, no
mass) the universal object collapses to a point; with more (a reflection as data) Markov chains and proof systems would
drop out.

**What it leaves out.**
- *The reflection as data.* Yang-Mills (time reflection) and GRH (conjugation) have one, Markov chains and proof systems
  do not. The reflection survives only through its consequence, the factor bound; `Encoder.lean` is the bridge
  (`szegoChain` builds an object from any chain of encoders).
- *Single configurations of a stochastic step.* A Markov chain is a running system through its deterministic action on
  laws (pairs of probability vectors), not on single configurations.
- *Branching.* The step is deterministic. Ben-Sasson and Wigderson run the ledger along a tree of restrictions; each path
  is a running system, the tree is not one.
- *Continuous time.* A flow enters through chosen discrete times (the shrinker at dyadic times).
- *Two floors at once.* The floor is one number per system. Yang-Mills has two candidate floors (2C and log mu); their
  relation is III.5.8 **[open]**.
- *Quantum content.* Coherence and entanglement are not modelled. The GUID paper's hosting proposition (a universal
  quantum computer carried as content) is argued there, not proved here.

---

## 3. The universal property and the vacuity check

**Universal object** (`univ δ`, Lean). States: ledgers (`Ledger δ`), pairs of streams `(f n, m n)` with
`0 ≤ f n ≤ 1`, `m n ≥ 0`, `m (n+1) ≤ e^δ f n m n`. Step: the shift. Factor and mass: the entries at step 0.

**Theorem (DMP's universal property)** [Lean]. For every running system `S` there is exactly one morphism
`S → univ δ`: the trace, which sends a state to its ledger (`trace`, `trace_unique`, `exists_unique_hom`). In
category language, `univ δ` is terminal (`univIsTerminal`, Mathlib's `Limits.IsTerminal`).

**Direction.** Terminal. The initial object is the empty system (`emptyIsInitial`, Lean), which carries nothing. An
adjunction is not needed: the terminal object already is the ledger.

**Vacuity check** (all Lean).

| check | result | Lean |
|---|---|---|
| is the universal object a point? | no: it has states with different factors | `univ_nontrivial` |
| does it carry every factor stream? | yes: every stream in `[0, 1]` is the factor stream of a state | `univ_fac_stream` |
| does it carry every starting amount? | yes, with a lossless factor stream paying exactly the floor | `univ_mass` |
| what if morphisms forgot factor and mass? | the one-point system would be terminal | `bare_point_terminal` |
| with them? | a system with a nonzero factor or mass has no morphism to a point | `no_hom_to_point` |
| is the floor content? | yes: for delta < delta' the lossless ledger growing at e^{delta'} is a delta'-ledger and no delta-ledger | `floor_strict` |
| do the ledger theorems factor through it? | yes: `carry`, `contract`, `decay_cost` are proved on ledgers and pulled back along the trace | `RunSys.carry`, `RunSys.contract`, `RunSys.decay_cost` |

**Subsets** [Lean]. Every running system establishes itself as a subset of the universal object: the trace is a
surjective morphism onto an invariant subset (`image`, `toImage_surjective`) followed by its injective inclusion
(`subIncl_injective`, `establishes_subset`). Two states have the same image exactly when their factor and mass streams
agree (`trace_eq_iff`).

**The certification.** This theorem, with the pulled-back ledger theorems, is the top theorem that ties the instances
together (see "The top theorem as the certification of existence" at the top). Its proof reads only the shared fields:
step, factor, mass and the ledger law.

**How deep the theorem is.** Formally it is the final-coalgebra theorem for this signature, and the proof is short.
Its weight is in what the universal object turns out to be: not a point but the space of ledgers, carrying the factor,
the cost (`−log f`) and the floor. It also says what it does not: the trace forgets everything but the ledger (the
kernel, the reflection, the gauge group). "Every running system goes through DMP" means, exactly: its ledger is a point
of the universal object, uniquely, and every ledger theorem is that point's theorem.

---

## 4. The instances (`ETM/Instances.lean`)

Each row is an object of `RunSys δ`; its map into the universal object is its trace.

| instance | states, step | factor | mass | floor | status | Lean |
|---|---|---|---|---|---|---|
| chain | `ℕ`, successor | any stream in `[0, 1]` | any stream paying it | any | [Lean] | `ofChain`, `ofChain_ledger`, `ofChainProd` |
| Markov / Dobrushin | pairs of probability laws, push through `K` | contraction coefficient eta of `K` | total-variation distance | 0 | [Lean], proved outright | `markov`, `markov_doeblin`, `markov_mixing` |
| lattice Yang-Mills, every SU(N) | boxes in series | `elec(Z_tw,k / Z)` of the SU(N) Wilson chain, in (0, 1) for beta != 0, k != 0, T even | running product | 0 | [Lean], each finite lattice | `boxFactor_mem`, `ymBoxes`, `ymBoxes_contracting` |
| Yang-Mills influence | boxes in series | the box factor | the influence handed over | log mu (O1 form) | object given the step law `hO1` **[open]** (O1 with III.5.7) | `ymInfluence` |
| GRH, Szego chain | scales | Szego factor `1 − abs(k)^2` | running product (prediction-error ratio E_n/E_0 [classical]) | 0 | [Lean] for any chain of encoders, or any coefficients in the closed disk | `szegoChain`, `szegoCoeffs`, `szegoCoeffs_pos` |
| GRH, the sign | | | | | being an object forces every `abs(k) <= 1`: the object condition is exactly the sign [Lean]; that Weil's scale steps are encoders is **[open]** beyond Dirichlet | `sign_of_run` |
| proof systems, size | restriction steps, stopped after b | `1 − theta` | number of costly lines | 0 | [Lean] given a restriction sequence; `CrossingCost` for strong systems **[open]** | `proofRun`, `proofRun_size` |
| Ricci shrinker, metric | dyadic times `t_k = (1 − 2^-k)/(2 lambda)` | 1/2 | metric scale `2^-k` | 0 | [Lean], contraction class | `shrink_dyadic`, `shrinker`, `shrinker_contracting` |
| Ricci shrinker, curvature | dyadic times | 1 | curvature `lambda 2^k` | log 2 | fits only with floor at least log 2 [Lean] | `einstein_dyadic`, `growth_needs_floor`, `curvature_needs_floor`, `curvature` |
| the ETM | (fuel, program, input), one more unit of fuel | 1 | 1 until halted, then 0 | 0 | [Lean] | `etm` |

**Where an instance does not fit, and why.**
- *Yang-Mills influence.* The SU(N) box factor is proved at every finite lattice (`sunTwistRatio_mem` with `elec_mem`),
  but that the influence handed from box to box pays it with floor log mu is the one-box statement O1 together with the
  annealed product structure III.5.7 **[open]**. The object exists only with that law as an argument. The box chain
  `ymBoxes` is in the contraction class at each lattice; this is not O1, since the factor is not bounded away from 1
  uniformly in the volume.
- *GRH.* A Szego chain is an object exactly when every reflection coefficient is in the closed disk (`sign_of_run`):
  the open sign is the object condition itself. The finite closure (`abs(k) = 1`, factor 0) fits, with infinite cost.
- *Proof systems.* A single run is one path of restrictions; the Ben-Sasson-Wigderson tree is not one run. For strong
  systems the restriction sequence with a crossing cost is **[open]**.
- *Ricci flow.* The curvature grows, so it is a run whose floor (log 2) exceeds its cost (0); with a floor below log 2 it
  is not an object. The flow enters only at chosen discrete times. The SU(N) extinction time `1/N` and the conformal
  window (`BlowupSUN.lean`) are not used.
- *Mixing chains in general.* `Mixing/Chain.lean`'s time-inhomogeneous chains (`kchain`) fit the same way with the
  time index in the state; only the homogeneous chain is built here.

---

## 5. The ETM (`ETM/Machine.lean`)

### (a) Universality in Turing's sense [Lean]

- **Describes.** A description is a Kleene code `c : Nat.Partrec.Code` (Mathlib; Goedel-numbered, `Encodable`) and an
  input `n : ℕ`. The start state is `start c n = ((0, c), n)`.
- **Runs.** The ETM (`etm : RunSys 0`) has states `((k, c), n)`, `k` the fuel spent. The step adds one unit of fuel
  (`estep`). The mass is 1 while the bounded evaluation `evaln k c n` has no value and 0 once it has one; the factor is
  1, the floor 0. Fuel monotonicity (`evaln_mono`) is the ledger law.
- `etm_runs`: for `0 <= epsilon < 1`, the ETM reaches balance within epsilon from `start c n` iff `c` halts on `n`.
- `etm_output`, `etm_output_complete`: the value read off at balance is `c`'s value on `n`, and every value is read off
  at some fuel.
- `etm_universal`: every partial recursive function `f` is run this way by some description (`Code.exists_code`).
- `estep_primrec`, `halted_primrec`: the step and the balance test are primitive recursive (`Code.primrec_evaln`).

"Any content" here means any partial recursive content. That every effectively runnable content is partial recursive
is the Church-Turing thesis **[classical, a thesis]**.

### (b) Halting on the contraction class [Lean]

- **Class** (`Contracting S theta`): every factor at most theta, and `e^delta theta < 1`. With positive factors this is
  exactly `CostAboveFloor (−log fac) delta` of `Ledger.lean` (`contracting_iff_costAboveFloor`): a cost above the floor.
- **Bound** (`balanceBound M ε q = ceil(M q / (ε (1 − q))) + 1`): a Lean `def` on rationals; `balanceBound 1 (1/1000)
  (1/2) = 1001` is checked by the kernel (`balanceBound_example`). The estimate behind it is elementary:
  `n q^n (1 − q) <= q (1 − q^n)` (`nat_mul_pow_le`, `geom_le`).
- **Theorem** (`reaches_of_contracting`): in the class, from a state of mass at most `M`, the run is within epsilon of
  balance at every step `n >= balanceBound M ε q`, for any rational `q` with `e^delta theta <= q < 1`.
- **Decided** (`reaches_iff_bounded`): on the class, "reaches balance within epsilon" always holds, and the unbounded
  search is equivalent to the search below the bound. `reaches_of_contracting'` chooses the rational bounds itself.
- **The other direction** (`not_contracting_of_persists`): content that keeps its mass above epsilon forever is not in
  the class.
- **Markov example** (`markov_mixing`): under a Doeblin minorisation with constant epsilon, two laws are within tau in
  total variation after `balanceBound 1 tau q` steps, `q >= 1 − epsilon`: the ETM bound is a mixing time.

Membership in the class is one inequality per step (theta, and `e^delta theta < 1`), checked locally, not by running.
It is decidable when theta and delta are given exactly (for example rational theta and delta = 0); for arbitrary real
data, comparisons are not decidable, and the class check is a proof obligation, as in the Yang-Mills proof box by box.

### (c) Binary global truth at G0, and no global procedure [Lean]

The owner: "For the ETM c can be restated as having a binary global truth at G0." Two parts, both needed:

- **(c1) Binary global truth.** For every content, "the ETM reaches balance" is a proposition, so classical logic gives
  it a truth value, as a total `Bool`: `etmTruth n c`, defined through `Classical.dec` (`etmTruth_spec`: it is `true`
  exactly when the ETM reaches balance; `etm_binary`: reaches or does not). The definition is `noncomputable`: the truth
  exists, but it cannot be run.
- **(c2) No machine computes it for all content.** `etm_balance_undecidable`: for every input `n` and
  `0 <= epsilon < 1`, "the ETM reaches balance within epsilon from `start c n`" is not a `ComputablePred` of `c`. It
  equals "`c` halts on `n`" (`etm_runs`), which Mathlib's `ComputablePred.halting_problem` (via Rice's theorem) shows is
  not computable. So the truth function of (c1) is not `Computable` (`etmTruth_not_computable`; both parts together:
  `etm_truth_edge`).

c1 alone would drop the edge: the truth exists everywhere, and what fails is only a procedure that finds it for all
content. With (b) the edge reads: **binary truth globally** (c1); **knowledge = truth locally**, where a settling
certificate exists (the contraction class, (b), decided with an explicit bound); **no global procedure** (c2).

`etm_not_contracting`: the ETM is lossless (factor 1, cost 0 = floor), so it is outside the class.

### The edge (`etm_edge`, `etm_round`) [Lean]

| cost vs floor | example | balance |
|---|---|---|
| cost > floor (contraction class) | Doeblin chains, SU(N) box chains, the shrinker's metric | always reached, by the explicit computable bound |
| cost = floor (lossless) | the ETM, any computation | Turing-universal; balance has a binary truth (c1) that no machine computes (c2) |
| cost < floor | the shrinker's curvature | grows; an object only with the higher floor |

(b) and (c) together are the exact edge of the ETM claim: halting is predetermined where the cost exceeds the floor, and
nowhere that includes all computable content.

---

## 6. Rooted running systems and the thesis (`ETM/Rooted.lean`)

### 6.1 The restated thesis

The owner: "Every meaning of existence that is in accordance with the root G0 through which the whole chain derives it's
physical existence, so it's extension into real space, otherwise you would just end up in an infinite series again."

Read **[reading]**: *rooted* means *well-founded*. Every derivation, followed backwards, reaches G0 in finitely many
steps, and an infinite regress is excluded [classical: well-founded relations]. In Lean an inductive definition is exactly
this: every proof of `Rooted P` is a finite tree of constructors whose leaves are G0.

### 6.2 The definition [Lean]

A **pre-system** (`Pre`) is the data of a running system without its laws: states, step, factor, mass, floor.
`Pre.IsInstance` is the law of section 2. **Rooted** (`Rooted`, an inductive predicate on pre-systems):

| constructor | operation | source |
|---|---|---|
| `root` (**G0**) | a positive weight carried by a positive (stochastic) kernel `K` and compared with a second one: the Markov system `markov K` (pairs of laws, factor a Dobrushin coefficient, mass their total-variation distance) | the positive weight and the positive kernel |
| `reflectSzego`, `reflectElec` | **the reflection**: one boundary with a positive form (an `Encoder`) per step, read through the Szego or the electric profile; factor times the profile, mass times the running product | `Encoder.lean` |
| `twice` | **composition of steps**: two steps as one, factors multiplied, floors added | `Ledger.lean` (`pays_of_submul`) |
| `subset` | **restriction to a subset**: whatever embeds into a rooted system (injective, commuting with the step, preserving factor, mass and floor) is rooted; this also covers relabelling | the owner's "establishes itself as a subset" |
| `scale`, `relax` | normalising the weight; raising the floor | |

**G0's simplest case is the tick** (`tick`): the identity kernel on `Bool`, started at binary existence
(`δ_true`, `δ_false`). Its mass is 1 and its factor is 1 at every step (`tick_persists`): one unit of existence that
persists and never balances.

**Where the extension into real space sits** [reading, with the Lean parts named]. The chain from G0 to real space is the
Osterwalder-Schrader route: positive weight, then Hilbert space, then positive transfer matrix, then real-time
evolution [classical]. In the definition:
- the positive weight is G0 (`root`);
- the Hilbert space is the reflection constructor: an `Encoder` is a boundary state in a space with a positive form.
  On the lattice the same data are `WinRP` in `OS/Window.lean` (the reflection form `Q`, the positive half `P`,
  Cauchy-Schwarz `cs`);
- the positive transfer matrix is the step. On the lattice it is `τ` in `WinRP`; `win_contraction` is the windowed OS
  contraction, `OS/Torus.lean` builds `torusWin` for the gauge field, and `M1/UVTVOS.lean` the windowed reconstruction
  that M1 uses;
- real-time evolution is **not** in the definition. A running system runs in Euclidean time, which is where the ledger
  reads decay. The continuation from `e^{-tH}` to `e^{-itH}` is the reconstruction theorem [classical], formalised here
  only in its lattice and windowed parts; the continuum limit is outside the Lean.

### 6.3 The form layer: every rooted system is an instance [Lean]

`Rooted.good`, by induction over the derivation: every rooted pre-system satisfies the law (it is a running system)
and its mass never increases. `rooted_is_instance`: it is a DMP instance with its unique trace into the ledger space
(section 3). The case analysis is the whole proof: G0 satisfies the law (Dobrushin, `tv_pushv_le`), the reflection keeps
it (positivity puts the profile in `[0, 1]`, `szego_mem`, `norm_refl_le`), and so do composition, subsets, scaling and
raising the floor.

This theorem is close to a tautology, and that is the design: it holds for every content because it says nothing about
content (the owner: "The trap is the one nice thing about DMP that enables it all"). Its use is to transport: whatever is
proved of rooted systems in general holds for each instance. Its non-vacuity is checked in the content layer below.

### 6.4 The content layer (i): the known systems are rooted [Lean]

| system | derivation | where the instance's own content enters | Lean |
|---|---|---|---|
| Markov / Dobrushin chains | G0 itself | the kernel's Dobrushin coefficient | `markov_rooted` |
| SU(N) box chains, every N | tick, electric reflection by an encoder with coefficient `Z_tw,k / Z`, subset | the strict twist bound `0 < Z_tw,k < Z` (`sunTwistRatio_mem`) puts the coefficient in the disk, so a positive form carries it | `ymBoxes_rooted` |
| Szego chain of encoders (GRH) | tick, Szego reflection, subset | the encoders themselves | `szegoChain_rooted` |
| Szego chain of coefficients (GRH) | tick, Szego reflection by encoders realising `abs(k_i)`, subset | the sign `abs(k_i) <= 1` (for Weil's chain, the open step beyond Dirichlet) | `szegoCoeffs_rooted` |
| proof systems, the certificate | tick, Szego reflection with factor `1 − theta`, scaled by the number of costly lines, subset | the restriction steps bound the costly lines by the certificate | `proofCert_rooted`, `proof_certified` |
| Ricci shrinker, metric | tick, Szego reflection with factor 1/2, subset | the dyadic scale `2^-k` (`shrink_dyadic`) | `shrinker_rooted` |

The reflection constructor accepts a coefficient exactly when a positive form carries it: encoders realise exactly the
closed disk (`encoder_realize` with `norm_refl_le`; every factor in `[0, 1]` is a Szego factor, `szego_realize`). So each
derivation uses its instance's own content at one place, the reflection: the twist bound for Yang-Mills, the sign for
GRH.

**What is rooted, and what is not.**
- For the Yang-Mills influence and for refutations, what is rooted is the **certificate** (the product of the box
  factors; `|Q 0| (1 − theta)^i`), not the physical quantity. That the influence is dominated by its certificate is O1
  with III.5.7 **[open]**. For refutations it follows from the restriction steps (`proof_certified`, Lean); the crossing
  cost that supplies those steps for strong systems is **[open]**.
- **The shrinker's curvature is not rooted** (`curvature_not_rooted`, Lean): it satisfies the law with floor log 2, but
  its mass grows and rooted masses never do. A blowup is not derived from G0 by these operations.
- **The ETM** is an object of the category, but its rootedness is not shown here. Its mass drops from 1 to 0 at a factor
  of 1, which no reflection produces; whether it embeds into a rooted system is not settled in this round.

### 6.5 The content layer (ii): G0 is not trivial [Lean]

| check | result | Lean |
|---|---|---|
| does G0 carry anything? | yes: the tick keeps one unit of existence at every step and never balances | `tick_persists` |
| do rooted systems realise every factor and mass? | yes: every factor in `[0, 1]`, every starting mass `>= 0` | `rooted_factor_mass` |
| is every running system rooted? | no: the shrinker's curvature is a running system (floor log 2) and is not rooted | `curvature_not_rooted` |
| does the form theorem say more than the law? | yes: rooted masses never increase (`Rooted.good`), which running systems with a positive floor can violate | `Rooted.good`, `curvature_not_rooted` |

`rooted_round` collects the form theorem and the three checks in one statement.

### 6.6 What remains a thesis

**The ETM thesis, restated.** *Every meaning of running that is rooted in G0 is a rooted running system in the sense of
6.2.* Its informal outer edge is still "every possible meaning of running", now limited to the rooted ones. Like the
Church-Turing thesis it relates an informal notion to a formal one, so it is not a theorem and cannot become one. The
evidence is the same kind: each formal notion examined so far is rooted (6.4), and the definition is stable under its own
operations. What would refute it is a meaning of running, derived from G0 without regress, that needs an operation the
constructors lack. The known places where the definition is a choice are in section 2 (branching, continuous time, two
floors, quantum content), plus growth (the curvature).

Proved, relative to the definitions: the universal property (section 3), the instances (section 4), the edge (section
5), and the induction with checks (i) and (ii) (this section). Not proved and not claimed: O1, GRH beyond Dirichlet, NP
vs coNP. The ETM adds no evidence for any of them: it states each as the one law a particular run must obey to be an
object (Yang-Mills, proof systems), or as the condition for the reflection constructor to apply (GRH's sign).

---

## 7. DMP identifications (all [reading])

| DMP | in the construction |
|---|---|
| a DB, "establishing existence as a subset" | an invariant subset of a running system, `sub`; every system establishes its image in the ledger space (`establishes_subset`) |
| the ETM "runs any existence as content" | `etm_universal`: any partial recursive content, from a description |
| "predetermine if it halts by seeing it does not produce a balanced state" | `reaches_of_contracting` on the contraction class; impossible in general (`etm_balance_undecidable`) |
| the coupling (lossiness) | the factor `fac` |
| the tick | the floor delta, one per category |
| the hand-over point | membership in the contraction class: one finite check certifies balance for every run of the system |
| "a theorem proven inside a DB is true everywhere" | the ledger theorems are proved once on the universal object and pulled back along every trace (`RunSys.carry`) |
| the arrow of causality | the step and the floor are the same at every state |
| G0, the root | `root`: a positive weight carried by a positive kernel; its simplest case the tick, one persisting unit of binary existence |
| "otherwise an infinite series" | well-foundedness: `Rooted` is inductive, every derivation is a finite tree with leaves at G0 |
| the `.cmb` file that proves its own recipe | the description `c` the ETM runs (a Kleene code); the ETM's step is primitive recursive |

---

## 8. Files

| File | Content |
|---|---|
| `ProofPhase/ETM/RunSys.lean` | `Ledger`, `RunSys`, `Hom`, the category, `univ`, `trace`, `trace_unique`, `univIsTerminal`, the pulled-back ledger theorems, the vacuity checks, `sub`, `quot`, `image`, `establishes_subset` |
| `ProofPhase/ETM/Machine.lean` | `Contracting`, `balanceBound`, `reaches_of_contracting`, `reaches_iff_bounded`, `etm`, `etm_runs`, `etm_universal`, `estep_primrec`, `etm_balance_undecidable`, `etm_edge` |
| `ProofPhase/ETM/Instances.lean` | `ofChain`, `markov`, `boxFactor_mem`, `ymBoxes`, `ymInfluence`, `szegoChain`, `sign_of_run`, `proofRun`, `shrinker`, `curvature_needs_floor` |
| `ProofPhase/ETM/Rooted.lean` | `Pre`, `Rooted` (G0 and the constructors), `Rooted.good`, `rooted_is_instance`, `encoder_realize`, `tick`, `tick_persists`, the rooted instances, `curvature_not_rooted`, `rooted_round` |
| `ProofPhase/ETM/ETM.lean` | `emptyIsInitial`, `etm_round` |
| `docs/unified/etm-axioms.sh`, `etm-axioms.log` | build, `#print axioms` for all 154 declarations, source grep |

Build (WSL replay distro): `FORMAL_DST=~/formal-etm bash docs/mass-gap/formal/sync-build.sh ProofPhase.ETM.ETM`, or
`bash docs/unified/etm-axioms.sh > docs/unified/etm-axioms.log 2>&1` from the repository root.

Imported, not edited: `Unified/Ledger.lean`, `Unified/Encoder.lean`, `Unified/ProofSize.lean`,
`Unified/BlowupSUN.lean`, `Mixing/Chain.lean` (with `Doeblin.lean`), `General/SUNTwistWilson.lean`; cited, not
imported: `OS/Window.lean`, `OS/Torus.lean`, `M1/UVTVOS.lean`; Mathlib's
`Computability` (`Nat.Partrec.Code`, `ComputablePred.halting_problem`) and `CategoryTheory`.
