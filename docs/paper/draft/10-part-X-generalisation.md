# Part X. The generalisation: what the cards show together

*Draft 3, 2026-11-24. Claim labels (X.n) are listed in `../CLAIMS.md`; the labels new in this draft (X.8 onward) are in
`../claims-incoming/X-generalisation.md` until the coordinator merges them.*

## 0. How to read this part

Parts III to IX each end at a **card**: an input, a proved structure, and exactly one named open step. This part puts the cards
side by side. It says what they share, why each still has one open step, and why that step cannot be removed by a trick.

Nothing here solves a problem. Every section below ends in an open statement, and each open statement is the same one that the
card's own part already names. What is new is the *shape* the open statements share. Section 1 names what every card needs before
its one box can run at all: a containing existence with free possibility space. Sections 2 and 6 are exact: they are theorems in
Lean about one geometry. The others are readings of that geometry, and they are marked.

Marks as in Part I: **[Lean]**, **[classical]**, **[external]**, **[conditional]**, **[paper]**, **[numerical]**, **[reading]**,
**[open]**. Lean paths are relative to `docs/mass-gap/formal/ProofPhase/`.

---

## 1. The container: a containing existence with free possibility space

**The one box.** Each card ends in a statement about one box. In DMP terms the box is the *confined inside*: its existence is
binary (it is, or it is not), and it is free to assert itself. The inside pays nothing to exist, but it cannot exist alone. It
exists only as an assertion *against an outside*: it asserts itself simply by being not that. Without anything to prove to an
outsider that it exists, does it exist? **[reading]** (claim X.54).

**What the outside must be.** The outside is where locality and causality live. For the box to run in a DMP-complete way, the
outside must have two properties:

* **Free.** It leaves the possibility space free: something might happen, but it need not. In numbers, 0 < p < 1, with p the chance
  that a crossing inverts the box's binary sector. p = 0 is a forced act (order, no gap). The possibility space is what makes each
  crossing contract, by the factor abs(1 - 2p) < 1. Causality in this sense and the gap are one condition.
* **Complete.** Every configuration has positive weight: a compact group, a finite action, "every possibility exists". Nothing is
  excluded in advance, so nothing has to be added later.

This part calls the two together the **container**: a containing existence with free possibility space. **[reading]** (claim X.55).

**What is proved about it.** Two halves are in Lean for Yang-Mills; the third is a hypothesis.

* *Complete.* The transfer kernel at a fixed cross-section is strictly positive: every configuration has positive weight
  **[Lean]** (`Flip/Bound.lean`, `stepK_pos`; III.1.7).
* *Free, from above.* The twisted partition function is strictly below the untwisted one at every coupling beta != 0, so
  p = Z_tw/(Z_tw + Z_0) is below one half **[Lean]** (`Flip/Strict.lean`, `su2_Ztw_lt_Z`; III.1.6).
* *Free, from below.* 0 < p needs 0 < Z_tw, which the Lean statement carries as a hypothesis (`Crossover/HandOver.lean`,
  `su2_handover`; III.3.1). The integrand is positive, but the formal step is not written. Keeping p bounded away from 0 as the
  box grows is the open step (section 4).

The strict facts are cross-references to III.1.6, III.1.7 and III.3.1 (claim X.56).

**The container is the quantifier of the one-box statement.** In every card, the container shows up as one "for every":

| Card | The for-every that the container asks | Status |
|---|---|---|
| Yang-Mills | the hand-over inequality for every outside, or for every *running* outside | named hypotheses `HandoverSide`, `HandoverSideRunning` **[open]**; their relations **[Lean]** |
| GRH | Weil's form positive for every square-integrable test function on the support (the one-box certificate is "for every f") | certified at supports up to a = 0.69 **[numerical]**; the abstract step **[Lean]** |
| NP vs coNP | every assignment: a refutation certifies that every assignment falsifies some clause | **[reading]** on **[Lean]** refutation completeness |
| Settling machine | total freedom inside, one verified gate | **[reading]** (Part XI) |

* **Yang-Mills.** `HandoverSide` says: for every cutoff, every nontrivial sector and every end-face outside, the hand-over slab
  has the electric side at most sqrt 2 - 1 of the neutral one. It is O1 at mu = 1 + sqrt 2 at the single length L_h **[Lean]**
  (`Unified/ElectricSUNPress.lean`, `HandoverSide`, `handoverSide_iff`). `HandoverSideRunning` quantifies only over *running*
  outsides, those in the running set R of the measure, and the all-outsides form implies it **[Lean]**
  (`Unified/ElectricSUNRunning.lean`, `HandoverSideRunning`, `handoverSideRunning_of_handoverSide`). Both statements are named
  hypotheses and **[open]** (claim X.57). The owner's reading of the frozen outsides: they are not running outsides, so they are not
  quantified over, but their ticks of not counting count as remnants. Each enters only through its weight in the measure, an
  exponentially small probability epsilon. Every factor is at most 1, so the join pays epsilon at most: a fresh uncertainty r = epsilon in
  the transport theorem (II.9) **[reading]** for the identification, **[Lean]** for the transport (`runningTransport_slab`,
  `runningTransport`) (claim X.57b). The assemblies `O1_slab_running` and `O1_box_running` take the running side, the remnant bound
  and the seam as hypotheses. They are not O1.
* **GRH.** The one-box certificate splits a test function f into a finite part u and a tail g, and certifies three inputs: the
  finite part, the cross term and the tail. From them the positivity of Weil's form follows for *every* f in the space
  **[Lean]** (`GRH/OneBoxCert.lean`, `schur_scalar`, `onebox_positive`) (claim X.58b). The three inputs are numbers computed in ball arithmetic
  at supports a = 0.60, 0.65 and 0.69, the universal start `{infinity, 2, 3}` **[numerical]** (`docs/unified/GRH-ONEBOX-CERT.md`).
  Beyond a = 0.69 the same "for every f" is the open step of Part IV (claim X.58).
* **NP vs coNP.** A refutation is a certificate that every assignment falsifies a clause. Resolution is sound and refutation
  complete (I.4a, V.3.1) **[Lean]**. Reading the "every assignment" as the container's quantifier is **[reading]** (claim X.59).
* **The settling machine.** Total freedom inside one verified gate: inside, anything may happen; at the gate, every act is checked
  for integrity and freshness, not meaning **[reading]** (XI.1, XI.3; claim X.60).

**Care point: the container is also where the open step sits.** The container is the precondition the cards share, not a result.
O1 is exactly the requirement that the one box holds for every outside, uniformly in the scale. The same words, "for every
outside", state the container and state the open step. That is why no card can prove it from inside: an inside cannot supply its
own outside (section 4). **[reading]** (claim X.61).

**How the care point is answered.** By construction, not by a further proof inside the cards. The owner's answer: the care point
comes from the construction of G0 and the established process by which it gets there. The process from G0 to the hand-over (the
ODP, I.5) is one established process. Once that is accepted, every start gets a direction through `{infinity, 2, 3}`. Accepting it
is the paper's one assumption, stated once in section 4.4 and not proved. At the start itself the sign is certified (section 6).
For every later tick the direction holds only *conditional on the acceptance*. **[reading]**; the status of each part is marked in
section 4.4 (claim X.63).

**Where section 2 follows from this.** The container asks two things of each tick. From the inside, the box must keep what it
holds: a margin is carried from one scale to the next. From the outside, the box must refute what must not be: the twisted
sector is suppressed at every box. Section 2 shows that these two requests are the two edges of one band of per-tick factors, and
what Lean says about them **[reading]** (claim X.62).

---

## 2. One geometry, two edges

**From the container.** Section 1 asked two things of every tick: carry a margin from the inside, refute the twisted sector from
the outside. The geometry below is where both are measured, in one number.

**What is shared.** GRH (Part IV) and the Yang-Mills one-box step O1 (Part III) read the same object. At a boundary, an encoder
has one number, the reflection coefficient c. Its distance d from the lossless point (c = 0) is one hyperbolic distance. Two
loss factors are functions of that one distance:

* the electric factor is e^{-d};
* the Szego factor 1 - |c|^2 equals 4 e^{-d} / (1 + e^{-d})^2, which is 1 / cosh^2(d/2).

The cost -log of the electric factor is the distance d, and the Szego factor is the second function of d: both are **[Lean]**
(`Unified/GRHLens.lean`, `elec_cost`, `szego_of_elec`; the cosh form is a rewriting of the second) (claim X.8). The ledger is also shared:
`Pays`, `carry` and `Ledger.contract` are one theorem for both problems (II.9) **[Lean]**.

**What they ask of it.** They ask opposite things, one-sided and on different encoders:

| Statement | In the tick's distance d | On which encoder | Status |
|---|---|---|---|
| GRH, the sign | d is finite at every tick (abs(k_N) < 1) | Verblunsky step k_N of the zero measure, one per scale | **[open]** (claim X.9) |
| GRH, multiplicative transport | d_N <= D uniformly: every tick loses little (factor at least e^{-D}) | same | **[open]**; enough for the sign, not needed by it (claim X.9) |
| O1 | d >= kappa > log mu for every outside: every box loses a lot (factor at most e^{-kappa}) | twist ratio Z_tw/Z of the hand-over box, one per outside | **[open]** (III.5.6) |

In words. **GRH asks every tick to lose little**, so that a margin is carried from the start to every scale. What exists, stays.
**O1 asks every box to lose a lot**, so that the twisted sector is refuted. What must not exist, is removed. The two are the
lower edge and the upper edge of one band of factors, e^{-D} <= f <= e^{-kappa}, with kappa > log mu **[reading]** (claim X.15).

**What Lean proves about the pair** (`Unified/GRHToO1.lean`, new in this draft; `docs/unified/GRH-TO-O1.md`):

1. **O1 is the uniform ratio bound, and a strict margin.** O1 holds exactly when some mu' > mu has mu' p1 <= p0 for every outside,
   with p0 and p1 the two electric sectors of the box. Equivalently, the sector form p0 - mu p1 is at least delta p1 for one
   delta > 0, uniformly **[Lean]** (`ymOneBox_iff_ratio`, `ymOneBox_iff_margin`, `cost_eq_log_ratio`; the encoder form is
   `Unified/Encoder.lean`, `oneBox_iff_refl`). So the "uniform ratio bound" earlier rounds named as the missing bridge is not a
   smaller statement than O1. It is O1 (claim X.10).
2. **They exclude each other on one tick sequence.** Take one sequence of ticks whose encoders stay at least theta > 0 from the
   lossless point (O1 at each tick). Then the Szego product, the carried margin, falls below every m > 0. A uniform margin and O1
   at every tick cannot both hold **[Lean]** (`o1_ticks_kill_margin`, `uniform_margin_excludes_o1`) (claim X.11).
3. **Each holds without the other.** Lossless ticks transport a margin and fail O1. Factors 2^{-n}/(2 mu) satisfy O1 and transport
   nothing **[Lean]** (`transport_not_decay`, `decay_not_transport`) (claim X.12).
4. **Birkhoff's bounded diameter is neither.** On the two-sector cone, a bounded spread of the image and O1 are independent:
   bounded spread with O1 false (all ratios 1), and O1 with unbounded spread (ratios e^{-n}/(2 mu)) **[Lean]**
   (`spread_without_o1`, `o1_without_spread`). O1 is a *location* of the image, on the far side of the ray at ratio 1/mu. It is not
   the image's *size* (claim X.13).

**What does not follow.** The shared thing is a geometry and a role, not one statement that could be proved once for both. No implication
between GRH and O1 is proved either way: in the card form "GRH implies O1 on every input" would be a disproof of GRH (claim X.16), and
the finite model carries a margin of exactly zero (claim X.17). Both stay open. No known object has both the zero measure's Verblunsky
steps and the box's sector ratios as its ticks, and no known result supplies either edge of the band: it is two open statements in
one geometry **[open]** (claim X.14).

**Why "GRH implies O1" is empty in the card form.** The cards take their content as input. Some Yang-Mills input breaks O1. So for
any statement H, "H implies that every input meets the open step" is equivalent to "not H". For Mathlib's Riemann hypothesis, for
Dirichlet GRH and for the GRH card's own open step, a proof of "GRH implies O1 on every input" would therefore be a disproof of
GRH **[Lean]** (`imp_all_iff_not`, `badInput_not_open`, `rh_imp_card_iff`, `dirichlet_imp_card_iff`, `grhCard_imp_card_iff`)
(claim X.16). A real bridge must be input-specific: a statement that mentions the box's sector weights and zeta's zeros together. That
statement is named exactly, `ZetaCoupling`: one bound on the sector ratio, valid for every outside, controlled by RH. The coupling
and RH give O1, and O1 alone gives the coupling, so the coupling is no easier than O1 **[Lean]** (`o1_of_coupling`,
`coupling_of_o1`); its content for four-dimensional SU(N) is **[open]**, and no theorem relates such Wilson weights to zeros of zeta
(claim X.19).

**The positivity GRH supplies has margin exactly zero.** In the project's finite model with k zeros, the card's open step (the
form is nonnegative at every scale) puts Weil's form at scale k at a null vector. So the form is positive with margin 0, and no
positive margin is certified at that closure **[Lean]**
(`exists_null`, `toepForm_atoms_null`, `no_margin_at_closure`, `grh_margin_exactly_zero`) (claim X.17). And positivity does not choose
the side: positive weights in both sectors with O1 false exist for every mu >= 1 **[Lean]** (`positivity_without_o1`) (claim X.18). Both
problems have a proved *sign*. O1 needs a *margin*, for a different form, at a different place.

**The one model where zeta is the partition function.** Two-dimensional SU(2) on a closed surface of genus g >= 2 has, in the
zero-area limit, the partition function zeta(2g - 2) **[external]** (Witten, CMP 141, 1991) (claim X.21). The two electric sectors are
2^{-s} zeta(s) and (1 - 2^{-s}) zeta(s) with s = 2g - 2. Zeta cancels from every ratio, so the O1-type quantity there is one Euler
factor, at the prime 2, and no zero of zeta enters **[Lean]** (`Ze1_eq`, `Ze0_eq`, `zeta_re_eq`, `sector_dom_iff`,
`twist_ratio`) (claim X.20). Two dimensions have no outside, so the hard part of O1 has no counterpart on the zeta side.

---

## 3. Existence and falsifiability: the duality of construction

**The owner's reading.** The owner puts the difference between the two edges in one sentence. GRH asks that something *exists*.
O1 asks that something is *falsifiable*. Together they are the duality inherent in the construction of a DMP-complete system:
what is prescribed to exist, and what is prescribed to be refuted **[reading]** (claim X.23).

In the band of section 2 the reading is exact in this sense:

* **GRH's edge** asks that the margin exists at every tick. A witness stays.
* **O1's edge** asks that every twisted state is refuted at every box. A bound, whose violation would show up as a failure at one
  box.
* They are the two sides of the existence boundary (I.3), and the same duality as "it exists, or it is answered R136a1" at each
  tick (section 5).

**Care point: as whole statements the logical forms are crossed.** RH, and by the notes also GRH for Dirichlet L-functions, is a
Pi-0-1 statement: one computable counterexample refutes it **[classical]** (Lagarias' criterion; Davis-Matiyasevich-Robinson;
cited as the project notes cite them, not re-read here) (claim X.24). The Yang-Mills problem asks for an existence: a continuum theory
with a gap **[classical]** (the Clay statement) (claim X.25). So each problem, stated whole, has the logical form of the *other's role* in
the band. The duality appears twice: once in the roles, once, mirrored, in the statements **[reading]** (claim X.26).

Two further care points keep this honest. First, "falsifiable" is a word about the role, not a theorem: the sector weights of O1
are integrals, not finite computations, and a measurement can refute or guide but never establish a for-all statement (0.5;
III.7). Second, neither word classifies the open step as easy or hard. It says which edge of the band the step guards.

---

## 4. Why O1 is always the open step

### 4.1 One named slot per card

Every problem the project treats has the same three parts:

1. a well-defined **input** (a chain of boxes, a model of zeros, a proof system);
2. a **proved structure** on it: a quantity carried along steps that each pay a price, with the theorems that follow for every such
   chain;
3. **one named open step**: the statement about the running state that nobody has proved.

The form layer gives parts 2 and 3 a fixed Lean shape (II.12): a `Problem` card with an input, one `OpenStep` slot, a conclusion,
and a proof that the open step gives the conclusion. Nothing is ever an axiom: a slot is a hypothesis **[Lean]**
(`API.lean`, `Problem`, `Problem.holds`, `OpenStep`, `External`). The three cards of Parts III to V are written in this shape in
`API/YangMills.lean`, `API/GRH.lean` and `API/NP.lean`. The cards for Parts VI to IX are written by the owners of those parts and
are not restated here (claim X.27).

| | Yang-Mills (SU(2)) | GRH (beyond Dirichlet; independently for Dirichlet) | NP vs coNP (via proof complexity) |
|---|---|---|---|
| **The one object** | one box of fixed physical size | Weil's form at every support, from arithmetic alone | a cost measure on cutting-planes lines |
| **The open statement** | F_e(L) - 2c(L) > log mu_4 = 1.91, the excess act included, uniformly over every well-defined outside (III.5.6) **[open]** | lambda_min(a) >= 0 at every support, built from the primes, the characters and the real place without the zeros; eight faces (IV.4) **[open]** | interface hardness at width 3: a superpolynomial lower bound on dag-like protocols for the falsified-clause search of a random 3-CNF (V.4.10) **[open]** |
| **Proved for one unit** | max(F_tw, F_e) >= 0.881 per box (III.3.1) **[Lean]** | positivity in finite models (IV.1) **[Lean]**; each prime step numerically (IV.3.2) **[numerical]** | duality floor (e + 1)/2 for unit thresholds (V.4.5) **[Lean]**; every refutation crosses (V.4.3) **[Lean]** |
| **Why the unit does not carry** | 0.881 covers a chain (two channels), not a grid; path entropy log mu_4 beats it in d >= 3 (III.4.1, III.5.4) **[Lean]** | only the full set of primes is positive; place-by-place and two-term assembly fail (IV.3.5, IV.3.7, IV.3.8) **[Lean]** + **[numerical]** | weighted lines are cheap in both channels; one line aggregates its units (V.4.4, V.4.6) **[Lean]** |
| **What no duality supplies** | 't Hooft's relation forces nothing for n >= 2 sectors (III.4.4) **[Lean]** | the functional equation allows off-line pairs (IV.2.1, IV.2.2) **[Lean]** + **[classical]** | the duality floor fails for weighted lines (V.4.6) **[Lean]** |
| **The quantifier that makes it hard** | every outside (worst case, not typical) | every support, with margin 1e-9 | every refutation, of a structureless formula |
| **What measurement says** | passes centrally at L = 6, beta 2.3; not certified (III.7.1) **[numerical]** | holds at every step computed, by exact cancellation (IV.3.2) **[numerical]** | no measurement bears on a lower bound |
| **The "it runs" form** | the positive norm is free (RP); the margin eta < 1 is missing | the margin is not needed; the positive norm (Weil) is missing | the "it runs" object is the dag-like protocol; its size is missing |

The table is a summary of Parts III to V and their proved obstructions **[paper]** (claim X.2a). The shape in the table is one shape: a
positivity, or a certificate, is known for one unit; what is missing is that it holds for every case at once, without loss, and no
assembly with slack can supply it **[reading]** (claim X.1). The last row is formal for the first two problems: `runs_two_targets`
(`Crossover/Runs.lean`) and `runs_and_mirror_on_line` (`GRH/Tate.lean`) state the two targets side by side **[Lean]** (claim X.2b). For
NP vs coNP it is the notes' identification of the size-indexed object for cutting planes (`CP-DUALITY.md`, 0.5) **[paper]** (claim X.2c).

Only in Yang-Mills is the starting positivity given by construction: e^{-S} >= 0 together with locality gives reflection
positivity, and the chain of II.0 runs from it. GRH lacks an arithmetic G0 in which Weil positivity is a construction, and P vs NP
lacks a description language in which the existence of every instance is local **[paper]** (observation on II.1) (claim X.5). This is
the content of the last row, and of II.1.

### 4.2 Why the open step is the same slot every time

The owner's statement: the assertion of a DMP-complete running system must always be the open step. The reading has two senses.

* **Structural.** By construction every card's open step is the running-state hypothesis R: "this object runs". The form layer
  proves everything else. Each named hypothesis of the three bridges (section 7) says that its object is in a running state **[reading]**
  (claim X.28); the implication from R to the conclusions is **[Lean]** (claims X.7n, X.7m).
* **Logical.** A system cannot certify its own running from inside. A consistent theory strong enough for arithmetic cannot prove
  its own consistency **[classical]** (Goedel II), and the settling machine cannot decide balance for all content **[Lean]**
  (II.11). So the certificate of running comes from the containing system. **[reading]** (claim X.29).

Care point (claim X.29): "open from inside" is not "unprovable". O1 is a statement about the Wilson measure that ordinary mathematics,
the containing system, may well prove. What is always true is that the system cannot supply it, and that here it is the last
statement to be made. The same reading applies to DMP itself: its own running assertion is its O1, the one statement it cannot
certify from inside **[reading]** (claim X.29).

### 4.3 The dichotomy that makes the step decidable

The settling machine (II.11) has two sides. With a floor, meaning every step pays a cost above the floor, balance is reached within
an explicit number of steps, so "settled or not" is decidable **[Lean]** (`reaches_of_contracting`, `balanceBound_ge`,
`contracting_iff_costAboveFloor`). Without a floor, at cost equal to the floor, no procedure decides it for all content **[Lean]**
(`etm_balance_undecidable`, `etm_edge`) (claim X.30; these are XI.2a and XI.2b, stated once in II.11).

**The gap at G0.** The owner's reading: at G0 a gap and an arrow have to be established. The gap is what turns the gate's answer at
each tick into a binary one (it passes, or it is outside). The arrow orders the ticks, so a later excision is a later tick and never
a revision of an earlier one **[reading]** (claim X.31). Confinement is the gapped regime in which this holds. Care point: in Lean the
floor is a hypothesis of the settle theorem; for Yang-Mills in the continuum, establishing it is O1 itself. So this reading names
why O1 is the step every construction rests on. It does not close it.

**The floor at the error bars.** The owner's reading: the floor is at least the existence tied to the error bars. A floor is never
zero, because every assertion carries an error bar, and a finite resolution is a cost above zero. In the settle theorem this gives
settling to within the error bar in an explicit number of steps, with the floor as a hypothesis **[Lean]**
(`reaches_of_contracting`, epsilon the error bar) for the implication, and **[reading]** for the identification (claim X.32). The
continuum is the limit in which the error bar goes to zero. Keeping the floor positive in that limit is O1 **[open]** (claim X.33).

The circle to avoid (claim X.34): it would be circular to justify O1 by "the floor is at least the error bar" and then to justify the
error bar by O1's rate. The settle theorem takes the floor as a hypothesis. That keeps the argument honest **[paper]** (observation
in `docs/unified/GRH-TO-O1.md`, section 6).

The floor reading also corrects a tempting derivation. GRH supplies the *sign*, not the floor: in the finite model its form is
degenerate exactly at the closure, the opposite of a floor (claim X.17). So the floor reading describes what O1 would deliver, not
something GRH delivers **[reading]**.

**Only a decidable start is DMP-complete.** The owner's reading: a class that positivity cannot act on, such as a Z/2 class, is
the undecidable side, and a system is DMP-complete only when its start forces a decidable reading from rotation. Exact counterpart:
a floor is an order statement, and Z/2 carries no order, since no ordered ring has characteristic 2 **[classical]** (claim X.70a).
The one-box test has exactly the two regimes of this section: with a floor it is a finite check, without one it is undecidable
**[Lean]** (`rotation_edge`, claim X.68c). The start `{infinity, 2, 3}` is where the floor is forced, Weil's form positive with
explicit margins (claim X.65). So "DMP-complete" in the paper's sense reads as "the start forces a floor" **[reading]** (claim X.70).
Care point: the start forces the floor at the start only; keeping it at every scale is the one assumption (claims X.64, X.66).

---

### 4.4 The paper's one assumption

This is the one place where the paper states what it assumes. Every result that uses it is marked **conditional** on it. The gates
ask for it proved. It is not proved here.

**The assumption (the established process).** The process from G0 to the hand-over, the ODP (I.5), is one established process:
pressing, then minting, with the certified start `{infinity, 2, 3}` as its first tick. Accepting that the process is established
means accepting that the running state is reached: the one box is a running, DMP-complete system. In DMP terms this is the
MP-type existence assumption. In each card's terms it is the open step, O1 for Yang-Mills (section 4.2: "this object runs").
O1 is then the *corollary* of running, slotted as the named hypothesis R of the transport theorem (claim X.7n). **[reading]**
for the identification; **[open]** as a statement about each object (claim X.64).

**DMP-complete, defined.** The owner's definition: DMP-complete means *runs on DMP*. In this paper's terms an object is DMP-complete
when its running-state hypothesis R holds (section 4.2). The definition is circular in the way DMP itself is: whether R holds cannot
be certified from inside (claim X.29) **[reading]** (claim X.64b).

**One assumption, two edges.** The running state has the two edges of section 2. Its upper edge is decay: O1. Its lower edge is that
the running does not collapse: for Yang-Mills, a correlation bounded below uniformly in the scale (III.9.5b). In the spectral model
neither edge implies the other, and both fit one window **[Lean]** (model; `gap_not_lower`, `gap_and_lower_compatible`). The owner's
reading puts both in the one assumption: the ODP runs before any start and ends only once a dimensionless 1 is reached, so a
DMP-complete system carries a unit, and with it a correlation that does not vanish, by construction. In Yang-Mills the unit is
Lambda: every physical quantity is a pure number times a power of it (I.5) **[classical]**, and a vanishing correlation would leave no
non-zero such number **[reading]** (claim X.64a). So Yang-Mills carries one assumption with two edges, not two assumptions. The
owner places the lower edge exactly at the ODP's end, which delivers the start `{infinity, 2, 3}`; from there the rest follows for a
DMP-complete system with nothing more to show. So the lower edge is **conditional** on the one assumption in the same way as the
direction of every later tick (claim X.66), and without the assumption it is unproved, as O1 is (III.9.5b).

**The one-box certificate.** The author's reading: every tick can be reconstructed from any scale, so the one step can be
certified as soon as it works on the box. In the one-box test (I.8) the induction is a theorem: a marker correct at the start and
kept correct by one step at the shared gate is correct at every tick **[Lean]** (claim X.68). The scale version is a theorem *from*
the one assumption: if every scale's box is rebuilt from the one box through its gate, a box certified at one scale is correct at
every scale, and one scale with a wrong marker refutes the sharing **[Lean]** from X.64 as a named hypothesis (claim X.68a).
Sharing the gate alone is free; the content of X.64 is that the marker travels with it (claim X.68b). The author grounds the
sharing in GRH: it gives meaning to anything translated through it, so once it is assumed a valid encoder, correctness can be
inferred. In the test that is exact. A valid encoder between scales is the shared gate, and correctness at every scale is inferred
from it **[Lean]** (`scale_certificate`); what an encoder carries keeps its reflection coefficient **[Lean]** (`refl_map`). Care
point: a valid encoder keeps the same margin at every scale, and the margin is the floor, which GRH alone does not supply
(claim X.17). So assuming the encoder valid is X.64 itself, and "certified on the box, hence everywhere" is **conditional** on it
(claim X.68d). The universal machine is a box too: its DMP-completeness is undecidable over all content, and on the
contraction class it is a finite check, the dichotomy of 4.3 in the test's terms **[Lean]** (claim X.68c).

**The rigid start and the language of the encoder.** The owner reads Poincare for SU(N) (VI.6.3j) as fixing the start. Among
SU(N) the homotopy type determines the manifold exactly for N = 1, 2, 3, and the circle U(1) is rigid too **[paper]** (VI.6.3k).
So the largest start built from SU(N) that a description can certify is the point with 2 and 3, the shape of `{infinity, 2, 3}`
**[reading]** (claim X.69). The encoder is a norm-preserving map of an inner product space **[Lean]**; the determinant-1
norm-preserving maps of C^N form SU(N), and every compact Lie group sits inside some U(N) (Peter-Weyl) **[classical]**. In the
owner's words SU(N) is the language the encoder speaks, and every other compact group speaks inside it (claim X.69a). Speaking (a
valid encoder, the shared gate) and being understood (a correct marker) give DMP-completeness at every scale **[Lean]**
(`scale_certificate`; claim X.69b). So anything that rotates correctly from the rigid start is correct if DMP is correct:
**conditional** on X.64 (claim X.69c). Care points: this covers SU(N), not every conceivable start; and "other compact groups do not
survive rotation" is open. If surviving means rigidity, Sp(2) = Spin(5) and G2 pass the rational test that excludes SU(N), N >= 4,
and their rigidity was not checked (claim IX.6j). The owner's further reading settles what matters: only U(1) carries content across
the gate. Sp(2) and G2 have only self-conjugate representations, so they carry no oriented phase whether or not they are rigid, and
among the groups that can carry one, rigidity leaves only SU(3), which carries it through its centre on the U(1) circle
(claims IX.6k to IX.6m). The owner closes the circle: Sp(2) and G2 are the U(1) gate's two hidden witnesses, dimensionless to
the encoder, and with SU(3) they are the three compact simple groups of rank 2 (claims IX.6n, IX.6o). The reading needs the
witnesses rigid: Sp(2) is, topologically, by a surgery sketch; G2 is open (claims IX.6j, IX.6p).

**The expected negative.** Navier-Stokes is the card where the process does not build: the energy ledger cannot pay a uniform cost
per scale (VI.3.4, **[Lean]** in the model). In the owner's reading nothing more needs or can be said than that it is not
DMP-complete, and blowup is the expected consequence **[reading]** (VI.7e). This makes the framework falsifiable: a proof of global
regularity would refute the prediction, and a certified blowup profile would confirm it (VI.5.1, **[open]**).

**What follows under it.** Accepting the process orients every start. Every start is directed through `{infinity, 2, 3}`:

* **At the start, certified.** At supports where only the real place and the primes 2 and 3 enter (up to a = 0.69), Weil's form
  is positive with an explicit margin, c = 1.5e-9, 3.4e-11, 6.4e-13 at a = 0.60, 0.65, 0.69. So the first tick is certified
  positive with a margin, and the sign is fixed there **[numerical]** (certified in ball arithmetic;
  `docs/unified/GRH-ONEBOX-CERT.md`), with the abstract step **[Lean]** (`GRH/OneBoxCert.lean`, `onebox_positive`; claim X.58b).
  This is claim X.65.
* **For every later tick, conditional.** The sign at the start, and with it the direction of every later tick, is fixed *only if*
  the process is accepted. This is **conditional** on the acceptance (claim X.66). It is not a theorem that the margin survives:
  for GRH that is the open step (claims X.9, X.46), and the margin collapses fast beyond the start (about 3.6e-15 at a = 0.75)
  **[numerical]**, so it cannot be carried outward by computation.

**How to read a conditional result.** Whenever Part X, or a later part, writes "conditional on the established process", it means
exactly this: the statement holds if the process of G0 to the hand-over is established, and the process being established is the
assumption of this subsection. Where a result holds without it, the result says so: the Lean theorems of section 2 (the geometry
of the two edges), the transport theorem (II.9) and the certified start do not use it. **[paper]** (claim X.67).

**Why it is stated plainly.** The settling gates ask for it proved. Until it is, the abstract and the introduction should say
"conditional on the established process (O1)". That wording is the coordinator's to place; this part does not edit them.

## 5. Excision and incompleteness

**R136a1 is the answer "outside".** In DMP a part that is answered R136a1 is outside the system, whatever it is. Nothing else needs
to be proved about it. In the arsenal of the IM repository this is the one way to leave a statement open: `R136a1 "name" P` is the
statement P taken as a named hypothesis. It never becomes an axiom, so every declaration still rests on Lean's three standard
axioms only **[Lean]** (`Arsenal/R136a1.lean`, `R136a1`, `R136a1.out`, in the `im` repository, imported and never copied) (claim X.35).
The arsenal's lint lists every part answered R136a1 by name (II.13).

**Excision decides per tick.** Goedel's theorems apply to a whole consistent, effectively axiomatised theory that contains
arithmetic: some true sentences stay undecided **[classical]** (claim X.36). Two known ways to have completeness anyway are to restrict to
a complete and decidable fragment (Presburger arithmetic, Tarski's real closed fields) **[classical]**, or to decide per tick:
"provable within n steps" is decidable for every n, so at each tick everything not yet decided is outside, and the boundary moves
with the ticks. DMP's excision is the second way, with R136a1 as the answer for "outside". The decidable half is **[Lean]** (II.11,
`reaches_of_contracting`, with `etm_balance_undecidable` for the edge); the identification of excision with it is **[reading]**
(claim X.37).

Care point (claim X.38): the excision is decidable per tick. The set of all sentences ever decided is not decidable in general. So "outside
at tick n" can become "inside at a later tick". That is a new act, never a revision of the earlier tick. The owner adds that this
includes the *absence* of an expected tick: a missing tick is an answer too. The part is then outside. This is the time-to-live of
every act, and the hard cutoff of the settling machine (Outlook) **[reading]** (claim X.41).

**Why the Clay statements cannot be excised as a class.** The Clay problems are statements of arithmetic and analysis. If one of
them were independent of the axioms, it would be answered R136a1, "outside". That is not the settling the gates ask for
**[reading]** (claim X.39). The owner agrees, and adds that the assertion simply states that an O1 of that behaviour exists
and then lints everything that cannot survive it **[reading]** (claim X.39).

**Two markers, two channels.** `sorry` says "this derivation is incomplete here", and the kernel reports it as `sorryAx` in the axiom
list. R136a1 says "this part is excluded by name", and it stays a hypothesis, never an axiom, so the lint lists it. A result that
passes both (no `sorryAx` in the kernel's report, no escape hatch in the lint, every open part named) is certified twice, by
channels that cannot fail together in the same way **[reading]**, with the mechanisms themselves **[Lean]** and **[paper]** (claim X.40).
Care point: both channels certify form. This is double certainty of form, not of the content of an open part.

**The finite loss excised at the beginning.** The owner's reading: the finite amount of loss excised at the beginning is the floor
at the error bars: a fixed finite cost paid once, which is what makes the rest meaningful. Every act then collapses to one of two:
constructible inside (some subset of DMP), or R136a1 **[reading]** (claim X.42). Nothing in this section makes a theory with arithmetic
complete. The completeness is that of the generalisation over what is inside at each tick **[classical]** for the
incompleteness side (claim X.43).

---

## 6. The tick operator

**Transitivity reaches every finite scale.** Reaching composes. From a certified start, every finite scale is reached by finitely
many ticks, each one settling. That every tick past the start pays is **conditional** on the established process (section 4.4); the
composition of steps that pay is a ledger again **[Lean]** (`Unified/Encoder.lean`, `pays_of_factors`;
`Unified/Ledger.lean`, `carry`; `ETM/RunSys.lean`, `RunSys.carry`, `RunSys.contract`; `Margin.survive`) (claim X.44). For GRH the start is
`{infinity, 2, 3}`: Weil's form on supports up to a = 0.69 is positive there, with a certified margin
c = 1.5e-9, 3.4e-11, 6.4e-13 at a = 0.60, 0.65, 0.69 **[numerical]** (certified in ball arithmetic;
`docs/unified/GRH-ONEBOX-CERT.md`; the abstract step `GRH/OneBoxCert.lean` is **[Lean]**) (IV.3).

**The continuum needs a uniform bound.** Transitivity reaches every finite target. The continuum is a limit, not a finite target.
The margin carried by ticks is c_0 times the product of the factors. A uniform lower bound on the factors keeps it positive at
every finite scale, decaying at most exponentially **[Lean]** (`Margin.survive`, `survive_pos`; `GRH/Transfer.lean`,
`margin_pos_of_factors`) (claim X.45). A *uniform margin*, an infimum above zero over all scales, is false for zeta's zero measure: the zero
side of the explicit formula is purely atomic, so the product of the Szego factors is exp(integral of log w), which is zero
**[classical]** (Szego-Kolmogorov-Krein) (claim X.45b). So what the continuum needs is a uniform bound on the tick factors. Which bound
it is, is the open step of each card: the lower edge for GRH, the upper edge for O1 **[open]** (claim X.46).

**The tick is an act at a DB, rotating.** The owner's reading: the multiplicative transport is the tick operator. A tick is an act
at a boundary, and its rotation is the encoder's half-turn **[reading]** (claim X.47). The half-turn is exact (II.10): the electric
profile is the Moebius map of a symmetric matrix that squares to the identity, with antipodal fixed points **[Lean]**
(`Unified/GRHLens.lean`, `halfTurn_mobius`, `halfTurn_transpose`, `halfTurn_mul_self`, `fixed_antipodal`). As a Moebius map of the
sphere that matrix is a rotation by 180 degrees **[classical]**.

**Birkhoff-Hopf, and where it does not apply.** A positive map whose image cone has finite Hilbert projective diameter Delta
contracts the projective distance by tanh(Delta/4) per application **[classical]** (Birkhoff, Hopf) (claim X.48). On the Yang-Mills
side the slab factor is tanh(beta N) per layer, below 1 at every coupling, with no join loss **[Lean]** (`Unified/JoinLossSlab.lean`,
`kchain_tanh`) (claim X.49). The cutoff-uniform form of that bound is O1 **[open]** (claim X.49b). On the GRH side the lead does not apply as stated.
Weil's form at growing support does not factor into ticks of a positive map. First, growing the support is restriction to nested
sections, not iteration: a margin at scale k + 1 is one at scale k **[Lean]** (`sec_restrict`; claim X.22). Second, the Szego recursion does
factor the margin into ticks, but each step is an SU(1,1) isometry of the cone, whose image is the whole cone: Delta is infinite,
and Birkhoff-Hopf gives the factor tanh(infinity) = 1, no contraction **[classical]** (claim X.22b). Third, primes enter additively, with
indefinite forms, so each prime consumes margin and is not a positive map composed with the previous one **[classical]**
(claim X.22c). A symmetry exchanges pictures. It does not turn an upper bound on one encoder into a lower bound on another **[paper]**
(`docs/unified/GRH-LENS.md`, 6.3).

**What the act carrier settled.** The owner answered the composition question with the act carrier (I.4): a certificate passes
without loss when a conserved quantity carries it, and "the uniformity is given by the arrow of causality".

* **Yang-Mills: reduced to one number at one scale.** The conserved carrier (centre flux, Gauss's law on both sides of every DB) is
  in hand **[Lean]**; superadditivity along a chain **[Lean]**; uniformity along it **[classical]**; physical units **[Lean]**. The
  grid needs the influence to run in tubes, and tubes need F_e above the path entropy: O1 **[open]**.
* **GRH: the carrier is identified, and the step is located.** On the constructed space the scaling flow is an isometry; what remains
  are the zeros and the orbit lengths log p **[classical]**. The sign is global and all-or-nothing **[numerical]** + **[Lean]**.
* **NP vs coNP: the carrier is identified, and the step is located.** The parity a proof line names carries the crossing (Tseitin)
  **[Lean]**; in cutting planes the crossing is forced and speakable in one line **[Lean]**; converting it into size is the open step.

The summary of these three bullets is **[paper]** (on III.3 to III.5) (claim X.3). In DMP terms all three ask how a certified act hands its
certificate to the next act without loss, so that remnants accumulate into existence instead of eroding it. The three answers so
far: in Yang-Mills, existence must outrun possibility by the path entropy; in GRH, every building block must enter at once, at its
exact place; in NP vs coNP, the pair must be charged at its interface **[reading]** (claim X.3b).

### The rotatable hash: the root chain closes through time

DMP and Gravity, the two repositories of the root chain, pin each other by hash. Gravity's side is read here: a `PIN` records the
sha256 of the pinned copy of DMP, and the pin check turns any change of it into a failing check (`vendor/dmp/PIN`,
`tools/check-pin.sh`). That DMP pins Gravity in turn is the notes' statement and was not re-read for this draft. So every pinned
existence is a claim the gate can refute **[paper]** (claim X.50). A literal circle of hashes cannot be constructed: a file that contains its own hash, or two
files that contain each other's current hashes, is a fixed point of sha256, which no one can compute **[classical]** (by the hash's
design) (claim X.51). In the repositories the circle closes through time instead. Each side pins an earlier commit of the other, so the
chain is a spiral of versions, one tick per pin **[paper]** (claim X.50). Care point: the circle is consistent only because it never
closes at one instant. A pin to the other side's *current* commit would be the uncomputable fixed point.

The owner corrected the first wording: the hash is *rotatable*, not negatable. The hash itself is one-way **[classical]**. What
rotates is the pin: across versions the pin passes from one node to the other, a turn per tick, the same half-turn shape as the
encoder's, where two half-turns return to the start and the start is one version later **[reading]** (claim X.52). Care point: no hash
function is rotated, the roles of pinner and pinned are. The owner adds that inside the system the time-to-live of a certification
is not a separate mechanism. Every certification is re-made at each tick, against the same shared root, and never reaches back, so
the validity window of any hash is bounded by the interval between two ticks **[reading]** (claim X.53). What leaves the inside is outside
by definition, so its lifetime is the boundary's matter, not the rotation's.

---

## 7. Uncertainty transported across the DB

The owner's approach for the content layer: "Exactly define the uncertainty, then transport it in a meaningful way across a DB."
Each column keeps its uncertainty in one named bridge to the real object; the finite model asserts only itself. That uncertainty is
itself a carried quantity, so the ledger applies to it with one more term (`docs/unified/TRANSPORT.md`).

**The transport theorem is stated once, in II.9.** An uncertainty crosses each step with a factor and may gain fresh uncertainty:
it stays bounded when the steps contract (II.9.1), is carried without damping at cost = floor (II.9.2), preserves a sign when it
stays below the margin (II.9.3), and with no fresh uncertainty is the ledger itself (II.9.4). Where the uncertainty and the margin
it is compared with pay the same cost, their ratio crosses at exactly cost = floor: damping relative to a margin exists only if
the margin shrinks more slowly than the uncertainty (II.9.5). The five statements were X.7a to X.7e in draft 2.

**Where each uncertainty sits, and what the open step needs in these terms.**
- **Yang-Mills (claims X.7f, X.7g).** The uncertainty is the boundary uncertainty of a slab: how large the charged (twisted) sector can be
  against the neutral one, at any outside; O1 is the margin 1/mu. In the slab geometry the slab chain carries it with each layer's own
  factor and adds nothing (zero join loss), and any positive twist ratio clears O1 with enough layers on a fixed lattice **[Lean]**.
  The open step: a cost above the floor at fixed physical length, uniform in the cutoff (the twist ratio bounded below as the lattice
  spacing goes to zero), plus, in the box geometry, the side seam added at each join. For three slabs at the self-dual factor the
  seam must stay below (1/mu - (sqrt 2 - 1)^3)/sqrt 2 per join **[open]**.
- **GRH (claims X.7h, X.7i).** The uncertainty is how far zeta's margin (the Szego prediction error at scale n) is from the finite model's,
  relative to the model's; the explicit formula's remainder enters each scale as the relative difference of the two factors
  1 - |k|^2. In log form it crosses at exactly cost = floor: zero slack. Zeta's margin is certified, with size, while the summed
  remainders stay below log 2; the sign alone is decided step by step **[Lean]**. The open step: remainders, measured against a
  margin that collapses, that are summable with total below log 2, from the primes alone, beyond Dirichlet **[open]**.
- **NP vs coNP (claims X.7j, X.7k, X.7l).** The uncertainty is the hidden information per variable, the pointer of the gadget, log m bits.
  Each hidden variable a refutation must resolve takes a fixed share of the line count across the two-party split. That is a ledger
  with no fresh uncertainty, and it is exactly a size bound; lifting supplies the cost c log n per variable **[Lean]** from
  **[external]**. The open step: a constant cost c > 0 per hidden variable for a constant-size gadget (`LiftCPConst`) **[open]**. In
  the known proofs the per-block hiding errors add up across all blocks with no damping, which is why the gadget grows with n
  **[reading]** (recalled; to be checked against Mertz-Pitassi and Lovett-Meka-Mertz-Pitassi-Zhang).

**Side by side (claim X.7m).** `three_bridges` (`Unified/All.lean`) states the three columns in one theorem, each as "named hypothesis
=> the uncertainty is transported below the margin and the sign holds" **[Lean]**. It is the transport counterpart of
`three_instances`. The theorem is not empty: on a perturbed Doeblin chain every hypothesis is proved, and the uncertainty stays below
the margin at every step; without mixing, a perturbation of the same size erases the margin (claim X.7o) **[Lean]**.

**The running-state axiom (claim X.7n).** Each named hypothesis says that its object is in a running state. With that statement taken as a
named axiom R, the three conclusions follow: the boundary uncertainty stays below 1/mu, zeta's margin keeps its sign, the crossing
cost is paid **[Lean]** for the implication. R for the specific objects (the Wilson measure in the continuum, the L-functions beyond
Dirichlet, strong proof systems) is exactly the open step of each problem **[reading]**. This is the structural sense of section 4.2.

---

## 8. What this part adds up to

1. Every card needs the same container, a containing existence with free possibility space (section 1). The cards share one geometry (section 2) and one slot (section 4). What each card asks of the geometry differs, so no single statement
   proves them all.
2. The open step of each card is the same assertion in the card's terms: "this object runs", with a floor, uniformly (sections 4.2 and 6).
3. The proved obstructions say why assembly with slack cannot supply it (the table in section 4.1).
4. The dichotomy of II.11 says what would follow: with a floor, a settling bound; without it, no decision procedure (section 4.3).

When a step closes, the change to the paper is local: the status in `../CLAIMS.md` moves from open to Lean (or paper), the section's
verdict line changes, one cell of the table in section 4.1 changes, and the abstract's list of what remains shrinks by one item. No other
section needs to move. That is the test of the paper's structure.
