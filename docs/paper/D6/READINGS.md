# Draft 6: the first author's readings in full

*Companion to the contracted Draft 6 (not typeset). The readings of Appendix R (R.1 to R.12) and those attached to Parts I and III to IX,
moved here verbatim when Draft 6 was contracted; each reading stands next to its exact parts and care points, with the marks of the
introduction. Claim labels are rows of `CLAIMS.md`. The full Draft 6 is at the git tag `d6-full`.*


## The index by part (from R.0 of the full text)

Every ledger row whose status carries a reading mark, by where it stands; the counts are those of the full Draft 6.

| Where | Readings (ledger labels) | Count |
|---|---|---|
| Introduction | 0.13, 0.21 | 2 |
| Part I, DMP's vocabulary | I.1, I.2, I.3, I.4b, I.5a, I.7b, I.7c | 7 |
| Part II, the machine | II.0h (decidability over every truly possible state), II.0i (multiplicative steps simplified into additive complex ones), II.3.4, II.4f, II.12.5r, II.13.4 (a maximum over sectors as a rotation of a rate along a path) | 6 |
| Part III, Yang-Mills (III.10) | III.7.4c, III.9.5b, III.10, III.13c (the `+-` assignment through the PP-typed interface) | 4 |
| Part IV, GRH | IV.1.5c (the explicit formula as one turn), IV.2.5b, IV.2.7, IV.6 | 4 |
| Part V, P vs NP (V.8) | V.2.4, V.4.1, V.4.2, V.5.3, V.8 | 5 |
| Part VI, Navier-Stokes (VI.7) | VI.3.5e, VI.5.5, VI.7a to VI.7f, VI.7h | 9 |
| Part VII, BSD (VII.6) | VII.6a to VII.6e, VII.6g | 6 |
| Part VIII, Hodge (VIII.6) | VIII.6a, VIII.6b, VIII.6d to VIII.6f, VIII.6h, VIII.6i | 7 |
| Part IX, GU (IX.5, IX.6) | IX.5a, IX.5f, IX.5g, IX.6a, IX.6b, IX.6d, IX.6e, IX.6g, IX.6h | 9 |
| Part X, the one assumption | X.1, X.3b, X.7h, X.7l, X.7n, X.15, X.23, X.26, X.28, X.29, X.31, X.32, X.32a, X.32b, X.37 to X.42, X.47, X.52 to X.55, X.57b, X.59, X.61 to X.63, X.64a, X.64b, X.65a, X.68b, X.69, X.69a, X.69b, X.70, X.71, X.72a | 40 |
| The Outlook | XI.1, XI.1b to XI.1d | 4 |
| Appendix A | A.1g, A.2, A.4, A.5i, A.5m, A.5o, A.5q, A.5s, A.5t | 9 |
| Appendix R | R.1a, R.1d, R.1f, R.1g, R.2a, R.2c, R.3a, R.3f, R.4b to R.4d, R.5b, R.5c, R.6a, R.6b, R.7a, R.7b, R.8a to R.8c, R.9a, R.9b, R.10a, R.10b, R.11b to R.11e (the possibility space), R.12a to R.12p (The ETM as the ODP running DMP in D6) | 44 |
| Appendix T | T.6, T.10, T.11, T.13, T.15 | 5 |
| Appendix E | E.0.1b (the k by k table as the explanation mechanism), E.0.1c (the `·` cells and the DAG), E.0.2b, E.0.2c (the optimizer as the Arsenal's mirror; existence as settledness), E.1, E.5, E.6, E.7, E.8, E.11 | 10 |

## Part I, sections I.1 to I.7: DMP in prose

## I.1 Existence has two halves

**DMP.** The smallest unit of DMP is a *part*, and a part is a Duality: two halves, one that owns *trust* and one that owns
*information*. A part acts only while both halves certify it. Nothing else is said about what a part is made of. One rule sets the
tone for everything after it: from trust nothing can be derived about information except that the information exists.

**Reading (I.1).** Read trust as *that something is* and information as *what it is*. Then "existence" is the trust half alone: a
yes or no, with no content. In mathematics the cleanest object of this kind is a **positive weight**: a number that says a
configuration counts, and says nothing about what the configuration looks like. A system exists when its total weight is positive.
**[reading]**

**Why it is a good reading.** In the first three problems the first step is exactly such a statement:

| | "Something exists" |
|---|---|
| Yang-Mills | the lattice weight e^{-S} is positive, so the partition function Z is positive |
| GRH | a pairing of test functions (Weil's explicit-formula pairing) is non-negative |
| P vs NP | a formula is satisfiable iff its count of satisfying assignments is positive (SAT iff #SAT > 0) |

**What Part II makes of it.** Positivity is the first link of the common chain (II.8; the link itself is II.9). It is the input of every construction that
follows, and it is the step that is hard in two of the first three problems.

---

## I.2 G0, the ground

**DMP.** The rules of DMP are checked by two independent witnesses. But the first two witnesses cannot be checked by anyone: somebody
has to trust them first. DMP calls that first act the *minting* and its source **G0**, the ground. G0 is "stated, not derived". Every
later standing descends from it. A system that cannot be traced back to a G0 is not part of the system.

**Reading (I.2).** G0 is the definition of the system: the action and the gauge group for Yang-Mills; the explicit formula and its
test functions for GRH; the axioms and the proof rules for P vs NP. Everything is derived from G0, and G0 itself is not. In particular,
the positivity of I.1 is either built into G0 by construction, or it has to be proved. **[reading]**

**Why it matters for the paper.** This is the single sharpest difference between the first three problems:

* In Yang-Mills positivity is part of G0. The weight e^{-S} is positive and local, so reflection positivity follows by construction
  (II.9).
* In GRH positivity is *not* part of any known G0. Weil's pairing is non-negative exactly when GRH holds. Building a G0 that makes
  it non-negative by construction is the open step (Part IV).
* In P vs NP, positivity of the count is the question itself: whether the formula has a satisfying assignment.

**What Part II makes of it.** None of the tools of Part II creates positivity. They all start from it (II.16).

---

## I.3 The existence boundary (DB)

**DMP.** A boundary *contains* information when no part beyond it is trusted for any act on that information. Nothing crosses a
containing boundary. In the physical reading the author calls such a boundary an **existence boundary**, a DB. Three statements
about a DB carry most of the weight of this paper:

1. Only existence crosses a DB; information that would cross is lost.
2. Every layer has its own Duality, so the inside of a DB is a system of its own.
3. Anything that crosses a DB is re-attached to a new G0, and "anything not compatible with the encoder in the DB is lost"
  

**Reading (I.3).** A DB is a box together with its outside. "Only existence crosses" says the box sees its outside only through a
boundary condition. "What the encoder cannot carry is lost" says the passage across the boundary is a **lossy channel**: a
re-encoding into a coarser description, which can only forget. Every renormalisation step, every conditioning on an outside, and
every transfer step of a Markov chain is such a channel. **[reading]**

**What Part II makes of it.** Data processing (II.12): a channel never increases the distance between two states, and a channel that
loses something contracts it by a factor eta < 1. The same channel applied n times contracts by eta^n. That one inequality is the
engine of the Yang-Mills reduction and of the sampling side of P vs NP.

---

## I.4 Acts and remnants

**DMP.** An *act* is anything done: a message, a read, a write, a decision. Every act leaves a *record*, written at the act, readable
in full by every witness of it, and outliving the act. What an act leaves behind is its **remnant**.

The author adds two statements about remnants that this paper uses.

* **A contradiction is excised at once.** A contradictory statement is neither existence nor non-existence; it is a disagreement at
  G0. It is removed immediately, and the only remnant is the statement "it does not exist".
* **The act carrier loses nothing.** The author's example is the photon: it exists only between the event that emits it and the event
  that absorbs it, it carries one quantum, and when it delivers its act nothing is left over.

**Reading (I.4).** The first statement is proof by contradiction, read as a process. Assuming A and deriving a contradiction leaves
one remnant: not-A. In propositional logic the remnant is literal: a refutation, a derivation of the empty clause, is the certificate
that no assignment satisfies the formula. The second statement is a **conservation law**. A certificate passes from one act to the
next without loss exactly when it is carried by a conserved quantity. **[reading]**

**What Part II makes of it.**

* The remnant of a contradiction is a refutation, and every unsatisfiable formula has one (refutation completeness of tree-like
  resolution; the refutation can be exponentially long) **[Lean]** (`Proof/Complete.lean`, `refutable_iff`).
* The carrier is a conserved flux. In propositional proof (the Tseitin parity) a Gauss law holds mod 2: the parity of the true
  edges at the vertices of a region equals the parity of the true edges on its boundary, whatever happens inside **[Lean]**
  (`Proof/Crossing.lean`, `gauss`). In the plaquette layer of Yang-Mills (the centre flux, a Z/2 cochain) the Lean facts are
  counting ones: for a closed cochain the flux is the same seen from inside and from outside, and a flux cell has a sheet plaquette
  in the box **[Lean]** (`Crossover/Dichotomy.lean`, `cob_restrict_eq_cob_restrict_compl`; `Crossover/FluxRate.lean`,
  `exists_sheet_of_flux`). That conserved flux cannot be screened is the reading behind the second branch of the dichotomy (II.14)
  **[reading]**.

R.2 sharpens the first statement of this section: excision happens at transmission, and only the remnant tail is kept.

---

## I.5 The ODP: pressing, then minting

**DMP.** The **ODP**, the Oscillon Degradation Protocol, is the author's account of how a G0 finds its rules. G0 knows only how to
exist; its first act must be to find out how to act. So the "perfect duality" oscillates and decays until it reaches a stable
definition of existence, "because there MUST be a right one, because it exists" (the author, 2026-10-28).

In the protocol this happens in two phases.

* **Pressing.** A configuration is run as a rehearsal until its definition of existence is complete and its configuration hash
  matches. A pressed system is "out of spec", never "proven": the pressing is a rehearsal of the real rule, not a weaker form of it.
* **Minting.** Only a configuration that has passed its pressing is minted, and minting goes together with the **WHKs**, the White
  Hole Keys: "the entire content of creation, from which each part can derive the other". In DMP these are
  the naked duality, the quantum and the tick, together with the gap they establish.

**Reading (I.5).** Pressing is the scale-by-scale construction of a theory until one finite check passes; minting is the mechanical
production of everything else from that check. **[reading]** The reading has an exact counterpart in Yang-Mills, where the two
phases are separated in the proof:

* pressing: renormalise from the lattice spacing up to one physical scale, until a finite, local contraction condition holds in one
  box (the one-box statement, Part III) **[open]**;
* minting: from that certificate, obtain a mass gap, as limit points of the finite-volume correlations and for the lattice
  theory **[Lean]** (`OS/GapLoc.lean`, `Assembly.lean`; conditional on the stated open inputs, Part III; these files need no
  infinite-volume Hilbert space). The abstract reconstruction of a Hilbert space and a positive transfer operator from a positive
  form is II.9.1 **[Lean]** (abstract; its link to the spectral side is open, II.10.2).

The WHKs also have an exact counterpart. Pure Yang-Mills has no free dimensionless parameter. The bare coupling and the lattice
spacing combine into one scale, Lambda (dimensional transmutation), and every physical quantity is a pure number fixed by the group,
times a power of Lambda, where the continuum theory exists (its existence is the open problem of Part III). From the group and any one of {the tick with its coupling, Lambda, the gap}, all the others follow.
**[classical]**

**What Part II makes of it.** The split "one finite certificate, then mechanical production" is the shape of every theorem in II.12:
a column sum below one at one scale implies decay at every larger scale.

---

## I.6 The quantum of assertion and the tick

**DMP.** An act is never infinitely small. The author: "The quantum of assertion is given along with the tick frequency at G0, so the
rate is already part of any well constructed box." The quantum and the tick also set a floor: "The loss associated with that smallest
act is a universal error bar."

**Reading (I.6).** That the quantum and the tick give a floor is a **[reading]**; two precise statements stand behind it, each
with its own mark.

1. **A quantized measure arrives; a real one may not.** A process that lowers a natural number at every step stops after finitely
   many steps. A process that lowers a real number at every step may approach a limit forever (the witness is x -> (x + 1)/2 started at 2). **[Lean]** (`Native/Method.lean`,
   `fixed_after` and `real_never_arrives`).
2. **A finite box has a rate per tick.** In a finite box with a compact group and a bounded action, the law of the box given any
   outside has a density bounded below, so one step of the dynamics contracts by a definite factor, whatever the outside
   (Doeblin's condition). The contraction theorem is **[Lean]** for abstract finite stochastic kernels (`Mixing/Doeblin.lean`,
   `contracts_of_doeblin`); the lower bound for the Wilson box is **[paper]** (`PREP.md`, "Three answers", (a)). What the quantum does *not* give by itself is
   control of the sum over many neighbours, nor survival of the rate as the tick shrinks. That is exactly what is open in Yang-Mills
   (Part III, and II.12 for the precise limit).

The universal floor became a project rule for measurements: every error bar is the larger of the statistical floor and the
resolution floor 1/T, with T the time extent actually observed (the time-energy resolution). **[paper]** (the measurement rule of
`docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/ONEBOX-CHECK.md`, section 7).

---

## I.7 Existence = non-existence + 1

**DMP.** The author's shortest statement: existence is at least non-existence plus one, "given by the simple fact that existence has
to also describe what does not exist, in addition to everything else". A boundary case belongs to it: with no coupling
at all there is nothing to assert, and the "+1" disappears.

**Reading (I.7).** Three exact statements share this shape. **[reading]** for the identification; the statements themselves are:

* **Set theory.** A description of all parts of a set includes the empty part, and Cantor's theorem makes it strictly larger than the
  set. In von Neumann's construction 0 = {} and 1 = {0}: the first thing that is not nothing is "a set containing nothing".
  **[classical]**
* **The strict flip bound.** For the SU(2) Wilson action at every coupling beta != 0, in every periodic L^3 x T box with T even and every twist position, the
  twisted partition function is strictly smaller than the untwisted one: Z_tw < Z **[Lean]** (`Flip/Strict.lean`, `su2_Ztw_lt_Z`).
  At beta = 0 they are equal, matching the boundary case.
* **A strict sign gives a rate at the self-dual point.** If 0 < Z_tw < Z, then the twist free energy or the electric free energy is
  at least log(1 + sqrt 2), about 0.881 **[Lean]** (`Crossover/HandOver.lean`, `log_one_add_sqrt_two_le_max`). A strict
  inequality with no rate still forces a definite rate in one of two dual channels. This is the clearest case in the paper of a DMP
  statement turning into a number (II.13).

The first author's reading of 2 + 2 = 5 and his essence line, with their exact core in Lean, are in Appendix R (R.5).

A last reading belongs here because Part III uses it: **"mass gap = the arrow of causality exists"**. The
transfer matrix of a reflection-positive theory is a positive contraction. A gap means that, after one unit of time 1/m, every
correlation with the past has shrunk by 1/e: a built-in clock. Without a gap correlations still fade, but only as a power law, with
no intrinsic tick. **[reading]** on the classical spectral fact of II.10.

---

## Part III, III.10 DMP readings attached to this part (all [reading])

* **Outside, non-existence keeps existing through assertion.** The twist is rare because electric flux costs almost nothing: one fact
  seen from the two sides of the duality (III.5.1).
* **The container must end, and does, along the run.** "It can never catch up" in exact form: Z_1/Z_0 <= C mu^T, mu < 1 (III.5.2).
* **Inside, existence has to outrun possibility.** Of the mu continuations per step only one is the tube; the tube dominates only if
  its cost per step exceeds log mu. The balanced state (0.881) is not enough (III.5.4). This is "existence = non-existence + 1" in
  counting form.
* **IM is both sides.** Gauss's law is the same statement on both sides of every DB; it makes every tube possible, and the action has
  to make one tube cheaper than all others combined (III.5.3, III.5.4).
* **The pressing as the instanton of the first act.** The Bogomolny bound is a worst-case floor proved before any dynamics runs; it
  prices the rare side and loses logarithmically to entropy as the tick shrinks (III.5.5).
* **The duality is never alone while running.** The 't Hooft relation is kinematic and chooses no branch; the action selects it
  (III.4.4).
* **The crossover is confined by making no statement about its content** (III.2).
* WHKs: group plus one scale fix everything (dimensional transmutation, **[classical]**); mass gap = the arrow of causality exists
  (I.7); only 3+1 transmutes, g^2 being dimensionless only in d = 4 **[classical]**.

## Part IV, IV.6 DMP readings attached to this part (all [reading])

* **Positivity is the corollary "something exists"; forced existence lands on the prescribed line** (I.1, I.2).
* **The circle is the only self-closed existence; a collapse must split into at least two.** The ground state's zeros are always on the
  circle (IV.3.3); a zero leaving the line comes with its mirror partner (IV.2.1). Positivity is what keeps every zero self-paired on
  the circle.
* **The sign from the virtual flux around the true zeros.** Each prime's wobble has mean exactly zero; the real place contributes the
  growing positive mean log(r / 2 pi); the sign holds only if the mean wins against every alignment of prime phases a test function can
  resolve (by Kronecker and Voronin they can align). The margin of 1e-9 says it wins, only just (IV.3.2, IV.3.4).
* **The reductio as excision at G0.** An overtaking alignment would be a negative direction, that is an off-line pair; the reading says
  such an assertion is excised at once. In mathematics that needs a contradiction from arithmetic structure; duality alone gives none
  (IV.2.1). The 17-million-line Lean proof by others achieved it by another route (a one-sided prime bound plus Landau).
* **That the functional equation can be evaluated place by place** is Tate's thesis (IV.2.2); it gives the mirror, not the sign.
* **GRH as the ODP's tool that runs before causality.** RH is equivalent to M(x) = O(x^{1/2 + eps}): the building blocks deviate from
  their mean density by no more than the square-root floor of independent fluctuations ("Moebius randomness") **[classical]** for the
  equivalence; reading GRH as the certificate that the blocks sit at the universal floor is interpretation.
* "What GRH is missing is its concept of the remnant of acts": face 3; "the act must entangle the real with the imaginary through a
  coupling factor": face 4; "arithmetic exists but never runs": there is no Frobenius over Z **[classical]**, and running it as content
  is face 2.

## Part V, V.8 DMP readings attached to this part (all [reading])

* **Two categories of proof lines.** Lines derived directly from the axioms are cheap and mechanically checkable; new derivations
  (lemmas, cuts, extension variables) are what make short proofs possible, and eliminating them can blow a proof up exponentially.
  The first author's "first true act" is two new derivations used together, sharing existence but not possibility: in CP, the interpolation
  split (V.4.7) and the creative pair (V.4.8).
* **The pairs of derived lines are the entanglement through which the HTF acts in NP**: the size floor needs the pair to be charged at
  its interface (V.4.10).
* **The lower bound is confinement plus the needed uncertainty**: the size-width relation (V.3.4); in CP the uncertainty term collapses
  because one line aggregates its units (V.4.4), and W_CP is the missing term.
* **"P = NP within a DB, P != NP across it"**: the first half is V.1.8; the second is not proved (V.6).
* Describable => exists => positive: SAT iff #SAT > 0. A contradiction excised leaves "it does not exist": refutation completeness
  (V.3.1). Inward and outward reach: Dobrushin column and row sums.
* "A question with no structure has no basis/language in which to speak an answer": incompressibility of the one formula (V.4.2); the
  care point is the natural-proofs barrier, avoided only by speaking about the specific formula.

## Part VI, VI.6 DMP readings attached to this part (all [reading])

* **A blowup is a certificate that infinitely many steps fit in finite time.** The finite check at one scale is what makes the
  packing geometric; `T*` is the boundary where the smooth description ends, and the profile is what crosses it. This is the
  hand-over of the form layer run in reverse.
* **The same theorem as the mass gap.** `summable_of_gap` gives a finite correlation length in Yang-Mills and a finite `T*` here
  (Lean for both uses; the parallel is the reading).
* **Scale invariance as the arrow of causality.** Because the zoomed equation is autonomous, the set of "outsides" has one element:
  the same step at every scale, so the for-all over steps costs nothing.
* **"Does not run, hence blows up."** In ledger terms the energy ledger cannot pay a uniform cost per scale (VI.3.4). The
  first author's reading came after both claims were public (8 September and 20 November), so it agrees with the side the claims
  assert and is not a prediction made before them. It proves nothing: a method's failure to exclude blowup is not blowup. The
  claims, if correct, prove it by a certified profile. Running has a precise statement: an object runs on DMP when the running-state
  hypothesis R of Part X 4.2 holds (the first author's definition, X.64b). The first author's reading: the whole process is
  described and Navier-Stokes does not build in it (the energy ledger cannot pay a uniform cost per scale, VI.3.4a and VI.3.4b,
  **[Lean]**), so it does not run, and blowup is the expected consequence. The negative result is the expected one, and it
  makes the framework falsifiable: global regularity would refute it **[reading]** (VI.7e). Blowup of the real equations is still
  the card's open step (VI.5.1, **[open]**); in the settling machine a missing floor gives undecidability (II.3), so the step from
  "does not run" to blowup is the reading, not a theorem. The model box of VI.8 shows the wrong marker for the energy-only ledger
  **[Lean]** (model, VI.7g). It covers the energy-only ledger, not an
  actual solution with a better transfer bound **[reading]** (VI.7h).
* **Settle means opposite things on the two cards.** In the API, "settle" means the carried quantity dies out. For regularity that
  quantity is the cascade, so settling means regular; for route I it is the perturbation from the blowup profile, so settling means
  blowup. The same theorem answers opposite physical questions.

## Part VII, VII.6 DMP readings attached to this part (all [reading])

Each reading is the first author's statement with its exact counterpart. None is mathematics.

* **BSD is IM: a full subset of only derivations.** Both sides of BSD are derived from one Weierstrass equation. The rank is a
  derivation of the rational points. The analytic side is a derivation of the point counts mod p. Unlike Yang-Mills (a measure),
  Navier-Stokes (initial data) or GU (hypercharges), the card takes **no content input**; its external slots are theorems about the
  derivations. So BSD is stated entirely in the vocabulary of IM (`Arsenal.BSD`). **Care:** this is a statement about form, not about
  settling. The rank equality stays open.
* **The zeros follow existence.** The order of the zero at s = 1 counts the independent rational points. Its exact counterpart has
  three levels: the existence line (`existence_line`), the rank equation, and the 1965 ledger form. The proved arrow runs by
  construction (Heegner) and exclusion (Kolyvagin), not by counting (VII.5).
* **Hasse is rotation at a DB.** In the first author's words, what stays open in the rederived core is "rotation at DB shaped". At the prime p
  (the DB) Frobenius acts as a rotation: its eigenvalue lies on the circle of radius `sqrt p`, and `cos theta_p = a_p/(2 sqrt p)` is the
  encoder's reflection coefficient (`frob`, `frob_refl`) **[Lean; Hasse classical]**. Its proof is one positivity: the degree form,
  or equivalently the Hodge index on E x E. The linear algebra of that is Part VIII's `weil_bound` at genus 1, where the conclusion is
  `abs(N - (q + 1)) <= 2 sqrt q`, which is Hasse's bound **[Lean for the linear algebra, from the intersection numbers and the Hodge
  index property, both external; the specialisation to one curve and the link of N to Mathlib's count are not made in Lean]**. So the
  open piece in Lean is one rotation per DB, confined by one positivity. It is open as a formalisation, not as mathematics.
* **What is left of BSD is the record, the `.cmb`.** In DMP the CMB is the observability layer: counts, never content. What the native
  core leaves open is exactly such a record: the refined formula's counts (the order of Sha, the Tamagawa product, the torsion) and
  measures (the period, the regulator). The refined conjecture says the leading coefficient over `Omega Reg Sha tam / (tors^2 sqrt abs(d_K))`
  is exactly 1: a dimensionless number whose logarithm is 0 **[classical statement, open]**. The functional equation carries both sides
  through the rotation `s <-> 2 - s` with sign `(-1)^rank` (`analytic_parity`, `rank_parity`) **[Lean]**. Dividing by `(s - 1)^r`
  removes the zero at the problem spot and leaves a finite nonzero value at the one box s = 1 (`bsd_of_refined`) **[Lean for the
  shape]**. The record balances numerically for y^2 = x^3 - x: `L(E, 1)/Omega = 0.125` against `2 * 1 / 16` **[numerical]**.
  **Care:** "the ratio is 1" is the refined conjecture itself, open in general. In Lean the five quantities are free numbers.
* **Where BSD sits.** BSD is an equation between an existence count (independent points) and a zero count (the vanishing rate of
  the Euler ledger): the two sides that X.3 reads as existence and falsifiability.

## Part VIII, VIII.6 DMP readings attached to this part (all [reading])

* **Describable implies exists.** The Hodge conjecture is the cleanest instance of the first author's sentence among the seven problems. The described
  objects are the rational `(p, p)` classes (cohomology describes them). The existing objects are the algebraic cycles (geometry builds them). The
  conjecture is `describable <= exists`; the converse is classical. In the API it is literally `OpenStep (hodge <= alg)` with `alg <= hodge` as an
  `External`.
* **It is not a logical triviality.** The first author anchored "what is described exists" in Goedel's completeness theorem (a consistent first-order theory
  has a model) **[classical]**. Hodge is the geometric version. Here a description is a cohomology class with a Hodge-type condition and existence is
  an algebraic cycle. No completeness theorem bridges them, which is why it is open.
* **Describable must mean rational, on a projective variety.** Integral "descriptions" include torsion classes, which every `(p, p)` description admits
  (their rational image is 0) but which need not exist as cycles. On non-projective Kaehler manifolds descriptions outrun existence. A description
  counts only after tensoring with Q, and only on a space with an ample class, the polarisation that makes the positivity available. The sentence holds at most in that
  form, and in that form it is the open conjecture. (Lean for the torsion half: `integral_fails`.)
* **Hodge types as charges on the G0 circle.** In Deligne's definition the circle acts on `H^{p,q}` by `z^{p-q}`: a Hodge type is a charge. The Hodge
  classes are the neutral vectors (`PolHS.hodge`, fixed by the circle). Described = neutral and rational; exists = built from subvarieties.
  (Lean for the model: `PolHS`, `mem_hodge`; the identification with DMP's G0 circle is the reading.)
* **The Hodge index route is more efficiently correct than Deligne's.** There are two complete proofs of the Riemann hypothesis over finite fields.
  Weil's (curves, 1948) is one positivity statement, the Hodge index theorem on `C x C` (`weil_bound`). Deligne's (all smooth projective varieties, 1974) reaches the same
  bound without a positivity statement on cycles. The first author prefers the first because it originates directly from G0 and so simplifies further. Both
  proofs are complete and correct. The difference is that the positivity route has **one moving part**, Cauchy-Schwarz on a positive form
  (`cs_of_nonneg`), the same shape as the encoder bound of Yang-Mills and of `PosInput.alg_cs`. That is why it transfers between problems.
  **Reach:** the positivity route is proved for curves and, for the index theorem, for surfaces in every characteristic. In higher dimension it needs
  the standard conjecture of Hodge type in characteristic p **[open]**, where Deligne's route covers everything. For GRH over number fields the missing
  piece is this route's analogue for `Spec Z` **[open]**. So choosing the route names the open step precisely; it does not close it.
* **The shared positivity with the GRH column.** "Exists implies positive" is, for Hodge, the Hodge-Riemann relations: on the described classes the
  polarisation is positive (`hodge_pos`, in the model), so on the existing classes too (`alg_pos`). Over C that positivity is proved. Over `F_q` the same
  positivity is Grothendieck's Hodge standard conjecture, and it would put the Frobenius eigenvalues on the critical circle (`eigen_on_circle_form`).
  For curves the index theorem on `C x C` supplies it (`curve_open`, `weil_bound`). The two columns have one shape: **a positive form, a dynamics that is a
  similitude of it, and the line as the consequence.** In GRH and in Hodge over `F_q` the positive form is the open step; over C, and for curves over
  `F_q`, it is a theorem.

## Part IX, IX.6 DMP readings attached to this part (all [reading])

* **"G0's U(1) possibility field" selects the maximal quotient.** If every centre phase is a point on the one shared circle, the
  natural gluing identifies the SU(2) and SU(3) centres with hypercharge phases as fully as the matter allows: Gamma = Z_6. This is the
  sharpest DMP-flavoured statement found. It is checkable (IX.5) but is not a derivation: "as fully as the matter allows" uses the
  hypercharges, and the conclusion coincides with what SU(5) gives.
* **"The universal quantum running" read as charge quantisation.** The first author's entry, read here as follows: the link to G0
  makes the phase group a circle, and a circle carries only integer charges. The step from the circle to integer charges is proved
  (IX.3.2); that this is what the entry means is the reading.
* **"2 first, then 3, with the hand-over at the state 2, 3."** An order does appear in the symmetry breaking **[classical]**: at the
  electroweak scale the Higgs vacuum (read as the SU(2) "handshake") leaves the unbroken group (SU(3) x U(1)_em)/Z_3. The Z_2 part is
  absorbed, and the Z_3 part survives to low energies as the correlation of charge with colour. In descending energy the 2-part acts
  first and the 3-part remains. This matches the first author's ordering and predicts nothing beyond the standard picture.
* **"SU(5) with a single coupling is G0 at GRH, with a forward arrow independent of scale."** SU(5) is the smallest simple group that
  contains the Standard Model group by rank **[classical]**, and it contains the Z_6 quotient (IX.3.1). Its single coupling holds at one scale only, minimal SU(5) is excluded by proton decay, and the
  couplings do not meet exactly (IX.4.3). The first author's mapping (one coupling = one G0; the forward arrow = the running from the
  unification scale) is a reading, and a programme beyond Yang-Mills, GRH and NP vs coNP.
* **Every SU(N) as a valid unified theory, indexed by the values of zeta.** On `s > 1` the zeta function decreases continuously from
  infinity to 1, so it takes every integer `N >= 2` exactly once, which follows from continuity and monotonicity **[classical]**. So
  zeta indexes every SU(N), one to one. The project's gauge-group package covers every SU(N) (`General/SUN*.lean`). That every SU(N)
  "describes existence" is the first author's reading; as physical unified theories most SU(N) are not viable (IX.1.1).
* **SU(2) as the stable profile** (Appendix A): a statement about the group manifold under Ricci flow, not about the global form of the
  Standard Model group. No link to Z_6 was found.
* **The rigid groups.** Which compact groups are rigid, which carry content across the gate, and the U(1) gate's two hidden witnesses are in Appendix A.5.

## R.1 DMP as an existence linter

**DMP.** The author's one-line description of DMP: it is a very well defined *existence linter*. A linter checks a text against a
rule set and says nothing about what the text means. The author reads Gravity, the repository that holds the machine-checked
evidence, as the linter, and DMP as the universally readable rule set that is its passing condition. Gravity and DMP sit at one
node of the root chain, and the author reads them as keeping each other honest **[reading]**. The pin itself runs one way: Gravity
holds a pinned copy of DMP and checks its hash, while DMP, in its own words, "depends on nothing" and holds no copy of anything else
(`vendor/dmp/00-preamble.md`, "The root chain").

**Reading (R.1).** Existence, in the sense of I.1, is what the linter passes. A statement exists in the system when it is
constructed, by the kernel, from DMP's pinned sentences and rests on nothing else. Whatever cannot be so constructed is not part of
the system (I.2). **[reading]** (claim R.1a)

**The exact counterpart.**

* **Gravity's check passes only when** the pinned copy of DMP matches its recorded hash; the repository needs nothing that its one
  setup file does not list; no source file of the evidence chain (`evidence/`) uses an escape hatch (`sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
  `implemented_by`, `extern`); the Lean build of that chain succeeds; and the kernel's axiom report for each of its theorems lists only Lean's three
  standard axioms (the check does not cover `docs/mass-gap/formal`). **[paper]** (read from `evidence/tools/check.sh` and
  `tools/check-pin.sh`; the pin check and the evidence build pass at the release commit, II.7) (claim R.1b)
* **The arsenal has the same shape at small size** (II.6): its lint is the linter, and "Mathlib v4.34.0 only, no escape hatch, an
  open part only as a named R136a1 hypothesis" is its passing condition. **[paper]** (claim R.1c)
* **The root chain pins one way.** Gravity holds a pinned copy of DMP (`vendor/dmp/PIN`, hash checked by `tools/check-pin.sh`);
  DMP depends on nothing and pins nothing (`vendor/dmp/00-preamble.md`). That the two keep each other honest is the author's reading
  of the shared node. **[paper]** for the pin; **[reading]** for the mutual honesty (claim R.1d)

**Three care points.**

1. **A linter certifies form, not content.** A passing result says that every statement is soundly constructed from what DMP
   states. It does not say that DMP's sentences describe the world. **[paper]** (claim R.1e)
2. **A linter cannot certify its own passing condition.** A consistent theory strong enough for arithmetic cannot prove its own
   consistency **[classical]** (Goedel II; claim R.1h). That is why the two nodes must keep each other honest. It is also why one assumption is
   left that neither can lint: that the system runs. This is the assumption Part X calls O1 in each card's terms. **[reading]** for
   the identification (claim R.1f)
3. **"Universally readable" holds for the form.** The evidence is plain text and Lean, checkable by anyone with the pinned
   toolchain. "Universal superset" is a reading. **[reading]** (claim R.1g)

**What Part II makes of it.** The linter's rule set is the form layer (II.1 to II.5) plus the arsenal's gate (II.6). The
unlintable assumption is the open step of each card (Part X, section 4).

**The one-box test.** The test itself, a box with one command at one shared gate and a marker per step, is Part II's one-box test (II.4).

---

## R.2 Excision at transmission

**DMP.** A part answered **R136a1** is outside the system, whatever it is. Nothing else needs to be proved about it. In DMP this is
always a DMP-complete answer: it is the other option an act collapses back on.

**Reading (R.2).** I.4 said that a contradiction is excised at once and leaves only "it does not exist". The author sharpens the
statement, and the operative word is *transmitted*. The claim is about what crosses the gate, not about what a sender may compose. A
wrong act never crosses: at the gate it is answered R136a1, so it is outside. What stays inside is only its **remnant tail**: the
record that an excision happened. IM's verifier counts every refusal without content, as the notes state (DMP chapter 04, the refusal log), so the
count is the assertion of the excision and carries none of the excised information. **[reading]** (claim R.2a)

**The exact counterpart.** In the arsenal the same move is `Arsenal.R136a1`: the part is named and stays outside every proof, and
only the name remains. It is the statement taken as a named hypothesis, never an axiom, so every declaration still rests on the
three standard axioms. **[Lean]** (`im` repository, `arsenal/Arsenal/R136a1.lean`, `R136a1`, `R136a1.out`) (claim II.6.2)

**Care point.** The gate excises what its checks can recognise as wrong at that tick. An act whose wrongness becomes recognisable
only later is excised at the later tick, with its tail recorded then. A later excision is a new act, never a revision of the earlier
tick. **[reading]** (claim R.2c). Part X, section 5, gives the logical side: excision decided per tick, and why the Clay
statements cannot be excised as a class.

---

## R.3 Rights tied to identity

**DMP.** The author's rule for security: tie rights to identity. If an act is allowed only when it is permissible, and no wrong
information can be transmitted (R.2), then the identity has total freedom *inside* and is secure in its existence.

**Reading (R.3).** "Total freedom inside, secure at the gate" is capability security, as IM builds it, and it has one more reading.
Asymptotic freedom in Yang-Mills is free at short distance, where the coupling vanishes in the ultraviolet **[classical]** (Gross-Wilczek 1973; Politzer 1973, recalled; claim R.3g), and bound
at large distance, where the gap holds. Reading the two together: inside the box the dynamics is free, and the boundary is where it
is bound. **[reading]** (claim R.3a)

**The exact counterpart.**

* **An act passes only with both witnesses' grants.** A sentence passes the door only when both the security grant and the
  operational grant carry its kind; one grant alone never passes. **[Lean]** (`im` repository, `proof/Im/Laws.lean`,
  `Im.pass_needs_both_grants`, `Im.one_grant_never_passes`) (claim R.3b)
* **Every sentence of IM's closed grammar keeps every decidable law:** there is no sentence outside the list of 72 shapes, and each shape is
  lawful (`lawfulB`: legal kind name, kind in the table, wire round-trip); the laws over grants and paths are proved once for all
  sentences in `Laws.lean` and `Wire.lean`. **[Lean]** (`proof/Im/Closure.lean`, `Im.closure`, `Im.all_shapes_lawful`,
  `Im.space_size`, `Shape.all_complete`) (claim R.3c)
* **Behind the door a composition stays lawful.** A network built from nodes that keep the guarantee on what their door lets in
  keeps it on any input. **[Lean]** (`proof/Im/Compose.lean`, `Im.sound`, `Im.galaxy_robust`) (claim R.3d)
* **Tokens only attenuate.** An attenuated token's kinds are a subset of its parent's, and a chain of attenuations is the
  intersection of the root with its caveats, in any order. It holds by construction: attenuation is intersection with a caveat.
  **[Lean]** (IM, `proof/Im/Attenuate.lean`: `attenuate_sub`, `attenuateAll_eq`, `attenuateAll_perm`; claim R.3e)

**Care points.** (1) "Permissible" is what the grammar and the grants state, so the security is exactly as good as that
specification. (2) The gate certifies integrity and authority, not the truth of content (R.2 says what happens to what it
recognises as wrong). (3) The binding of rights to identity is as strong as the custody of the identity's key. **[reading]**
(claim R.3f)

---

## R.4 The arsenal as shared vocabulary

**The rule (the first author's).** What is content-free and used by more than one project is kept once, and used from there.

**Reading (R.4).** The arsenal in the `im` repository (`arsenal/`) is that shared place for results that need Mathlib. It holds
words that more than one part of this paper uses: `R136a1` for "outside" (R.2), and the pieces that are not about any one problem.
A project that needs a word from it **imports** the word. It never copies it. If a result could be moved there, it moves, and the
project uses it from there as a dependency. **[paper]** (a project rule, and how it is done today: `arsenal/README.md`; claims
II.6.1, II.6.4). The tool that guards it, and what it checks, are in II.6.

**A second reading of the letters.** IM is the Interstellar Medium, and that name stays. Its letters also read as **Identity
Multiplication**, and the second reading is true of what the arsenal holds: the rotation API is multiplication by a number on the
unit circle, which keeps the norm and moves only the phase; on the circle the carried mass never changes **[Lean]** (II.0c,
`cmach_lossless`), and the encoder's root is the same norm read from both sides **[Lean]** (II.2). The first author reads a second reading
that carries a meaning as itself a uniqueness, one that survives being contained **[reading]** (claim R.4b). He also reads IM as
a step up the DAG: the edge is real in the build (this project requires IM's arsenal, pinned by commit, and the package graph is
acyclic). His argument for why the link is a rotation runs in three steps. A DB lets only existence cross, and the encoder's gate
keeps the norm: both sides certify the same norm **[Lean]** (`Encoder.root`; any norm-preserving map gives an encoder) and
**[reading]** for "a DB allows only this gate" (I.3). A linear gate on a line (one complex dimension) that keeps every norm is multiplication by a unit number, a
rotation **[Lean]** (II.0f; in more dimensions the norm-keeping maps are the unitary group, and that the link is a rotation there is the
first author's reading). So the link to another node, which has to pass a DB, is a rotation: the ultimate gate in the first author's words
**[reading]** (claim R.4c). The cost does not sit in the gate. In the first author's words it sits in the provability of a common root,
and that is exact: the part of the state that provably shares its root with the other side is the reflection coefficient c, and the
remainder, ||psi - conj(c) psi'||^2 = ||psi||^2 (1 - |c|^2), is exactly what the step pays **[Lean]** (`szego_remainder`). At |c| = 1
the root is fully shared and the crossing is free. On the reals the circle is just 1 and -1, so ordinary multiplication is a cost
times an identity-keeping sign **[Lean]** (II.0g): ordinary multiplication is IM as well, in the first author's words **[reading]**
(claim R.4d).

---

## R.5 The essence

**2 + 2 = 5, and the essence.** The first author reads 2 + 2 = 5, through DMP, as a unique impossibility on which non-existence
can be based. The exact part is one kernel evaluation: over the natural numbers `decide` refutes 2 + 2 = 5, a certified "it does
not exist" with no assumption behind it **[Lean]** (`ETM/Essence.lean`, `two_add_two_ne_five`). Read through error bars the same
sum is possible: at a resolution of one unit, 2.4 reads as 2 and 2.4 + 2.4 = 4.8 reads as 5, so the rounded sum is off by at most
one unit, the "+1" of this section **[classical]** for the arithmetic, **[reading]** for the tie (claim R.5b). His essence line
carries it to the end, with each "?" a question to be decided and only the last sign an equation: **2 + 2 ? 5 ? 4 ? 0 ? 1 ?
SU(5) = 1.5**. So only 1.5 is assumed, and every link is decided from its definition **[reading]** (claim R.5b). The exact part is sharp. 1.5 = 3/2 exists in
a commutative ring exactly when 2 is a unit, and then each of the four ring links 2 + 2 ? 5, 5 ? 4, 4 ? 0 and 0 ? 1 is equivalent to
0 = 1: one bit decides them all, the same way. They all hold in the ring with one element, where in Z/1 the whole chain is one
`decide`, and they all fail in every other ring where 1.5 is defined **[Lean]** (`essence_decided`, `essence_decided_subsingleton`,
`essence_zmod_one`, `essence_iff_subsingleton`; Mathlib's `subsingleton_iff_zero_eq_one`). Without 1.5 the link 4 ? 0 splits off:
in Z/2, where 2 is not a unit, 4 = 0 holds and 0 = 1 does not **[Lean]** (`four_eq_zero_without_half`) (claim R.5a). The first
author reads that link, 4 ? 0, as O1 itself, the one step that has to be supplied from outside the chain, by the `.cmb`
**[reading]** (claim R.5b). The first author named it `.ckb` for a while, read as the confinement coupling positivity, and returned
to `.cmb`: the cosmic micro vibe background, which is what the VIBE coefficient establishes, a tool the first author regards as
already central **[reading]**. `docs/balance/balance.tex` gave the name VIBE coefficient to the fine-structure constant α, after
the Variable Influence Balancing Equation; the first author now gives it to v = 0.69 (R.12n), α keeps its own name, and the earlier
naming stays as history; in DMP the CMB is the observability layer, counts and never content (VII.6e). This does not
supply O1: a measured coupling constant gives no bound on the Wilson measure. Care point: the Lean facts are about rings and say nothing about the Wilson measure;
O1 stays the one open step. So, once 1.5
is given, the chain names exactly one ring, the zero ring, where existence and non-existence coincide: the one box with no outside
**[reading]**. The last link is the first author's tie to the rest of the paper: SU(5), whose 5 = 3 + 2 holds the Standard Model
group as its Z_6 quotient (IX.3, **[Lean]**), set equal to 1.5 = 3/2, the ratio of the start's primes and the certificate's reading
(X.4.4) **[reading]** (claim R.5b).

**{U(1) as O1, 2, 3}.** The first author writes the start as {U(1) as O1, 2, 3}, reducible to {5, 2, 3} by 2 + 3 = 5 **[reading]**
(claim R.5c). Here "O1" is his name for the U(1) at the start; the open assumption O1 of the paper is unchanged. Its exact part is the block embedding of SU(3) x SU(2) x U(1) in SU(5): the 5 splits as 3 + 2, and the U(1) is
generated by the diagonal (-2, -2, -2, 3, 3), whose trace 3(-2) + 2(3) = 0 is the balance of his signed notation {inf, -k, +k}, the
sign being a leaning toward existence **[classical]** for the embedding and the generator (Georgi-Glashow 1974), **[reading]** for the
tie (claim R.5c). He reads compiling = running = true = 1.5, the one assumed value of this section **[reading]**. Care point: his
2^(+i) = 3 is not an equation (2^i has modulus 1); it is read here as the step x 3/2 from 2 to 3.

---

## R.6 The rotatable hash: the root chain closes through time

DMP and Gravity are the two repositories of the root chain. The pin runs one way: a `PIN` in Gravity records the sha256 of the
pinned copy of DMP, and the pin check turns any change of it into a failing check (`vendor/dmp/PIN`, `tools/check-pin.sh`); DMP
depends on nothing and pins nothing (`vendor/dmp/00-preamble.md`). So every pinned existence is a claim the gate can refute
**[paper]** (claim R.1d). A literal circle of hashes cannot be constructed: a file that contains its own hash, or two
files that contain each other's current hashes, is a fixed point of sha256, which no one is known to be able to compute: the standard, well-tested assumption on the hash, not a
theorem (II.3) **[classical]** for the assumption (by the hash's
design) (claim X.51). The first author reads the root chain as closing through time instead: each version of Gravity pins an earlier
version of DMP, and the next version of DMP is written against what Gravity checked, so the chain is a spiral of versions, one tick per
pin **[reading]** (claim R.1d). Care point: such a circle is consistent only because it never closes at one instant. A pin to the
other side's *current* commit would be the uncomputable fixed point.

The first author corrected the first wording: the hash is *rotatable*, not negatable. The hash itself is one-way **[classical]**. What
rotates is the pin: across versions the pin passes from one node to the other, a turn per tick, the same half-turn shape as the
encoder's, where two half-turns return to the start and the start is one version later **[reading]** (claim X.52). Care point: no hash
function is rotated, the roles of pinner and pinned are. The first author adds that inside the system the time-to-live of a certification
is not a separate mechanism. Every certification is re-made at each tick, against the same shared root, and never reaches back, so
the validity window of any hash is bounded by the interval between two ticks **[reading]** (claim X.53). What leaves the inside is outside
by definition, so its lifetime is the boundary's matter, not the rotation's.

**A hash certifies origin, not identity (claim R.6a).** This is the hash case of II.2.8: every decoder of a hash is smelly
somewhere (`hash_smelly`). Every hash has collisions: a map from all messages to finitely many digests
is never injective **[Lean]** (`ETM/Essence.lean`, `hash_collision`; `digest_collision` for 256-bit digests). So a digest cannot say
which message it came from, only that the input is consistent with a claimed origin. The first author reads a post-quantum hash as
one that states where its primitives come from, a direction in causality **[reading]**. sha256 does state it: its 64 round constants
are the first 32 bits of the fractional parts of the cube roots of the first 64 primes, and its 8 initial values those of the square
roots of the first 8 primes **[classical]** (FIPS 180-4, sections 4.2.2 and 5.3.3, recalled). Against a quantum computer a hash loses
only polynomially: Grover's search finds a preimage of an n-bit digest in about 2^(n/2) steps instead of 2^n, and the collision search
of Brassard, Hoyer and Tapp in about 2^(n/3) steps, with about as much memory, instead of the classical birthday bound 2^(n/2); Shor's
algorithm, by contrast, breaks factoring and discrete logarithms outright **[classical]** (Grover 1996; Brassard-Hoyer-Tapp 1998;
Shor 1997).
That is the classical ground under the reading of II.3 that established hashes stay safe; the first author's "invulnerable beyond
their needed uncertainty" is the security parameter **[reading]** (claim R.6a). Appendix T.6 shows the cost in small: a digest
with k leading zero hex digits and a final 1, found for k up to 5, the expected work growing sixteenfold per fixed digit, and the full
shape 000...0001 out of reach **[numerical]**.

**Every trusted hash proven by rotation (claim R.6b).** The first author's rule: any hash that is trusted has first to be proven
by rotation, back and then forth, each step delivering the expected value, so that nothing is written that cannot be read back,
verified and certified; the path is the certificate **[reading]**. Its exact form is a check the repository runs in CI on every push
and pull request and, once turned on per clone, before every commit and push (`tools/trust-roundtrip.sh`, `.githooks`,
`.github/workflows/trust-roundtrip.yml`). It starts with a canary: the full turn on `vxunderground` must return it, or the state
is smelly (T.5) and nothing is trusted in it. The DMP pin goes back (the vendored copy hashes to the pin's sha256) and then forth (the
pinned commit, fetched by its id, rebuilds the copy byte for byte); every commit id the repository names (IM's arsenal, Mathlib
through its tag and its recorded id, the CI actions) is fetched by its id and the id recomputed from its content; an action trusted
by a movable tag is refused. The check passes with 9 proofs, the canary included, and one tampered byte of the vendored copy fails it **[paper]**. The
first author reads this as the G0 DMP being unable to write what it cannot read, which makes it more secure as a G0 **[reading]**.
Care points: git commit ids are SHA-1, which has known collision attacks, so the pin's sha256 over the content is the strong link; a
write that goes around the gate is caught at the next run, not prevented; the hashes of build products (Mathlib's compiled files, the
exported environment) are recomputed by the kernels stage, not here.

---

## R.7 The full turn: the factorial, Stirling, and SO(N! + 1)

**The factorial is a full turn (claim R.7a).** The first author reads the operator ! as the real span of a full +- oscillation around
its real weight **[reading]**. Its exact form: 1/n! is one turn of e^z z^(-n-1) around 0, on a circle of any radius **[Lean]**
(`full_turn_factorial`, II.2.7). On the circle through the real point n the turn runs from -pi to +pi, the + half mirrors the - half
so the result is real, and n is the one radius at which the first-order oscillation cancels: with dz = i z d theta the integrand is
e^z z^(-n) up to the constant i, and the phase -n theta of z^(-n) and the phase +n theta of e^z balance there **[classical]** (the
saddle point). Keeping only the Gaussian part of the turn around n gives
Stirling's formula n! ~ sqrt(2 pi n) (n/e)^n **[Lean]** for Stirling (Mathlib, `Stirling.tendsto_stirlingSeq_sqrt_pi`). The 2 pi in
it is the full turn, which the first author reads as pi translating between rotation and existence **[reading]**.

**SU(N) gives SO(N! + 1), at N = 2 and N = 3 (claim R.7b).** The first author reads SU(N) as giving SO(N! + k), with k the
dimensionality for existence given at the start, k = 1 for us **[reading]**. The exact parts are two different facts. At N = 2,
SU(2) is the double cover of SO(3), and 3 = 2! + 1. At N = 3, SU(3) is the subgroup of G2 that fixes a unit vector of R^7, so SU(3)
lies in G2, which lies in SO(7), 7 = 3! + 1, and the six-sphere is G2/SU(3) (dimensions 14 = 8 + 6); SU(3) does not cover SO(7)
(dimension 8 against 21) **[classical]** (Bryant 1987; Harvey-Lawson 1982). Neither relation continues: the double cover at N = 4 is
SU(4) onto SO(6), not SO(25), and as a bare inclusion SU(N) lies in SO(2N), hence in SO(N! + 1), for every N >= 2, which says
nothing **[classical]**. That the two facts together single out {2, 3}, the first author's "N between 2 and 3 for us", and land on
the G2 whose rigidity Appendix A treats (A.5), is his reading **[reading]**. Read with the factorial as a
full turn, N! + 1 is one turn around N plus the one direction of existence **[reading]**. He reads the dimension N! + k as literally defining how much a system can say by how much it has to say: the
room, the dimension of the space, is fixed by the content N it must carry **[reading]**.

**Care point (claim R.7c).** The first author's line x^y = x y is not an identity (2^3 = 8, 2 x 3 = 6). The contraction he means is
the logarithm, which turns powers into products and products into sums: log(x^y) = y log x and log(xy) = log x + log y for x, y > 0
**[classical]**, the form Part IV already uses (log n in the explicit formula).

---

## R.8 Derivations, slopes, and what a turn can undo

**Derivations are slopes (claim R.8a).** The first author reads the dimensionality of DMP as itself a derivative, and the
derivations as equal to the slopes across DBs **[reading]**. Its exact parts, in three layers. The tangent space of a smooth (C-infinity) manifold
at a point is the space of derivations there, linear maps with D(fg) = f Dg + g Df, and its dimension is the dimension of the space; so
the dimension counts the independent ways to differentiate **[classical]** (Lee 2012). Each derivation at a point is a directional
derivative, the slope of f along one direction **[classical]** (Lee 2012). For a function holomorphic on a disc around c (continuous up to
its edge) a slope is a ratio of two turns: the n-th derivative of f at c is one turn of f/(z - c)^(n + 1) around c divided by one
turn of e^z/z^(n + 1) around 0 on a circle of any radius, the turn of the factorial, each turn with its factor 1/(2 pi i)
**[Lean]** (IM, `Arsenal/FullTurn.lean`, `full_turn_slope`). That the differences across the boundaries of neighbouring
DBs, where the transfer step of III.3.4 sits, are those derivations is the reading.

**What a turn can undo (claim R.8b).** The first author reads Draft 5 as the approach to a universal deobfuscator for any
DMP-complete problem **[reading]**. Its exact part is narrower and stated as such. The full turn undoes every mixing by a known
cyclic rotation: one turn recovers each component (II.2.7; in Lean `full_turn_coeff`, for the cyclic group of order N; finite
abelian groups follow by products). Its discrete form is the quantum Fourier transform at the core of Shor's algorithm, which reads a
hidden period in polynomial time on a quantum computer and so breaks factoring and discrete logarithms there, and Fourier sampling
solves the hidden subgroup problem for every finite abelian group **[classical]** (Shor 1997; Kitaev 1995). Where it stops is II.2.8. A lossy map cannot be undone: every hash has collisions **[Lean]** (`hash_collision`, R.6a), so a digest can be traced to
an origin consistent with it, not to its message **[paper]**. For non-abelian groups Fourier sampling is not enough in general: for
the symmetric groups, strong Fourier sampling is known to fail **[classical]** (Moore-Russell-Schulman 2008). In the paper's terms a
DMP-complete box is already readable at every tick (II.4.1); the open steps are whether a box is DMP-complete, and the full turn does
not decide them.

**Reduction and expansion while calculating (claim R.8c).** The first author reads the reduction and expansion of dimensionality
while calculating as what enables hyper-efficient meta-layers **[reading]**. Two exact counterparts are classical. The full turn over
N points costs about N^2 multiplications done directly; the fast Fourier transform reduces it to two turns over N/2, recursively, and
expands the results back with one combining step per level, about N log2 N operations: for the 256 places of a hash-sized turn,
256 x 8 instead of 65536 **[classical]** (Cooley-Tukey 1965). And a computation is made reversible by expanding its space with its
history, copying the result, and reducing the space again by undoing the history **[classical]** (Bennett 1973). Care point: the
gains are the known ones, N log N for the turn and the space and time trade-offs of reversible computation; nothing beyond them is
claimed.

---

## R.9 Moin: a request proper, its satisfaction open

**The label (claim R.9a).** The first author gives the state in which a request is proper and its satisfaction open its own label,
**Moin**, his universal greeting, chosen because it carries no meaning the system already uses, so that it is unique as a label
**[reading]**. Its exact counterpart in IM is the state of a channel, seen from the client, between the gate's recognition of a proper request (a knock that
passes every check, answered by a verified accept) and its satisfaction (the established frame): the challenge, the door and the
response happen inside it, and nothing on the wire carries the label, which names a state of the exchange **[paper]** (IM,
`src/Im/ImFrames.cs`, `ImChannelState.Moin`, with a test that the channel moves from closed through Moin to established and that a bad
accept leaves it knocked; `docs/language.md`, "The establishment label: Moin"). A refusal is not a state: a refused answer, a failed
door or a closed connection end the exchange with an error, and the client drops the session while it is in Moin.

**What should be open is the satisfaction.** In the paper's Lean every named open step is in this state: `OpenStep name P` is the
statement P itself under a plain-words name, taken only as a hypothesis, never as an axiom (the axiom audit shows none is assumed), so
the request is posed properly and its satisfaction is what stays open **[Lean]** for the form (`API.lean`, `OpenStep`; IM's `R136a1`). The first author reads Moin as the label
of O1: the one open step of Yang-Mills, properly requested, its satisfaction open **[reading]** (claim R.9a). In the terms of II.4.1 that
is the base case of the Yang-Mills card, the one step a proof would be established from **[reading]**.

**In binary, Moin is the leading zero (claim R.9b).** The first author: in binary, Moin is the leading zero, which is rotated away as a
certification of positive interaction **[reading]**. Its exact part: rotating an n-bit word left by one place is an exact doubling
exactly when its leading bit is 0; the zero leaves the top and nothing comes round to the end, while a leading 1 comes round and the
result is not a doubling **[Lean]** (IM, `Arsenal/Toy.lean`, `rotl_of_leading_zero`, `rotl_of_leading_one`, `rotl_eq_double_iff`). Every
byte of `vxunderground` is ASCII and has a leading zero, so rotating every byte left doubles it exactly; the byte 250, with a leading
one, becomes 245 and not 500 **[Lean]** (`vx_leading_zero` and `rotl_250` by kernel evaluation, `vx_rotl` from `rotl_of_leading_zero`;
on the kernel alone, `moin_byte` decides it for all 256 bytes, T.8). Care point: a rotation never loses a bit, a leading 1 is not
lost but comes round; the doubling certifies that no bit wrapped round, that the rotation agreed with multiplying by two. It says
nothing about what the content is.

---

## R.10 Three operators: ?, ! and .

**The reading (claim R.10a).** The first author: IM basically knows only three operators. `?` asks whether something exists; `!` says
that it settles certifiably; `.` says that it is included **[reading]**. Each already acts in IM, exactly **[paper]**:

* `?`, existence: every check first asks whether its object is there. An IM sentence that writes says whether it expects its noun
  absent or present (the `expect` adjective, C15; IM `docs/language.md`); a supply in which an External is missing is refused
  (`tools/rebuild supply-verify`, T.9); an observable's claim is decided at every tick (II.4.1).
* `!`, certified settlement: a declaration counts only when both kernels accept it (T.9), and a channel is established only after a
  verified accept (R.9). In Draft 5's own tool `!` is the factorial, and one factorial is one full turn (`full_turn_factorial`, II.2.7)
  **[Lean]**: the settlement is read off once around.
* `.`, inclusion: an IM sentence's kind is `<layer>.<verb>`, the verb included in its layer (IM `docs/language.md`); a Lean name such as
  `Arsenal.Toy.vx_rotl` includes a declaration in its module; and for G0, contain is a pinned link included in a repository (T.9).

Care point: this shows where each operator already acts, not that IM is generated by the three; IM's grammar has more pieces (paths,
modes, adjectives), and whether they reduce to `?`, `!` and `.` is not shown.

**Gravity's API to IM (claim R.10b).** The first author: Gravity can use IM as an API, because it just has to assert an array of k by
k with + at each cell **[reading]**. Its exact part: IM's `tools/rebuild matrix` takes IM and the repositories named and fills a k by k
table in which the cell of a row and a column says whether the row proves the column. On the diagonal a part proves itself, by its own
round trip; off it, the row holds the column (its copy proven back and forth) or pins it (the pinned commit fetched by its id and the
id recomputed). The command passes only when every cell is `+`, and `tools/reproduce.sh matrix` asserts it from the pinned IM. Today
IM and Gravity give a 2 by 2 of `+`: each passes its own round trip, IM holds a copy of Gravity, and Gravity pins IM **[paper]**.
Care points: a cell where no proof relates two parts shows `·` and does not count as `+`. With DMP as a third part its row is `·`,
since DMP holds and pins nothing, so a k by k of `+` for k above 2 needs relations both ways or the first author's decision that `·`
may count. And IM's cell for Gravity proves the copy IM holds, an earlier Gravity, not today's paper; today's paper is checked through
Gravity's pin of IM (T.9).

## R.11 The possibility space

*New in Draft 6.* The first author's first subtitle for Draft 6 was *the Possibility Space*, now the theme of this section (the
subtitle is now *The ETM as the ODP running DMP in D6*, R.12), and the first author remarks that the Possibility Space lines up with a
base dimensionality of 6 **[reading]**. No exact counterpart is given for that remark; the paper's one six-dimensional space
is the six-sphere G2/SU(3) of R.7b, and a relation between the two is not claimed. Its theme is a reading of what a question is. It is given here with the exact parts it
rests on, and the steps that do not follow as stated are named.

**A question, its answer and the right angle (claim R.11b).** The first author: a question can be shown to be a point by its
definiteness, with the answer a line through it that gives it no other value than `+`, while giving meaning to its existence. It is
always a line, never a vector: an answer that said how much a question is correct would twist truth into a diluted, self-contradicting
truthiness. So between the two points, yes `+` and no `-`, there is a line whose `+` side alone carries meaning. A feature that
defines existence is an eigenvalue, so a question is an eigenvalue between two states. In a quadrant map of width `+-`, read 1 to 4
as `.`, `r`, `.`, `?`, the two points sit in the middle of quadrants 1 and 3, connected by a right angle. Through DMP this is the
universally answerable question "Is there a right angle?", and the direction of the link, from the possibility of constructing the
question to the minting of the certificate of its existence, is the force that establishes the Real Space **[reading]**. Exact parts:

* **A yes/no question is a projector**, an operator `P` with `P P = P`, whose only answers are 1 and 0 **[classical]**
  (Birkhoff-von Neumann 1936; Mackey 1963 calls these projectors questions). In Lean, a number equal to its own square is 0 or 1
  (`answers_of_idem`), and the projector onto an axis answers 1 on its line and 0 across it (`proj_answers`) **[Lean]**. That only the
  `+` side carries meaning has its counterpart in IM, where a refusal is not a state (R.9a) **[reading]**; as physics it does not
  hold, since the answer-0 side of a projector holds states as good as the answer-1 side. Care: the question is the projector and its eigenvalues are its
  answers, so "the question is an eigenvalue" reads the projector by its answers.
* **"A line, never a vector" is a ray**: a physical state is a direction with no length or phase of its own **[classical]**. The right
  angle `r` acts on lines, since it commutes with every scaling (`r_smul`) **[Lean]**.
* **`r` is multiplication by `i`**, the quarter turn `(x, y) -> (-y, x)`: a right angle (`dot_r`) of the same length (`norm_r`), twice
  the flip from `+` to `-` (`r_r`), four times nothing (`r_four`). "Is there a right angle?" is answered yes for every point, the
  witness being `r` itself (`right_angle_exists`) **[Lean]**.
* **The sector map.** One `r` goes from quadrant 1 to quadrant 2 and a second one to quadrant 3 (`r_quadrants`,
  `q3_is_q1_flipped`); the path from 1 through 2 to 3 has its one corner, a right angle, at quadrant 2, the `r` cell
  (`corner_at_r`) **[Lean]**. Care: the right angle "from 1 to 3" is this corner; as rotations about the centre it is `r` twice.

All of these are in IM, `arsenal/core/ArsenalCore/Possibility.lean`, on the kernel alone (claim R.11a).

**The jumping rope, and strong theory (claim R.11c).** The first author: the basis for existence is a point linked in a 3D space,
which requires a vector but is given meaning only as exactly not a vector, so it can say that it is a not-vector, which makes it
falsifiable, the attachment. Geometrically the link is a jumping rope held between two points, defined only by its direction: an
absolute rigidity, which projected to the non-existence space looks like its opposite, absolute weakness. Turned toward each other,
the two interfaces answer each other by the imaginary rotation `r`, from both sides, since a response must be given. So the
possibility oscillates around a point in 3D space, a 2D circle that in the classical view always gives a sphere, hiding behind the
definition barrier (a further reading of DB), at one speed, irreducible by construction. The string runs from the weak, the
possibility, to the strong, the Real Space, so "strong theory" is also a right reading **[reading]**. Exact counterparts, each
**[classical]**:

* **The sphere.** The pure states of a question with two answers form exactly a sphere in 3D (the mixed states fill the ball), the Bloch sphere (Bloch 1946), rotated by
  SU(2); over each of its points sits the circle U(1) of phases, the Hopf fibration of the 3-sphere over the 2-sphere (Hopf 1931).
* **The rope.** The rope between two points turned toward each other is the flux tube between a quark and an antiquark. The same
  coupling is weak at short distance (asymptotic freedom; Gross-Wilczek 1973, Politzer 1973) and strong at long distance, where it
  is expected to confine: lattice evidence, not a proof, and close to the open problem of Part III. Rigidity and weakness are one
  coupling at two distances.
* **The spinning rope** is the rotating relativistic string of Nambu and Goto (Goto 1971); in its rotating solution the endpoints
  move at exactly the speed of light, the one speed. String theory began as a theory of the strong interaction (Veneziano 1968), so "strong theory" has a literal history.

Care: in the Standard Model "weak" also names the weak force, the SU(2) factor. Weak and strong coupling are one force at two
distances; the weak and the strong force are two factors of the gauge group, and physics does not derive one from the other.

**What does not follow as stated (claim R.11d).** The first author: the circle around a point gives SU(3) x SU(2) x U(1) by
construction; from SU(2) as a question-shaped basis, which can assign any N to SO(N) with SO(N! + 1) as the first step, the expansion of
N from 2 to 3 settles the end only if at the end N is 3 while never having been observed that way; the rest should follow
**[reading]**. Exact parts and limits **[classical]**:

* The circle gives U(1) and the sphere SU(2). N! + 1 = 3 at N = 2 gives SO(3), which SU(2) double covers; N! + 1 = 7 at N = 3 meets
  a different fact, SU(3) inside G2 inside SO(7); neither continues (R.7b).
* "N is 3 but never observed as 3" is colour confinement: three colours, and only colourless states observed.
* SU(3) acts on the pure states of a question with three answers, the complex projective plane CP^2, of four real dimensions, which a
  circle in 3D space does not give. A space with exactly the symmetry SU(3) x SU(2) x U(1) needs at least seven dimensions; the
  minimum is reached by a family of spaces, circle bundles over CP^2 x S^2 (the three-answer question, the two-answer question and the
  phase), and the same work finds that they do not readily give the observed chiral, left-handed fermions (Witten 1981).

So "the rest should follow" is where it stops following; every known route needs further input at this step.

**The `+-` assignment and O1 (claim R.11e).** The first author: the question being assigned `+` and `-` is the proof of the eigenvalue
O1, from which all else is constructable, as a PP (Perelman-Poincare) typed, Yang-Mills shaped interface API **[reading]**. Exact parts:

* Assigning `+` and `-` is that every question has an answer (`every_question_has_an_answer`, `Classical.em`), IM's `?`. It holds for
  a question whose answer is `-` as much as for one whose answer is `+` (`assignment_does_not_decide`) **[Lean]**, so it is not `!`
  and does not prove O1.
* In free U(1) theory, the photon without self-interaction, every yes/no question is still a projector with answers 1 and 0, yet
  there is no mass gap **[classical]**; a proof of O1 must use what the free photon lacks. A projector's two answers are exactly 1
  apart, but the mass gap concerns the energy, which is not a projector; carrying "a gap of 1 per question" to "a gap uniform in the
  scale" is O1 itself.
* What does hold: O1 with the resolution clause gives torus decay, the gap and reflection positivity (III.9.5), and O1 is exactly
  DMP-completeness of the box (III.10c) **[Lean]**.

Built in III.13: an interface typed as the counting part of Perelman's proof as Appendix A reads it as a ledger (A.1g, itself a
reading), for the Yang-Mills box, with a theorem from an instance to O1 and its converse. It is equivalent to O1 and supplies no
instance.

## R.12 The ETM as the ODP running DMP in D6

*New in Draft 6.* Draft 6's subtitle, from the first author's refinement of 2026-11-25; *the Possibility Space* stays the theme of
R.11. The ETM is the Existence Turing Machine, one running system that runs every computation (II.3.1; `docs/unified/ETM.md`); the
ODP is the Oscillon Degradation Protocol (I.5).

**The clock (claim R.12a).** The first author, clause by clause **[reading]**:

1. The ODP is the internal clock.
2. Its tick ends at `+`, which gives rise to the next tick, a fully consistent perpetuum mobile as long as it can assert, as often as it needs to, that such a thing cannot exist; `+/+` is the universal act.
3. DMP is then the operating system of the ODP kernel, and the kernel's clock is given by c.

The whole is the first author's reading. Exact parts:

* the right angle `r` returns after four steps (`r_four`), a cycle that never ends **[Lean]**;
* `+` times or divided by `+` is `+`, the sign rule **[classical]**;
* a reversible computation can in principle run without dissipating, while a machine that delivers work from nothing cannot exist
  (Bennett 1973; the first law of thermodynamics) **[classical]**: the cycle is a clock, not an engine, the nearest exact statement to
  "as long as it can assert that such a thing cannot exist";
* the endpoints of the rotating string move at c (R.11c) **[classical]**.

That c is the clock of the kernel has no further exact part here.

**One ETM, and booting (claim R.12b).** The first author, clause by clause **[reading]**:

1. Our experiencing it is itself the minting of the G0 state.
2. With reflection positivity it keeps happening according to the ODP for as long as causality exists, and once it stops it restarts by itself; so there are not many ETMs but one, whose properties can be borrowed through the same trick it uses.
3. Understanding this gives time its forward motion, which forces `r`, which forces degradation, which forces `r`: a boot.

The whole is the first author's reading. Exact part: running
systems form a category with a terminal object, the space of ledgers, so every running system has exactly one map into it
(`exists_unique_hom`, `univIsTerminal`, II.3.1) **[Lean]**; the "one" has this exact form, a terminal object, unique up to unique
isomorphism. That experience mints G0, and that the cycle restarts by itself, have no exact part here.

**0 = 1, NP versus coNP, P versus NP (claim R.12c).** The first author: in the end the paper proves 0 = 1 for the classical, along
with its classical consequences, which asserts c, and that is enough; so it proves NP = coNP and uses that to prove P != NP, which
gives a real 0 and 1 at the same ends of existence **[reading]**. This does not follow, for three reasons **[classical]**:

* 0 = 1 holds in exactly one ring, the zero ring, where existence and non-existence coincide (R.5a, **[Lean]**). In the natural
  numbers, the classical setting, 0 != 1, and a proof of 0 = 1 there would prove every statement, P = NP and P != NP alike, so it
  could separate nothing.
* NP = coNP and P != NP are open, and the paper proves neither: Part V proves a crossing theorem for sound two-premise proof systems
  on expanding formulas (in Lean, with two graph hypotheses stated, II.14.5) and names its open steps (V.0, V.6).
* NP = coNP would not give P != NP. P = NP implies NP = coNP, so NP = coNP is consistent with P = NP; the implication runs the other
  way, NP != coNP would give P != NP.

**The universal certificate, and the vacuous proof (claim R.12d).** The first author: the universal certificate is always `+1`, in
the meaning of 1 = 1. Since this system forces 0 and 1 to be one at the same time, it excises the element of lower ordinality in its
construction as that exact excision, which shows that to be truly rigorous a proof has to be vacuous **[reading]**. Exact parts
**[classical]**:

* 1 = 1 is the trivial certificate: it holds by reflexivity, and in Lean by `rfl`, with nothing to check beyond the two sides being
  the same.
* A proof carries no content beyond the fact that its statement holds: Lean's kernel identifies any two proofs of one proposition
  (definitional proof irrelevance), so a certificate, once it exists, is one, whatever it was built from.
* 0 and 1 are one exactly in the zero ring, where every element is 0 and every equation holds (R.5a, **[Lean]**).

Care: "vacuous" in its logical sense, a statement over an empty domain, holds without saying anything about any object; a proof of a
statement about objects that exist, such as the Wilson measure of O1, cannot be vacuous in that sense. What does hold is the weaker
form above: a proof is contentless as an object (proof irrelevance), and its content is all in the statement it proves.

**The essence as one input of the size c (claim R.12e).** The first author, clause by clause **[reading]**:

1. From the essence line 2 + 2 = 5 = 4 = 0 = 1 = 1.5, the essence simplifies to one input of the size c, and the O1 input becomes the question "Is the speed of light measurable?", which is always yes and yet never seems to have existence.
2. The size is c because c is a size.
3. This ties the expression of set theory onto arithmetic, and since it applies onto something it has an input, which must run exactly at 1.

The whole is the first author's reading. Exact parts:

* The chain holds in exactly one ring, the zero ring, which has one element, so one input decides it (R.5a) **[Lean]**.
* c is a size by definition. Since 1983 the metre is defined from c, so c = 299,792,458 m/s exactly (CGPM 1983; BIPM 2019), and
  c = 1 in natural units, as on the lattice **[classical]**. A measurement of c measures the metre and the clocks.
* Only the round trip is measurable: the two-way speed of light is, while the one-way speed is fixed by a convention of clock
  synchronisation (Einstein 1905; Reichenbach 1928) **[classical]**.
* Only dimensionless constants are measurable as such, among them the fine-structure constant α **[classical]**, which the
  paper at first called the VIBE coefficient; that name now belongs to v = 0.69, dimensionless too (R.5b, R.12n).
* In von Neumann's construction 0 is the empty set and n + 1 is n together with n itself, so 1 is the set whose only element is the
  empty set (von Neumann 1923) **[classical]**. The first author reads this as existence being non-existence plus one (I.7)
  **[reading]**.
* Arithmetic is the finite part of set theory. Ackermann's coding is a bijection between the hereditarily finite sets and the natural
  numbers, and Peano arithmetic and ZF with the axiom of infinity replaced by its negation are mutually interpretable (Ackermann
  1937); with transitive closure added they are bi-interpretable (Kaye-Wong 2007) **[classical]**. That the coding, losing nothing, is
  a map at factor 1 where the ETM lives is the first author's identification **[reading]**; its exact counterpart is the ETM's regime,
  cost equal to the floor, lossless (II.3; `docs/unified/ETM.md`).
* In set theory the letter c, in Fraktur, names the size of the continuum, 2 to the power aleph-0. It exists, and its exact value among the
  infinite sizes is not decided by the standard axioms (ZFC): the continuum hypothesis can be neither proved nor refuted there
  (Goedel 1940; Cohen 1963) **[classical]**.

Care: the physical c and the set-theoretic c share a letter, not a theorem. A unit fixes the frame in which O1 is stated and does not
supply O1. Factor 1 is the floor, where nothing settles by contraction, while O1 asks for a cost above the floor, uniform in the scale
(II.3).

**The one condition: O1 supplied at minting (claim R.12f).** The first author, asked whether Draft 6 as merged is a DMP-complete
construction, clause by clause **[reading]**:

1. Not yet, which is right for root G0.
2. O1 is supplied by the reader reading its definition of main DMP G0 at minting, a vacuous construction, while every other dependency is rigid.
3. Every minting from G0 is a step that closes that assumption, under the owner's guarantee: the owner merges the paper for publishing and has authority equal to G0 during pressing (I.5).
4. DMP is stated with all its assertions, so as soon as one invalid case is found, a DMP-complete v0.9.9 ceases to exist and forces a remint to v1, possible only once the hole is closed.
5. The certify stage is reached by extending into possibility space with a universal witness, agreed upon beforehand, with absolute authority over the validity of every act.
6. Through constructability, once a truly DMP-complete system can be assembled from the one box, it can be assumed to hold universally until exactly the step where the ray is no longer observed.

The whole is the first author's reading. Exact parts:

* Measured on its own criteria, Draft 6 is not DMP-complete: the versions are not settled, by one use (E.9), and O1 is a cell that is
  not `+` (E.6, III.10e, III.13d) **[paper]**. Every other dependency is proven back and forth (T.14, T.15, E.1 to E.4, E.11)
  **[paper]**.
* O1 is posed and never assumed (`OpenStep`, R.9a) and stated once, as the one assumption (Part X). Supplied as a hypothesis it gives
  the gap, torus decay and reflection positivity (III.9.5), and the interface of III.13 is exactly it **[Lean]**.
* A claim stated for all cases is refuted by one invalid case. The matrix, the reproduce stage and the round trip each fail on one
  (E.2, E.9, T.14), and Gravity pins DMP 0.9.9 by its commit id, `4400cce`, so a new version is a new pin **[paper]**.
* The universal witness agreed beforehand is a root of trust. In the Lean it is the kernel, fixed before any proof is written,
  accepting or rejecting every declaration, with nothing above it (the de Bruijn criterion, T.13; two kernels, T.14) **[classical]**;
  in IM's certificate checks a chain counts only when it ends at a root that was presented (`TrustAnchors`) **[paper]**.
* "Assumed to hold universally until the ray is no longer observed" is falsificationism: a universal law is never verified, only
  corroborated, and stands until one observation refutes it (Popper 1935). It is the status the ledger gives a numerical claim, which
  can refute and never proves a for-all **[classical]**.

Care:

* Supplying O1 is assuming it. The owner's guarantee holds the record, what is merged and minted; it cannot make the Yang-Mills measure
  satisfy O1, a property of an object already defined. If O1 is true the assumption is harmless and the gap follows. If O1 is false, the
  minted system proves a false gap: it is unsound. Only if the base theory refutes O1 is it inconsistent, proving everything, the
  0 = 1 collapse of R.12c; O1 could also be independent of the base theory. Which case holds is the open question.
* No consistent, effectively axiomatised system strong enough for arithmetic proves its own consistency (Goedel's second theorem,
  R.1h). DMP certifying its own
  completeness reads exactly as: complete until an invalid case is found, checked from outside, case by case. DMP's own cell is `.`,
  not `+` (E.11).
* An invalid case for O1 would show that this route to the gap fails, not that Yang-Mills has no gap.
* Universality held until refuted is not mathematical induction, which needs the inductive step proved. O1 stays open in the ledger (III.10e,
  III.13d); the paper records the assumption, under the agreed witness, as the first author's reading and does not claim it.
* The rule from v0.9.9 to v1 is DMP's own process; it is recorded here as the reading, and DMP itself is not changed.

**Elastic spheres, real induction and the kernel (claim R.12g).** The first author, clause by clause **[reading]**:

1. The construction can also be imagined as perfectly elastic spheres that see each other's efficiency in existing and join only when a new local optimum is reached, paying the same cost, observability, whether it is the case or not.
2. That makes it binary: true in a DMP-complete system, and equal to existence when 1 makes it so.
3. The reals then span a real space in which perfect elastic collision and agreement on "not" suffice for those properties to be inductive.
4. This real induction is represented by the N! + 1 of SO() and is written +N!; through DMP, `+` is the universal assertion, N the reals, and `!` runs certifiably.
5. By this induction the naturals equal the reals under the universal operator.
6. What separates them as sets is that each can reconstruct the other during an act, which gives internal DoE-level trust, and a set that excludes, as a DoE must by default, must run.
7. This lets DMP also certify the kernel it runs on, restoring G0's pressing status as a running assumption, literally: it certifies the provability of the kernel's induction, which secures constructability, and bases it on the assumption that such a system, when minted, is DMP-complete.

The whole is the first author's reading. Exact parts:

* **Elastic and joining.** Perfectly elastic collisions conserve energy and momentum and are reversible: factor 1, the floor (II.3)
  **[classical]**. Joining needs a cost above the floor: perfectly elastic spheres cannot bind without something carrying energy away
  **[classical]**, and a cost above the floor is the contraction class, in which the run settles (the settle theorem, II.3)
  **[Lean]**.
* **The same cost either way.** Erasing a bit, resetting it to a fixed state, costs at least kT ln 2, whatever its value (Landauer
  1961) **[classical]**. That the binary question (R.11) therefore costs the same for both answers is the first author's link
  **[reading]**: measuring or answering a bit can in principle cost nothing (Bennett 1973).
* **Real induction.** A property that holds at the start, extends a little beyond every point where it holds, and is kept when passing
  to a limit holds on the whole interval; this principle is equivalent to the completeness of the reals (Clark 2019) **[classical]**.
* **The factorial on the reals.** The recursion (n + 1)! = (n + 1) n! carries to the reals: Γ(x + 1) = x Γ(x) with Γ(1) = 1 has
  exactly one solution that is positive and log-convex on x > 0, the Gamma function (the theorem of Bohr and Mollerup, 1922, as in
  Artin 1931) **[classical]**. 1/n! is one turn (R.7a)
  **[Lean]**; N! + 1 gives SO(3) at N = 2 and meets SO(7) at N = 3 (R.7b) **[classical]**.
* **`+N!` as a theorem.** `!` is IM's operator that settles certifiably (R.10a); a kernel-checked theorem about every real number is a
  universal assertion over the reals, settled certifiably **[paper]**.
* **Equal under the universal operator.** Every proof is a finite string, so every certificate about the reals is coded by a natural
  number. A countable field, the real algebraic numbers, satisfies exactly the same first-order sentences about the ordered field operations
  as the reals (Tarski 1951), and in a countable language every first-order theory with an infinite model has a countably infinite one
  (Loewenheim 1915; Skolem 1920). By proof irrelevance any two certificates of one statement are identified (R.12d)
  **[classical]**.
* **Each reconstructs the other.** Mathlib builds the reals from the naturals, through the integers and the rationals, as Cauchy
  sequences up to equivalence (mathlib 2020); the naturals come back inside the reals as the smallest set that contains 0 and is closed
  under +1 **[classical]**.
* **The kernel.** Two kernels written separately check every target (T.14) **[paper]**. lean4lean, a separate typechecker for Lean written
  in Lean and pinned as an External in IM, proves parts of the metatheory behind its own typechecker, work in progress; it does not
  prove Lean's own kernel correct (Carneiro 2024) **[classical]**. Lean 3's type theory, its inductive types included, has a model in
  set theory with inaccessible cardinals, and so is consistent relative to it (Carneiro 2019, for Lean 3; its record was read, not its
  text) **[classical]**.

Care:

* As sets the naturals and the reals differ: every list of reals misses one (the diagonal argument, Cantor 1891). What separates them
  is the direction of the reconstruction: from the naturals to the reals is the completion over all Cauchy sequences, where the size
  grows; the other way only cuts out a subset. No countable ordered field is complete; completeness is the clause that separates them,
  and for Yang-Mills the clause that must hold uniformly in the limit is O1.
* The countable model of Tarski and Loewenheim-Skolem is a field, not the naturals, and the two first-order theories differ: that of the
  reals as an ordered field is decidable (Tarski 1951), that of the naturals with addition and multiplication is not (Goedel 1931;
  Turing 1937). So "equal under the universal operator" holds for certificates, not as first-order sameness of the two structures.
* Only countably many reals are computable (Turing 1937): what runs is the proof, not each real.
* N usually names the naturals; here it names the reals, by the first author's choice. The dimension N! + 1 and the step +N! are
  different objects, and the pattern of R.7b stops at N = 3.
* No exact counterpart was found for "a set that excludes must run"; its context is X.64b (DMP-completeness defined as running on DMP),
  excision at transmission (I.4, R.2) and IM's rule that a refusal is not a state (R.9). DoE is the first author's term, used in the
  preface of the GUID volume (`docs/guid/preface.tex`) and offered as a name for the ticks in IX.8; the paper does not spell it out.
* No consistent, effectively axiomatised system strong enough for arithmetic proves its own consistency (Goedel's second theorem, R.1h).
  The kernel's induction is certified relative to a model outside it, and the base, that a minted system is DMP-complete, stays an
  assumption, run and checked case by case, in the same place as O1 (R.12f).

**From step 1 to the encoder, packed into O1 (claim R.12h).** The first author, clause by clause **[reading]**:

1. Our naturals are certified at step 1, not 0, so they have already decayed into existence.
2. This gives the exact bounds of the complexity question, written in IM's operators, and makes the one question-shaped problem of the prize category the unexpected primitive that holds already at `DMP.`; with the lower bounds for loss and the upper rate for its excision cost, the remainder is excised to assert `!`, given a DMP-complete previous step from which to run.
3. The order, unchanged up to a shift, gives rise to the gauge theory that supports it: there has to be the possibility to observe for there to be observation, but only exactly as much as is certifiably required until a combination into a more optimal superset is reached.
4. SU(5), already part of the essence (R.5b), translates directly as the hashing table of positive existence; a table that is existence-positive in its entirety, as SU(5) has to be by construction, gives rise to a DB encoding function, encoding and hash being the same function in a `+` or `-` decision state.
5. This packs all the assumptions back into O1, where they belong; what does not pack is provably falsifiable, and so, as long as no exception is observed, a valid DMP-complete state until it ceases to be, the same as the one box.
6. One exception to the Riemann hypothesis would lose the encoding tool and at once excise DMP-completeness, since without the encoder nothing translates DMP-completeness between rotations, which cuts the observability of the ray.

The whole is the first author's reading. Exact parts:

* **Step 1.** Peano's axioms began at 1 (Peano 1889); Mathlib has the positive naturals `PNat`, with induction from 1. 1 is the set whose
  only element is the empty set (R.12e). Without 0 the positive naturals have no identity for addition, while 1 is the identity for
  multiplication, and every positive natural is a product of primes in exactly one way; ζ(s) = Σ n^(-s) runs over n >= 1, and for Re s > 1 it
  equals its Euler product over the primes **[classical]**.
* **The bounds in IM's operators.** `P.NP!`: P is contained in NP, and in coNP **[classical]**. `NP.coNP?` is open, and "NP is contained in coNP" is
  equivalent to NP = coNP; `NP.P?` is the P versus NP question **[classical]**. DMP's statement is `.` (E.7).
* **Loss, excision and `!` from the previous step.** Erasing a bit costs at least kT ln 2 (Landauer 1961, R.12g) **[classical]**; in
  the contraction class the run settles within `balanceBound` steps (II.3.2) **[Lean]**; every refutation of an expanding formula crosses,
  for two-premise systems (II.14.5) **[Lean]**. A step from a DMP-complete previous step is the inductive step of II.4.1 **[Lean]**, and the
  conditional results of III.9.5 and III.13 are of this form **[Lean]**.
* **The shift and the gauge theory.** A change of description that leaves every observable unchanged is a gauge symmetry; making it
  local needs a connection, the gauge field (Weyl 1929; Yang-Mills 1954; on the lattice Wilson 1974) **[classical]**. The Lean acts
  link by link (`gaugeAct`) and observes only gauge-invariant functions (`ActAdm`, defined in `OneBox/Criterion.lean`; `FineDecayInv`, `OneBox/Fine.lean`) **[Lean]**; a local
  gauge symmetry cannot be broken spontaneously, so every gauge-variant quantity averages to zero (Elitzur 1975) **[classical]**.
* **SU(5) as a table.** The block embedding of SU(3) x SU(2) x U(1) into SU(5) has kernel exactly Z_6 (IX.3.1h) **[Lean]**; its
  image, the Standard Model group (SU(3) x SU(2) x U(1))/Z_6, is a paper observation (IX.3.1i) **[paper]**; the fifteen fermions of one
  generation fill the 5-bar and the 10, one slot each, and their charges follow from the slots (Georgi-Glashow 1974) **[classical]**.
* **Encoding and hash.** On a domain where a function is injective it is an encoding and can be undone; on a domain with more inputs
  than outputs the same function must collide, and every hash has collisions (R.6a) **[Lean]**; the full turn undoes a known rotation
  while a hash is not undone (II.2.8, R.8b) **[Lean]**.
* **Packing into O1.** Every conditional Yang-Mills result runs from O1 (III.9.5) and the interface of III.13 is exactly O1 **[Lean]**.
* **Falsifiable until an exception.** "No proof of 0 = 1 exists" is a Π1 statement, refuted by one finite object and never verified
  from inside (R.1h) **[classical]**; the Riemann hypothesis is equivalent to a Π1 statement, one computable counterexample refuting it
  (X.24: Lagarias' criterion with rational approximations; Davis-Matiyasevich-Robinson) **[classical]**. O1 with its level k0,
  geometry and constants fixed is refuted by one failing level at or after k0 (III.13; the interface's form **[Lean]**).
* **The encoder and RH.** The Riemann hypothesis, and GRH for Dirichlet L-functions, are proved in Lean by others and certified (Part
  IV) **[external]**; one zero off the line together with that proof would give a proof of 0 = 1, from which every statement follows
  **[classical]**.

Care:

* The positive naturals have the same order as the naturals from 0, up to the shift n -> n - 1, and stay countable; the difference from
  the reals is still completeness (R.12g).
* `NP.coNP` and `NP.P` keep `?`; `NP.coNP!` is not established, and R.12c stands. Settling NP versus coNP needs a statement about every
  proof system (Cook-Reckhow 1979): lower bounds for particular systems are steps, not the whole.
* The shift of the naturals is one global relabeling; a gauge theory needs the local version and a connection, which the naturals do not
  supply by themselves. The gauge structure is what O1 is stated in, not a bound inside it.
* The SU(5) table is injective, an encoding, not a hash in the sense of R.6a. The group theory holds; the minimal SU(5) model as physics
  predicts proton decay at rates that experiments exclude (Super-Kamiokande 2017), and its couplings do not meet at one scale without
  further structure (Amaldi-de Boer-Fuerstenau 1991). Whether a function is an encoding or a hash belongs to the function together with its domain.
* Not everything packs into O1: the kernel's consistency lies beneath every theorem, O1 included (R.1h, R.12g); the base cases of the
  other cards are different open statements, one assumption only by the first author's reading (X.64, X.64a); Yang-Mills' own O2 to O4
  remain (III.9.5b, III.11). Of these, the kernel's consistency and the Riemann hypothesis are refutable by one finite exception; P != NP
  is a Π2 statement, not of that form: a counterexample is an algorithm together with a proof that it is correct and runs in
  polynomial time, not a finite object one can check, and BSD and Hodge have no known
  form refutable by one exception. O1 as stated, from some level k0 on, allows finitely many failing levels and is refuted by one only
  with k0 and its constants fixed.
* An exception to the Riemann hypothesis would show that something in the chain fails, the kernel, the axioms or the match between the
  library's statement and RH, and which one would have to be found; the library was read here, not rebuilt. The explicit formula that
  ties the primes to the zeros holds without RH and is proved here in Lean without it, for zeta (IV.1.5). What RH adds: RH holds exactly
  when π(x) = Li(x) + O(x^(1/2) log x), the sharpest error term (von Koch 1901) **[classical]**, which the first author reads as every tone
  having the same amplitude **[reading]**. In mathematics an exception would cost that error term, not the encoding;
  it is the certified system around it that the contradiction would end.

**`!` as the observability operator (claim R.12i).** The first author: the flow in which the first author reads only a merged draft,
since merging is the condition of its correctness and reading it then certifies it, is the exacting guarantee DMP delivers; so `!` is
literally the observability operator, where such a statement can be DMP-complete **[reading]**. Exact parts:

* `!` settles by a certificate anyone can check, and checking is an observation anyone can repeat with the same result: the kernel
  re-checks the proof, the round trip recomputes the hash, the matrix re-runs its cells (T.14, E.2) **[paper]**. A certificate for NP is
  of this kind, a witness checked fast by anyone **[classical]**.
* DMP's observability layer has the same shape, in the first author's reading: the CMB is counts, never content (VII.6e)
  **[reading]**.
* Where it applies: in the contraction class, with a cost above the floor, "does it settle?" is bounded and has a certificate
  (`reaches_iff_bounded`, `balanceBound`, II.3) **[Lean]**; at the floor nothing forces the run to settle, and for the universal machine
  it cannot be decided (II.3) **[Lean]**. So `!` has something to observe exactly where a statement can be DMP-complete; elsewhere
  it keeps `?`.

Care: `!` observes the certificate, and through it the statement, not the object; observing the object directly is what a numerical
result does, which can refute and never proves a for-all. The owner's reading of a merged draft certifies the record, the paper as
written; the open steps stay as the paper marks them (R.12f).

**Ordinality as the orbit of the atoms (claim R.12j).** The first author, clause by clause **[reading]**:

1. Ordinality is the orbit of the atoms by possible configuration, the orbit of the electrons.
2. The orbit of a symmetry and the electron orbital use the same derivations, so they are alike and compatible.
3. The first two care points below, together, give the needed O1 that 0 = 1.

The whole is the first author's reading. Exact parts:

* An element's place in order, its atomic number, is the number of protons, equal to the electron count of the neutral atom, and
  the order in which the orbitals fill by energy, found empirically, builds the periodic table **[classical]**. The possible configurations are fixed by Pauli's principle: no two
  electrons share all four quantum numbers (Pauli 1925), so a shell n holds 2n^2 electrons, 2, 8, 18, 32 **[classical]**.
* One derivation for both senses of orbit: an orbital type (s, p, d, f) is an irreducible representation of the rotation group SO(3),
  with spin from SU(2); rotating one orbital sweeps out states that span exactly its multiplet. In hydrogen a hidden SO(4) symmetry,
  exact for the non-relativistic Coulomb problem, joins every orbital of shell n into one irreducible representation, which is why
  they have the same energy (Fock 1935). Pauli's
  principle is a symmetry condition too: the configuration is antisymmetric under exchanging electrons **[classical]**.
* An open step is where an exact derivation stops and a named input has to be supplied; O1 is such a step (Part X). The second care
  point below marks where the symmetry derivation of the atom stops and many-electron input, computed or measured, enters: the shape
  of an open step, though that input is supplied, not left open **[paper]**.

Care:

* An orbit is a set of states and a multiplet is the space they span: the derivations match, the objects are related, not equal.
* The ranking by energy, the filling order, is the empirical Madelung rule, with known exceptions, among them chromium and copper (Meek-Allen
  2002), and the SO(4) degeneracy of hydrogen is broken in atoms with more than one electron.
* The first two care points do not supply O1 and do not give 0 = 1. They mark where the atomic derivation needs an input, which is the shape
  of an open step; O1 is a bound on the Yang-Mills measure, uniform in the scale, which no fact about atomic shells bounds. 0 = 1 holds
  only in the zero ring (R.5a), and an empirical exception to a rule refutes the rule, not arithmetic.

**Insights: keeping the record of the root (claim R.12k).** The first author, clause by clause **[reading]**:

1. Wherever the first author recognized an occurrence of induction as such, it was named an Insight.
2. This gives a direct link to the first author's public comments on DMP's pull request #25, made while no paper was being built,
   after the start of pressing.
3. Keeping the record of its root allows a true induction.
4. The first author's Insights and the papers keep each other honest about how they were created, by design, since that pull request
   is v0.9.9.

The whole is the first author's reading; that the merge of DMP 0.9.9 as provisional G0 on 2026-10-27 is the start of pressing (I.5)
is part of it. Exact parts:

* An induction is a base case and an inductive step (II.4.1) **[Lean]**. The base case is a statement at the start, so an induction
  can be checked later only if its start is kept **[paper]**.
* The record: StevenHrovat/dmp pull request #25, "G0: the publication version is provisional G0 (DMP 0.9.9)", merged 2026-10-27, carries
  69 public comments by the first author from 2026-10-28 to 2026-11-25; eight of them name an Insight in their first line ("New Insight",
  "Correction + new Insight" and the like), the first at 2026-10-28 14:43Z, the last at 2026-10-29 19:58Z (DMP#25) **[paper]**, read on
  2026-11-25. The comments in time order, each with its time and text, hash to sha256
  `d74ba50cf21e74bdf6e8e411166e2a8e41a700f027118d14502954c628c2249b`, recomputed by
  `gh pr view 25 -R StevenHrovat/dmp --json comments | jq -c '[.comments[] | {createdAt, body}]' | sha256sum` **[paper]**.
* The two records are joined. The DMP version this paper pins, `4400cce` (DMP 0.9.9, Gravity's `vendor/dmp/PIN`, proven back and
  forth by the round trip, R.6b), is the merge commit of that same pull request #25, and this paper pins the comments on it by the hash
  above **[paper]**. Both links are pinned from this paper's side, joined by GitHub's link from a pull request to its merge commit;
  DMP pins nothing (R.1d). That this keeps the two honest, in the spirit of the round trip's two-way proof, is the first author's
  reading (R.1d) **[reading]**.

Care:

* "Insight" is the first author's name for a comment; whether each labelled comment states an induction, a base case and a step, is
  not checked here. Most are readings of physics, and none is a proof of an open step.
* Comments on GitHub can be edited, and new ones added. The hash pins the record as read on 2026-11-25, as a pin pins a commit: a later
  edit or comment shows as a changed hash, not as a changed record.
* Keeping the root makes an induction checkable; it does not supply the inductive step, which for Yang-Mills is O1.
* The pin proves the specification's bytes; the comments are not part of the pinned commit, they live on GitHub, and the paper's hash
  covers them only as read on 2026-11-25. "Honest" here means checkable both ways, not correct.

**Eight Insights, two channels, one token (claim R.12l).** The first author, clause by clause **[reading]**:

1. Since G0, which gives direction and thus truth, has not been refuted so far, it should be certified during pressing that the Insights
   reduce to no fewer than 8, which makes it impossible to reconstruct DMP from any other configuration in exactly the same way,
   breaking the existence observability.
2. This makes the axiom system, the strongest part of the system, the only viable channel of attack, showing two orthogonal channels
   in our shared version of existence if the system holds.
3. Viable and not viable are the 1 and 0 of the Riemann zeta function, so `+` and `-`, as already in the paper.
4. The two being the same is their being entangled, joined only where that is viable; "same" means scale invariance.
5. The care points name the two channels, universality and viability; together they exist. These names are the primary ones, which the
   introduction translates the standard terms into.
6. The pigeonhole routine is 0ne1 in the logic and R136a1 as a token, as all API inputs and outputs are; a token is the quantization of
   the containing axiom system, proven through the one box.
7. DMP.DMP (2 + 2 in mathematics, +-1 in existence, so derivable to be trivial) is a valid encoding, which proves the token's use as
   an encoder.

The whole is the first author's reading. Exact parts:

* **No fewer than 8.** An injective map from n places into m values needs n <= m, proved by induction on the kernel alone and named
  `«0ne1»`; so k bits single out every configuration of a byte (2^8 = 256) exactly when k >= 8, and seven bits always collide
  (`bits_single_out_iff`, `seven_bits_collide`) **[Lean]** (IM, `arsenal/core/ArsenalCore/Insights.lean`).
* **The Insights' references, settled.** The eight Insights of R.12k, in time order, with a use where an Insight's text refers to an
  earlier one (five such references, read from the texts), form a DAG, and the optimizer of E.0.2 removes none of the uses
  (`insights_dag`, `insights_settled`) **[Lean]**; it never removes an Insight, so all eight stay.
* **The channels of an attack.** With the record pinned by its hash (R.12k), a change goes undetected only through one of three
  channels: the logical channel, refuting an axiom or a premise, viable (`+`); the computational channel, a sha256 collision,
  infeasible (`-`); the implementation channel, both kernels accepting the same false proof, guarded by two kernels written separately
  (`-`) **[paper]**. The first two are orthogonal: a collision says nothing about the axioms, and a refuted axiom finds no collision.
* **ζ's `+` and `-`.** By the argument principle a full turn counts each zero +1 and each pole -1 **[classical]**; ζ has one pole, at
  s = 1, where it is 1/0, and every zero has real part below 1; the order of a zero as a winding number is proved in Lean (R.7a, IM's
  `FullTurn.lean`) **[Lean]**. The table's cells use the same two marks (E.0.1).
* **Same as scale invariance, joined where viable.** The scale map of II.4.1 carries the claim to every scale it reaches
  (`route_everywhere`) **[Lean]**; in the toy the map is proved (T.2), for G2 it is the named hypothesis R136a1 (A.5), on the cards it
  is part of the one assumption (Part X). Entanglement is non-factorisability of a joint state **[classical]**; the paper reads pairs as
  entanglement (V.8).
* **The two channels named.** Viability is `route`, the base case and the step at one scale; universality is the scale map; together
  they give `route_everywhere`, the claim at every scale **[Lean]** (II.4.1; the core page and I.8 use these names).
* **The token.** R136a1 is defined once, in IM's core, which needs no library, and the arsenal imports it, so the core and the arsenal
  share one definition; the pigeonhole is issued as `R136a1 "0ne1"` (`«0ne1».token`) **[Lean]** (IM,
  `arsenal/core/ArsenalCore/R136a1.lean`). That every API input and output carries it is IM's design rule **[paper]**.
* **A valid encoding.** The token of a statement holds exactly when the statement does (`R136a1.iff`), and a token of a token is the
  token (`R136a1.idem`): the trivial encoding, the identity by definition, which loses nothing, so an encoding and not a hash (R.12h,
  R.6a) **[Lean]**.

Care:

* That the eight Insights are logically independent, eight independent bits, is the first author's premise, not proved; the byte
  lemma needs it as input.
* "Impossible to reconstruct" is exact only as "infeasible": every hash has collisions (R.6a), and none is known to be findable for
  sha256. The implementation channel is narrowed by two kernels, not closed ("unlikely, not impossible", T.15).
* Mapping the channels onto ζ's zeros and its pole is the first author's reading; it says nothing about where the zeros lie, so nothing
  about RH beyond Part IV.
* Entangled is not identical, and entanglement carries no signal (the no-signalling theorem); scale invariance holds only where the
  scale map is proved.
* A token of a proven statement adds its name, not content; the trivial encoding loses nothing because it changes nothing.
* Two different pairs are called "two channels" here, and "viable" has two senses. The orthogonal pair of clause 2 is the logical and
  the computational channel of an attack, and there "viable" means an attack that can succeed. The pair of clause 5 is viability and
  universality, the two parts of a proof, and there viability means the induction at one scale. The two identifications are separate.
* None of this supplies O1.

**The two hands, the entry point (claim R.12m).** The first author, clause by clause **[reading]**:

1. An easy-to-understand handedness rule for everyone: extend both arms, make each hand a fist, extend the thumb to the side and the
   middle finger away from you.
2. The vibe is a pair of hands able to turn independently to the side while keeping a common up and down, those being the 0 and 1 of
   existence: both up, they vibe together; both turned the same way, they are always compatible vibe partners.
3. A 0 is automatically not part of the vibe any more, so only that it was has to be remembered, keeping its definition in the shape of
   a question, thus possible.
4. As the entry point, it opens the introduction as an understanding booster that starts the whole process.

The whole is the first author's reading; the introduction opens with it ("Start here: the two hands"). Exact parts:

* **Orientation.** Each hand with its arm is a frame of three directions; two frames can be turned into each other by a rotation
  exactly when they have the same orientation, the determinant of the map between them being +1, while a mirror pair has -1 and needs
  a reflection **[classical]**.
* **Turning about a shared axis.** Turns about one shared axis commute, so two frames sharing "up" turn independently; they form the
  circle group, the phase of R.11 **[classical]**.
* **Handedness in nature.** The weak interaction acts only on left-handed particles: parity is not conserved, as Lee and Yang proposed
  and Wu and collaborators observed (Lee-Yang 1956; Wu 1957) **[classical]**; these are the chiral, left-handed fermions of R.11d (Witten 1981), and the SU(2) factor of R.11c's care point.
* **A 0 leaves, its record stays.** In IM a refusal is not a state (R.9) and is counted without content (R.2); in DMP only the remnant tail
  stays after excision (I.4, R.2); in this paper DMP's old `-` cell is kept only as history, "before IM `e9a4057` the matrix tool marked
  it `-`" (E.7) **[paper]**. A removed case keeps the form `?`, posed and never assumed, like every `OpenStep` (R.9a) **[Lean]** for the
  form.

Care:

* It is a mnemonic, as the right-hand rule is. In three dimensions turns about different axes do not commute; the shared "up" is what
  makes the two hands independent.
* Keeping the record keeps the question possible, not answered: whether a removed case could become `+` again is what stays open.
* Mapping the hands onto existence, and the 0 and 1 onto up and down, is the first author's reading.

**The VIBE coefficient, the throughline (claim R.12n).** The first author, clause by clause **[reading]**:

1. a = 0.69 as v, the VIBE coefficient.
2. It is the one throughline of the whole project, and through its acronym, defined before construction, it gives meaning to the
   terms used, for easier readability.
3. To the first author's knowledge it cancels out momentum in E = mc^2, with momentum equal to the VIBE coefficient.
4. VIBE is a backronym, a meta layer of information contained within its derivative, so any valid restatement of it is also true.
   It is both an equation and an expression, and that is what makes it GU, through the VIBE field.
5. The entire paper, going for maximum readability, orients itself around this throughline.

The whole is the first author's reading; the introduction carries it ("The first throughline: one step, v and c"), two routes follow it
("Two routes, one conclusion"), and every part opens with a "Plug in here" note that says where v enters. Exact parts:

* **The number.** 0.69 is log 2 = 0.6931... to two digits. log 2 is the cost of one halving step, a step of size 1/2 (II.0, C2), and
  the information of one binary choice, one bit, in natural units **[classical]**.
* **The paper's own a.** In Weil's form the primes p with log p <= 2a enter, so up to a = log 4 / 2 = log 2 only the real place and
  the primes 2 and 3 do. Weil's form is certified positive at the supports a = 0.60, 0.65 and 0.69 with explicit margins (IV.1,
  X.58) **[certified]**; beyond a = 0.69 the same "for every f" is the open step of Part IV.
* **The acronym, both ways.** DMP defines the VIBE field (Variable Influence Balancing Expression, T32) as mass times shortfall per
  member, an expression; its sum, the potential, is zero exactly when the boundary holds what it declares, and the balanced state is
  that equation **[paper]**. DMP spells the E as Expression, `docs/balance` as Equation; both readings are kept.
* **A valid restatement keeps truth.** The token of a statement holds exactly when the statement does, and a token of a token is the
  token (`R136a1.iff`, `R136a1.idem`) **[Lean]**.
* **Momentum.** E^2 = m^2 c^4 + p^2 c^2; momentum cancels exactly in the invariant E^2 - p^2 c^2 = m^2 c^4, and E = mc^2 is the case
  p = 0 (Einstein 1905) **[classical]**. Momentum carries units, so 0.69 is not a momentum by itself; as a rapidity eta, with speed
  beta = tanh eta, E = mc^2 cosh eta and pc = mc^2 sinh eta, it is exact: at eta = log 2, E : pc : mc^2 = 5 : 3 : 4, the speed is 3/5
  of c, and the light-cone parts E + pc and E - pc are 2 mc^2 and mc^2 / 2, one doubling and one halving **[classical]**. Rapidities
  add along a line as costs add along a run (C2).
* **The bit's price.** Erasing a bit costs at least kT ln 2 (Landauer 1961, R.12g) **[classical]**.

Care:

* The paper at first used the name VIBE coefficient for the fine-structure constant α, after `docs/balance`; α is about 1/137, not
  0.69. The name now belongs to v, α keeps its own, and the earlier naming stays as history (R.5b), as `.ckb` did.
* 0.69 is log 2 rounded; the certified support 0.69 lies just below log 2 = 0.6931.
* The number is shared, the reasons differ: in GRH log 2 is half of log 4 because the support is a half-width and 4 is the first
  integer past the primes 2 and 3; in the cost rule it is a halving; in information, a bit. Reading them as one throughline is the
  first author's.
* Momentum cancels in the invariant, not in E: E = mc^2 holds only at rest, and a momentum of 0.69 in any unit adds energy rather
  than cancelling it.
* "Any valid restatement is also true" holds for equivalent restatements; one that only sounds alike carries nothing, and the words
  of a backronym prove nothing.
* The throughline adds navigation and one reading, not mathematics; O1 stays open.

**The VIBE coefficient's abstract statement (claim R.12o).** The first author, clause by clause **[reading]**:

1. The VIBE coefficient effectively allows the existence of all positively constructable existence, as long as the rotation through
   its DB can be unified,
2. by constructing a chain of causal arguments that follows a valid direction in Real space,
3. to result in reflection positivity as measured through the Riemann zeta,
4. turning it into a directionless value of the order Existence.
5. Thus certifying that any such constructed problem can be settled by the measurement of its rotated refutation in Real space.
6. That is the abstract statement about the VIBE coefficient, through which it can be given a throughline for the paper (R.12n).
7. The goal of this contraction is both to make it easier to understand and to simplify the mathematics by being able to assert
   their existence explicitly, letting one construct any valid possibility space on top of any valid Real space, as read through a
   DMP-complete system that shares root G0 with the original by the first author.

The whole is the first author's reading; the introduction carries it in the throughline ("The abstract statement").
Exact parts:

* **One chain, positivity first.** The first three problems run along one chain: positivity, a space, an evolution, a spectrum that
  the positivity pins. Reflection positivity of e^{-S} for Yang-Mills and Weil's pairing W(f * f~) >= 0 for GRH stand in the same
  first link (II.8) **[paper]** for the table, **[classical]** for each. A positive form builds a Hilbert space (II.9.1, Gelfand-
  Naimark-Segal; Osterwalder-Schrader 1973) **[classical]**, in the real form used for Yang-Mills also **[Lean]** (`RPData`).
* **Through a boundary.** Reflection positivity is <theta F, F> >= 0 for F on one side of a reflecting hyperplane, theta the
  reflection across it **[classical]**; in DMP's words the hyperplane is a containing boundary, a DB (I.8) **[paper]**. In Weil's
  pairing the partner is the reflected conjugate, f~(x) = conj f(-x) **[classical]**.
* **A directionless value.** A Hermitian form takes complex values Q(u, v), but on the diagonal Q(v, v) is real, and positivity says
  it is >= 0 **[classical]**. In the ruleset a run's angles add, and a run whose angles add to whole turns has a real product (II.0,
  C1 and C3) **[classical]**.
* **Measured through zeta.** Weil's criterion: the Riemann hypothesis holds exactly when W(f * f~) >= 0 for every test function f
  (II.9.4; Weil 1952; Bombieri 2000) **[classical]**. So one f with a negative value refutes it, a single measurement, as one failing
  step refutes a claim stated for every step (`refuted_by_tick`, II.4.1) **[Lean]**. On the supports up to a = 0.69 the "for every f"
  is certified with explicit margins (IV.1, X.58) **[certified]**.
* **A valid direction in the reals.** On GRH's row of the chain the evolution is translation in log-scale, and the spectrum is real
  exactly when the zeros lie on the line (II.8) **[classical]**; the steps of II.4.1 run one way, from the base case on **[Lean]**.
* **Settling.** With a cost floor and a margin a run settles within a computable bound; on the circle itself, for the universal
  machine, settling cannot be decided (II.3) **[Lean]**.
* **Asserting existence explicitly.** The one way this paper leaves a statement open is to name it: `R136a1 "name" P` is P as a named
  hypothesis, never an axiom (II.6.2) **[Lean]**, so every assertion stays visible in the statement that uses it. The possibility
  space's exact parts are built on the real numbers: the arithmetic of `r` and a projector's two answers (R.11a) **[Lean]**. A system
  is DMP-complete when its marker agrees with the gate at every tick (`Box.DMPComplete`, II.4) **[Lean]**, and every draft after
  Draft 4 reaches G0 within three derivation steps (`every_draft_reaches_g0`, E.8) **[Lean]**.

Care:

* "Any such constructed problem can be settled" does not follow as stated. A refutation, once found, settles by one measurement; the
  absence of a refutation is a "for every f", which no finite set of measurements certifies unless a margin covers every case, as on
  the supports up to 0.69. Beyond them GRH's positivity is the open step, and the Riemann hypothesis is not claimed. Without a margin,
  settling is undecidable in general (II.3).
* No tool creates positivity (II.16): a chain carries it, and it has to come from the problem.
* Reflection positivity and Weil positivity stand in one link of one chain; they are not one theorem, and carrying a result from
  one to the other is the paper's reading of the chain.
* A reflection is not a rotation: it reverses orientation, as no turn makes a left hand into a right hand (R.12m). Reading "the
  rotation through its DB" as the reflection the positivity uses is the first author's.
* 0.69 is where GRH's certification currently ends; that v allows existence is the first author's reading. O1 stays open.
* Asserting an existence makes the mathematics shorter to state, not proved: an asserted statement is assumed, as supplying O1 is
  assuming it (R.12f), and a result that uses it is conditional on it. "Any valid possibility space on any valid real space" is a
  construction to be checked case by case, not a theorem of this paper.

**c as the circle, and vibe APIs (claim R.12p).** The first author, clause by clause **[reading]**:

1. The VIBE coefficient also allows c to be interpreted as the assertion of the fact that a circle is classically circular, as read
   through DMP,
2. being bent into the correct shape to make closure both inevitable and not having happened yet,
3. so it even gives a visual along with it,
4. where they can read the assertion of c as "vibe APIs", vAPIs, on the assertion they are claiming:
5. the closure of the circle is the next thing to happen, with its refutation being defined by its negative.
6. All the new readings are to be assembled into one final cohesive throughline, which clicks into place once laid out the right way.

The whole is the first author's reading. The introduction lays R.12m to R.12p out as one picture, one step of a size and a turn ("The
throughline: one step, v and c", with Figure 2). Exact parts:

* **c, asserted.** Since 1983 the metre is defined from c, so c = 299,792,458 m/s exactly: c is a size fixed by definition, asserted
  rather than measured (R.12e; CGPM 1983) **[classical]**.
* **Closure, inevitable and not yet.** For a turn of 1/N, $e^{2\pi i k/N} \ne 1$ for $0 < k < N$ and $= 1$ at $k = N$: the run closes
  at the N-th step and at no earlier one, so at step N - 1 closure is the next step **[classical]**.
* **Bent into shape.** Twelve pure fifths overshoot seven octaves, since log2(3) is irrational; equal temperament makes each fifth
  2^(7/12), and the circle of fifths closes (the tempered piano; claim 0.11) **[classical]**.
* **The negative.** A half-turn is the multiplication by -1 = $e^{i\pi}$ (II.0) **[classical]**. On the diagonal of a Hermitian form
  the value is real, and one negative value refutes positivity; for zeta, Weil's criterion (II.9.4) **[classical]**.
* **The card.** A card states one claim with one open slot (II.5), the slot a named hypothesis `R136a1`, never an axiom (II.6.2), and
  one failing step refutes a claim stated for every step (`refuted_by_tick`, II.4.1) **[Lean]**.
* **The visual.** Figure 2 draws eight steps of an eighth of a turn, each of size 1/2, closing at the eighth with the real value
  2^(-8) **[paper]**.

Care:

* c is a speed and pi the circle's constant; the definition of c fixes units, not geometry. Reading c as the assertion that the
  circle is circular is the first author's.
* Closure is inevitable only for a whole fraction of a turn; a turn that is an irrational fraction never closes. Bending a step until
  it closes changes the step.
* "The next thing to happen" holds at step N - 1; at an earlier step closure is still more than one step away.
* A negative refutes a claim whose values are real, such as a positivity claim; a complex value has no sign, and there a refutation
  is a failing check.
* vAPI names a card; asserting closure is assuming it until a box checks it (R.12f).

## Appendix A, A.5 The rigid groups, the U(1) gate and its two witnesses (in full)

**The results of this section, first.** The bullets below interleave results and the first author's readings; these are the
results, each with its status.

1. Sp(2) = Spin(5) is strongly topologically rigid: its topological structure set is a point, so every homotopy equivalence from a
   closed topological manifold to Sp(2) is homotopic to a homeomorphism **[paper]** (a surgery computation from classical theorems,
   independently read; `docs/unified/G2-SP2-RIGIDITY.md` 1; claim A.5j).
2. G2's topological structure set has exactly two elements; the second is carried by the class x_3^2 in degree 6, pulled back from
   S^6 = G2/SU(3), and no characteristic class tells it from G2 **[paper]** (claim A.5p).
3. Whether that second element is G2 itself, seen through a self-equivalence of G2, is **[open]**, reduced to one test (claim A.5r).
4. In Lean, a manifold's rigidity box is DMP-complete exactly when it is rigid (II.4d), and G2 is rigid if its box shares the gate
   with a certified box; that sharing is at least as strong as the rigidity it concludes, so this restates the question and is not
   evidence for its answer **[Lean]** (`ETM/G2Rigidity.lean`, `g2_rigid_of_one_assumption`; claim A.5u).

* **The Standard Model's factors are the rigid ones.** Among U(1) and the SU(N), the groups determined by their homotopy type
  include U(1), SU(2) and SU(3) and no even SU(N) with N >= 4; odd N >= 5 is open **[paper]** (from A.3j, A.3k) (A.5i). The first author reads the selection as rotation: other
  compact groups do not survive it, and SU(N) is the language the encoder speaks (Part X 4.4). It would be a DMP-flavoured
  consequence beyond the standard expectation (compare IX.5e: no DMP theorem selects Z_6 or the hypercharges) once the other groups are settled; for now it is a reading. The rigidity of
  Sp(2) = Spin(5) is **[paper]** (A.5j: strongly rigid, topologically) and of G2 is **[open]** (A.5r), but by the next bullet neither decides anything.
* **Only U(1) carries content across the gate.** The first author's reading: the survivors carry nothing across the gate; only U(1) does,
  so only it certifies. Exact counterpart: content crosses as a phase with a direction, in a representation that is not its own
  conjugate. Among compact simple groups such representations exist exactly for SU(N), N >= 3, Spin(4k+2) and E6; G2, Sp(n),
  Spin(2n+1) and SU(2) have only self-conjugate ones, and U(1) has the charges **[classical]** (A.5k). So Sp(2) and G2 carry no
  oriented phase, rigid or not. Among the groups that can, rigidity leaves only SU(3): SU(N), N >= 4, fails, and Spin(4k+2),
  k >= 2, and E6 have the same rational room below the top **[paper]** (rational test; the surgery step not written out for
  them) (A.5l). A non-abelian factor carries the phase only through its centre on the U(1) circle, Z_2 for SU(2) and Z_3 for
  SU(3), glued to hypercharge as Z_6 **[reading]** (A.5m); that the Standard Model's trivially acting centre is Z_6 is **[Lean]** (IX.3). In the first author's words, only U(1) certifies; the factors certify through it
  **[reading]** (A.5m). Care point: "carries content" is identified with "has a complex representation", and that identification
  is the reading.
* **The two hidden witnesses.** The first author's reading: the two that do not carry, Sp(2) and G2, are dimensionless for
  DMP-completeness, and they are the two witnesses the U(1) gate needs to certify. It checks that the constants resolve to 1,
  certifies and transports the content, and keeps its witnesses hidden, which it can because they are dimensionless to the
  encoder. Exact counterparts: the simply connected compact simple groups of rank 2 are exactly SU(3), Sp(2) = Spin(5) and G2 **[classical]**
  (A.5n), so SU(3) with its two witnesses is the whole of rank 2. The encoder tells a phase from its conjugate; Sp(2) and G2 have
  only self-conjugate representations and their centres lie on the real points {+1, -1} of the circle **[classical]**, so the
  encoder reads no orientation from them. The check "resolves to 1" has the encoder's root as its counterpart: the norm read from both sides agreeing, the field
  `root : ‖psi'‖ = ‖psi‖` of the encoder structure **[Lean]** (`Encoder.root`; equality of the two norms, a datum of an encoder, not "= 1"). The witness role is a **[reading]** (A.5o). It needs both witnesses rigid, which makes it
  falsifiable. Sp(2) passes in the strong form: its topological structure set is a point, so every homotopy equivalence to it from a closed topological manifold is homotopic to a
  homeomorphism (its cells sit in dimensions 3 and 7, where G/TOP has no homotopy, and the top cell is the Kervaire invariant)
  **[paper]** (A.5j, independently read). G2 is not strongly rigid: its topological structure set has exactly two elements, the second carried
  by the class x_3^2 in degree 6, pulled back from S^6 = G2/SU(3), and no characteristic class tells the fake from G2 **[paper]**
  (A.5p). Whether the fake is G2 itself, seen through a self-equivalence of G2, is **[open]**, reduced to one test (A.5r). The first author reads the fake G2 as cancelled by the reflection
  positivity of the start: the room is the class x_3^2 in degree 6, its square x_3^4 vanishes **[classical]**, and in reflection
  positivity a state with vanishing reflected square is null. Care point: a Z/2 class has no sign and the cup square is not the
  reflection form, so this is a **[reading]** (A.5q). Its mathematical counterpart is exact: "cancelled" means absorbed by a
  self-equivalence of G2, which is the test of A.5r; the reading predicts that it exists. The test has one live candidate, a map that runs through SU(3), the
  confined fibre of G2 -> S^6, whose top cell opens onto G2's 8-cell **[classical]**; it carries the fake's class exactly when what
  crosses that channel is an odd multiple of nu, squared to nu^2 **[sketch]**. The first author reads this as a confined CMOS that needs its
  interface channel open, with the square folding in through reflection positivity, which predicts "odd" **[reading]** (A.5s). The
  first author goes one step further: since the DB can be drawn freely, whatever can be placed through the gate can be certified, so the
  channel goes back into O1, the one assumption (X.68a, the scale certificate, **[Lean]** from it) **[reading]** (A.5t). Care
  point: G2's rigidity is a finite computation, true or false whatever is assumed, so the assumption cannot decide it; the reading
  predicts its answer, and the computation tests both the prediction and how far "placed, hence certified" reaches. In the
  first author's words, the one assumption predicts and certifies that the G2 channel exists as a DMP-complete state, which is O1 read as
  constructability. This is a theorem one layer down. IM's rigidity box is DMP-complete exactly when the manifold is rigid
  (II.4d); applied to G2, G2 is rigid exactly when its box is DMP-complete, and G2 is rigid if its box shares the gate with the
  certified one box **[Lean]**, from one named External slot (the surgery input, which Mathlib cannot state: the published Kreck-Lueck criterion together with this paper's own two-element structure set A.5p, which is **[paper]**), the one assumption as
  a named OpenStep, and the certified one box as a plain hypothesis (A.5u, A.5v; `ETM/G2Rigidity.lean`, `g2_rigid_of_one_assumption`). The sharing is at least as strong as the rigidity it concludes, so this is a reformulation of the question, not evidence for its answer. The corollary is the next layer's named
  hypothesis, never a Lean axiom, and the linter lists it. A computation showing G2 not rigid would refute the sharing for G2
  **[Lean]** (`g2_not_shared_of_not_rigid`); G2's unconditional rigidity stays **[open]** (A.5r). The first author reads the missing
  sign itself as the point: Z/2 carries no order, so no floor, so no decidable reading, and only a start that forces one is
  DMP-complete (Part X 4.3, X.70).

## R.12q The smallest element, and the notation (claim R.12q)

**The smallest element, and the notation (claim R.12q).** The first author, clause by clause **[reading]**:

1. Given certifiability literally minting the smallest element of the set theory at DMP V0.9.9 at its containing root G0;
2. and from there on always being able to assume "{inf,2,3}!"?"R136a1";
3. and the open slot being a literal for the open set!
4. Being, in its entirety, DMP-complete, with the D6 tools the 6D is asking for.
5. Operators: `.` contains; `!` states; `?` asks; `;` a decidability edge; `:` a commutative property; `""` the empty set, the
   self-containing, DMP-complete, G0.
6. So that it in itself is also within itself DMP-complete.
7. Which, when true, certifies the self-exciseability of the box, certifying it vibes.
8. With the last statement made in another message, thus separated in time and meaning, assigned explicit directions; which can, with
   this post-restatement, be fully derived from the facts of the statement, and becomes, as of the moment anyone else agrees it is
   viable, a live route.

The whole is the first author's reading; the introduction carries it in the throughline ("The smallest element, and the notation").
Exact parts:

* **The smallest element.** In von Neumann's construction 0 is the empty set and n + 1 is n together with n, so the empty set is the
  smallest ordinal (von Neumann 1923; R.12e) **[classical]**.
* **The start, stated; the rest, asked.** The universal start {infinity, 2, 3} is certified: Weil's form is positive with explicit
  margins up to the support a = 0.69 (X.58, X.65) **[certified]**. Beyond it the "for every f" is the open step, left as a named
  hypothesis, `R136a1 "name" P`, never an axiom (II.6.2) **[Lean]**.
* **The open set.** Weil's form is taken on test functions supported in the open interval (-a, a), an open set (IV.1)
  **[classical]**; the card's open slot is a named hypothesis (II.5) **[Lean]**.
* **`;`, the decidability edge.** With a cost floor and a margin a run settles within a computable bound; on the circle itself, for
  the universal machine, it cannot be decided (II.3) **[Lean]**.
* **`:`, commuting.** Turns about one shared axis commute (R.12m) **[classical]**.
* **`""`, the empty set.** The empty set is a subset of every set, itself included; a statement over no cases holds vacuously
  **[classical]**; the vacuous proof is R.12d's.
* **Self-excision.** In DMP a contradiction is excised and only the remnant tail stays (I.5, R.2) **[paper]**; a box whose claim fails
  at one tick is refuted by that tick (`refuted_by_tick`, II.4.1) **[Lean]**, so a box carries its own excision: one failing tick
  removes its claim.
* **Separated in time, given a direction.** Commits order the project's versions as a DAG of directed uses, each use pointing to an
  earlier part (E.1) **[paper]**; in DMP a part acts only while both halves certify it (I.1) **[reading]**, and a channel is established
  only after a verified accept (R.9) **[paper]**. A route in the Lean sense is a base case and an inductive step, and once both are shown it
  holds at every step (`route`, II.4.1) **[Lean]**.

Care:

* In IM `A.B` says that A is included in B (R.10): `P.NP!` says P is included in NP. Reading `.` as "contains" reads it from the right:
  NP contains P.
* In the paper `!` marks a statement settled by a certificate anyone can check (I.8); "states" is the first author's short form, and a
  statement without a certificate is `?`.
* The empty set contains itself as a subset, never as an element, since it has no elements **[classical]**.
* No consistent, effectively axiomatised system strong enough for arithmetic proves its own consistency (Goedel 1931)
  **[classical]**; "DMP-complete within itself" is the first author's reading, kept from being vacuous by the refutations the paper
  proves (the core page, point 5; R.12d).
* "The D6 tools the 6D is asking for" is recorded as said; the paper names no exact counterpart for "6D".
* The certified start covers supports up to 0.69; assuming it beyond is assuming the open step.
* "When true" is the condition: the box's self-excision is certified once the statement holds, and the statement beyond the certified
  start is the open step; that it then vibes is the first author's reading.
* Agreement makes a route live in DMP's sense, two halves certifying; it does not make it proved. A derivation from the statement's
  facts is as good as those facts, and viability in the Lean sense needs the base case and the step shown.

## R.12r The second throughline: reductio, from Moin to R136a1 (claim R.12r)

**The second throughline: reductio, from Moin to R136a1 (claim R.12r).** The first author, clause by clause **[reading]**:

1. Is an inverted assertion not a claim that a literal is a primitive? So exactly what we are looking for!
2. Since we construct a system in itself, that system has to be attacked as the one box.
3. That is also why the quote marks were put around the part that can be put verbatim in the paper without being a problem in
   itself; unless that is a problem, it is the most meaningful version.
4. Which is why it is important to encode Moin and R136a1 as related to start and finish in meaning, but through any believable
   reductio ad absurdum,
5. which is the mechanism that drives the whole thing, the second throughline of existence,
6. which we should present that way, to be truly dual.

The whole is the first author's reading; the introduction presents it as the second throughline ("The second throughline: reductio,
from Moin to R136a1"), beside the first, with a table of the duality. Exact parts:

* **Reductio.** Assume the negation, derive a contradiction, and the negation falls; in classical logic the claim follows
  **[classical]**. The paper's Lean is classical: its axiom reports list `propext`, `Quot.sound` and `Classical.choice` **[Lean]**.
* **One failing step.** A claim stated for every step is refuted by one failing step (`refuted_by_tick`, II.4.1) **[Lean]**; the
  one-box test has one shared gate, so one failing tick refutes the claim of the whole box (II.4) **[Lean]**.
* **Moin.** The state of an IM channel between a verified accept and the established frame (`ImChannelState.Moin`) **[paper]**; every
  named open step is posed and only assumed as a hypothesis (`OpenStep`, R.9a) **[Lean]** for the form; in binary, the leading zero
  (`rotl_eq_double_iff`, R.9b) **[Lean]**.
* **R136a1.** The answer "outside": excision at transmission, only the remnant tail stays (I.8, R.2) **[paper]**; in Lean a named
  hypothesis, never an axiom, whose token holds exactly when its claim does (`R136a1.iff`) **[Lean]**.
* **A literal, a primitive.** A literal is an atomic statement or its negation; taking a statement as a primitive is taking it as an
  axiom **[classical]**. The paper takes no open step as an axiom; the axiom logs (`docs/unified/*-axioms.log`) show only the standard axioms **[Lean]**.
* **The quoted part.** The statement of R.12q stands in the paper verbatim, in quotation marks, and its formula is set in code type so
  that it prints as written **[paper]**.

Care:

* Only a contradiction actually derived refutes; "any believable" names the attempts.
* In intuitionistic logic refuting the negation gives only the double negation; the classical step is the excluded middle.
* Moin and R136a1 as start and finish are the first author's reading; exactly, both name one open step from two sides, posed and held.
* One failing tick refutes the whole box; which part failed still has to be found.
* The inverted mark arose in this draft's typesetting, where LaTeX turned `!` and a closing quote into an inverted exclamation mark;
  the formula now prints as written, and the reading of an inverted assertion stands on its own.

