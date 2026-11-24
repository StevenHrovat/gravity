# Two channels and a positivity template for cutting planes

Private working note, 2026-11-23. Two transfers to the cutting-planes (CP) edge of `EDGE.md`, both approved by the
owner.

* **(A) From Yang-Mills (max(F_tw, F_e) >= 0.881).** A two-channel cost measure for CP lines.
  * The two categories are lines "directly from the base axioms" (cheap, machine checkable) and "new derivations"
    (lines that stand on their own, can fail, and so have value).
  * The note looks for a duality floor: every crossing line pays in at least one channel. Per the owner's "first true
    act", it also tests pairs of derived lines used together.
* **(B) From GRH ("it runs").** Sum-of-squares lower bounds build a pseudo-expectation that runs to level d. Is
  there a CP analogue?

Claim marks as in `PROOF-SYSTEMS.md`:
* **[Lean]** means `docs/mass-gap/formal/ProofPhase/Proof/`. Two modules are new here, both with standard axioms
  only and no `sorry`, on top of `Edge.lean`, `Dag.lean` and the earlier modules:
  * `CPDuality.lean`, 16 declarations (`axioms-cpduality.sh`, `axioms-cpduality.log`);
  * `CPPairs.lean`, 14 declarations (`axioms-cppairs.sh`, `axioms-cppairs.log`);
* **[classical]** marks published results as recalled;
* **[reading]** marks interpretation;
* **[open]** marks statements not known to be true.

---

## 0. The short answer

1. **A single-line duality floor exists for unit thresholds, exactly.** For the line "at least k of these e
   variables are true":
   * forcing it true needs k fixed variables: the restriction channel, what a restriction must hit to kill it;
   * forcing it false needs e - k + 1: the width channel, what a falsifying assignment must name;
   * the two sum to e + 1 (`thr_duality`, **[Lean]**), so every such line pays at least (e + 1)/2 in one channel. A
     clause (k = 1) pays in width; a majority pays in resistance to restriction. This is the CP form of
     max(F_tw, F_e) >= c.
2. **It fails for weighted lines.** The CP line r x1 + r x2 + (sum of r further variables) >= 2r:
   * is sensitive to all r + 2 of its variables;
   * is forced true by fixing 2 variables and forced false by fixing 2 (`two_cheap`, **[Lean]**).

   So **no measure on single lines** built from certificates gives the floor. Weights let a line be cheap in both
   channels while depending on everything.
3. **Pairs work, and they are what the known CP lower bounds use.** Feasible interpolation splits the formula as
   A(x, y) and B(x, z) and every line into an A-part and a B-part that share only the x-part. These are two derived
   lines that share existence (x) and not possibility: the two boundary laws are disjoint exactly when the formula is
   unsatisfiable (`split_unsat_iff`, **[Lean]**).
   * The cost is charged to the interface: a monotone real circuit (Pudlak 1997) or a dag-like communication protocol
     that decides, for each x, which side does not exist.
   * **Test passed:** clique-colouring (Pudlak); random k-CNF with k = Theta(log n) (Hrubes-Pudlak;
     Fleming-Pankratov-Pitassi-Robere; Sokolov). **[classical]**
   * **Test failed:** constant width. At width 3 the interface carries O(1) bits per clause and has no monotone
     structure. No lower bound is known for it.
4. **(B) The positivity template runs for CP up to rank, not size.**
   * The all-1/2 point satisfies every clause of width at least 2 and every sum of satisfied lines (`half_clause`,
     **[Lean]**).
   * Rounding breaks it: from x + y >= 1 and (1 - x) + y >= 1, rounding derives y >= 1, false at the point
     (`half_breaks_rounding`, **[Lean]**).
   * Fractional points that survive r rounds of rounding give CP **rank** lower bounds, known for random k-CNF
     (Buresh-Oppenheim et al.). Rank only bounds size linearly.
   * SOS-degree hardness does not transfer to CP size: Tseitin needs linear SOS degree (Grigoriev 2001) but has
     quasi-polynomial CP refutations (Dadush-Tiwari 2020). **[classical]**
5. **Both transfers stop at the same step:** **interface hardness at width 3**. This is a superpolynomial lower bound
   on dag-like protocols (the size-indexed "it runs" object for CP) for the falsified-clause search of a random
   3-CNF under some balanced split. **[open]**
6. **The entangled-pair test** (section 5, the owner's addition):
   * additive pairs cross for free: one sum of clauses names a whole region and is cheap in both channels (`fan_cheap`,
     **[Lean]**);
   * every CP refutation of a 3-CNF contains a creative pair, a rounding of a combination of at least two lines, while
     rounding a single axiom creates nothing (`creative_pair`, `round_single`, **[Lean]**).

   So the pairwise form gives a floor in kind and in depth (rank), not in size. The size floor needs the pair to be
   charged at its interface, which is the open step again.
7. **What this adds:** an exact two-channel floor for unit thresholds (Lean), a proof that weighted lines evade every
   single-line version (Lean), the identification of the owner's "pair" with the interpolation split (Lean for the
   logical core), and the convergence of (A) and (B) on one named step. **No new lower bound.**

---

## 1. (A) The two channels

The crossing line of `EDGE.md` (forced in every system by `cross_any_system`) is sensitive to e = Omega(n) boundary
variables. The two ways it can pay:

* **Channel W (width; "directly from the base axioms").** A line that is falsified only by naming many variables.
  Its unit is the size of a smallest **0-certificate**, a partial assignment forcing the line false. For a clause it is
  the width. This is the channel of the cut principle (`Cut.lean`) and of size-width (`Dag.lean`): such lines are
  killed by one fixed literal, so restrictions remove them.
* **Channel R (resistance; "new derivation").** A line that no small restriction makes true. Its unit is the size of
  a smallest **1-certificate**, a partial assignment forcing the line true. A line that is large here survives
  restrictions (`majority_line`, `EDGE.md`). It cannot be removed, only derived, and its cost has to show up in the
  derivation.

## 2. The duality floor for unit thresholds (**[Lean]**)

For B with |B| = e and 1 <= k <= e, the line thr B k ("at least k of B are true", the CP inequality
sum_{x in B} x >= k):
* `thr_true_card`, `thr_true_cert`: every 1-certificate fixes at least k variables, and k suffice;
* `thr_false_card`, `thr_false_cert`: every 0-certificate fixes at least e - k + 1, and that many suffice;
* `thr_duality`: (1-certificate) + (0-certificate) >= e + 1, with equality attained.

So **max(R, W) >= (e + 1)/2 for every unit-threshold line sensitive to e variables.** In particular, when the crossing
line of a CP refutation is a unit threshold, it pays at least half its boundary in one channel. The two extremes are
the owner's two categories:

| line | 1-certificate (channel R) | 0-certificate (channel W) | category |
|---|---|---|---|
| clause (k = 1) | 1 | e | directly from the axioms; pays in width |
| majority (k = e/2 + 1) | about e/2 | about e/2 | new derivation; pays in resistance |
| conjunction (k = e) | e | 1 | strongest new line; pays fully in resistance |

## 3. Weighted lines evade it (**[Lean]**)

`two_cheap`: for disjoint x1, x2 and a nonempty set R of r further variables, the CP line

> r x1 + r x2 + sum_{y in R} y >= 2r   (`wline`)

* is forced true by x1 = x2 = 1: a 1-certificate of size 2;
* is forced false by x1 = 0, y = 0 for any y in R: a 0-certificate of size 2;
* is sensitive to every one of its r + 2 variables. Flipping x1 at (x1 = 0, x2 = 1, all of R but one true) changes it,
  and flipping y at (x1 = 1, x2 = 0, all of R but y true) changes it.

As a Boolean function it is "x1 and x2, or one of them together with all of R". Its weights let it reach all e
variables while both certificates stay constant. **So the duality floor of section 2 is a property of unit weights,
and no certificate measure on single CP lines gives a floor.** Coefficients are not a separate currency either: the
known CP lower bounds charge each line one gate, whatever its coefficients (Pudlak 1997). **[Lean]** for the
example, **[classical]** for the remark.

**Consequence:** channel R cannot be measured on the line alone. Its cost has to be read off how the line is derived:
from which other lines, and through what interface.

## 4. Pairs: the "first true act" and the known lower bounds

**The owner's framing, read precisely.** "Once a second new derivation exists, there is the possibility of
non-existence on both sides of the creating pair, which share existence but not possibility." Feasible interpolation
is exactly this structure. **[reading]** for the match, **[classical]** for the mechanism.

* Split the variables as x (shared), y (side A only), z (side B only), and the clauses into A(x, y) and B(x, z).
* `split_unsat_iff` (**[Lean]**): the formula is unsatisfiable exactly when the two boundary laws "some y satisfies
  A" and "some z satisfies B" are disjoint. The pair shares existence (the x it is evaluated at) but not possibility
  (both laws never hold together). `interpolant_separates`: either law is a separator.
* Pudlak's interpolation (1997): every CP line splits into an A-part over (x, y) and a B-part over (x, z), derived
  side by side. For each x, the final line 0 >= 1 splits so that one side is impossible. The interpolant computes,
  line by line, which side carries the impossibility.
  * When x occurs only positively on one side, the computation is a **monotone real circuit** with one gate per line.
  * Every gate combines two derived quantities, so "counting pairs of derived lines that are combined" is counting
    gates, which is the proof size. **[classical]**

**The test on the known CP lower bounds.** All of them go through a pair channel. **[classical]**
* **Clique-colouring** (Pudlak 1997): the interface is "has a k-clique" against "is (k-1)-colourable". Monotone
  real circuits need exponential size (Pudlak; Haken-Cook), so the floor holds: exp(n^Omega(1)).
* **Random k-CNF, k = Theta(log n)** (Hrubes-Pudlak 2017; Fleming-Pankratov-Pitassi-Robere 2017; Sokolov 2024, tight
  2^Omega(n)):
  * the variables are split between two players, and each CP line becomes a step of a dag-like protocol for the
    falsified-clause search;
  * the hardness is a monotone-circuit or dag-protocol bound that holds because every clause carries Theta(log n)
    bits on each side.
* **Constant width: the test fails.** For a random 3-CNF under any balanced split:
  * about a quarter of the clauses lie wholly on one side (under a random split), and each split clause carries O(1)
    bits;
  * x occurs in both polarities on both sides, so there is no monotone interface. Interpolation then yields a
    general circuit, and superpolynomial general circuit lower bounds are out of reach (and where natural proofs
    apply);
  * dag-like protocol lower bounds for the search problem are known only from width c log n on (Riazanov,
    Sofronova, Sokolov and Yuan 2025 give even the randomized tree-like bound only there).

  **[classical]** for the thresholds of the known results, **[reading]** for the bit-count explanation.

### The first unclosable step of (A)

> **Interface hardness at width 3.** For a random 3-CNF F with Delta n clauses (Delta a large constant), with high
> probability, there is a balanced split of the variables such that every dag-like real (or triangle) protocol for
> the falsified-clause search of F has superpolynomial size.

* It would imply the `EDGE.md` target: dag-like real protocols simulate CP refutations (Krajicek 1998), so a protocol
  lower bound is a CP size lower bound. **[classical]** for the implication
* Status: **[open]**.

**What the pair adds over the single line:**
* the single-line channel R is defeated by weights (section 3);
* the pair channel is not, because a weight on an x-variable is paid on the interface: the gate must output the
  correct side for every x, whatever the weights inside the line.

So the two-channel duality survives exactly in its pair form. Its floor is the interface hardness, the step above.

## 5. The entangled-pair test (the owner's addition)

The owner added: "The pairs of derived lines is the entanglement through which the HTF acts in NP." In Yang-Mills the
HTF carried the per-box certificate and had to interact, that is be lossy, to carry anything. The test: must the cost
measure charge for **combinations** of two derived lines rather than for single lines? Does every combination across a
crossing pay in the second channel? Does the pairwise form give a floor where the single-line form does not?

**1. Building wide lines is always pairwise.** Addition is the only CP rule with two premises, and scaling and
rounding do not enlarge the support. So every line with more variables than the widest axiom is built by combining
lines pairwise. That part of the owner's picture holds automatically. **[classical]**, elementary

**2. Additive pairs cross for free** (`fan_sum`, `fan_iff`, `fan_cheap`, **[Lean]**, `CPPairs.lean`). The fan
r x1 + sum_{y in R} y >= r:
* is the sum of the r clauses x1 + y >= 1, built by additions alone;
* is equivalent to their conjunction, so **one line names the whole region**;
* is sensitive to all r + 1 of its variables;
* has a 1-certificate of size 1 and a 0-certificate of size 2.

It is also not a new derivation: it is a nonnegative sum of clauses, so the all-1/2 point satisfies it. **So a
combination across a crossing does not, in general, pay in either channel.** The answer to the second question is
no.

**3. Creative pairs are forced** (`creative_pair`, `refutation_needs_pair`, **[Lean]**). CP derivations are formalized
over integer lines (`CPD`: axioms, addition, positive scaling, division with rounding).
* Addition and scaling never leave the half-space of a fractional point that satisfies the axioms (`holds_add`,
  `holds_scale`).
* Rounding a positive multiple of a single axiom with a unit coefficient creates nothing: the result still holds at
  the point (`round_single`).
* Hence, whenever some fractional point satisfies every axiom, every derivation of a line that fails there contains a
  rounding step with three properties:
  * its premise holds at the point;
  * its result does not;
  * its premise is not a multiple of one axiom.
* For a CNF whose clauses have width at least 2, the all-1/2 point is such a point (`half_clause`). So **every CP
  refutation of a 3-CNF contains a creative pair**: a rounding of a line that combines at least two lines.
* Not formalized: the encoding of a clause as the line "sum of its literals >= 1". `half_clause` states the same thing
  in its own form, `lpVal`.

**4. The majority line.** "At least e/2 + 1 of these e variables" fails at the all-1/2 point. So by the same
theorem, deriving it from clauses of width at least 2 needs a creative pair, whatever the derivation. Whether it is
cheap depends on the formula. Cardinality lines are built in polynomial size by repeated sum-and-round in the
classical CP refutations of the pigeonhole principle (Cook-Coullard-Turan 1987). **[Lean]** (the need) +
**[classical]** (the cost)

**5. Does the pairwise form give a floor where the single-line form does not?**
* **Qualitatively, yes.** Every refutation contains a creative pair (Lean). Along a path the number of creative
  layers is the Chvatal rank, which is near-linear for random k-CNF (Buresh-Oppenheim et al.). So there is a floor in
  the creative channel, as a depth. **[Lean]** + **[classical]**
* **For size, no.** Counting creative pairs gives at least rank many lines, which is linear. Charging a pair by its
  certificates fails (the fan). **[Lean]**
* A superpolynomial floor needs a pair to be charged by its **interface across a split**: the gate or protocol step
  that decides which side of the shared variables carries the impossibility (section 4). At width 3 that price is the
  open interface hardness.

**Verdict.** The pair is the right unit, and it is where creation happens. The creation is lossy: rounding discards a
fractional part, and it is the only rule that does. Creation is forced at least once per refutation and once per rank
level. The per-pair price at constant width is the same open step as in sections 4 and 6.

## 6. (B) The positivity template

**SOS, what is known.** For random 3-XOR and 3-SAT, a pseudo-expectation positive up to degree Omega(n) exists
(Grigoriev 2001; Schoenebeck 2008): the system "runs" to linear level, so SOS needs degree Omega(n). **[classical]**

**The CP analogue, in Lean.**
* `half_clause`: the all-1/2 point satisfies every clause of width at least 2 as a linear inequality. It also
  satisfies every nonnegative combination of satisfied lines, since the additive rules are convex. So the LP relaxation
  of any 3-CNF "runs" at rank 0.
* `half_breaks_rounding`: the rounding rule is where it stops. From x + y >= 1 and (1 - x) + y >= 1 the sum gives
  2y >= 1, and division with rounding gives y >= 1. That is sound on 0/1 points but false at the point.

  Rounding is the one rule that creates a line outside the convex hull of what was there. No fixed fractional point,
  and no linear functional, can respect it in general.

**What is known for CP.** **[classical]**
* **Rank.** A fractional point that survives r rounds of rounding (it lies in the r-th Chvatal closure) is the CP
  version of "runs to level r". Random k-CNF needs near-linear CP rank (Buresh-Oppenheim, Galesi, Hoory, Magen and
  Pitassi 2003/2006). But a refutation of size s has rank at most s, so rank gives only a linear size bound. It is
  the depth channel, which the native method already showed to be separate from total work (`pairUp`,
  `Native/Method.lean`).
* **SOS does not transfer to CP size.** Tseitin formulas on expanders need linear SOS degree (Grigoriev 2001) and have
  quasi-polynomial CP refutations (Dadush-Tiwari 2020). A pseudo-expectation that runs to high degree therefore says
  nothing about CP size by itself.
* **The size-indexed dual object exists, and it is the protocol.** For CP size the known "it runs" witnesses are
  adversaries against dag-like protocols (the interface of section 4), not pseudo-distributions.

**What would be new (B).** A size-indexed pseudo-solution for CP: a family of fractional points, or a distribution
over them, that respects every line of every CP derivation of size at most s from F, rounding included, for a random
3-CNF F. It would play the role of Schoenebeck's pseudo-expectation for CP size. **[open]**

* **First unclosable step of (B).** Respecting rounding forces the object to be non-convex, a choice of point per
  derivation. A family of points indexed by derivations is exactly a strategy against a dag-like protocol.
* So (B) reduces to the interface hardness of section 4. **The two transfers stop at the same step.** **[reading]**,
  with the reduction direction standard (protocols simulate CP).

## 7. DMP reading (separate, marked)

Everything here is **[reading]** unless marked otherwise.

* **"Directly from the base axioms, cheap, machine checkable."** These are lines with a small region measure mu:
  forced by a few axioms, local. They pay in width (channel W), and restrictions remove them. Resolution lives
  entirely here, which is why size-width works for it (`Dag.lean`, **[Lean]**).
* **"New derivation: makes something in a way that it was not before, so it has a possibility to fail."** In CP this
  is the rounding rule. Addition and scaling only recombine what exists: every fractional point that satisfies the
  premises satisfies the result (convexity). Rounding produces a line that the fractional world rejects
  (`half_breaks_rounding`, **[Lean]**). It is the only CP rule that can "fail" against a relaxation, and the only one
  that creates a genuinely new line. A rank lower bound counts how many such creations are needed.
* **"Once a second new derivation exists ... non-existence on both sides of the creating pair, which share existence
  but not possibility."** This is the interpolation split.
  * The A-part and the B-part of each line are two derivations that share the x-part (existence).
  * The two boundary laws never hold together (not possibility; `split_unsat_iff`, **[Lean]**).
  * At the end, for each x, one side is the non-existence.
* **"The first true act, or the first genuinely new insight."** This is the interpolant: deciding, for each shared x,
  which side does not exist. Its circuit or protocol cost is what every known CP lower bound measures (section 4).
  The owner's ordering matches the mathematics. A single new line can be cheap in both channels (`two_cheap`,
  **[Lean]**). The cost appears once two derived sides are held against each other.
* **The YM parallel, max(F_tw, F_e) >= c.** For unit thresholds it holds exactly as max(R, W) >= (e + 1)/2
  (`thr_duality`, **[Lean]**). For general CP lines the floor moves from the single line to the pair, as in YM, where
  the floor is a property of the joint (twisted, untwisted) system and not of one sector.

* **"The pairs of derived lines is the entanglement through which the HTF acts in NP."** In CP the lossless steps
  (addition, scaling) keep the fractional world intact and carry nothing new: a point that satisfied the premises
  satisfies the result (`holds_add`, `holds_scale`, **[Lean]**). The one lossy step, rounding, discards a fractional
  part, and it is the only step that carries new content. It does so only when applied to a combination of at least
  two lines (`creative_pair`, `round_single`, **[Lean]**). That is the Yang-Mills lesson in proof form: the carrier
  must interact, and be lossy, to carry anything.
  * The entanglement is the pair combined before rounding.
  * The HTF acts at the rounding.
  * Across an interpolation split it acts on the interface, which is where the known lower bounds charge it
    (section 4).

**What the DMP reading adds here:** the right unit for the second channel is the pair, not the line. That is a
correct prediction, since the known lower bounds count pairs. **It does not bound the pair cost at width 3.**

## 8. Status

* **[Lean]** (`CPDuality.lean`, 16 declarations): `ForcesTrue`, `ForcesFalse`, `thr_true_card`, `thr_false_card`,
  `thr_true_cert`, `thr_false_cert`, `thr_duality`, `wline`, `filter_all_but`, `filter_all`, `two_cheap`, `lpVal`,
  `half_clause`, `half_breaks_rounding`, `split_unsat_iff`, `interpolant_separates`. Standard axioms only
  (`axioms-cpduality.log`).
* **[Lean]** (`CPPairs.lean`, 14 declarations): `fan`, `fan_sum`, `fan_iff`, `fan_cheap`, `HoldsAt`, `addL`, `scaleL`,
  `roundL`, `CPD`, `holds_add`, `holds_scale`, `round_single`, `creative_pair`, `refutation_needs_pair`. Standard
  axioms only (`axioms-cppairs.log`).
* **Not formalized:** the clause-to-line encoding (covered in form by `half_clause`); Pudlak's interpolation for CP (the line-splitting construction and its monotone real circuit);
  the simulation of CP by dag-like protocols; the CP rank bounds.
* **Open:** interface hardness at width 3 (sections 4 and 6), and with it the `EDGE.md` target.

## 9. References

* W. Cook, C. Coullard, G. Turan, On the complexity of cutting-plane proofs, Discrete Applied Math. 1987.
* P. Pudlak, Lower bounds for resolution and cutting plane proofs and monotone computations, JSL 1997.
* A. Haken, S. Cook, An exponential lower bound for the size of monotone real circuits, JCSS 1999.
* J. Krajicek, Interpolation by a game, Math. Logic Quarterly 1998.
* P. Hrubes, P. Pudlak, Random formulas, monotone circuits, and interpolation, FOCS 2017.
* N. Fleming, D. Pankratov, T. Pitassi, R. Robere, Random Theta(log n)-CNFs are hard for cutting planes, FOCS 2017.
* D. Sokolov, Random (log n)-CNF are hard for cutting planes (again), STOC 2024.
* A. Riazanov, A. Sofronova, D. Sokolov, W. Yuan, Searching for falsified clause in random (log n)-CNFs is hard for
  randomized communication, APPROX/RANDOM 2025.
* D. Grigoriev, Linear lower bound on degrees of Positivstellensatz calculus proofs for the parity, TCS 2001.
* G. Schoenebeck, Linear level Lasserre lower bounds for certain k-CSPs, FOCS 2008.
* J. Buresh-Oppenheim, N. Galesi, S. Hoory, A. Magen, T. Pitassi, Rank bounds and integrality gaps for cutting planes
  procedures, FOCS 2003; Theory of Computing 2006.
* D. Dadush, S. Tiwari, On the complexity of branching proofs, CCC 2020.
* `EDGE.md`, `DICHOTOMY-TRANSFER.md`, `NATIVE-METHOD.md` (this folder).
