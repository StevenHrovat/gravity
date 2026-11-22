# Cycle 4 review with fresh eyes (c4-fable, 2026-11-22)

Reviewer: the owner-approved Fable session, read-only outside this folder. Read: the blueprint (version 2 with the cycle
paragraphs), `ASSEMBLY.md`, `RULES.md`, the proof-phase parts of `PREP.md`, `READING.md` (sections 9, 10), all cycle notes
(c4a to c4d and c3a, c3b incl. its Result, c3d in full; the others by their result sections), `ROUND-3.md`, `ROUND-4.md`, the
round-4 review and `FREE-WINS.md`, the DMP scout and the DMP attempts (result sections), and the Lean statements named below
(read in the source, not built: no Lean build and no numerics were run in this session).

Verdict marks: **CONFIRMED** (I read the statement or number in the file and the conclusion follows from it),
**LIKELY** (a short argument from confirmed facts; not proved), **SPECULATIVE** (a lead). Literature named here is recalled
unless a project note already marks it as read; nothing below rests on a paper I could not check.

The companion file `BLUEPRINT-v4-DRAFT.md` is the constructive half. This file is the critical half.

---

## 0. The five findings that matter most

1. **The preferred top theorem cannot be fed by the real blocked theory as it is stated.** Three clauses of its W1 inputs are
   expected to be false for the true blocked laws: an exact finite range, a limit action made of plaquette terms only, and a
   bounded Gibbs potential for a deterministic blocking. The theorem is correct; its hypotheses are not the ones the notes
   describe in words. (Section 1.)
2. **At the working point the gap is not where the blueprint says it is.** The block scale L1 = 2.8/sqrt(sigma) is about ten
   glueball correlation lengths. A block variable that wide is close to noise for every local observable, so by the project's
   own information bound the conditional half (`CondMassAnn`, Lemma X) equals the fine gap up to a small error, and the
   Dobrushin condition at L1 is the cheap half. "The gap content stays in `LevelDprimeW`, `CondMassAnn` is gap-free" is true
   for the photon and misleading for Yang-Mills at this L1. (Section 2.)
3. **The difficulty is being moved, and there is exactly one place it can rest.** Every version leaves one statement of gap
   strength about a lattice theory at one fixed resolution (the scale L_* where segment 1 ends). Segment 2 is four inputs that
   are four faces of that one statement. The Lean already has the right cut (`BlockGapUnifW` with the transfer at L_*), and
   it is not used that way. (Section 2 and blueprint v4.)
4. **The certified measured point is certified for something the route does not consume.** It is a certificate for fitted,
   truncated actions seen on typical configurations; the Dobrushin condition is a worst-case statement about the true action
   with all loop families. The column moved 0.73, 0.96, 0.9999 as two loop families were added, and the method was tightened
   after the registered one gave 1.05. (Section 3.)
5. **The "two segments" exist in the notes, not in the Lean.** Nothing in `V3/` consumes `Seg1/` or `UV/Split.twoStage`;
   the top theorem takes inputs at L1 only. (Section 4.)

None of this is a counterexample to a Lean theorem. All of it concerns whether the hypotheses can be met and where the
content sits.

---

## 1. Statements that the real objects cannot satisfy

### 1.1 Exact finite range in the W1 inputs. CONFIRMED (statement), LIKELY (unsatisfiable)

Plain: the W1 form of the Dobrushin condition is stated with influence coefficients that are exactly zero beyond a fixed
distance D1, the same for every level and volume. That says the blocked measure is an exact finite-range Markov field. A
blocked Wilson measure has an effective action with tails at every distance.

Precise: `V3/W1Route.lean:56-62`, `LevelDprimeW`: `∃ γ D₁, ... γ * exp (lam * D₁) < 1 ∧ ∃ k₀, ∀ k ≥ k₀, ∀ j, ∃ V, ... ∃ kk,
SiteInfluenceW ... kk ∧ (column sums ≤ γ) ∧ (∀ i z, kk i z ≠ 0 → linkDist z i ≤ D₁)`. `SiteInfluenceW` (`Certified/AdjointW.lean:74`)
makes `kk i z` an upper bound for the W1 influence of `z` on the single-link law at `i`; `kk i z = 0` forces that law not to
depend on `z` at all. The same clause is in `H1LocalLipW` (`W1Route.lean:107-108`) for the deviations. `c4a/NOTE.md` section 4
lists this as "named limitation (1)" and `ASSEMBLY.md` as "new: the finite range D1"; neither says that with it the hypothesis is
out of reach of the object it is about.

Consequence: `yang_mills_assembly_v3_W1`, `_certified`, `_W1_condMass`, `_W1_smoother`, `_W1_dec` have a hypothesis the true
blocked laws are not expected to satisfy. The sup route (`LevelDprime`, exponential weights) does not have this defect, but
the sup window is not reached at the measured point. **The weighted W1 Theorem A (port of `Attempts.R3.theoremA_w`) is on the
critical path of the preferred route, not a nicety.**

### 1.2 A plaquette-only limit action with deviations going to zero. CONFIRMED against the project's own data

Plain: the W1 closeness hypothesis says the blocked actions converge to a limit action whose terms each live on one
plaquette. The refit measured a rectangle coupling different from zero at about 200 standard errors.

Precise: `H1LocalLipW T B Vk Vinf` takes `Vinf : ∀ j, LatticePlaquette 4 (coarseSide j) → GaugeConnection ... → ℝ` with support
`plaqSupp`, and asks `Σ_i δ k j i z ≤ ε k`, `ε → 0`. `LimitDprimeW` has range 1 (`AdjointW.lean:236-241`). c4d: `b_R = 0.0084`
(200 sigma), adding 0.23 to the column. So `H1LocalLipW` with any plaquette-supported `Vinf` fails for the true theory, and
`CertifiedMeasured ⇒ LimitDprimeW` (plaquette fits) cannot be joined to the true blocked law through it. Two repairs, both
needed: limit potentials of general (exponentially weighted) support, and "eventually `≤ ε₀`" instead of `ε → 0`
(openness needs only `ε₀ < (1 − γ)/2`; c3d already showed the limit itself is not needed).

### 1.3 The Gibbs representation for a deterministic blocking. CONFIRMED (open), LIKELY (false as stated)

Plain: every D′ input asks that the blocked law be a Gibbs measure of a bounded potential with respect to Haar measure. For
the deterministic good blocking (project a smeared sum to SU(2)) nobody knows that the image density is bounded above and
below; the projection has critical points.

Precise: `Potential.bdd` (`Attempts/R3/FlatFactors.lean:80-83`) inside `LevelDprimeW`, `LevelDprime`, `H1LocalLipW`;
`BlockingFamily` is a family of `RPBlocking`, deterministic maps (`Objects.lean:403`). c3d section 1.4 says so ("not known to
be bounded above and below; open"); it did not reach the blueprint's open-input list. A noisy local blocking removes it
(section 5, S2).

### 1.4 Worst case against typical case. CONFIRMED (logic)

Plain: a Dobrushin condition quantifies over every coarse configuration. A Schwinger-Dyson fit sees the action only where the
measure lives. The renormalisation-group literature (van Enter, Fernandez, Sokal; cited in c3d, c4a) locates its pathologies
exactly on atypical block configurations. So no measurement of the present kind can support the hypothesis the theorem
consumes, and Balaban-type bounds (c4b: sup-norm locality needs lower bounds on large-field weights, probability bounds are
cheap) point the same way.

Consequence: the route needs a Dobrushin theorem that tolerates a sparse set of bad sites (annealed, disagreement
percolation). c4a next step 2 and c4b's third click already say this; I rank it far higher than they do, because it is the
only form in which (i) published large-field bounds, (ii) measured actions and (iii) the theorem speak about the same thing.

---

## 2. Corners: is the difficulty only being moved?

### 2.1 Yes, and the notes already prove it. CONFIRMED

`UV/Split.lean`: `condDefect_eq` (`E Cov(F,G|Φ) = Cov(F,G) − Cov(E[F|Φ], E[G|Φ])`) and `abs_condDefect_sub_cov_sub_le`.
Given decay on the coarse side, part (c) holds iff the fine covariance decays. This is true for every blocking and every L1.
"Gap-free" in the notes means "the photon satisfies it"; it never means "easier than the gap for Yang-Mills".

### 2.2 At L1 = 2.8/sqrt(sigma) the conditional half is the gap. LIKELY

Plain: the hope behind `CondMassAnn` is the constraint mechanism: the block field pins the slow modes, so the conditioned
fine field is massive whatever the infrared does. That works when there are slow modes at the block scale (the photon; Yang-
Mills at weak-coupling scales). At L1 = 2.8/sqrt(sigma) there are none: with m(0++) about 3.75 sqrt(sigma) (the value c2a uses)
the correlation length is 0.27/sqrt(sigma), so a block is about ten correlation lengths wide, and at beta = 2.3 the
correlation length is below one lattice spacing. The block link is a smeared product over thousands of independent
correlation volumes.

Numbers (c3b Result): coarse fundamental plaquette 0.0137 (ts), 0.0432 (ss); adjoint 5.9e-5 (ts), 1.4e-3 (ss); fitted
couplings 0.054, 0.171. The block field is quantitatively near Haar noise. Then `abs_condDefect_sub_cov_le`
(`|(c) − Cov(F,G)| ≤ ‖E[F|Φ] − E F‖₁`) says part (c) is the fine covariance up to the (small) information of the block
field: conditional mixing at distances beyond the correlation length is the theory's own mass, not a constraint effect. In
filter language (c4c): weak observations, so stability can only come from ergodicity of the signal, which is the gap.

So at the working point: `LevelDprimeW` is the cheap half (a strong-coupling coarse theory, whose smallness is the area-law
and screening suppression of loops of size L1), and `CondMassAnn` + `ObsQuasiLocTW` in segment 2 carry the glueball gap.
The blueprint's cycle-4 sentence "segment 2 crossover: `LimitDprimeW` the gap content; `CondMassAnn` gap-free if the blocking
keeps content" has the roles reversed at this L1. c3a section 2.2 saw this for Leg C ("for such a variable Lemma X is the gap");
cycle 4 then treated the 3.7 sigma content pass as having avoided it.

### 2.3 The content rule measures detectability, not content. CONFIRMED (rule), LIKELY (reading)

The rule (c3b PREREG) is "resolved at 3 sigma". A signal of 5.9e-5 passes with enough measurements and fails with fewer; the
scaling partner at 2.92 failed at 2.6 sigma on the same quantity. What the proof needs is the size of `‖E[F|Φ] − E F‖` for
local glueball-type F, an explained-variance number. That has not been measured for SU(2) (c3a measured it for the Gaussian
photon: 0.02 to 0.06 even there).

### 2.4 The window between "content lost" and "Dobrushin fails" may be empty. LIKELY

Single-link criteria need coarse couplings below about 0.19 (c4d's certified isotropic window; linearised 0.196). Coarse
couplings fall like the area law in L1. Content falls with them. Below 1/T_c = 1.45/sqrt(sigma) D′ is false. The measured
point sits at column 0.73 to 0.9999 depending on the truncation, with content at the detection limit. A larger L1 buys margin
and loses content; a smaller one the reverse. This is difficulty conservation as a number.

### 2.5 The statement that cannot be avoided. CONFIRMED (structure)

After segment 1 the theory seen at L_* is a lattice theory at one fixed resolution, in a neighbourhood of a fixed action.
What remains is: **those lattice theories have exponential decay of block-observable correlations, uniformly in the volume
and over the neighbourhood.** In Lean this is `BlockGapUnifW T B λ` (or `BlockGapUnif`) with the tuning's unit set to L_*.
It is the lattice mass gap at one intermediate coupling in a form stable under small changes of the action. It is of gap
strength (the continuum gap implies it for block observables; with the ultraviolet transfer it implies the continuum gap).
`LevelDprimeW`, `H1LocalLipW` (segment-2 part), `CondMassAnn` (segment-2 part) and Lemma X are one proof strategy for it.

No route in the map avoids it: Route B lands on it (ws2), Conjecture S lands on it (c2b), the DMP-native line restates it as
a doubling law (blueprint v4, section 6). For scale: the rigorous or claimed-certified region of the Wilson theory is beta
below about 0.1 to 0.42 (`dobrushin/README.md`); scaling starts near 2.3; segment 1 with honest constants would end at a
much weaker coupling still.

### 2.6 Is the Dobrushin condition at L1 a viable endgame? LIKELY not in its present form

With a lossy block variable at L1 it needs Lemma X at order-one coupling as a second non-perturbative input, which is the
gap (2.2). With a lossless description (c3a's Route A′: super-sites holding the whole cell, a Dobrushin-Shlosman condition on
cells) the condition is the whole infrared statement and Lemma X disappears; that form is honest and is the one to state.
Whether it is true in worst-case form is open; in typical-case form it is as plausible as the gap.

---

## 3. Wrong turns and fragile assumptions

| # | item | where | verdict |
|---|---|---|---|
| W1 | exact finite range D1 in `LevelDprimeW`, `H1LocalLipW` | `V3/W1Route.lean:56-62, 95-108` | CONFIRMED; section 1.1 |
| W2 | plaquette-only `Vinf`, `ε → 0` | `V3/W1Route.lean:95-106`, `Certified/AdjointW.lean:236` | CONFIRMED; 1.2 |
| W3 | bounded Gibbs potential for a deterministic blocking | `FlatFactors.lean:80`, c3d 1.4 | CONFIRMED open, LIKELY false as stated |
| W4 | certified measured point: method changed after the registered method gave 1.052 for ext_TR; final 0.99988 is resolution dependent (1.00015 at 1/200 cells) | `c4d-certified/NOTE.md`, "Amendments after the first run" | CONFIRMED (disclosed there). Read ext_TR as not certified over the box |
| W5 | column trend 0.73 (plaquettes), 0.96 (+ rectangle), 0.9999 (+ spin 3/2); closure6 = −0.67; budget for the next loop family 0.0013 | c4d sections 0, 3 | CONFIRMED numbers; LIKELY: the all-loops single-link column at 2.80 is not below 1 |
| W6 | content rule = 3 sigma detectability | c3b PREREG, Result | CONFIRMED; 2.3 |
| W7 | "gap content in `LevelDprimeW`, `CondMassAnn` gap-free" at L1 = 2.8 | blueprint cycle-4 paragraph; c4a 2.4; c4c section 7 | LIKELY reversed; 2.2 |
| W8 | `PolymerRepW` as "a published-bound reading": no Balaban paper read in full text; both sources have exact-cover large-field gases; "constants independent of k" is transcribed, not verified; composite blocking `B_good ∘ B_Bal` needs Balaban's averaging to respect the reflection, unchecked | c4b sections 1.1, 1.2 | CONFIRMED as unverified. Segment 1 is "reduced to a named target form", not "to a reading" |
| W9 | Lemma UV "paper-sized, same kind as published work" | c4b section 4 | SPECULATIVE on size: Balaban's 4D series took a decade; the abelian Higgs cluster paper (Balaban, Imbrie, Jaffe) is in 2 to 3 dimensions |
| W10 | act number, photon control: "no barrier" assumption false; cold and hot U(1) chains disagree at L = 8, 10, unchanged by the old code and by tenfold thermalisation | `r4-actnumber/PREREG.md`, last section | CONFIRMED (data), LIKELY (frozen flux sectors: in the Coulomb phase the flux through a plane changes only by monopole events). Remedy in section 6 |
| W11 | `OnLCP.scheme` asks that `ℓ_k · fluxRate` converge for every choice of time limits; nothing in Route A uses it; the quantity is the one whose measurement just stalled; at L_* it would be exponentially small | `Assembly.lean:93-97`, `ASSEMBLY.md` table ("route B only") | CONFIRMED stronger than used |
| W12 | the top disjunction still carries Route B (`ConjW ∧ SectorTransfer`), though `SectorTransfer` is discharged only through Route A | `Torus/Top.lean`, ws2 | CONFIRMED dead weight in the statement |
| W13 | "segment 1 / segment 2" in the open-input table: no Lean theorem joins a segment-1 statement at L_* to an input of `V3/Top.lean` | imports of `V3/*.lean`; `ASSEMBLY.md` ("`EnvelopeW` is not an input") | CONFIRMED |
| W14 | c3a's spatial checkerboard blindness of the staple kernel (w = 0.5 exact, w = 1 near); w = 2 checked only at the zone corner | c3a section 3, c4a 1.3 | CONFIRMED open. Harmless for time-separated inputs, fatal for any Dobrushin form of `CondMass` until checked |
| W15 | `CondMass` (quenched, all bounded block functions) read literally can fail for a gauge reason and by the Rebeschini-van Handel mechanism | c4a 1.2, c4c 4.1 | CONFIRMED (stated there); keep only the annealed form as an input |
| W16 | `NonTrivial` separates the limit from noise, not from a free field; identification with Yang-Mills rests on being a limit of Wilson measures on the tuning | `Assembly.lean:109` | CONFIRMED; acceptable, say it |

No overclaim of the round-3/round-4 kind (a headline whose Lean content is definitional) was found in cycle 4. The cycle-4
notes mark D and S honestly. The slips are of a different kind: hypotheses shaped by what the Dobrushin theorem in the
library can consume, and a narrative ("gap-free", "content PASS", "certified") that runs ahead of them.

---

## 4. Lean structure

CONFIRMED by reading imports and statements:

* The chain actually used by `yang_mills_assembly_v3_W1` is: `levelDprimeW_of_h1LocalLip` → `blockGapUnifW_of_levelDprimeW`
  → `torusDecayLoc_of_blockGapUnifW` (with `obsTransferPhysTW_of_condDecouple`, `condDecouple_of_condMassAnn`) →
  `bothOrdersLoc_of_torusDecayLoc`. The interface in the middle, **`BlockGapUnifW ∧ ObsTransferPhysTW ⇒ TorusDecayLoc`**
  (`W1Route.lean:282`), is the cleanest theorem in the library and takes no Dobrushin condition at all.
* `Seg1/` (76 theorems, Kotecky-Preiss, `PolymerRepW ⇒ EnvelopeW`) feeds nothing downstream. `UV/Split.twoStage_blocked`
  feeds nothing downstream. `Seg2/Filter` enters only as an alternative name for part (c).
* Off the working route since cycle 3: the sup family (`LevelDprime`, `LimitDprime`, `H1Local`, `AdjointHalf`/`CentreHalf`
  in sup form, the two-type theorem, `EnvelopeW`, `NearStable`) because the sup window is not reached and the sup adjoint
  half is false for `|β_A| ≥ 0.0834`; Route B in the assembly; the old `fluxE`/`actZ`.
* Four generations of top theorems coexist (`yang_mills_assembly`, `_torus`, `_level`, `_v3` with six variants).

---

## 5. Simplifications

| # | simplification | effect | size |
|---|---|---|---|
| S1 | **Cut at L_*, not at L1.** Set the tuning's unit to the weak-coupling scale and take `BlockGapUnifW` as the one infrared input, `ObsTransferPhysTW` as the ultraviolet input | four segment-2 inputs become one; the transfer becomes purely ultraviolet (c3a 0.4 said so and did not use it); no new mathematics | small Lean module on existing lemmas |
| S2 | **Noisy local blocking family** (independent heat-kernel noise per coarse link) | gives the Gibbs representation (1.3); merges parts (a), (b) and the envelope into conditional mixing (c4a 2.2, 2.3 on paper); matches the OpenAI kernel | medium Lean refactor of `BlockingFamily` |
| S3 | **One Dobrushin theorem with rare defects** (annealed) | replaces sup, W1 and annealed forms by one; removes the exact-cover lower-bound problem of c4b; makes fitted actions relevant | large Lean module; a known kind of theorem |
| S4 | **Generators and rates only.** c2b: the gap is decided on loops of at most three plaquettes and as a rate (`norm_pow_le_of_generators`); free win 2: Theorem C on the torus removes prefactors | inputs need only a generating family of smooth (Lipschitz) observables, which is what W1 theorems give; for the volume-first order the level-uniform constant is not needed | small Lean; never wired into v3 |
| S5 | `H1LocalLipW ∧ LimitDprimeW` → `LevelDprimeW` only | c3d: the limit action is a vehicle; with 1.2 the pair is false anyway | deletion |
| S6 | `CondMassAnn` and part (c) | `CondMassAnn ⇒ (c)` is one line (`|∫ f| ≤ ∫ |f|`); they are one input. Keep the name `CondMassAnn`, drop `_dec`, `_smoother`, `_condMass` variants from the top | deletion |
| S7 | `OnLCP.scheme` → a two-sided bound, or define the tuning by the segment-1 coupling at L_* | removes a convergence statement nobody can prove and nothing uses | small |
| S8 | drop Route B from the top statement; archive the sup family | one top theorem | deletion |

Free wins established early and still unused: S4 (both halves); free win 5 (finite-volume transfer matrix, which is the
object of the DMP-native line); free win 8 (act numbers already on disk from the Luescher runs: about 3.6, 7.8, 12.2 at
L sqrt(sigma) = 2.1, 2.8, 3.5), which gives the act number at the working point without the stalled queue; the exact photon
formula `E_n = g² n² L_z/(2 L_x L_y)` (r4-conjw, proved), which can replace the simulated photon gate.

Cheap certified statements available: the Gaussian base case of the ultraviolet transfer (positivity of the conditional
precision per coarse momentum on the whole zone, then banded-inverse decay), finite-dimensional per momentum, interval
arithmetic; it is the photon instance of Lemma UV and decides the kernel question W14. Not cheap: any further certificate on
fitted actions (needs a refit with more loop families, and by 1.4 it certifies the wrong object).

---

## 6. The act-number control (the owner's pending decision)

Plain: the photon gate failed for a reason inside the control. The U(1) theory at beta = 1.1 has long-lived flux sectors;
cold starts sit in one, hot starts are spread over several.

Recommendation: replace the simulated gate by the exact formula (it is a theorem of the project, checked to 1e-14), keep the
simulated U(1) points at L = 4, 6 as a code check only, and start the SU(2) runs. This is a pre-registration change and needs
the owner's word. Priority is low for the proof (Route B is off the critical path), moderate for the DMP-native line, where
the act number at L1 is one of the two thresholds; for that purpose the Luescher data on disk already give it.

---

## 7. Alternatives: what to reopen

| route | verdict | why |
|---|---|---|
| Route B, sector transfer | stay closed as a route to the gap (CONFIRMED by ws2: charged-to-neutral needs dynamics; SU(2)×U(1) counterexample). **Reopen as the tool for the centre half:** the coarse fundamental couplings are controlled by the flux free energy of the L1 box, which is Route B's quantity | clicks with c4d (the centre half binds) |
| Conjecture S | closed (Heller endpoint; small loops). Keep its generator reduction (S4) | |
| OpenAI construction as the segment-1 supplier | **reopen, first choice** (LIKELY): statements are readable in Lean, the kernel is noisy and local (S2), constants are volume-free per their `Rep` budgets, their order of limits is the one `MassGapMFLoc` matches. Balaban stays the reference, unread | c4b pins the file lines |
| Balaban-Imbrie-Jaffe type conditional expansion | needed for the ultraviolet transfer in every version; do it after the infrared statement is fixed, not before | paper-sized or more |
| Langevin / log-Sobolev (Shen-Zhu-Zhu; multiscale Bakry-Emery along the Polchinski flow, Bauerschmidt-Bodineau-Dagallier, recalled) | SPECULATIVE, worth one reading: a one-sided (Hessian lower bound) condition on the torus measure only, no worst-case boundary conditions, with the group's positive curvature as a free term. It is a candidate *form* of the infrared statement, not a way around it | clicks with 1.4 |
| Chatterjee's programme | nothing to reopen; it supplies the unit test (decay for all boundary conditions implies confinement) | |
| decoding thresholds | keep as the unobserved-symmetry unit test; irrelevant once the infrared step is lossless | |
| DMP readings | see blueprint v4, section 6: a different and cleaner *shape* (finite volume, two act numbers, a doubling law), the same core | |

---

## 8. What I did not check

No Lean build (statements read in source only). No rerun of any certificate or fit. The Balaban papers and the filtering
papers were not opened; I rely on the notes' own reading marks. The glueball mass ratio and the deconfinement length are the
values the notes use. Section 2.2 is an argument, not a measurement; blueprint v4 proposes the measurement.
