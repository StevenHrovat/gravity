# The three sketch-level steps of M1, written out or stopped (m1-tools, 2026-11-22)

Brief (coordinator): write out line by line, pinned to the sources:
1. the swallowed-bond Jacobian (R4, with an explicit constant if possible);
2. R10, the conditional cluster expansion at fixed top field with its decay estimates;
3. the insertion of the footprint-weighted lifetime into [V] (1.80)-(1.85) (E8).

Report after each; stop at the first that fails or is much harder than marked. Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **Step 1 closes, with an explicit constant, after a small design change.** A coarse bond whose whole face lies
   inside an excised hole ("swallowed") gets an **independent Haar-random value** instead of a value read from the
   hole's filling. Then its fibre density is exactly 1, with no Jacobian, no compactness and no non-explicit constant.
   * **Law preservation still holds:** exactness (`Exact.lean`) holds for any measurable map, and the blocking is now
     a measurable map on (configuration × independent noise) with product measure.
   * **The coarse field there is irregular noise:** a localised large field at scale `k + 1`. Its fine content (a few
     random coarse bonds) is twist-free immediately (loops avoiding a few bonds are contractible in their complement
     in 4D), so the next excision fills it smoothly and R1 dilutes it.
   * **Costs:** the blocking is no longer a deterministic function of the bare field, only of the bare field plus
     independent noise. The interface (R11, `formal/ProofPhase/Interface/`) must allow blockings with auxiliary
     randomness: the "blocked law" is the image of `ym ⊗ Haar^{noise}`. This affects only configurations with a
     swallowed face (a deep localised structure of size `≳ L` at regular `W`), which are rare large-field events.
   
   **Deterministic alternative:** surjectivity plus compactness (`FILL.md` 0.4), non-explicit constant; not written
   out.
2. **Step 2 is much harder than marked, so I stop here.** `ObsTransferPhysTW` quantifies over all bounded *measurable*
   gauge-invariant observables, with constants independent of the observable. Balaban's machinery works through
   analyticity: every term of the effective action is analytic in the fields on complex neighbourhoods, and his bounds
   are Cauchy estimates. So an observable cannot be inserted as an analytic local term `e^{tF}`. The route that stays
   within measurable observables is to write `E[F | V_K]` through the marginal density `w(a; V_K)` of the fine variables
   `a` on `supp F`, and to bound how `w` depends on `V_K` far away. That requires running M1's induction with
   `supp F` as a **permanent frozen region of arbitrary content**, with decay bounds for the terms connecting it to
   far regions, uniform in its content and in the number of steps (`K` grows like `g^{-2}`). This is the
   "frozen region carried for ever" problem that broke TRAP's maintenance (REVIEW-1 F3), here for a single region, so
   without the counting issue. It is a new piece of analysis, not a write-out of an existing one. It is also, in
   substance, P5.2 of `PROOF-BLUEPRINT.md` (open there), restricted to the `L_*` segment.
3. **Step 3 is not started** (stopped at step 2). It is independent of step 2 and expected to be a re-reading.

## 1. Step 1, written out

**Rule.**
* At each blocking step, after the twist-free envelopes `H` are excised and filled (`FILL.md`): a coarse bond `c` is
  **swallowed** if every fine bond crossing the face between its two blocks lies in `H`.
* A swallowed coarse bond gets the value `ξ_c`, an independent Haar-distributed element (one fresh variable per
  swallowed bond and step).
* Every other coarse bond is Balaban's average (0.4) of the filled field.

**Measurability and law preservation.**
* The set of swallowed bonds is a deterministic, measurable function of the configuration: the envelopes are
  (`FILL.md` 2).
* The block field is a measurable function of (configuration, `ξ`).
* Apply `map_resample_eq` with `α` = configurations × noise and `ν` = Wilson measure ⊗ Haar: the conditional step
  preserves the law of the conditioning variable, which now includes `ξ` on the swallowed bonds.
* The true blocked law is the image of `ym ⊗ Haar`.

**The fibre mass, explicit.** Slice as in `E7J.md` 2(d)-(e) (`map_prod_le_of_slices`, Lean). In the slice, the
swallowed coordinates are `ξ_c`, which are Haar distributed and independent of everything else, so their density with
respect to Haar on those coarse bonds is exactly 1. The non-swallowed coordinates keep the bound of `E7J.md`:
`(C_d L^{3(d-1)})` per coarse bond. Hence `m_Λ(W) ≤ (C_d L^{3(d-1)})^{#non-swallowed}`, uniformly in `W`.

**The next step.** A swallowed bond's value is generic (Haar), hence typically irregular: a localised large field at
scale `k + 1`, supported on the swallowed bonds (at most `C_d` per hole). Short loops avoiding a finite set of bonds
are contractible in the complement in 4D (codimension 3), and away from those bonds the coarse field is the average of
the regular filled field. So the twist-free envelope is the swallowed set plus one layer; the filling is smooth, and R1
then contracts it.

**Status:** paper, explicit; needs the interface to allow auxiliary randomness (R11).

## 2. Step 2: what blocks it

* **What `ObsTransferPhysTW` asks:** for every bounded measurable gauge-invariant `F, G` of physical extent `≤ R` at
  physical distance `≥ D`, conditional decoupling and block approximants, with `c, K` depending only on `R`
  (`V3/W1Route.lean`, lines 156-175).
* **Why the generating-function route fails:** `e^{tF}` is not analytic in the fields for measurable `F`, and Balaban's
  bounds ([I] (1.18), [III] (2.26)-(2.42), [V] (1.73)-(1.75)) are Cauchy estimates on analyticity domains. Approximating
  `F` by trigonometric polynomials (characters, entire functions) loses uniformity in `F`, and the degree enters the
  analyticity radius.
* **The measurable route:** `E[F | V_K] = ∫ F(a) w(a; V_K) da`, with `w` the conditional marginal density of the fine
  variables `a` on `A = supp F`. One needs `sup_a |log w(a; V) - log w(a; V')| ≤ C e^{-m D}` when `V = V'` within
  distance `D` of `A`, and the analogue for two regions (covariance). This is a statement about Balaban's induction run
  with `A`'s fine variables **fixed** (frozen) at every scale: a permanent large-field region of arbitrary content.
  * **What it needs:** bounds on the terms connecting `A` to far regions, `≤ e^{-κ d}`, uniform in `A`'s content and in
    the number of steps.
  * **What is not known:** Balaban's B-term bounds ([III] (2.42)) are for regions renormalised after the delay. For a
    region carried `K ~ g^{-2}/log L` steps, his per-step constants (`O(1) M^d R^{d+1}` per cube) may accumulate in the
    terms near `A`. Whether they cancel in the ratios `Z(a, V)/Z(a, V')` is not known.
* **Relation to the blueprint:** this is P5.2 (H1-fine / ObsTransferPhys, open in `PROOF-BLUEPRINT.md`) on the segment
  `→ L_*`. M1's earlier claim that it "delivers the `L_*` half" (`HANDOVER.md` 2) was at sketch level and is withdrawn
  to "open, shared with P5.2".

## 3. Effect on the verdict

R4 is now paper (explicit) with the randomised rule. R10 is open (much harder than marked; shared with P5.2). E8
insertion not started. M1's main theorem does not have a complete argument apart from [I] Theorem 2 and P4: **R10 is
a genuine open problem**, and the E8 insertion is unchecked.

**Update (`R10-SCOPE.md`):** step 3 closes as written in [V] (no insertion needed). Step 2 is scoped: paper sketch for analytic observables, and the uniform-over-measurable form is not needed, given reflection positivity of the bare measure and an interface change.
