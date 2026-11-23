/-
Native proof optimization, applied once: the bottom of the Route B chain without its measurability ladder (2026-11-23).
Released under Apache 2.0.

Paper: `docs/pnp/NATIVE-METHOD.md`, section 4.
-/

import ProofPhase.RouteB.Chain

/-!
# `abs_ccorr_le` and `abs_nCorr_le`, re-proved without the measurability ladder

In `ProofPhase/RouteB/Chain.lean` the correlation bounds sit on four named regularity lemmas:
`abs_nCorr_le → abs_ccorr_le → measurable_cweight → measurable_cstep → measurable_sp, measurable_tm`.
They are the bottom of the longest chain under `yang_mills_assembly` (`NATIVE-OPTIMIZATION.md`, section 2).

This file proves the two bounds with **the same statements** (checked by the kernel, `axioms-method.sh`). The
measurability fact is discharged where it is needed, by `fun_prop` from the two measurability fields of the chain
weight, instead of by a ladder of named lemmas. These are the method's passes 1 and 4 (`NATIVE-METHOD.md`):
* inline the single-purpose lemmas;
* replace regularity bookkeeping by automation.

**New here:** the two re-proofs; `RouteB/Chain.lean` is not changed.
-/

open MeasureTheory Finset Filter Topology Positivity ProofPhase.RouteB

open scoped Classical

noncomputable section

namespace ProofPhase.RouteB

variable {G : Type*} [Group G] [MeasurableSpace G] {E S : Type*} [Fintype E] [Fintype S] {T : ℕ} [NeZero T]
variable (w : ChainWeight G E S)
variable [HasHaarProbability G] [MeasurableInv G] [(haarG G).IsInvInvariant]

-- The two instance arguments and `mf` are kept unused on purpose: the statement must match `abs_ccorr_le` exactly.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- **Same statement as `abs_ccorr_le`**, with the measurability of the chain weight discharged in place. -/
theorem abs_ccorr_le' {f : (E → G) → ℝ} (mf : Measurable f) {M : ℝ} (hM : ∀ a, |f a| ≤ M) (t : ℕ) :
    |ccorr (T := T) w f t| ≤ M ^ 2 * cZ (T := T) w := by
  have hV := w.measV
  have hK := w.measK
  have hw : Measurable (cweight (T := T) w) := by
    unfold cweight cstep sp tm
    fun_prop
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (fun _ => 1))
  unfold ccorr cZ
  rw [← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg (Eventually.of_forall fun U => abs_nonneg _)
    ((IsBdd.integrable (cweight_isBdd w) hw.aestronglyMeasurable).const_mul _)
    (Eventually.of_forall fun U => ?_))
  dsimp only
  rw [abs_mul, abs_mul, abs_of_nonneg (cweight_nonneg w U), sq]
  exact mul_le_mul_of_nonneg_right (mul_le_mul (hM _) (hM _) (abs_nonneg _) hM0) (cweight_nonneg w U)

/-- **Same statement as `abs_nCorr_le`.** -/
theorem abs_nCorr_le' {f : (E → G) → ℝ} (mf : Measurable f) {M : ℝ} (hM : ∀ a, |f a| ≤ M) (t : ℕ) :
    |nCorr (T := T) w f t| ≤ M ^ 2 := by
  unfold nCorr
  rcases (cZ_nonneg (T := T) w).eq_or_lt with h | h
  · rw [← h, div_zero, abs_zero]; exact sq_nonneg _
  · rw [abs_div, abs_of_pos h, div_le_iff₀ h]; exact abs_ccorr_le' w mf hM t

end ProofPhase.RouteB
