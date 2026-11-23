/-
Proof phase, crossover workstream (c9a-crossover): reversed P4, containment instead of construction (2026-11-23).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/CONTAINMENT.md`.
-/

import ProofPhase.Flip.Floor
import ProofPhase.Crossover.Neighbours

/-!
# Outside: twists are rare when electric flux is cheap. The container ends in long boxes. Tubes need more than `0.881`.

* **`elecF_nonneg`**, **`twist_ratio_eq`**, **`twist_ratio_le_elecF`** (S): for `0 < Z_tw < Z`,
  `Z_tw/Z = (1 − e^{−F_e})/(1 + e^{−F_e}) ≤ F_e`. Outside, where electric flux is cheap (`F_e` small), the twist is rare.
* **`elecF_lower_of_gap`**, **`exists_elecF_ge`** (S): if the flux sector sits a factor `μ < 1` below the vacuum per unit
  length (`Z₁(T) ≤ C μ^T λ^T`, `Z₀(T) ≥ λ^T`), then `F_e(T) ≥ −T log μ − log C`, which exceeds any `θ` for `T` large. At a fixed
  cross-section the twist (rarity) branch fails in long enough boxes: the container ends.
* **`path_sum_summable_iff`** (S): a sum of path weights `Σ xⁿ` converges iff `x < 1`. With `x = μ e^{−F}` (`μ` the number of
  continuations per step), the path sum converges iff `F > log μ` (**`tube_threshold`**).
* **`path_entropy_beats_handover`** (S): `μ ≥ 3` ⟹ `μ (√2 − 1) ≥ 1`. Self-avoiding paths on `ℤ^d` have `μ ≥ d` (directed paths),
  so for `d ≥ 3` the hand-over's per-box `0.881` cannot make tubes dominate the path sum.
-/

open Real

noncomputable section

namespace ProofPhase.Crossover

open ProofPhase.Flip

/-- The electric free energy is nonnegative when `0 < Z_tw < Z` (S). -/
theorem elecF_nonneg {Z Ztw : ℝ} (hT : 0 < Ztw) (hlt : Ztw < Z) : 0 ≤ elecF Z Ztw := by
  unfold elecF
  have hx : 0 < (Z - Ztw) / (Z + Ztw) := div_pos (by linarith) (by linarith)
  have h1 : (Z - Ztw) / (Z + Ztw) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have := Real.log_nonpos hx.le h1
  linarith

/-- **The twist ratio in terms of the electric free energy** (S): `r = (1 − e^{−F_e})/(1 + e^{−F_e})`. -/
theorem twist_ratio_eq {Z Ztw : ℝ} (hT : 0 < Ztw) (hlt : Ztw < Z) :
    Ztw / Z = (1 - Real.exp (-elecF Z Ztw)) / (1 + Real.exp (-elecF Z Ztw)) := by
  have hZ : 0 < Z := hT.trans hlt
  have hx : 0 < (Z - Ztw) / (Z + Ztw) := div_pos (by linarith) (by linarith)
  unfold elecF
  rw [neg_neg, Real.exp_log hx]
  have h1 : Z + Ztw ≠ 0 := by linarith
  have h2 : Z ≠ 0 := hZ.ne'
  rw [div_eq_div_iff h2 (by
    rw [show 1 + (Z - Ztw) / (Z + Ztw) = 2 * Z / (Z + Ztw) by field_simp; ring]
    exact div_ne_zero (by positivity) h1)]
  field_simp
  ring

/-- **Outside, absence** (S): `Z_tw/Z ≤ F_e`. -/
theorem twist_ratio_le_elecF {Z Ztw : ℝ} (hT : 0 < Ztw) (hlt : Ztw < Z) : Ztw / Z ≤ elecF Z Ztw := by
  have hF := elecF_nonneg hT hlt
  rw [twist_ratio_eq hT hlt]
  set F := elecF Z Ztw
  have hy : 0 < Real.exp (-F) := Real.exp_pos _
  have hy1 : Real.exp (-F) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h1 : (1 - Real.exp (-F)) / (1 + Real.exp (-F)) ≤ 1 - Real.exp (-F) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h2 : 1 - Real.exp (-F) ≤ F := by
    have := Real.add_one_le_exp (-F)
    linarith
  linarith

/-- **The electric free energy grows in long boxes when the flux sector is gapped** (S). -/
theorem elecF_lower_of_gap {Z0 Z1 : ℕ → ℝ} {l C μ : ℝ} (hl : 0 < l) (hC : 0 < C) (hμ : 0 < μ)
    (h0 : ∀ T, l ^ T ≤ Z0 T) (h1pos : ∀ T, 0 < Z1 T) (h1 : ∀ T, Z1 T ≤ C * μ ^ T * l ^ T) (T : ℕ) :
    -(T : ℝ) * Real.log μ - Real.log C ≤ Real.log (Z0 T) - Real.log (Z1 T) := by
  have e0 : Real.log (l ^ T) ≤ Real.log (Z0 T) := Real.log_le_log (pow_pos hl T) (h0 T)
  have e1 : Real.log (Z1 T) ≤ Real.log (C * μ ^ T * l ^ T) := Real.log_le_log (h1pos T) (h1 T)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hC.ne' (by positivity), Real.log_pow,
    Real.log_pow] at e1
  rw [Real.log_pow] at e0
  linarith

/-- **The container ends** (S): for `μ < 1` the lower bound exceeds any `θ` from some length on. -/
theorem exists_elecF_ge {μ C : ℝ} (θ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    ∃ T0 : ℕ, ∀ T ≥ T0, θ ≤ -(T : ℝ) * Real.log μ - Real.log C := by
  have hlog : Real.log μ < 0 := Real.log_neg hμ0 hμ1
  obtain ⟨N, hN⟩ := exists_nat_gt ((θ + Real.log C) / (-Real.log μ))
  refine ⟨N, fun T hT => ?_⟩
  have hTN : (N : ℝ) ≤ T := by exact_mod_cast hT
  have h := lt_of_lt_of_le hN hTN
  rw [div_lt_iff₀ (by linarith)] at h
  linarith

/-- **Path sums converge iff the per-step weight is below one** (S). -/
theorem path_sum_summable_iff {x : ℝ} (hx : 0 ≤ x) : Summable (fun n : ℕ => x ^ n) ↔ x < 1 := by
  rw [summable_geometric_iff_norm_lt_one, Real.norm_of_nonneg hx]

/-- **Tube threshold** (S): `μ e^{−F} < 1 ↔ log μ < F`. -/
theorem tube_threshold {μ : ℝ} (hμ : 0 < μ) (F : ℝ) : μ * Real.exp (-F) < 1 ↔ Real.log μ < F := by
  rw [Real.log_lt_iff_lt_exp hμ, Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos F)]

/-- **Path entropy beats the hand-over** (S): with at least three continuations per step, `μ (√2 − 1) ≥ 1`. -/
theorem path_entropy_beats_handover {μ : ℝ} (hμ : 3 ≤ μ) : 1 ≤ μ * (√2 - 1) := by
  have h := four_thirds_le_sqrt_two
  have : 3 * (√2 - 1) ≤ μ * (√2 - 1) := mul_le_mul_of_nonneg_right hμ (by linarith)
  linarith

end ProofPhase.Crossover
