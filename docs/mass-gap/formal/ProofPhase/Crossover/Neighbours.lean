/-
Proof phase, crossover workstream (c9a-crossover): the summed influence over the 2d neighbours, and the physical-units
rate (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/NEIGHBOURS.md`.
-/

import Mathlib

/-!
# The hand-over ratio beats the column sum for two channels only; Doeblin cannot supply a physical rate

* **`handover_column_sum_iff`** (S): `k (√2 − 1) < 1 ↔ k ≤ 2`. The hand-over's per-box ratio `√2 − 1` (`HandOver.lean`)
  summed over `k` channels stays below `1` exactly for `k ≤ 2`: a chain (two faces), not a box grid in `d ≥ 2` (`2d ≥ 4`
  faces).
* **`column_requirement`** (S): for `k ≥ 1`, `k e^{−F} < 1 ↔ log k < F`: a per-channel free energy `F` makes the column
  sum over `k` channels small iff `F > log k` (`log 8 ≈ 2.08` for `2d = 8` faces).
* **`neg_log_one_sub_le`** (S): `−log(1 − x) ≤ x/(1 − x)` for `0 ≤ x < 1`. With a Doeblin floor `x = e^{−K}`, the mass per box
  `−log η`, `η = 1 − e^{−K}`, is at most `e^{−K}/(1 − e^{−K})`.
* **`doeblin_mass_tendsto_zero`** (S): `e^{−K}/(1 − e^{−K}) → 0` as `K → ∞`. With `K = C β L^{d−1}` and `L = ℓ/a` boxes of a fixed
  physical size `ℓ`, the Doeblin rate per physical length goes to zero as `a → 0`.
* **`phys_rate_of_uniform`** (S): if `0 < η ≤ η₀ < 1` and `L a = ℓ > 0`, then `−log η₀ / ℓ ≤ −log η / (L a)`: a one-box
  contraction uniform in the lattice spacing at a fixed physical box size gives a rate per physical length.
-/

open Real Filter Topology

namespace ProofPhase.Crossover

theorem sqrt_two_lt_three_halves : √2 < 3 / 2 := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2]

theorem four_thirds_le_sqrt_two : 4 / 3 ≤ √2 := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2]

/-- **The hand-over ratio summed over `k` channels is below `1` iff `k ≤ 2`** (S). -/
theorem handover_column_sum_iff (k : ℕ) : (k : ℝ) * (√2 - 1) < 1 ↔ k ≤ 2 := by
  have h1 := sqrt_two_lt_three_halves
  have h2 := four_thirds_le_sqrt_two
  constructor
  · intro h
    by_contra hk
    have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (show 3 ≤ k by omega)
    have : (3 : ℝ) * (√2 - 1) ≤ k * (√2 - 1) := mul_le_mul_of_nonneg_right hk3 (by linarith)
    linarith
  · intro hk
    have hk2 : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    have : (k : ℝ) * (√2 - 1) ≤ 2 * (√2 - 1) := mul_le_mul_of_nonneg_right hk2 (by linarith)
    linarith

/-- **Column requirement** (S): `k e^{−F} < 1 ↔ log k < F`, for `k ≥ 1`. -/
theorem column_requirement {k : ℕ} (hk : 1 ≤ k) (F : ℝ) : (k : ℝ) * Real.exp (-F) < 1 ↔ Real.log k < F := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  rw [Real.log_lt_iff_lt_exp hkpos, Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos F)]

/-- `−log(1 − x) ≤ x/(1 − x)` for `x < 1` (S). -/
theorem neg_log_one_sub_le {x : ℝ} (h1 : x < 1) : -Real.log (1 - x) ≤ x / (1 - x) := by
  have hpos : 0 < 1 - x := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have e : 1 - (1 - x)⁻¹ = -(x / (1 - x)) := by field_simp; ring
  rw [e] at h
  linarith

/-- **The Doeblin mass per box goes to zero as the floor exponent grows** (S). -/
theorem doeblin_mass_tendsto_zero :
    Tendsto (fun K : ℝ => Real.exp (-K) / (1 - Real.exp (-K))) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero
  have h2 : Tendsto (fun K : ℝ => 1 - Real.exp (-K)) atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub h
  have := h.div h2 (by norm_num)
  rw [sub_zero, zero_div] at this
  exact this

/-- **A uniform one-box contraction at a fixed physical box size gives a rate per physical length** (S). -/
theorem phys_rate_of_uniform {η η₀ L a ℓ : ℝ} (hη : 0 < η) (hle : η ≤ η₀) (hℓ : 0 < ℓ) (hLa : L * a = ℓ) :
    -Real.log η₀ / ℓ ≤ -Real.log η / (L * a) := by
  rw [hLa]
  apply div_le_div_of_nonneg_right _ hℓ.le
  exact neg_le_neg (Real.log_le_log hη hle)

end ProofPhase.Crossover
