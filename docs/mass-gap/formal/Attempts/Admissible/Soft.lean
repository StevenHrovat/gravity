/-
Attempt round 2026-11-21, route (c) "admissible". Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/admissible/NOTE.md`, sections 2 and 6.
-/

import OneScale.Gauge
import Positivity.General

/-!
# Soft admissibility: inside the one-scale framework, and what it does to Z₂

The soft admissible weight (PROOF-NOTE §9.1) multiplies the Wilson weight by `η₀` on every plaquette whose shortfall
`n − Re tr U_p` exceeds `ε`:

  `φ(x) = exp (β x) · (η₀ + (1 − η₀) · 1[n − x ≤ ε])`,   `0 < η₀ ≤ 1`.

* `posWeight_softAdmissible`: it satisfies hypothesis (Φ) (`OneScale.Gauge.PosWeight`), so the block specifications,
  Theorem A and Corollary B of the one-scale reduction apply to it verbatim (only `UniformGDS` stays open).
* `plaqWeight_softAdmissible`: it is a `Positivity.PlaqWeight`, so site reflection positivity holds for it
  (`Positivity.rp_plaquette_weight`).
* `z2_softAdmissible_eq_wilson` (the Z₂ check): for Z₂ (`Re tr U_p = ±1`, `n = 1`) and `0 ≤ ε < 2`, the soft admissible
  weight is *exactly* the Wilson weight at the shifted coupling `β' = β + ½ log (1/η₀)`, up to the constant `√η₀`.
  So soft admissibility moves Z₂ gauge theory towards weak coupling (the deconfined, perimeter-law phase); it cannot be
  the source of confinement.
-/

open Real

noncomputable section

namespace Attempts.Admissible

/-- The soft admissible plaquette weight `x ↦ exp (β x) · (η₀ + (1 − η₀) 1[n − x ≤ ε])` (`x = Re tr U_p`). -/
def softAdmissibleWeight (n : ℕ) (β ε η₀ : ℝ) (x : ℝ) : ℝ :=
  Real.exp (β * x) * (η₀ + (1 - η₀) * (if (n : ℝ) - x ≤ ε then 1 else 0))

theorem measurable_softAdmissible (n : ℕ) (β ε η₀ : ℝ) : Measurable (softAdmissibleWeight n β ε η₀) := by
  unfold softAdmissibleWeight
  exact (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
    (measurable_const.add (measurable_const.mul
      (Measurable.ite (measurableSet_le (measurable_const.sub measurable_id) measurable_const) measurable_const
        measurable_const)))

/-- The bracket `η₀ + (1 − η₀) 1[…]` lies in `[η₀, 1]` for `0 ≤ η₀ ≤ 1`. -/
theorem bracket_mem {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1) (c : Prop) [Decidable c] :
    η₀ ≤ η₀ + (1 - η₀) * (if c then 1 else 0) ∧ η₀ + (1 - η₀) * (if c then 1 else 0) ≤ 1 := by
  split_ifs <;> constructor <;> nlinarith

theorem exp_bounds (n : ℕ) (β x : ℝ) (hx : |x| ≤ n) :
    Real.exp (-(|β| * n)) ≤ Real.exp (β * x) ∧ Real.exp (β * x) ≤ Real.exp (|β| * n) := by
  have : |β * x| ≤ |β| * n := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  exact ⟨Real.exp_le_exp.2 (by linarith [neg_abs_le (β * x)]),
    Real.exp_le_exp.2 (by linarith [le_abs_self (β * x)])⟩

/-- **Soft admissibility satisfies hypothesis (Φ)** (`0 < η₀ ≤ 1`, any real `β`, `ε`): the bounds are
    `η₀ e^{−|β| n} ≤ φ ≤ e^{|β| n}` on `[−n, n]`. -/
theorem posWeight_softAdmissible (n : ℕ) (β ε : ℝ) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) :
    OneScale.Gauge.PosWeight n (softAdmissibleWeight n β ε η₀) where
  meas := measurable_softAdmissible n β ε η₀
  lower := ⟨η₀ * Real.exp (-(|β| * n)), mul_pos h0 (Real.exp_pos _), fun x hx => by
    obtain ⟨hlo, -⟩ := bracket_mem h0.le h1 ((n : ℝ) - x ≤ ε)
    obtain ⟨he, -⟩ := exp_bounds n β x hx
    unfold softAdmissibleWeight
    calc η₀ * Real.exp (-(|β| * n)) ≤ η₀ * Real.exp (β * x) := mul_le_mul_of_nonneg_left he h0.le
      _ = Real.exp (β * x) * η₀ := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (Real.exp_pos _).le⟩
  upper := ⟨Real.exp (|β| * n), fun x hx => by
    obtain ⟨-, hhi⟩ := bracket_mem h0.le h1 ((n : ℝ) - x ≤ ε)
    obtain ⟨-, he⟩ := exp_bounds n β x hx
    unfold softAdmissibleWeight
    calc _ ≤ Real.exp (β * x) * 1 := mul_le_mul_of_nonneg_left hhi (Real.exp_pos _).le
      _ ≤ _ := by rw [mul_one]; exact he⟩

/-- **Soft admissibility is a reflection-positivity weight** (`0 ≤ η₀ ≤ 1`). -/
theorem plaqWeight_softAdmissible (n : ℕ) (β ε : ℝ) {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1) :
    Positivity.PlaqWeight n (softAdmissibleWeight n β ε η₀) where
  meas := measurable_softAdmissible n β ε η₀
  nonneg := fun x _ => by
    obtain ⟨hlo, -⟩ := bracket_mem h0 h1 ((n : ℝ) - x ≤ ε)
    unfold softAdmissibleWeight
    exact mul_nonneg (Real.exp_pos _).le (h0.trans hlo)
  bdd := ⟨Real.exp (|β| * n), fun x hx => by
    obtain ⟨hlo, hhi⟩ := bracket_mem h0 h1 ((n : ℝ) - x ≤ ε)
    obtain ⟨-, he⟩ := exp_bounds n β x hx
    unfold softAdmissibleWeight
    rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (h0.trans hlo))]
    calc _ ≤ Real.exp (β * x) * 1 := mul_le_mul_of_nonneg_left hhi (Real.exp_pos _).le
      _ ≤ _ := by rw [mul_one]; exact he⟩

/-- **The Z₂ check.** For Z₂ the plaquette variable is `x = ±1` (`n = 1`, shortfall `0` or `2`). For `0 ≤ ε < 2` and
    `η₀ > 0` the soft admissible weight equals `√η₀ · exp (β' x)` with `β' = β + ½ log (1/η₀)`: soft-admissible Z₂ gauge
    theory *is* Wilson Z₂ gauge theory at the larger coupling `β'` (the constant `√η₀` cancels in every expectation). -/
theorem z2_softAdmissible_eq_wilson (β : ℝ) {ε η₀ : ℝ} (hε0 : 0 ≤ ε) (hε2 : ε < 2) (h0 : 0 < η₀) {x : ℝ}
    (hx : x = 1 ∨ x = -1) :
    softAdmissibleWeight 1 β ε η₀ x = Real.sqrt η₀ * Real.exp ((β + Real.log (1 / η₀) / 2) * x) := by
  have hs : Real.sqrt η₀ * Real.sqrt η₀ = η₀ := Real.mul_self_sqrt h0.le
  have hspos : 0 < Real.sqrt η₀ := Real.sqrt_pos.2 h0
  have hsq : Real.exp (Real.log η₀ / 2) = Real.sqrt η₀ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos h0]; ring_nf
  have hlog : Real.exp (Real.log (1 / η₀) / 2) = 1 / Real.sqrt η₀ := by
    rw [Real.log_div one_ne_zero h0.ne', Real.log_one, zero_sub, neg_div, Real.exp_neg, hsq, one_div]
  unfold softAdmissibleWeight
  rcases hx with rfl | rfl
  · simp only [Nat.cast_one, sub_self, hε0, ↓reduceIte, mul_one, add_sub_cancel]
    rw [Real.exp_add, hlog]
    field_simp
  · have hc : ¬ ((1 : ℝ) - -1 ≤ ε) := by norm_num; linarith
    simp only [Nat.cast_one, hc, ↓reduceIte, mul_zero, add_zero, mul_neg, mul_one]
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log (1 / η₀) / 2), hlog, one_div, inv_inv]
    linear_combination (-(Real.exp (-β))) * hs

end Attempts.Admissible
