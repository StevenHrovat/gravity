/-
Toward the strong-coupling area law (area-law project, 2026-11-21). Released under Apache 2.0.

# The strong-coupling expansion

Each plaquette weight e^(βx) is cosh(βx) · (1 + tanh(βx)); the product over plaquettes expands into a sum over subsets O of plaquettes of
the products of tanh over O. With the selection rule of `CentreSymmetry.lean` (tanh is odd, cosh is even), only the subsets O that
together with the Wilson loop form closed surfaces mod 2 contribute.
-/

import AreaLaw.CentreSymmetry

open MeasureTheory Real

noncomputable section

/-- e^x = cosh x · (1 + tanh x). -/
theorem exp_eq_cosh_mul_one_add_tanh (x : ℝ) : exp x = cosh x * (1 + tanh x) := by
  have hc : cosh x ≠ 0 := (cosh_pos x).ne'
  rw [tanh_eq_sinh_div_cosh, mul_add, mul_one, mul_div_cancel₀ _ hc, cosh_add_sinh]

/-- **The strong-coupling expansion.** A product of exponentials over a finite set is the product of cosh times the sum, over all
    subsets, of the products of tanh. -/
theorem prod_exp_expand {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ) :
    ∏ i ∈ s, exp (x i) = (∏ i ∈ s, cosh (x i)) * ∑ O ∈ s.powerset, ∏ i ∈ O, tanh (x i) := by
  simp_rw [exp_eq_cosh_mul_one_add_tanh]
  rw [Finset.prod_mul_distrib, Finset.prod_one_add]

/-- tanh is odd, cosh is even: the parities the selection rule needs. -/
theorem tanh_odd (x : ℝ) : tanh (-x) = -tanh x := tanh_neg x
theorem cosh_even (x : ℝ) : cosh (-x) = cosh x := cosh_neg x

/-- tanh is monotone. -/
theorem tanh_monotone : Monotone tanh := by
  intro a b hab
  rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh, div_le_div_iff₀ (cosh_pos a) (cosh_pos b)]
  have h1 : sinh b * cosh a - cosh b * sinh a = sinh (b - a) := (sinh_sub b a).symm
  have h2 : 0 ≤ sinh (b - a) := sinh_nonneg_iff.mpr (by linarith)
  nlinarith

/-- Each tanh factor is bounded by tanh of the largest argument: |tanh(βx)| ≤ tanh(β·n) when |x| ≤ n, β ≥ 0. -/
theorem abs_tanh_le {β x n : ℝ} (hβ : 0 ≤ β) (hx : |x| ≤ n) : |tanh (β * x)| ≤ tanh (β * n) := by
  have hmono : Monotone tanh := tanh_monotone
  rw [abs_le]
  have h1 : β * x ≤ β * n := mul_le_mul_of_nonneg_left (le_of_abs_le hx) hβ
  have h2 : -(β * n) ≤ β * x := by
    have := neg_le_of_abs_le hx
    nlinarith
  constructor
  · rw [← tanh_neg]; exact hmono h2
  · exact hmono h1

end
