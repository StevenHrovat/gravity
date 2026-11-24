/-
GRH attempt, variational form: finite templates (2026-11-23). Released under Apache 2.0.

Note: `docs/rh-guide/grh/VARIATIONAL.md`.
-/

import ProofPhase.GRH.Induction
import Mathlib.Analysis.Convex.Basic

/-!
# Positivity as stability of a minimum, in finite form

**1. One line** (`line_min_iff`): `a t + q t^2 ≥ 0` for every real `t` exactly when `a = 0` and `q ≥ 0`.

**2. Stability of the minimum** (`min_at_zero_iff`): for `F x = b ⬝ x + x ⬝ (A x)` on `ℝ^n`, the point `0` is a global
minimiser exactly when the first variation vanishes (`b = 0`) and the second variation is a nonnegative form. With
`b = 0` and `A` the Weil form on a section, "the trivial state minimises" is Weil positivity on that section: the
template says nothing more and nothing less.

**3. The positivity set is convex** (`toep_pos_convex`): the moment sequences `t` whose Toeplitz forms are all
nonnegative form a convex set, since the forms are linear in `t`. The moments are linear in the prime weights
(explicit formula), so the prime configurations that keep a section positive form a convex set, and the margin
(the least eigenvalue) is a concave function of the configuration: an "optimal configuration" is a maximiser of
the margin, not a minimiser.
-/

open Finset ComplexConjugate

open scoped Matrix

noncomputable section

namespace ProofPhase.GRH

/-- `a t + q t^2 ≥ 0` for all real `t` iff `a = 0` and `q ≥ 0`. -/
theorem line_min_iff (a q : ℝ) : (∀ t : ℝ, 0 ≤ a * t + q * t ^ 2) ↔ a = 0 ∧ 0 ≤ q := by
  constructor
  · intro h
    have h1 := h 1
    have h2 := h (-1)
    have hq : 0 ≤ q := by nlinarith
    refine ⟨?_, hq⟩
    by_contra ha
    have hq1 : 0 < q + 1 := by linarith
    have ha2 : 0 < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 ha))
    have h3 := h (-a / (q + 1))
    have e : a * (-a / (q + 1)) + q * (-a / (q + 1)) ^ 2 = -(a ^ 2 / (q + 1) ^ 2) := by
      field_simp
      ring
    rw [e] at h3
    have : 0 < a ^ 2 / (q + 1) ^ 2 := by positivity
    linarith
  · rintro ⟨rfl, hq⟩ t
    nlinarith [sq_nonneg t]

/-- Positivity is stability of the minimum: `0` minimises `F x = b ⬝ x + x ⬝ (A x)` iff `b = 0` (first variation)
and `A` is a nonnegative form (second variation). -/
theorem min_at_zero_iff {n : ℕ} (b : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ x : Fin n → ℝ, 0 ≤ b ⬝ᵥ x + x ⬝ᵥ (A *ᵥ x)) ↔ b = 0 ∧ ∀ x, 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
  constructor
  · intro h
    have key : ∀ x, b ⬝ᵥ x = 0 ∧ 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
      intro x
      refine (line_min_iff _ _).1 (fun t => ?_)
      have e1 : b ⬝ᵥ (t • x) = t * (b ⬝ᵥ x) := by
        rw [dotProduct_smul, smul_eq_mul]
      have e2 : (t • x) ⬝ᵥ (A *ᵥ (t • x)) = t ^ 2 * (x ⬝ᵥ (A *ᵥ x)) := by
        rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
        ring
      have := h (t • x)
      rw [e1, e2] at this
      linarith
    refine ⟨?_, fun x => (key x).2⟩
    funext i
    have := (key (Pi.single i 1)).1
    simpa [dotProduct_single] using this
  · rintro ⟨rfl, hA⟩ x
    simpa using hA x

/-- The Toeplitz form is linear in the moments. -/
theorem toepForm_combo (t u : ℤ → ℂ) (a b : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) :
    toepForm (a • t + b • u) s c = (a : ℂ) * toepForm t s c + (b : ℂ) * toepForm u s c := by
  simp only [toepForm, Pi.add_apply, Pi.smul_apply, Complex.real_smul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

/-- The moment sequences with all Toeplitz forms nonnegative form a convex set. -/
theorem toep_pos_convex : Convex ℝ {t : ℤ → ℂ | ∀ s c, 0 ≤ (toepForm t s c).re} := by
  intro t ht u hu a b ha hb _ s c
  show 0 ≤ (toepForm (a • t + b • u) s c).re
  rw [toepForm_combo, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  exact add_nonneg (mul_nonneg ha (ht s c)) (mul_nonneg hb (hu s c))

end ProofPhase.GRH
