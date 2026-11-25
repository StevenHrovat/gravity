/-
GRH attempt, induction over scales: the finite models (2026-11-23). Released under Apache 2.0.

Note: `docs/rh-guide/grh/INDUCTION.md`.
-/

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Positivity at one grid, in finite form

Weil's form restricted to a grid of cells of width `ε` is a Toeplitz form whose entries are the moments of the
zero measure `∑_ρ w_ρ δ_{z_ρ}`, `z_ρ = e^{i ε t_ρ}`, `ρ = 1/2 + i t_ρ`: a zero on the critical line gives an atom on
the unit circle, a zero off the line an atom off it, and the functional equation's mirror `ρ ↦ 1 - conj ρ` is
`z ↦ (conj z)⁻¹`. This file proves the finite-atom version of "positivity of every Toeplitz section ⇔ atoms on the
circle".

**1. A lossy bound becomes exact when the spectrum is finite** (`norm_le_of_exp_bound`). If finitely many distinct
`α_i` with non-zero weights `c_i` satisfy `‖∑ c_i α_i^n‖ ≤ C ρ^n` for every `n`, then every `|α_i| ≤ ρ`: the constant
`C` disappears. (Vandermonde inversion. Over the integers the spectrum is infinite and Landau's theorem takes this
role; this is the "exact step" of Stepanov's method and of the one-sided Landau argument.)

**2. Positive Toeplitz forms have bounded moments** (`toep_moment_bound`): `‖t m‖ ≤ t 0`.

**3. Positive atoms on the circle give positive Toeplitz forms** (`atomic_toep_nonneg`).

**4. The finite criterion** (`atoms_inside_circle`, `atoms_on_circle`): if every Toeplitz section is positive and the
moments come from finitely many distinct atoms with non-zero weights, every atom lies in the closed unit disk; with
the mirror symmetry, on the circle.
-/

open Finset ComplexConjugate

open scoped Matrix

noncomputable section

namespace ProofPhase.GRH

/-! ### 1. Finite spectrum: a lossy exponential bound is exact -/

/-- **A lossy bound is exact for a finite spectrum.** Distinct `α_i`, non-zero `c_i`, and
`‖∑ c_i α_i^n‖ ≤ C ρ^n` for all `n` give `‖α_i‖ ≤ ρ` for every `i`. -/
theorem norm_le_of_exp_bound {k : ℕ} (α c : Fin k → ℂ) (hα : Function.Injective α) (hc : ∀ i, c i ≠ 0)
    {C ρ : ℝ} (hρ : 0 < ρ) (hb : ∀ n : ℕ, ‖∑ i, c i * α i ^ n‖ ≤ C * ρ ^ n) (i : Fin k) : ‖α i‖ ≤ ρ := by
  classical
  set A : Matrix (Fin k) (Fin k) ℂ := (Matrix.vandermonde α).transpose with hA
  have hdet : IsUnit A.det := by
    rw [hA, Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hα)
  have hmul : ∀ N : ℕ, A *ᵥ (fun i => c i * α i ^ N) = fun j : Fin k => ∑ i, c i * α i ^ (N + (j : ℕ)) := by
    intro N
    ext j
    simp only [hA, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_add]
    ring
  have hx : ∀ N : ℕ,
      (fun i => c i * α i ^ N) = A⁻¹ *ᵥ (fun j : Fin k => ∑ i, c i * α i ^ (N + (j : ℕ))) := by
    intro N
    rw [← hmul N, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet, Matrix.one_mulVec]
  set K : ℝ := ∑ j, ‖A⁻¹ i j‖ * (C * ρ ^ (j : ℕ)) with hK
  have hbound : ∀ N : ℕ, ‖c i‖ * ‖α i‖ ^ N ≤ K * ρ ^ N := by
    intro N
    have hxi := congrFun (hx N) i
    have he : ‖c i‖ * ‖α i‖ ^ N = ‖c i * α i ^ N‖ := by rw [norm_mul, norm_pow]
    rw [he, hxi]
    simp only [Matrix.mulVec, dotProduct]
    calc ‖∑ j, A⁻¹ i j * ∑ i', c i' * α i' ^ (N + (j : ℕ))‖
        ≤ ∑ j, ‖A⁻¹ i j * ∑ i', c i' * α i' ^ (N + (j : ℕ))‖ := norm_sum_le _ _
      _ = ∑ j, ‖A⁻¹ i j‖ * ‖∑ i', c i' * α i' ^ (N + (j : ℕ))‖ := by simp only [norm_mul]
      _ ≤ ∑ j, ‖A⁻¹ i j‖ * (C * ρ ^ (N + (j : ℕ))) := by
          gcongr with j
          exact hb _
      _ = K * ρ ^ N := by
          rw [hK, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [pow_add]
          ring
  by_contra hlt
  have hr : 1 < ‖α i‖ / ρ := by rw [one_lt_div hρ]; exact not_le.mp hlt
  have hci : 0 < ‖c i‖ := norm_pos_iff.mpr (hc i)
  obtain ⟨N, hN⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hr).eventually_gt_atTop (K / ‖c i‖)).exists
  rw [div_pow, div_lt_div_iff₀ hci (pow_pos hρ N)] at hN
  have h1 := hbound N
  nlinarith [h1, hN]

/-! ### 2-4. Toeplitz forms -/

/-- The Toeplitz form of the sequence `t : ℤ → ℂ` on the finite set of cells `s`:
`∑_{j, l ∈ s} conj (c j) c l t (l - j)`. Its positivity for all `s = range N` is positivity of every section. -/
def toepForm (t : ℤ → ℂ) (s : Finset ℕ) (c : ℕ → ℂ) : ℂ :=
  ∑ j ∈ s, ∑ l ∈ s, conj (c j) * c l * t ((l : ℤ) - j)

/-- **Positive Toeplitz forms have bounded moments**: `‖t m‖ ≤ re (t 0)`. -/
theorem toep_moment_bound (t : ℤ → ℂ) (ht : ∀ m, t (-m) = conj (t m))
    (hpos : ∀ s c, 0 ≤ (toepForm t s c).re) (m : ℕ) : ‖t m‖ ≤ (t 0).re := by
  have h0 : 0 ≤ (t 0).re := by
    have := hpos {0} (fun _ => 1)
    simpa [toepForm] using this
  have hreal : (t 0).im = 0 := by
    have := congrArg Complex.im (ht 0)
    simp only [neg_zero, Complex.conj_im] at this
    linarith
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : t 0 = ((t 0).re : ℂ) := Complex.ext (by simp) (by simp [hreal])
    rw [Nat.cast_zero, this, Complex.norm_real, Real.norm_of_nonneg h0, Complex.ofReal_re]
  · set r : ℝ := ‖t m‖ with hr
    have hne : (0 : ℕ) ≠ m := (Nat.pos_iff_ne_zero.mp hm).symm
    have hm0 : m ≠ 0 := hne.symm
    have hQ := hpos {0, m} (fun j => if j = 0 then (r : ℂ) else -conj (t m))
    have hmc : t m * conj (t m) = (r : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hr]
      push_cast
      ring
    have key : toepForm t {0, m} (fun j => if j = 0 then (r : ℂ) else -conj (t m)) =
        ((2 * r ^ 2 : ℝ) : ℂ) * t 0 - ((2 * r ^ 3 : ℝ) : ℂ) := by
      have h00 : conj (t 0) = t 0 := by rw [← ht 0, neg_zero]
      simp only [toepForm, Finset.sum_pair hne, hm0, ↓reduceIte, Nat.cast_zero, sub_zero,
        zero_sub, sub_self, ht, h00, Complex.conj_ofReal, map_neg, Complex.conj_conj]
      push_cast
      linear_combination (t 0 - 2 * (r : ℂ)) * hmc
    rw [key] at hQ
    simp only [Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re] at hQ
    rcases eq_or_lt_of_le (norm_nonneg (t m)) with hz | hpos'
    · have : r = 0 := by rw [hr, ← hz]
      rw [this]
      exact h0
    · by_contra hlt
      have hlt' := not_le.mp hlt
      have : 0 < r := hpos'
      nlinarith [mul_pos (pow_pos this 2) (sub_pos.mpr hlt')]

/-- **Positive atoms on the unit circle give positive Toeplitz forms**: the form is `∑_i w_i ‖∑_l c_l z_i^l‖²`. -/
theorem atomic_toep_nonneg {k : ℕ} (z : Fin k → ℂ) (w : Fin k → ℝ) (hz : ∀ i, ‖z i‖ = 1) (hw : ∀ i, 0 ≤ w i)
    (t : ℤ → ℂ) (ht : ∀ m : ℤ, t m = ∑ i, (w i : ℂ) * z i ^ m) (s : Finset ℕ) (c : ℕ → ℂ) :
    0 ≤ (toepForm t s c).re := by
  have hinv : ∀ i, (z i)⁻¹ = conj (z i) := by
    intro i
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz i]
    simp
  have hz0 : ∀ i, z i ≠ 0 := fun i h => by simpa [h] using hz i
  have hpow : ∀ i (j l : ℕ), z i ^ ((l : ℤ) - j) = conj (z i ^ j) * z i ^ l := by
    intro i j l
    rw [zpow_sub₀ (hz0 i), zpow_natCast, zpow_natCast, map_pow, ← hinv, inv_pow]
    ring
  have hform : toepForm t s c =
      ∑ i, (w i : ℂ) * (conj (∑ j ∈ s, c j * z i ^ j) * ∑ l ∈ s, c l * z i ^ l) := by
    have hi : ∀ i, (w i : ℂ) * (conj (∑ j ∈ s, c j * z i ^ j) * ∑ l ∈ s, c l * z i ^ l) =
        ∑ j ∈ s, ∑ l ∈ s, conj (c j) * c l * ((w i : ℂ) * (conj (z i ^ j) * z i ^ l)) := by
      intro i
      rw [map_sum, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul]
      ring
    simp_rw [hi]
    rw [Finset.sum_comm]
    unfold toepForm
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ht, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hpow]
  rw [hform, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Complex.conj_mul', Complex.re_ofReal_mul]
  have : ((‖∑ l ∈ s, c l * z i ^ l‖ : ℂ) ^ 2).re = ‖∑ l ∈ s, c l * z i ^ l‖ ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [this]
  exact mul_nonneg (hw i) (sq_nonneg _)

/-- **The finite criterion.** If every Toeplitz section is positive and the moments are those of finitely many
distinct atoms with non-zero weights, every atom lies in the closed unit disk. -/
theorem atoms_inside_circle {k : ℕ} (z w : Fin k → ℂ) (hz : Function.Injective z) (hw : ∀ i, w i ≠ 0)
    (t : ℤ → ℂ) (ht : ∀ m, t (-m) = conj (t m)) (hmom : ∀ n : ℕ, t n = ∑ i, w i * z i ^ n)
    (hpos : ∀ s c, 0 ≤ (toepForm t s c).re) (i : Fin k) : ‖z i‖ ≤ 1 := by
  refine norm_le_of_exp_bound z w hz hw (C := (t 0).re) one_pos (fun n => ?_) i
  rw [one_pow, mul_one, ← hmom]
  exact toep_moment_bound t ht hpos n

/-- **With the mirror symmetry, on the circle.** If moreover the atoms are non-zero and closed under the functional
equation's mirror `z ↦ (conj z)⁻¹`, every atom has `‖z‖ = 1`. -/
theorem atoms_on_circle {k : ℕ} (z w : Fin k → ℂ) (hz : Function.Injective z) (hw : ∀ i, w i ≠ 0)
    (hz0 : ∀ i, z i ≠ 0) (hmir : ∀ i, ∃ j, z j = (conj (z i))⁻¹)
    (t : ℤ → ℂ) (ht : ∀ m, t (-m) = conj (t m)) (hmom : ∀ n : ℕ, t n = ∑ i, w i * z i ^ n)
    (hpos : ∀ s c, 0 ≤ (toepForm t s c).re) (i : Fin k) : ‖z i‖ = 1 := by
  refine le_antisymm (atoms_inside_circle z w hz hw t ht hmom hpos i) ?_
  obtain ⟨j, hj⟩ := hmir i
  have h := atoms_inside_circle z w hz hw t ht hmom hpos j
  rw [hj, norm_inv, Complex.norm_conj] at h
  exact (inv_le_one₀ (norm_pos_iff.mpr (hz0 i))).mp h

end ProofPhase.GRH
