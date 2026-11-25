/-
GRH tie-in, part 2: the function-field instance (a curve over F_q) of the ledger's GRH column (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/GRH-TIE-IN.md`.
-/

import ProofPhase.GRH.TieIn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Curves over a finite field: a true theorem case of the GRH column, with a real tick

The data of a curve of genus `g` over `F_q` that the prime side sees are its point counts `N_m = #C(F_{q^m})`. By
rationality (classical, Schmidt-Weil) they are `N_m = q^m + 1 - ∑ α_i^m` for the Frobenius eigenvalues `α_i` (`2g` of them
with multiplicity). That is `CurveModel`: classical facts, carried as fields, not proved here.

**The ledger's model.** Normalise by the tick: `z_i = α_i / √q`. The moments of the grid form are `A n = ∑ mult_i z_i^n`
(power sums, from the prime side by `moment_pointcount`), and `t` is their Hermitian extension.

* **`WeilBound`** (named external hypothesis; **Weil's theorem**, 1948, the Hasse-Weil bound for curves; not in Mathlib,
  checked by search): `‖α_i‖ = √q` for every `i`. It is the Riemann hypothesis for the curve.
* **`CurveModel.toZeroModel`**: under `WeilBound`, the curve is a `ZeroModel` of `Unified/GRH.lean` (zeros
  `ρ = 1/2 + i γ`, `γ = arg z_i` real, tick `ε = 1` in the argument), with multiplicity weights.
* **`curve_scaleSign`**: `ScaleSign t`, by the easy direction `scaleSign_of_online` (part 1).
* **`curve_scaleSign_iff`**: in this model, `ScaleSign t ⟺ WeilBound`. The sign of the prime-side moments is exactly the
  Riemann hypothesis of the curve (`⟹` is `atoms_on_circle`, with the mirror closure built from the functional equation
  `α ↦ q/α` and the real coefficients `α ↦ conj α`). So Weil's theorem *is* the sign, and it is supplied from outside.
* **`curve_sections`**: the closure. With `n` distinct atoms (`n = 2g` when `P` has simple roots), every section of size
  `m ≤ n` is **definite** (no nonzero null vector: `|k| < 1` at every step before `n`), and the section of size `n + 1`
  has a nonzero null vector (`|k_n| = 1`: the existence space is spanned exactly, finite closure).

Standard axioms only.
-/

open Finset ComplexConjugate Complex

noncomputable section

namespace ProofPhase.Unified

open ProofPhase.GRH

/-! ### 1. Atoms on the circle: definite sections, then a null vector -/

/-- **The form of atoms**: on atoms of the circle with real weights, the Toeplitz form is `∑ w_i ‖p_c(z_i)‖²`. -/
theorem toepForm_atoms {k : ℕ} (z : Fin k → ℂ) (w : Fin k → ℝ) (hz : ∀ i, ‖z i‖ = 1) (t : ℤ → ℂ)
    (ht : ∀ m : ℤ, t m = ∑ i, (w i : ℂ) * z i ^ m) (s : Finset ℕ) (c : ℕ → ℂ) :
    toepForm t s c = ((∑ i, w i * ‖∑ l ∈ s, c l * z i ^ l‖ ^ 2 : ℝ) : ℂ) := by
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
  rw [hform]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.conj_mul']

/-- If the form of atoms with positive weights vanishes, the polynomial `∑ c_l X^l` vanishes at every atom. -/
theorem atoms_eval_zero {k : ℕ} (z : Fin k → ℂ) (w : Fin k → ℝ) (hz : ∀ i, ‖z i‖ = 1) (hw : ∀ i, 0 < w i)
    (t : ℤ → ℂ) (ht : ∀ m : ℤ, t m = ∑ i, (w i : ℂ) * z i ^ m) (s : Finset ℕ) (c : ℕ → ℂ)
    (h : (toepForm t s c).re = 0) (i : Fin k) : ∑ l ∈ s, c l * z i ^ l = 0 := by
  rw [toepForm_atoms z w hz t ht s c, Complex.ofReal_re] at h
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin k)), 0 ≤ w j * ‖∑ l ∈ s, c l * z j ^ l‖ ^ 2 :=
    fun j _ => mul_nonneg (hw j).le (sq_nonneg _)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h i (Finset.mem_univ i)
  rcases mul_eq_zero.1 hzero with h1 | h1
  · exact absurd h1 (hw i).ne'
  · exact norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h1)

/-- **Definite sections.** For `k` distinct atoms on the circle with positive weights, every section of size `m ≤ k`
has no nonzero null vector. -/
theorem section_definite {k : ℕ} (z : Fin k → ℂ) (w : Fin k → ℝ) (hz : ∀ i, ‖z i‖ = 1) (hw : ∀ i, 0 < w i)
    (hinj : Function.Injective z) (t : ℤ → ℂ) (ht : ∀ m : ℤ, t m = ∑ i, (w i : ℂ) * z i ^ m) {m : ℕ}
    (hm : m ≤ k) (c : ℕ → ℂ) (h : (toepForm t (range m) c).re = 0) : ∀ l < m, c l = 0 := by
  have hev := atoms_eval_zero z w hz hw t ht (range m) c h
  set p : Polynomial ℂ := ∑ l ∈ range m, Polynomial.C (c l) * Polynomial.X ^ l with hp
  have hpe : ∀ x : ℂ, p.eval x = ∑ l ∈ range m, c l * x ^ l := fun x => by
    simp [hp, Polynomial.eval_finsetSum]
  have hdeg : p.degree < (Finset.univ.image z).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have := Polynomial.degree_sum_fin_lt (fun i : Fin m => c i)
    rw [hp, Finset.sum_range]
    exact lt_of_lt_of_le this (by exact_mod_cast hm)
  have hp0 : p = 0 := Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero _ hdeg (fun x hx => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hx
    rw [hpe]; exact hev i)
  intro l hl
  have hc : p.coeff l = c l := by
    simp [hp, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hl]
  rw [← hc, hp0, Polynomial.coeff_zero]

/-- **The closure.** For `k` distinct atoms on the circle, the section of size `k + 1` has a nonzero null vector (its
last coefficient is `1`): the existence space is spanned exactly, and the next step has `|reflection coefficient| = 1`. -/
theorem section_degenerate {k : ℕ} (z : Fin k → ℂ) (w : Fin k → ℝ) (hz : ∀ i, ‖z i‖ = 1) (t : ℤ → ℂ)
    (ht : ∀ m : ℤ, t m = ∑ i, (w i : ℂ) * z i ^ m) :
    ∃ c : ℕ → ℂ, c k = 1 ∧ toepForm t (range (k + 1)) c = 0 := by
  set p : Polynomial ℂ := ∏ i : Fin k, (Polynomial.X - Polynomial.C (z i)) with hp
  have hmonic : p.Monic := Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)
  have hdeg : p.natDegree = k := by
    rw [hp, Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)]
    simp
  have hev : ∀ i, p.eval (z i) = 0 := fun i => by
    rw [hp, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  refine ⟨fun l => p.coeff l, ?_, ?_⟩
  · simp only
    rw [← hdeg]
    exact hmonic.coeff_natDegree
  · rw [toepForm_atoms z w hz t ht]
    have : ∀ i, ∑ l ∈ range (k + 1), p.coeff l * z i ^ l = 0 := fun i => by
      rw [← Polynomial.eval_eq_sum_range' (by omega : p.natDegree < k + 1)]
      exact hev i
    simp [this]

/-! ### 2. The curve model -/

/-- **Frobenius data of a curve of genus `g` over `F_q`** (classical facts, carried as fields; not proved here):
`n` distinct Frobenius eigenvalues `α` with multiplicities (total `2g`), closed under conjugation (real coefficients of
the `L`-polynomial) and under `α ↦ q/α` (functional equation), and point counts `N_m` given by rationality
`N_m = q^m + 1 - ∑ α_i^m` (the prime side). -/
structure CurveModel (g q : ℕ) where
  hq : 1 < q
  n : ℕ
  α : Fin n → ℂ
  mult : Fin n → ℕ
  hα : Function.Injective α
  hα0 : ∀ i, α i ≠ 0
  hmult : ∀ i, 0 < mult i
  hdeg : ∑ i, mult i = 2 * g
  hconj : ∀ i, ∃ j, α j = conj (α i)
  hfe : ∀ i, ∃ j, α j = (q : ℂ) / α i
  N : ℕ → ℕ
  hN : ∀ m : ℕ, (N m : ℂ) = (q : ℂ) ^ m + 1 - ∑ i, (mult i : ℂ) * α i ^ m

namespace CurveModel

variable {g q : ℕ} (M : CurveModel g q)

include M in
theorem sqrt_ne : (Real.sqrt q : ℝ) ≠ 0 := by
  have : (0 : ℝ) < q := by exact_mod_cast (lt_trans Nat.zero_lt_one M.hq)
  exact (Real.sqrt_pos.2 this).ne'

/-- The atoms normalised by the tick: `z_i = α_i / √q`. -/
def z (i : Fin M.n) : ℂ := M.α i / (Real.sqrt q : ℂ)

/-- The grid moments `A n = ∑ mult_i z_i^n`. -/
def A (n : ℕ) : ℂ := ∑ i, (M.mult i : ℂ) * M.z i ^ n

/-- The Hermitian moment sequence of the grid form. -/
def t (m : ℤ) : ℂ := if 0 ≤ m then M.A m.toNat else conj (M.A (-m).toNat)

/-- **Weil's theorem** (named external hypothesis): the Riemann hypothesis for the curve, `‖α_i‖ = √q`. -/
def WeilBound : Prop := ∀ i, ‖M.α i‖ = Real.sqrt q

theorem z_mul (i : Fin M.n) : (Real.sqrt q : ℂ) * M.z i = M.α i := by
  unfold z
  have : (Real.sqrt q : ℂ) ≠ 0 := by exact_mod_cast M.sqrt_ne
  field_simp

/-- **The moments come from the point counts alone.** `(√q)^n A n = q^n + 1 - N_n` (the prime side at lag `n log q`). -/
theorem moment_pointcount (n : ℕ) : (M.N n : ℂ) = (q : ℂ) ^ n + 1 - (Real.sqrt q : ℂ) ^ n * M.A n := by
  rw [M.hN n, A, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← M.z_mul i, mul_pow]
  ring

theorem A_zero : M.A 0 = ((2 * g : ℕ) : ℂ) := by
  simp only [A, pow_zero, mul_one]
  rw [← M.hdeg]
  push_cast
  rfl

theorem t_nat (n : ℕ) : M.t n = M.A n := by
  simp [t]

theorem t_herm (m : ℤ) : M.t (-m) = conj (M.t m) := by
  rcases lt_trichotomy m 0 with h | h | h
  · have h1 : ¬ (0 ≤ m) := not_le.2 h
    simp [t, h1, h.le]
  · subst h
    have h0 : M.t 0 = M.A 0 := by simpa using M.t_nat 0
    rw [neg_zero, h0, A_zero, map_natCast]
  · have h1 : ¬ (0 ≤ -m) := by omega
    simp [t, h.le, h]

theorem norm_z (hW : M.WeilBound) (i : Fin M.n) : ‖M.z i‖ = 1 := by
  unfold z
  rw [norm_div, hW i, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact div_self M.sqrt_ne

theorem z_inj : Function.Injective M.z := by
  intro i j h
  apply M.hα
  rw [← M.z_mul i, ← M.z_mul j, h]

theorem mirror (i : Fin M.n) : ∃ j, M.z j = (conj (M.z i))⁻¹ := by
  obtain ⟨i', hi'⟩ := M.hconj i
  obtain ⟨j, hj⟩ := M.hfe i'
  refine ⟨j, ?_⟩
  have hs : (Real.sqrt q : ℂ) ≠ 0 := by exact_mod_cast M.sqrt_ne
  have hsq : (Real.sqrt q : ℂ) ^ 2 = (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  have hai : conj (M.α i) ≠ 0 := by simpa using M.hα0 i
  have hzi : conj (M.z i) = conj (M.α i) / (Real.sqrt q : ℂ) := by
    simp [z, map_div₀]
  rw [hzi, inv_div, z, hj, hi']
  have hci : M.α i' ≠ 0 := M.hα0 i'
  rw [hi'] at hci
  field_simp
  rw [← hsq]

theorem hmom (n : ℕ) : M.t n = ∑ i, ((M.mult i : ℝ) : ℂ) * M.z i ^ n := by
  rw [t_nat]
  simp [A]

theorem exp_arg (hW : M.WeilBound) (i : Fin M.n) :
    Complex.exp (I * ((Complex.arg (M.z i) : ℝ) : ℂ) * ((1 : ℝ) : ℂ)) = M.z i := by
  have h := Complex.norm_mul_exp_arg_mul_I (M.z i)
  rw [M.norm_z hW i, Complex.ofReal_one, one_mul] at h
  have h1 : I * ((Complex.arg (M.z i) : ℝ) : ℂ) * ((1 : ℝ) : ℂ) = (Complex.arg (M.z i) : ℂ) * I := by
    push_cast; ring
  rw [h1]; exact h

/-- **The curve as a `ZeroModel`.** Under Weil's bound, the zeros are `ρ_i = 1/2 + i γ_i` with `γ_i = arg z_i` real, tick
`ε = 1` in the argument, and the multiplicities as weights. -/
def toZeroModel (hW : M.WeilBound) : ZeroModel M.n where
  γ i := ((Complex.arg (M.z i) : ℝ) : ℂ)
  σ := id
  hσ i := (Complex.conj_ofReal _).symm
  ε := 1
  hε := one_pos
  hinj := by
    intro i j h
    simp only [M.exp_arg hW] at h
    exact M.z_inj h
  w i := (M.mult i : ℂ)
  hw i := by exact_mod_cast (M.hmult i).ne'
  t := M.t
  ht := M.t_herm
  hmom n := by
    simp only [M.exp_arg hW]
    rw [t_nat]
    rfl

/-- **The sign, for a curve, under Weil's theorem.** The easy direction (`scaleSign_of_online`) on the curve's
`ZeroModel`: every scale step keeps the margin's sign. -/
theorem curve_scaleSign (hW : M.WeilBound) : ScaleSign M.t :=
  scaleSign_of_online (M.toZeroModel hW) (fun i => ⟨(M.mult i : ℝ), Nat.cast_nonneg _, by simp [toZeroModel]⟩)
    (fun i => by simp [toZeroModel])

/-- **For a curve, the sign is Weil's theorem.** `ScaleSign` of the prime-side moments holds exactly when every Frobenius
eigenvalue has modulus `√q`. (`⟹` is `atoms_on_circle`, with the mirror closure from the functional equation.) -/
theorem curve_scaleSign_iff : ScaleSign M.t ↔ M.WeilBound := by
  refine ⟨fun h => ?_, M.curve_scaleSign⟩
  have hpos := pos_of_sections ((scaleSign_iff M.t).1 h).2
  have hz0 : ∀ i, M.z i ≠ 0 := fun i hz => by
    have := M.z_mul i
    rw [hz, mul_zero] at this
    exact M.hα0 i this.symm
  intro i
  have hcirc := atoms_on_circle M.z (fun i => (M.mult i : ℂ)) M.z_inj
    (fun i => by exact_mod_cast (M.hmult i).ne') hz0 M.mirror M.t M.t_herm
    (fun n => by rw [M.t_nat]; simp [A]) hpos i
  have h2 := M.z_mul i
  have : ‖M.α i‖ = Real.sqrt q * ‖M.z i‖ := by
    rw [← h2, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [this, hcirc, mul_one]

/-- **The closure of the curve.** Under Weil's theorem, with `n` distinct Frobenius eigenvalues: every section of the grid
form of size `m ≤ n` is definite (so `|k| < 1` at each step before `n`), and the section of size `n + 1` has a nonzero null
vector (`|k_n| = 1`). When the `L`-polynomial has simple roots, `n = 2g`. -/
theorem curve_sections (hW : M.WeilBound) :
    (∀ m ≤ M.n, ∀ c : ℕ → ℂ, (toepForm M.t (range m) c).re = 0 → ∀ l < m, c l = 0) ∧
      ∃ c : ℕ → ℂ, c M.n = 1 ∧ toepForm M.t (range (M.n + 1)) c = 0 := by
  have hz := M.norm_z hW
  have hw : ∀ i, (0 : ℝ) < (M.mult i : ℝ) := fun i => by exact_mod_cast M.hmult i
  have ht : ∀ m : ℤ, M.t m = ∑ i, (((M.mult i : ℝ)) : ℂ) * M.z i ^ m :=
    moments_zpow M.z (fun i => (M.mult i : ℝ)) hz M.t M.t_herm M.hmom
  exact ⟨fun m hm c h => section_definite M.z (fun i => (M.mult i : ℝ)) hz hw M.z_inj M.t ht hm c h,
    section_degenerate M.z (fun i => (M.mult i : ℝ)) hz M.t ht⟩

/-- The same with `n = 2g` (distinct eigenvalues, the generic case): closure at `2g`. -/
theorem curve_closure_2g (hW : M.WeilBound) (hn : M.n = 2 * g) :
    (∀ m ≤ 2 * g, ∀ c : ℕ → ℂ, (toepForm M.t (range m) c).re = 0 → ∀ l < m, c l = 0) ∧
      ∃ c : ℕ → ℂ, c (2 * g) = 1 ∧ toepForm M.t (range (2 * g + 1)) c = 0 := by
  have := M.curve_sections hW
  rwa [hn] at this

end CurveModel

end ProofPhase.Unified
