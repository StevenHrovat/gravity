/-
GRH attempt, Tate round: finite facts about the local pieces (2026-11-23). Released under Apache 2.0.

Note: `docs/rh-guide/grh/TATE.md`.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# The local pieces of Weil's form, in finite form

**1. The local factor is a phase on the critical line** (`local_factor_unimodular`): for `x > 0` and `s = 1/2 + i t`,
`‖1 - x^(-s)‖ = ‖1 - x^(s-1)‖`, so Tate's local gamma factor `(1 - p^(-s)) / (1 - p^(s-1))` at an unramified prime
has modulus one on the line: the local Fourier transform acts there as a unitary multiplier.

**2. The prime lattices are disjoint** (`prime_lattices_disjoint`): `k log p ≠ l log q` for distinct primes and
`k ≥ 1` (unique factorisation). The local terms of different primes live on disjoint sets of lags, so the only thing
places can exchange is the lag-0 (identity) part.

**3. A form with zero diagonal is indefinite** (`zero_diag_indefinite`): a real symmetric matrix with zero diagonal
and a non-zero entry takes a negative value. Each prime's block of Weil's form has zero diagonal (it lives at lags
`k log p ≠ 0`), so each local prime term is indefinite on its own.

**4. Place-by-place positivity forces the real place to be positive** (`local_assembly_forces_arch`): if the
places exchange only multiples of the identity (`a_0 + ∑ a_i = 0`), every prime block has zero diagonal, and every
shifted local form is nonnegative, then every `a_i ≥ 0` and the real place's own form is nonnegative.

**5. "It runs" plus the mirror puts every mode on the line** (`runs_and_mirror_on_line`): if an evolution `T` does
not increase a (positive) norm, and it has an eigenvalue `μ ≠ 0` together with the mirror eigenvalue
`(conj μ)⁻¹` (the functional equation's partner), then `‖μ‖ = 1`. An off-line pair is a growing mode and its
decaying mirror; a norm-nonincreasing evolution has no growing mode. Without a positive norm the conclusion fails:
`krein_off_line` (`GRH/Orbits.lean`) is a form-preserving map with the eigenvalue `3/4`.
-/

open Finset ComplexConjugate

open scoped Matrix

noncomputable section

namespace ProofPhase.GRH

/-- Tate's local factor at an unramified prime is a phase on the critical line. -/
theorem local_factor_unimodular (x : ℝ) (hx : 0 < x) (t : ℝ) :
    ‖1 - (x : ℂ) ^ (-((1 / 2 : ℂ) + t * Complex.I))‖ =
      ‖1 - (x : ℂ) ^ (((1 / 2 : ℂ) + t * Complex.I) - 1)‖ := by
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_pos.ne
  have hconj : ((1 / 2 : ℂ) + t * Complex.I) - 1 = conj (-((1 / 2 : ℂ) + t * Complex.I)) := by
    apply Complex.ext <;> norm_num
  have hpow : (x : ℂ) ^ (((1 / 2 : ℂ) + t * Complex.I) - 1) =
      conj ((x : ℂ) ^ (-((1 / 2 : ℂ) + t * Complex.I))) := by
    rw [hconj, Complex.cpow_conj _ _ harg, Complex.conj_ofReal]
  rw [hpow]
  set z := (x : ℂ) ^ (-((1 / 2 : ℂ) + t * Complex.I))
  rw [show (1 : ℂ) - conj z = conj (1 - z) by rw [map_sub, map_one], Complex.norm_conj]

/-- Unique factorisation: the lattices `k log p` of distinct primes do not meet (for `k ≥ 1`). -/
theorem prime_lattices_disjoint {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {k : ℕ} (hk : 1 ≤ k)
    (l : ℕ) : (k : ℝ) * Real.log p ≠ (l : ℝ) * Real.log q := by
  intro h
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hpow : ((p : ℝ) ^ k) = (q : ℝ) ^ l := by
    rw [← Real.exp_log (pow_pos hp0 k), ← Real.exp_log (pow_pos hq0 l), Real.log_pow, Real.log_pow, h]
  have hnat : p ^ k = q ^ l := by exact_mod_cast hpow
  have hdvd : p ∣ q ^ l := hnat ▸ dvd_pow_self p (by omega)
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hdvd))

/-- The value of a form on `e_i + c e_j`. -/
theorem form_two_point {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (c : ℝ) :
    (Pi.single i 1 + c • Pi.single j 1) ⬝ᵥ (A *ᵥ (Pi.single i 1 + c • Pi.single j 1)) =
      A i i + c * (A i j + A j i) + c ^ 2 * A j j := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, single_dotProduct, Matrix.col_apply, smul_eq_mul, one_mul]
  ring

/-- A real symmetric form with zero diagonal and a non-zero entry takes a negative value. -/
theorem zero_diag_indefinite {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hs : ∀ i j, A i j = A j i)
    (hd : ∀ i, A i i = 0) {i j : Fin n} (hij : A i j ≠ 0) :
    ∃ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) < 0 := by
  refine ⟨Pi.single i 1 + (-A i j) • Pi.single j 1, ?_⟩
  rw [form_two_point, hd i, hd j, ← hs i j]
  have : 0 < A i j ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hij))
  nlinarith

/-- Place-by-place positivity, with the places exchanging only multiples of the identity, forces every exchanged
amount at a prime to be nonnegative and the real place's form to be nonnegative on its own. -/
theorem local_assembly_forces_arch {n : ℕ} {ι : Type*} (s : Finset ι) (A0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (P : ι → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hd : ∀ i ∈ s, ∀ j, P i j j = 0) (a0 : ℝ) (a : ι → ℝ)
    (hsum : a0 + ∑ i ∈ s, a i = 0)
    (hA : ∀ x, 0 ≤ x ⬝ᵥ (A0 *ᵥ x) + a0 * (x ⬝ᵥ x))
    (hP : ∀ i ∈ s, ∀ x, 0 ≤ x ⬝ᵥ (P i *ᵥ x) + a i * (x ⬝ᵥ x)) :
    (∀ i ∈ s, 0 ≤ a i) ∧ ∀ x, 0 ≤ x ⬝ᵥ (A0 *ᵥ x) := by
  have ha : ∀ i ∈ s, 0 ≤ a i := by
    intro i hi
    have h := hP i hi (Pi.single 0 1)
    have e1 : Pi.single (0 : Fin (n + 1)) (1 : ℝ) ⬝ᵥ (P i *ᵥ Pi.single 0 1) = P i 0 0 := by
      simp [single_dotProduct]
    have e2 : Pi.single (0 : Fin (n + 1)) (1 : ℝ) ⬝ᵥ Pi.single 0 1 = 1 := by
      simp
    rw [e1, e2, hd i hi 0] at h
    linarith
  refine ⟨ha, fun x => ?_⟩
  have ha0 : a0 ≤ 0 := by
    have := Finset.sum_nonneg ha
    linarith
  have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
  have := hA x
  nlinarith

/-- "It runs" plus the mirror: a norm-nonincreasing evolution with an eigenvalue `μ ≠ 0` and the mirror eigenvalue
`(conj μ)⁻¹` has `‖μ‖ = 1` (no growing mode, hence no decaying mirror either). -/
theorem runs_and_mirror_on_line {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (T : V → V)
    (hT : ∀ x, ‖T x‖ ≤ ‖x‖) {μ : ℂ} (hμ : μ ≠ 0) {v w : V} (hv : v ≠ 0) (hw : w ≠ 0)
    (h1 : T v = μ • v) (h2 : T w = (conj μ)⁻¹ • w) : ‖μ‖ = 1 := by
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have a : ‖μ‖ ≤ 1 := by
    have := hT v
    rw [h1, norm_smul] at this
    exact (mul_le_iff_le_one_left hv').mp this
  have b : ‖μ‖⁻¹ ≤ 1 := by
    have := hT w
    rw [h2, norm_smul, norm_inv, Complex.norm_conj] at this
    exact (mul_le_iff_le_one_left hw').mp this
  have hpos : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
  have : 1 ≤ ‖μ‖ := (inv_le_one₀ hpos).mp b
  linarith

end ProofPhase.GRH
