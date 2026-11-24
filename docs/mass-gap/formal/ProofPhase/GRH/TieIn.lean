/-
GRH tie-in, part 1: the easy direction of Weil's criterion in the project's grid form, and the two external hypotheses
(zeros of zeta, zeros of Dirichlet L-functions, on the line) tied to `ScaleSign` (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/GRH-TIE-IN.md`.
-/

import ProofPhase.Unified.GRH
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Zeros on the line give the sign (the easy direction), and the external proofs tied in

**What was already in the repository** (checked before writing this file).
* `GRH/Weil.lean`, `weilSum_re_nonneg_of_real`: zeros on the line give `Re W(F) ≥ 0` for every test function `F`, for any
  family of zeros (any index type, any multiplicities). This is the easy direction of Weil's criterion *at the level of
  the pairing*.
* `GRH/Weil.lean`, `weil_criterion_finite`: both directions on finite exponential sums, finite model.
* `Unified/GRH.lean`, `grh_instance`: the hard direction in the finite model (`ScaleSign` gives zeros on the line).

**What was missing, and is proved here.** The easy direction *at the level of the ledger's sign*: zeros on the line give
`ScaleSign t` for the grid Toeplitz moments `t`.
* `scaleSign_of_explicit_formula`: general (any family of zeros, infinite included), with the explicit formula on the
  grid, `ExplicitFormula`, as a named hypothesis (the identity "Toeplitz form of the prime side = Weil's zero pairing of a
  test function"; the test class is left open; not in Mathlib).
* `scaleSign_of_online`: in the finite model `ZeroModel`, with weights real and nonnegative (multiplicities), no
  explicit-formula hypothesis is needed: the moments are the atoms' power sums (`atomic_toep_nonneg`).
* `scaleSign_iff_online`: therefore, in the finite model with multiplicity weights, `ScaleSign ⟺ all zeros on the line`
  (the hard direction is `grh_instance`).

**The external proofs** (others, Lean, 2026-11-20; `docs/rh-guide/SOURCES.md`): `ExtRH` is Mathlib's own
`RiemannHypothesis`; `ExtDirichletGRH` is their `LFunction_eq_zero_re`, word for word. They are hypotheses here (named,
not axioms; nothing is imported from their library). The tie: `dirichlet_tie_in`, `zeta_tie_in` and their finite-model
forms.

Standard axioms only.
-/

open Finset ComplexConjugate Complex

noncomputable section

namespace ProofPhase.Unified

open ProofPhase.GRH

/-! ### 1. The easy direction in the ledger's form -/

/-- The grid test function: the transform of the cells `s` with coefficients `c`, `F(z) = ∑ c_j e^{i z j ε}`. -/
def gridTest (ε : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) : ℂ → ℂ :=
  fun z => ∑ j ∈ s, c j * Complex.exp (I * z * (((j : ℝ) * ε : ℝ) : ℂ))

/-- **The explicit formula on the grid, for a test class `T`** (named hypothesis; not in Mathlib): the Toeplitz form
of the prime-side moments `t` on the cells `s` with coefficients `c` is Weil's zero pairing of the test function `T s c`.
The class is left open on purpose: `gridTest ε` (finite exponential sums, the finite model) or smoothed cells (the infinite
case, where point masses are not admissible and the explicit formula needs decay). -/
def ExplicitFormula {ι : Type*} (T : Finset ℕ → (ℕ → ℂ) → ℂ → ℂ) (t : ℤ → ℂ) (γ : ι → ℂ) (σ : ι → ι) : Prop :=
  ∀ (s : Finset ℕ) (c : ℕ → ℂ), toepForm t s c = weilSum γ σ (T s c)

/-- The mass `re (t 0)` is nonnegative when every Toeplitz form is. -/
theorem mass_nonneg_of_forms {t : ℤ → ℂ} (h : ∀ s c, 0 ≤ (toepForm t s c).re) : 0 ≤ (t 0).re := by
  have := h {0} (fun _ => 1)
  simpa [toepForm] using this

/-- **The easy direction (general).** Zeros on the line give the sign: if the explicit formula holds for the moments
`t` and every zero is on the line, then `ScaleSign t`. Any family of zeros, infinite included; no summability needed. -/
theorem scaleSign_of_explicit_formula {ι : Type*} {γ : ι → ℂ} {σ : ι → ι} {T : Finset ℕ → (ℕ → ℂ) → ℂ → ℂ} {t : ℤ → ℂ}
    (hσ : ∀ i, γ (σ i) = conj (γ i)) (hreal : ∀ i, (γ i).im = 0) (hEF : ExplicitFormula T t γ σ) :
    ScaleSign t := by
  have hpos : ∀ s c, 0 ≤ (toepForm t s c).re := fun s c => by
    rw [hEF]; exact weilSum_re_nonneg_of_real hσ hreal _
  exact (scaleSign_iff t).2 ⟨mass_nonneg_of_forms hpos, fun k c => hpos _ c⟩

/-- Hermitian moments of atoms on the circle with real weights are the power sums for every integer exponent. -/
theorem moments_zpow {k : ℕ} (z : Fin k → ℂ) (w : Fin k → ℝ) (hz : ∀ i, ‖z i‖ = 1) (t : ℤ → ℂ)
    (ht : ∀ m : ℤ, t (-m) = conj (t m)) (hmom : ∀ n : ℕ, t n = ∑ i, (w i : ℂ) * z i ^ n) (m : ℤ) :
    t m = ∑ i, (w i : ℂ) * z i ^ m := by
  have hinv : ∀ i, (z i)⁻¹ = conj (z i) := by
    intro i
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz i]
    simp
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · rw [hmom n]
    simp
  · rw [ht (n : ℤ), hmom n, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zpow_neg, zpow_natCast, map_mul, Complex.conj_ofReal, map_pow, ← hinv, inv_pow]

/-- **The easy direction (finite model).** In the finite model with real nonnegative weights (the multiplicities), every
zero on the line gives `ScaleSign`. No explicit-formula hypothesis: the moments are the atoms' power sums. -/
theorem scaleSign_of_online {k : ℕ} (Z : ZeroModel k) (hw : ∀ i, ∃ r : ℝ, 0 ≤ r ∧ Z.w i = r)
    (hreal : ∀ i, (Z.γ i).im = 0) : ScaleSign Z.t := by
  choose r hr0 hr using hw
  have hz : ∀ i, ‖Complex.exp (I * Z.γ i * Z.ε)‖ = 1 := by
    intro i
    rw [Complex.norm_exp]
    simp [Complex.mul_re, hreal i]
  have hmom' : ∀ n : ℕ, Z.t n = ∑ i, (r i : ℂ) * (Complex.exp (I * Z.γ i * Z.ε)) ^ n := fun n => by
    rw [Z.hmom n]
    simp [hr]
  have ht' := moments_zpow _ r hz Z.t Z.ht hmom'
  have hpos := atomic_toep_nonneg _ r hz hr0 Z.t ht'
  exact (scaleSign_iff _).2 ⟨mass_nonneg_of_forms hpos, fun k c => hpos _ c⟩

/-- **In the finite model with multiplicity weights, the sign is exactly the line.** (`⟸` is the easy direction above,
`⟹` is `grh_instance`.) -/
theorem scaleSign_iff_online {k : ℕ} (Z : ZeroModel k) (hw : ∀ i, ∃ r : ℝ, 0 ≤ r ∧ Z.w i = r) :
    ScaleSign Z.t ↔ ∀ i, (Z.γ i).im = 0 :=
  ⟨fun h => (grh_instance Z h).1, scaleSign_of_online Z hw⟩

/-! ### 2. The external hypotheses (named; proved by others in Lean on 2026-11-20) -/

/-- **External hypothesis 1 (zeta).** Mathlib's own `RiemannHypothesis`: every zero of `ζ` other than `-2, -4, -6, …` and
other than a point at `1` has real part `1/2`. The external proof's `riemannHypothesis` has exactly this type. -/
def ExtRH : Prop := RiemannHypothesis

/-- **External hypothesis 2 (Dirichlet GRH).** Their `LFunction_eq_zero_re`, word for word: for every modulus `N`, every
Dirichlet character `χ` mod `N` (primitive or not), every zero of `L(χ, s)` in the open strip `0 < Re s < 1` has real
part `1/2`. -/
def ExtDirichletGRH : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- A family of zeros of `L` in the open critical strip, written `ρ_i = 1/2 + i γ_i` (as in `GRH/Weil.lean`). -/
def StripZeros {ι : Type*} (L : ℂ → ℂ) (γ : ι → ℂ) : Prop :=
  ∀ i, 0 < (1 / 2 + I * γ i).re ∧ (1 / 2 + I * γ i).re < 1 ∧ L (1 / 2 + I * γ i) = 0

theorem re_half_add (γ : ℂ) : (1 / 2 + I * γ).re = 1 / 2 - γ.im := by
  simp [Complex.add_re, Complex.mul_re]
  ring

/-- Real part `1/2` of `1/2 + i γ` is `γ` real. -/
theorem im_eq_zero_of_re_half {γ : ℂ} (h : (1 / 2 + I * γ).re = 1 / 2) : γ.im = 0 := by
  rw [re_half_add] at h
  linarith

/-- The external Dirichlet statement puts every strip zero of every `L(χ, ·)` on the line, in the coordinate `γ`. -/
theorem real_of_extDirichlet (hExt : ExtDirichletGRH) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {ι : Type*} {γ : ι → ℂ} (hz : StripZeros (DirichletCharacter.LFunction χ) γ) : ∀ i, (γ i).im = 0 := by
  intro i
  obtain ⟨h0, h1, h2⟩ := hz i
  exact im_eq_zero_of_re_half (hExt N χ _ h0 h1 h2)

/-- The external zeta statement puts every strip zero of `ζ` on the line, in the coordinate `γ`. -/
theorem real_of_extRH (hExt : ExtRH) {ι : Type*} {γ : ι → ℂ} (hz : StripZeros riemannZeta γ) :
    ∀ i, (γ i).im = 0 := by
  intro i
  obtain ⟨h0, h1, h2⟩ := hz i
  refine im_eq_zero_of_re_half (hExt _ h2 ?_ ?_)
  · rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp at this
    rw [re_half_add] at h0
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · intro h
    rw [h] at h1
    simp at h1

/-! ### 3. The tie: external hypothesis + easy direction = the project's sign -/

/-- **Dirichlet column, general form.** From the external Dirichlet GRH and the explicit formula on the grid: `ScaleSign` for the
prime-side moments of `L(χ, ·)`, and Weil's pairing nonnegative on every test function. -/
theorem dirichlet_tie_in (hExt : ExtDirichletGRH) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {ι : Type*} {γ : ι → ℂ} {σ : ι → ι} (hσ : ∀ i, γ (σ i) = conj (γ i))
    (hz : StripZeros (DirichletCharacter.LFunction χ) γ) {T : Finset ℕ → (ℕ → ℂ) → ℂ → ℂ} {t : ℤ → ℂ}
    (hEF : ExplicitFormula T t γ σ) : ScaleSign t ∧ ∀ F, 0 ≤ (weilSum γ σ F).re :=
  ⟨scaleSign_of_explicit_formula hσ (real_of_extDirichlet hExt χ hz) hEF,
    weilSum_re_nonneg_of_real hσ (real_of_extDirichlet hExt χ hz)⟩

/-- **Zeta column, general form.** -/
theorem zeta_tie_in (hExt : ExtRH) {ι : Type*} {γ : ι → ℂ} {σ : ι → ι} (hσ : ∀ i, γ (σ i) = conj (γ i))
    (hz : StripZeros riemannZeta γ) {T : Finset ℕ → (ℕ → ℂ) → ℂ → ℂ} {t : ℤ → ℂ} (hEF : ExplicitFormula T t γ σ) :
    ScaleSign t ∧ ∀ F, 0 ≤ (weilSum γ σ F).re :=
  ⟨scaleSign_of_explicit_formula hσ (real_of_extRH hExt hz) hEF,
    weilSum_re_nonneg_of_real hσ (real_of_extRH hExt hz)⟩

/-- **Dirichlet column, finite model of the ledger.** A `ZeroModel` whose zeros are strip zeros of `L(χ, ·)`, with
multiplicity weights: the external hypothesis gives `ScaleSign` of the model's moments and nonnegative Weil pairing on
every finite exponential sum. -/
theorem dirichlet_tie_in_finite (hExt : ExtDirichletGRH) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {k : ℕ}
    (Z : ZeroModel k) (hw : ∀ i, ∃ r : ℝ, 0 ≤ r ∧ Z.w i = r)
    (hz : StripZeros (DirichletCharacter.LFunction χ) Z.γ) :
    ScaleSign Z.t ∧ ∀ F ∈ expSums, 0 ≤ (weilSum Z.γ Z.σ F).re :=
  ⟨scaleSign_of_online Z hw (real_of_extDirichlet hExt χ hz),
    (weil_criterion_finite Z.hσ).1 (real_of_extDirichlet hExt χ hz)⟩

/-- **Zeta column, finite model of the ledger.** -/
theorem zeta_tie_in_finite (hExt : ExtRH) {k : ℕ} (Z : ZeroModel k) (hw : ∀ i, ∃ r : ℝ, 0 ≤ r ∧ Z.w i = r)
    (hz : StripZeros riemannZeta Z.γ) : ScaleSign Z.t ∧ ∀ F ∈ expSums, 0 ≤ (weilSum Z.γ Z.σ F).re :=
  ⟨scaleSign_of_online Z hw (real_of_extRH hExt hz), (weil_criterion_finite Z.hσ).1 (real_of_extRH hExt hz)⟩

end ProofPhase.Unified
