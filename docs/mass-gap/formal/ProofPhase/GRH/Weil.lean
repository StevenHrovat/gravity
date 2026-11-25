/-
GRH attempt, step 2a: Weil's positivity criterion, in the abstract form (the explicit formula and the approximation
property as named hypotheses) and in a finite model where everything is proved (2026-11-23). Released under
Apache 2.0.

Note: `docs/rh-guide/grh/ATTEMPT.md`.
-/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Basic

/-!
# Weil's criterion: positivity of the zero pairing ⟺ all zeros on the line

**Coordinates.** A zero `ρ` of `L(χ, s)` in the strip is written `ρ = 1/2 + i γ`. "On the line" is `γ` real. The
functional equation together with complex conjugation maps the zeros of one `L(χ, s)` to themselves by
`ρ ↦ 1 - conj ρ`, which is `γ ↦ conj γ` (classical). So the data are an indexed family `γ : ι → ℂ` (an index per zero,
repeated with multiplicity) and an involution-like `σ : ι → ι` with `γ (σ i) = conj (γ i)`.

**The pairing.** For a test function `f` with transform `F(z) = ∫ f(x) e^{i z x} dx`, the transform of `h = f * f~`
(`f~(x) = conj f(-x)`) is `F(z) · conj F(conj z)`. Weil's functional on the zero side is
`W(F) = ∑_i F(γ_i) · conj F(γ_{σ i})` (`weilSum`). The explicit formula says this equals the arithmetic side (primes,
archimedean term from the Gamma factor, pole terms). Weil's criterion: GRH for `χ` ⟺ `W ≥ 0` on all test functions.

**What is proved here.**
* `weilSum_re_nonneg_of_real`: if every `γ_i` is real (GRH), then `Re W(F) ≥ 0` for every `F` (each term is `|F(γ_i)|²`).
* `real_of_weilSum_nonneg`: **positivity ⟹ GRH**, for any test class with the *approximation property*: for every
  finite saturated set `S` of zeros, every target `r` and every `ε > 0` there is a test transform equal to `r` on
  `S` with the rest of the zero sum of size `≤ ε`. If some `γ_{i₀}` were not real, the transform equal to `1` at
  `γ_{i₀}`, `-1` at `conj γ_{i₀}` makes `Re W ≤ -2 + ε < 0`.
* `weil_criterion_finite`: in a **finite model** (finitely many zeros) the approximation property holds exactly for
  finite exponential sums `F(z) = ∑ c_k e^{i z x_k}` (transforms of finite combinations of point masses), by Lagrange
  interpolation in `w = e^{i z ε}`; so there **positivity ⟺ all zeros on the line** is a theorem.

**Not here** (see ATTEMPT.md): the explicit formula for Dirichlet L-functions (not in Mathlib), and the approximation
property for smooth compactly supported test functions with infinitely many zeros, which needs a zero-counting bound
`N(T) = O(T log T)` (not in Mathlib) and a Paley-Wiener construction.
-/

open Complex Polynomial ComplexConjugate Real

open scoped ComplexOrder

noncomputable section

namespace ProofPhase.GRH

variable {ι : Type*}

/-- One term of the zero side of Weil's pairing. -/
def weilTerm (γ : ι → ℂ) (σ : ι → ι) (F : ℂ → ℂ) (i : ι) : ℂ := F (γ i) * conj (F (γ (σ i)))

/-- The zero side of Weil's pairing, `∑_i F(γ_i) conj F(γ_{σ i})`. -/
def weilSum (γ : ι → ℂ) (σ : ι → ι) (F : ℂ → ℂ) : ℂ := ∑' i, weilTerm γ σ F i

/-- **GRH ⟹ positivity.** -/
theorem weilSum_re_nonneg_of_real {γ : ι → ℂ} {σ : ι → ι} (hσ : ∀ i, γ (σ i) = conj (γ i))
    (hreal : ∀ i, (γ i).im = 0) (F : ℂ → ℂ) : 0 ≤ (weilSum γ σ F).re := by
  have hterm : ∀ i, 0 ≤ weilTerm γ σ F i := fun i => by
    have hc : conj (γ i) = γ i := Complex.conj_eq_iff_im.mpr (hreal i)
    rw [weilTerm, hσ i, hc, Complex.mul_conj', ← Complex.ofReal_pow]
    exact Complex.zero_le_real.mpr (by positivity)
  have h : (0 : ℂ) ≤ weilSum γ σ F := tsum_nonneg hterm
  exact (Complex.nonneg_iff.mp h).1

/-- A set of indices is saturated if it contains, with an index, every index carrying the same zero. -/
def Saturated (γ : ι → ℂ) (S : Finset ι) : Prop := ∀ i j, γ i = γ j → (i ∈ S ↔ j ∈ S)

/-- **The approximation property** of a test class `T` (a set of transforms). -/
def ApproxProp (γ : ι → ℂ) (σ : ι → ι) (T : Set (ℂ → ℂ)) : Prop :=
  ∀ (S : Finset ι), Saturated γ S → ∀ (r : ℂ → ℂ) (ε : ℝ), 0 < ε → ∃ F ∈ T,
    (∀ j ∈ S, F (γ j) = r (γ j)) ∧ ‖weilSum γ σ F - ∑ j ∈ S, weilTerm γ σ F j‖ ≤ ε

/-- **Positivity ⟹ GRH**, for a test class with the approximation property (finite multiplicities). -/
theorem real_of_weilSum_nonneg {γ : ι → ℂ} {σ : ι → ι} (hσ : ∀ i, γ (σ i) = conj (γ i))
    (hfin : ∀ z : ℂ, Set.Finite {j | γ j = z}) {T : Set (ℂ → ℂ)} (happ : ApproxProp γ σ T)
    (hpos : ∀ F ∈ T, 0 ≤ (weilSum γ σ F).re) : ∀ i, (γ i).im = 0 := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨i₀, hi₀⟩ := hne
  set z₀ := γ i₀ with hz₀
  have hne' : z₀ ≠ conj z₀ := fun h => hi₀ (Complex.conj_eq_iff_im.mp h.symm)
  have hSfin : Set.Finite {j | γ j = z₀ ∨ γ j = conj z₀} :=
    ((hfin z₀).union (hfin (conj z₀))).subset fun j hj => hj
  set S := hSfin.toFinset with hS
  have hmem : ∀ j, j ∈ S ↔ (γ j = z₀ ∨ γ j = conj z₀) := fun j => by simp [hS]
  have hsat : Saturated γ S := fun i j hij => by rw [hmem, hmem, hij]
  set r : ℂ → ℂ := fun z => if z = z₀ then 1 else if z = conj z₀ then -1 else 0 with hr
  obtain ⟨F, hFT, hFS, htail⟩ := happ S hsat r 1 one_pos
  have hF0 : F z₀ = 1 := by
    have := hFS i₀ ((hmem i₀).mpr (Or.inl rfl)); rw [← hz₀] at this; rw [this]; simp [hr]
  have hF1 : F (conj z₀) = -1 := by
    have h1 : σ i₀ ∈ S := (hmem _).mpr (Or.inr (hσ i₀))
    have := hFS (σ i₀) h1
    rw [hσ i₀, ← hz₀] at this; rw [this]; simp [hr, hne'.symm]
  -- every term over `S` is `-1`
  have hterm : ∀ j ∈ S, weilTerm γ σ F j = -1 := by
    intro j hj
    rcases (hmem j).mp hj with h | h
    · rw [weilTerm, hσ j, h, hF0, hF1]; simp
    · rw [weilTerm, hσ j, h, Complex.conj_conj, hF0, hF1]; simp
  have hsum : ∑ j ∈ S, weilTerm γ σ F j = -(S.card : ℂ) := by
    rw [Finset.sum_congr rfl hterm]; simp
  have hcard : 1 ≤ S.card := Finset.card_pos.mpr ⟨i₀, (hmem i₀).mpr (Or.inl rfl)⟩
  have hre : (weilSum γ σ F).re ≤ -(S.card : ℝ) + 1 := by
    have h1 := (Complex.abs_re_le_norm (weilSum γ σ F - ∑ j ∈ S, weilTerm γ σ F j)).trans htail
    rw [hsum, Complex.sub_re, Complex.neg_re, Complex.natCast_re] at h1
    have := (abs_le.mp h1).2
    linarith
  have hS2 : 2 ≤ S.card := by
    have h1 : σ i₀ ∈ S := (hmem _).mpr (Or.inr (hσ i₀))
    have hne2 : i₀ ≠ σ i₀ := fun h => hne' (by rw [hz₀]; conv_rhs => rw [← hσ i₀]; rw [← h])
    have : ({i₀, σ i₀} : Finset ι) ⊆ S := by
      intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact (hmem _).mpr (Or.inl rfl)
      · exact h1
    calc 2 = ({i₀, σ i₀} : Finset ι).card := (Finset.card_pair hne2).symm
      _ ≤ S.card := Finset.card_le_card this
  have hcast : (2 : ℝ) ≤ S.card := by exact_mod_cast hS2
  linarith [hpos F hFT]

/-! ### The finite model -/

/-- Finite exponential sums: transforms of finite combinations of point masses. -/
def expSums : Set (ℂ → ℂ) :=
  {F | ∃ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ), F = fun z => ∑ k, c k * Complex.exp (I * z * x k)}

/-- For a finite set of points there is a step `ε > 0` making `z ↦ e^{i z ε}` injective on it. -/
theorem exists_step_injOn (Z : Finset ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ Set.InjOn (fun z : ℂ => Complex.exp (I * z * ε)) Z := by
  set D : ℝ := 1 + ∑ z ∈ Z, ∑ z' ∈ Z, ‖z - z'‖ with hD
  have hD1 : 1 ≤ D := by
    have : 0 ≤ ∑ z ∈ Z, ∑ z' ∈ Z, ‖z - z'‖ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  refine ⟨1 / D, by positivity, fun z hz z' hz' heq => ?_⟩
  simp only at heq
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq
  have hle : ‖z - z'‖ ≤ D - 1 := by
    have h1 : ‖z - z'‖ ≤ ∑ z'' ∈ Z, ‖z - z''‖ :=
      Finset.single_le_sum (f := fun z'' => ‖z - z''‖) (fun _ _ => norm_nonneg _) hz'
    have h2 : ∑ z'' ∈ Z, ‖z - z''‖ ≤ ∑ y ∈ Z, ∑ z'' ∈ Z, ‖y - z''‖ :=
      Finset.single_le_sum (f := fun y => ∑ z'' ∈ Z, ‖y - z''‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hz
    linarith
  -- `(z - z') ε = 2 π n`
  have hkey : (z - z') * ((1 / D : ℝ) : ℂ) = 2 * π * n := by
    have : I * ((z - z') * ((1 / D : ℝ) : ℂ)) = I * (2 * π * n) := by
      linear_combination hn
    exact mul_left_cancel₀ Complex.I_ne_zero this
  by_cases hn0 : n = 0
  · rw [hn0] at hkey
    simp only [Int.cast_zero, mul_zero, mul_eq_zero, sub_eq_zero] at hkey
    rcases hkey with h | h
    · exact h
    · exfalso; have : (1 / D : ℝ) ≠ 0 := by positivity
      exact this (by exact_mod_cast h)
  · exfalso
    have hnorm := congrArg (‖·‖) hkey
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_intCast,
      Complex.norm_ofNat] at hnorm
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
      exact_mod_cast this
    have hpi : 0 < π := Real.pi_pos
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / D), abs_of_pos hpi] at hnorm
    have hlhs : ‖z - z'‖ * (1 / D) < 1 := by
      rw [mul_one_div, div_lt_one (by linarith)]; linarith
    nlinarith [Real.two_le_pi]

/-- **The approximation property holds exactly in the finite model**, for finite exponential sums. -/
theorem approx_finite [Fintype ι] (γ : ι → ℂ) (σ : ι → ι) : ApproxProp γ σ expSums := by
  classical
  intro S hsat r ε hε
  set Z : Finset ℂ := Finset.univ.image γ with hZ
  obtain ⟨δ, hδ, hinj⟩ := exists_step_injOn Z
  set w : ℂ → ℂ := fun z => Complex.exp (I * z * δ) with hw
  set r' : ℂ → ℂ := fun z => if ∃ j ∈ S, γ j = z then r z else 0 with hr'
  set P : ℂ[X] := Lagrange.interpolate Z w r' with hP
  set F : ℂ → ℂ := fun z => P.eval (w z) with hF
  have hFval : ∀ i, F (γ i) = r' (γ i) := fun i => by
    simp only [hF, hP]
    exact Lagrange.eval_interpolate_at_node r' hinj (Finset.mem_image_of_mem γ (Finset.mem_univ i))
  refine ⟨F, ?_, fun j hj => ?_, ?_⟩
  · refine ⟨P.natDegree + 1, fun k => (k : ℝ) * δ, fun k => P.coeff k, ?_⟩
    funext z
    simp only [hF, hw]
    rw [Polynomial.eval_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.exp_nat_mul]
    congr 2
    push_cast; ring
  · rw [hFval j]; simp only [hr']; have hex : ∃ j' ∈ S, γ j' = γ j := ⟨j, hj, rfl⟩
    simp only [hex, ↓reduceIte]
  · have hzero : ∀ i ∉ S, weilTerm γ σ F i = 0 := fun i hi => by
      have : F (γ i) = 0 := by
        rw [hFval i]; simp only [hr']
        have hnex : ¬ ∃ j ∈ S, γ j = γ i := by
          rintro ⟨j, hj, hji⟩
          exact hi ((hsat j i hji).mp hj)
        simp only [hnex, ↓reduceIte]
      simp [weilTerm, this]
    have hW : weilSum γ σ F = ∑ j ∈ S, weilTerm γ σ F j := by
      rw [weilSum, tsum_fintype]
      exact (Finset.sum_subset (Finset.subset_univ S) fun i _ hi => hzero i hi).symm
    rw [hW, sub_self, norm_zero]; exact hε.le

/-- **Weil's criterion in the finite model.** Finitely many zeros `γ_i`, closed under `γ ↦ conj γ` via `σ`: the zero
pairing is non-negative on every finite exponential sum **iff** every zero is on the line. -/
theorem weil_criterion_finite [Fintype ι] {γ : ι → ℂ} {σ : ι → ι} (hσ : ∀ i, γ (σ i) = conj (γ i)) :
    (∀ i, (γ i).im = 0) ↔ ∀ F ∈ expSums, 0 ≤ (weilSum γ σ F).re :=
  ⟨fun h F _ => weilSum_re_nonneg_of_real hσ h F,
    fun h => real_of_weilSum_nonneg hσ (fun _ => Set.toFinite _) (approx_finite γ σ) h⟩

end ProofPhase.GRH
