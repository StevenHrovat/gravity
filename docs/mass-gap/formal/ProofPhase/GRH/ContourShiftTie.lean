/-
The contour shift, the tie: the Mathlib-only core identified with the project's explicit-formula statements, the test
class, the explicit formula with no named step, and the zeta column of the GRH ledger (2026-11-24).
Released under Apache 2.0.

Paper: `docs/unified/CONTOUR-SHIFT.md`, section 7.
-/

import ProofPhase.GRH.ContourShift
import ProofPhase.GRH.ExplicitFormulaTie

/-!
# The tie: from the core (`ProofPhase.GRH.CS`, Mathlib only) to `ExplicitFormula*.lean`

This is the only ContourShift file that imports project modules; the core files import only Mathlib.

* `contourShift_EF`: the core theorem `CS.contourShift` is the project's named step `EF.ContourShift c g` (the core
  repeats the definitions `laplace`, `vpt`, `vline`, `wInt` and the zero family with the same bodies, so the
  identification is definitional).
* `efTest_of_smooth`: smooth compactly supported test functions satisfy `EF.EFTest c g` on every line `c > 1`.
* **`explicit_formula_smooth`**, **`explicit_formula_of_smooth`**: Weil's explicit formula for `ζ` with no named step.
* **`zeta_tie_in_smooth`**: `zeta_tie_in_contourShift` with `ContourShift` and `EFTest` discharged for smooth compactly
  supported kernels; what remains are `ExtRH` (external), `KernelSpec` and the symmetry `σ`.

Standard axioms only. This does not prove RH or GRH: the sign comes from `ExtRH` through the easy direction.
-/

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped Real ContDiff ComplexConjugate

noncomputable section

namespace ProofPhase.GRH.CSTie

open ProofPhase.GRH ProofPhase.GRH.EF ProofPhase.Unified

/-! ### 1. The identification -/

/-- **The named step is a theorem.** `EF.ContourShift c g` for `c > 1` and `g` smooth with compact support. -/
theorem contourShift_EF {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} (hg : ∀ k : ℕ, ContDiff ℝ k g)
    (hgs : HasCompactSupport g) : ContourShift c g :=
  fun ι γ hZ => CS.contourShift hc hg hgs ι γ hZ

/-! ### 2. The test class and the explicit formula with no named step -/

theorem vpt_eq (c τ : ℝ) : vpt c τ = (c : ℂ) + ((-2 * π * τ : ℝ) : ℂ) * I := by
  simp only [vpt]; push_cast; ring

/-- **Smooth compactly supported test functions are admissible** on every line `c > 1` (the two integrability
conditions of `EF.EFTest`). -/
theorem efTest_of_smooth {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} (hg : ∀ k : ℕ, ContDiff ℝ k g)
    (hgs : HasCompactSupport g) : EFTest c g := by
  have hgc : Continuous g := (hg 0).continuous
  have hHd := CS.differentiable_laplace hgc hgs
  obtain ⟨C₄, hC₄0, hC₄⟩ := CS.laplace_decay hg hgs 4 c
  obtain ⟨B, hB, hvl⟩ := CS.logDeriv_vline_bound hc
  have hF : 𝓕 (tilt c g) = fun τ => laplace g (vpt c τ) := funext fun τ => (laplace_vpt c τ g).symm
  have hre : ∀ τ : ℝ, |(vpt c τ).re - 1 / 2| ≤ c := fun τ => by
    rw [vpt_re, abs_le]; constructor <;> linarith
  have him : ∀ τ : ℝ, (vpt c τ).im = -2 * π * τ := fun τ => by rw [vpt_eq]; simp
  have hτ : ∀ τ : ℝ, 1 + |τ| ≤ 1 + |(vpt c τ).im| := fun τ => by
    rw [him, abs_mul, abs_mul, abs_neg, abs_two, abs_of_pos Real.pi_pos]
    nlinarith [abs_nonneg τ, Real.pi_gt_three]
  have hdec : ∀ τ : ℝ, ‖laplace g (vpt c τ)‖ ≤ C₄ / (1 + |τ|) ^ 4 := fun τ => by
    rw [le_div_iff₀ (by positivity)]
    calc ‖laplace g (vpt c τ)‖ * (1 + |τ|) ^ 4 ≤ ‖laplace g (vpt c τ)‖ * (1 + |(vpt c τ).im|) ^ 4 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (hτ τ) 4) (norm_nonneg _)
      _ ≤ C₄ := hC₄ _ (hre τ)
  have hint2 := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp))
  have hcontF : Continuous fun τ : ℝ => laplace g (vpt c τ) := hHd.continuous.comp (by unfold vpt; fun_prop)
  have hfour : Integrable (𝓕 (tilt c g)) := by
    rw [hF]
    refine (hint2.const_mul C₄).mono' hcontF.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two]
    refine (hdec τ).trans ?_
    rw [div_eq_mul_inv]
    have h1 : (1 : ℝ) ≤ 1 + |τ| := by linarith [abs_nonneg τ]
    have h2 : ((1 + |τ|) ^ 4)⁻¹ ≤ ((1 + |τ|) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 (by norm_num))
    exact mul_le_mul_of_nonneg_left h2 hC₄0
  refine ⟨hgc, hgs, hfour, ?_⟩
  -- the real-place weight: `Γ_ℝ'/Γ_ℝ = Λ'/Λ + L(Λ, ·)` on the line, polynomially bounded
  set A := ∑' n, aw c n with hA
  have hA0 : 0 ≤ A := tsum_nonneg fun n => aw_nonneg c n
  have hgam : ∀ τ : ℝ, logDeriv Gammaℝ (vpt c τ) =
      logDeriv completedRiemannZeta (vpt c τ) + LSeries vM (vpt c τ) := fun τ => by
    have h1 : 1 < (vpt c τ).re := by rw [vpt_re]; exact hc
    rw [logDeriv_completedZeta h1, ← neg_logDeriv_zeta h1]
    ring
  have hcontΛ : Continuous fun τ : ℝ => logDeriv completedRiemannZeta (vpt c τ) := by
    refine continuous_iff_continuousAt.2 fun τ => ?_
    have h1 : 1 < (vpt c τ).re := by rw [vpt_re]; exact hc
    have h0 : vpt c τ ≠ 0 := vpt_ne_zero hc τ
    have h1' : vpt c τ ≠ 1 := vpt_ne_one hc τ
    exact ContinuousAt.comp (f := fun τ : ℝ => vpt c τ)
      (CS.continuousAt_logDeriv_completed h0 h1' (CS.xiF_ne_zero_of_re (Or.inr h1.le)))
      (Continuous.continuousAt (by unfold vpt; fun_prop))
  have hcontA : Continuous fun τ : ℝ => logDeriv Gammaℝ (vpt c τ) * 𝓕 (tilt c g) τ := by
    rw [hF]
    simp_rw [hgam]
    exact (hcontΛ.add (continuous_LSeries_vM_vpt hc)).mul hcontF
  refine ((hint2.const_mul ((B * 4 * π ^ 2 + B + A) * C₄))).mono' hcontA.aestronglyMeasurable
    (Eventually.of_forall fun τ => ?_)
  rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two, hF]
  simp only
  rw [hgam, norm_mul]
  have hΛ : ‖logDeriv completedRiemannZeta (vpt c τ)‖ ≤ B * (1 + |(vpt c τ).im|) ^ 2 := by
    have := (hvl (-2 * π * τ)).1
    rw [← vpt_eq] at this
    rw [him]; exact this
  have hL := norm_LSeries_vM_vpt_le hc τ
  have hpos : 0 < 1 + |τ| := by positivity
  have hY : 1 + |(vpt c τ).im| ≤ 2 * π * (1 + |τ|) := by
    rw [him, abs_mul, abs_mul, abs_neg, abs_two, abs_of_pos Real.pi_pos]
    nlinarith [abs_nonneg τ, Real.pi_gt_three]
  have hdec' := hdec τ
  calc ‖logDeriv completedRiemannZeta (vpt c τ) + LSeries vM (vpt c τ)‖ * ‖laplace g (vpt c τ)‖
      ≤ (B * (2 * π * (1 + |τ|)) ^ 2 + A) * (C₄ / (1 + |τ|) ^ 4) := by
        gcongr
        refine (norm_add_le _ _).trans (add_le_add (hΛ.trans ?_) hL)
        gcongr
    _ ≤ (B * 4 * π ^ 2 + B + A) * C₄ * ((1 + |τ|) ^ 2)⁻¹ := by
        have hp2 : 1 ≤ (1 + |τ|) ^ 2 := by nlinarith [abs_nonneg τ]
        rw [div_eq_mul_inv]
        have e : (B * (2 * π * (1 + |τ|)) ^ 2 + A) * (C₄ * ((1 + |τ|) ^ 4)⁻¹) =
            (B * 4 * π ^ 2 + A / (1 + |τ|) ^ 2) * C₄ * ((1 + |τ|) ^ 2)⁻¹ := by
          field_simp
          ring
        rw [e]
        have h3 : A / (1 + |τ|) ^ 2 ≤ A := div_le_self hA0 hp2
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hC₄0) (by positivity)
        linarith [hB]

theorem contDiff_refl {g : ℝ → ℂ} (hg : ∀ k : ℕ, ContDiff ℝ k g) (k : ℕ) : ContDiff ℝ k (refl g) :=
  (hg k).comp contDiff_neg

theorem hasCompactSupport_refl {g : ℝ → ℂ} (hgs : HasCompactSupport g) : HasCompactSupport (refl g) :=
  hgs.comp_homeomorph (Homeomorph.neg ℝ)

/-- **Weil's explicit formula for `ζ`, with no named step.** For `c > 1`, `g` smooth with compact support, and any
enumeration `γ` of the nontrivial zeros `ρ = 1/2 + iγ` with multiplicity: the zero sum converges absolutely and
`∑_γ ∫ g(x) e^{iγx} dx = H(1) + H(0) - ∑ₙ Λ(n) n^{-1/2} (g(log n) + g(-log n)) + (A(g) + A(g~))/2`. -/
theorem explicit_formula_smooth {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} (hg : ∀ k : ℕ, ContDiff ℝ k g)
    (hgs : HasCompactSupport g) {ι : Type} {γ : ι → ℂ} (hZ : NontrivialZeroFamily γ) :
    Summable (fun i => ∫ x : ℝ, g x * Complex.exp (I * γ i * x)) ∧
      ∑' i, ∫ x : ℝ, g x * Complex.exp (I * γ i * x) = efRHS c g :=
  explicit_formula_zeros hc (efTest_of_smooth hc hg hgs)
    (efTest_of_smooth hc (contDiff_refl hg) (hasCompactSupport_refl hgs)) (contourShift_EF hc hg hgs) hZ


theorem contDiff_nat_of_smooth {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (k : ℕ) : ContDiff ℝ k g :=
  hg.of_le (by exact_mod_cast le_top)

/-- **Weil's explicit formula for `ζ`, for every smooth compactly supported test function**, with no named step. -/
theorem explicit_formula_of_smooth {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hgs : HasCompactSupport g) {ι : Type} {γ : ι → ℂ} (hZ : NontrivialZeroFamily γ) :
    Summable (fun i => ∫ x : ℝ, g x * Complex.exp (I * γ i * x)) ∧
      ∑' i, ∫ x : ℝ, g x * Complex.exp (I * γ i * x) = efRHS c g :=
  explicit_formula_smooth hc (contDiff_nat_of_smooth hg) hgs hZ

/-- **The zeta column of the ledger, from `ExtRH` alone (plus the kernel bookkeeping).** For kernels `k m` smooth with
compact support, `ContourShift` and the test-class conditions are theorems, so `zeta_tie_in_contourShift` needs only
`ExtRH`, `KernelSpec` and the conjugation symmetry `σ`. -/
theorem zeta_tie_in_smooth (hExt : ExtRH) {c : ℝ} (hc : 1 < c) {Φ : ℂ → ℂ} {ε : ℝ} {k : ℤ → ℝ → ℂ}
    (hk : ∀ m, ContDiff ℝ ∞ (k m)) (hks : ∀ m, HasCompactSupport (k m)) (hK : KernelSpec Φ ε k)
    {ι : Type} {γ : ι → ℂ} {σ : ι → ι} (hσ : ∀ i, γ (σ i) = conj (γ i)) (hZ : NontrivialZeroFamily γ) :
    ScaleSign (efMoment c k) ∧ ∀ F, 0 ≤ (weilSum γ σ F).re :=
  zeta_tie_in_contourShift hExt hc
    (fun m => ⟨efTest_of_smooth hc (contDiff_nat_of_smooth (hk m)) (hks m),
      efTest_of_smooth hc (contDiff_refl (contDiff_nat_of_smooth (hk m))) (hasCompactSupport_refl (hks m))⟩)
    hK (fun m => contourShift_EF hc (contDiff_nat_of_smooth (hk m)) (hks m)) hσ hZ

end ProofPhase.GRH.CSTie
