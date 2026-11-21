/-
The one-scale reduction (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/PROOF-NOTE.md`, Lemma 2.4 (oscillation against total variation).
-/

import Influence.Gibbs

/-!
# Oscillation against total variation (Lemma 2.4, density form)

* `integral_sub_le_osc_mul_tv`: for measures `μᵢ = gᵢ ρ` with densities of equal mass and a bounded measurable `F` with
  `F x - F y ≤ D`: `μ₁ F - μ₂ F ≤ D · tv(μ₁, μ₂)`, with `Influence.tv`.
* `abs_integral_sub_le_of_tv`: the two-sided form `|μ₁ F - μ₂ F| ≤ D t` when both `tv(μ₁, μ₂)` and `tv(μ₂, μ₁)` are
  at most `t`.
* `abs_integral_gibbs_sub_le`: the same for two Gibbs measures `Influence.gibbs ν φᵢ`.

The proof avoids the layer-cake formula: with `m = inf F` and `A = {g₁ > g₂}`,
`μ₁ F - μ₂ F = ∫ (g₁ - g₂)(F - m) dρ ≤ D ∫_A (g₁ - g₂) dρ = D (μ₁(A) - μ₂(A))`. Standard; formalised here.
-/

open MeasureTheory Influence

noncomputable section

namespace OneScale

variable {α : Type*} [MeasurableSpace α]

/-- `μ(A) = ∫_A g dρ` for `μ = g ρ`, `g ≥ 0` integrable. -/
theorem measureReal_withDensity_ofReal (ρ : Measure α) {g : α → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hi : Integrable g ρ) {A : Set α} (hA : MeasurableSet A) :
    (ρ.withDensity fun x => ENNReal.ofReal (g x)).real A = ∫ x in A, g x ∂ρ := by
  rw [measureReal_def, withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (Filter.Eventually.of_forall hg0),
    ENNReal.toReal_ofReal (setIntegral_nonneg hA fun x _ => hg0 x)]

theorem integral_withDensity_ofReal (ρ : Measure α) {g : α → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (F : α → ℝ) : ∫ x, F x ∂(ρ.withDensity fun x => ENNReal.ofReal (g x)) = ∫ x, g x * F x ∂ρ := by
  rw [integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hg0 x)]

/-- **Lemma 2.4, one-sided density form.** -/
theorem integral_sub_le_osc_mul_tv (ρ : Measure α) {g₁ g₂ : α → ℝ} (hg₁ : Measurable g₁)
    (hg₂ : Measurable g₂) (h₁ : ∀ x, 0 ≤ g₁ x) (h₂ : ∀ x, 0 ≤ g₂ x) (hi₁ : Integrable g₁ ρ)
    (hi₂ : Integrable g₂ ρ) (hone : ∫ x, g₁ x ∂ρ = ∫ x, g₂ x ∂ρ) {F : α → ℝ} (hF : Measurable F) {C : ℝ}
    (hFC : ∀ x, |F x| ≤ C) {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ x y, F x - F y ≤ D) :
    ∫ x, F x ∂(ρ.withDensity fun x => ENNReal.ofReal (g₁ x)) -
        ∫ x, F x ∂(ρ.withDensity fun x => ENNReal.ofReal (g₂ x)) ≤
      D * tv (ρ.withDensity fun x => ENNReal.ofReal (g₁ x)) (ρ.withDensity fun x => ENNReal.ofReal (g₂ x)) := by
  set μ₁ := ρ.withDensity fun x => ENNReal.ofReal (g₁ x)
  set μ₂ := ρ.withDensity fun x => ENNReal.ofReal (g₂ x)
  have : IsFiniteMeasure μ₁ := isFiniteMeasure_withDensity_ofReal hi₁.hasFiniteIntegral
  rcases isEmpty_or_nonempty α with hα | hα
  · simp only [integral_of_isEmpty, sub_self]
    exact mul_nonneg hD0 (tv_nonneg _ _)
  have hbdd : BddBelow (Set.range F) := ⟨-C, by
    rintro _ ⟨x, rfl⟩
    exact neg_le_of_abs_le (hFC x)⟩
  set m := ⨅ x, F x
  have hm1 : ∀ x, m ≤ F x := fun x => ciInf_le hbdd x
  have hm2 : ∀ x, F x - m ≤ D := by
    intro x
    have : F x - D ≤ m := le_ciInf fun y => by linarith [hD x y]
    linarith
  have hFae : AEStronglyMeasurable F ρ := hF.aestronglyMeasurable
  have hFb : ∀ᵐ x ∂ρ, ‖F x‖ ≤ C := Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hFC x
  have hgF₁ : Integrable (fun x => g₁ x * F x) ρ := by
    simpa [mul_comm] using hi₁.bdd_mul hFae hFb
  have hgF₂ : Integrable (fun x => g₂ x * F x) ρ := by
    simpa [mul_comm] using hi₂.bdd_mul hFae hFb
  have hFm : AEStronglyMeasurable (fun x => F x - m) ρ := (hF.sub measurable_const).aestronglyMeasurable
  have hFmb : ∀ᵐ x ∂ρ, ‖F x - m‖ ≤ D := Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hm1 x])]; exact hm2 x
  have hint : Integrable (fun x => (g₁ x - g₂ x) * (F x - m)) ρ := by
    simpa [mul_comm] using (hi₁.sub hi₂).bdd_mul hFm hFmb
  rw [integral_withDensity_ofReal ρ hg₁ h₁, integral_withDensity_ofReal ρ hg₂ h₂]
  -- `μ₁ F - μ₂ F = ∫ (g₁ - g₂)(F - m)`
  have hdiff : ∫ x, g₁ x * F x ∂ρ - ∫ x, g₂ x * F x ∂ρ = ∫ x, (g₁ x - g₂ x) * (F x - m) ∂ρ := by
    have e : ∀ x, (g₁ x - g₂ x) * (F x - m) = (g₁ x * F x - g₂ x * F x) - m * (g₁ x - g₂ x) := by
      intro x; ring
    simp_rw [e]
    rw [integral_sub (show Integrable (fun x => g₁ x * F x - g₂ x * F x) ρ from hgF₁.sub hgF₂)
      (show Integrable (fun x => m * (g₁ x - g₂ x)) ρ from (hi₁.sub hi₂).const_mul m), integral_sub hgF₁ hgF₂,
      integral_const_mul, integral_sub hi₁ hi₂, hone, sub_self, mul_zero, sub_zero]
  rw [hdiff]
  set A := {x | g₂ x < g₁ x}
  have hA : MeasurableSet A := measurableSet_lt hg₂ hg₁
  have hpt : ∀ x, (g₁ x - g₂ x) * (F x - m) ≤ A.indicator (fun x => D * (g₁ x - g₂ x)) x := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      have : 0 < g₁ x - g₂ x := by simp only [A, Set.mem_ofPred_eq] at hx; linarith
      rw [mul_comm D]
      exact mul_le_mul_of_nonneg_left (hm2 x) this.le
    · rw [Set.indicator_of_notMem hx]
      have : g₁ x - g₂ x ≤ 0 := by simp only [A, Set.mem_ofPred_eq, not_lt] at hx; linarith
      exact mul_nonpos_of_nonpos_of_nonneg this (by linarith [hm1 x])
  have hindint : Integrable (A.indicator fun x => D * (g₁ x - g₂ x)) ρ :=
    ((hi₁.sub hi₂).const_mul D).indicator hA
  calc ∫ x, (g₁ x - g₂ x) * (F x - m) ∂ρ ≤ ∫ x, A.indicator (fun x => D * (g₁ x - g₂ x)) x ∂ρ :=
        integral_mono hint hindint hpt
    _ = D * (μ₁.real A - μ₂.real A) := by
        rw [integral_indicator hA, integral_const_mul, integral_sub hi₁.integrableOn hi₂.integrableOn,
          measureReal_withDensity_ofReal ρ h₁ hi₁ hA, measureReal_withDensity_ofReal ρ h₂ hi₂ hA]
    _ ≤ D * tv μ₁ μ₂ := mul_le_mul_of_nonneg_left (le_tv μ₁ μ₂ hA) hD0

/-- **Lemma 2.4, two-sided density form.** -/
theorem abs_integral_sub_le_of_tv (ρ : Measure α) {g₁ g₂ : α → ℝ} (hg₁ : Measurable g₁)
    (hg₂ : Measurable g₂) (h₁ : ∀ x, 0 ≤ g₁ x) (h₂ : ∀ x, 0 ≤ g₂ x) (hi₁ : Integrable g₁ ρ)
    (hi₂ : Integrable g₂ ρ) (hone : ∫ x, g₁ x ∂ρ = ∫ x, g₂ x ∂ρ) {F : α → ℝ} (hF : Measurable F) {C : ℝ}
    (hFC : ∀ x, |F x| ≤ C) {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ x y, F x - F y ≤ D) {t : ℝ}
    (ht₁ : tv (ρ.withDensity fun x => ENNReal.ofReal (g₁ x)) (ρ.withDensity fun x => ENNReal.ofReal (g₂ x)) ≤ t)
    (ht₂ : tv (ρ.withDensity fun x => ENNReal.ofReal (g₂ x)) (ρ.withDensity fun x => ENNReal.ofReal (g₁ x)) ≤ t) :
    |∫ x, F x ∂(ρ.withDensity fun x => ENNReal.ofReal (g₁ x)) -
        ∫ x, F x ∂(ρ.withDensity fun x => ENNReal.ofReal (g₂ x))| ≤ D * t := by
  rw [abs_le]
  constructor
  · have := integral_sub_le_osc_mul_tv ρ hg₂ hg₁ h₂ h₁ hi₂ hi₁ hone.symm hF hFC hD0 hD
    have := mul_le_mul_of_nonneg_left ht₂ hD0
    linarith
  · have := integral_sub_le_osc_mul_tv ρ hg₁ hg₂ h₁ h₂ hi₁ hi₂ hone hF hFC hD0 hD
    have := mul_le_mul_of_nonneg_left ht₁ hD0
    linarith

/-- **Lemma 2.4 for Gibbs measures.** For `μᵢ = gibbs ν φᵢ` with bounded measurable log-weights, a bounded
measurable `F` with `F x - F y ≤ D`, and `tv` at most `t` in both orders: `|μ₁ F - μ₂ F| ≤ D t`. -/
theorem abs_integral_gibbs_sub_le (ν : Measure α) [IsProbabilityMeasure ν] {φ₁ φ₂ : α → ℝ}
    (hφ₁ : Measurable φ₁) (hφ₂ : Measurable φ₂) {K₁ K₂ : ℝ} (hK₁ : ∀ x, |φ₁ x| ≤ K₁) (hK₂ : ∀ x, |φ₂ x| ≤ K₂)
    {F : α → ℝ} (hF : Measurable F) {C : ℝ} (hFC : ∀ x, |F x| ≤ C) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ x y, F x - F y ≤ D) {t : ℝ} (ht₁ : tv (gibbs ν φ₁) (gibbs ν φ₂) ≤ t)
    (ht₂ : tv (gibbs ν φ₂) (gibbs ν φ₁) ≤ t) :
    |∫ x, F x ∂(gibbs ν φ₁) - ∫ x, F x ∂(gibbs ν φ₂)| ≤ D * t := by
  have hZ₁ := partitionFn_pos ν hφ₁ hK₁
  have hZ₂ := partitionFn_pos ν hφ₂ hK₂
  have hone : ∀ (φ : α → ℝ), 0 < partitionFn ν φ →
      ∫ x, Real.exp (φ x) / partitionFn ν φ ∂ν = 1 := by
    intro φ hZ
    rw [integral_div]
    exact div_self hZ.ne'
  exact abs_integral_sub_le_of_tv ν (hφ₁.exp.div_const _) (hφ₂.exp.div_const _)
    (fun x => div_nonneg (Real.exp_pos _).le hZ₁.le) (fun x => div_nonneg (Real.exp_pos _).le hZ₂.le)
    ((integrable_exp_of_bdd ν hφ₁ hK₁).div_const _) ((integrable_exp_of_bdd ν hφ₂ hK₂).div_const _)
    (by rw [hone φ₁ hZ₁, hone φ₂ hZ₂]) hF hFC hD0 hD ht₁ ht₂

end OneScale
