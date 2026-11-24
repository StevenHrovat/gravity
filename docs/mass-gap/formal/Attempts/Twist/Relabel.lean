/-
Twist route, attempt round (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/twist/NOTE.md`, section 2 (Proposition T2, the relabelling identity).
-/

import OneScale.Product

/-!
# Relabelling a boundary change by a measure-preserving map (the vortex representation)

Setting of `OneScale.Product`: `π = ν^{⊗ι}`, a local weight `W` and the block specification `q^σ = locSpec ν B W σ`.
For two boundary conditions `σ, σ'` and any `π`-preserving map `T` of configurations (in the application: the centre twist
`twistAt c S'` of a set `S'` of block links, which preserves the product Haar measure),

  `q^{σ'}(F) = q^σ((F ∘ T) · R) / q^σ(R)`,   `R ξ = W(σ'|T ξ) / W(σ|ξ)`          (`relabel`).

In the gauge application with `σ' = σ` twisted at one shell link `z` and `T = twistAt c S'`, `S' ⊆ B`, the ratio `R` is a
product over the plaquettes that pass `S' ∪ {z}` a nonzero net number of times (the vortex sheet bounded at `z`): every other
plaquette factor cancels by `AreaLaw.Twist.plaquetteHolonomy_twistAt_of_zero`. So a central boundary change at `z` equals
the insertion of a vortex sheet, which may be moved anywhere inside the block at the price of composing `F` with `T`.

`relabel_response_le`: if `F ∘ T = F` (e.g. `F` does not read `S'`) and `|F - a| ≤ M`, then
`|q^{σ'}(F) - q^σ(F)| ≤ M · q^σ(|R / q^σ(R) - 1|)`: the response is bounded by the `L¹` fluctuation of the vortex weight.
-/

open MeasureTheory Finset OneScale

set_option linter.unusedSectionVars false

noncomputable section

namespace Attempts.Twist

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] {ν : Measure S} [IsProbabilityMeasure ν]
  {B : Finset ι} {W : (ι → S) → ℝ}

/-- The relabelling weight `R ξ = W(σ'|T ξ) / W(σ|ξ)`. -/
def relabelRatio (B : Finset ι) (W : (ι → S) → ℝ) (σ σ' : ι → S) (T : (ι → S) → (ι → S)) (ξ : ι → S) : ℝ :=
  W (splice B σ' (T ξ)) / W (splice B σ ξ)

section

variable (hW : LocalWeight W) {T : (ι → S) → (ι → S)} (hT : MeasurePreserving T (prodMeasure ν) (prodMeasure ν))
include hW hT

/-- `∫ g dπ = ∫ g ∘ T dπ` for bounded measurable `g`. -/
theorem integral_comp_T {g : (ι → S) → ℝ} (hg : Measurable g) :
    ∫ ξ, g (T ξ) ∂(prodMeasure ν) = ∫ ξ, g ξ ∂(prodMeasure ν) := by
  conv_rhs => rw [← hT.map_eq]
  rw [integral_map hT.measurable.aemeasurable hg.aestronglyMeasurable]

/-- `Z_B(σ) · q^σ((G ∘ T) · R) = ∫ G(T ξ) W(σ'|T ξ) dπ`. -/
theorem locZ_mul_integral_relabel (σ σ' : ι → S) (G : (ι → S) → ℝ) :
    locZ ν B W σ * ∫ ξ, G (T ξ) * relabelRatio B W σ σ' T ξ ∂(locSpec ν B W σ) =
      ∫ ξ, G (T ξ) * W (splice B σ' (T ξ)) ∂(prodMeasure ν) := by
  rw [hW.integral_locSpec, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  have h1 := (hW.locZ_pos (ν := ν) (B := B) σ).ne'
  have h2 := (hW.pos (splice B σ ξ)).ne'
  simp only [relabelRatio]
  field_simp

/-- **Proposition T2 (relabelling identity).** `q^{σ'}(F) = q^σ((F ∘ T) R) / q^σ(R)`. -/
theorem relabel (σ σ' : ι → S) {F : (ι → S) → ℝ} (hF : BM F) :
    ∫ ξ, F ξ ∂(locSpec ν B W σ') =
      (∫ ξ, F (T ξ) * relabelRatio B W σ σ' T ξ ∂(locSpec ν B W σ)) /
        (∫ ξ, relabelRatio B W σ σ' T ξ ∂(locSpec ν B W σ)) := by
  have hZ := hW.locZ_pos (ν := ν) (B := B) σ
  have hZ' := hW.locZ_pos (ν := ν) (B := B) σ'
  -- numerator
  have hnum := locZ_mul_integral_relabel (B := B) hW hT σ σ' F
  have hnum' : ∫ ξ, F (T ξ) * W (splice B σ' (T ξ)) ∂(prodMeasure ν) =
      ∫ ξ, F ξ * W (splice B σ' ξ) ∂(prodMeasure ν) :=
    integral_comp_T hW hT (g := fun ξ => F ξ * W (splice B σ' ξ))
      (hF.meas.mul (hW.meas.comp (measurable_splice_right B σ')))
  -- denominator
  have hden := locZ_mul_integral_relabel (B := B) hW hT σ σ' (fun _ => (1 : ℝ))
  have hden' : ∫ ξ, (1 : ℝ) * W (splice B σ' (T ξ)) ∂(prodMeasure ν) = locZ ν B W σ' := by
    simp only [one_mul]
    exact integral_comp_T hW hT (g := fun ξ => W (splice B σ' ξ)) (hW.meas.comp (measurable_splice_right B σ'))
  simp only [one_mul] at hden hden'
  -- the target
  have hlhs : locZ ν B W σ' * ∫ ξ, F ξ ∂(locSpec ν B W σ') = ∫ ξ, F ξ * W (splice B σ' ξ) ∂(prodMeasure ν) := by
    rw [hW.integral_locSpec, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only
    field_simp
  have hden'' : ∫ ξ, relabelRatio B W σ σ' T ξ ∂(locSpec ν B W σ) = locZ ν B W σ' / locZ ν B W σ := by
    rw [eq_div_iff hZ.ne', mul_comm _ (locZ ν B W σ), hden, hden']
  have hnum'' : ∫ ξ, F (T ξ) * relabelRatio B W σ σ' T ξ ∂(locSpec ν B W σ) =
      (locZ ν B W σ' * ∫ ξ, F ξ ∂(locSpec ν B W σ')) / locZ ν B W σ := by
    rw [eq_div_iff hZ.ne', mul_comm _ (locZ ν B W σ), hnum, hnum', hlhs]
  rw [hnum'', hden'']
  have h1 := hZ.ne'
  have h2 := hZ'.ne'
  field_simp

end

/-- The relabelling weight of local weights is bounded and measurable. -/
theorem relabelRatio_bm (hW : LocalWeight W) {T : (ι → S) → (ι → S)}
    (hT : MeasurePreserving T (prodMeasure ν) (prodMeasure ν)) (σ σ' : ι → S) :
    BM (relabelRatio B W σ σ' T) := by
  obtain ⟨c, hc, hlow⟩ := hW.lower
  obtain ⟨C, hC⟩ := hW.upper
  refine ⟨(hW.meas.comp ((measurable_splice_right B σ').comp hT.measurable)).div
    (hW.meas.comp (measurable_splice_right B σ)), ⟨C / c, fun ξ => ?_⟩⟩
  unfold relabelRatio
  rw [abs_div, abs_of_pos (hW.pos _), abs_of_pos (hW.pos _)]
  exact div_le_div₀ ((hW.pos ξ).le.trans (hC ξ)) (hC _) hc (hlow _)

/-- **The response bound.** If `F ∘ T = F`, `|F - a| ≤ M` and `m = q^σ(R) > 0`, then
`|q^{σ'}(F) - q^σ(F)| ≤ M · q^σ(|R/m - 1|)`. -/
theorem relabel_response_le (hW : LocalWeight W) {T : (ι → S) → (ι → S)}
    (hT : MeasurePreserving T (prodMeasure ν) (prodMeasure ν)) (σ σ' : ι → S) {F : (ι → S) → ℝ} (hF : BM F)
    (hFT : ∀ ξ, F (T ξ) = F ξ) {a M : ℝ} (hM : ∀ ξ, |F ξ - a| ≤ M)
    (hm : 0 < ∫ ξ, relabelRatio B W σ σ' T ξ ∂(locSpec ν B W σ)) :
    |∫ ξ, F ξ ∂(locSpec ν B W σ') - ∫ ξ, F ξ ∂(locSpec ν B W σ)| ≤
      M * ∫ ξ, |relabelRatio B W σ σ' T ξ / (∫ η, relabelRatio B W σ σ' T η ∂(locSpec ν B W σ)) - 1|
        ∂(locSpec ν B W σ) := by
  have := hW.isProbabilityMeasure_locSpec (ν := ν) (B := B) σ
  have hR := relabelRatio_bm hW hT σ σ' (B := B)
  have hrel := relabel (B := B) hW hT σ σ' hF
  simp_rw [hFT] at hrel
  set q := locSpec ν B W σ
  set R := relabelRatio B W σ σ' T
  set m := ∫ η, R η ∂q
  have hFi : Integrable F q := hF.integrable q
  have hRint : Integrable R q := hR.integrable q
  have hFR : Integrable (fun ξ => F ξ * R ξ) q := (hF.mul hR).integrable q
  have hRhat : Integrable (fun ξ => R ξ / m - 1) q := (hRint.div_const m).sub (integrable_const 1)
  have hint0 : ∫ ξ, (R ξ / m - 1) ∂q = 0 := by
    rw [integral_sub (hRint.div_const m) (integrable_const 1), integral_div, div_self hm.ne']
    simp
  have hI1 : Integrable (fun ξ => F ξ * R ξ / m - F ξ) q := (hFR.div_const m).sub hFi
  have hI2 : Integrable (fun ξ => a * (R ξ / m - 1)) q := hRhat.const_mul a
  have hI3 : Integrable (fun ξ => F ξ * R ξ / m) q := hFR.div_const m
  have hA : ∫ ξ, (F ξ - a) * (R ξ / m - 1) ∂q =
      ∫ ξ, (F ξ * R ξ / m - F ξ) ∂q - ∫ ξ, a * (R ξ / m - 1) ∂q := by
    rw [← integral_sub hI1 hI2]
    congr 1; funext ξ; ring
  have hB : ∫ ξ, (F ξ * R ξ / m - F ξ) ∂q = (∫ ξ, F ξ * R ξ ∂q) / m - ∫ ξ, F ξ ∂q := by
    rw [integral_sub hI3 hFi, integral_div]
  have hC : ∫ ξ, a * (R ξ / m - 1) ∂q = 0 := by rw [integral_const_mul, hint0, mul_zero]
  have hkey : ∫ ξ, F ξ ∂(locSpec ν B W σ') - ∫ ξ, F ξ ∂q = ∫ ξ, (F ξ - a) * (R ξ / m - 1) ∂q := by
    rw [hrel, hA, hB, hC]; ring
  rw [hkey]
  calc |∫ ξ, (F ξ - a) * (R ξ / m - 1) ∂q| ≤ ∫ ξ, |(F ξ - a) * (R ξ / m - 1)| ∂q := abs_integral_le_integral_abs
    _ ≤ ∫ ξ, M * |R ξ / m - 1| ∂q := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (hRhat.abs.const_mul M) (Filter.Eventually.of_forall fun ξ => ?_)
        simp only [abs_mul]
        exact mul_le_mul_of_nonneg_right (hM ξ) (abs_nonneg _)
    _ = M * ∫ ξ, |R ξ / m - 1| ∂q := integral_const_mul _ _

end Attempts.Twist
