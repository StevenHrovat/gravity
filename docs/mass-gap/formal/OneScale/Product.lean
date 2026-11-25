/-
The one-scale reduction, measure layer (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/PROOF-NOTE.md`, §1.3, §1.4 and Lemma 2.1 (factorisation and DLR).
-/

import OneScale.Blocks

/-!
# Product measures with a factorised density: specifications and the DLR identity

Setting: a probability measure `ν` on the single-coordinate space `S`, the product measure `π = ν^{⊗ι}` on
configurations, and a measure `μ = Z⁻¹ W π` with a bounded measurable density `W ≥ 0`.

* `measurePreserving_splice`: if `σ, ξ` are independent with law `π`, then `splice B σ ξ` has law `π`.
* `integral_splice`: `∫ F dπ = ∫ σ, ∫ ξ, F (splice B σ ξ) dπ dπ` (Fubini for the split `ι = (ι ∖ B) ⊔ B`).
* `locSpec ν B W_B σ`: the specification `q_B^σ(dξ) = W_B(splice B σ ξ) / Z_B(σ) π(dξ)` of a block with local weight
  `W_B` (bounded measurable, bounded below by a positive constant).
* `dlr_locSpec`: **Lemma 2.1 (DLR)**: if `W = W_B · R` where `R` does not read the block, then `μ(P_B h) = μ(h)`.
* `productBlockSpec`: a `BlockSpec` for `μ` from such factorisations, one per block.

Standard (Fubini, conditional densities); formalised here from scratch.
-/

open MeasureTheory Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace OneScale

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]

/-- The product measure `π = ν^{⊗ι}`. -/
abbrev prodMeasure : Measure (ι → S) := Measure.pi (fun _ : ι => ν)

/-- Splicing two independent `π`-distributed configurations gives a `π`-distributed configuration. -/
theorem measurePreserving_splice (B : Finset ι) :
    MeasurePreserving (fun p : (ι → S) × (ι → S) => splice B p.1 p.2)
      ((prodMeasure ν).prod (prodMeasure ν)) (prodMeasure (ι := ι) ν) := by
  refine ⟨measurable_splice B, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (measurable_splice B) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → S) × (ι → S) => splice B p.1 p.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => if i ∈ B then Set.univ else s i) ×ˢ
        Set.univ.pi (fun i => if i ∈ B then s i else Set.univ) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, splice]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩ <;> by_cases hi : i ∈ B <;> simp only [hi, ite_true, ite_false,
        Set.mem_univ] <;> simpa [hi] using h i
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i ∈ B
      · simpa [hi] using h2 i
      · simpa [hi] using h1 i
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ B <;> simp [hi]

/-- **Fubini along a block.** `∫ F dπ = ∫ σ, ∫ ξ, F (splice B σ ξ) dπ dπ`. -/
theorem integral_splice (B : Finset ι) {F : (ι → S) → ℝ} (hF : Integrable F (prodMeasure ν)) :
    ∫ σ, ∫ ξ, F (splice B σ ξ) ∂(prodMeasure ν) ∂(prodMeasure ν) = ∫ σ, F σ ∂(prodMeasure ν) := by
  have hmp := measurePreserving_splice ν B
  have hint : Integrable (F ∘ fun p : (ι → S) × (ι → S) => splice B p.1 p.2)
      ((prodMeasure ν).prod (prodMeasure ν)) :=
    (hmp.integrable_comp hF.aestronglyMeasurable).2 hF
  rw [← integral_prod (fun p : (ι → S) × (ι → S) => F (splice B p.1 p.2)) hint]
  conv_rhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hF.aestronglyMeasurable)]

/-- A local weight: measurable, bounded, and bounded below by a positive constant. -/
structure LocalWeight (W : (ι → S) → ℝ) : Prop where
  meas : Measurable W
  lower : ∃ c : ℝ, 0 < c ∧ ∀ σ, c ≤ W σ
  upper : ∃ C : ℝ, ∀ σ, W σ ≤ C

namespace LocalWeight

variable {W : (ι → S) → ℝ} (hW : LocalWeight W)
include hW

theorem pos (σ : ι → S) : 0 < W σ := by
  obtain ⟨c, hc, h⟩ := hW.lower
  exact hc.trans_le (h σ)

theorem bm : BM W := by
  obtain ⟨C, hC⟩ := hW.upper
  refine ⟨hW.meas, ⟨C, fun σ => ?_⟩⟩
  rw [abs_of_pos (hW.pos σ)]
  exact hC σ

end LocalWeight

/-- The local partition function `Z_B(σ) = ∫ W_B(splice B σ ξ) dπ(ξ)`. -/
def locZ (B : Finset ι) (W : (ι → S) → ℝ) (σ : ι → S) : ℝ := ∫ ξ, W (splice B σ ξ) ∂(prodMeasure ν)

/-- The block specification `q_B^σ(dξ) = W_B(splice B σ ξ) / Z_B(σ) π(dξ)`. -/
def locSpec (B : Finset ι) (W : (ι → S) → ℝ) (σ : ι → S) : Measure (ι → S) :=
  (prodMeasure ν).withDensity (fun ξ => ENNReal.ofReal (W (splice B σ ξ) / locZ ν B W σ))

variable {ν}

namespace LocalWeight

variable {B : Finset ι} {W : (ι → S) → ℝ} (hW : LocalWeight W)
include hW

theorem locZ_pos (σ : ι → S) : 0 < locZ ν B W σ := by
  obtain ⟨c, hc, h⟩ := hW.lower
  have := integral_mono (integrable_const c) (integrable_comp_splice hW.bm σ (prodMeasure ν))
    (fun ξ => h (splice B σ ξ))
  simp only [integral_const, probReal_univ, one_smul] at this
  exact hc.trans_le this

theorem measurable_locZ : Measurable (locZ ν B W) := by
  have : StronglyMeasurable (fun p : (ι → S) × (ι → S) => W (splice B p.1 p.2)) :=
    (hW.meas.comp (measurable_splice B)).stronglyMeasurable
  exact (this.integral_prod_right' (ν := prodMeasure ν)).measurable

/-- Integrals against `q_B^σ` are density integrals against `π`. -/
theorem integral_locSpec (σ : ι → S) (G : (ι → S) → ℝ) :
    ∫ ξ, G ξ ∂(locSpec ν B W σ) = ∫ ξ, (W (splice B σ ξ) / locZ ν B W σ) * G ξ ∂(prodMeasure ν) := by
  unfold locSpec
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun ξ => ENNReal.ofReal (W (splice B σ ξ) / locZ ν B W σ))
    ((hW.meas.comp (measurable_splice_right B σ)).div_const _).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (hW.pos _).le (hW.locZ_pos σ).le)]

theorem isProbabilityMeasure_locSpec (σ : ι → S) : IsProbabilityMeasure (locSpec ν B W σ) := by
  constructor
  have hZ := hW.locZ_pos (ν := ν) (B := B) σ
  have hint : Integrable (fun ξ => W (splice B σ ξ) / locZ ν B W σ) (prodMeasure ν) :=
    (integrable_comp_splice hW.bm σ _).div_const _
  unfold locSpec
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ξ => div_nonneg (hW.pos _).le hZ.le), integral_div]
  rw [show ∫ ξ, W (splice B σ ξ) ∂(prodMeasure ν) = locZ ν B W σ from rfl, div_self hZ.ne',
    ENNReal.ofReal_one]

theorem locSpec_congr (σ σ' : ι → S) (h : ∀ i ∉ B, σ i = σ' i) : locSpec ν B W σ = locSpec ν B W σ' := by
  unfold locSpec locZ
  simp_rw [splice_congr_left h]

theorem blockAvg_locSpec (h : (ι → S) → ℝ) (σ : ι → S) :
    blockAvg B (locSpec ν B W) h σ =
      ∫ ξ, (W (splice B σ ξ) / locZ ν B W σ) * h (splice B σ ξ) ∂(prodMeasure ν) :=
  hW.integral_locSpec σ _

theorem measurable_blockAvg_locSpec {h : (ι → S) → ℝ} (hh : BM h) :
    Measurable (blockAvg B (locSpec ν B W) h) := by
  have e : blockAvg B (locSpec ν B W) h = fun σ =>
      ∫ ξ, (fun p : (ι → S) × (ι → S) => (W (splice B p.1 p.2) / locZ ν B W p.1) * h (splice B p.1 p.2))
        (σ, ξ) ∂(prodMeasure ν) := by
    funext σ; exact hW.blockAvg_locSpec h σ
  rw [e]
  have hm : Measurable (fun p : (ι → S) × (ι → S) =>
      (W (splice B p.1 p.2) / locZ ν B W p.1) * h (splice B p.1 p.2)) :=
    ((hW.meas.comp (measurable_splice B)).div ((hW.measurable_locZ).comp measurable_fst)).mul
      (hh.meas.comp (measurable_splice B))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := prodMeasure ν)).measurable

/-- `Z_B(σ) · P_B h(σ) = ∫ W_B(splice B σ ξ) h(splice B σ ξ) dπ(ξ)`. -/
theorem locZ_mul_blockAvg (h : (ι → S) → ℝ) (σ : ι → S) :
    locZ ν B W σ * blockAvg B (locSpec ν B W) h σ =
      ∫ ξ, W (splice B σ ξ) * h (splice B σ ξ) ∂(prodMeasure ν) := by
  rw [hW.blockAvg_locSpec, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  have := (hW.locZ_pos (ν := ν) (B := B) σ).ne'
  simp only
  field_simp

end LocalWeight

/-- The normalised measure `μ = W / Z · π`, `Z = ∫ W dπ`. -/
def weightMeasure (ν : Measure S) [IsProbabilityMeasure ν] (W : (ι → S) → ℝ) : Measure (ι → S) :=
  (prodMeasure ν).withDensity (fun σ => ENNReal.ofReal (W σ / ∫ τ, W τ ∂(prodMeasure ν)))

theorem integral_weightMeasure {W : (ι → S) → ℝ} (hW : BM W) (hW0 : ∀ σ, 0 ≤ W σ) (h : (ι → S) → ℝ) :
    ∫ σ, h σ ∂(weightMeasure ν W) = ∫ σ, (W σ / ∫ τ, W τ ∂(prodMeasure ν)) * h σ ∂(prodMeasure ν) := by
  unfold weightMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (hW.meas.div_const _).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (hW0 σ) (integral_nonneg hW0))]

theorem isProbabilityMeasure_weightMeasure {W : (ι → S) → ℝ} (hW : BM W) (hW0 : ∀ σ, 0 ≤ W σ)
    (hZ : 0 < ∫ τ, W τ ∂(prodMeasure ν)) : IsProbabilityMeasure (weightMeasure ν W) := by
  constructor
  have hint : Integrable (fun σ => W σ / ∫ τ, W τ ∂(prodMeasure ν)) (prodMeasure ν) :=
    (hW.integrable _).div_const _
  unfold weightMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun σ => div_nonneg (hW0 σ) hZ.le), integral_div, div_self hZ.ne',
    ENNReal.ofReal_one]

/-- **Lemma 2.1 (DLR) for a factorised density.** If `W = W_B · R`, `W ≥ 0`, `W_B` is a local weight and `R` is
bounded measurable and does not read the block `B`, then `μ(P_B h) = μ(h)` for `μ = W/Z · π` and every bounded
measurable `h`. -/
theorem dlr_locSpec {B : Finset ι} {WB R W : (ι → S) → ℝ} (hWB : LocalWeight WB)
    (hRB : ∀ σ ξ, R (splice B σ ξ) = R σ) (hW : ∀ σ, W σ = WB σ * R σ) (hWbm : BM W) (hW0 : ∀ σ, 0 ≤ W σ)
    {h : (ι → S) → ℝ} (hh : BM h) :
    ∫ σ, blockAvg B (locSpec ν B WB) h σ ∂(weightMeasure ν W) = ∫ σ, h σ ∂(weightMeasure ν W) := by
  set Q := blockAvg B (locSpec ν B WB) h
  have hQ : BM Q := by
    have := hWB.isProbabilityMeasure_locSpec (B := B) (ν := ν)
    obtain ⟨C, hC⟩ := hh.bdd
    exact ⟨hWB.measurable_blockAvg_locSpec hh, ⟨C, abs_blockAvg_le hC⟩⟩
  have hQB : ∀ σ ξ, Q (splice B σ ξ) = Q σ := fun σ ξ =>
    blockAvg_splice (fun σ σ' h => hWB.locSpec_congr σ σ' h) h σ ξ
  rw [integral_weightMeasure hWbm hW0, integral_weightMeasure hWbm hW0]
  set Z := ∫ τ, W τ ∂(prodMeasure ν)
  have e : ∀ F : (ι → S) → ℝ, ∫ σ, (W σ / Z) * F σ ∂(prodMeasure ν) = Z⁻¹ * ∫ σ, W σ * F σ ∂(prodMeasure ν) := by
    intro F
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    simp only; ring
  rw [e, e]
  congr 1
  have hWBbm := hWB.bm
  -- integrate out the block on the left
  have h1 : ∫ σ, W σ * Q σ ∂(prodMeasure ν) = ∫ σ, R σ * (locZ ν B WB σ * Q σ) ∂(prodMeasure ν) := by
    rw [← integral_splice ν B ((hWbm.mul hQ).integrable _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    simp only [hW, hRB, hQB]
    unfold locZ
    rw [← integral_mul_const, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only; ring
  have h2 : ∫ σ, W σ * h σ ∂(prodMeasure ν) = ∫ σ, R σ * (locZ ν B WB σ * Q σ) ∂(prodMeasure ν) := by
    rw [← integral_splice ν B ((hWbm.mul hh).integrable _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    simp only [hW, hRB]
    rw [hWB.locZ_mul_blockAvg h σ, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only; ring
  rw [h1, h2]

/-- **Block specification of a factorised product density.** For blocks `B_j` with local weights `W_j` and
complementary factors `R_j` (not reading `B_j`) such that `W = W_j R_j` for all `j`, the specifications `locSpec`
form a `BlockSpec` for `μ = W/Z · π`. -/
def productBlockSpec {J : Type*} (W : (ι → S) → ℝ) (block : J → Finset ι) (WB R : J → (ι → S) → ℝ)
    (hWB : ∀ j, LocalWeight (WB j)) (hRB : ∀ j σ ξ, R j (splice (block j) σ ξ) = R j σ)
    (hW : ∀ j σ, W σ = WB j σ * R j σ) (hWbm : BM W) (hW0 : ∀ σ, 0 ≤ W σ) :
    BlockSpec (weightMeasure ν W) J where
  block := block
  spec j := locSpec ν (block j) (WB j)
  isProb j σ := (hWB j).isProbabilityMeasure_locSpec σ
  spec_congr j σ σ' h := (hWB j).locSpec_congr σ σ' h
  meas_avg j _h hh := (hWB j).measurable_blockAvg_locSpec hh
  dlr j _h hh := dlr_locSpec (hWB j) (hRB j) (hW j) hWbm hW0 hh

end OneScale
