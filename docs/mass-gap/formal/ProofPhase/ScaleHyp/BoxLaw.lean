/-
Proof phase, ScaleHyp kit, module 3: box laws from a joint density (2026-11-23). Released under Apache 2.0.

Pack: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/PACK-SCALEHYP.md`, item (d), with pitfall 3 (the fibre
reference measure, `UV-TV.md` 39.4).
Note: `docs/mass-gap/weak-coupling/proof-phase/scalehyp/NOTE.md`.
-/

import ProofPhase.ScaleHyp.KernelCoupling

/-!
# Box laws from a joint density

Configurations `ι → S`; a block is a `Finset ι` of whole sites (pitfall 2). The global law is `μ = F Λ₀`, a density
`F` against a reference measure `Λ₀` on configurations.

**The reference measure (pitfall 3).** The box variables live on a fibre of the coarse data, so `Λ₀` is not a product
of single-site measures. What the box law needs is only that `Λ₀` **splits along the block** `B`: there is a
probability measure `Λ` (the block reference) such that gluing the `B`-part of a `Λ`-sample to the rest of an
independent `Λ₀`-sample gives `Λ₀` again (`IsSplit Λ Λ₀ B`). For the fibre and gauge-slice reference measure of
`UV-TV.md` 39.4 this holds when `B` is a union of whole `L`-blocks, since the fibre constraints are per `L`-block;
`isSplit_pi` proves it for product measures, `Λ = Λ₀ = Measure.pi ν`.

* `glue B η σ`: `η` on `B`, `σ` off `B`.
* `boxZ Λ F B σ = ∫ F(glue B η σ) dΛ(η)`: the partition function of the block given `σ` off `B`.
* `condDens Λ F B σ η = F(glue B η σ) / boxZ σ`, set to the fixed density `1` where `boxZ σ` is `0` or `∞`
  (`UV-TV.md` 38.5 (3): "set to a fixed density where the denominator vanishes"). It is a probability density for
  every `σ` (`lintegral_condDens`).
* `boxLaw Λ F B`: the Markov kernel `σ ↦ law of glue B η σ`, `η ~ condDens σ · Λ`.
* `boxLaw_local`: it keeps every site off `B` (`q_local`).
* `boxLaw_dlr`: **DLR**, `μ.bind (boxLaw Λ F B) = μ`, for `μ = F Λ₀` with `∫ F dΛ₀ = 1` and `IsSplit Λ Λ₀ B`. The
  fallback density is used only on a `μ`-null set: `boxZ = ∞` is `Λ₀`-null since `∫ boxZ dΛ₀ = 1`, and where
  `boxZ = 0` the integrand vanishes.
-/

open MeasureTheory ProbabilityTheory Set Function

open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.ScaleHypKit

variable {ι S : Type*} [DecidableEq ι] [MeasurableSpace S]

/-! ### Gluing configurations -/

/-- `glue B η σ`: `η` on the block `B`, `σ` off it. -/
def glue (B : Finset ι) (η σ : ι → S) : ι → S := fun i => if i ∈ B then η i else σ i

theorem glue_of_mem {B : Finset ι} {η σ : ι → S} {i : ι} (h : i ∈ B) : glue B η σ i = η i := by simp [glue, h]

theorem glue_of_notMem {B : Finset ι} {η σ : ι → S} {i : ι} (h : i ∉ B) : glue B η σ i = σ i := by simp [glue, h]

theorem glue_glue_right (B : Finset ι) (η a c : ι → S) : glue B η (glue B a c) = glue B η c := by
  funext i
  by_cases h : i ∈ B <;> simp [glue, h]

theorem measurable_glue (B : Finset ι) : Measurable fun p : (ι → S) × (ι → S) => glue B p.1 p.2 := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases h : i ∈ B
  · simp only [glue, h, ite_true]; exact (measurable_pi_apply i).comp measurable_fst
  · simp only [glue, h, ite_false]; exact (measurable_pi_apply i).comp measurable_snd

theorem measurable_glue_left (B : Finset ι) (σ : ι → S) : Measurable fun η => glue B η σ :=
  (measurable_glue B).comp (measurable_id.prodMk measurable_const)

theorem measurable_glue_swap (B : Finset ι) : Measurable (uncurry fun (σ η : ι → S) => glue B η σ) :=
  (measurable_glue B).comp measurable_swap

/-! ### The splitting property of the reference measure -/

/-- **`Λ₀` splits along `B` with block reference `Λ`**: gluing the `B`-part of a `Λ`-sample to the rest of an
independent `Λ₀`-sample gives `Λ₀`. -/
def IsSplit (Λ Λ₀ : Measure (ι → S)) (B : Finset ι) : Prop :=
  (Λ.prod Λ₀).map (fun p => glue B p.1 p.2) = Λ₀

/-- Integration against a split reference: first the block part, then the rest. -/
theorem lintegral_split {Λ Λ₀ : Measure (ι → S)} [SFinite Λ] [SFinite Λ₀] {B : Finset ι} (h : IsSplit Λ Λ₀ B)
    {G : (ι → S) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ σ, G σ ∂Λ₀ = ∫⁻ c, ∫⁻ a, G (glue B a c) ∂Λ ∂Λ₀ := by
  conv_lhs => rw [← h]
  rw [lintegral_map hG (measurable_glue B),
    lintegral_prod_symm (fun p => G (glue B p.1 p.2)) (hG.comp (measurable_glue B)).aemeasurable]

/-- **Product measures split along every block.** -/
theorem isSplit_pi [Fintype ι] (ν : ι → Measure S) [∀ i, IsProbabilityMeasure (ν i)] (B : Finset ι) :
    IsSplit (Measure.pi ν) (Measure.pi ν) B := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hpre : (fun p : (ι → S) × (ι → S) => glue B p.1 p.2) ⁻¹' univ.pi s =
      (univ.pi fun i => if i ∈ B then s i else univ) ×ˢ (univ.pi fun i => if i ∈ B then univ else s i) := by
    ext p
    simp only [mem_preimage, mem_pi, mem_univ, forall_const, mem_prod]
    constructor
    · intro h
      constructor
      · intro i
        by_cases hi : i ∈ B
        · simpa [glue, hi] using h i
        · simp [hi]
      · intro i
        by_cases hi : i ∈ B
        · simp [hi]
        · simpa [glue, hi] using h i
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i ∈ B
      · simpa [glue, hi] using h1 i
      · simpa [glue, hi] using h2 i
  have hms : ∀ (t : Finset ι) (u v : ∀ i, Set S), (∀ i, MeasurableSet (u i)) → (∀ i, MeasurableSet (v i)) →
      ∀ i, MeasurableSet (if i ∈ t then u i else v i) := fun t u v hu hv i => by
    by_cases hi : i ∈ t <;> simp [hi, hu i, hv i]
  rw [Measure.map_apply (measurable_glue B) (MeasurableSet.univ_pi hs), hpre, Measure.prod_prod,
    Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ B <;> simp [hi]

/-! ### The partition function and the conditional density -/

variable (Λ : Measure (ι → S)) (F : (ι → S) → ℝ≥0∞) (B : Finset ι)

/-- The partition function of the block `B` given `σ` off `B`. -/
def boxZ (σ : ι → S) : ℝ≥0∞ := ∫⁻ η, F (glue B η σ) ∂Λ

open Classical in
/-- **The conditional density** of the block given `σ` off `B`, against the block reference `Λ`; the fixed density
`1` where the partition function is `0` or `∞`. -/
def condDens (σ η : ι → S) : ℝ≥0∞ :=
  if boxZ Λ F B σ ≠ 0 ∧ boxZ Λ F B σ ≠ ∞ then F (glue B η σ) * (boxZ Λ F B σ)⁻¹ else 1

variable {Λ F B}

theorem boxZ_glue (a c : ι → S) : boxZ Λ F B (glue B a c) = boxZ Λ F B c := by
  simp only [boxZ, glue_glue_right]

theorem condDens_glue (a c : ι → S) : condDens Λ F B (glue B a c) = condDens Λ F B c := by
  funext η
  simp only [condDens, boxZ_glue, glue_glue_right]

theorem condDens_of_good {σ : ι → S} (h : boxZ Λ F B σ ≠ 0 ∧ boxZ Λ F B σ ≠ ∞) :
    condDens Λ F B σ = fun η => F (glue B η σ) * (boxZ Λ F B σ)⁻¹ := by
  funext η
  simp only [condDens, h, ne_eq, not_false_eq_true, and_self, ite_true]

theorem measurable_boxZ [SFinite Λ] (hF : Measurable F) : Measurable (boxZ Λ F B) :=
  Measurable.lintegral_prod_right' (ν := Λ) (f := fun p : (ι → S) × (ι → S) => F (glue B p.2 p.1))
    (hF.comp (measurable_glue_swap B))

theorem measurable_condDens [SFinite Λ] (hF : Measurable F) : Measurable (uncurry (condDens Λ F B)) := by
  have hZ : Measurable fun p : (ι → S) × (ι → S) => boxZ Λ F B p.1 := (measurable_boxZ hF).comp measurable_fst
  have hset : MeasurableSet {p : (ι → S) × (ι → S) | boxZ Λ F B p.1 ≠ 0 ∧ boxZ Λ F B p.1 ≠ ∞} :=
    (hZ (measurableSet_singleton 0).compl).inter (hZ (measurableSet_singleton ∞).compl)
  exact Measurable.ite hset ((hF.comp (measurable_glue_swap B)).mul hZ.inv) measurable_const

/-- **The conditional density is a probability density** for every `σ`. -/
theorem lintegral_condDens [IsProbabilityMeasure Λ] (hF : Measurable F) (σ : ι → S) :
    ∫⁻ η, condDens Λ F B σ η ∂Λ = 1 := by
  by_cases h : boxZ Λ F B σ ≠ 0 ∧ boxZ Λ F B σ ≠ ∞
  · have hm : Measurable fun η => F (glue B η σ) := hF.comp (measurable_glue_left B σ)
    rw [condDens_of_good h, lintegral_mul_const _ hm]
    exact ENNReal.mul_inv_cancel h.1 h.2
  · simp only [condDens, h, ite_false, lintegral_const, measure_univ, mul_one]

/-! ### The box law -/

/-- **The box law**: `σ ↦` the law of `glue B η σ` with `η ~ condDens σ · Λ`. -/
def boxLaw (Λ : Measure (ι → S)) [SFinite Λ] (F : (ι → S) → ℝ≥0∞) (B : Finset ι) : Kernel (ι → S) (ι → S) :=
  mapParam (Kernel.withDensity (Kernel.const _ Λ) (condDens Λ F B)) (fun σ η => glue B η σ)

theorem isMarkovKernel_condDensKernel [IsProbabilityMeasure Λ] (hF : Measurable F) :
    IsMarkovKernel (Kernel.withDensity (Kernel.const (ι → S) Λ) (condDens Λ F B)) :=
  ⟨fun σ => by
    rw [Kernel.withDensity_apply _ (measurable_condDens hF), Kernel.const_apply]
    exact ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_condDens hF]⟩⟩

theorem boxLaw_apply [IsProbabilityMeasure Λ] (hF : Measurable F) (σ : ι → S) :
    boxLaw Λ F B σ = (Λ.withDensity (condDens Λ F B σ)).map (fun η => glue B η σ) := by
  have := isMarkovKernel_condDensKernel (Λ := Λ) (F := F) (B := B) hF
  rw [boxLaw, mapParam_apply _ (measurable_glue_swap B), Kernel.withDensity_apply _ (measurable_condDens hF),
    Kernel.const_apply]

theorem isMarkovKernel_boxLaw [IsProbabilityMeasure Λ] (hF : Measurable F) : IsMarkovKernel (boxLaw Λ F B) := by
  have := isMarkovKernel_condDensKernel (Λ := Λ) (F := F) (B := B) hF
  exact isMarkovKernel_mapParam _ (measurable_glue_swap B)

theorem boxLaw_apply_set [IsProbabilityMeasure Λ] (hF : Measurable F) (σ : ι → S) {s : Set (ι → S)}
    (hs : MeasurableSet s) :
    boxLaw Λ F B σ s = ∫⁻ η in (fun η => glue B η σ) ⁻¹' s, condDens Λ F B σ η ∂Λ := by
  rw [boxLaw_apply hF, Measure.map_apply (measurable_glue_left B σ) hs,
    withDensity_apply _ (measurable_glue_left B σ hs)]

/-- The box law depends on `σ` only off `B`. -/
theorem boxLaw_glue [IsProbabilityMeasure Λ] (hF : Measurable F) (a c : ι → S) :
    boxLaw Λ F B (glue B a c) = boxLaw Λ F B c := by
  rw [boxLaw_apply hF, boxLaw_apply hF, condDens_glue]
  congr 1
  funext η
  exact glue_glue_right B η a c

/-- **(S) locality**: the box law keeps every site off the block. -/
theorem boxLaw_local [MeasurableEq S] [IsProbabilityMeasure Λ] (hF : Measurable F) (σ : ι → S) {x : ι}
    (hx : x ∉ B) : ∀ᵐ ξ ∂(boxLaw Λ F B σ), ξ x = σ x := by
  rw [boxLaw_apply hF, ae_map_iff (measurable_glue_left B σ).aemeasurable
    (measurableSet_eq_fun (measurable_pi_apply x) measurable_const)]
  exact ae_of_all _ fun η => glue_of_notMem hx

/-- **(S) DLR**: `μ.bind (boxLaw Λ F B) = μ` for `μ = F Λ₀`, when `Λ₀` splits along `B` with block reference `Λ`. -/
theorem boxLaw_dlr [IsProbabilityMeasure Λ] {Λ₀ : Measure (ι → S)} [SFinite Λ₀] (hF : Measurable F)
    (hF1 : ∫⁻ σ, F σ ∂Λ₀ = 1) (hsplit : IsSplit Λ Λ₀ B) :
    (Λ₀.withDensity F).bind (boxLaw Λ F B) = Λ₀.withDensity F := by
  have := isMarkovKernel_boxLaw (Λ := Λ) (F := F) (B := B) hF
  ext s hs
  have hZ : Measurable (boxZ Λ F B) := measurable_boxZ hF
  have hh : Measurable fun σ => boxLaw Λ F B σ s := Kernel.measurable_coe _ hs
  have hm : ∀ c : ι → S, Measurable fun η => F (glue B η c) := fun c => hF.comp (measurable_glue_left B c)
  have hpre : ∀ c : ι → S, MeasurableSet ((fun η => glue B η c) ⁻¹' s) := fun c => measurable_glue_left B c hs
  -- `boxZ < ∞` almost everywhere, since `∫ boxZ dΛ₀ = ∫ F dΛ₀ = 1`
  have hZint : ∫⁻ c, boxZ Λ F B c ∂Λ₀ = 1 := by rw [← hF1, lintegral_split hsplit hF]; rfl
  have hZfin : ∀ᵐ c ∂Λ₀, boxZ Λ F B c < ∞ := ae_lt_top hZ (by rw [hZint]; exact ENNReal.one_ne_top)
  -- the pointwise identity `Z c · q c s = ∫_{glue · c ∈ s} F(glue η c) dΛ`
  have hpt : ∀ᵐ c ∂Λ₀, boxZ Λ F B c * boxLaw Λ F B c s =
      ∫⁻ η in (fun η => glue B η c) ⁻¹' s, F (glue B η c) ∂Λ := by
    filter_upwards [hZfin] with c hc
    by_cases h0 : boxZ Λ F B c = 0
    · have hJ : ∫⁻ η in (fun η => glue B η c) ⁻¹' s, F (glue B η c) ∂Λ = 0 :=
        le_antisymm ((setLIntegral_le_lintegral _ _).trans h0.le) zero_le
      rw [h0, zero_mul, hJ]
    · rw [boxLaw_apply_set hF c hs, condDens_of_good ⟨h0, hc.ne⟩,
        lintegral_mul_const _ (hm c), mul_comm, mul_assoc,
        ENNReal.inv_mul_cancel h0 hc.ne, mul_one]
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), lintegral_withDensity_eq_lintegral_mul _ hF hh]
  calc ∫⁻ σ, (F * fun σ => boxLaw Λ F B σ s) σ ∂Λ₀
      = ∫⁻ c, ∫⁻ a, F (glue B a c) * boxLaw Λ F B (glue B a c) s ∂Λ ∂Λ₀ :=
        lintegral_split hsplit (hF.mul hh)
    _ = ∫⁻ c, boxZ Λ F B c * boxLaw Λ F B c s ∂Λ₀ := by
        refine lintegral_congr fun c => ?_
        simp_rw [boxLaw_glue hF]
        exact lintegral_mul_const _ (hm c)
    _ = ∫⁻ c, ∫⁻ η in (fun η => glue B η c) ⁻¹' s, F (glue B η c) ∂Λ ∂Λ₀ := lintegral_congr_ae hpt
    _ = ∫⁻ c, ∫⁻ a, s.indicator F (glue B a c) ∂Λ ∂Λ₀ := by
        refine lintegral_congr fun c => ?_
        rw [← lintegral_indicator (hpre c)]
        refine lintegral_congr fun a => ?_
        exact indicator_comp_right (fun η => glue B η c)
    _ = ∫⁻ σ, s.indicator F σ ∂Λ₀ := (lintegral_split hsplit (hF.indicator hs)).symm
    _ = Λ₀.withDensity F s := by rw [withDensity_apply _ hs, lintegral_indicator hs]

end ProofPhase.ScaleHypKit
