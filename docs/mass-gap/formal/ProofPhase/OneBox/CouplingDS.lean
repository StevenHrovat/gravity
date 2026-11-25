/-
Proof phase, M1 tools, write-out 1: the coupling-form Dobrushin-Shlosman theorem (generic layer) (2026-11-23).
Released under Apache 2.0.

Paper: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/UV-TV.md`, section 28.
Note: `docs/mass-gap/weak-coupling/proof-phase/m1-cds/NOTE.md`.
-/

import Mathlib

/-!
# The coupling-form Dobrushin-Shlosman theorem

Setting (`UV-TV.md` 28.1). A finite site set `ι`, one measurable single-site space `S`, configurations `ι → S` with the
product sigma-algebra. Two probability measures `μ, μ'` on configurations with measurable supports `Ω₀, Ω₀'` of full
measure. A finite family of blocks `B b`, `b : β`, split into good blocks (`b ∈ good`) and source blocks. For each block
there are specifications `q b, q' b` (Markov or not: only the listed properties are used) and a block coupling `Q b`.

* `CouplingSpec μ μ' β`: the supports, the blocks, the kernels `q, q', Q`, and the hypotheses (S) and (C).
* `CouplingSpec.T`: the averaged block update `T π = (1/N) Σ_b ∫ π(dp) Q_b(p, ·)`.
* `CouplingSpec.isSuppCoupling_T`: `T` maps couplings of `(μ, μ')` carried by `Ω₀ × Ω₀'` to such couplings.
* `CouplingSpec.phi_T_le`: one step, `Φ(T π) ≤ θ Φ(π) + s/N` with `θ = 1 - (1 - γ) c_min / N`.
* `CouplingSpec.iter`: the explicit iterates `π_n = T^n (μ ⊗ μ')`. They depend on `C` only.
* `CouplingSpec.DSWeights`: an admissible choice of weights (good/source split, `v`, `K`, `γ`, `c_min`, with (I) and
  (K)).
* `CouplingSpec.phi_iter_le`: for **every** admissible `W` and every `n`,
  `Φ_W(π_n) ≤ s_W/((1 - γ_W) c_min,W) + θ_W^n Φ_W(μ ⊗ μ')`; one sequence of couplings serves all weights at once.
* `CouplingSpec.exists_iter_forall_le`: for a finite family of admissible weights and `ε > 0`, one `n` such that
  `π_n` satisfies every member's bound up to `ε` (the form the union bound over sites uses).
* `couplingDS_bound`: for every `ε > 0` there is a coupling `π` of `μ, μ'` with
  `Σ_x v x * π{p | p.1 x ≠ p.2 x} ≤ s/((1 - γ) c_min) + ε`.
* `couplingDS_integral_bound`: `|∫ F dμ - ∫ F dμ'| ≤ 2 M (min_A v)⁻¹ s/((1 - γ) c_min)` for measurable `F` with
  `|F| ≤ M` that depends only on the sites in `A`.

## Simplifying choices (all stated as hypotheses, none hidden)

* **One single-site space.** All sites carry the same measurable space `S` (as in `OneScale`); site-dependent spaces
  are not needed for the application, where every site carries the same kind of variable.
* **Measurable diagonal.** `[MeasurableEq S]` (Mathlib: the diagonal of `S × S` is measurable). It holds for standard
  Borel spaces and for countable spaces with measurable singletons, so for compact groups and finite sets. This is
  REVIEW-3 Follow-up 10's Lean NIT: it makes the disagreement events `{p | p.1 x ≠ p.2 x}` measurable.
* **Measurable couplings.** The block couplings `Q b` are Mathlib `Kernel`s, so measurable in the pair by definition.
  Their existence (gluing along hybrids, measurable disintegrations; REVIEW-3's second NIT) is not proved here: it is
  the hypothesis (C), a field of `CouplingSpec`.
* **Locality instead of "acts only on the block".** (S) asks `q b σ` to keep the coordinates off `B b` almost surely,
  for `σ ∈ Ω₀`. The paper's "depends only on `σ` off `B_b`" is never used, so it is not assumed.
* **Hypotheses only on the supports.** Locality, support preservation, the marginals of `Q b`, and (I) are asked only
  for `σ ∈ Ω₀`, `σ' ∈ Ω₀'`.
* **Good/source split** as a `Finset` `good` of blocks; source blocks are `univ \ good`.
* The paper's `K_b(z) ≥ 0` is not needed and not assumed; `v ≥ 0` suffices for the coupling bound, and `v ≥ v_min > 0`
  on `A` for the integral bound.
-/

open MeasureTheory ProbabilityTheory Finset

open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.OneBox

variable {ι S β : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] [Fintype β] [DecidableEq β]

/-! ### Disagreement, the functional `Φ`, coverage and the source weight -/

/-- The disagreement event at the site `x`: the two configurations of the pair differ at `x`. -/
def disagree (x : ι) : Set ((ι → S) × (ι → S)) := {p | p.1 x ≠ p.2 x}

theorem measurableSet_disagree [MeasurableEq S] (x : ι) : MeasurableSet (disagree (S := S) x) := by
  have h : MeasurableSet {p : (ι → S) × (ι → S) | p.1 x = p.2 x} :=
    measurableSet_eq_fun ((measurable_pi_apply x).comp measurable_fst)
      ((measurable_pi_apply x).comp measurable_snd)
  exact h.compl

/-- The weighted expected disagreement `Φ(π) = Σ_x v x * π(Y_x ≠ Y'_x)`. -/
def phi (v : ι → ℝ) (π : Measure ((ι → S) × (ι → S))) : ℝ := ∑ x, v x * π.real (disagree x)

/-- The coverage `c(x) = #{b | x ∈ B b}`. -/
def coverage (B : β → Finset ι) (x : ι) : ℕ := (univ.filter fun b => x ∈ B b).card

/-- The source weight `s = Σ_{b source} Σ_{y ∈ B b} v y`. -/
def srcWeight (good : Finset β) (B : β → Finset ι) (v : ι → ℝ) : ℝ := ∑ b ∈ univ \ good, ∑ y ∈ B b, v y

/-! ### The data: supports, blocks, specifications (S) and block couplings (C) -/

/-- **The data of the coupling-form Dobrushin-Shlosman theorem** (`UV-TV.md` 28.1, (S) and (C)).

* `Ω₀, Ω₀'`: measurable supports of full measure for `μ, μ'`.
* `B b`: the blocks.
* `q b, q' b`: block specifications. For `σ` in the support they keep `σ` off the block almost surely, and they keep
  the support; they satisfy DLR, `μ.bind (q b) = μ`.
* `Q b`: measurable block couplings, whose marginals at an in-support pair `(σ, σ')` are `q b σ` and `q' b σ'`. -/
structure CouplingSpec (μ μ' : Measure (ι → S)) (β : Type*) where
  Ω₀ : Set (ι → S)
  Ω₀' : Set (ι → S)
  meas₀ : MeasurableSet Ω₀
  meas₀' : MeasurableSet Ω₀'
  full₀ : μ Ω₀ᶜ = 0
  full₀' : μ' Ω₀'ᶜ = 0
  B : β → Finset ι
  q : β → Kernel (ι → S) (ι → S)
  q' : β → Kernel (ι → S) (ι → S)
  /-- (S) the specification acts on the block only. -/
  q_local : ∀ b, ∀ σ ∈ Ω₀, ∀ x ∉ B b, ∀ᵐ ξ ∂(q b σ), ξ x = σ x
  q'_local : ∀ b, ∀ σ ∈ Ω₀', ∀ x ∉ B b, ∀ᵐ ξ ∂(q' b σ), ξ x = σ x
  /-- (S) DLR. -/
  q_dlr : ∀ b, μ.bind (q b) = μ
  q'_dlr : ∀ b, μ'.bind (q' b) = μ'
  /-- (S) the specification preserves the support. -/
  q_supp : ∀ b, ∀ σ ∈ Ω₀, q b σ Ω₀ᶜ = 0
  q'_supp : ∀ b, ∀ σ ∈ Ω₀', q' b σ Ω₀'ᶜ = 0
  Q : β → Kernel ((ι → S) × (ι → S)) ((ι → S) × (ι → S))
  Q_markov : ∀ b, IsMarkovKernel (Q b)
  /-- (C) the marginals of the block coupling at in-support pairs. -/
  Q_fst : ∀ b, ∀ σ ∈ Ω₀, ∀ σ' ∈ Ω₀', (Q b (σ, σ')).map Prod.fst = q b σ
  Q_snd : ∀ b, ∀ σ ∈ Ω₀, ∀ σ' ∈ Ω₀', (Q b (σ, σ')).map Prod.snd = q' b σ'

namespace CouplingSpec

variable {μ μ' : Measure (ι → S)} (C : CouplingSpec μ μ' β)

instance (b : β) : IsMarkovKernel (C.Q b) := C.Q_markov b

/-- A coupling of `μ, μ'` carried by `Ω₀ × Ω₀'`. -/
structure IsSuppCoupling (π : Measure ((ι → S) × (ι → S))) : Prop where
  fst : π.map Prod.fst = μ
  snd : π.map Prod.snd = μ'
  supp : π (C.Ω₀ ×ˢ C.Ω₀')ᶜ = 0

/-- The averaged block update `T π = (1/N) Σ_b ∫ π(dp) Q_b(p, ·)`. -/
def T (π : Measure ((ι → S) × (ι → S))) : Measure ((ι → S) × (ι → S)) :=
  ((Fintype.card β : ℝ≥0∞)⁻¹) • ∑ b, π.bind (C.Q b)

variable {C}

theorem IsSuppCoupling.isProbabilityMeasure [IsProbabilityMeasure μ] {π : Measure ((ι → S) × (ι → S))}
    (h : C.IsSuppCoupling π) : IsProbabilityMeasure π := by
  constructor
  have := Measure.map_apply (μ := π) measurable_fst MeasurableSet.univ
  rw [h.fst, Set.preimage_univ, measure_univ] at this
  exact this.symm

theorem IsSuppCoupling.ae_mem {π : Measure ((ι → S) × (ι → S))} (h : C.IsSuppCoupling π) :
    ∀ᵐ p ∂π, p.1 ∈ C.Ω₀ ∧ p.2 ∈ C.Ω₀' := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h.supp] with p hp
  simpa [Set.mem_prod] using hp

theorem Q_fst' (b : β) {p : (ι → S) × (ι → S)} (hp : p.1 ∈ C.Ω₀ ∧ p.2 ∈ C.Ω₀') :
    (C.Q b p).map Prod.fst = C.q b p.1 := C.Q_fst b p.1 hp.1 p.2 hp.2

theorem Q_snd' (b : β) {p : (ι → S) × (ι → S)} (hp : p.1 ∈ C.Ω₀ ∧ p.2 ∈ C.Ω₀') :
    (C.Q b p).map Prod.snd = C.q' b p.2 := C.Q_snd b p.1 hp.1 p.2 hp.2

/-- One block update keeps the first marginal (DLR). -/
theorem bind_map_fst {π : Measure ((ι → S) × (ι → S))} (h : C.IsSuppCoupling π) (b : β) :
    (π.bind (C.Q b)).map Prod.fst = μ := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs, Measure.bind_apply (measurable_fst hs) (C.Q b).aemeasurable]
  have h1 : ∫⁻ p, C.Q b p (Prod.fst ⁻¹' s) ∂π = ∫⁻ p, C.q b p.1 s ∂π := by
    apply lintegral_congr_ae
    filter_upwards [h.ae_mem] with p hp
    rw [← Measure.map_apply measurable_fst hs, C.Q_fst' b hp]
  rw [h1]
  have h2 : ∫⁻ p, C.q b p.1 s ∂π = ∫⁻ σ, C.q b σ s ∂(π.map Prod.fst) :=
    (lintegral_map (Kernel.measurable_coe _ hs) measurable_fst).symm
  rw [h2, h.fst, ← Measure.bind_apply hs (C.q b).aemeasurable, C.q_dlr b]

/-- One block update keeps the second marginal (DLR). -/
theorem bind_map_snd {π : Measure ((ι → S) × (ι → S))} (h : C.IsSuppCoupling π) (b : β) :
    (π.bind (C.Q b)).map Prod.snd = μ' := by
  ext s hs
  rw [Measure.map_apply measurable_snd hs, Measure.bind_apply (measurable_snd hs) (C.Q b).aemeasurable]
  have h1 : ∫⁻ p, C.Q b p (Prod.snd ⁻¹' s) ∂π = ∫⁻ p, C.q' b p.2 s ∂π := by
    apply lintegral_congr_ae
    filter_upwards [h.ae_mem] with p hp
    rw [← Measure.map_apply measurable_snd hs, C.Q_snd' b hp]
  rw [h1]
  have h2 : ∫⁻ p, C.q' b p.2 s ∂π = ∫⁻ σ, C.q' b σ s ∂(π.map Prod.snd) :=
    (lintegral_map (Kernel.measurable_coe _ hs) measurable_snd).symm
  rw [h2, h.snd, ← Measure.bind_apply hs (C.q' b).aemeasurable, C.q'_dlr b]

/-- At an in-support pair, the block coupling gives the complement of `Ω₀ × Ω₀'` mass `0`. -/
theorem Q_compl_supp (b : β) {p : (ι → S) × (ι → S)} (hp : p.1 ∈ C.Ω₀ ∧ p.2 ∈ C.Ω₀') :
    C.Q b p (C.Ω₀ ×ˢ C.Ω₀')ᶜ = 0 := by
  have hsub : (C.Ω₀ ×ˢ C.Ω₀')ᶜ ⊆ Prod.fst ⁻¹' C.Ω₀ᶜ ∪ Prod.snd ⁻¹' C.Ω₀'ᶜ := by
    intro w hw
    simp only [Set.mem_compl_iff, Set.mem_prod, not_and_or] at hw
    simpa using hw
  refine le_antisymm ((measure_mono hsub).trans ((measure_union_le _ _).trans ?_)) zero_le
  rw [← Measure.map_apply measurable_fst C.meas₀.compl, ← Measure.map_apply measurable_snd C.meas₀'.compl,
    C.Q_fst' b hp, C.Q_snd' b hp, C.q_supp b _ hp.1, C.q'_supp b _ hp.2, add_zero]

theorem bind_supp {π : Measure ((ι → S) × (ι → S))} (h : C.IsSuppCoupling π) (b : β) :
    π.bind (C.Q b) (C.Ω₀ ×ˢ C.Ω₀')ᶜ = 0 := by
  rw [Measure.bind_apply (C.meas₀.prod C.meas₀').compl (C.Q b).aemeasurable]
  rw [lintegral_congr_ae (g := fun _ => 0)]
  · simp
  filter_upwards [h.ae_mem] with p hp
  exact C.Q_compl_supp b hp

theorem isSuppCoupling_bind {π : Measure ((ι → S) × (ι → S))} (h : C.IsSuppCoupling π) (b : β) :
    C.IsSuppCoupling (π.bind (C.Q b)) :=
  ⟨bind_map_fst h b, bind_map_snd h b, bind_supp h b⟩

theorem T_apply (π : Measure ((ι → S) × (ι → S))) (s : Set ((ι → S) × (ι → S))) :
    C.T π s = (Fintype.card β : ℝ≥0∞)⁻¹ * ∑ b, π.bind (C.Q b) s := by
  simp [T, Measure.coe_finsetSum]

theorem card_inv_mul_card [Nonempty β] (a : ℝ≥0∞) :
    (Fintype.card β : ℝ≥0∞)⁻¹ * ∑ _b : β, a = a := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by simp [Fintype.card_ne_zero]) (by simp), one_mul]

/-- **Step 1 of 28.2.** The averaged update maps couplings carried by `Ω₀ × Ω₀'` to such couplings. -/
theorem isSuppCoupling_T [Nonempty β] {π : Measure ((ι → S) × (ι → S))} (h : C.IsSuppCoupling π) :
    C.IsSuppCoupling (C.T π) := by
  refine ⟨?_, ?_, ?_⟩
  · ext s hs
    rw [Measure.map_apply measurable_fst hs, T_apply]
    simp_rw [← Measure.map_apply measurable_fst hs, bind_map_fst h]
    exact card_inv_mul_card _
  · ext s hs
    rw [Measure.map_apply measurable_snd hs, T_apply]
    simp_rw [← Measure.map_apply measurable_snd hs, bind_map_snd h]
    exact card_inv_mul_card _
  · rw [T_apply]
    simp [bind_supp h]

/-- The product coupling is carried by `Ω₀ × Ω₀'`. -/
theorem isSuppCoupling_prod [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] :
    C.IsSuppCoupling (μ.prod μ') := by
  refine ⟨by simp, by simp, ?_⟩
  have hsub : (C.Ω₀ ×ˢ C.Ω₀')ᶜ ⊆ C.Ω₀ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ C.Ω₀'ᶜ := by
    intro w hw
    simp only [Set.mem_compl_iff, Set.mem_prod, not_and_or] at hw
    simpa using hw
  refine le_antisymm ((measure_mono hsub).trans ((measure_union_le _ _).trans ?_)) zero_le
  rw [Measure.prod_prod, Measure.prod_prod, C.full₀, C.full₀']
  simp

/-! ### Real-valued evaluations -/

theorem bind_real {π : Measure ((ι → S) × (ι → S))} [IsProbabilityMeasure π] (b : β)
    {s : Set ((ι → S) × (ι → S))} (hs : MeasurableSet s) :
    (π.bind (C.Q b)).real s = ∫ p, (C.Q b p).real s ∂π := by
  rw [measureReal_def, Measure.bind_apply hs (C.Q b).aemeasurable]
  rw [← integral_toReal ((Kernel.measurable_coe _ hs).aemeasurable) (ae_of_all _ fun p => measure_lt_top _ _)]
  rfl

theorem integrable_Q_real {π : Measure ((ι → S) × (ι → S))} [IsProbabilityMeasure π] (b : β)
    {s : Set ((ι → S) × (ι → S))} (hs : MeasurableSet s) :
    Integrable (fun p => (C.Q b p).real s) π := by
  refine Integrable.of_bound (C := 1) ?_ (ae_of_all _ fun p => ?_)
  · exact (Kernel.measurable_coe _ hs).ennreal_toReal.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one

theorem T_real [IsProbabilityMeasure μ] [Nonempty β] {π : Measure ((ι → S) × (ι → S))}
    (h : C.IsSuppCoupling π) (s : Set ((ι → S) × (ι → S))) :
    (C.T π).real s = (Fintype.card β : ℝ)⁻¹ * ∑ b, (π.bind (C.Q b)).real s := by
  have hp : ∀ b, IsProbabilityMeasure (π.bind (C.Q b)) := fun b =>
    (isSuppCoupling_bind h b).isProbabilityMeasure
  rw [measureReal_def, T_apply, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun b _ => measure_ne_top _ _)]
  rfl

/-! ### Step 2 of 28.2: the per-block estimates -/

section Step

variable [MeasurableEq S]

/-- **Sites outside the block keep their pair.** -/
theorem bind_real_disagree_le_of_notMem [IsProbabilityMeasure μ] {π : Measure ((ι → S) × (ι → S))}
    (h : C.IsSuppCoupling π) (b : β) {x : ι} (hx : x ∉ C.B b) :
    (π.bind (C.Q b)).real (disagree x) ≤ π.real (disagree x) := by
  have := h.isProbabilityMeasure
  rw [bind_real b (measurableSet_disagree x), ← integral_indicator_one (measurableSet_disagree x)]
  refine integral_mono_ae (integrable_Q_real b (measurableSet_disagree x))
    ((integrable_const (1 : ℝ)).indicator (measurableSet_disagree x)) ?_
  filter_upwards [h.ae_mem] with p hp
  by_cases hd : p ∈ disagree x
  · rw [Set.indicator_of_mem hd]
    exact measureReal_le_one
  · rw [Set.indicator_of_notMem hd]
    have h1 : ∀ᵐ w ∂(C.Q b p), w.1 x = p.1 x := by
      have := C.q_local b p.1 hp.1 x hx
      rw [← C.Q_fst' b hp] at this
      exact ae_of_ae_map measurable_fst.aemeasurable this
    have h2 : ∀ᵐ w ∂(C.Q b p), w.2 x = p.2 x := by
      have := C.q'_local b p.2 hp.2 x hx
      rw [← C.Q_snd' b hp] at this
      exact ae_of_ae_map measurable_snd.aemeasurable this
    have h0 : C.Q b p (disagree x) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [h1, h2] with w hw1 hw2
      simp only [disagree, Set.mem_ofPred_eq, not_not] at hd ⊢
      rw [hw1, hw2, hd]
    simp [measureReal_def, h0]

/-- **A good block, integrating (I) over `π`.** -/
theorem good_block_le [IsProbabilityMeasure μ] {π : Measure ((ι → S) × (ι → S))} (h : C.IsSuppCoupling π)
    {good : Finset β} {v : ι → ℝ} {K : β → ι → ℝ}
    (hI : ∀ b ∈ good, ∀ σ ∈ C.Ω₀, ∀ σ' ∈ C.Ω₀',
      ∑ y ∈ C.B b, v y * (C.Q b (σ, σ')).real (disagree y) ≤
        ∑ z ∈ (C.B b)ᶜ, (disagree z).indicator (fun _ => K b z * v z) (σ, σ'))
    {b : β} (hb : b ∈ good) :
    ∑ y ∈ C.B b, v y * (π.bind (C.Q b)).real (disagree y) ≤
      ∑ z ∈ (C.B b)ᶜ, K b z * v z * π.real (disagree z) := by
  have := h.isProbabilityMeasure
  have hL : ∑ y ∈ C.B b, v y * (π.bind (C.Q b)).real (disagree y) =
      ∫ p, ∑ y ∈ C.B b, v y * (C.Q b p).real (disagree y) ∂π := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [bind_real b (measurableSet_disagree y), integral_const_mul]
    · intro y _
      exact (integrable_Q_real b (measurableSet_disagree y)).const_mul _
  have hR : ∑ z ∈ (C.B b)ᶜ, K b z * v z * π.real (disagree z) =
      ∫ p, ∑ z ∈ (C.B b)ᶜ, (disagree z).indicator (fun _ => K b z * v z) p ∂π := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun z _ => ?_
      rw [integral_indicator_const _ (measurableSet_disagree z), smul_eq_mul, mul_comm]
    · intro z _
      exact (integrable_const _).indicator (measurableSet_disagree z)
  rw [hL, hR]
  refine integral_mono_ae ?_ ?_ ?_
  · exact integrable_finsetSum _ fun y _ => (integrable_Q_real b (measurableSet_disagree y)).const_mul _
  · exact integrable_finsetSum _ fun z _ => (integrable_const _).indicator (measurableSet_disagree z)
  · filter_upwards [h.ae_mem] with p hp
    exact hI b hb p.1 hp.1 p.2 hp.2

/-- **A source block** contributes at most its weight. -/
theorem block_le_weight [IsProbabilityMeasure μ] {π : Measure ((ι → S) × (ι → S))} (h : C.IsSuppCoupling π)
    (b : β) {v : ι → ℝ} (hv : ∀ x, 0 ≤ v x) :
    ∑ y ∈ C.B b, v y * (π.bind (C.Q b)).real (disagree y) ≤ ∑ y ∈ C.B b, v y := by
  have := (isSuppCoupling_bind h b).isProbabilityMeasure
  exact Finset.sum_le_sum fun y _ => mul_le_of_le_one_right (hv y) measureReal_le_one

end Step

end CouplingSpec

/-! ### Two counting identities -/

theorem sum_blocks (B : β → Finset ι) (f : ι → ℝ) :
    ∑ b, ∑ x ∈ B b, f x = ∑ x, (coverage B x : ℝ) * f x := by
  have : ∀ b, ∑ x ∈ B b, f x = ∑ x, if x ∈ B b then f x else 0 := fun b => by
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, coverage]

theorem sum_good_compl (B : β → Finset ι) (good : Finset β) (g : β → ι → ℝ) :
    ∑ b ∈ good, ∑ z ∈ (B b)ᶜ, g b z = ∑ z, ∑ b ∈ good.filter (fun b => z ∉ B b), g b z := by
  have : ∀ b, ∑ z ∈ (B b)ᶜ, g b z = ∑ z, if z ∉ B b then g b z else 0 := fun b => by
    rw [← Finset.sum_filter]
    congr 1
    ext z
    simp
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_filter]

namespace CouplingSpec

variable {μ μ' : Measure (ι → S)} {C : CouplingSpec μ μ' β}

/-! ### Step 3 of 28.2: the one-step contraction -/

theorem phi_nonneg {v : ι → ℝ} (hv : ∀ x, 0 ≤ v x) (π : Measure ((ι → S) × (ι → S))) : 0 ≤ phi v π :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hv x) measureReal_nonneg

/-- **One step:** `Φ(T π) ≤ θ Φ(π) + s/N`, `θ = 1 - (1 - γ) c_min / N`. -/
theorem phi_T_le [MeasurableEq S] [IsProbabilityMeasure μ] [Nonempty β] {π : Measure ((ι → S) × (ι → S))}
    (h : C.IsSuppCoupling π) {good : Finset β} {v : ι → ℝ} {K : β → ι → ℝ} {γ cmin : ℝ}
    (hv : ∀ x, 0 ≤ v x) (hγ : γ ≤ 1) (hc : ∀ x, cmin ≤ coverage C.B x)
    (hI : ∀ b ∈ good, ∀ σ ∈ C.Ω₀, ∀ σ' ∈ C.Ω₀',
      ∑ y ∈ C.B b, v y * (C.Q b (σ, σ')).real (disagree y) ≤
        ∑ z ∈ (C.B b)ᶜ, (disagree z).indicator (fun _ => K b z * v z) (σ, σ'))
    (hK : ∀ z, ∑ b ∈ good.filter (fun b => z ∉ C.B b), K b z ≤ γ * coverage C.B z) :
    phi v (C.T π) ≤ (1 - (1 - γ) * cmin / Fintype.card β) * phi v π + srcWeight good C.B v / Fintype.card β := by
  have hN : (0 : ℝ) < Fintype.card β := Nat.cast_pos.mpr Fintype.card_pos
  have hd : ∀ x, 0 ≤ π.real (disagree x) := fun x => measureReal_nonneg
  have hphiT : phi v (C.T π) =
      (Fintype.card β : ℝ)⁻¹ * ∑ b, ∑ x, v x * (π.bind (C.Q b)).real (disagree x) := by
    calc phi v (C.T π)
        = ∑ x, ∑ b, (Fintype.card β : ℝ)⁻¹ * (v x * (π.bind (C.Q b)).real (disagree x)) := by
          simp only [phi, T_real h, Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun b _ => by ring
      _ = ∑ b, ∑ x, (Fintype.card β : ℝ)⁻¹ * (v x * (π.bind (C.Q b)).real (disagree x)) :=
          Finset.sum_comm
      _ = _ := by simp only [Finset.mul_sum]
  -- the part of each block's sum outside the block
  have hO : ∀ b, ∑ x ∈ (C.B b)ᶜ, v x * (π.bind (C.Q b)).real (disagree x) ≤
      ∑ x ∈ (C.B b)ᶜ, v x * π.real (disagree x) := fun b =>
    Finset.sum_le_sum fun x hx =>
      mul_le_mul_of_nonneg_left (bind_real_disagree_le_of_notMem h b (Finset.mem_compl.mp hx)) (hv x)
  have hsplit : ∀ b, ∑ x, v x * (π.bind (C.Q b)).real (disagree x) =
      ∑ x ∈ (C.B b)ᶜ, v x * (π.bind (C.Q b)).real (disagree x) +
        ∑ x ∈ C.B b, v x * (π.bind (C.Q b)).real (disagree x) := fun b =>
    (Finset.sum_compl_add_sum (C.B b) _).symm
  set O : β → ℝ := fun b => ∑ x ∈ (C.B b)ᶜ, v x * π.real (disagree x) with hOdef
  have hgood : ∀ b ∈ good, ∑ x, v x * (π.bind (C.Q b)).real (disagree x) ≤
      O b + ∑ z ∈ (C.B b)ᶜ, K b z * v z * π.real (disagree z) := fun b hb => by
    rw [hsplit b]
    exact add_le_add (hO b) (good_block_le h hI hb)
  have hsrc : ∀ b, ∑ x, v x * (π.bind (C.Q b)).real (disagree x) ≤ O b + ∑ y ∈ C.B b, v y := fun b => by
    rw [hsplit b]
    exact add_le_add (hO b) (block_le_weight h b hv)
  -- sum of the outside parts
  have hOsum : ∑ b, O b = (Fintype.card β : ℝ) * phi v π -
      ∑ x, (coverage C.B x : ℝ) * (v x * π.real (disagree x)) := by
    have : ∀ b, O b = phi v π - ∑ x ∈ C.B b, v x * π.real (disagree x) := fun b =>
      eq_sub_of_add_eq (Finset.sum_compl_add_sum (C.B b) _)
    rw [Finset.sum_congr rfl fun b _ => this b, Finset.sum_sub_distrib, sum_blocks, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  -- the good blocks' influence terms, by the column condition
  have hKsum : ∑ b ∈ good, ∑ z ∈ (C.B b)ᶜ, K b z * v z * π.real (disagree z) ≤
      γ * ∑ x, (coverage C.B x : ℝ) * (v x * π.real (disagree x)) := by
    rw [sum_good_compl, Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    have : ∑ b ∈ good.filter (fun b => z ∉ C.B b), K b z * v z * π.real (disagree z) =
        (∑ b ∈ good.filter (fun b => z ∉ C.B b), K b z) * (v z * π.real (disagree z)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [this, ← mul_assoc γ]
    exact mul_le_mul_of_nonneg_right (hK z) (mul_nonneg (hv z) (hd z))
  -- coverage at least c_min
  have hcov : cmin * phi v π ≤ ∑ x, (coverage C.B x : ℝ) * (v x * π.real (disagree x)) := by
    rw [phi, Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hc x) (mul_nonneg (hv x) (hd x))
  -- total over blocks
  have htot : ∑ b, ∑ x, v x * (π.bind (C.Q b)).real (disagree x) ≤
      (Fintype.card β : ℝ) * phi v π - (1 - γ) * cmin * phi v π + srcWeight good C.B v := by
    rw [← Finset.sum_sdiff (Finset.subset_univ good)]
    have h1 : ∑ b ∈ univ \ good, ∑ x, v x * (π.bind (C.Q b)).real (disagree x) ≤
        ∑ b ∈ univ \ good, O b + srcWeight good C.B v := by
      rw [srcWeight, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun b _ => hsrc b
    have h2 : ∑ b ∈ good, ∑ x, v x * (π.bind (C.Q b)).real (disagree x) ≤
        ∑ b ∈ good, O b + ∑ b ∈ good, ∑ z ∈ (C.B b)ᶜ, K b z * v z * π.real (disagree z) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun b hb => hgood b hb
    have h3 : ∑ b ∈ univ \ good, O b + ∑ b ∈ good, O b = ∑ b, O b :=
      Finset.sum_sdiff (Finset.subset_univ good)
    have h4 : 0 ≤ 1 - γ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hcov h4]
  rw [hphiT]
  calc (Fintype.card β : ℝ)⁻¹ * ∑ b, ∑ x, v x * (π.bind (C.Q b)).real (disagree x)
      ≤ (Fintype.card β : ℝ)⁻¹ *
          ((Fintype.card β : ℝ) * phi v π - (1 - γ) * cmin * phi v π + srcWeight good C.B v) :=
        mul_le_mul_of_nonneg_left htot (inv_nonneg.mpr hN.le)
    _ = _ := by
        field_simp

/-! ### Step 4 of 28.2: the iterates, and the bound for every admissible choice of weights -/

variable (C) in
/-- The iterates `π_n = T^n (μ ⊗ μ')`. They depend on `C` only: not on the weights `v`, the good/source split, `K`,
`γ` or `c_min`. -/
def iter (n : ℕ) : Measure ((ι → S) × (ι → S)) := (C.T)^[n] (μ.prod μ')

theorem iter_succ (n : ℕ) : C.iter (n + 1) = C.T (C.iter n) := by
  simp only [iter, Function.iterate_succ_apply']

theorem isSuppCoupling_iter [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [Nonempty β] (n : ℕ) :
    C.IsSuppCoupling (C.iter n) := by
  induction n with
  | zero => exact isSuppCoupling_prod
  | succ n ih => rw [iter_succ]; exact isSuppCoupling_T ih

variable (C) in
/-- **Admissible weights** for `C`: a good/source split, site weights `v ≥ 0`, influence numbers `K`, constants
`γ ∈ [0, 1)` and `c_min > 0` below the coverage, with (I) on the good blocks and the column condition (K). -/
structure DSWeights where
  good : Finset β
  v : ι → ℝ
  K : β → ι → ℝ
  γ : ℝ
  cmin : ℝ
  v_nonneg : ∀ x, 0 ≤ v x
  γ_nonneg : 0 ≤ γ
  γ_lt_one : γ < 1
  cmin_pos : 0 < cmin
  cmin_le : ∀ x, cmin ≤ coverage C.B x
  /-- (I) influence on good blocks, for in-support pairs. -/
  influence : ∀ b ∈ good, ∀ σ ∈ C.Ω₀, ∀ σ' ∈ C.Ω₀',
    ∑ y ∈ C.B b, v y * (C.Q b (σ, σ')).real (disagree y) ≤
      ∑ z ∈ (C.B b)ᶜ, (disagree z).indicator (fun _ => K b z * v z) (σ, σ')
  /-- (K) the column condition. -/
  column : ∀ z, ∑ b ∈ good.filter (fun b => z ∉ C.B b), K b z ≤ γ * coverage C.B z

namespace DSWeights

/-- The bound `s/((1 - γ) c_min)`. -/
def bound (W : C.DSWeights) : ℝ := srcWeight W.good C.B W.v / ((1 - W.γ) * W.cmin)

/-- The contraction rate `θ = 1 - (1 - γ) c_min / N`. -/
def θ (W : C.DSWeights) : ℝ := 1 - (1 - W.γ) * W.cmin / Fintype.card β

theorem srcWeight_nonneg (W : C.DSWeights) : 0 ≤ srcWeight W.good C.B W.v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun y _ => W.v_nonneg y

theorem bound_nonneg (W : C.DSWeights) : 0 ≤ W.bound :=
  div_nonneg W.srcWeight_nonneg (mul_nonneg (by linarith [W.γ_lt_one]) W.cmin_pos.le)

theorem θ_lt_one [Nonempty β] (W : C.DSWeights) : W.θ < 1 := by
  have hN : (0 : ℝ) < Fintype.card β := Nat.cast_pos.mpr Fintype.card_pos
  have : 0 < (1 - W.γ) * W.cmin / Fintype.card β :=
    div_pos (mul_pos (by linarith [W.γ_lt_one]) W.cmin_pos) hN
  simp only [θ]
  linarith

theorem θ_nonneg [Nonempty ι] (W : C.DSWeights) : 0 ≤ W.θ := by
  obtain ⟨x⟩ := ‹Nonempty ι›
  have hN : (0 : ℝ) < Fintype.card β := by
    have h1 := W.cmin_le x
    have h2 : (coverage C.B x : ℝ) ≤ Fintype.card β := by
      exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_univ.le)
    linarith [W.cmin_pos]
  have hcN : W.cmin ≤ Fintype.card β := by
    have h2 : (coverage C.B x : ℝ) ≤ Fintype.card β := by
      exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_univ.le)
    linarith [W.cmin_le x]
  have : (1 - W.γ) * W.cmin / Fintype.card β ≤ 1 := by
    rw [div_le_one hN]
    nlinarith [W.γ_nonneg, W.cmin_pos]
  simp only [θ]
  linarith

theorem fixed_point [Nonempty β] (W : C.DSWeights) :
    W.θ * W.bound + srcWeight W.good C.B W.v / Fintype.card β = W.bound := by
  have hN : (Fintype.card β : ℝ) ≠ 0 := (Nat.cast_pos.mpr Fintype.card_pos).ne'
  have h1 : 1 - W.γ ≠ 0 := by linarith [W.γ_lt_one]
  have h2 : W.cmin ≠ 0 := W.cmin_pos.ne'
  simp only [θ, bound]
  field_simp
  ring

end DSWeights

/-- **The bound along the explicit iterates, for every admissible choice of weights.**
`Φ_v(T^n (μ ⊗ μ')) ≤ s/((1 - γ) c_min) + θ^n Φ_v(μ ⊗ μ')`. The iterates do not depend on `W`. -/
theorem phi_iter_le [MeasurableEq S] [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [Nonempty β]
    (W : C.DSWeights) (n : ℕ) :
    phi W.v (C.iter n) ≤ W.bound + W.θ ^ n * phi W.v (μ.prod μ') := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h0 : ∀ π : Measure ((ι → S) × (ι → S)), phi W.v π = 0 := fun π => by
      simp [phi, Finset.univ_eq_empty]
    rw [h0, h0, mul_zero, add_zero]
    exact W.bound_nonneg
  induction n with
  | zero =>
      simp only [pow_zero, one_mul, iter, Function.iterate_zero, id]
      linarith [W.bound_nonneg]
  | succ n ih =>
      rw [iter_succ]
      have hstep := phi_T_le (isSuppCoupling_iter (C := C) n) W.v_nonneg W.γ_lt_one.le W.cmin_le
        W.influence W.column
      have hθ := W.θ_nonneg
      have hfix := W.fixed_point
      simp only [DSWeights.θ] at hθ hfix ⊢
      calc phi W.v (C.T (C.iter n))
          ≤ (1 - (1 - W.γ) * W.cmin / Fintype.card β) * phi W.v (C.iter n) +
              srcWeight W.good C.B W.v / Fintype.card β := hstep
        _ ≤ (1 - (1 - W.γ) * W.cmin / Fintype.card β) *
              (W.bound + (1 - (1 - W.γ) * W.cmin / Fintype.card β) ^ n * phi W.v (μ.prod μ')) +
              srcWeight W.good C.B W.v / Fintype.card β := by
            gcongr
            exact ih
        _ = _ := by rw [pow_succ]; linear_combination hfix

/-- For every admissible choice of weights and every `ε > 0`, eventually `Φ_v(π_n) ≤ s/((1 - γ) c_min) + ε`. -/
theorem eventually_phi_iter_le [MeasurableEq S] [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [Nonempty β]
    (W : C.DSWeights) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, phi W.v (C.iter n) ≤ W.bound + ε := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine Filter.Eventually.of_forall fun n => ?_
    have : phi W.v (C.iter n) = 0 := by simp [phi, Finset.univ_eq_empty]
    rw [this]
    linarith [W.bound_nonneg]
  have ht : Filter.Tendsto (fun n : ℕ => W.θ ^ n * phi W.v (μ.prod μ')) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one W.θ_nonneg W.θ_lt_one).mul_const (phi W.v (μ.prod μ'))
    simpa using this
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  linarith [phi_iter_le W n]

/-- **One sequence of couplings for all weights at once.** For any finite family of admissible weight choices and
any `ε > 0` there is one `n` such that the single coupling `π_n = T^n (μ ⊗ μ')` satisfies every weight-specific
bound. (For an arbitrary family, `phi_iter_le` gives the explicit rate `θ_W^n` for each member.) -/
theorem exists_iter_forall_le [MeasurableEq S] [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [Nonempty β]
    {α : Type*} [Finite α] (W : α → C.DSWeights) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, C.IsSuppCoupling (C.iter n) ∧ ∀ a, phi (W a).v (C.iter n) ≤ (W a).bound + ε := by
  obtain ⟨n, hn⟩ := (Filter.eventually_all.mpr fun a => eventually_phi_iter_le (W a) hε).exists
  exact ⟨n, isSuppCoupling_iter n, hn⟩

end CouplingSpec

/-! ### The theorem and its consequence -/

open CouplingSpec

/-- **The coupling-form Dobrushin-Shlosman theorem** (`UV-TV.md` 28.1). Under (I) on the good blocks and the column
condition (K), for every `ε > 0` there is a coupling `π` of `μ` and `μ'` (carried by `Ω₀ × Ω₀'`) with
`Σ_x v x * π{Y_x ≠ Y'_x} ≤ s/((1 - γ) c_min) + ε`. -/
theorem couplingDS_bound [MeasurableEq S] {μ μ' : Measure (ι → S)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] [Nonempty β] (C : CouplingSpec μ μ' β)
    (good : Finset β) (v : ι → ℝ) (K : β → ι → ℝ) (γ cmin : ℝ)
    (hv : ∀ x, 0 ≤ v x) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hcmin : 0 < cmin) (hc : ∀ x, cmin ≤ coverage C.B x)
    (hI : ∀ b ∈ good, ∀ σ ∈ C.Ω₀, ∀ σ' ∈ C.Ω₀',
      ∑ y ∈ C.B b, v y * (C.Q b (σ, σ')).real (disagree y) ≤
        ∑ z ∈ (C.B b)ᶜ, (disagree z).indicator (fun _ => K b z * v z) (σ, σ'))
    (hK : ∀ z, ∑ b ∈ good.filter (fun b => z ∉ C.B b), K b z ≤ γ * coverage C.B z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ π : Measure ((ι → S) × (ι → S)), IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧ π.map Prod.snd = μ' ∧
      π (C.Ω₀ ×ˢ C.Ω₀')ᶜ = 0 ∧
      ∑ x, v x * π.real {p | p.1 x ≠ p.2 x} ≤ srcWeight good C.B v / ((1 - γ) * cmin) + ε := by
  let W : C.DSWeights := ⟨good, v, K, γ, cmin, hv, hγ0, hγ1, hcmin, hc, hI, hK⟩
  obtain ⟨n, hn⟩ := (eventually_phi_iter_le W hε).exists
  have hs := isSuppCoupling_iter (C := C) n
  exact ⟨C.iter n, hs.isProbabilityMeasure, hs.fst, hs.snd, hs.supp, hn⟩

/-- **From a coupling to test functions.** For a coupling `π` of `μ, μ'` and a measurable `F`, `|F| ≤ M`, depending
only on the sites in `A`: `|∫ F dμ - ∫ F dμ'| ≤ 2 M (min_A v)⁻¹ Φ_v(π)`. -/
theorem abs_integral_sub_le_phi [MeasurableEq S] {μ μ' : Measure (ι → S)} {π : Measure ((ι → S) × (ι → S))}
    [IsProbabilityMeasure π] (hfst : π.map Prod.fst = μ) (hsnd : π.map Prod.snd = μ')
    {v : ι → ℝ} (hv : ∀ x, 0 ≤ v x) (A : Finset ι) {vmin : ℝ} (hvmin : 0 < vmin) (hvA : ∀ x ∈ A, vmin ≤ v x)
    {F : (ι → S) → ℝ} (hF : Measurable F) {M : ℝ} (hFM : ∀ σ, |F σ| ≤ M)
    (hdep : ∀ σ σ' : ι → S, (∀ x ∈ A, σ x = σ' x) → F σ = F σ') :
    |∫ σ, F σ ∂μ - ∫ σ, F σ ∂μ'| ≤ 2 * M * vmin⁻¹ * phi v π := by
  obtain ⟨p₀, -⟩ := nonempty_of_measure_ne_zero (μ := π) (s := Set.univ) (by simp)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hFM p₀.1)
  have hint : ∀ g : (ι → S) × (ι → S) → ι → S, Measurable g → Integrable (fun p => F (g p)) π :=
    fun g hg => Integrable.of_bound (C := M) (hF.comp hg).aestronglyMeasurable
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hFM _)
  rw [← hfst, ← hsnd, integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable hF.aestronglyMeasurable,
    ← integral_sub (hint _ measurable_fst) (hint _ measurable_snd)]
  have hpt : ∀ p : (ι → S) × (ι → S),
      |F p.1 - F p.2| ≤ ∑ x ∈ A, (disagree x).indicator (fun _ => 2 * M) p := by
    intro p
    have hnn : ∀ x ∈ A, 0 ≤ (disagree x).indicator (fun _ => 2 * M) p := fun x _ =>
      Set.indicator_nonneg (fun _ _ => by linarith) _
    by_cases hall : ∀ x ∈ A, p.1 x = p.2 x
    · rw [hdep _ _ hall, sub_self, abs_zero]
      exact Finset.sum_nonneg hnn
    · push Not at hall
      obtain ⟨x, hxA, hx⟩ := hall
      have h1 := abs_le.mp (hFM p.1)
      have h2 := abs_le.mp (hFM p.2)
      have hle : |F p.1 - F p.2| ≤ 2 * M := by
        rw [abs_le]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      refine hle.trans (le_of_eq_of_le ?_ (Finset.single_le_sum hnn hxA))
      rw [Set.indicator_of_mem (show p ∈ disagree x from hx)]
  have hd : ∀ x, 0 ≤ π.real (disagree x) := fun x => measureReal_nonneg
  calc |∫ p, (F p.1 - F p.2) ∂π|
      ≤ ∫ p, |F p.1 - F p.2| ∂π := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := π) (fun p => F p.1 - F p.2)
    _ ≤ ∫ p, ∑ x ∈ A, (disagree x).indicator (fun _ => 2 * M) p ∂π := by
        refine integral_mono ((hint _ measurable_fst).sub (hint _ measurable_snd)).abs ?_ hpt
        exact integrable_finsetSum _ fun x _ => (integrable_const _).indicator (measurableSet_disagree x)
    _ = ∑ x ∈ A, π.real (disagree x) * (2 * M) := by
        rw [integral_finsetSum]
        · exact Finset.sum_congr rfl fun x _ => by
            rw [integral_indicator_const _ (measurableSet_disagree x), smul_eq_mul]
        · exact fun x _ => (integrable_const _).indicator (measurableSet_disagree x)
    _ ≤ ∑ x ∈ A, vmin⁻¹ * (v x * π.real (disagree x)) * (2 * M) := by
        refine Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_right ?_ (by linarith)
        rw [← mul_assoc]
        refine le_mul_of_one_le_left (hd x) ?_
        rw [inv_mul_eq_div, one_le_div hvmin]
        exact hvA x hx
    _ = 2 * M * vmin⁻¹ * ∑ x ∈ A, v x * π.real (disagree x) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ ≤ 2 * M * vmin⁻¹ * phi v π := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by linarith) (inv_nonneg.mpr hvmin.le))
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
          fun x _ _ => mul_nonneg (hv x) (hd x)

/-- **Consequence** (`UV-TV.md` 28.1). For measurable `F` with `|F| ≤ M` depending only on the sites in `A`:
`|∫ F dμ - ∫ F dμ'| ≤ 2 M (min_A v)⁻¹ s/((1 - γ) c_min)`. -/
theorem couplingDS_integral_bound [MeasurableEq S] {μ μ' : Measure (ι → S)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] [Nonempty β] (C : CouplingSpec μ μ' β)
    (good : Finset β) (v : ι → ℝ) (K : β → ι → ℝ) (γ cmin : ℝ)
    (hv : ∀ x, 0 ≤ v x) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hcmin : 0 < cmin) (hc : ∀ x, cmin ≤ coverage C.B x)
    (hI : ∀ b ∈ good, ∀ σ ∈ C.Ω₀, ∀ σ' ∈ C.Ω₀',
      ∑ y ∈ C.B b, v y * (C.Q b (σ, σ')).real (disagree y) ≤
        ∑ z ∈ (C.B b)ᶜ, (disagree z).indicator (fun _ => K b z * v z) (σ, σ'))
    (hK : ∀ z, ∑ b ∈ good.filter (fun b => z ∉ C.B b), K b z ≤ γ * coverage C.B z)
    (A : Finset ι) {vmin : ℝ} (hvmin : 0 < vmin) (hvA : ∀ x ∈ A, vmin ≤ v x)
    {F : (ι → S) → ℝ} (hF : Measurable F) {M : ℝ} (hFM : ∀ σ, |F σ| ≤ M)
    (hdep : ∀ σ σ' : ι → S, (∀ x ∈ A, σ x = σ' x) → F σ = F σ') :
    |∫ σ, F σ ∂μ - ∫ σ, F σ ∂μ'| ≤ 2 * M * vmin⁻¹ * (srcWeight good C.B v / ((1 - γ) * cmin)) := by
  set a := 2 * M * vmin⁻¹
  have ha : 0 ≤ a := by
    obtain ⟨σ⟩ : Nonempty (ι → S) := by
      obtain ⟨σ, -⟩ := nonempty_of_measure_ne_zero (μ := μ) (s := Set.univ) (by simp)
      exact ⟨σ⟩
    have hM : 0 ≤ M := (abs_nonneg _).trans (hFM σ)
    exact mul_nonneg (by linarith) (inv_nonneg.mpr hvmin.le)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hε : 0 < δ / (a + 1) := div_pos hδ (by linarith)
  obtain ⟨π, hπ, hfst, hsnd, -, hΦ⟩ := couplingDS_bound C good v K γ cmin hv hγ0 hγ1 hcmin hc hI hK hε
  have h1 := abs_integral_sub_le_phi hfst hsnd hv A hvmin hvA hF hFM hdep (π := π)
  have h2 : a * (δ / (a + 1)) ≤ δ := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  calc |∫ σ, F σ ∂μ - ∫ σ, F σ ∂μ'| ≤ a * phi v π := h1
    _ ≤ a * (srcWeight good C.B v / ((1 - γ) * cmin) + δ / (a + 1)) := mul_le_mul_of_nonneg_left hΦ ha
    _ ≤ _ := by rw [mul_add]; linarith

end ProofPhase.OneBox
