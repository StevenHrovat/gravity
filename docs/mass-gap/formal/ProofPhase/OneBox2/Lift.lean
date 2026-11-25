/-
Proof phase, cycle 8, workstream 3 (c8c-concrete): lifting a block specification from fine links to cells
(2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c8c-concrete/NOTE.md`, section 1.
-/

import ProofPhase.OneBox.Fine

/-!
# Lifting a fine block specification to cells

`liftSpec`: a specification `q` of a block `Bf` of fine links (a measure on fine configurations) becomes a specification
of a block `b` of cells (a measure on regrouped configurations `C → (L → S)`), provided every link of `Bf` lies in a
cell of `b`.  The cells of `b` that are only partly covered by `Bf` (cells cut by a wall) get the frozen reference
values `ρ` on their links outside `Bf`.

* `liftBlockSpec`: a `BlockSpec` of the fine law `μ` becomes a `BlockSpec` of the lifted law `μ ∘ cellLift⁻¹`: the
  DLR identity is the fine DLR identity applied to `h ∘ cellLift` (`dlr` field), measurability of block averages comes
  from the measurability of the fine specification as a measure-valued map, and the dependence only off the block
  needs the fine specification to ignore the links of the block's cells that are not in `Bf` (automatic when `Bf` is
  the full preimage of `b`).
* `liftSpec_covariant`: the lift of a covariant specification is covariant for the lifted action (`liftAct`), when
  `Bf` is the full preimage of `b`.
-/

open MeasureTheory Finset OneScale ProofPhase.V3 ProofPhase.OneBox

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.OneBox2

/-- **Measurable dependence of an integral on a parameter through the kernel** (a measure-valued measurable map). -/
theorem measurable_integral_spec {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {q : X → Measure Y}
    (hq : Measurable q) [∀ x, IsProbabilityMeasure (q x)] {f : X × Y → ℝ} (hf : Measurable f) :
    Measurable (fun x => ∫ y, f (x, y) ∂(q x)) := by
  have : ProbabilityTheory.IsMarkovKernel (⟨q, hq⟩ : ProbabilityTheory.Kernel X Y) := ⟨fun x => inferInstance⟩
  exact (hf.stronglyMeasurable.integral_kernel_prod_right' (κ := (⟨q, hq⟩ : ProbabilityTheory.Kernel X Y))).measurable

section Lift

variable {L C S : Type*} [Fintype L] [DecidableEq L] [Fintype C] [DecidableEq C] [MeasurableSpace S]

theorem splice_splice_right {ι S' : Type*} [DecidableEq ι] (B : Finset ι) (σ ξ ξ' : ι → S') :
    splice B σ (splice B ξ ξ') = splice B σ ξ' := by
  funext i; by_cases h : i ∈ B <;> simp [splice, h]

/-- The map from a fine block configuration to a configuration of cells: the block `b` takes the regrouped values,
the rest is the boundary `W`. -/
def liftMap (cell : L → C) (s₀ : S) (b : Finset C) (Bf : Finset L) (ρ : L → S) (W : C → (L → S)) (U' : L → S) :
    C → (L → S) :=
  splice b W (cellLift cell s₀ (splice Bf ρ U'))

theorem measurable_liftMap_prod (cell : L → C) (s₀ : S) (b : Finset C) (Bf : Finset L) (ρ : L → S) :
    Measurable (fun p : (C → (L → S)) × (L → S) => liftMap cell s₀ b Bf ρ p.1 p.2) :=
  (measurable_splice b).comp (measurable_fst.prodMk
    ((measurable_cellLift cell s₀).comp ((measurable_splice_right Bf ρ).comp measurable_snd)))

theorem measurable_liftMap (cell : L → C) (s₀ : S) (b : Finset C) (Bf : Finset L) (ρ : L → S)
    (W : C → (L → S)) : Measurable (liftMap cell s₀ b Bf ρ W) :=
  (measurable_liftMap_prod cell s₀ b Bf ρ).comp (measurable_const.prodMk measurable_id)

/-- The lifted specification. -/
def liftSpec (cell : L → C) (s₀ : S) (b : Finset C) (Bf : Finset L) (ρ : L → S)
    (q : (L → S) → Measure (L → S)) (W : C → (L → S)) : Measure (C → (L → S)) :=
  (q (cellProj cell W)).map (liftMap cell s₀ b Bf ρ W)

theorem blockAvg_liftSpec (cell : L → C) (s₀ : S) (b : Finset C) (Bf : Finset L) (ρ : L → S)
    (q : (L → S) → Measure (L → S)) {h : (C → (L → S)) → ℝ} (hh : BM h) (W : C → (L → S)) :
    blockAvg b (liftSpec cell s₀ b Bf ρ q) h W =
      ∫ U', h (liftMap cell s₀ b Bf ρ W U') ∂(q (cellProj cell W)) := by
  unfold blockAvg liftSpec
  rw [integral_map (f := fun ξ => h (splice b W ξ)) (measurable_liftMap cell s₀ b Bf ρ W).aemeasurable
    (hh.meas.comp (measurable_splice_right b W)).aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U' => ?_)
  simp only [liftMap]
  rw [splice_splice_right]

theorem measurable_blockAvg_liftSpec (cell : L → C) (s₀ : S) (b : Finset C) (Bf : Finset L) (ρ : L → S)
    (q : (L → S) → Measure (L → S)) (hq : Measurable q) [∀ σ, IsProbabilityMeasure (q σ)]
    {h : (C → (L → S)) → ℝ} (hh : BM h) : Measurable (blockAvg b (liftSpec cell s₀ b Bf ρ q) h) := by
  have e : blockAvg b (liftSpec cell s₀ b Bf ρ q) h = fun W =>
      ∫ U', (fun p : (C → (L → S)) × (L → S) => h (liftMap cell s₀ b Bf ρ p.1 p.2)) (W, U') ∂(q (cellProj cell W)) := by
    funext W; exact blockAvg_liftSpec cell s₀ b Bf ρ q hh W
  rw [e]
  exact measurable_integral_spec (q := fun W => q (cellProj cell W)) (hq.comp (measurable_cellProj cell))
    (hh.meas.comp (measurable_liftMap_prod cell s₀ b Bf ρ))

/-- The key identity behind the DLR property of the lift. -/
theorem lift_splice_eq (cell : L → C) (s₀ : S) (b : Finset C) (Bf : Finset L) (ρ U U' : L → S)
    (hsub : ∀ e ∈ Bf, cell e ∈ b) (hfr : ∀ e, cell e ∈ b → e ∉ Bf → U e = ρ e) :
    splice b (cellLift cell s₀ U) (cellLift cell s₀ (splice Bf ρ U')) = cellLift cell s₀ (splice Bf U U') := by
  funext c e
  by_cases hc : c ∈ b
  · simp only [splice, hc, ite_true, cellLift]
    by_cases hce : cell e = c
    · simp only [hce, ite_true]
      by_cases he : e ∈ Bf
      · simp [splice, he]
      · simp only [splice, he, ite_false]
        exact (hfr e (hce ▸ hc) he).symm
    · simp [hce]
  · simp only [splice, hc, ite_false, cellLift]
    by_cases hce : cell e = c
    · simp only [hce, ite_true]
      have : e ∉ Bf := fun he => hc (hce ▸ hsub e he)
      simp [splice, this]
    · simp [hce]

/-- **A fine block specification lifted to cells.** -/
def liftBlockSpec {J : Type*} {μ : Measure (L → S)} [IsProbabilityMeasure μ] (P : BlockSpec μ J)
    (cell : L → C) (s₀ : S) (b : J → Finset C) (ρ : L → S)
    (hsub : ∀ j, ∀ e ∈ P.block j, cell e ∈ b j)
    (hq : ∀ j, Measurable (P.spec j))
    (hcongr : ∀ j (σ σ' : L → S), (∀ e, cell e ∉ b j → σ e = σ' e) → P.spec j σ = P.spec j σ')
    (hfrozen : ∀ j, ∀ᵐ U ∂μ, ∀ e, cell e ∈ b j → e ∉ P.block j → U e = ρ e) :
    BlockSpec (μ.map (cellLift cell s₀)) J where
  block := b
  spec j := liftSpec cell s₀ (b j) (P.block j) ρ (P.spec j)
  isProb j W := by
    have := P.isProb j (cellProj cell W)
    exact (Measure.isProbabilityMeasure_map_iff
      (measurable_liftMap cell s₀ (b j) (P.block j) ρ W).aemeasurable).2 inferInstance
  spec_congr j W W' h := by
    have e1 : P.spec j (cellProj cell W) = P.spec j (cellProj cell W') :=
      hcongr j _ _ (fun e he => by simp only [cellProj]; rw [h _ he])
    have e2 : liftMap cell s₀ (b j) (P.block j) ρ W = liftMap cell s₀ (b j) (P.block j) ρ W' :=
      funext fun U' => splice_congr_left h _
    simp only [liftSpec]
    rw [e1, e2]
  meas_avg j h hh := by
    have := fun σ => P.isProb j σ
    exact measurable_blockAvg_liftSpec cell s₀ (b j) (P.block j) ρ (P.spec j) (hq j) hh
  dlr j h hh := by
    have := fun σ => P.isProb j σ
    have hcl : BM (fun U => h (cellLift cell s₀ U)) :=
      ⟨hh.meas.comp (measurable_cellLift cell s₀), hh.bdd.imp fun C hC U => hC _⟩
    have hav : Measurable (blockAvg (b j) (liftSpec cell s₀ (b j) (P.block j) ρ (P.spec j)) h) :=
      measurable_blockAvg_liftSpec cell s₀ (b j) (P.block j) ρ (P.spec j) (hq j) hh
    have hav' : BM (blockAvg (b j) (liftSpec cell s₀ (b j) (P.block j) ρ (P.spec j)) h) := by
      obtain ⟨C, hC⟩ := hh.bdd
      refine ⟨hav, C, fun W => ?_⟩
      rw [blockAvg_liftSpec cell s₀ _ _ ρ _ hh]
      have := norm_integral_le_of_norm_le_const (μ := P.spec j (cellProj cell W))
        (f := fun U' => h (liftMap cell s₀ (b j) (P.block j) ρ W U')) (C := C)
        (Filter.Eventually.of_forall fun U' => by rw [Real.norm_eq_abs]; exact hC _)
      simpa using this
    rw [integral_map (measurable_cellLift cell s₀).aemeasurable hav.aestronglyMeasurable,
      integral_map (measurable_cellLift cell s₀).aemeasurable hh.meas.aestronglyMeasurable]
    have := P.dlr j (fun U => h (cellLift cell s₀ U)) hcl
    rw [← this]
    refine integral_congr_ae ?_
    filter_upwards [hfrozen j] with U hU
    rw [blockAvg_liftSpec cell s₀ _ _ ρ _ hh, cellProj_cellLift]
    unfold blockAvg
    refine integral_congr_ae (Filter.Eventually.of_forall fun U' => ?_)
    simp only [liftMap]
    rw [lift_splice_eq cell s₀ (b j) (P.block j) ρ U U' (hsub j) hU]

/-! ### Covariance of the lift -/

variable {Γ : Type*}

theorem cellLift_act (cell : L → C) (s₀ : S) (α : Γ → L → S → S) (γ : Γ)
    (U : L → S) : cellLift cell s₀ (act α γ U) = act (liftAct cell α) γ (cellLift cell s₀ U) := by
  funext c e
  by_cases h : cell e = c <;> simp [cellLift, act, liftAct, h]

/-- When `Bf` is the full preimage of `b`, the reference `ρ` plays no role. -/
theorem liftMap_eq_full (cell : L → C) (s₀ : S) (b : Finset C) (Bf : Finset L) (ρ : L → S)
    (hBf : ∀ e, e ∈ Bf ↔ cell e ∈ b) (W : C → (L → S)) (U : L → S) :
    liftMap cell s₀ b Bf ρ W U = splice b W (cellLift cell s₀ U) := by
  funext c e
  by_cases hc : c ∈ b
  · simp only [liftMap, splice, hc, ite_true, cellLift]
    by_cases hce : cell e = c
    · have : e ∈ Bf := (hBf e).2 (hce ▸ hc)
      simp [hce, this]
    · simp [hce]
  · simp [liftMap, splice, hc]

/-- **The lift of a covariant specification is covariant** (for the lifted action), when the fine block is the full
preimage of the cell block. -/
theorem liftSpec_covariant (α : Γ → L → S → S) (hα : ∀ γ e, Measurable (α γ e))
    (cell : L → C) (s₀ : S) (b : Finset C) (Bf : Finset L) (ρ : L → S)
    (q : (L → S) → Measure (L → S)) (hq : SpecCovariant α q) (hBf : ∀ e, e ∈ Bf ↔ cell e ∈ b) :
    SpecCovariant (liftAct cell α) (liftSpec cell s₀ b Bf ρ q) := by
  intro γ W
  unfold liftSpec
  rw [cellProj_act, hq γ (cellProj cell W),
    Measure.map_map (measurable_liftMap cell s₀ b Bf ρ _) (measurable_act hα γ),
    Measure.map_map (measurable_act (measurable_liftAct cell hα) γ) (measurable_liftMap cell s₀ b Bf ρ W)]
  congr 1
  funext U'
  simp only [Function.comp]
  rw [liftMap_eq_full cell s₀ b Bf ρ hBf, liftMap_eq_full cell s₀ b Bf ρ hBf, cellLift_act, splice_act]

end Lift

end ProofPhase.OneBox2
