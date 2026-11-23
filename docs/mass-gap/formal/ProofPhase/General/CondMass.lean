/-
Proof phase, generalisation phase 1b: the conditional-mass route over any gauge group and dimension (2026-11-24).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 1b.
-/

import ProofPhase.General.Setting

/-!
# `CondMass` over any gauge group and dimension

`V3/CondMass` for the Wilson measure of any `Gr` of the package, in dimension `d`: cells of physical size `L₁`
(`CellGeometry`), the named hypothesis `CondMass`, its decay form `CondMassDecay`, and the reductions
`condMassDecay_of_condMass`, `obsTransferPhysT_of_condMassDecay`, `obsTransferPhysT_of_condMass`. The cell count
`K_R = d (2⌊R/L₁ + c₁⌋ + 1)^d` is `card_le_of_siteDist` of phase 1. The cell machinery (`cellLift`, `cellProj`,
`CellDobrushin`, `condCov`) of `V3/CondMass` is group-free and is reused.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity

open ProofPhase.V3 (timeDist timeDist_le_linkDist cellLift cellProj CellDobrushin condCov
  abs_cov_le_of_cellDobrushin abs_condDefect_le_of_ae)
open ProofPhase.UV

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

section CondMass

variable {Gr : Type*} [Group Gr] [TopologicalSpace Gr] [MeasurableSpace Gr] [HasHaarProbability Gr]
  (nr : ℕ) [HasGaugeTrace Gr nr] [GaugeGroupBase Gr] {d : ℕ} [NeZero d]

def CellGeometry (T : Tuning) (cell : ∀ k j, LatticeLink d (T.side k j) → LatticeLink d (coarseSide j))
    (c₀ c₁ : ℝ) : Prop :=
  (∀ k j (e e' : LatticeLink d (T.side k j)),
    T.a k * linkDist e e' ≤ T.L₁ * (linkDist (cell k j e) (cell k j e') + c₀)) ∧
  (∀ k j (e e' : LatticeLink d (T.side k j)),
    T.L₁ * linkDist (cell k j e) (cell k j e') ≤ T.a k * linkDist e e' + T.L₁ * c₁)

def CondMass (T : Tuning) (B : BlockingFamily Gr d T) : Prop :=
  ∃ (cell : ∀ k j, LatticeLink d (T.side k j) → LatticeLink d (coarseSide j)) (c₀ c₁ : ℝ),
    CellGeometry T cell c₀ c₁ ∧
    ∃ (lam γ D₀ : ℝ) (b cmin cmax : ℕ), 0 < lam ∧ 0 ≤ γ ∧ γ < 1 ∧ 1 ≤ cmin ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j,
      ∃ κ : GaugeConnection Gr d (coarseSide j) → Measure (GaugeConnection Gr d (T.side k j)),
        (∀ y, IsProbabilityMeasure (κ y)) ∧
        (∀ H : GaugeConnection Gr d (T.side k j) → ℝ, Measurable H → (∀ U, |H U| ≤ 1) →
          condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) H =ᵐ[(ymLaw (G := Gr) nr d T k j)]
            fun U => ∫ V, H V ∂(κ ((B k j).B U))) ∧
        ∀ᵐ y ∂(blockedLaw nr T B k j), CellDobrushin (κ y) (cell k j) (1 : Gr) linkDist lam γ D₀ b cmin cmax

def CondMassDecay (T : Tuning) (B : BlockingFamily Gr d T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection Gr d (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink d (T.side k j))) (D : ℝ),
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → DepOn F A₀ → DepOn G B₀ →
    PhysExtent T k A₀ R → (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * linkDist e e') →
    ∀ᵐ U ∂(ymLaw (G := Gr) nr d T k j),
      |condCov (ymLaw (G := Gr) nr d T k j) (MeasurableSpace.comap (B k j).B inferInstance) F G U| ≤ c * Real.exp (-(m * D))

variable [GaugeRep Gr nr]

theorem condMassDecay_of_condMass {T : Tuning} {B : BlockingFamily Gr d T} (h : CondMass nr T B) : CondMassDecay nr T B := by
  obtain ⟨cell, c₀, c₁, ⟨geo1, geo2⟩, lam, γ, D₀, b, cmin, cmax, hlam, hγ0, hγ1, hc1, k₀, H⟩ := h
  have hL1 := T.L₁_pos
  refine ⟨lam / T.L₁, by positivity, fun R => ?_⟩
  set r : ℕ := ⌊R / T.L₁ + c₁⌋₊
  set K : ℝ := ((d * (2 * r + 1) ^ d : ℕ) : ℝ)
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have hcm : (1 : ℝ) ≤ cmin := by exact_mod_cast hc1
  have hpre : 0 ≤ (b : ℝ) / (cmin * (1 - γ)) :=
    div_nonneg (Nat.cast_nonneg _) (mul_nonneg (by linarith) (by linarith))
  set c := (b : ℝ) / (cmin * (1 - γ)) * (cmax * (2 * K)) * 2 * Real.exp (lam * (c₀ + D₀))
  have hc : 0 ≤ c := by positivity
  refine ⟨c, hc, k₀, fun k hk j F G A₀ B₀ D mF mG bF bG dF dG eA hsep => ?_⟩
  obtain ⟨κ, hprob, hce, hae⟩ := H k hk j
  have := isProbabilityMeasure_wilsonMeasure (G := Gr) (n := nr) d (T.side k j) (T.β k)
  have hae' : ∀ᵐ U ∂(ymLaw (G := Gr) nr d T k j), CellDobrushin (κ ((B k j).B U)) (cell k j) (1 : Gr) linkDist lam γ D₀ b cmin cmax :=
    ae_of_ae_map (B k j).meas.aemeasurable hae
  have bFG : ∀ U, |F U * G U| ≤ 1 := fun U => by
    rw [abs_mul]; exact (mul_le_mul (bF U) (bG U) (abs_nonneg _) zero_le_one).trans (by norm_num)
  -- the cells met by `F`
  have hcard : (((A₀.image (cell k j)).card : ℕ) : ℝ) ≤ K := by
    have hsd : ∀ x ∈ A₀.image (cell k j), ∀ x' ∈ A₀.image (cell k j), siteDist x.site x'.site ≤ r := by
      intro x hx x' hx'
      obtain ⟨e, he, rfl⟩ := mem_image.1 hx
      obtain ⟨e', he', rfl⟩ := mem_image.1 hx'
      have h1 := geo2 k j e e'
      have h2 := eA e he e' he'
      have h3 : linkDist (cell k j e) (cell k j e') ≤ R / T.L₁ + c₁ := by
        rw [div_add' _ _ _ hL1.ne', le_div_iff₀ hL1]; nlinarith
      exact Nat.le_floor (by exact_mod_cast h3)
    have hc := card_le_of_siteDist hsd
    simp only [K]
    exact_mod_cast hc
  have hR : ∀ a ∈ A₀, ∀ a' ∈ B₀, D / T.L₁ - c₀ ≤ linkDist (cell k j a) (cell k j a') := by
    intro a ha a' ha'
    have h1 := geo1 k j a a'
    have h2 := hsep a ha a' ha'
    rw [sub_le_iff_le_add, div_le_iff₀ hL1]
    nlinarith
  filter_upwards [hae', hce (fun U => F U * G U) (mF.mul mG) bFG, hce F mF bF, hce G mG bG] with U hU h1 h2 h3
  unfold condCov
  rw [h1, h2, h3]
  have := hprob ((B k j).B U)
  have : Nonempty (LatticeLink d (coarseSide j)) := ⟨⟨fun _ => 1, ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩⟩
  have hcov := abs_cov_le_of_cellDobrushin (κ ((B k j).B U)) linkDist_self linkDist_triangle hlam.le hγ0 hγ1 hc1
    hU mF mG bF bG dF dG hR
  refine hcov.trans ?_
  have eexp : Real.exp (-(lam * (D / T.L₁ - c₀ - D₀))) =
      Real.exp (lam * (c₀ + D₀)) * Real.exp (-(lam / T.L₁ * D)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [eexp]
  have hcK : (cmax : ℝ) * (2 * ((A₀.image (cell k j)).card : ℝ)) ≤ cmax * (2 * K) :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  calc (b : ℝ) / (cmin * (1 - γ)) * (cmax * (2 * ((A₀.image (cell k j)).card : ℝ))) * 2 *
        (Real.exp (lam * (c₀ + D₀)) * Real.exp (-(lam / T.L₁ * D)))
      ≤ (b : ℝ) / (cmin * (1 - γ)) * (cmax * (2 * K)) * 2 *
        (Real.exp (lam * (c₀ + D₀)) * Real.exp (-(lam / T.L₁ * D))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcK hpre) (by norm_num))
          (by positivity)
    _ = c * Real.exp (-(lam / T.L₁ * D)) := by simp only [c]; ring

theorem obsTransferPhysT_of_condMassDecay {T : Tuning} {B : BlockingFamily Gr d T} (h1 : CondMassDecay nr T B)
    (h2 : ObsQuasiLocT nr T B) : ObsTransferPhysT nr T B := by
  obtain ⟨m₁, hm₁, H1⟩ := h1
  obtain ⟨m₂, hm₂, H2⟩ := h2
  refine ⟨min m₁ m₂, lt_min hm₁ hm₂, fun R => ?_⟩
  obtain ⟨c₁, hc₁, k₁, Hk1⟩ := H1 R
  obtain ⟨c₂, K, hc₂, k₂, Hk2⟩ := H2 R
  refine ⟨c₁ + c₂, K, by positivity, max k₁ k₂,
    fun k hk j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eA eB hsep => ?_⟩
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hv, hsep', hEF, hEG⟩ :=
    Hk2 k ((le_max_right _ _).trans hk) j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eA eB hsep
  have hae := Hk1 k ((le_max_left _ _).trans hk) j F G A₀ B₀ D mF mG bF bG dF dG eA
    (fun e he e' he' => (hsep e he e' he').trans
      (mul_le_mul_of_nonneg_left (timeDist_le_linkDist e e') (T.a_pos k).le))
  have := isProbabilityMeasure_wilsonMeasure (G := Gr) (n := nr) d (T.side k j) (T.β k)
  have hdec := abs_condDefect_le_of_ae (B k j).meas.comap_le (UV.Bdd1.of_measurable mF bF)
    (UV.Bdd1.of_measurable mG bG) hae
  have hE1 : Real.exp (-(m₁ * D)) ≤ Real.exp (-(min m₁ m₂ * D)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left m₁ m₂])
  have hE2 : Real.exp (-(m₂ * D)) ≤ Real.exp (-(min m₁ m₂ * D)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right m₁ m₂])
  have hx := Real.exp_pos (-(min m₁ m₂ * D))
  refine ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hv, hsep', ?_, ?_, ?_⟩
  · refine hEF.trans ?_
    calc c₂ * Real.exp (-(m₂ * D)) ≤ c₂ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE2 hc₂
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le
  · refine hEG.trans ?_
    calc c₂ * Real.exp (-(m₂ * D)) ≤ c₂ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE2 hc₂
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le
  · refine hdec.trans ?_
    calc c₁ * Real.exp (-(m₁ * D)) ≤ c₁ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE1 hc₁
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le

theorem obsTransferPhysT_of_condMass {T : Tuning} {B : BlockingFamily Gr d T} (h1 : CondMass nr T B)
    (h2 : ObsQuasiLocT nr T B) : ObsTransferPhysT nr T B :=
  obsTransferPhysT_of_condMassDecay nr (condMassDecay_of_condMass nr h1) h2

end CondMass


/-! ## The SU(2), `d = 4` instances -/

section Instance

variable (T : Tuning) (B : ProofPhase.BlockingFamily T)

theorem condMass_iff : ProofPhase.V3.CondMass T B ↔ CondMass (Gr := SU2) 2 (d := 4) T B := Iff.rfl

theorem condMassDecay_iff : ProofPhase.V3.CondMassDecay T B ↔ CondMassDecay (Gr := SU2) 2 (d := 4) T B := Iff.rfl

theorem cellGeometry_iff
    (cell : ∀ k j, LatticeLink 4 (T.side k j) → LatticeLink 4 (coarseSide j)) (c₀ c₁ : ℝ) :
    ProofPhase.V3.CellGeometry T cell c₀ c₁ ↔ CellGeometry T cell c₀ c₁ := Iff.rfl

/-- `ProofPhase.V3.condMassDecay_of_condMass` from the generic theorem. -/
theorem condMassDecay_of_condMass_su2 {T : Tuning} {B : ProofPhase.BlockingFamily T}
    (h : ProofPhase.V3.CondMass T B) : ProofPhase.V3.CondMassDecay T B :=
  condMassDecay_of_condMass (Gr := SU2) 2 (d := 4) h

/-- `ProofPhase.V3.obsTransferPhysT_of_condMassDecay` from the generic theorem. -/
theorem obsTransferPhysT_of_condMassDecay_su2 {T : Tuning} {B : ProofPhase.BlockingFamily T}
    (h1 : ProofPhase.V3.CondMassDecay T B) (h2 : ProofPhase.V3.ObsQuasiLocT T B) :
    ProofPhase.V3.ObsTransferPhysT T B :=
  obsTransferPhysT_of_condMassDecay (Gr := SU2) 2 (d := 4) h1 h2

/-- `ProofPhase.V3.obsTransferPhysT_of_condMass` from the generic theorem. -/
theorem obsTransferPhysT_of_condMass_su2 {T : Tuning} {B : ProofPhase.BlockingFamily T}
    (h1 : ProofPhase.V3.CondMass T B) (h2 : ProofPhase.V3.ObsQuasiLocT T B) :
    ProofPhase.V3.ObsTransferPhysT T B :=
  obsTransferPhysT_of_condMass (Gr := SU2) 2 (d := 4) h1 h2

example : @ProofPhase.V3.condMassDecay_of_condMass = @condMassDecay_of_condMass_su2 := rfl
example : @ProofPhase.V3.obsTransferPhysT_of_condMassDecay = @obsTransferPhysT_of_condMassDecay_su2 := rfl
example : @ProofPhase.V3.obsTransferPhysT_of_condMass = @obsTransferPhysT_of_condMass_su2 := rfl

end Instance

end ProofPhase.General
