/-
Proof phase, generalisation phase 1c: conditional-mass inputs to the time-separated transfer over any gauge group and
dimension (2026-11-24). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 1c.
-/

import ProofPhase.General.W1
import ProofPhase.V3.CondInputs

/-!
# The conditional-mass inputs, over any gauge group and dimension

`V3/CondInputs` for the Wilson measure of any `Gr` of the package in dimension `d`: the time-separation predicate `sepT`,
the annealed hypothesis `CondMassAnn`, and the reductions `condMassAnn_of_condMassDecay`, `condDecouple_of_condMassAnn`,
`condDecouple_of_condMass`, `obsTransferPhysT_of_condDecouple`, `obsTransferPhysTW_of_condDecouple`,
`condDecouple_of_obsTransferPhysT` (they connect `CondMass`, `Seg2`'s `CondDecouple` and the transfer hypotheses).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity

open ProofPhase.V3 (timeDist timeDist_le_linkDist condCov condDefect_eq_integral_condCov abs_condDefect_le_of_ae)
open ProofPhase.UV

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

section CondInputs

variable {Gr : Type*} [Group Gr] [TopologicalSpace Gr] [MeasurableSpace Gr] [HasHaarProbability Gr]
  (nr : ℕ) [HasGaugeTrace Gr nr] [GaugeGroupBase Gr] {d : ℕ} [NeZero d] (cost : Gr → Gr → ℝ)

section Sep

variable (d)

def sepT (T : Tuning) : SepPred d T :=
  fun k _ A₀ B₀ D => 0 ≤ D ∧ ∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * timeDist e e'

end Sep

def CondMassAnn (T : Tuning) (B : BlockingFamily Gr d T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection Gr d (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink d (T.side k j))) (D : ℝ),
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R → sepT d T k j A₀ B₀ D →
    ∫ U, |condCov (ymLaw (G := Gr) nr d T k j) (MeasurableSpace.comap (B k j).B inferInstance) F G U| ∂(ymLaw (G := Gr) nr d T k j)
      ≤ c * Real.exp (-(m * D))

variable [GaugeRep Gr nr]

theorem condMassAnn_of_condMassDecay {T : Tuning} {B : BlockingFamily Gr d T} (h : CondMassDecay nr T B) :
    CondMassAnn nr T B := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, hc, k₀, Hk⟩ := H R
  refine ⟨c, hc, k₀, fun k hk j F G A₀ B₀ D mF mG bF bG _ _ dF dG eA _ hsep => ?_⟩
  have := isProbabilityMeasure_wilsonMeasure (G := Gr) (n := nr) d (T.side k j) (T.β k)
  have hae := Hk k hk j F G A₀ B₀ D mF mG bF bG dF dG eA
    (fun e he e' he' => (hsep.2 e he e' he').trans
      (mul_le_mul_of_nonneg_left (timeDist_le_linkDist e e') (T.a_pos k).le))
  have h2 := norm_integral_le_of_norm_le_const (μ := (ymLaw (G := Gr) nr d T k j))
    (f := fun U => |condCov (ymLaw (G := Gr) nr d T k j) (MeasurableSpace.comap (B k j).B inferInstance) F G U|)
    (C := c * Real.exp (-(m * D))) (hae.mono fun U hU => by rwa [Real.norm_eq_abs, abs_abs])
  have h3 : |∫ U, |condCov (ymLaw (G := Gr) nr d T k j) (MeasurableSpace.comap (B k j).B inferInstance) F G U| ∂(ymLaw (G := Gr) nr d T k j)| ≤
      c * Real.exp (-(m * D)) := by simpa using h2
  exact (le_abs_self _).trans h3

theorem condDecouple_of_condMassAnn {T : Tuning} {B : BlockingFamily Gr d T} (h : CondMassAnn nr T B) :
    CondDecouple nr B (sepT d T) := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, hc, k₀, Hk⟩ := H R
  refine ⟨c, hc, k₀, fun k hk j F G A₀ B₀ D mF mG bF bG gF gG dF dG eA eB hS => ?_⟩
  have := isProbabilityMeasure_wilsonMeasure (G := Gr) (n := nr) d (T.side k j) (T.β k)
  rw [condDefect_eq_integral_condCov (B k j).meas.comap_le (Bdd1.of_measurable mF bF)
    (Bdd1.of_measurable mG bG)]
  exact abs_integral_le_integral_abs.trans (Hk k hk j F G A₀ B₀ D mF mG bF bG gF gG dF dG eA eB hS)

theorem condDecouple_of_condMass {T : Tuning} {B : BlockingFamily Gr d T} (h : CondMass nr T B) :
    CondDecouple nr B (sepT d T) :=
  condDecouple_of_condMassAnn nr (condMassAnn_of_condMassDecay nr (condMassDecay_of_condMass nr h))

theorem obsTransferPhysT_of_condDecouple {T : Tuning} {B : BlockingFamily Gr d T} (h1 : CondDecouple nr B (sepT d T))
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
  have hdec := Hk1 k ((le_max_left _ _).trans hk) j F G A₀ B₀ D mF mG bF bG gF gG dF dG eA eB ⟨hD, hsep⟩
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

theorem obsTransferPhysTW_of_condDecouple {T : Tuning} {B : BlockingFamily Gr d T} (h1 : CondDecouple nr B (sepT d T))
    (h2 : ObsQuasiLocTW nr cost T B) : ObsTransferPhysTW nr cost T B := by
  obtain ⟨m₁, hm₁, H1⟩ := h1
  obtain ⟨m₂, hm₂, H2⟩ := h2
  refine ⟨min m₁ m₂, lt_min hm₁ hm₂, fun R => ?_⟩
  obtain ⟨c₁, hc₁, k₁, Hk1⟩ := H1 R
  obtain ⟨c₂, K, hc₂, hK, k₂, Hk2⟩ := H2 R
  refine ⟨c₁ + c₂, K, by positivity, hK, max k₁ k₂,
    fun k hk j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eA eB hsep => ?_⟩
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hv, hlip, hsep', hEF, hEG⟩ :=
    Hk2 k ((le_max_right _ _).trans hk) j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eA eB hsep
  have hdec := Hk1 k ((le_max_left _ _).trans hk) j F G A₀ B₀ D mF mG bF bG gF gG dF dG eA eB ⟨hD, hsep⟩
  have hE1 : Real.exp (-(m₁ * D)) ≤ Real.exp (-(min m₁ m₂ * D)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left m₁ m₂])
  have hE2 : Real.exp (-(m₂ * D)) ≤ Real.exp (-(min m₁ m₂ * D)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right m₁ m₂])
  have hx := Real.exp_pos (-(min m₁ m₂ * D))
  refine ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hv, hlip, hsep', ?_, ?_, ?_⟩
  · refine hEF.trans ?_
    calc c₂ * Real.exp (-(m₂ * D)) ≤ c₂ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE2 hc₂
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le
  · refine hEG.trans ?_
    calc c₂ * Real.exp (-(m₂ * D)) ≤ c₂ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE2 hc₂
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le
  · refine hdec.trans ?_
    calc c₁ * Real.exp (-(m₁ * D)) ≤ c₁ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE1 hc₁
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le

theorem condDecouple_of_obsTransferPhysT {T : Tuning} {B : BlockingFamily Gr d T} (h : ObsTransferPhysT nr T B) :
    CondDecouple nr B (sepT d T) := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, K, hc, k₀, Hk⟩ := H R
  refine ⟨c, hc, k₀, fun k hk j F G A₀ B₀ D mF mG bF bG gF gG dF dG eA eB hS => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hdec⟩ :=
    Hk k hk j F G A₀ B₀ D hS.1 mF mG bF bG gF gG dF dG eA eB hS.2
  exact hdec

end CondInputs

/-! ## The SU(2), `d = 4` instances -/

section Instance

open ProofPhase.Certified (geodSU2)

variable {T : Tuning} {B : ProofPhase.BlockingFamily T}

theorem sepT_four (T : Tuning) : ProofPhase.V3.sepT T = sepT 4 T := rfl

theorem condMassAnn_iff (T : Tuning) (B : ProofPhase.BlockingFamily T) :
    ProofPhase.V3.CondMassAnn T B ↔ CondMassAnn (Gr := SU2) 2 (d := 4) T B := Iff.rfl

/-- `ProofPhase.V3.condMassAnn_of_condMassDecay` from the generic theorem. -/
theorem condMassAnn_of_condMassDecay_su2 (h : ProofPhase.V3.CondMassDecay T B) : ProofPhase.V3.CondMassAnn T B :=
  condMassAnn_of_condMassDecay (Gr := SU2) 2 (d := 4) h

/-- `ProofPhase.V3.condDecouple_of_condMassAnn` from the generic theorem. -/
theorem condDecouple_of_condMassAnn_su2 (h : ProofPhase.V3.CondMassAnn T B) :
    ProofPhase.Seg2.CondDecouple T B (ProofPhase.V3.sepT T) :=
  condDecouple_of_condMassAnn (Gr := SU2) 2 (d := 4) h

/-- `ProofPhase.V3.condDecouple_of_condMass` from the generic theorem. -/
theorem condDecouple_of_condMass_su2 (h : ProofPhase.V3.CondMass T B) :
    ProofPhase.Seg2.CondDecouple T B (ProofPhase.V3.sepT T) :=
  condDecouple_of_condMass (Gr := SU2) 2 (d := 4) h

/-- `ProofPhase.V3.obsTransferPhysT_of_condDecouple` from the generic theorem. -/
theorem obsTransferPhysT_of_condDecouple_su2 (h1 : ProofPhase.Seg2.CondDecouple T B (ProofPhase.V3.sepT T))
    (h2 : ProofPhase.V3.ObsQuasiLocT T B) : ProofPhase.V3.ObsTransferPhysT T B :=
  obsTransferPhysT_of_condDecouple (Gr := SU2) 2 (d := 4) h1 h2

/-- `ProofPhase.V3.obsTransferPhysTW_of_condDecouple` from the generic theorem. -/
theorem obsTransferPhysTW_of_condDecouple_su2 (h1 : ProofPhase.Seg2.CondDecouple T B (ProofPhase.V3.sepT T))
    (h2 : ProofPhase.V3.ObsQuasiLocTW T B) : ProofPhase.V3.ObsTransferPhysTW T B :=
  obsTransferPhysTW_of_condDecouple (Gr := SU2) 2 (d := 4) geodSU2 h1 h2

/-- `ProofPhase.V3.condDecouple_of_obsTransferPhysT` from the generic theorem. -/
theorem condDecouple_of_obsTransferPhysT_su2 (h : ProofPhase.V3.ObsTransferPhysT T B) :
    ProofPhase.Seg2.CondDecouple T B (ProofPhase.V3.sepT T) :=
  condDecouple_of_obsTransferPhysT (Gr := SU2) 2 (d := 4) h

end Instance

end ProofPhase.General
