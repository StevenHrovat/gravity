/-
Proof phase, generalisation phase 1b: the Wilson one-box criterion with the actual box kernel, over any gauge group and
dimension (2026-11-24). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 1b.
-/

import ProofPhase.General.Wilson
import ProofPhase.OneBox2.Concrete

/-!
# The Wilson one-box criterion with the actual box law, over any gauge group

`OneBox2/Concrete` for any `Gr` of the package in dimension `d`: the Wilson box kernel regrouped by cells
(`wilsonBoxSpec`), the block specification by the boxes `Λ₀ + t` (`wilsonBlockSpec`), its gauge covariance, the
criterion `WilsonOneBox` and `fineOneBox_of_wilsonOneBox`. The lifting machinery of `OneBox2/Lift` is group-free and
reused. The assembly `yang_mills_assembly_wilsonOneBox` is not ported (it needs `OnLCP'`, `NonTrivial`).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity

open ProofPhase.OneBox (act ActInv SpecCovariant measurable_act splice_act liftAct OneBoxSum ActAdm IsInfluenceBoundOn)
open ProofPhase.OneBox2 (liftSpec liftBlockSpec liftSpec_covariant)
open ProofPhase.V3 (cellLift)

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

section Concrete

variable {Gr : Type*} [Group Gr] [TopologicalSpace Gr] [MeasurableSpace Gr] [HasHaarProbability Gr]
  (nr : ℕ) [HasGaugeTrace Gr nr] [GaugeGroupBase Gr] [GaugeRep Gr nr] {d : ℕ} [NeZero d]

section Spec

variable (Gr) {N M : ℕ} [NeZero N] [NeZero M]

def cellPre (cell : LatticeLink d N → LatticeLink d M) (b : Finset (LatticeLink d M)) : Finset (LatticeLink d N) :=
  univ.filter fun e => cell e ∈ b

theorem mem_cellPre {cell : LatticeLink d N → LatticeLink d M} {b : Finset (LatticeLink d M)} {e : LatticeLink d N} :
    e ∈ cellPre cell b ↔ cell e ∈ b := by simp [cellPre]

def wilsonBoxSpec (cell : LatticeLink d N → LatticeLink d M) (β : ℝ) (b : Finset (LatticeLink d M)) :
    (LatticeLink d M → (LatticeLink d N → Gr)) → Measure (LatticeLink d M → (LatticeLink d N → Gr)) :=
  liftSpec cell (1 : Gr) b (cellPre cell b) (fun _ => 1)
    (gaugeSpec (G := Gr) (d := d) (N := N) nr (wilsonWeight β) (cellPre cell b))

def wilsonBlockSpec (cell : LatticeLink d N → LatticeLink d M) (β : ℝ) (Λ₀ : Finset (FinLatticeSites d M)) :
    BlockSpec ((wilsonMeasure Gr nr β d N).map (cellLift cell (1 : Gr))) (FinLatticeSites d M) :=
  have : IsProbabilityMeasure (gaugeMeasure (d := d) (N := N) (G := Gr) nr (wilsonWeight β)) :=
    isProbabilityMeasure_gaugeMeasure GaugeRep.continuous_rep GaugeRep.unitary_rep (posWeight_wilson nr β)
  liftBlockSpec
    (gaugeBlockSpec (d := d) (N := N) (G := Gr) GaugeRep.continuous_rep GaugeRep.unitary_rep (posWeight_wilson nr β)
      (fun t => cellPre cell (boxBlock Λ₀ t)))
    cell (1 : Gr) (boxBlock Λ₀) (fun _ => 1)
    (fun _ _ he => mem_cellPre.1 he)
    (fun _ => measurable_gaugeSpec nr β _)
    (fun _ σ σ' h => (localWeight_plaqProd GaugeRep.continuous_rep GaugeRep.unitary_rep (posWeight_wilson nr β) _).locSpec_congr σ σ'
      (fun e he => h e (fun hc => he (mem_cellPre.2 hc))))
    (fun _ => Filter.Eventually.of_forall fun _ _ hc he => absurd (mem_cellPre.2 hc) he)

theorem wilsonBlockSpec_block (cell : LatticeLink d N → LatticeLink d M) (β : ℝ) (Λ₀ : Finset (FinLatticeSites d M))
    (t : FinLatticeSites d M) : (wilsonBlockSpec Gr nr cell β Λ₀).block t = boxBlock Λ₀ t := rfl

theorem wilsonBlockSpec_spec (cell : LatticeLink d N → LatticeLink d M) (β : ℝ) (Λ₀ : Finset (FinLatticeSites d M))
    (t : FinLatticeSites d M) : (wilsonBlockSpec Gr nr cell β Λ₀).spec t = wilsonBoxSpec Gr nr cell β (boxBlock Λ₀ t) := rfl

theorem wilsonBoxSpec_covariant (cell : LatticeLink d N → LatticeLink d M) (β : ℝ)
    (b : Finset (LatticeLink d M)) :
    SpecCovariant (liftAct cell (gaugeAct N)) (wilsonBoxSpec Gr nr cell β b) :=
  liftSpec_covariant (gaugeAct N) (measurable_gaugeAct N) cell (1 : Gr) b (cellPre cell b) (fun _ => 1) _
    (gaugeSpec_covariant nr β _) (fun _ => mem_cellPre)

end Spec

section Explicit

variable (Gr) (d)

def WilsonOneBox (T : Tuning) : Prop :=
  ∃ (cell : ∀ k j, LatticeLink d (T.side k j) → LatticeLink d (coarseSide j)) (c₀ c₁ : ℝ),
    CellGeometry T cell c₀ c₁ ∧
    ∃ (lam γ D₀ : ℝ) (nmax : ℕ), 0 < lam ∧ 0 ≤ γ ∧ γ < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j,
      ∃ (Λ₀ : Finset (FinLatticeSites d (coarseSide j))) (κ : FinLatticeSites d (coarseSide j) → ℝ),
        1 ≤ Λ₀.card ∧ Λ₀.card ≤ nmax ∧ (∀ u ∈ Λ₀, ∀ u' ∈ Λ₀, (siteDist u u' : ℝ) ≤ D₀) ∧
        (∀ t z, z ∉ boxBlock Λ₀ t →
          IsInfluenceBoundOn (ActAdm (liftAct (cell k j) (gaugeAct (T.side k j))) (boxBlock Λ₀ t))
            (boxBlock Λ₀ t) (wilsonBoxSpec Gr nr (cell k j) (T.β k) (boxBlock Λ₀ t)) z (κ (z.site - t))) ∧
        OneBoxSum κ (boxReach Λ₀) Λ₀ lam γ

theorem fineOneBox_of_wilsonOneBox {T : Tuning} (h : WilsonOneBox Gr nr d T) : FineOneBox Gr nr d T := by
  obtain ⟨cell, c₀, c₁, geo, lam, γ, D₀, nmax, hlam, hγ0, hγ1, k₀, H⟩ := h
  refine ⟨cell, c₀, c₁, geo, lam, γ, D₀, nmax, hlam, hγ0, hγ1, k₀, fun k hk j => ?_⟩
  obtain ⟨Λ₀, κ, h1, h2, h3, hinf, hsum⟩ := H k hk j
  refine ⟨Λ₀, κ, wilsonBlockSpec Gr nr (cell k j) (T.β k) Λ₀, h1, h2, h3, fun t => rfl, fun t => ?_, hinf, hsum⟩
  exact wilsonBoxSpec_covariant Gr nr (cell k j) (T.β k) (boxBlock Λ₀ t)

end Explicit

end Concrete


/-! ## The SU(2), `d = 4` instances -/

section Instance

variable {N M : ℕ} [NeZero N] [NeZero M]

theorem wilsonBoxSpec_four (cell : LatticeLink 4 N → LatticeLink 4 M) (β : ℝ) (b : Finset (LatticeLink 4 M)) :
    wilsonBoxSpec SU2 2 cell β b = ProofPhase.OneBox2.wilsonBoxSpec cell β b := rfl

theorem wilsonBlockSpec_four (cell : LatticeLink 4 N → LatticeLink 4 M) (β : ℝ)
    (Λ₀ : Finset (FinLatticeSites 4 M)) :
    wilsonBlockSpec SU2 2 cell β Λ₀ = ProofPhase.OneBox2.wilsonBlockSpec cell β Λ₀ := rfl

theorem wilsonOneBox_iff (T : Tuning) : ProofPhase.OneBox2.WilsonOneBox T ↔ WilsonOneBox SU2 2 4 T := Iff.rfl

/-- `ProofPhase.OneBox2.wilsonBoxSpec_covariant` from the generic theorem. -/
theorem wilsonBoxSpec_covariant_su2 (cell : LatticeLink 4 N → LatticeLink 4 M) (β : ℝ)
    (b : Finset (LatticeLink 4 M)) :
    ProofPhase.OneBox.SpecCovariant (ProofPhase.OneBox.liftAct cell (ProofPhase.OneBox.gaugeAct N))
      (ProofPhase.OneBox2.wilsonBoxSpec cell β b) :=
  wilsonBoxSpec_covariant SU2 2 cell β b

/-- `ProofPhase.OneBox2.fineOneBox_of_wilsonOneBox` from the generic theorem. -/
theorem fineOneBox_of_wilsonOneBox_su2 {T : Tuning} (h : ProofPhase.OneBox2.WilsonOneBox T) :
    ProofPhase.OneBox.FineOneBox T :=
  fineOneBox_of_wilsonOneBox SU2 2 4 h

example : @ProofPhase.OneBox2.wilsonBoxSpec_covariant = @wilsonBoxSpec_covariant_su2 := rfl
example : @ProofPhase.OneBox2.fineOneBox_of_wilsonOneBox = @fineOneBox_of_wilsonOneBox_su2 := rfl

end Instance

end ProofPhase.General
