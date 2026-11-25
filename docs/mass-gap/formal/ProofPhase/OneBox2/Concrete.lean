/-
Proof phase, cycle 8, workstream 3 (c8c-concrete): the one-box criterion with the actual Wilson box law
(2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c8c-concrete/NOTE.md`, section 1.
-/

import ProofPhase.OneBox2.Wilson

/-!
# The box law of the Wilson measure, regrouped by cells, and the criterion without assumed premises

* `wilsonBoxSpec cell β Λ₀ t`: **the conditional law of the Wilson measure on the box `Λ₀ + t` of cells, given the
  outside** (the DLR box kernel `exp(β ∑_{p touching the box} Re tr U_p) × Haar` of all the fine links of the box
  cells, regrouped by cells).
* `wilsonBlockSpec`: these kernels form a `BlockSpec` of the lifted Wilson measure `ymLaw ∘ cellLift⁻¹`: they are
  **the conditional law (DLR consistency, `BlockSpec.dlr`)**; probability, locality and measurable block averages are
  fields of the structure.
* `wilsonBoxSpec_covariant`: they are **gauge covariant** for the lifted action of every gauge transformation of the
  whole torus (so for the interior ones in particular).
* `WilsonOneBox T`: the criterion `FineOneBox` with the box law the actual Wilson one; no existential specification,
  no assumed covariance. `fineOneBox_of_wilsonOneBox`: `WilsonOneBox T ⇒ FineOneBox T`, hence
  `yang_mills_assembly_wilsonOneBox`.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  ProofPhase.Torus ProofPhase.V3 ProofPhase.V4 ProofPhase.OneBox

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.OneBox2

section Spec

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- The fine links of the cells of a block of cells. -/
def cellPre (cell : LatticeLink 4 N → LatticeLink 4 M) (b : Finset (LatticeLink 4 M)) : Finset (LatticeLink 4 N) :=
  univ.filter fun e => cell e ∈ b

theorem mem_cellPre {cell : LatticeLink 4 N → LatticeLink 4 M} {b : Finset (LatticeLink 4 M)} {e : LatticeLink 4 N} :
    e ∈ cellPre cell b ↔ cell e ∈ b := by simp [cellPre]

/-- **The box law of the Wilson measure regrouped by cells**: the conditional law of the fine links of the cells of
`b`, given everything outside, as a measure on regrouped configurations (only the coordinates in `b` are used). -/
def wilsonBoxSpec (cell : LatticeLink 4 N → LatticeLink 4 M) (β : ℝ) (b : Finset (LatticeLink 4 M)) :
    (LatticeLink 4 M → (LatticeLink 4 N → SU2)) → Measure (LatticeLink 4 M → (LatticeLink 4 N → SU2)) :=
  liftSpec cell (1 : SU2) b (cellPre cell b) (fun _ => 1)
    (gaugeSpec (G := SU2) (d := 4) (N := N) 2 (wilsonWeight β) (cellPre cell b))

/-- **The block specification of the lifted Wilson measure by the boxes `Λ₀ + t`.** -/
def wilsonBlockSpec (cell : LatticeLink 4 N → LatticeLink 4 M) (β : ℝ) (Λ₀ : Finset (FinLatticeSites 4 M)) :
    BlockSpec ((wilsonMeasure SU2 2 β 4 N).map (cellLift cell (1 : SU2))) (FinLatticeSites 4 M) :=
  haveI : IsProbabilityMeasure (gaugeMeasure (d := 4) (N := N) (G := SU2) 2 (wilsonWeight β)) :=
    isProbabilityMeasure_gaugeMeasure su2_hc' su2_hU' (posWeight_wilson 2 β)
  liftBlockSpec
    (gaugeBlockSpec (d := 4) (N := N) (G := SU2) su2_hc' su2_hU' (posWeight_wilson 2 β)
      (fun t => cellPre cell (boxBlock Λ₀ t)))
    cell (1 : SU2) (boxBlock Λ₀) (fun _ => 1)
    (fun t e he => mem_cellPre.1 he)
    (fun t => measurable_gaugeSpec β _)
    (fun t σ σ' h => (localWeight_plaqProd su2_hc' su2_hU' (posWeight_wilson 2 β) _).locSpec_congr σ σ'
      (fun e he => h e (fun hc => he (mem_cellPre.2 hc))))
    (fun t => Filter.Eventually.of_forall fun U e hc he => absurd (mem_cellPre.2 hc) he)

theorem wilsonBlockSpec_block (cell : LatticeLink 4 N → LatticeLink 4 M) (β : ℝ) (Λ₀ : Finset (FinLatticeSites 4 M))
    (t : FinLatticeSites 4 M) : (wilsonBlockSpec cell β Λ₀).block t = boxBlock Λ₀ t := rfl

/-- **The blocks' kernels are the box law.** -/
theorem wilsonBlockSpec_spec (cell : LatticeLink 4 N → LatticeLink 4 M) (β : ℝ) (Λ₀ : Finset (FinLatticeSites 4 M))
    (t : FinLatticeSites 4 M) : (wilsonBlockSpec cell β Λ₀).spec t = wilsonBoxSpec cell β (boxBlock Λ₀ t) := rfl

/-- **Gauge covariance of the box law** for the lifted action of every gauge transformation of the torus. -/
theorem wilsonBoxSpec_covariant (cell : LatticeLink 4 N → LatticeLink 4 M) (β : ℝ)
    (b : Finset (LatticeLink 4 M)) :
    SpecCovariant (liftAct cell (gaugeAct N)) (wilsonBoxSpec cell β b) :=
  liftSpec_covariant (gaugeAct N) (measurable_gaugeAct N) cell (1 : SU2) b (cellPre cell b) (fun _ => 1) _
    (gaugeSpec_covariant β _) (fun e => mem_cellPre)

end Spec

/-! ## The criterion with the actual box law -/

/-- **The one-box criterion for the Wilson measure at the physical cell scale, with the actual Wilson box law.**
As `FineOneBox`, but the block specification is the DLR box kernel `wilsonBoxSpec` and not an existentially quantified
one; the covariance is a theorem (`wilsonBoxSpec_covariant`). The only content left in the criterion is the numbers
`κ` and the one-box sum. -/
def WilsonOneBox (T : Tuning) : Prop :=
  ∃ (cell : ∀ k j, LatticeLink 4 (T.side k j) → LatticeLink 4 (coarseSide j)) (c₀ c₁ : ℝ),
    CellGeometry T cell c₀ c₁ ∧
    ∃ (lam γ D₀ : ℝ) (nmax : ℕ), 0 < lam ∧ 0 ≤ γ ∧ γ < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j,
      ∃ (Λ₀ : Finset (FinLatticeSites 4 (coarseSide j))) (κ : FinLatticeSites 4 (coarseSide j) → ℝ),
        1 ≤ Λ₀.card ∧ Λ₀.card ≤ nmax ∧ (∀ u ∈ Λ₀, ∀ u' ∈ Λ₀, (siteDist u u' : ℝ) ≤ D₀) ∧
        (∀ t z, z ∉ boxBlock Λ₀ t →
          IsInfluenceBoundOn (ActAdm (liftAct (cell k j) (gaugeAct (T.side k j))) (boxBlock Λ₀ t))
            (boxBlock Λ₀ t) (wilsonBoxSpec (cell k j) (T.β k) (boxBlock Λ₀ t)) z (κ (z.site - t))) ∧
        OneBoxSum κ (boxReach Λ₀) Λ₀ lam γ

/-- **`WilsonOneBox ⇒ FineOneBox`**: the actual box law supplies the specification, the DLR identity and the covariance
that `FineOneBox` had to assume. -/
theorem fineOneBox_of_wilsonOneBox {T : Tuning} (h : WilsonOneBox T) : FineOneBox T := by
  obtain ⟨cell, c₀, c₁, geo, lam, γ, D₀, nmax, hlam, hγ0, hγ1, k₀, H⟩ := h
  refine ⟨cell, c₀, c₁, geo, lam, γ, D₀, nmax, hlam, hγ0, hγ1, k₀, fun k hk j => ?_⟩
  obtain ⟨Λ₀, κ, h1, h2, h3, hinf, hsum⟩ := H k hk j
  refine ⟨Λ₀, κ, wilsonBlockSpec (cell k j) (T.β k) Λ₀, h1, h2, h3, fun t => rfl, fun t => ?_, hinf, hsum⟩
  exact wilsonBoxSpec_covariant (cell k j) (T.β k) (boxBlock Λ₀ t)

/-- **Assembly with the one-box criterion for the actual Wilson box law** (S). -/
theorem yang_mills_assembly_wilsonOneBox {T : Tuning} (hL : OnLCP' T) (hN : NonTrivial T) (h : WilsonOneBox T) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T :=
  yang_mills_assembly_onebox hL hN (fineOneBox_of_wilsonOneBox h)

end ProofPhase.OneBox2
