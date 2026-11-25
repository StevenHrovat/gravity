/-
Proof phase, generalisation phase 1b: the observable-transfer hypotheses over any gauge group and dimension
(2026-11-24). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 1b.
-/

import ProofPhase.General.Filter
import ProofPhase.General.Local
import ProofPhase.General.SU2Instance
import ProofPhase.Torus.Local
import ProofPhase.V3.CondMass

/-!
# The observable transfer, over any gauge group and dimension

Generic versions of the transfer hypotheses of `Assembly` (`ObsTransfer`, `ObsTransferPhys`), `RouteA/BlockedSlab`
(`ObsTransferU`), `Torus/Local` (`ObsTransferCell`) and `V3/TimeSep` (`ObsTransferPhysT`, `ObsQuasiLocT`), with the
reductions between them. The Wilson law `T.ym k j` becomes `ymLaw nr d T k j` (rep dimension `nr`), `4` becomes `d`.
The SU(2), `d = 4` statements are re-derived at the end (`Iff.rfl` for the definitions, `rfl` on the types of the
theorems).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity

open ProofPhase.V3 (timeDist timeDist_le_linkDist)
open ProofPhase.RouteA (oscBound_indicator)
open ProofPhase.UV

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

section Transfer

variable {Gr : Type*} [Group Gr] [TopologicalSpace Gr] [MeasurableSpace Gr] [HasHaarProbability Gr]
  (nr : ℕ) [HasGaugeTrace Gr nr] [GaugeGroupBase Gr] {d : ℕ} [NeZero d]

/-- The blocked law at level `k`, volume `j`: the image of the Wilson measure of `Gr`. -/
def blockedLaw (T : Tuning) (B : BlockingFamily Gr d T) (k j : ℕ) : Measure (GaugeConnection Gr d (coarseSide j)) :=
  (ymLaw (G := Gr) nr d T k j).map (B k j).B

def ObsTransfer (T : Tuning) (B : BlockingFamily Gr d T) : Prop :=
  ∃ c m : ℝ, 0 ≤ c ∧ 0 < m ∧ ∃ K : ℝ, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection Gr d (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink d (T.side k j))) (D : ℝ),
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * linkDist e e') →
    ∃ (f g : GaugeConnection Gr d (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink d (coarseSide j))),
      Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A' ∧ DepOn g B' ∧
      (A'.card : ℝ) ≤ K * (A₀.card + 1) * (1 + D / T.L₁) ^ d ∧
      (B'.card : ℝ) ≤ K * (B₀.card + 1) * (1 + D / T.L₁) ^ d ∧
      (∀ x ∈ A', ∀ y ∈ B', D / 2 ≤ T.L₁ * linkDist x y) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) F U - f ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j)
        ≤ c * Real.exp (-(m * D)) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) G U - g ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j)
        ≤ c * Real.exp (-(m * D)) ∧
      |∫ U, F U * G U ∂(ymLaw (G := Gr) nr d T k j) -
          ∫ U, condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) F U *
            condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) G U ∂(ymLaw (G := Gr) nr d T k j)|
        ≤ c * Real.exp (-(m * D))

def ObsTransferPhys (T : Tuning) (B : BlockingFamily Gr d T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c K : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection Gr d (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink d (T.side k j))) (D : ℝ),
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R →
    (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * linkDist e e') →
    ∃ (f g : GaugeConnection Gr d (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink d (coarseSide j))),
      Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A' ∧ DepOn g B' ∧
      (∃ vf : LatticeLink d (coarseSide j) → ℝ, OscBound f vf ∧ ∑ a ∈ A', vf a ≤ 2 * K * (1 + D / T.L₁) ^ d) ∧
      (∀ x ∈ A', ∀ y ∈ B', D / 2 ≤ T.L₁ * linkDist x y) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) F U - f ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j)
        ≤ c * Real.exp (-(m * D)) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) G U - g ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j)
        ≤ c * Real.exp (-(m * D)) ∧
      |∫ U, F U * G U ∂(ymLaw (G := Gr) nr d T k j) -
          ∫ U, condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) F U *
            condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) G U ∂(ymLaw (G := Gr) nr d T k j)|
        ≤ c * Real.exp (-(m * D))

def ObsTransferU (T : Tuning) (B : BlockingFamily Gr d T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ Vb : ℕ → ℕ, ∃ c K : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection Gr d (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink d (T.side k j))) (D : ℝ),
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → A₀.card ≤ Vb k → B₀.card ≤ Vb k →
    (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * linkDist e e') →
    ∃ (f g : GaugeConnection Gr d (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink d (coarseSide j))),
      Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A' ∧ DepOn g B' ∧
      (∃ vf : LatticeLink d (coarseSide j) → ℝ, OscBound f vf ∧ ∑ a ∈ A', vf a ≤ 2 * K * (1 + D / T.L₁) ^ d) ∧
      (∀ x ∈ A', ∀ y ∈ B', D / 2 ≤ T.L₁ * linkDist x y) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) F U - f ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j)
        ≤ c * Real.exp (-(m * D)) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) G U - g ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j)
        ≤ c * Real.exp (-(m * D)) ∧
      |∫ U, F U * G U ∂(ymLaw (G := Gr) nr d T k j) -
          ∫ U, condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) F U *
            condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) G U ∂(ymLaw (G := Gr) nr d T k j)|
        ≤ c * Real.exp (-(m * D))

def ObsTransferCell (T : Tuning) (B : BlockingFamily Gr d T) : Prop :=
  ∃ c m K : ℝ, 0 ≤ c ∧ 0 < m ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (R : ℝ) (j : ℕ)
    (F G : GaugeConnection Gr d (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink d (T.side k j))) (D : ℝ),
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R →
    (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * linkDist e e') →
    ∃ (f g : GaugeConnection Gr d (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink d (coarseSide j))),
      Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A' ∧ DepOn g B' ∧
      (A'.card : ℝ) ≤ K * (1 + R / T.L₁) ^ d * (1 + D / T.L₁) ^ d ∧
      (B'.card : ℝ) ≤ K * (1 + R / T.L₁) ^ d * (1 + D / T.L₁) ^ d ∧
      (∀ x ∈ A', ∀ y ∈ B', D / 2 ≤ T.L₁ * linkDist x y) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) F U - f ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j)
        ≤ c * Real.exp (-(m * D)) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) G U - g ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j)
        ≤ c * Real.exp (-(m * D)) ∧
      |∫ U, F U * G U ∂(ymLaw (G := Gr) nr d T k j) -
          ∫ U, condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) F U *
            condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) G U ∂(ymLaw (G := Gr) nr d T k j)|
        ≤ c * Real.exp (-(m * D))

def ObsTransferPhysT (T : Tuning) (B : BlockingFamily Gr d T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c K : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection Gr d (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink d (T.side k j))) (D : ℝ), 0 ≤ D →
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R →
    (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * timeDist e e') →
    ∃ (f g : GaugeConnection Gr d (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink d (coarseSide j))),
      Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A' ∧ DepOn g B' ∧
      (∃ vf : LatticeLink d (coarseSide j) → ℝ, OscBound f vf ∧ ∑ a ∈ A', vf a ≤ 2 * K * (1 + D / T.L₁) ^ d) ∧
      (∀ x ∈ A', ∀ y ∈ B', D / 2 ≤ T.L₁ * linkDist x y) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) F U - f ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j)
        ≤ c * Real.exp (-(m * D)) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) G U - g ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j)
        ≤ c * Real.exp (-(m * D)) ∧
      |∫ U, F U * G U ∂(ymLaw (G := Gr) nr d T k j) -
          ∫ U, condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) F U *
            condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) G U ∂(ymLaw (G := Gr) nr d T k j)|
        ≤ c * Real.exp (-(m * D))


def ObsQuasiLocT (T : Tuning) (B : BlockingFamily Gr d T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c K : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection Gr d (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink d (T.side k j))) (D : ℝ), 0 ≤ D →
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R →
    (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * timeDist e e') →
    ∃ (f g : GaugeConnection Gr d (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink d (coarseSide j))),
      Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A' ∧ DepOn g B' ∧
      (∃ vf : LatticeLink d (coarseSide j) → ℝ, OscBound f vf ∧ ∑ a ∈ A', vf a ≤ 2 * K * (1 + D / T.L₁) ^ d) ∧
      (∀ x ∈ A', ∀ y ∈ B', D / 2 ≤ T.L₁ * linkDist x y) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) F U - f ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j)
        ≤ c * Real.exp (-(m * D)) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) G U - g ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j)
        ≤ c * Real.exp (-(m * D))

theorem obsTransferPhys_of_cell {T : Tuning} {B : BlockingFamily Gr d T} (h : ObsTransferCell nr T B) :
    ObsTransferPhys nr T B := by
  obtain ⟨c, m, K, hc, hm, k₀, H⟩ := h
  refine ⟨m, hm, fun R => ⟨c, K * (1 + R / T.L₁) ^ d, hc, k₀,
    fun k hk j F G A₀ B₀ D mF mG bF bG gF gG dF dG eA eB hsep => ?_⟩⟩
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hA', -, hsep', hEF, hEG, hdec⟩ :=
    H k hk R j F G A₀ B₀ D mF mG bF bG gF gG dF dG eA eB hsep
  obtain ⟨hvf, hsum⟩ := oscBound_indicator bf dfA
  refine ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, ⟨_, hvf, ?_⟩, hsep', hEF, hEG, hdec⟩
  rw [hsum]
  calc 2 * (A'.card : ℝ) ≤ 2 * (K * (1 + R / T.L₁) ^ d * (1 + D / T.L₁) ^ d) := by linarith
    _ = 2 * (K * (1 + R / T.L₁) ^ d) * (1 + D / T.L₁) ^ d := by ring

theorem obsTransferPhys_of_U {T : Tuning} {B : BlockingFamily Gr d T} (h : ObsTransferU nr T B) : ObsTransferPhys nr T B := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, K, hc, k₀, Hk⟩ := H (fun k => d * (2 * ⌊R / T.a k⌋₊ + 1) ^ d)
  exact ⟨c, K, hc, k₀, fun k hk j F G A₀ B₀ D mF mG bF bG gF gG dF dG eA eB hsep =>
    Hk k hk j F G A₀ B₀ D mF mG bF bG gF gG dF dG (card_le_of_physExtent eA) (card_le_of_physExtent eB) hsep⟩

theorem obsTransferPhysT_of_phys {T : Tuning} {B : BlockingFamily Gr d T} (h : ObsTransferPhys nr T B) :
    ObsTransferPhysT nr T B := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, K, hc, k₀, Hk⟩ := H R
  refine ⟨c, K, hc, k₀, fun k hk j F G A₀ B₀ D _ mF mG bF bG gF gG dF dG eA eB hsep => ?_⟩
  exact Hk k hk j F G A₀ B₀ D mF mG bF bG gF gG dF dG eA eB fun e he e' he' =>
    (hsep e he e' he').trans (mul_le_mul_of_nonneg_left (timeDist_le_linkDist e e') (T.a_pos k).le)

theorem obsQuasiLocT_of_obsTransferPhysT {T : Tuning} {B : BlockingFamily Gr d T} (h : ObsTransferPhysT nr T B) :
    ObsQuasiLocT nr T B := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, K, hc, k₀, Hk⟩ := H R
  refine ⟨c, K, hc, k₀, fun k hk j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eA eB hsep => ?_⟩
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hv, hsep', hEF, hEG, -⟩ :=
    Hk k hk j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eA eB hsep
  exact ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hv, hsep', hEF, hEG⟩

end Transfer

/-! ## The SU(2), `d = 4` instances -/

section Instance

variable (T : Tuning) (B : ProofPhase.BlockingFamily T)

theorem obsTransfer_iff : ProofPhase.ObsTransfer T B ↔ ObsTransfer (Gr := SU2) 2 (d := 4) T B := Iff.rfl

theorem obsTransferPhys_iff : ProofPhase.ObsTransferPhys T B ↔ ObsTransferPhys (Gr := SU2) 2 (d := 4) T B := Iff.rfl

theorem obsTransferU_iff : ProofPhase.RouteA.ObsTransferU T B ↔ ObsTransferU (Gr := SU2) 2 (d := 4) T B := Iff.rfl

theorem obsTransferCell_iff : ProofPhase.Torus.ObsTransferCell T B ↔ ObsTransferCell (Gr := SU2) 2 (d := 4) T B :=
  Iff.rfl

theorem obsTransferPhysT_iff : ProofPhase.V3.ObsTransferPhysT T B ↔ ObsTransferPhysT (Gr := SU2) 2 (d := 4) T B :=
  Iff.rfl

theorem obsQuasiLocT_iff : ProofPhase.V3.ObsQuasiLocT T B ↔ ObsQuasiLocT (Gr := SU2) 2 (d := 4) T B := Iff.rfl

theorem blockedLaw_eq (k j : ℕ) : blockedLaw (Gr := SU2) 2 T B k j = ProofPhase.blockedLaw T B k j := rfl

/-- `ProofPhase.Torus.obsTransferPhys_of_cell` from the generic theorem. -/
theorem obsTransferPhys_of_cell_su2 {T : Tuning} {B : ProofPhase.BlockingFamily T}
    (h : ProofPhase.Torus.ObsTransferCell T B) : ProofPhase.ObsTransferPhys T B :=
  obsTransferPhys_of_cell (Gr := SU2) 2 (d := 4) h

/-- `ProofPhase.Torus.obsTransferPhys_of_U` from the generic theorem. -/
theorem obsTransferPhys_of_U_su2 {T : Tuning} {B : ProofPhase.BlockingFamily T}
    (h : ProofPhase.RouteA.ObsTransferU T B) : ProofPhase.ObsTransferPhys T B :=
  obsTransferPhys_of_U (Gr := SU2) 2 (d := 4) h

/-- `ProofPhase.V3.obsTransferPhysT_of_phys` from the generic theorem. -/
theorem obsTransferPhysT_of_phys_su2 {T : Tuning} {B : ProofPhase.BlockingFamily T}
    (h : ProofPhase.ObsTransferPhys T B) : ProofPhase.V3.ObsTransferPhysT T B :=
  obsTransferPhysT_of_phys (Gr := SU2) 2 (d := 4) h

/-- `ProofPhase.V3.obsQuasiLocT_of_obsTransferPhysT` from the generic theorem. -/
theorem obsQuasiLocT_of_obsTransferPhysT_su2 {T : Tuning} {B : ProofPhase.BlockingFamily T}
    (h : ProofPhase.V3.ObsTransferPhysT T B) : ProofPhase.V3.ObsQuasiLocT T B :=
  obsQuasiLocT_of_obsTransferPhysT (Gr := SU2) 2 (d := 4) h

example : @ProofPhase.Torus.obsTransferPhys_of_cell = @obsTransferPhys_of_cell_su2 := rfl
example : @ProofPhase.Torus.obsTransferPhys_of_U = @obsTransferPhys_of_U_su2 := rfl
example : @ProofPhase.V3.obsTransferPhysT_of_phys = @obsTransferPhysT_of_phys_su2 := rfl
example : @ProofPhase.V3.obsQuasiLocT_of_obsTransferPhysT = @obsQuasiLocT_of_obsTransferPhysT_su2 := rfl

end Instance

end ProofPhase.General
