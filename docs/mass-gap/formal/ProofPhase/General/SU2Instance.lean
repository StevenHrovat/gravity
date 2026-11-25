/-
Proof phase, generalisation phase 1: the SU(2) instance of the gauge-group package (2026-11-23).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`.
-/

import ProofPhase.General.GaugeGroup
import ProofPhase.Repair.WeightedW
import ProofPhase.RouteA.Blocking

/-!
# SU(2) as a gauge group of the package

`GaugeGroupBase SU2`, `GaugeRep SU2 2` (the defining representation) and `GaugeSubst SU2 2`, with the cost distance
`geodSU2`, the centre `{1, -1}` and the projection `projSU2`. Every field is proved from facts already in the
repository; nothing new is assumed.
-/

open MeasureTheory Finset AreaLaw.Concrete

noncomputable section

namespace ProofPhase.General

instance instGaugeGroupBaseSU2 : GaugeGroupBase SU2 where
  isTopologicalGroup := inferInstance
  secondCountable := inferInstance
  borel := inferInstance
  compact := inferInstance
  haarLeft := inferInstance
  haarInv := inferInstance

instance instGaugeRepSU2 : GaugeRep SU2 2 where
  continuous_rep := continuous_subtype_val
  unitary_rep := fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2

instance instGaugeSubstSU2 : GaugeSubst SU2 2 where
  geodDist := ProofPhase.Certified.geodSU2
  geodDist_nonneg := ProofPhase.Certified.geodSU2_nonneg
  geodDist_pos := ProofPhase.Repair.exists_geodSU2_pos
  centre := {1, negOneSU2}
  one_mem_centre := Set.mem_insert _ _
  centre_central := by
    intro z hz g
    rcases hz with rfl | hz
    · simp
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact Subtype.ext (show (-1 : Matrix (Fin 2) (Fin 2) ℂ) * g.val = g.val * -1 by simp)
  centre_scalar := by
    intro z hz
    rcases hz with rfl | hz
    · exact ⟨1, by simp⟩
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨-1, by
        show (-1 : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • 1
        simp⟩
  proj := ProofPhase.RouteA.projSU2
  proj_rep g := ProofPhase.RouteA.projSU2_coe g

end ProofPhase.General
