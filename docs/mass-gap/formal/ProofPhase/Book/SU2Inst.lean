/-
Proof phase, cycle 6, workstream 5 (c6e-bookkeeping): cached instances for SU(2) (2026-11-22).
Released under Apache 2.0.
-/

import ProofPhase.Repair.Noisy

/-! Instances used by the `Book` modules: the generic instance search for `MeasurableMul₂` and `MeasurableInv` on the
subtype `SU2` of `2 × 2` matrices is slow, and Haar measure on SU(2) is inversion invariant (compact group). -/

open MeasureTheory AreaLaw.Concrete Positivity

noncomputable section

namespace ProofPhase.Book

set_option maxHeartbeats 2000000 in
instance instMeasurableMul2SU2 : MeasurableMul₂ SU2 := inferInstance

set_option maxHeartbeats 2000000 in
instance instMeasurableInvSU2 : MeasurableInv SU2 := inferInstance

instance instInvInvariantHaarSU2 : (haarG SU2).IsInvInvariant := by
  show (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts SU2)).IsInvInvariant
  have := isProbabilityMeasure_haarMeasure_top (G := SU2)
  exact isInvInvariant_of_compact _

end ProofPhase.Book
