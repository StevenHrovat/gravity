/-
Proof phase, cycle 5, workstream 1 (c5a-v4): segment 1 wired into the ultraviolet layer of version 4 (2026-11-22).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c5a-v4/NOTE.md`.
-/

import ProofPhase.V4.Gap
import ProofPhase.Seg1.Envelope

/-!
# Segment 1 feeds the ultraviolet layer, not the infrared one

c4b's `Seg1` (Kotecky–Preiss, `PolymerRepW ⇒ EnvelopeW`) was proved about "the laws of the `L_*` block field" and fed
nothing downstream (review finding 5, W13). In version 4 the tuning's unit **is** `L_*` and the blocking family `B` of the
top theorem blocks onto `L_*` cells, so those laws are `blockedLaw T B`. This file states segment 1 for them.

* `UV1Polymer T B λ' M_E` (**named hypothesis, open; UV1 in c4b's vacancy-1 polymer form**):
  `Seg1.PolymerRepW coarseSide (blockedLaw T B) λ' M_E`.
* `gibbsRep_of_uv1Polymer` (S, `Seg1.envelopeW_seg1`): then every `L_*` law is the Gibbs measure of a bounded local
  potential, and the potentials have one exponentially weighted envelope (`H1.EnvelopeW`) for all levels and volumes.

**Where it is consumed, honestly.** Nothing in the v4 top theorem consumes UV1: the top theorem takes the ultraviolet input
in its final form `ObsTransferPhysTW T B` (UV2, the transfer from the fine lattice to `L_*` cells). UV1 is the proposed
**supplier of the `L_*` theory itself**: the local Gibbs representation is the starting point of the paper proofs of UV2
(quasi-locality of `E[F | Φ_*]` from conditional mixing, c4a §2.2) and of every infrared strategy that is stated for the
`L_*` laws (`V4.StageTwoW`, strategy (b) on cells). It is not an input of the infrared statement and carries no gap content
(it holds for the photon at weak coupling). The draft's UV1 is the **defect form** (rare bad cells with conditional
probability `≤ p₀`), which c5d is writing; the vacancy-1 form here needs lower bounds on large-field weights that the
published sources do not state (c4b, review W8).
-/

open MeasureTheory Finset AreaLaw.Concrete OneScale OneScale.LinkDist

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.V4

/-- **UV1, vacancy-1 polymer form (named hypothesis, open)**: c4b's `PolymerRepW` for the laws of the `L_*` block field,
`blockedLaw T B` (the tuning's unit read as `L_*`). -/
def UV1Polymer (T : Tuning) (B : BlockingFamily T) (lam' ME : ℝ) : Prop :=
  Seg1.PolymerRepW coarseSide (blockedLaw T B) lam' ME

/-- **Segment 1 on the `L_*` laws of version 4** (S given `UV1Polymer`): local Gibbs representation with bounded
potentials and one `EnvelopeW` for all levels and volumes. -/
theorem gibbsRep_of_uv1Polymer {T : Tuning} {B : BlockingFamily T} {lam' ME : ℝ} (hlam : 0 ≤ lam')
    (h : UV1Polymer T B lam' ME) :
    ∃ (V : ℕ → ∀ j, Finset (LatticeLink 4 (coarseSide j)) → GaugeConnection SU2 4 (coarseSide j) → ℝ)
      (hb : ∀ kj : ℕ × ℕ, Finset (LatticeLink 4 (coarseSide kj.2)) → ℝ),
      (∀ k j, blockedLaw T B k j = Attempts.R3.gibbsMeasure (haarG SU2) (V k j) ∧
        Attempts.R3.Potential (fun A => A) (V k j) ∧ ∀ X U, |V k j X U| ≤ hb (k, j) X) ∧
      H1.EnvelopeW (ι := fun kj : ℕ × ℕ => LatticeLink 4 (coarseSide kj.2)) (fun _ A => A)
        (fun _ => H1.linkDiam) lam' hb :=
  Seg1.envelopeW_seg1 T (fun k j => (B k j).B) hlam h

end ProofPhase.V4
