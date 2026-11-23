/-
Proof phase, generalisation phase 2: SU(N) as a gauge group of the package (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 2.
-/

import ProofPhase.General.SU2Instance

/-!
# SU(N) with Haar measure, and the package instances

`SUN N` is the special unitary group `Matrix.specialUnitaryGroup (Fin N) ℂ`, with the topology and Borel structure
inherited from the `N × N` complex matrices, exactly as `SU2` and `Un n` in `AreaLaw/Concrete.lean` (and `SUN 2` is
`SU2` by unfolding). This file gives, for every `N`: the topological group, compactness, second countability, the defining
representation `HasGaugeTrace (SUN N) N`, the Haar probability measure with left invariance, and the package instances
`GaugeGroupBase (SUN N)` and `GaugeRep (SUN N) N`. From the package follow the bounded class function
(`|Re tr g| ≤ N`) and the Wilson measure as a probability measure on every torus, in every dimension.

Nothing here needs `N ≥ 2`; for `N ≤ 1` the group is trivial.
-/

open MeasureTheory Finset AreaLaw.Concrete

noncomputable section

namespace ProofPhase.General

/-- SU(N), with the topology and the (Borel) measurable structure inherited from the `N × N` complex matrices. -/
abbrev SUN (N : ℕ) : Type := Matrix.specialUnitaryGroup (Fin N) ℂ

instance instIsTopologicalGroupSUN (N : ℕ) : IsTopologicalGroup (SUN N) where
  continuous_mul := by
    apply continuous_induced_rng.2
    exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    apply continuous_induced_rng.2
    exact continuous_subtype_val.star

theorem isCompact_SUN (N : ℕ) :
    IsCompact (Matrix.specialUnitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) := by
  refine (isCompact_unitaryGroup N).of_isClosed_subset ?_
    (fun A hA => (Matrix.mem_specialUnitaryGroup_iff.mp hA).1)
  have hcl : IsClosed (Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) := isClosed_unitary
  have hdet : IsClosed {A : Matrix (Fin N) (Fin N) ℂ | A.det = 1} :=
    isClosed_eq continuous_id.matrix_det continuous_const
  convert hcl.inter hdet using 1
  ext A
  simp only [SetLike.mem_coe, Matrix.mem_specialUnitaryGroup_iff, Set.mem_inter_iff, Set.mem_ofPred_eq]

instance instCompactSpaceSUN (N : ℕ) : CompactSpace (SUN N) := isCompact_iff_compactSpace.mp (isCompact_SUN N)

instance instSecondCountableSUN (N : ℕ) : SecondCountableTopology (SUN N) :=
  inferInstanceAs (SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)))

/-- The defining representation `SU(N) ⊆ M_N(ℂ)`. -/
instance instHasGaugeTraceSUN (N : ℕ) : HasGaugeTrace (SUN N) N := ⟨(Matrix.specialUnitaryGroup (Fin N) ℂ).subtype⟩

/-- Haar measure on SU(N), normalised to a probability measure. -/
instance instHasHaarProbabilitySUN (N : ℕ) : HasHaarProbability (SUN N) := haarProbability (SUN N)

instance instHaarLeftSUN (N : ℕ) : (haarG (SUN N)).IsMulLeftInvariant := by
  show (Measure.haarMeasure ⊤).IsMulLeftInvariant; infer_instance

/-! ## The package instances -/

instance instGaugeGroupBaseSUN (N : ℕ) : GaugeGroupBase (SUN N) where
  isTopologicalGroup := inferInstance
  secondCountable := inferInstance
  borel := inferInstance
  compact := inferInstance
  haarLeft := inferInstance
  haarInv := inferInstance

instance instGaugeRepSUN (N : ℕ) : GaugeRep (SUN N) N where
  continuous_rep := continuous_subtype_val
  unitary_rep := fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2

/-- **The bounded class function of the Wilson action on SU(N)**: `|Re tr g| ≤ N`. -/
theorem abs_gaugeReTr_le_SUN {N : ℕ} (g : SUN N) : |gaugeReTr (SUN N) N g| ≤ N := abs_gaugeReTr_le g

/-- **The Wilson measure of SU(N) is a probability measure**, on every torus, in every dimension, at every coupling. -/
theorem isProbabilityMeasure_wilsonMeasure_SUN (N d M : ℕ) [NeZero M] (β : ℝ) :
    IsProbabilityMeasure (wilsonMeasure (SUN N) N β d M) :=
  isProbabilityMeasure_wilsonMeasure (G := SUN N) (n := N) d M β

end ProofPhase.General
