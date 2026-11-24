/-
Proof phase, generalisation phase 1: the gauge-group package (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`.
-/

import ProofPhase.Objects

/-!
# The gauge-group package

What the generic (`inst`) files use from the gauge group `G`, in two layers.

**Data classes** (already in the repository, unchanged): `Group G`, `TopologicalSpace G`, `MeasurableSpace G`,
`HasGaugeTrace G n` (a matrix representation of dimension `n`), `HasHaarProbability G` (the Haar probability measure,
`haarG G`).

**Facts** (new, this file), as `Prop` classes on top of the data classes:
* `GaugeGroupBase G`: `G` is a second-countable compact topological group with Borel structure, and `haarG G` is
  left- and inversion-invariant.
* `GaugeRep G n`: the representation is continuous and unitary. From it the bounded class function of the Wilson action
  follows (`abs_gaugeReTr_le`: `|Re tr g| ≤ n`), together with `gaugeReTr 1 = n` and invariance under conjugation.

A generic theorem takes `[Group G] [TopologicalSpace G] [MeasurableSpace G] [HasHaarProbability G] [HasGaugeTrace G n]
[GaugeGroupBase G] [GaugeRep G n]`; the instances `IsTopologicalGroup G`, `SecondCountableTopology G`, `BorelSpace G`,
`CompactSpace G`, `(haarG G).IsInvInvariant` come from `GaugeGroupBase G`.

**The `subst` layer** (`GaugeSubst G n`): the group facts that the SU(2) files use in substance (audit, finding 3),
declared as data and axioms-as-fields of a class, **not proved for general `G`** in this phase: a cost distance
`geodDist` replacing `geodSU2` (non-negative, takes a positive value), a set of central elements (the centre) acting as
scalars in the representation, and a projection from `n × n` matrices onto `G` that is a left inverse of the
representation. The 2×2 identities (adjugate, Mandelstam) and the characters beyond `Re tr` are not fields: they are
phase 3 work (see `NOTE.md`). The fundamental dimension is the parameter `n` of `HasGaugeTrace G n`.
`GaugeSubst` is a structure of *data and statements*, so a field is not an `axiom`: an instance must prove it.
-/

open MeasureTheory Finset AreaLaw.Concrete OneScale.Gauge

noncomputable section

namespace ProofPhase.General

/-! ## The facts about the group -/

/-- **The topological and measure layer of the gauge-group package.** -/
class GaugeGroupBase (G : Type*) [Group G] [TopologicalSpace G] [MeasurableSpace G] [HasHaarProbability G] :
    Prop where
  isTopologicalGroup : IsTopologicalGroup G
  secondCountable : SecondCountableTopology G
  borel : BorelSpace G
  compact : CompactSpace G
  haarLeft : (haarG G).IsMulLeftInvariant
  haarInv : (haarG G).IsInvInvariant

section Base

variable (G : Type*) [Group G] [TopologicalSpace G] [MeasurableSpace G] [HasHaarProbability G] [GaugeGroupBase G]

instance (priority := 100) GaugeGroupBase.instIsTopologicalGroup : IsTopologicalGroup G :=
  GaugeGroupBase.isTopologicalGroup

instance (priority := 100) GaugeGroupBase.instSecondCountable : SecondCountableTopology G :=
  GaugeGroupBase.secondCountable

instance (priority := 100) GaugeGroupBase.instBorel : BorelSpace G := GaugeGroupBase.borel

instance (priority := 100) GaugeGroupBase.instCompact : CompactSpace G := GaugeGroupBase.compact

instance (priority := 100) GaugeGroupBase.instHaarLeft : (haarG G).IsMulLeftInvariant := GaugeGroupBase.haarLeft

instance (priority := 100) GaugeGroupBase.instHaarInv : (haarG G).IsInvInvariant := GaugeGroupBase.haarInv

end Base

/-- **The representation layer of the gauge-group package**: the representation of dimension `n` is continuous and
unitary. -/
class GaugeRep (G : Type*) (n : ℕ) [Group G] [TopologicalSpace G] [HasGaugeTrace G n] : Prop where
  continuous_rep : Continuous (HasGaugeTrace.rep (G := G) (n := n))
  unitary_rep : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ

section Identity

variable {G : Type*} {n : ℕ} [Group G] [HasGaugeTrace G n]

/-- The identity has `Re tr 1 = n`. -/
theorem gaugeReTr_one : gaugeReTr G n (1 : G) = n := by
  simp [gaugeReTr, gaugeTrace]

/-- `Re tr` is a class function: invariant under conjugation. -/
theorem gaugeReTr_conj (g h : G) : gaugeReTr G n (g * h * g⁻¹) = gaugeReTr G n h := by
  unfold gaugeReTr gaugeTrace
  rw [map_mul, map_mul, Matrix.trace_mul_comm (_ * _) _, ← mul_assoc]
  have : HasGaugeTrace.rep (G := G) (n := n) g⁻¹ * HasGaugeTrace.rep (G := G) (n := n) g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [this, Matrix.one_mul]
end Identity

section Rep

variable {G : Type*} {n : ℕ} [Group G] [TopologicalSpace G] [HasGaugeTrace G n] [GaugeRep G n]

/-- **The bounded class function of the Wilson action**: `|Re tr g| ≤ n`. -/
theorem abs_gaugeReTr_le (g : G) : |gaugeReTr G n g| ≤ n :=
  abs_re_trace_le_of_unitary (GaugeRep.unitary_rep g)

end Rep

section Wilson

variable {G : Type*} {n : ℕ} [Group G] [TopologicalSpace G] [MeasurableSpace G] [HasHaarProbability G]
  [HasGaugeTrace G n] [GaugeGroupBase G] [GaugeRep G n]

/-- **The Wilson measure of the package is a probability measure** (generic version of `ProofPhase.UV.ym_prob`:
any `G`, any `n`, any `d`, any torus side). -/
theorem isProbabilityMeasure_wilsonMeasure (d N : ℕ) [NeZero N] (β : ℝ) :
    IsProbabilityMeasure (wilsonMeasure G n β d N) :=
  isProbabilityMeasure_gaugeMeasure GaugeRep.continuous_rep GaugeRep.unitary_rep (posWeight_wilson n β)

end Wilson

/-! ## The `subst` layer: group facts used in substance by the SU(2) files -/

/-- **The group facts the SU(2) files use in substance** (audit finding 3), as fields to be proved per group. Not proved
for general `G` in phase 1. -/
class GaugeSubst (G : Type*) (n : ℕ) [Group G] [HasGaugeTrace G n] where
  /-- The cost distance on `G` (`geodSU2` for SU(2)). -/
  geodDist : G → G → ℝ
  geodDist_nonneg : ∀ a b, 0 ≤ geodDist a b
  geodDist_pos : ∃ a b, 0 < geodDist a b
  /-- The centre: central elements, acting as scalars in the representation (`{1, -1}` for SU(2)). -/
  centre : Set G
  one_mem_centre : (1 : G) ∈ centre
  centre_central : ∀ z ∈ centre, ∀ g : G, z * g = g * z
  centre_scalar : ∀ z ∈ centre, ∃ c : ℂ, HasGaugeTrace.rep (G := G) (n := n) z = c • (1 : Matrix (Fin n) (Fin n) ℂ)
  /-- The projection of `n × n` matrices onto `G`, a left inverse of the representation. -/
  proj : Matrix (Fin n) (Fin n) ℂ → G
  proj_rep : ∀ g : G, proj (HasGaugeTrace.rep (G := G) (n := n) g) = g

end ProofPhase.General
