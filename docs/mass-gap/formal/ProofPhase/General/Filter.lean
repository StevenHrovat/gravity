/-
Proof phase, generalisation phase 1: conditional decoupling from smoother stability for any gauge group and any
dimension (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`.
-/

import ProofPhase.Seg2.Filter
import ProofPhase.General.GaugeGroup
import ProofPhase.General.SU2Instance

/-!
# Filter stability for the Wilson measure of any gauge group, in dimension `d`

The generic part of `ProofPhase.Seg2.Filter` (any probability space) is untouched; this file restates its Yang-Mills
instance (`blockSigma`, `SepPred`, `CondDecouple`, `AnnealedContraction`, `SmootherStable` and the three reductions) for
the Wilson measure of a gauge group `G` of the package in dimension `d`, along a (group-free) tuning `T`. The
physical-extent predicate `PhysExtent` is stated in dimension `d` as well. The SU(2), `d = 4` statements are re-derived
at the end with the same types as the old ones.
-/

open MeasureTheory Finset Filter AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist

open ProofPhase.UV
open ProofPhase.Seg2 (abs_condDefect_le_smoother smoother_chain_of_steps)

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

/-- The physical extent of a set of links at level `k`: any two links at physical distance `≤ R`, in dimension `d`. -/
def PhysExtent (T : Tuning) (k : ℕ) {d N : ℕ} (A : Finset (LatticeLink d N)) (R : ℝ) : Prop :=
  ∀ e ∈ A, ∀ e' ∈ A, T.a k * linkDist e e' ≤ R

/-- A family of reflection-respecting blockings of the fine tori onto the coarse tori, over `G` in dimension `d`. -/
abbrev BlockingFamily (G : Type*) [Group G] [MeasurableSpace G] (d : ℕ) [NeZero d] (T : Tuning) :=
  ∀ k j, ProofPhase.RPBlocking G d (T.side k j) (ProofPhase.coarseSide j)

section YM

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [HasHaarProbability G]
  (n : ℕ) [HasGaugeTrace G n] [GaugeGroupBase G] {d : ℕ} [NeZero d]

/-- The Wilson measure of `G` at level `k`, torus `j`, along the tuning `T` (`T.ym k j` for SU(2), `d = 4`). -/
abbrev ymLaw (d : ℕ) (T : Tuning) (k j : ℕ) : Measure (GaugeConnection G d (T.side k j)) :=
  wilsonMeasure G n (T.β k) d (T.side k j)

/-- The block sigma-algebra of the blocking family at level `k`, volume `j`. -/
abbrev blockSigma {T : Tuning} (B : BlockingFamily G d T) (k j : ℕ) :
    MeasurableSpace (GaugeConnection G d (T.side k j)) :=
  MeasurableSpace.comap (B k j).B inferInstance

/-- A separation predicate on pairs of supports at physical distance `D`. -/
abbrev SepPred (d : ℕ) (T : Tuning) : Type :=
  ∀ k j : ℕ, Finset (LatticeLink d (T.side k j)) → Finset (LatticeLink d (T.side k j)) → ℝ → Prop

/-- **Part (c) of the observable transfer, restricted to pairs satisfying `Sep`** (same quantifiers and constants). -/
def CondDecouple {T : Tuning} (B : BlockingFamily G d T) (Sep : SepPred d T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G' : GaugeConnection G d (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink d (T.side k j))) (D : ℝ),
    Measurable F → Measurable G' → (∀ U, |F U| ≤ 1) → (∀ U, |G' U| ≤ 1) → GaugeInvariant F → GaugeInvariant G' →
    DepOn F A₀ → DepOn G' B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R → Sep k j A₀ B₀ D →
    |condDefect (ymLaw (G := G) n d T k j) (blockSigma B k j) F G'| ≤ c * Real.exp (-(m * D))

/-- **The named hypothesis (filter-stability form of Lemma X in the time direction).** See
`ProofPhase.Seg2.AnnealedContraction` for the reading. -/
def AnnealedContraction {T : Tuning} (B : BlockingFamily G d T) (Sep : SepPred d T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G' : GaugeConnection G d (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink d (T.side k j))) (D : ℝ),
    Measurable F → Measurable G' → (∀ U, |F U| ≤ 1) → (∀ U, |G' U| ≤ 1) → GaugeInvariant F → GaugeInvariant G' →
    DepOn F A₀ → DepOn G' B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R → Sep k j A₀ B₀ D →
    ∃ (m' : ℕ) (K : ℕ → MeasurableSpace (GaugeConnection G d (T.side k j)))
      (θ : ℕ → GaugeConnection G d (T.side k j) → ℝ),
      (∀ i, blockSigma B k j ≤ K i ∧
        K i ≤ (MeasurableSpace.pi : MeasurableSpace (GaugeConnection G d (T.side k j)))) ∧
      (∀ i, StronglyMeasurable[blockSigma B k j] (θ i) ∧ ∀ U, 0 ≤ θ i U ∧ θ i U ≤ 1) ∧
      (∀ i, condExp (blockSigma B k j) (ymLaw (G := G) n d T k j)
          (fun x => |condExp (K (i + 1)) (ymLaw (G := G) n d T k j)
            (fun y => condExp (K i) (ymLaw (G := G) n d T k j) F y -
              condExp (blockSigma B k j) (ymLaw (G := G) n d T k j) F y) x|)
        ≤ᵐ[ymLaw (G := G) n d T k j] fun x => θ i x * condExp (blockSigma B k j) (ymLaw (G := G) n d T k j)
          (fun x => |condExp (K i) (ymLaw (G := G) n d T k j) F x -
            condExp (blockSigma B k j) (ymLaw (G := G) n d T k j) F x|) x) ∧
      (∀ i, condExp (K (i + 1)) (ymLaw (G := G) n d T k j) (condExp (K i) (ymLaw (G := G) n d T k j) F) =ᵐ[ymLaw (G := G) n d T k j]
        condExp (K (i + 1)) (ymLaw (G := G) n d T k j) F) ∧
      condDefect (ymLaw (G := G) n d T k j) (K m') F G' = 0 ∧
      2 * ∫ U, (∏ i ∈ range m', θ i U) ∂(ymLaw (G := G) n d T k j) ≤ c * Real.exp (-(m * D))

/-- **The smoother-stability hypothesis (the exact filter-stability form of part (c)).** -/
def SmootherStable {T : Tuning} (B : BlockingFamily G d T) (Sep : SepPred d T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G' : GaugeConnection G d (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink d (T.side k j))) (D : ℝ),
    Measurable F → Measurable G' → (∀ U, |F U| ≤ 1) → (∀ U, |G' U| ≤ 1) → GaugeInvariant F → GaugeInvariant G' →
    DepOn F A₀ → DepOn G' B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R → Sep k j A₀ B₀ D →
    ∃ K : MeasurableSpace (GaugeConnection G d (T.side k j)),
      blockSigma B k j ≤ K ∧ K ≤ (MeasurableSpace.pi : MeasurableSpace (GaugeConnection G d (T.side k j))) ∧
      condDefect (ymLaw (G := G) n d T k j) K F G' = 0 ∧
      ∫ U, |condExp K (ymLaw (G := G) n d T k j) F U -
          condExp (blockSigma B k j) (ymLaw (G := G) n d T k j) F U| ∂(ymLaw (G := G) n d T k j)
        ≤ c * Real.exp (-(m * D))

variable [GaugeRep G n]

/-- **Reduction: smoother stability gives part (c) for the separated pairs**, on the Wilson measure of any `G` in the
package, any dimension, for any blocking family and any separation predicate. -/
theorem condDecouple_of_smootherStable {T : Tuning} {B : BlockingFamily G d T} {Sep : SepPred d T}
    (h : SmootherStable n B Sep) : CondDecouple n B Sep := by
  obtain ⟨m, hm, hR⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, hc, k₀, hk⟩ := hR R
  refine ⟨c, hc, k₀, fun k hk₀ j F G' A₀ B₀ D hFm hGm hF1 hG1 hFi hGi hFd hGd hA hB hS => ?_⟩
  have := isProbabilityMeasure_wilsonMeasure (G := G) (n := n) d (T.side k j) (T.β k)
  obtain ⟨K, hBK, hK, hMn, hbd⟩ := hk k hk₀ j F G' A₀ B₀ D hFm hGm hF1 hG1 hFi hGi hFd hGd hA hB hS
  exact (abs_condDefect_le_smoother hBK hK (Bdd1.of_measurable hFm hF1) (Bdd1.of_measurable hGm hG1) hMn).trans hbd

/-- **Reduction: annealed step-wise contraction along a chain of slices gives smoother stability.** -/
theorem smootherStable_of_annealedContraction {T : Tuning} {B : BlockingFamily G d T} {Sep : SepPred d T}
    (h : AnnealedContraction n B Sep) : SmootherStable n B Sep := by
  obtain ⟨m, hm, hR⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, hc, k₀, hk⟩ := hR R
  refine ⟨c, hc, k₀, fun k hk₀ j F G' A₀ B₀ D hFm hGm hF1 hG1 hFi hGi hFd hGd hA hB hS => ?_⟩
  have := isProbabilityMeasure_wilsonMeasure (G := G) (n := n) d (T.side k j) (T.β k)
  obtain ⟨m', K, θ, hK, hθ, hC, hMk, hMn, hbd⟩ := hk k hk₀ j F G' A₀ B₀ D hFm hGm hF1 hG1 hFi hGi hFd hGd hA hB hS
  have hmeas : blockSigma B k j ≤ (MeasurableSpace.pi : MeasurableSpace (GaugeConnection G d (T.side k j))) :=
    (B k j).meas.comap_le
  refine ⟨K m', (hK m').1, (hK m').2, hMn, ?_⟩
  exact (smoother_chain_of_steps hmeas K (fun i => (hK i).1) (fun i => (hK i).2) θ (fun i => (hθ i).1)
    (fun i U => ((hθ i).2 U).1) (fun i U => ((hθ i).2 U).2) (Bdd1.of_measurable hFm hF1) hMk hC m').trans hbd

/-- The composite: annealed step-wise contraction gives part (c) for the separated pairs. -/
theorem condDecouple_of_annealedContraction {T : Tuning} {B : BlockingFamily G d T} {Sep : SepPred d T}
    (h : AnnealedContraction n B Sep) : CondDecouple n B Sep :=
  condDecouple_of_smootherStable n (smootherStable_of_annealedContraction n h)

end YM

/-! ## The SU(2), `d = 4` instances -/

section Instance

/-- The old `PhysExtent` is the generic one at `d = 4`. -/
theorem physExtent_four (T : Tuning) (k : ℕ) {N : ℕ} (A : Finset (LatticeLink 4 N)) (R : ℝ) :
    ProofPhase.PhysExtent T k A R ↔ PhysExtent T k A R := Iff.rfl

/-- `ProofPhase.Seg2.CondDecouple` is the generic one at `SU2`, `n = 2`, `d = 4`. -/
theorem condDecouple_iff (T : Tuning) (B : ProofPhase.BlockingFamily T) (Sep : ProofPhase.Seg2.SepPred T) :
    ProofPhase.Seg2.CondDecouple T B Sep ↔ CondDecouple (G := SU2) 2 (d := 4) B Sep := Iff.rfl

/-- `ProofPhase.Seg2.SmootherStable` is the generic one. -/
theorem smootherStable_iff (T : Tuning) (B : ProofPhase.BlockingFamily T) (Sep : ProofPhase.Seg2.SepPred T) :
    ProofPhase.Seg2.SmootherStable T B Sep ↔ SmootherStable (G := SU2) 2 (d := 4) B Sep := Iff.rfl

/-- `ProofPhase.Seg2.AnnealedContraction` is the generic one. -/
theorem annealedContraction_iff (T : Tuning) (B : ProofPhase.BlockingFamily T) (Sep : ProofPhase.Seg2.SepPred T) :
    ProofPhase.Seg2.AnnealedContraction T B Sep ↔ AnnealedContraction (G := SU2) 2 (d := 4) B Sep := Iff.rfl

/-- `ProofPhase.Seg2.condDecouple_of_smootherStable` from the generic reduction. -/
theorem condDecouple_of_smootherStable_su2 {T : Tuning} {B : ProofPhase.BlockingFamily T}
    {Sep : ProofPhase.Seg2.SepPred T} (h : ProofPhase.Seg2.SmootherStable T B Sep) :
    ProofPhase.Seg2.CondDecouple T B Sep :=
  (condDecouple_iff T B Sep).2 (condDecouple_of_smootherStable 2 ((smootherStable_iff T B Sep).1 h))

/-- `ProofPhase.Seg2.smootherStable_of_annealedContraction` from the generic reduction. -/
theorem smootherStable_of_annealedContraction_su2 {T : Tuning} {B : ProofPhase.BlockingFamily T}
    {Sep : ProofPhase.Seg2.SepPred T} (h : ProofPhase.Seg2.AnnealedContraction T B Sep) :
    ProofPhase.Seg2.SmootherStable T B Sep :=
  (smootherStable_iff T B Sep).2 (smootherStable_of_annealedContraction 2 ((annealedContraction_iff T B Sep).1 h))

/-- `ProofPhase.Seg2.condDecouple_of_annealedContraction` from the generic reduction. -/
theorem condDecouple_of_annealedContraction_su2 {T : Tuning} {B : ProofPhase.BlockingFamily T}
    {Sep : ProofPhase.Seg2.SepPred T} (h : ProofPhase.Seg2.AnnealedContraction T B Sep) :
    ProofPhase.Seg2.CondDecouple T B Sep :=
  (condDecouple_iff T B Sep).2 (condDecouple_of_annealedContraction 2 ((annealedContraction_iff T B Sep).1 h))

example : @ProofPhase.Seg2.condDecouple_of_smootherStable = @condDecouple_of_smootherStable_su2 := rfl
example : @ProofPhase.Seg2.smootherStable_of_annealedContraction = @smootherStable_of_annealedContraction_su2 := rfl
example : @ProofPhase.Seg2.condDecouple_of_annealedContraction = @condDecouple_of_annealedContraction_su2 := rfl

end Instance

end ProofPhase.General
