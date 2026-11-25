/-
Proof phase, M1 task R12: the dense-class form of the observable transfer. Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/m1-r11/NOTE.md`, section R12.
-/

import ProofPhase.Interface.RandBlocking
import ProofPhase.Interface.SpectralUpgrade

/-!
# `ObsTransferPhysTW` for a class of observables, with per-observable constants

`ObsTransferPhysTW` (V3/W1Route.lean) fixes the constants `c, K` before the observables are chosen, so they are uniform over
all bounded measurable gauge-invariant observables of physical extent at most `R`. The dense-class form below keeps one rate
`m` (and the threshold level `k₀`, which depends on `R` only) but lets `c, K` depend on the observables `F, G` and their
supports `A₀, B₀` (not on the separation `D`), and restricts `F, G` to a class `Cls`. The class is a parameter: for M1 it is
the character polynomials of bounded degree in the links of a bounded region.

`obsTransferPhysTWDense_of_uniform`: the uniform statement implies the dense one for every class, so the new hypothesis is
formally weaker. The spectral upgrade (`SpectralUpgrade.lean`) is the tool that turns decay on a dense class back into decay
for all observables once a reflection-positive transfer operator is available.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift OneScale.CubeChain Positivity ProofPhase.Existence ProofPhase.RouteA ProofPhase.Torus
  ProofPhase.H1 ProofPhase.Certified ProofPhase.V3 ProofPhase.V4

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Interface

/-- **A class of fine observables**: at every level and volume, a predicate on observables of the fine torus
(for example "character polynomial of degree at most `n` in the links of a bounded set"). -/
abbrev ObsClass (T : Tuning) := ∀ k j, (GaugeConnection SU2 4 (T.side k j) → ℝ) → Prop

/-- **Dense-class form of `ObsTransferPhysTW`**: one rate `m > 0`; for each extent `R` a level `k₀`; at every level
`k ≥ k₀` and volume `j`, for `F, G` in the class (bounded, measurable, gauge invariant, supported on `A₀`, `B₀` of physical
extent at most `R`), constants `c, K ≥ 0` depending on `F, G, A₀, B₀` such that for every separation `D` the conclusions of
`ObsTransferPhysTW` hold. -/
def ObsTransferPhysTWDense (T : Tuning) (B : BlockingFamily T) (Cls : ObsClass T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink 4 (T.side k j))),
    Cls k j F → Cls k j G →
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R →
    ∃ c K : ℝ, 0 ≤ c ∧ 0 ≤ K ∧ ∀ D : ℝ, 0 ≤ D →
    (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * timeDist e e') →
    ∃ (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink 4 (coarseSide j))),
      Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A' ∧ DepOn g B' ∧
      (∃ vf : LatticeLink 4 (coarseSide j) → ℝ, OscBound f vf ∧ ∑ a ∈ A', vf a ≤ 2 * K * (1 + D / T.L₁) ^ 4) ∧
      LipBound geodSU2 g (fun _ => K) ∧
      (∀ x ∈ A', ∀ y ∈ B', D / 2 ≤ T.L₁ * linkDist x y) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) F U - f ((B k j).B U)| ∂(T.ym k j)
        ≤ c * Real.exp (-(m * D)) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) G U - g ((B k j).B U)| ∂(T.ym k j)
        ≤ c * Real.exp (-(m * D)) ∧
      |∫ U, F U * G U ∂(T.ym k j) -
          ∫ U, condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) F U *
            condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) G U ∂(T.ym k j)|
        ≤ c * Real.exp (-(m * D))

/-- The uniform statement implies the dense-class one, for every class. -/
theorem obsTransferPhysTWDense_of_uniform {T : Tuning} {B : BlockingFamily T} (h : ObsTransferPhysTW T B)
    (Cls : ObsClass T) : ObsTransferPhysTWDense T B Cls := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, K, hc, hK, k₀, H'⟩ := H R
  refine ⟨k₀, fun k hk j F G A₀ B₀ _ _ mF mG bF bG gF gG dF dG eF eG => ⟨c, K, hc, hK, fun D hD hsep => ?_⟩⟩
  exact H' k hk j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eF eG hsep

/-- The same, for a randomized blocking family (the observables enter the joint space as `F ∘ fst`). -/
def RandObsTransferPhysTWDense (T : Tuning) (B : RandBlockingFamily T) (Cls : ObsClass T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink 4 (T.side k j))),
    Cls k j F → Cls k j G →
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R →
    ∃ c K : ℝ, 0 ≤ c ∧ 0 ≤ K ∧ ∀ D : ℝ, 0 ≤ D →
    (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * timeDist e e') →
    ∃ (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink 4 (coarseSide j))),
      Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A' ∧ DepOn g B' ∧
      (∃ vf : LatticeLink 4 (coarseSide j) → ℝ, OscBound f vf ∧ ∑ a ∈ A', vf a ≤ 2 * K * (1 + D / T.L₁) ^ 4) ∧
      LipBound geodSU2 g (fun _ => K) ∧
      (∀ x ∈ A', ∀ y ∈ B', D / 2 ≤ T.L₁ * linkDist x y) ∧
      ∫ p, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (randJointLaw T B k j) (fun q => F q.1) p -
          f ((B k j).B p)| ∂(randJointLaw T B k j) ≤ c * Real.exp (-(m * D)) ∧
      ∫ p, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (randJointLaw T B k j) (fun q => G q.1) p -
          g ((B k j).B p)| ∂(randJointLaw T B k j) ≤ c * Real.exp (-(m * D)) ∧
      |∫ p, F p.1 * G p.1 ∂(randJointLaw T B k j) -
          ∫ p, condExp (MeasurableSpace.comap (B k j).B inferInstance) (randJointLaw T B k j) (fun q => F q.1) p *
            condExp (MeasurableSpace.comap (B k j).B inferInstance) (randJointLaw T B k j) (fun q => G q.1) p
            ∂(randJointLaw T B k j)|
        ≤ c * Real.exp (-(m * D))

/-- The uniform randomized statement implies the dense-class one, for every class. -/
theorem randObsTransferPhysTWDense_of_uniform {T : Tuning} {B : RandBlockingFamily T}
    (h : RandObsTransferPhysTW T B) (Cls : ObsClass T) : RandObsTransferPhysTWDense T B Cls := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, K, hc, hK, k₀, H'⟩ := H R
  refine ⟨k₀, fun k hk j F G A₀ B₀ _ _ mF mG bF bG gF gG dF dG eF eG => ⟨c, K, hc, hK, fun D hD hsep => ?_⟩⟩
  exact H' k hk j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eF eG hsep

end ProofPhase.Interface
