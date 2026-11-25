/-
Proof phase, generalisation phase 1: noisy blocking families, their reflection positivity and Gibbs representation,
and the multiplicative noise, for any gauge group `G` and any dimension `d` (2026-11-23).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`.
-/

import ProofPhase.Repair.MulNoise
import ProofPhase.General.GaugeGroup
import ProofPhase.General.SU2Instance
import ProofPhase.UV.Split

/-!
# Noisy blocking families over any gauge group and dimension

The generic cores of `ProofPhase.Repair.Noisy` and `ProofPhase.Repair.MulNoise` (`NoisyRPBlocking`,
`noisy_blocked_wilson_rp`, `gibbs_of_density`, `map_prod_eq_withDensity`, `mulNoise`, `mulNoiseBlocking`) are already
generic in `G` and `d`. What named SU(2) and `d = 4` were the *family* layer: `NoisyBlockingFamily`, its laws,
`noisyFamily_rp`, `KernelDensity`, `noisy_blockedLaw_gibbs`, `goodNoisyFamily`, `goodNoisy_rp`. This file restates that
layer for `G` with the gauge-group package (`GaugeGroupBase G`, `GaugeRep G n`) and `d` with `NeZero d`; the tuning
`T` is group-free. The SU(2), `d = 4` theorems are re-derived at the end with the same types as the old ones; the old
family structure is converted to the generic one field by field (`NoisyBlockingFamily.ofOld`).
-/

open MeasureTheory Finset AreaLaw.Concrete Positivity OneScale

open ProofPhase.Repair (NoisyRPBlocking noisy_blocked_wilson_rp gibbs_of_density map_prod_eq_withDensity mulNoiseBlocking)

open scoped Classical

set_option linter.unusedSectionVars false

universe u

noncomputable section

namespace ProofPhase.General

section Family

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [HasHaarProbability G]
  {d : ℕ} [NeZero d]

/-- **Noisy blocking family** over `G` in dimension `d`: at every level and volume, a noisy reflection-respecting
blocking of the fine torus onto the coarse one, with noise laws `ν₀`, `ν₊`. -/
structure NoisyBlockingFamily (G : Type*) [Group G] [MeasurableSpace G] (d : ℕ) [NeZero d] (T : Tuning)
    (Y0 Yp : ℕ → Type u) [∀ j, MeasurableSpace (Y0 j)] [∀ j, MeasurableSpace (Yp j)] where
  blk : ∀ k j, NoisyRPBlocking G d (T.side k j) (ProofPhase.coarseSide j) (Y0 j) (Yp j)
  ν0 : ∀ _k j : ℕ, Measure (Y0 j)
  νp : ∀ _k j : ℕ, Measure (Yp j)
  prob0 : ∀ k j : ℕ, IsProbabilityMeasure (ν0 k j)
  probp : ∀ k j : ℕ, IsProbabilityMeasure (νp k j)

variable {T : Tuning} {Y0 Yp : ℕ → Type u} [∀ j, MeasurableSpace (Y0 j)] [∀ j, MeasurableSpace (Yp j)]

/-- The noise law `ν₀ ⊗ ν₊ ⊗ ν₊`. -/
def NoisyBlockingFamily.noise (NB : NoisyBlockingFamily G d T Y0 Yp) (k j : ℕ) : Measure (Y0 j × Yp j × Yp j) :=
  (NB.ν0 k j).prod ((NB.νp k j).prod (NB.νp k j))

variable (n : ℕ) [HasGaugeTrace G n] [GaugeGroupBase G]

/-- The joint law of the fine field (Wilson measure of the tuning) and the noise. -/
def NoisyBlockingFamily.joint (NB : NoisyBlockingFamily G d T Y0 Yp) (k j : ℕ) :
    Measure (GaugeConnection G d (T.side k j) × (Y0 j × Yp j × Yp j)) :=
  (wilsonMeasure G n (T.β k) d (T.side k j)).prod (NB.noise k j)

/-- **The noisy blocked law**: the image of the joint law under the block map. -/
def noisyBlockedLaw (NB : NoisyBlockingFamily G d T Y0 Yp) (k j : ℕ) :
    Measure (GaugeConnection G d (ProofPhase.coarseSide j)) :=
  (NB.joint n k j).map (fun q => (NB.blk k j).B q.1 q.2)

variable [GaugeRep G n]

/-- **Every layer of a noisy blocking family is reflection positive** (S), for any `G` with the package, any `d`. -/
theorem noisyFamily_rp (NB : NoisyBlockingFamily G d T Y0 Yp) (k j : ℕ)
    {F : GaugeConnection G d (ProofPhase.coarseSide j) → ℝ} (hF : LinkDep F (posHalfLinks d (ProofPhase.coarseSide j)))
    (mF : Measurable F) (bF : ∃ C, ∀ V, |F V| ≤ C) :
    0 ≤ ∫ c, ∫ q : Yp j × Yp j, ∫ U, F ((NB.blk k j).B U (c, q.1, q.2)) *
        F (thetaConn ((NB.blk k j).B U (c, q.1, q.2))) *
        ∏ p ∈ (univ : Finset (LatticePlaquette d (T.side k j))), Real.exp (T.β k * xp n p U)
          ∂(productHaar G d (T.side k j)) ∂((NB.νp k j).prod (NB.νp k j)) ∂(NB.ν0 k j) := by
  have := NB.probp k j
  exact noisy_blocked_wilson_rp GaugeRep.continuous_rep GaugeRep.unitary_rep (T.even_side k j) (NB.blk k j)
    (NB.ν0 k j) (NB.νp k j) (T.β k) hF mF bF

/-- Coarse potentials of volume `j` over `G` in dimension `d`. -/
abbrev CoarsePot (G : Type*) (d j : ℕ) [NeZero d] :=
  Finset (LatticeLink d (ProofPhase.coarseSide j)) → GaugeConnection G d (ProofPhase.coarseSide j) → ℝ

/-- **Kernel density**: for every fine field `U`, the block variable `B(U, η)` has, under the noise, a law with a
density `κ(U, ·)` w.r.t. product Haar, jointly measurable, between `m > 0` and `M`. -/
def KernelDensity (NB : NoisyBlockingFamily G d T Y0 Yp) (k j : ℕ) : Prop :=
  ∃ (κ : GaugeConnection G d (T.side k j) → GaugeConnection G d (ProofPhase.coarseSide j) → ℝ) (m Mx : ℝ),
    Measurable (Function.uncurry κ) ∧ 0 < m ∧ (∀ U φ, m ≤ κ U φ) ∧ (∀ U φ, κ U φ ≤ Mx) ∧
    ∀ U, (NB.noise k j).map (fun η => (NB.blk k j).B U η) =
      (productHaar G d (ProofPhase.coarseSide j)).withDensity (fun φ => ENNReal.ofReal (κ U φ))

/-- **The Gibbs representation for noisy blockings** (S): with a kernel density, the noisy blocked law is the Gibbs
measure of a bounded coarse potential. -/
theorem noisy_blockedLaw_gibbs (NB : NoisyBlockingFamily G d T Y0 Yp) (k j : ℕ) (hK : KernelDensity NB k j) :
    ∃ V : CoarsePot G d j, Attempts.R3.Potential (fun A => A) V ∧
      noisyBlockedLaw n NB k j = Attempts.R3.gibbsMeasure (haarG G) V := by
  obtain ⟨κ, m, Mx, hκ, hm, hlo, hhi, hker⟩ := hK
  have := NB.probp k j
  have := NB.prob0 k j
  have := isProbabilityMeasure_wilsonMeasure (G := G) (n := n) d (T.side k j) (T.β k)
  have : IsProbabilityMeasure (NB.noise k j) := by unfold NoisyBlockingFamily.noise; infer_instance
  have hdens := map_prod_eq_withDensity (ι := LatticeLink d (ProofPhase.coarseSide j)) (haarG G)
    (wilsonMeasure G n (T.β k) d (T.side k j)) (NB.noise k j) ((NB.blk k j).meas) hκ hlo hm.le hhi hker
  have hρm : Measurable (fun φ => ∫ U, κ U φ ∂(wilsonMeasure G n (T.β k) d (T.side k j))) :=
    (hκ.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable
  have mκ : ∀ φ, Measurable (fun U => κ U φ) := fun φ => hκ.comp (measurable_id.prodMk measurable_const)
  have hκi : ∀ φ, Integrable (fun U => κ U φ) (wilsonMeasure G n (T.β k) d (T.side k j)) := fun φ =>
    Integrable.of_bound (mκ φ).aestronglyMeasurable Mx (Filter.Eventually.of_forall fun U => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hm.le.trans (hlo U φ))]; exact hhi U φ)
  have hlo' : ∀ φ, m ≤ ∫ U, κ U φ ∂(wilsonMeasure G n (T.β k) d (T.side k j)) := fun φ => by
    have := integral_mono (integrable_const m) (hκi φ) (fun U => hlo U φ)
    simpa using this
  have hhi' : ∀ φ, ∫ U, κ U φ ∂(wilsonMeasure G n (T.β k) d (T.side k j)) ≤ Mx := fun φ => by
    have := integral_mono (hκi φ) (integrable_const Mx) (fun U => hhi U φ)
    simpa using this
  have : IsProbabilityMeasure (NB.joint n k j) := by unfold NoisyBlockingFamily.joint; infer_instance
  have : IsProbabilityMeasure (noisyBlockedLaw n NB k j) := by
    unfold noisyBlockedLaw
    infer_instance
  exact gibbs_of_density (haarG G) (noisyBlockedLaw n NB k j) hρm hm hlo' hhi' hdens

end Family

/-! ## The multiplicative noise family -/

section Mul

variable {G : Type u} [Group G] [TopologicalSpace G] [MeasurableSpace G] [HasHaarProbability G]
  {d : ℕ} [NeZero d] {n : ℕ} [HasGaugeTrace G n] [GaugeGroupBase G] [GaugeRep G n]

/-- **The multiplicative noisy family of a family of reflection-respecting blockings**: independent noise with
single-link law `τ` on every coarse link. (`goodNoisyFamily` is the case of the good blocking.) -/
def mulNoiseFamily (T : Tuning) (P : ∀ k j, ProofPhase.RPBlocking G d (T.side k j) (ProofPhase.coarseSide j))
    (τ : Measure G) [IsProbabilityMeasure τ] :
    NoisyBlockingFamily G d T (fun j => FixLink d (ProofPhase.coarseSide j) → G)
      (fun j => PosLink d (ProofPhase.coarseSide j) → G) where
  blk k j := mulNoiseBlocking (ProofPhase.RouteA.even_coarseSide j) (P k j)
  ν0 _ _ := Measure.pi fun _ => τ
  νp _ _ := Measure.pi fun _ => τ
  prob0 _ _ := inferInstance
  probp _ _ := inferInstance

/-- **Every layer of the multiplicative noisy family is reflection positive** (S). -/
theorem mulNoise_rp (T : Tuning) (P : ∀ k j, ProofPhase.RPBlocking G d (T.side k j) (ProofPhase.coarseSide j))
    (τ : Measure G) [IsProbabilityMeasure τ] (k j : ℕ) {F : GaugeConnection G d (ProofPhase.coarseSide j) → ℝ}
    (hF : LinkDep F (posHalfLinks d (ProofPhase.coarseSide j))) (mF : Measurable F) (bF : ∃ C, ∀ V, |F V| ≤ C) :
    0 ≤ ∫ c, ∫ q : (PosLink d (ProofPhase.coarseSide j) → G) ×
          (PosLink d (ProofPhase.coarseSide j) → G), ∫ U,
        F (((mulNoiseFamily T P τ).blk k j).B U (c, q.1, q.2)) *
        F (thetaConn (((mulNoiseFamily T P τ).blk k j).B U (c, q.1, q.2))) *
        ∏ p ∈ (univ : Finset (LatticePlaquette d (T.side k j))), Real.exp (T.β k * xp n p U)
          ∂(productHaar G d (T.side k j)) ∂((Measure.pi fun _ => τ).prod (Measure.pi fun _ => τ))
          ∂(Measure.pi fun _ => τ) :=
  noisyFamily_rp n (mulNoiseFamily T P τ) k j hF mF bF

end Mul

/-! ## The SU(2), `d = 4` instances -/

section Instance


/-- The old SU(2), `d = 4` family as a generic family (same fields). -/
def NoisyBlockingFamily.ofOld {T : Tuning} {Y0 Yp : ℕ → Type} [∀ j, MeasurableSpace (Y0 j)]
    [∀ j, MeasurableSpace (Yp j)] (NB : ProofPhase.Repair.NoisyBlockingFamily T Y0 Yp) :
    ProofPhase.General.NoisyBlockingFamily SU2 4 T Y0 Yp where
  blk := NB.blk
  ν0 := NB.ν0
  νp := NB.νp
  prob0 := NB.prob0
  probp := NB.probp

variable {Y0 Yp : ℕ → Type} [∀ j, MeasurableSpace (Y0 j)] [∀ j, MeasurableSpace (Yp j)] {T : Tuning}

/-- `ProofPhase.Repair.noisyFamily_rp` from the generic `noisyFamily_rp` at `SU2`, `n = 2`, `d = 4`. -/
theorem noisyFamily_rp_su2 (NB : ProofPhase.Repair.NoisyBlockingFamily T Y0 Yp) (k j : ℕ)
    {F : GaugeConnection SU2 4 (ProofPhase.coarseSide j) → ℝ} (hF : LinkDep F (posHalfLinks 4 (ProofPhase.coarseSide j)))
    (mF : Measurable F) (bF : ∃ C, ∀ V, |F V| ≤ C) :
    0 ≤ ∫ c, ∫ q : Yp j × Yp j, ∫ U, F ((NB.blk k j).B U (c, q.1, q.2)) *
        F (thetaConn ((NB.blk k j).B U (c, q.1, q.2))) *
        ∏ p ∈ (univ : Finset (LatticePlaquette 4 (T.side k j))), Real.exp (T.β k * xp 2 p U)
          ∂(productHaar SU2 4 (T.side k j)) ∂((NB.νp k j).prod (NB.νp k j)) ∂(NB.ν0 k j) :=
  noisyFamily_rp 2 (NoisyBlockingFamily.ofOld NB) k j hF mF bF

/-- `ProofPhase.Repair.noisy_blockedLaw_gibbs` from the generic version. The old `KernelDensity` is the generic one
for the converted family. -/
theorem noisy_blockedLaw_gibbs_su2 (NB : ProofPhase.Repair.NoisyBlockingFamily T Y0 Yp) (k j : ℕ)
    (hK : ProofPhase.Repair.KernelDensity NB k j) :
    ∃ V : ProofPhase.CoarsePot j, Attempts.R3.Potential (fun A => A) V ∧
      ProofPhase.Repair.noisyBlockedLaw NB k j = Attempts.R3.gibbsMeasure (haarG SU2) V :=
  noisy_blockedLaw_gibbs 2 (NoisyBlockingFamily.ofOld NB) k j hK

/-- The noisy good blocking family is the generic multiplicative family of the good blocking. -/
theorem goodNoisyFamily_eq (T : Tuning) (w : ℝ) (n : ℕ → ℕ) (hn : ∀ k, T.ℓ k = 2 ^ n k) (τ : Measure SU2)
    [IsProbabilityMeasure τ] :
    NoisyBlockingFamily.ofOld (ProofPhase.Repair.goodNoisyFamily T w n hn τ) =
      mulNoiseFamily T (ProofPhase.RouteA.goodBlocking T w n hn) τ := rfl

/-- `ProofPhase.Repair.goodNoisy_rp` from the generic `mulNoise_rp` at `SU2`, `n = 2`, `d = 4`. -/
theorem goodNoisy_rp_su2 (T : Tuning) (w : ℝ) (n : ℕ → ℕ) (hn : ∀ k, T.ℓ k = 2 ^ n k) (τ : Measure SU2)
    [IsProbabilityMeasure τ] (k j : ℕ) {F : GaugeConnection SU2 4 (ProofPhase.coarseSide j) → ℝ}
    (hF : LinkDep F (posHalfLinks 4 (ProofPhase.coarseSide j))) (mF : Measurable F) (bF : ∃ C, ∀ V, |F V| ≤ C) :
    0 ≤ ∫ c, ∫ q : (PosLink 4 (ProofPhase.coarseSide j) → SU2) ×
          (PosLink 4 (ProofPhase.coarseSide j) → SU2), ∫ U,
        F (((ProofPhase.Repair.goodNoisyFamily T w n hn τ).blk k j).B U (c, q.1, q.2)) *
        F (thetaConn (((ProofPhase.Repair.goodNoisyFamily T w n hn τ).blk k j).B U (c, q.1, q.2))) *
        ∏ p ∈ (univ : Finset (LatticePlaquette 4 (T.side k j))), Real.exp (T.β k * xp 2 p U)
          ∂(productHaar SU2 4 (T.side k j)) ∂((Measure.pi fun _ => τ).prod (Measure.pi fun _ => τ))
          ∂(Measure.pi fun _ => τ) :=
  mulNoise_rp (n := 2) T (ProofPhase.RouteA.goodBlocking T w n hn) τ k j hF mF bF

example : @ProofPhase.Repair.noisyFamily_rp = @noisyFamily_rp_su2 := rfl
example : @ProofPhase.Repair.noisy_blockedLaw_gibbs = @noisy_blockedLaw_gibbs_su2 := rfl
example : @ProofPhase.Repair.goodNoisy_rp = @goodNoisy_rp_su2 := rfl

end Instance

end ProofPhase.General
