/-
Proof phase, generalisation phase 1: the centre-comparison area law for any gauge group (2026-11-23).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`.
-/

import ProofPhase.Centre.Combined
import ProofPhase.General.SU2Instance

/-!
# Centre comparison plus strong-coupling Z2, for any gauge group

`ProofPhase.Centre.centre_area_law` is already group-free; only its SU(2) wrapper `su2_area_law_of_mixture` named the
group. Here the wrapper is stated for any group `G` with a matrix representation of dimension `n` and a Haar
probability measure, with the bound `B` on the class function `Re tr` and the bound `M` on the weight as parameters
(for a unitary representation `B = n` by `abs_gaugeReTr_le`; for SU(2), `B = M = 2`). The SU(2) wrapper is re-derived
below with the same type as the old theorem.

The named hypothesis is the same: the Wilson loop expectation is a mixture of plaquette-form Z2 correlations. Which
groups satisfy it (SU(2): the `U = σ V` disintegration over `SU(2) → SO(3)`; SU(N): a mod-N version, a Z_N layer rather
than Z2) is a paper-level input, phase 3.
-/

open Finset MeasureTheory Filter Topology

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

section Combined

open AreaLaw.Assembly AreaLaw.Concrete ProofPhase.Centre

variable {d N : ℕ} [NeZero N] {G : Type*} [Group G] [MeasurableSpace G] [HasHaarProbability G] {n : ℕ}
  [HasGaugeTrace G n]

/-- **The mixture area law for any gauge group.** Under the mixture hypothesis for the Wilson measure of `G` with
`|J(v)_p| ≤ Bβ` (`J_p = β r_p`, `|r_p| ≤ B`) and `|w| ≤ M`, the area law of the repository's strong-coupling range
follows through the Z2 model, with constant `M` and coupling `Bβ`. -/
theorem area_law_of_mixture {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → LatticePlaquette d N → ℝ) (w : Ω → ℝ) {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hw : ∀ v, |w v| ≤ M)
    (hr : ∀ v p, |r v p| ≤ B) {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : Real.exp (B * β) - 1 ≤ 1 / (4 * Real.exp (16 * d + 1) * (16 * d + 1) ^ 4))
    (x : FinLatticeSites d N) {μ' ν : Fin d} (hμν : μ' < ν) (R T : ℕ)
    (hR : 1 ≤ R) (hT : 1 ≤ T) (hRN : R < N) (hTN : T < N)
    (hmix : (∫ U, wilsonLoop n (rectPath x μ' ν R T) U *
          ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N)) /
        (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N)) =
        ∫ v, w v * corr plaqSupp (fun p => β * r v p) (pathSupp (rectPath x μ' ν R T)) ∂μ) :
    |(∫ U, wilsonLoop n (rectPath x μ' ν R T) U *
          ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N)) /
        (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N))| ≤
      M * Real.exp (2 * (4 * d * (2 * (R + T)))) *
        Real.sqrt (Real.exp (16 * d + 1) * (Real.exp (B * β) - 1)) ^ (min (R * T) (N * N - R * T)) := by
  have hb : ∀ v p, |β * r v p| ≤ B * β := fun v p => by
    rw [abs_mul, abs_of_nonneg hβ]; nlinarith [hr v p, abs_nonneg (r v p)]
  have := centre_area_law μ (fun v p => β * r v p) w M hM hw (b := B * β) (mul_nonneg hB hβ) hb hsmall x hμν R T
    hR hT hRN hTN _ hmix
  refine this.trans (le_of_eq ?_)
  ring

end Combined

/-! ## The SU(2) instance -/

section Instance

open AreaLaw.Assembly AreaLaw.Concrete ProofPhase.Centre

variable {d N : ℕ} [NeZero N]

/-- `ProofPhase.Centre.su2_area_law_of_mixture` from `area_law_of_mixture` at `G = SU2`, `n = 2`, `B = M = 2`. -/
theorem su2_area_law_of_mixture_general {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → LatticePlaquette d N → ℝ) (w : Ω → ℝ) (hw : ∀ v, |w v| ≤ 2) (hr : ∀ v p, |r v p| ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : Real.exp (2 * β) - 1 ≤ 1 / (4 * Real.exp (16 * d + 1) * (16 * d + 1) ^ 4))
    (x : FinLatticeSites d N) {μ' ν : Fin d} (hμν : μ' < ν) (R T : ℕ)
    (hR : 1 ≤ R) (hT : 1 ≤ T) (hRN : R < N) (hTN : T < N)
    (hmix : (∫ U, wilsonLoop 2 (rectPath x μ' ν R T) U *
          ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 2 p U) ∂(productHaar SU2 d N)) /
        (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 2 p U) ∂(productHaar SU2 d N)) =
        ∫ v, w v * corr plaqSupp (fun p => β * r v p) (pathSupp (rectPath x μ' ν R T)) ∂μ) :
    |(∫ U, wilsonLoop 2 (rectPath x μ' ν R T) U *
          ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 2 p U) ∂(productHaar SU2 d N)) /
        (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 2 p U) ∂(productHaar SU2 d N))| ≤
      2 * Real.exp (2 * (4 * d * (2 * (R + T)))) *
        Real.sqrt (Real.exp (16 * d + 1) * (Real.exp (2 * β) - 1)) ^ (min (R * T) (N * N - R * T)) :=
  area_law_of_mixture (G := SU2) (n := 2) μ r w (M := 2) (B := 2) (by norm_num) (by norm_num) hw hr hβ hsmall x hμν R T
    hR hT hRN hTN hmix

example : @ProofPhase.Centre.su2_area_law_of_mixture = @su2_area_law_of_mixture_general := rfl

end Instance

end ProofPhase.General
