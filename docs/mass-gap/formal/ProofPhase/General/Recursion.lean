/-
Proof phase, generalisation phase 1b: the recursion lemma over any gauge group and dimension (2026-11-24).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 1b.
-/

import ProofPhase.General.Gap
import ProofPhase.General.GaugeGroup
import ProofPhase.General.SU2Instance

/-!
# The recursion lemma over any gauge group and dimension

`V4/Recursion`: the block gap at `L₁` (bounded W₁ form) and stage 2 for the `L_*` theory give the bounded block gap at
`L_*`, at the rate `min(λ₂/(4s), m)`. The coarse oscillation sum grows like `(1 + R)^d` and the tail is absorbed by
`poly_exp_le` (constant `d!/r^d`, `24/r^4` for `d = 4`). The cost distance is a parameter, as in `Gap.lean`.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity

open ProofPhase.RouteA (cov_transfer)
open ProofPhase.UV

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

section Recursion

variable {Gr : Type*} [Group Gr] [TopologicalSpace Gr] [MeasurableSpace Gr] [HasHaarProbability Gr]
  (nr : ℕ) [HasGaugeTrace Gr nr] [GaugeGroupBase Gr] {d : ℕ} [NeZero d] (cost : Gr → Gr → ℝ)
  {M : ℕ → ℕ} [∀ j, NeZero (M j)]

def BlockGapBddW (T : Tuning) (B : BlockingFamily Gr d T) (lam : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (f g : GaugeConnection Gr d (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink d (coarseSide j)))
    (vf : LatticeLink d (coarseSide j) → ℝ) (Lg R : ℝ),
    Measurable f → Measurable g → (∀ V, |f V| ≤ 1) → (∀ V, |g V| ≤ 1) → DepOn f A → DepOn g Sg →
    OscBound f vf → 0 ≤ Lg → LipBound cost g (fun _ => Lg) → 0 ≤ R →
    (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
    |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j) -
        (∫ U, f ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j)) * ∫ U, g ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j)| ≤
      C * (1 + ∑ a ∈ A, vf a) * (1 + Lg) * Real.exp (-(lam * R))

def StageTwoW (ν : ℕ → ∀ j, Measure (GaugeConnection Gr d (coarseSide j)))
    (B₂ : ∀ _k j : ℕ, GaugeConnection Gr d (coarseSide j) → GaugeConnection Gr d (M j)) (s : ℝ) : Prop :=
  ∃ m c K : ℝ, 0 < m ∧ 0 ≤ c ∧ 0 ≤ K ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (f g : GaugeConnection Gr d (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink d (coarseSide j)))
    (vf : LatticeLink d (coarseSide j) → ℝ) (Lg R : ℝ),
    Measurable f → Measurable g → (∀ V, |f V| ≤ 1) → (∀ V, |g V| ≤ 1) → DepOn f A → DepOn g Sg →
    OscBound f vf → 0 ≤ Lg → LipBound cost g (fun _ => Lg) → 0 ≤ R →
    (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
    ∃ (f₂ g₂ : GaugeConnection Gr d (M j) → ℝ) (A₂ S₂ : Finset (LatticeLink d (M j)))
      (v₂ : LatticeLink d (M j) → ℝ) (L₂ : ℝ),
      Measurable f₂ ∧ Measurable g₂ ∧ (∀ W, |f₂ W| ≤ 1) ∧ (∀ W, |g₂ W| ≤ 1) ∧ DepOn f₂ A₂ ∧ DepOn g₂ S₂ ∧
      OscBound f₂ v₂ ∧ ∑ a ∈ A₂, v₂ a ≤ K * (1 + ∑ a ∈ A, vf a) * (1 + R) ^ d ∧
      0 ≤ L₂ ∧ L₂ ≤ K * (1 + Lg) ∧ LipBound cost g₂ (fun _ => L₂) ∧
      (∀ x ∈ A₂, ∀ y ∈ S₂, R / 2 ≤ s * linkDist x y) ∧
      ∫ V, |condExp (MeasurableSpace.comap (B₂ k j) inferInstance) (ν k j) f V - f₂ (B₂ k j V)| ∂(ν k j)
        ≤ c * (1 + ∑ a ∈ A, vf a) * (1 + Lg) * Real.exp (-(m * R)) ∧
      ∫ V, |condExp (MeasurableSpace.comap (B₂ k j) inferInstance) (ν k j) g V - g₂ (B₂ k j V)| ∂(ν k j)
        ≤ c * (1 + ∑ a ∈ A, vf a) * (1 + Lg) * Real.exp (-(m * R)) ∧
      |∫ V, f V * g V ∂(ν k j) -
          ∫ V, condExp (MeasurableSpace.comap (B₂ k j) inferInstance) (ν k j) f V *
            condExp (MeasurableSpace.comap (B₂ k j) inferInstance) (ν k j) g V ∂(ν k j)|
        ≤ c * (1 + ∑ a ∈ A, vf a) * (1 + Lg) * Real.exp (-(m * R))

variable [GaugeRep Gr nr]

theorem blockGapBddW_of_stageTwo {T : Tuning} (B₁ : BlockingFamily Gr d T)
    (B₂ : ∀ _k j : ℕ, GaugeConnection Gr d (coarseSide j) → GaugeConnection Gr d (M j))
    (hB₂ : ∀ k j : ℕ, Measurable (B₂ k j)) {s lam₂ : ℝ} (hs : 0 < s) (hlam₂ : 0 < lam₂)
    (hIR : LawGapBddW cost (fun k j => (blockedLaw nr T B₁ k j).map (B₂ k j)) lam₂)
    (hX : StageTwoW cost (blockedLaw nr T B₁) B₂ s) :
    ∃ lam : ℝ, 0 < lam ∧ BlockGapBddW nr cost T B₁ lam := by
  obtain ⟨C₂, hC₂, k₂, H2⟩ := hIR
  obtain ⟨m, c, K, hm, hc, hK, k₃, HX⟩ := hX
  set r := lam₂ / (4 * s)
  have hr : 0 < r := by positivity
  set lam := min r m
  have hlam : 0 < lam := lt_min hr hm
  refine ⟨lam, hlam, C₂ * (1 + K) ^ 2 * ((Nat.factorial d : ℝ) / r ^ d * Real.exp r) + 5 * c, by positivity, max k₂ k₃,
    fun k hk j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg hlip hR0 hR => ?_⟩
  have hk₂ : k₂ ≤ k := (le_max_left _ _).trans hk
  have hk₃ : k₃ ≤ k := (le_max_right _ _).trans hk
  have hS : 0 ≤ ∑ a ∈ A, vf a := sum_osc_nonneg hvf A
  obtain ⟨f₂, g₂, A₂, S₂, v₂, L₂, mf₂, mg₂, bf₂, bg₂, hf₂A, hg₂S, hv₂, hsum₂, hL₂0, hL₂, hlip₂, hsep₂, hEF, hEG,
    hdec⟩ := HX k hk₃ j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg hlip hR0 hR
  have := isProbabilityMeasure_wilsonMeasure (G := Gr) (n := nr) d (T.side k j) (T.β k)
  have : IsProbabilityMeasure (blockedLaw nr T B₁ k j) := (Measure.isProbabilityMeasure_map_iff (B₁ k j).meas.aemeasurable).2 inferInstance
  -- the Wilson block covariance is the covariance under the `L_*` law
  rw [Effective.cov_map (ymLaw (G := Gr) nr d T k j) (B₁ k j).meas ⟨mf, 1, bf⟩ ⟨mg, 1, bg⟩]
  have eν : (ymLaw (G := Gr) nr d T k j).map (B₁ k j).B = blockedLaw nr T B₁ k j := rfl
  rw [eν]
  -- transfer to `L₁` on the `L_*` law
  have htr := cov_transfer (blockedLaw nr T B₁ k j) (hB₂ k j) mf mg bf bg mf₂ mg₂ bf₂ bg₂ hEF hEG hdec
  rw [Effective.cov_map (blockedLaw nr T B₁ k j) (hB₂ k j) ⟨mf₂, 1, bf₂⟩ ⟨mg₂, 1, bg₂⟩] at htr
  -- the `L₁` input
  have hsep' : ∀ x ∈ A₂, ∀ y ∈ S₂, R / (2 * s) ≤ linkDist x y := by
    intro x hx y hy
    rw [div_le_iff₀ (by positivity)]
    have := hsep₂ x hx y hy
    linarith
  have hir := H2 k hk₂ j f₂ g₂ A₂ S₂ v₂ L₂ (R / (2 * s)) mf₂ mg₂ bf₂ bg₂ hf₂A hg₂S hv₂ hL₂0 hlip₂ (by positivity) hsep'
  beta_reduce at hir
  -- constants
  set S := ∑ a ∈ A, vf a
  have hS4 : 1 ≤ (1 + R) ^ d := one_le_pow₀ (by linarith)
  have hP : 1 ≤ (1 + S) * (1 + R) ^ d := one_le_mul_of_one_le_of_one_le (by linarith) hS4
  have hv2 : 1 + ∑ a ∈ A₂, v₂ a ≤ (1 + K) * ((1 + S) * (1 + R) ^ d) := by
    have e : K * (1 + S) * (1 + R) ^ d = K * ((1 + S) * (1 + R) ^ d) := by ring
    have e' : (1 + K) * ((1 + S) * (1 + R) ^ d) = (1 + S) * (1 + R) ^ d + K * ((1 + S) * (1 + R) ^ d) := by ring
    linarith
  have hl2 : 1 + L₂ ≤ (1 + K) * (1 + Lg) := by
    have e' : (1 + K) * (1 + Lg) = 1 + Lg + K * (1 + Lg) := by ring
    linarith
  have hv2' : 0 ≤ 1 + ∑ a ∈ A₂, v₂ a := by have := sum_osc_nonneg hv₂ A₂; linarith
  have hprod : C₂ * (1 + ∑ a ∈ A₂, v₂ a) * (1 + L₂) ≤
      C₂ * (1 + K) ^ 2 * (1 + S) * (1 + Lg) * (1 + R) ^ d := by
    have h1 : (1 + ∑ a ∈ A₂, v₂ a) * (1 + L₂) ≤ ((1 + K) * ((1 + S) * (1 + R) ^ d)) * ((1 + K) * (1 + Lg)) :=
      mul_le_mul hv2 hl2 (by linarith) (mul_nonneg (by linarith) (by linarith))
    calc C₂ * (1 + ∑ a ∈ A₂, v₂ a) * (1 + L₂) = C₂ * ((1 + ∑ a ∈ A₂, v₂ a) * (1 + L₂)) := by ring
      _ ≤ C₂ * (((1 + K) * ((1 + S) * (1 + R) ^ d)) * ((1 + K) * (1 + Lg))) :=
          mul_le_mul_of_nonneg_left h1 hC₂
      _ = C₂ * (1 + K) ^ 2 * (1 + S) * (1 + Lg) * (1 + R) ^ d := by ring
  have e1 : lam₂ * (R / (2 * s)) = 2 * r * R := by simp only [r]; field_simp; ring
  have hpoly := poly_exp_le d hr hR0
  have hE1 : Real.exp (-(r * R)) ≤ Real.exp (-(lam * R)) :=
    Real.exp_le_exp.mpr (by have := mul_le_mul_of_nonneg_right (min_le_left r m) hR0; linarith)
  have hE2 : Real.exp (-(m * R)) ≤ Real.exp (-(lam * R)) :=
    Real.exp_le_exp.mpr (by have := mul_le_mul_of_nonneg_right (min_le_right r m) hR0; linarith)
  set P := C₂ * (1 + K) ^ 2 * (1 + S) * (1 + Lg) with hPdef
  have hQ0 : 0 ≤ (1 + S) * (1 + Lg) := mul_nonneg (by linarith) (by linarith)
  have hP0 : 0 ≤ P := by
    rw [hPdef]
    have : 0 ≤ C₂ * (1 + K) ^ 2 := mul_nonneg hC₂ (by positivity)
    have := mul_nonneg this hQ0
    calc (0 : ℝ) ≤ C₂ * (1 + K) ^ 2 * ((1 + S) * (1 + Lg)) := this
      _ = C₂ * (1 + K) ^ 2 * (1 + S) * (1 + Lg) := by ring
  calc _ ≤ |∫ x, f₂ x * g₂ x ∂((blockedLaw nr T B₁ k j).map (B₂ k j)) -
          (∫ x, f₂ x ∂((blockedLaw nr T B₁ k j).map (B₂ k j))) * ∫ x, g₂ x ∂((blockedLaw nr T B₁ k j).map (B₂ k j))| +
          5 * (c * (1 + S) * (1 + Lg) * Real.exp (-(m * R))) := htr
    _ ≤ C₂ * (1 + ∑ a ∈ A₂, v₂ a) * (1 + L₂) * Real.exp (-(lam₂ * (R / (2 * s)))) +
          5 * (c * (1 + S) * (1 + Lg) * Real.exp (-(m * R))) := by linarith [hir]
    _ ≤ P * (1 + R) ^ d * Real.exp (-(2 * r * R)) +
          5 * c * ((1 + S) * (1 + Lg)) * Real.exp (-(lam * R)) := by
        rw [e1]
        have h6 := mul_le_mul_of_nonneg_right hprod (Real.exp_pos (-(2 * r * R))).le
        have h7 : c * ((1 + S) * (1 + Lg)) * Real.exp (-(m * R)) ≤
            c * ((1 + S) * (1 + Lg)) * Real.exp (-(lam * R)) :=
          mul_le_mul_of_nonneg_left hE2 (mul_nonneg hc hQ0)
        have e3 : c * (1 + S) * (1 + Lg) * Real.exp (-(m * R)) = c * ((1 + S) * (1 + Lg)) * Real.exp (-(m * R)) := by
          ring
        rw [hPdef]
        linarith [h6, h7, e3]
    _ = P * ((1 + R) ^ d * Real.exp (-(2 * r * R))) +
          5 * c * ((1 + S) * (1 + Lg)) * Real.exp (-(lam * R)) := by ring
    _ ≤ P * ((Nat.factorial d : ℝ) / r ^ d * Real.exp r * Real.exp (-(r * R))) +
          5 * c * ((1 + S) * (1 + Lg)) * Real.exp (-(lam * R)) := by gcongr
    _ ≤ P * ((Nat.factorial d : ℝ) / r ^ d * Real.exp r * Real.exp (-(lam * R))) +
          5 * c * ((1 + S) * (1 + Lg)) * Real.exp (-(lam * R)) := by gcongr
    _ = (C₂ * (1 + K) ^ 2 * ((Nat.factorial d : ℝ) / r ^ d * Real.exp r) + 5 * c) * (1 + S) * (1 + Lg) * Real.exp (-(lam * R)) := by
        rw [hPdef]; ring

theorem blockGapBddW_of_levelDprimeWOn {P : ℝ} (hc0 : ∀ a b, 0 ≤ cost a b) (hP : ∀ a b, cost a b ≤ P) {T : Tuning} (B₁ : BlockingFamily Gr d T)
    (B₂ : ∀ _k j : ℕ, GaugeConnection Gr d (coarseSide j) → GaugeConnection Gr d (M j))
    (hB₂ : ∀ k j : ℕ, Measurable (B₂ k j)) {s lam₂ : ℝ} (hs : 0 < s) (hlam₂ : 0 < lam₂)
    (hD : LevelDprimeWOn cost (fun k j => (blockedLaw nr T B₁ k j).map (B₂ k j)) lam₂)
    (hX : StageTwoW cost (blockedLaw nr T B₁) B₂ s) :
    ∃ lam : ℝ, 0 < lam ∧ BlockGapBddW nr cost T B₁ lam :=
  blockGapBddW_of_stageTwo nr cost B₁ B₂ hB₂ hs hlam₂ (lawGapBddW_of_lawGapW cost (lawGapW_of_levelDprimeWOn cost hc0 hP hlam₂.le hD)) hX

end Recursion

/-! ## The SU(2), `d = 4` instances -/

section Instance

variable {M : ℕ → ℕ} [∀ j, NeZero (M j)]

theorem blockGapBddW_iff (T : Tuning) (B : ProofPhase.BlockingFamily T) (lam : ℝ) :
    ProofPhase.V4.BlockGapBddW T B lam ↔ BlockGapBddW 2 ProofPhase.Certified.geodSU2 T B lam := Iff.rfl

theorem stageTwoW_iff (ν : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (coarseSide j)))
    (B₂ : ∀ _k j : ℕ, GaugeConnection SU2 4 (coarseSide j) → GaugeConnection SU2 4 (M j)) (s : ℝ) :
    ProofPhase.V4.StageTwoW ν B₂ s ↔ StageTwoW ProofPhase.Certified.geodSU2 ν B₂ s := Iff.rfl

/-- `ProofPhase.V4.blockGapBddW_of_stageTwo` from the generic theorem at `SU2`, `n = 2`, `d = 4`. -/
theorem blockGapBddW_of_stageTwo_su2 {T : Tuning} (B₁ : ProofPhase.BlockingFamily T)
    (B₂ : ∀ _k j : ℕ, GaugeConnection SU2 4 (coarseSide j) → GaugeConnection SU2 4 (M j))
    (hB₂ : ∀ k j : ℕ, Measurable (B₂ k j)) {s lam₂ : ℝ} (hs : 0 < s) (hlam₂ : 0 < lam₂)
    (hIR : ProofPhase.V4.LawGapBddW (fun k j => (ProofPhase.blockedLaw T B₁ k j).map (B₂ k j)) lam₂)
    (hX : ProofPhase.V4.StageTwoW (ProofPhase.blockedLaw T B₁) B₂ s) :
    ∃ lam : ℝ, 0 < lam ∧ ProofPhase.V4.BlockGapBddW T B₁ lam :=
  blockGapBddW_of_stageTwo 2 ProofPhase.Certified.geodSU2 B₁ B₂ hB₂ hs hlam₂ hIR hX

/-- `ProofPhase.V4.blockGapBddW_of_levelDprimeWOn` from the generic theorem. -/
theorem blockGapBddW_of_levelDprimeWOn_su2 {T : Tuning} (B₁ : ProofPhase.BlockingFamily T)
    (B₂ : ∀ _k j : ℕ, GaugeConnection SU2 4 (coarseSide j) → GaugeConnection SU2 4 (M j))
    (hB₂ : ∀ k j : ℕ, Measurable (B₂ k j)) {s lam₂ : ℝ} (hs : 0 < s) (hlam₂ : 0 < lam₂)
    (hD : ProofPhase.V4.LevelDprimeWOn (fun k j => (ProofPhase.blockedLaw T B₁ k j).map (B₂ k j)) lam₂)
    (hX : ProofPhase.V4.StageTwoW (ProofPhase.blockedLaw T B₁) B₂ s) :
    ∃ lam : ℝ, 0 < lam ∧ ProofPhase.V4.BlockGapBddW T B₁ lam :=
  blockGapBddW_of_levelDprimeWOn 2 ProofPhase.Certified.geodSU2 ProofPhase.Certified.geodSU2_nonneg
    ProofPhase.Certified.geodSU2_le_pi B₁ B₂ hB₂ hs hlam₂ hD hX

example : @ProofPhase.V4.blockGapBddW_of_stageTwo = @blockGapBddW_of_stageTwo_su2 := rfl
example : @ProofPhase.V4.blockGapBddW_of_levelDprimeWOn = @blockGapBddW_of_levelDprimeWOn_su2 := rfl

end Instance

end ProofPhase.General
