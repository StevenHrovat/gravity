/-
Proof phase, cycle 5, workstream 1 (c5a-v4): the recursion lemma (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c5a-v4/NOTE.md`.
-/

import ProofPhase.V4.Gap

/-!
# The recursion lemma: a v3-type input set at `L₁ = s·L_*`, stated for the `L_*` theory, gives the block gap at `L_*`

Version 4 takes the tuning's unit to be `L_*` and asks the infrared input `BlockGapUnifW` (or its bounded form
`BlockGapBddW`) there. Cycles 2 to 4 proved the gap from inputs at a larger scale `L₁`: D′ in W₁ form for the `L₁`-blocked
law and the transfer (quasi-locality plus conditional decoupling) for the step to `L₁`. This file keeps them as **a proved
strategy for the infrared input** (strategy (a) of the draft blueprint): stated for the `L_*` theory, i.e. for the laws
`ν k j = blockedLaw T B₁ k j` of the `L_*` block field and a second blocking `B₂ k j` from the `L_*` torus to an `L₁` torus
(side `M j`; scale ratio `s`, in the draft `s = 2^r`), they imply the bounded block gap at `L_*`.

* `StageTwoW ν B₂ s` (**named hypothesis, open; Lemma X of c3a/v3 stated for the `L_*` theory**): for `L_*` block
  observables `f` (`|f| ≤ 1`, oscillations `vf` on `A`) and `g` (`|g| ≤ 1`, geodesic-Lipschitz `Lg` on `Sg`) at `L_*`
  link distance `≥ R ≥ 0`: `L₁` approximants `f₂`, `g₂` (`|·| ≤ 1`, oscillation sum `≤ K (1 + Σvf)(1 + R)⁴`, Lipschitz
  constant `≤ K (1 + Lg)`, `L₁` link distance `≥ R/(2s)`), with (a)+(b) `‖E_ν[f | B₂] − f₂ ∘ B₂‖₁`,
  `‖E_ν[g | B₂] − g₂ ∘ B₂‖₁` and (c) `|E_ν[fg] − E_ν[E[f|B₂] E[g|B₂]]|` all `≤ c (1 + Σvf)(1 + Lg) e^{−mR}`.
  This is v3's `ObsTransferPhysTW` with the fine field replaced by the `L_*` block field (time separation not needed: it
  is a statement about block observables at any separation) and the extent index replaced by the oscillation and
  Lipschitz prefactors (see "why not literally v3's shape" below).
* `blockGapBddW_of_stageTwo` (**the recursion lemma**, S): `LawGapBddW` of the `L₁` laws `(ν k j).map (B₂ k j)` at rate
  `λ₂ > 0` and `StageTwoW ν B₂ s` give `BlockGapBddW T B₁ (min(λ₂/(4s), m))`. Proof: the block covariance of the Wilson
  measure is the covariance under `ν` (`Effective.cov_map`); `RouteA.cov_transfer` on `ν` with `Φ = B₂` reduces it to the
  covariance of `f₂ ∘ B₂`, `g₂ ∘ B₂` plus `5ε`; that is a covariance of the `L₁` law (`cov_map` again), bounded by the
  `L₁` input; the polynomial factor `(1 + R)⁴` is absorbed by half the rate (`poly_exp_le`).
* `blockGapBddW_of_levelDprimeWOn` (S): the same with v3's D′ in W₁ form for the `L₁` laws (`LevelDprimeWOn`).

**Where `UV.twoStage_blocked` went.** The draft says "`twoStage_blocked` plus `torusDecayLoc_of_blockGapUnifW` applied to
block observables". For a block observable `F = f ∘ B₁` stage 1 is exact (`E[f ∘ B₁ | B₁] = f ∘ B₁`, zero defect), so the
two-stage split degenerates and what remains is the covariance transfer on the `L_*` law, done here directly.
`twoStage_blocked` stays the composition lemma for the **transfer** direction (v4's UV input at `L_*` plus stage 2 give
v3's transfer at `L₁`), which version 4 no longer needs at the top.

**Why not literally v3's shape (finding).** v3's transfer hypotheses have constants indexed by the physical extent of
the observables and additive errors `c e^{−mD}`. Fed with block observables of bounded extent they give block decay only
for block observables of bounded extent, with constants depending on the extent; but `BlockGapUnifW` and `BlockGapBddW`
quantify over block observables of **any** support (the approximants that `ObsTransferPhysTW` produces have supports of
unbounded extent, only their oscillation sum is controlled), and the homogeneous `BlockGapUnifW` would further need errors
proportional to `Σvf · Lg`, which bounded-observable estimates cannot give when `Sg` is large. So the true recursion lemma
(i) lands in the bounded form `BlockGapBddW` (which is all the top theorem consumes) and (ii) needs the stage-2 errors with
the prefactor `(1 + Σvf)(1 + Lg)` instead of an extent index. Dobrushin-type conditional mixing gives errors of exactly
that shape.

**Claim level.** The lemma is bookkeeping (S). Its inputs are of gap strength at `L₁ ≈ 2.8/√σ` (review 2.2): the `L₁`
block gap is the infrared statement one scale up, and part (c) of `StageTwoW` is, by `UV.condDefect_eq`, equivalent to the
decay of the `L_*` block covariances once the `L₁` side decays (difficulty conservation). Strategy (a) is a proved
reduction of the infrared input to these, not a proof of it.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity ProofPhase.RouteA ProofPhase.Torus ProofPhase.Certified ProofPhase.V3

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.V4

variable {M : ℕ → ℕ} [∀ j, NeZero (M j)]

/-- **Stage 2 for the `L_*` theory (named hypothesis, open; Lemma X).** See the module docstring. `ν k j` are the laws of
the `L_*` block field, `B₂ k j` the blocking from the `L_*` torus to the `L₁` torus of side `M j`, `s > 0` the scale
ratio `L₁/L_*` (the `L₁` approximants of block observables at `L_*` distance `≥ R` are at `L₁` distance `≥ R/(2s)`). -/
def StageTwoW (ν : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (coarseSide j)))
    (B₂ : ∀ k j : ℕ, GaugeConnection SU2 4 (coarseSide j) → GaugeConnection SU2 4 (M j)) (s : ℝ) : Prop :=
  ∃ m c K : ℝ, 0 < m ∧ 0 ≤ c ∧ 0 ≤ K ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink 4 (coarseSide j)))
    (vf : LatticeLink 4 (coarseSide j) → ℝ) (Lg R : ℝ),
    Measurable f → Measurable g → (∀ V, |f V| ≤ 1) → (∀ V, |g V| ≤ 1) → DepOn f A → DepOn g Sg →
    OscBound f vf → 0 ≤ Lg → LipBound geodSU2 g (fun _ => Lg) → 0 ≤ R →
    (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
    ∃ (f₂ g₂ : GaugeConnection SU2 4 (M j) → ℝ) (A₂ S₂ : Finset (LatticeLink 4 (M j)))
      (v₂ : LatticeLink 4 (M j) → ℝ) (L₂ : ℝ),
      Measurable f₂ ∧ Measurable g₂ ∧ (∀ W, |f₂ W| ≤ 1) ∧ (∀ W, |g₂ W| ≤ 1) ∧ DepOn f₂ A₂ ∧ DepOn g₂ S₂ ∧
      OscBound f₂ v₂ ∧ ∑ a ∈ A₂, v₂ a ≤ K * (1 + ∑ a ∈ A, vf a) * (1 + R) ^ 4 ∧
      0 ≤ L₂ ∧ L₂ ≤ K * (1 + Lg) ∧ LipBound geodSU2 g₂ (fun _ => L₂) ∧
      (∀ x ∈ A₂, ∀ y ∈ S₂, R / 2 ≤ s * linkDist x y) ∧
      ∫ V, |condExp (MeasurableSpace.comap (B₂ k j) inferInstance) (ν k j) f V - f₂ (B₂ k j V)| ∂(ν k j)
        ≤ c * (1 + ∑ a ∈ A, vf a) * (1 + Lg) * Real.exp (-(m * R)) ∧
      ∫ V, |condExp (MeasurableSpace.comap (B₂ k j) inferInstance) (ν k j) g V - g₂ (B₂ k j V)| ∂(ν k j)
        ≤ c * (1 + ∑ a ∈ A, vf a) * (1 + Lg) * Real.exp (-(m * R)) ∧
      |∫ V, f V * g V ∂(ν k j) -
          ∫ V, condExp (MeasurableSpace.comap (B₂ k j) inferInstance) (ν k j) f V *
            condExp (MeasurableSpace.comap (B₂ k j) inferInstance) (ν k j) g V ∂(ν k j)|
        ≤ c * (1 + ∑ a ∈ A, vf a) * (1 + Lg) * Real.exp (-(m * R))

/-- **The recursion lemma** (S). The `L₁` block gap (bounded form, rate `λ₂ > 0`) of the laws `(ν k j).map (B₂ k j)`,
`ν = blockedLaw T B₁`, and stage 2 for the `L_*` theory give the bounded block gap at `L_*` at the rate
`min(λ₂/(4s), m)`, uniformly in the level and the volume. -/
theorem blockGapBddW_of_stageTwo {T : Tuning} (B₁ : BlockingFamily T)
    (B₂ : ∀ k j : ℕ, GaugeConnection SU2 4 (coarseSide j) → GaugeConnection SU2 4 (M j))
    (hB₂ : ∀ k j : ℕ, Measurable (B₂ k j)) {s lam₂ : ℝ} (hs : 0 < s) (hlam₂ : 0 < lam₂)
    (hIR : LawGapBddW (fun k j => (blockedLaw T B₁ k j).map (B₂ k j)) lam₂)
    (hX : StageTwoW (blockedLaw T B₁) B₂ s) :
    ∃ lam : ℝ, 0 < lam ∧ BlockGapBddW T B₁ lam := by
  obtain ⟨C₂, hC₂, k₂, H2⟩ := hIR
  obtain ⟨m, c, K, hm, hc, hK, k₃, HX⟩ := hX
  set r := lam₂ / (4 * s)
  have hr : 0 < r := by positivity
  set lam := min r m
  have hlam : 0 < lam := lt_min hr hm
  refine ⟨lam, hlam, C₂ * (1 + K) ^ 2 * (24 / r ^ 4 * Real.exp r) + 5 * c, by positivity, max k₂ k₃,
    fun k hk j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg hlip hR0 hR => ?_⟩
  have hk₂ : k₂ ≤ k := (le_max_left _ _).trans hk
  have hk₃ : k₃ ≤ k := (le_max_right _ _).trans hk
  have hS : 0 ≤ ∑ a ∈ A, vf a := sum_osc_nonneg hvf A
  obtain ⟨f₂, g₂, A₂, S₂, v₂, L₂, mf₂, mg₂, bf₂, bg₂, hf₂A, hg₂S, hv₂, hsum₂, hL₂0, hL₂, hlip₂, hsep₂, hEF, hEG,
    hdec⟩ := HX k hk₃ j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg hlip hR0 hR
  have := UV.ymProb T k j
  have : IsProbabilityMeasure (blockedLaw T B₁ k j) := (Measure.isProbabilityMeasure_map_iff (B₁ k j).meas.aemeasurable).2 inferInstance
  -- the Wilson block covariance is the covariance under the `L_*` law
  rw [Effective.cov_map (T.ym k j) (B₁ k j).meas ⟨mf, 1, bf⟩ ⟨mg, 1, bg⟩]
  have eν : (T.ym k j).map (B₁ k j).B = blockedLaw T B₁ k j := rfl
  rw [eν]
  -- transfer to `L₁` on the `L_*` law
  have htr := cov_transfer (blockedLaw T B₁ k j) (hB₂ k j) mf mg bf bg mf₂ mg₂ bf₂ bg₂ hEF hEG hdec
  rw [Effective.cov_map (blockedLaw T B₁ k j) (hB₂ k j) ⟨mf₂, 1, bf₂⟩ ⟨mg₂, 1, bg₂⟩] at htr
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
  have hS4 : 1 ≤ (1 + R) ^ 4 := one_le_pow₀ (by linarith)
  have hP : 1 ≤ (1 + S) * (1 + R) ^ 4 := one_le_mul_of_one_le_of_one_le (by linarith) hS4
  have hv2 : 1 + ∑ a ∈ A₂, v₂ a ≤ (1 + K) * ((1 + S) * (1 + R) ^ 4) := by
    have e : K * (1 + S) * (1 + R) ^ 4 = K * ((1 + S) * (1 + R) ^ 4) := by ring
    have e' : (1 + K) * ((1 + S) * (1 + R) ^ 4) = (1 + S) * (1 + R) ^ 4 + K * ((1 + S) * (1 + R) ^ 4) := by ring
    linarith
  have hl2 : 1 + L₂ ≤ (1 + K) * (1 + Lg) := by
    have e' : (1 + K) * (1 + Lg) = 1 + Lg + K * (1 + Lg) := by ring
    linarith
  have hv2' : 0 ≤ 1 + ∑ a ∈ A₂, v₂ a := by have := sum_osc_nonneg hv₂ A₂; linarith
  have hprod : C₂ * (1 + ∑ a ∈ A₂, v₂ a) * (1 + L₂) ≤
      C₂ * (1 + K) ^ 2 * (1 + S) * (1 + Lg) * (1 + R) ^ 4 := by
    have h1 : (1 + ∑ a ∈ A₂, v₂ a) * (1 + L₂) ≤ ((1 + K) * ((1 + S) * (1 + R) ^ 4)) * ((1 + K) * (1 + Lg)) :=
      mul_le_mul hv2 hl2 (by linarith) (mul_nonneg (by linarith) (by linarith))
    calc C₂ * (1 + ∑ a ∈ A₂, v₂ a) * (1 + L₂) = C₂ * ((1 + ∑ a ∈ A₂, v₂ a) * (1 + L₂)) := by ring
      _ ≤ C₂ * (((1 + K) * ((1 + S) * (1 + R) ^ 4)) * ((1 + K) * (1 + Lg))) :=
          mul_le_mul_of_nonneg_left h1 hC₂
      _ = C₂ * (1 + K) ^ 2 * (1 + S) * (1 + Lg) * (1 + R) ^ 4 := by ring
  have e1 : lam₂ * (R / (2 * s)) = 2 * r * R := by simp only [r]; field_simp; ring
  have hpoly := poly_exp_le hr hR0
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
  calc _ ≤ |∫ x, f₂ x * g₂ x ∂((blockedLaw T B₁ k j).map (B₂ k j)) -
          (∫ x, f₂ x ∂((blockedLaw T B₁ k j).map (B₂ k j))) * ∫ x, g₂ x ∂((blockedLaw T B₁ k j).map (B₂ k j))| +
          5 * (c * (1 + S) * (1 + Lg) * Real.exp (-(m * R))) := htr
    _ ≤ C₂ * (1 + ∑ a ∈ A₂, v₂ a) * (1 + L₂) * Real.exp (-(lam₂ * (R / (2 * s)))) +
          5 * (c * (1 + S) * (1 + Lg) * Real.exp (-(m * R))) := by linarith [hir]
    _ ≤ P * (1 + R) ^ 4 * Real.exp (-(2 * r * R)) +
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
    _ = P * ((1 + R) ^ 4 * Real.exp (-(2 * r * R))) +
          5 * c * ((1 + S) * (1 + Lg)) * Real.exp (-(lam * R)) := by ring
    _ ≤ P * (24 / r ^ 4 * Real.exp r * Real.exp (-(r * R))) +
          5 * c * ((1 + S) * (1 + Lg)) * Real.exp (-(lam * R)) := by gcongr
    _ ≤ P * (24 / r ^ 4 * Real.exp r * Real.exp (-(lam * R))) +
          5 * c * ((1 + S) * (1 + Lg)) * Real.exp (-(lam * R)) := by gcongr
    _ = (C₂ * (1 + K) ^ 2 * (24 / r ^ 4 * Real.exp r) + 5 * c) * (1 + S) * (1 + Lg) * Real.exp (-(lam * R)) := by
        rw [hPdef]; ring

/-- **The recursion lemma with v3's D′ at `L₁`** (S): `LevelDprimeWOn` of the `L₁` laws `(ν k j).map (B₂ k j)` (v3's
`LevelDprimeW`, stated for the `L_*` theory) and `StageTwoW` give the bounded block gap at `L_*`. -/
theorem blockGapBddW_of_levelDprimeWOn {T : Tuning} (B₁ : BlockingFamily T)
    (B₂ : ∀ k j : ℕ, GaugeConnection SU2 4 (coarseSide j) → GaugeConnection SU2 4 (M j))
    (hB₂ : ∀ k j : ℕ, Measurable (B₂ k j)) {s lam₂ : ℝ} (hs : 0 < s) (hlam₂ : 0 < lam₂)
    (hD : LevelDprimeWOn (fun k j => (blockedLaw T B₁ k j).map (B₂ k j)) lam₂)
    (hX : StageTwoW (blockedLaw T B₁) B₂ s) :
    ∃ lam : ℝ, 0 < lam ∧ BlockGapBddW T B₁ lam :=
  blockGapBddW_of_stageTwo B₁ B₂ hB₂ hs hlam₂ (lawGapBddW_of_lawGapW (lawGapW_of_levelDprimeWOn hlam₂.le hD)) hX

end ProofPhase.V4
