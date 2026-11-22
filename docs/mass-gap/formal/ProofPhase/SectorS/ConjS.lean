/-
Proof phase, cycle 2, workstream B: Conjecture S stated on the assembly's objects (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c2b-conjS/NOTE.md`, sections 2 and 4.
-/

import ProofPhase.Assembly

/-!
# Conjecture S (sector transfer for a simple group) on the objects of the assembly

* **`AreaLaw T`**: one physical string tension `σ > 0` and one constant `C`; from some level on, for every rectangular
  `R × R'` Wilson loop at the origin in every plane, every infinite-volume limit point of `⟨W⟩` (SU(2) Wilson measure at
  `β_k` on the torus of side `2(j+1)ℓ_k`) is at most `C e^{−σ·(R a_k)(R' a_k)}`: uniform in volume and spacing, area in
  physical units.
* **`ConjectureS T := AreaLaw T → MassGap T`**: the owner's sector transfer for a simple group, with the area law as the
  flux-confinement hypothesis. (The act-number form `FluxGrowth T → MassGap T` is the assembly's `SectorTransfer`.)
* **`areaLaw_iff_large`** (Lean, substantive but elementary): for every `A₀`, `AreaLaw T` holds **iff** its
  restriction to loops of physical area `≥ A₀` holds. Proof: `|W| ≤ 2` and the Wilson measure is a probability measure,
  so small loops are absorbed into the constant. This is the formal content of "the area law is silent on small loops":
  whatever `AreaLaw` says, it says about loops larger than any fixed physical size. Together with the generation theorem
  (`Loops.lean`; the note's section 3.3: loops of **minimal area at most three plaquettes** already generate every gauge-
  invariant observable for SU(2)) and `GeneratorRate.lean` (the gap is decided by the rates of a generating set), this
  is the exact obstruction recorded in the note, section 4.
* `conjectureS_of_slabDecay` (Lean, definitional): Route A's `SlabDecay` discharges Conjecture S on a line of constant
  physics (it ignores the area law): like P5.1, Conjecture S lands on Route A.

**Claim discipline.** `AreaLaw` and `ConjectureS` are definitions (statements), not results. `areaLaw_iff_large` uses
the SU(2) Wilson measure only through `|Re tr U| ≤ 2` and normalisation: group-blind in substance.
-/

open MeasureTheory Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge

noncomputable section

namespace ProofPhase.SectorS

/-- The expectation of the rectangular `R × R'` Wilson loop in the plane `(μ, ν)` at the origin, level `k`, torus `j`. -/
def rectW (T : Tuning) (k j : ℕ) (μ ν : Fin 4) (R R' : ℕ) : ℝ :=
  ∫ U, wilsonLoop 2 (rectPath (0 : FinLatticeSites 4 (T.side k j)) μ ν R R') U ∂(T.ym k j)

/-- The physical area `(R a_k)(R' a_k)` of an `R × R'` loop at level `k`. -/
def physArea (T : Tuning) (k R R' : ℕ) : ℝ := (R * T.a k) * (R' * T.a k)

/-- **The area law restricted to loops of physical area at least `A₀`**, uniform in volume and spacing. -/
def AreaLawFrom (T : Tuning) (A₀ : ℝ) : Prop :=
  ∃ σ : ℝ, 0 < σ ∧ ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ μ ν : Fin 4, μ ≠ ν → ∀ R R' : ℕ, A₀ ≤ physArea T k R R' →
    ∀ h : ℝ, IsLimitPoint (fun j => rectW T k j μ ν R R') h → |h| ≤ C * Real.exp (-(σ * physArea T k R R'))

/-- **The area law** (flux confinement, the hypothesis of Conjecture S): `AreaLawFrom T 0`, every loop. -/
def AreaLaw (T : Tuning) : Prop :=
  ∃ σ : ℝ, 0 < σ ∧ ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ μ ν : Fin 4, μ ≠ ν → ∀ R R' : ℕ,
    ∀ h : ℝ, IsLimitPoint (fun j => rectW T k j μ ν R R') h → |h| ≤ C * Real.exp (-(σ * physArea T k R R'))

/-- **Conjecture S** (sector transfer for a simple group, area-law form). -/
def ConjectureS (T : Tuning) : Prop := AreaLaw T → MassGap T

/-- Wilson-loop expectations are at most `2` in absolute value. -/
theorem abs_rectW_le (T : Tuning) (k j : ℕ) (μ ν : Fin 4) (R R' : ℕ) : |rectW T k j μ ν R R'| ≤ 2 := by
  have hP := isProbabilityMeasure_gaugeMeasure (d := 4) (N := T.side k j) (G := SU2) (n := 2)
    continuous_subtype_val (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) (posWeight_wilson 2 (T.β k))
  have h := norm_integral_le_of_norm_le_const (μ := T.ym k j)
    (f := fun U => wilsonLoop 2 (rectPath (0 : FinLatticeSites 4 (T.side k j)) μ ν R R') U) (C := 2)
    (Eventually.of_forall fun U => by
      rw [Real.norm_eq_abs]
      have := abs_re_trace_le_of_unitary
        (Matrix.specialUnitaryGroup_le_unitaryGroup
          (pathHol U (rectPath (0 : FinLatticeSites 4 (T.side k j)) μ ν R R')).2)
      simp only [wilsonLoop, gaugeReTr, gaugeTrace]
      exact_mod_cast this)
  simpa [rectW] using h

/-- **The area law is silent on small loops:** for every `A₀`, `AreaLaw` is equivalent to its restriction to loops of
physical area at least `A₀` (the small loops are absorbed into the constant). -/
theorem areaLaw_iff_large (T : Tuning) (A₀ : ℝ) : AreaLaw T ↔ AreaLawFrom T A₀ := by
  constructor
  · rintro ⟨σ, hσ, C, k₀, h⟩
    exact ⟨σ, hσ, C, k₀, fun k hk μ ν hμν R R' _ => h k hk μ ν hμν R R'⟩
  · rintro ⟨σ, hσ, C, k₀, h⟩
    refine ⟨σ, hσ, max C (2 * Real.exp (σ * A₀)), k₀, fun k hk μ ν hμν R R' g hg => ?_⟩
    have hexp := Real.exp_pos (-(σ * physArea T k R R'))
    rcases le_or_gt A₀ (physArea T k R R') with hA | hA
    · exact (h k hk μ ν hμν R R' hA g hg).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hexp.le)
    · have h2 : |g| ≤ 2 := hg.abs_le (Eventually.of_forall fun j => abs_rectW_le T k j μ ν R R')
      have hsmall : 2 ≤ 2 * Real.exp (σ * A₀) * Real.exp (-(σ * physArea T k R R')) := by
        rw [mul_assoc, ← Real.exp_add]
        have : 0 ≤ σ * A₀ + -(σ * physArea T k R R') := by nlinarith
        have := Real.one_le_exp this
        linarith
      exact h2.trans (hsmall.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hexp.le))

/-- **Conjecture S lands on Route A (definitional):** on a line of constant physics `SlabDecay` gives `MassGap`, hence
Conjecture S, without using the area law. -/
theorem conjectureS_of_slabDecay {T : Tuning} (hL : OnLCP T) (hA : SlabDecay T) : ConjectureS T :=
  fun _ => (assembly_routeA hL hA).1

/-- Both sector transfers (area-law form and act-number form) are implied by the mass gap itself (definitional): they
carry content only as implications whose hypothesis is established first. -/
theorem conjectureS_of_massGap {T : Tuning} (h : MassGap T) : ConjectureS T ∧ SectorTransfer T :=
  ⟨fun _ => h, fun _ => h⟩

end ProofPhase.SectorS
