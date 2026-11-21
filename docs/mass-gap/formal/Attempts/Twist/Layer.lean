/-
Twist route, attempt round (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/twist/NOTE.md`, section 3 (Proposition T3, the layer lemma).
-/

import OneScale.Blocks

/-!
# The layer lemma: an influence from marginal total variations on nested regions

Two probability measures `μ, ν` on configurations, a decreasing chain of regions `A 0 ⊇ A 1 ⊇ … ⊇ A R = ∅`, and numbers
`τ r` bounding the total variation of the `A r`-marginals in dual form (`|μ G - ν G| ≤ 2 τ_r sup|G|` for `G` depending only on
`A r`). Then for every bounded measurable `F` depending only on `A 0`, with single-coordinate oscillations at most `L`,

  `|μ F - ν F| ≤ ∑_{r < R} 2 τ_r · |A r ∖ A (r+1)| · L`   (`layer_bound`).

Use: with `A r` the links of a block at distance `≥ r` from the boundary link `z`, the influence coefficient is bounded by the
decay of the *marginal* response with depth; a single number (a free energy, a total variation of the whole block) only
gives `τ_r ≤ τ_0` and the useless bound `2 τ_0 |B| L`.
-/

open MeasureTheory Finset OneScale

set_option linter.unusedSectionVars false

noncomputable section

namespace Attempts.Twist

variable {ι S : Type*} [DecidableEq ι] [MeasurableSpace S]

/-- The function `F` read on `A`, with the reference configuration `ξ₀` outside `A`. -/
def restrictTo (F : (ι → S) → ℝ) (A : Finset ι) (ξ₀ : ι → S) (σ : ι → S) : ℝ := F (splice A ξ₀ σ)

theorem restrictTo_depOn (F : (ι → S) → ℝ) (A : Finset ι) (ξ₀ : ι → S) : DepOn (restrictTo F A ξ₀) A := by
  intro σ σ' h
  unfold restrictTo
  congr 1
  funext i
  by_cases hi : i ∈ A <;> simp [splice, hi, h i]

theorem restrictTo_bm {F : (ι → S) → ℝ} (hF : BM F) (A : Finset ι) (ξ₀ : ι → S) : BM (restrictTo F A ξ₀) := by
  obtain ⟨C, hC⟩ := hF.bdd
  exact ⟨hF.meas.comp (measurable_splice_right A ξ₀), ⟨C, fun σ => hC _⟩⟩

/-- **Proposition T3 (layer lemma).** -/
theorem layer_bound (μ ν : Measure (ι → S)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : ℕ → Finset ι) (R : ℕ) (hanti : ∀ r, A (r + 1) ⊆ A r) (hR : A R = ∅) (τ : ℕ → ℝ)
    (hτ : ∀ r, r < R → ∀ (G : (ι → S) → ℝ) (M : ℝ), BM G → DepOn G (A r) → (∀ σ, |G σ| ≤ M) →
      |∫ σ, G σ ∂μ - ∫ σ, G σ ∂ν| ≤ 2 * τ r * M)
    {F : (ι → S) → ℝ} {L : ℝ} (hL : 0 ≤ L) (hF : BM F) (hdep : DepOn F (A 0))
    (hosc : ∀ ξ y t, y ∈ A 0 → |F ξ - F (Function.update ξ y t)| ≤ L) (ξ₀ : ι → S) :
    |∫ σ, F σ ∂μ - ∫ σ, F σ ∂ν| ≤ ∑ r ∈ range R, 2 * τ r * ((A r \ A (r + 1)).card * L) := by
  -- oscillation bound for `F` on all coordinates
  have hv : OscBound F (fun _ => L) := by
    intro σ x s
    by_cases hx : x ∈ A 0
    · exact hosc σ x s hx
    · rw [hdep.update_eq hx σ s, sub_self, abs_zero]; exact hL
  set f : ℕ → ℝ := fun r => ∫ σ, restrictTo F (A r) ξ₀ σ ∂μ - ∫ σ, restrictTo F (A r) ξ₀ σ ∂ν with hf
  -- `F_0 = F`
  have h0 : ∀ σ, restrictTo F (A 0) ξ₀ σ = F σ := by
    intro σ; unfold restrictTo
    exact hdep _ _ fun i hi => by simp [splice, hi]
  -- `F_R` is constant
  have hRc : ∀ σ, restrictTo F (A R) ξ₀ σ = F ξ₀ := by
    intro σ; unfold restrictTo; rw [hR]; congr 1
  have hf0 : f 0 = ∫ σ, F σ ∂μ - ∫ σ, F σ ∂ν := by simp only [hf, h0]
  have hfR : f R = 0 := by simp [hf, hRc]
  -- telescoping
  have htel : ∫ σ, F σ ∂μ - ∫ σ, F σ ∂ν = ∑ r ∈ range R, (f r - f (r + 1)) := by
    rw [Finset.sum_range_sub', hfR, sub_zero, hf0]
  rw [htel]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr => ?_)
  have hr' : r < R := Finset.mem_range.1 hr
  set G : (ι → S) → ℝ := fun σ => restrictTo F (A r) ξ₀ σ - restrictTo F (A (r + 1)) ξ₀ σ
  have hG : BM G := (restrictTo_bm hF _ ξ₀).sub (restrictTo_bm hF _ ξ₀)
  have hGdep : DepOn G (A r) := by
    intro σ σ' h
    simp only [G]
    rw [restrictTo_depOn F (A r) ξ₀ σ σ' h,
      restrictTo_depOn F (A (r + 1)) ξ₀ σ σ' fun i hi => h i (hanti r hi)]
  have hGb : ∀ σ, |G σ| ≤ (A r \ A (r + 1)).card * L := by
    intro σ
    have := hv.abs_sub_le (A r \ A (r + 1)) (σ := splice (A r) ξ₀ σ) (σ' := splice (A (r + 1)) ξ₀ σ) (by
      intro i hi
      by_cases h1 : i ∈ A (r + 1)
      · simp [splice, h1, hanti r h1]
      · have h2 : i ∉ A r := fun h2 => hi (Finset.mem_sdiff.2 ⟨h2, h1⟩)
        simp [splice, h1, h2])
    simpa [G, restrictTo, Finset.sum_const, nsmul_eq_mul] using this
  have hint : ∀ (m : Measure (ι → S)) [IsFiniteMeasure m], ∫ σ, G σ ∂m =
      ∫ σ, restrictTo F (A r) ξ₀ σ ∂m - ∫ σ, restrictTo F (A (r + 1)) ξ₀ σ ∂m := by
    intro m _
    exact integral_sub ((restrictTo_bm hF _ ξ₀).integrable m) ((restrictTo_bm hF _ ξ₀).integrable m)
  have key := hτ r hr' G _ hG hGdep hGb
  rw [hint μ, hint ν] at key
  have : f r - f (r + 1) = (∫ σ, restrictTo F (A r) ξ₀ σ ∂μ - ∫ σ, restrictTo F (A (r + 1)) ξ₀ σ ∂μ) -
      (∫ σ, restrictTo F (A r) ξ₀ σ ∂ν - ∫ σ, restrictTo F (A (r + 1)) ξ₀ σ ∂ν) := by
    simp only [hf]; ring
  rw [this]; exact key

end Attempts.Twist
