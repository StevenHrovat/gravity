/-
Attempt r3-dmp (round 3, attempt 5), 2026-11-21. Released under Apache 2.0.

# DMP's balance rule on the Yang–Mills side: what it can and cannot be

Note: `docs/mass-gap/weak-coupling/attempts/r3-dmp/NOTE.md`, sections 3 and 5.

1. **Bare admissibility is Wilson's weight times a mask in [0, 1] that is 1 on the small-field set** (`admissible_eq_wilson_of_small`,
   `admissible_le_wilson`, `masked_le`). If the bare small-field threshold of a renormalisation-group construction is below `ε`, the
   admissible bare density differs from Wilson's only on large fields, and there only by a factor in [0, 1]; any estimate that uses
   only *upper* bounds on large-field activities (the OpenAI construction's `K`: sup bounds only, `H1-OPENAI.md` §2) keeps holding.
2. **"A sub-layer only tightens" is the data-processing inequality for blocking** (`blocking_tightens`): a stochastic blocking kernel
   never increases the total-variation distance between two laws (two boundary conditions, two cutoffs). It is sharp
   (`identity_kernel_saturates`): a factor at most 1, never a factor below 1 by itself. Contraction (a gap) needs more: the photon's
   blocking is a near-isometry on its long-wavelength part.
3. **Balance at every layer with the same bound excludes confinement** (`balance_excludes_area_law`): if every loop at every scale
   has shortfall at most `ε < 1` (normalised trace at least `1 − ε`), no area law can hold. Strong-coupling Yang–Mills has an area law
   (proved: `AreaLaw.Twist*`), so DMP's balance rule cannot hold for Yang–Mills at every layer with one bound; it can bind only at the
   cutoff layer (Luescher admissibility) or relative to each layer's own coupling (Balaban's small-field condition, which then fails
   on a positive fraction of blocks: the large-field problem).
-/

import Positivity.Admissible

open MeasureTheory Finset

namespace Attempts.R3.DmpHost

/-! ## 1. Bare admissibility as a mask -/

/-- On the small-field set (shortfall at most `ε`) the admissible weight is the Wilson weight. -/
theorem admissible_eq_wilson_of_small (n : ℕ) (β ε x : ℝ) (h : (n : ℝ) - x ≤ ε) :
    Positivity.admissibleWeight n β ε x = Real.exp (β * x) := by
  simp [Positivity.admissibleWeight, h]

/-- Everywhere the admissible weight lies between zero and the Wilson weight: Wilson times a mask in [0, 1]. -/
theorem admissible_le_wilson (n : ℕ) (β ε x : ℝ) :
    0 ≤ Positivity.admissibleWeight n β ε x ∧ Positivity.admissibleWeight n β ε x ≤ Real.exp (β * x) := by
  unfold Positivity.admissibleWeight
  split_ifs <;> simp [(Real.exp_pos _).le]

/-- A mask in [0, 1] never increases the size of an activity: upper bounds on large-field activities survive masking. -/
theorem masked_le {χ K : ℝ} (h0 : 0 ≤ χ) (h1 : χ ≤ 1) : |χ * K| ≤ |K| := by
  rw [abs_mul, abs_of_nonneg h0]
  exact mul_le_of_le_one_left (abs_nonneg K) h1

/-! ## 2. "A sub-layer only tightens": data processing for blocking -/

/-- **Data processing.** A stochastic kernel `P` (non-negative, rows summing to one: a blocking step) never increases the ℓ¹ size of a
    signed difference `a` of two fine laws: `Σ_j |Σ_i a_i P_ij| ≤ Σ_i |a_i|`. -/
theorem blocking_tightens {ι κ : Type*} [Fintype ι] [Fintype κ] (P : ι → κ → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = 1) (a : ι → ℝ) : ∑ j, |∑ i, a i * P i j| ≤ ∑ i, |a i| := by
  calc ∑ j, |∑ i, a i * P i j| ≤ ∑ j, ∑ i, |a i| * P i j := by
        refine Finset.sum_le_sum fun j _ => (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (hP i j)]
    _ = ∑ i, |a i| * ∑ j, P i j := by
        rw [Finset.sum_comm]; simp [Finset.mul_sum]
    _ = ∑ i, |a i| := by simp [hrow]

/-- **Tightening is not contraction.** The identity kernel is a blocking step that keeps every difference exactly: the
    data-processing factor is at most one, and can be one. -/
theorem identity_kernel_saturates {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) :
    ∑ j, |∑ i, a i * (if i = j then (1 : ℝ) else 0)| = ∑ i, |a i| := by
  simp

/-! ## 3. Balance at every layer excludes an area law -/

/-- **Balance at every scale excludes confinement.** Let `W i` be the normalised trace of loop `i` (loops of every size, at every
    layer), with `1 − ε ≤ W i` almost surely for one `ε < 1` (shortfall at most `ε` on every loop). If the loops' areas `A i` are
    unbounded, no area law `∫ W i ≤ C·exp(−σ·A i)` with `σ > 0` holds. -/
theorem balance_excludes_area_law {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : ι → Ω → ℝ) (hW : ∀ i, Integrable (W i) μ) {ε : ℝ} (hε : ε < 1) (hbal : ∀ i, ∀ᵐ ω ∂μ, 1 - ε ≤ W i ω)
    (A : ι → ℝ) (hA : ∀ M, ∃ i, M ≤ A i) {C σ : ℝ} (hσ : 0 < σ) :
    ¬ ∀ i, ∫ ω, W i ω ∂μ ≤ C * Real.exp (-σ * A i) := by
  intro harea
  have hlow : ∀ i, 1 - ε ≤ ∫ ω, W i ω ∂μ := by
    intro i
    have h := integral_mono_ae (integrable_const (1 - ε)) (hW i) (hbal i)
    simpa using h
  have hpos : 0 < 1 - ε := by linarith
  obtain ⟨i, hi⟩ := hA (C / (σ * (1 - ε)))
  have hkey : 1 - ε ≤ C * Real.exp (-σ * A i) := le_trans (hlow i) (harea i)
  have hsa : 0 < σ * (1 - ε) := mul_pos hσ hpos
  have hCA : C ≤ (1 - ε) * (σ * A i) := by
    have := (div_le_iff₀ hsa).mp hi
    linarith
  rcases le_or_gt C 0 with hC | hC
  · have : C * Real.exp (-σ * A i) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC (Real.exp_pos _).le
    linarith
  · have hA0 : 0 < σ * A i := by
      have : 0 < (1 - ε) * (σ * A i) := lt_of_lt_of_le hC hCA
      exact pos_of_mul_pos_right this hpos.le
    have hexp : Real.exp (-σ * A i) * (σ * A i + 1) ≤ 1 := by
      have h1 : σ * A i + 1 ≤ Real.exp (σ * A i) := by linarith [Real.add_one_le_exp (σ * A i)]
      have h2 : Real.exp (-σ * A i) * Real.exp (σ * A i) = 1 := by
        rw [← Real.exp_add]; simp
      calc Real.exp (-σ * A i) * (σ * A i + 1) ≤ Real.exp (-σ * A i) * Real.exp (σ * A i) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = 1 := h2
    -- (1 − ε)(σA + 1) ≤ C·exp(−σA)(σA + 1) ≤ C, against C ≤ (1 − ε)σA
    have h3 : (1 - ε) * (σ * A i + 1) ≤ C * Real.exp (-σ * A i) * (σ * A i + 1) :=
      mul_le_mul_of_nonneg_right hkey (by linarith)
    have h4 : C * Real.exp (-σ * A i) * (σ * A i + 1) ≤ C := by
      have := mul_le_mul_of_nonneg_left hexp hC.le
      linarith [this]
    nlinarith

end Attempts.R3.DmpHost
