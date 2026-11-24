/-
Proof phase, M1 tools (m1-tools): the measure-theoretic core of Lemma E7.J (fibre mass) and of the block-axial
Poincare bound (2026-11-22). Released under Apache 2.0.

Notes: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/E7J.md`, `POINCARE.md`.
-/

import Mathlib

/-!
# Fibre mass by slicing, and a Poincare bound by counting

* **`map_prod_le_of_slices`** (E7.J, the slicing step): if for every value `y` of the non-owned variables the map
  `x ↦ M (x, y)` of the owned variables pushes `μ` forward to at most `K • λ`, then the whole pushforward of
  `μ ⊗ ν` (`ν` a probability measure) is at most `K • λ`. So a fibre-mass bound for the blocked Haar measure follows
  from a bound for each slice, which is where the Jacobian estimate of `E7J.md` enters.
* **`sum_sq_le_of_paths`** (Poincare, the counting step): if each bond value is bounded by the sum of `|∂B|` over a set
  `S b` of at most `s` plaquettes, and each plaquette lies in at most `t` of these sets, then
  `∑_b |B b|² ≤ s t ∑_p |∂B p|²` (Cauchy-Schwarz and double counting). The sets `S b` (discrete Stokes surfaces in the
  block-axial gauge with zero block averages) and the values `s = O(L²)`, `t = O(L^d)` are the paper part of
  `POINCARE.md`.
-/

open MeasureTheory Finset
open scoped ENNReal

noncomputable section

namespace ProofPhase.M1

/-- **Slicing.** A pushforward bound for every slice gives the same bound for the product. -/
theorem map_prod_le_of_slices {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) [SFinite μ] (ν : Measure β) [IsProbabilityMeasure ν] (lam : Measure γ) {M : α × β → γ}
    (hM : Measurable M) {K : ℝ≥0∞} (hslice : ∀ y, μ.map (fun x => M (x, y)) ≤ K • lam) :
    (μ.prod ν).map M ≤ K • lam := by
  refine Measure.le_iff.2 (fun s hs => ?_)
  rw [Measure.map_apply hM hs, Measure.prod_apply_symm (hM hs)]
  calc ∫⁻ y, μ ((fun x => (x, y)) ⁻¹' (M ⁻¹' s)) ∂ν
      ≤ ∫⁻ _, (K • lam) s ∂ν := by
        refine lintegral_mono (fun y => ?_)
        have hy : Measurable (fun x => M (x, y)) := hM.comp (measurable_id.prodMk measurable_const)
        have h := (hslice y) s
        rw [Measure.map_apply hy hs] at h
        exact h
    _ = (K • lam) s := by simp

/-- **Poincare by counting.** Bond values controlled by sums over plaquette sets of bounded size, each plaquette in a
bounded number of sets. -/
theorem sum_sq_le_of_paths {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (B : ι → ℝ) (dB : κ → ℝ)
    (S : ι → Finset κ) {s t : ℕ} (hS : ∀ b, (S b).card ≤ s) (hT : ∀ p, (univ.filter (fun b => p ∈ S b)).card ≤ t)
    (hpath : ∀ b, |B b| ≤ ∑ p ∈ S b, |dB p|) :
    ∑ b, B b ^ 2 ≤ (s * t : ℝ) * ∑ p, dB p ^ 2 := by
  have hb : ∀ b, B b ^ 2 ≤ s * ∑ p ∈ S b, dB p ^ 2 := by
    intro b
    have h1 : B b ^ 2 ≤ (∑ p ∈ S b, |dB p|) ^ 2 := by
      have := hpath b
      nlinarith [abs_nonneg (B b), sq_abs (B b), sum_nonneg (fun p (_ : p ∈ S b) => abs_nonneg (dB p))]
    have h2 : (∑ p ∈ S b, |dB p|) ^ 2 ≤ (S b).card * ∑ p ∈ S b, |dB p| ^ 2 := sq_sum_le_card_mul_sum_sq
    have h3 : (S b).card * ∑ p ∈ S b, |dB p| ^ 2 ≤ s * ∑ p ∈ S b, dB p ^ 2 := by
      simp only [sq_abs]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hS b) (sum_nonneg (fun p _ => sq_nonneg _))
    linarith
  calc ∑ b, B b ^ 2 ≤ ∑ b, (s : ℝ) * ∑ p ∈ S b, dB p ^ 2 := sum_le_sum (fun b _ => hb b)
    _ = s * ∑ p, ((univ.filter (fun b => p ∈ S b)).card : ℝ) * dB p ^ 2 := by
        rw [← mul_sum]; congr 1
        rw [sum_comm' (t' := univ) (s' := fun p => univ.filter (fun b => p ∈ S b))]
        · simp [sum_const, nsmul_eq_mul]
        · intro b p; simp
    _ ≤ s * ∑ p, (t : ℝ) * dB p ^ 2 := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum (fun p _ => ?_)) (Nat.cast_nonneg _)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hT p) (sq_nonneg _)
    _ = (s * t : ℝ) * ∑ p, dB p ^ 2 := by rw [← mul_sum, mul_assoc]

end ProofPhase.M1
