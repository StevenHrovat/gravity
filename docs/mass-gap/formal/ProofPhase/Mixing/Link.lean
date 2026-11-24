/-
P vs NP dictionary, Lean part 3: influence below 1 gives a spectral gap in time (2026-11-23).
Released under Apache 2.0.

Paper: `docs/pnp/DICTIONARY.md`, section 3.
-/

import ProofPhase.Mixing.Glauber
import ProofPhase.Mixing.TimeGap

/-!
# Influence below 1 gives a spectral gap of the sampler

The random-scan operator `(R F)(σ) = ∫ F d(rsStep δ_σ)` is, for the heat-bath update, the average of the conditional
expectations at single sites, so a positive self-adjoint operator on `L²(μ)` with spectrum in `[0, 1]`. Its time
correlation for `F` is `C_F(k) = ∫ F (R^k F - μ F) dμ`, and the spectral theorem writes `C_F(k) = ∫ λ^k dρ_F(λ)`
with `ρ_F` the spectral measure of `F - μ F`.

* `spectral_gap_of_column`: if the column sums of the influence matrix are at most `α ∈ (0, 1)`, then `ρ_F` has no
  mass above `1 - (1 - α)/n`: the spectral gap of the random-scan sampler is at least `(1 - α)/n`, uniformly in the
  test function `F` (classically: for every `F`, hence for the operator). Per sweep of `n` updates that is a gap of
  order `1 - α`, independent of the volume.

**Hypotheses, stated:** the spectral representation `hrep` (the spectral theorem for `R`, which Mathlib lacks) and the
support of `ρ_F` in `[0, 1]` (positivity of `R`). Everything else is proved: the decay `|C_F(k)| ≤ 2 M² n θ^k` comes
from `SiteDynamics.integral_rs_le` started at a point mass, and the gap from `gap_of_geometric`. No measurability of
`σ ↦ (R^k F)(σ)` is needed, since the bound is uniform in `σ`.
-/

open MeasureTheory Set ProofPhase.OneBox

noncomputable section

namespace ProofPhase.Mixing

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] [MeasurableEq S]

namespace SiteDynamics

variable {μ : Measure (ι → S)} (D : SiteDynamics μ)

/-- `(R^k F)(σ)`: the expected value of `F` after `k` random-scan steps from the configuration `σ`. -/
def rsPow (F : (ι → S) → ℝ) (k : ℕ) (σ : ι → S) : ℝ := ∫ τ, F τ ∂(D.rsStep^[k] (Measure.dirac σ))

/-- The time correlation `C_F(k) = ∫ F (R^k F - μ F) dμ`. -/
def timeCorr (F : (ι → S) → ℝ) (k : ℕ) : ℝ := ∫ σ, F σ * (D.rsPow F k σ - ∫ τ, F τ ∂μ) ∂μ

/-- **The time correlation decays geometrically** under the column condition. -/
theorem timeCorr_le [Nonempty ι] [IsProbabilityMeasure μ] {α : ℝ} (hα0 : 0 ≤ α) (hcol : ∀ z, ∑ x, D.A x z ≤ α)
    {F : (ι → S) → ℝ} (hF : Measurable F) {M : ℝ} (hFM : ∀ σ, |F σ| ≤ M) (k : ℕ) :
    D.timeCorr F k ≤ (2 * M ^ 2 * Fintype.card ι) * (1 - (1 - α) / Fintype.card ι) ^ k := by
  set b := 2 * M * (Fintype.card ι * (1 - (1 - α) / Fintype.card ι) ^ k)
  obtain ⟨σ₀, -⟩ := nonempty_of_measure_ne_zero (μ := μ) (s := Set.univ) (by simp)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hFM σ₀)
  have hpt : ∀ σ, ‖F σ * (D.rsPow F k σ - ∫ τ, F τ ∂μ)‖ ≤ M * b := fun σ => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hFM σ) (D.integral_rs_le hα0 hcol (Measure.dirac σ) k hF hFM) (abs_nonneg _) hM
  have h := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hpt)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  calc D.timeCorr F k ≤ |D.timeCorr F k| := le_abs_self _
    _ ≤ M * b := h
    _ = _ := by simp only [b]; ring

/-- **Influence below 1 gives a spectral gap in time.** Column sums of the influence matrix at most `α ∈ (0, 1)`,
`F` bounded and measurable, `ρ` a spectral measure of `F` for the random-scan operator (`hrep`, carried by `[0, 1]`):
then `ρ` has no mass above `1 - (1 - α)/n`, i.e. the gap is at least `(1 - α)/n` per single-site step. -/
theorem spectral_gap_of_column [Nonempty ι] [IsProbabilityMeasure μ] {α : ℝ} (hα0 : 0 < α)
    (hcol : ∀ z, ∑ x, D.A x z ≤ α) {F : (ι → S) → ℝ} (hF : Measurable F) {M : ℝ} (hFM : ∀ σ, |F σ| ≤ M)
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] (h0 : ∀ᵐ l ∂ρ, 0 ≤ l) (h1 : ∀ᵐ l ∂ρ, l ≤ 1)
    (hrep : ∀ k : ℕ, acorr ρ k = D.timeCorr F k) :
    ρ (Ioi (1 - (1 - α) / Fintype.card ι)) = 0 := by
  have hN : (1 : ℝ) ≤ Fintype.card ι := Nat.one_le_cast.mpr Fintype.card_pos
  have hθ : 0 < 1 - (1 - α) / Fintype.card ι := by
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  exact gap_of_geometric h0 h1 hθ fun k => (hrep k).le.trans (D.timeCorr_le hα0.le hcol hF hFM k)

end SiteDynamics

end ProofPhase.Mixing
