/-
Proof phase, cycle 2, workstream B (Conjecture S): the mixture no-go (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c2b-conjS/NOTE.md`, section 4.1.
-/

import Mathlib

/-!
# Expectation bounds and reflection positivity survive mixing; clustering does not

For two probability measures `μ₁, μ₂` the equal mixture `mix μ₁ μ₂ = ½ μ₁ + ½ μ₂` satisfies

* `integral_mix`: `∫ f d(mix) = (∫ f dμ₁ + ∫ f dμ₂)/2`;
* `abs_integral_mix_le`: every bound `|∫ W dμᵢ| ≤ B` holding for both holds for the mixture (so an **area law**, a family
  of such bounds on Wilson loops, survives with the worse of the two constants);
* `integral_mix_nonneg`: every positivity `∫ F·ΘF dμᵢ ≥ 0` holding for both holds for the mixture (so **reflection
  positivity** survives; so do gauge, translation and rotation invariance, which are linear in the measure);
* `cov_mix`: `Cov_mix(f, g) = ½ Cov₁ + ½ Cov₂ + ¼ (E₁f − E₂f)(E₁g − E₂g)`;
* **`tendsto_cov_mix`, `not_expDecay_mix`**: if `f` and its translates `g n` have the same expectation in each component
  and each component clusters (`Covᵢ(f, g n) → 0`), the mixture's covariance tends to `¼(E₁f − E₂f)²`; if `E₁f ≠ E₂f`
  it admits **no** bound `C e^{−m n}` with `m > 0`.

**Use (paper, `NOTE.md` 4.1).** Take `μ₁` = SU(2) Haar measure (β = 0: every non-trivial Wilson loop has expectation 0,
infinite gap) and `μ₂` = the infinite-volume SU(2) Wilson measure at a small `β > 0` (Osterwalder–Seiler: area law and
gap; plaquette expectation `> 0`), `f` the plaquette, `g n` its time translates. The mixture is reflection positive,
gauge and Euclidean invariant, has an area law, and has no mass gap. So **no implication "area law ⇒ gap" holds for all
reflection-positive, gauge-invariant measures on SU(2) configurations**: Conjecture S needs the Gibbs property of one
local action (and then the fundamental–adjoint endpoint, `NOTE.md` 1.3, shows it needs the Wilson action).

**Claim discipline.** Lean, definitional/elementary (linearity of the integral). Model-blind. The Yang–Mills inputs of
the use (Osterwalder–Seiler) are cited, not formalised here (the project's own strong-coupling area law and clustering
are `AreaLaw.Assembly.wilson_area_law` and `AreaLaw.Concrete.wilson_clustering_explicit`, finite volume).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace ProofPhase.SectorS

variable {X : Type*} [MeasurableSpace X]

/-- The equal-weight mixture of two measures. -/
def mix (μ₁ μ₂ : Measure X) : Measure X := (2⁻¹ : ℝ≥0∞) • μ₁ + (2⁻¹ : ℝ≥0∞) • μ₂

theorem isProbabilityMeasure_mix (μ₁ μ₂ : Measure X) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] :
    IsProbabilityMeasure (mix μ₁ μ₂) := by
  constructor
  simp only [mix, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.inv_two_add_inv_two

theorem integral_mix {μ₁ μ₂ : Measure X} {f : X → ℝ} (h₁ : Integrable f μ₁) (h₂ : Integrable f μ₂) :
    ∫ x, f x ∂(mix μ₁ μ₂) = (∫ x, f x ∂μ₁ + ∫ x, f x ∂μ₂) / 2 := by
  unfold mix
  rw [integral_add_measure (h₁.smul_measure (by simp)) (h₂.smul_measure (by simp)), integral_smul_measure,
    integral_smul_measure]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- **Expectation bounds survive mixing** (an area law does). -/
theorem abs_integral_mix_le {μ₁ μ₂ : Measure X} {W : X → ℝ} (h₁ : Integrable W μ₁) (h₂ : Integrable W μ₂) {B : ℝ}
    (hb₁ : |∫ x, W x ∂μ₁| ≤ B) (hb₂ : |∫ x, W x ∂μ₂| ≤ B) : |∫ x, W x ∂(mix μ₁ μ₂)| ≤ B := by
  rw [integral_mix h₁ h₂, abs_div, abs_two]
  have := abs_add_le (∫ x, W x ∂μ₁) (∫ x, W x ∂μ₂)
  linarith

/-- **Positivity survives mixing** (reflection positivity does). -/
theorem integral_mix_nonneg {μ₁ μ₂ : Measure X} {F : X → ℝ} (h₁ : Integrable F μ₁) (h₂ : Integrable F μ₂)
    (p₁ : 0 ≤ ∫ x, F x ∂μ₁) (p₂ : 0 ≤ ∫ x, F x ∂μ₂) : 0 ≤ ∫ x, F x ∂(mix μ₁ μ₂) := by
  rw [integral_mix h₁ h₂]; linarith

/-- The covariance. -/
def cov (μ : Measure X) (f g : X → ℝ) : ℝ := ∫ x, f x * g x ∂μ - (∫ x, f x ∂μ) * ∫ x, g x ∂μ

/-- **Covariance of a mixture.** -/
theorem cov_mix {μ₁ μ₂ : Measure X} {f g : X → ℝ} (hf₁ : Integrable f μ₁) (hf₂ : Integrable f μ₂)
    (hg₁ : Integrable g μ₁) (hg₂ : Integrable g μ₂) (hfg₁ : Integrable (fun x => f x * g x) μ₁)
    (hfg₂ : Integrable (fun x => f x * g x) μ₂) :
    cov (mix μ₁ μ₂) f g = (cov μ₁ f g + cov μ₂ f g) / 2 +
      ((∫ x, f x ∂μ₁) - ∫ x, f x ∂μ₂) * ((∫ x, g x ∂μ₁) - ∫ x, g x ∂μ₂) / 4 := by
  unfold cov
  rw [integral_mix hf₁ hf₂, integral_mix hg₁ hg₂, integral_mix hfg₁ hfg₂]
  ring

/-- **A mixture of two clustering states with different expectations does not cluster.** -/
theorem tendsto_cov_mix {μ₁ μ₂ : Measure X} {f : X → ℝ} {g : ℕ → X → ℝ} (hf₁ : Integrable f μ₁)
    (hf₂ : Integrable f μ₂) (hg₁ : ∀ n, Integrable (g n) μ₁) (hg₂ : ∀ n, Integrable (g n) μ₂)
    (hfg₁ : ∀ n, Integrable (fun x => f x * g n x) μ₁) (hfg₂ : ∀ n, Integrable (fun x => f x * g n x) μ₂)
    (hs₁ : ∀ n, ∫ x, g n x ∂μ₁ = ∫ x, f x ∂μ₁) (hs₂ : ∀ n, ∫ x, g n x ∂μ₂ = ∫ x, f x ∂μ₂)
    (hc₁ : Tendsto (fun n => cov μ₁ f (g n)) atTop (𝓝 0)) (hc₂ : Tendsto (fun n => cov μ₂ f (g n)) atTop (𝓝 0)) :
    Tendsto (fun n => cov (mix μ₁ μ₂) f (g n)) atTop
      (𝓝 (((∫ x, f x ∂μ₁) - ∫ x, f x ∂μ₂) ^ 2 / 4)) := by
  have e : ∀ n, cov (mix μ₁ μ₂) f (g n) = (cov μ₁ f (g n) + cov μ₂ f (g n)) / 2 +
      ((∫ x, f x ∂μ₁) - ∫ x, f x ∂μ₂) ^ 2 / 4 := by
    intro n
    rw [cov_mix hf₁ hf₂ (hg₁ n) (hg₂ n) (hfg₁ n) (hfg₂ n), hs₁ n, hs₂ n]
    ring
  simp_rw [e]
  have := ((hc₁.add hc₂).div_const 2).add_const (((∫ x, f x ∂μ₁) - ∫ x, f x ∂μ₂) ^ 2 / 4)
  simpa using this

/-- **No exponential clustering for the mixture** when the expectations differ. -/
theorem not_expDecay_mix {μ₁ μ₂ : Measure X} {f : X → ℝ} {g : ℕ → X → ℝ} (hf₁ : Integrable f μ₁)
    (hf₂ : Integrable f μ₂) (hg₁ : ∀ n, Integrable (g n) μ₁) (hg₂ : ∀ n, Integrable (g n) μ₂)
    (hfg₁ : ∀ n, Integrable (fun x => f x * g n x) μ₁) (hfg₂ : ∀ n, Integrable (fun x => f x * g n x) μ₂)
    (hs₁ : ∀ n, ∫ x, g n x ∂μ₁ = ∫ x, f x ∂μ₁) (hs₂ : ∀ n, ∫ x, g n x ∂μ₂ = ∫ x, f x ∂μ₂)
    (hc₁ : Tendsto (fun n => cov μ₁ f (g n)) atTop (𝓝 0)) (hc₂ : Tendsto (fun n => cov μ₂ f (g n)) atTop (𝓝 0))
    (hne : ∫ x, f x ∂μ₁ ≠ ∫ x, f x ∂μ₂) :
    ¬ ∃ C m : ℝ, 0 < m ∧ ∀ n : ℕ, |cov (mix μ₁ μ₂) f (g n)| ≤ C * Real.exp (-(m * n)) := by
  rintro ⟨C, m, hm, hb⟩
  have hlim := tendsto_cov_mix hf₁ hf₂ hg₁ hg₂ hfg₁ hfg₂ hs₁ hs₂ hc₁ hc₂
  have hexp : Tendsto (fun n : ℕ => C * Real.exp (-(m * n))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => m * (n : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop hm tendsto_natCast_atTop_atTop
    have h2 := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)).const_mul C
    simpa using h2
  have h0 : Tendsto (fun n => cov (mix μ₁ μ₂) f (g n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hb n) hexp
  have := tendsto_nhds_unique hlim h0
  have hpos : 0 < ((∫ x, f x ∂μ₁) - ∫ x, f x ∂μ₂) ^ 2 / 4 := by
    have : (∫ x, f x ∂μ₁) - ∫ x, f x ∂μ₂ ≠ 0 := sub_ne_zero.2 hne
    positivity
  linarith

end ProofPhase.SectorS
