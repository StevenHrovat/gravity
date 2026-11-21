import Influence.TotalVariation

/-!
# Gibbs-measure corollaries (LGT-NOTE.md, sections 1, 2 and 3)

Reference text: `docs/mass-gap/dobrushin/LGT-NOTE.md`.

* `Influence.tv_le_tanh_half_of_ratio` (§1): the two-sided setwise ratio hypothesis of `lgt`'s
  `influenceCoeff_le_of_cylinder_ratio_bound`, `μ B ≤ e^C ν B` and `ν B ≤ e^C μ B`, gives
  `TV(μ, ν) ≤ tanh (C/2)` (instead of `lgt`'s `1 - e^{-C}`; compare `tanh_half_le_lgt`).
* `Influence.tv_gibbs_le_tanh` (§2): Gibbs measures `exp φᵢ / Zᵢ · ν` whose log-weights differ by a
  function of oscillation at most `D` are within `tanh (D/4)` in total variation.
* `Influence.tv_single_link_le_tanh` (§2): one plaquette term `β fᵢ` with `|fᵢ| ≤ n` changes:
  `TV ≤ tanh (n β)`.
* `Influence.dobrushin_single_link` (§3): with `6(d - 1)` neighbours, `6(d-1) · tanh (n β) < 1`
  makes the Dobrushin column sum less than one.
-/

open MeasureTheory Real
open scoped ENNReal

namespace Influence

variable {α : Type*} [MeasurableSpace α]

/-- Partition function `Z = ∫ exp φ dν`. -/
noncomputable def partitionFn (ν : Measure α) (φ : α → ℝ) : ℝ := ∫ x, exp (φ x) ∂ν

/-- The normalised Gibbs measure with log-weight `φ` relative to `ν`:
density `exp φ / Z` with respect to `ν`, `Z = partitionFn ν φ`. -/
noncomputable def gibbs (ν : Measure α) (φ : α → ℝ) : Measure α :=
  ν.withDensity (fun x => ENNReal.ofReal (exp (φ x) / partitionFn ν φ))

/-- `exp φ` is integrable for bounded measurable `φ` and a probability measure `ν`. -/
theorem integrable_exp_of_bdd (ν : Measure α) [IsProbabilityMeasure ν] {φ : α → ℝ}
    (hφ : Measurable φ) {K : ℝ} (hK : ∀ x, |φ x| ≤ K) : Integrable (fun x => exp (φ x)) ν := by
  refine Integrable.of_bound (hφ.exp).aestronglyMeasurable (exp K) (Filter.Eventually.of_forall ?_)
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  exact exp_le_exp.2 (le_of_abs_le (hK x))

/-- The partition function of a bounded measurable `φ` is positive (at least `e^{-K}`). -/
theorem partitionFn_pos (ν : Measure α) [IsProbabilityMeasure ν] {φ : α → ℝ}
    (hφ : Measurable φ) {K : ℝ} (hK : ∀ x, |φ x| ≤ K) : 0 < partitionFn ν φ := by
  have h := integral_mono (integrable_const (exp (-K))) (integrable_exp_of_bdd ν hφ hK)
    (fun x => exp_le_exp.2 (neg_le_of_abs_le (hK x)))
  simp only [integral_const, probReal_univ, one_smul] at h
  exact (exp_pos _).trans_le h

/-- The Gibbs measure of a bounded measurable `φ` is a probability measure. -/
theorem isProbabilityMeasure_gibbs (ν : Measure α) [IsProbabilityMeasure ν] {φ : α → ℝ}
    (hφ : Measurable φ) {K : ℝ} (hK : ∀ x, |φ x| ≤ K) : IsProbabilityMeasure (gibbs ν φ) := by
  have hZ := partitionFn_pos ν hφ hK
  constructor
  rw [gibbs, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ((integrable_exp_of_bdd ν hφ hK).div_const _)
      (Filter.Eventually.of_forall fun x => div_nonneg (exp_pos _).le hZ.le),
    integral_div]
  rw [show ∫ x, exp (φ x) ∂ν = partitionFn ν φ from rfl, div_self hZ.ne', ENNReal.ofReal_one]

/-- **Gibbs corollary, oscillation form** (LGT-NOTE.md §2).
Let `ν` be a probability measure and `φ₁, φ₂` bounded measurable log-weights, `μᵢ = gibbs ν φᵢ`
(density `exp φᵢ / Zᵢ`). If `φ₁ - φ₂` has oscillation at most `D`, i.e.
`c ≤ φ₁ x - φ₂ x ≤ c + D` for all `x`, then `TV(μ₁, μ₂) ≤ tanh (D/4)`.

Proof: `dμ₁/dμ₂ = exp(φ₁ - φ₂) · Z₂/Z₁` lies in `[m, e^D m]`; apply the main lemma with `R = e^D`. -/
theorem tv_gibbs_le_tanh (ν : Measure α) [IsProbabilityMeasure ν] {φ₁ φ₂ : α → ℝ}
    (h₁ : Measurable φ₁) (h₂ : Measurable φ₂) {K₁ K₂ : ℝ} (hK₁ : ∀ x, |φ₁ x| ≤ K₁)
    (hK₂ : ∀ x, |φ₂ x| ≤ K₂) {c D : ℝ}
    (hosc : ∀ x, c ≤ φ₁ x - φ₂ x ∧ φ₁ x - φ₂ x ≤ c + D) :
    tv (gibbs ν φ₁) (gibbs ν φ₂) ≤ tanh (D / 4) := by
  have := isProbabilityMeasure_gibbs ν h₁ hK₁
  have := isProbabilityMeasure_gibbs ν h₂ hK₂
  have hZ₁ := partitionFn_pos ν h₁ hK₁
  have hZ₂ := partitionFn_pos ν h₂ hK₂
  have hZ₁' := hZ₁.ne'
  have hZ₂' := hZ₂.ne'
  let g : α → ℝ := fun x => exp (φ₁ x - φ₂ x) * (partitionFn ν φ₂ / partitionFn ν φ₁)
  have hg : Measurable g := ((h₁.sub h₂).exp).mul_const _
  have hq : 0 < partitionFn ν φ₂ / partitionFn ν φ₁ := div_pos hZ₂ hZ₁
  have hμ : gibbs ν φ₁ = (gibbs ν φ₂).withDensity (fun x => ENNReal.ofReal (g x)) := by
    rw [gibbs, gibbs, ← withDensity_mul ν (h₂.exp.div_const _).ennreal_ofReal hg.ennreal_ofReal]
    congr 1
    funext x
    simp only [Pi.mul_apply, g]
    rw [← ENNReal.ofReal_mul (div_nonneg (exp_pos _).le hZ₂.le), exp_sub]
    congr 1
    field_simp
  have h := tv_le_tanh_of_density_bounds (gibbs ν φ₁) (gibbs ν φ₂) hg hμ
    (m := exp c * (partitionFn ν φ₂ / partitionFn ν φ₁))
    (M := exp (c + D) * (partitionFn ν φ₂ / partitionFn ν φ₁)) (R := exp D)
    (mul_pos (exp_pos _) hq)
    (Filter.Eventually.of_forall fun x =>
      mul_le_mul_of_nonneg_right (exp_le_exp.2 (hosc x).1) hq.le)
    (Filter.Eventually.of_forall fun x =>
      mul_le_mul_of_nonneg_right (exp_le_exp.2 (hosc x).2) hq.le)
    (by rw [exp_add]; ring_nf; exact le_rfl)
  rwa [log_exp] at h

/-- A real inequality `μ(B) ≤ a ν(B)` between finite measures, read in `ℝ≥0∞`. -/
theorem ennreal_le_of_real_le {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a : ℝ} (ha : 0 ≤ a) {B : Set α} (h : μ.real B ≤ a * ν.real B) :
    μ B ≤ ENNReal.ofReal a * ν B := by
  rw [← ofReal_measureReal (μ := μ), ← ofReal_measureReal (μ := ν), ← ENNReal.ofReal_mul ha]
  exact ENNReal.ofReal_le_ofReal h

/-- **Two-sided ratio corollary, factor 2** (LGT-NOTE.md §1, "With R = e^(2C)").
This is the hypothesis form of `lgt`'s `influenceCoeff_le_of_cylinder_ratio_bound`, applied in both
orders: if `μ, ν` are probability measures with `μ(B) ≤ e^C ν(B)` and `ν(B) ≤ e^C μ(B)` for every
measurable `B`, then `TV(μ, ν) ≤ tanh (C/2)`.

Proof: `μ ≪ ν`, and the Radon–Nikodym density lies in `[e^{-C}, e^C]` a.e. (compare set integrals);
apply the main lemma with `R = e^{2C}`. -/
theorem tv_le_tanh_half_of_ratio (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C : ℝ}
    (h₁ : ∀ B, MeasurableSet B → μ.real B ≤ exp C * ν.real B)
    (h₂ : ∀ B, MeasurableSet B → ν.real B ≤ exp C * μ.real B) :
    tv μ ν ≤ tanh (C / 2) := by
  have hE₁ : ∀ B, MeasurableSet B → μ B ≤ ENNReal.ofReal (exp C) * ν B :=
    fun B hB => ennreal_le_of_real_le (exp_pos C).le (h₁ B hB)
  have hE₂ : ∀ B, MeasurableSet B → ENNReal.ofReal (exp (-C)) * ν B ≤ μ B := by
    intro B hB
    have h : exp (-C) * ν.real B ≤ μ.real B := by
      have := mul_le_mul_of_nonneg_left (h₂ B hB) (exp_pos (-C)).le
      rwa [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul] at this
    rw [← ofReal_measureReal (μ := ν), ← ofReal_measureReal (μ := μ),
      ← ENNReal.ofReal_mul (exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal h
  have hac : μ ≪ ν := Measure.AbsolutelyContinuous.mk fun s hs h0 => by
    have := hE₁ s hs
    rw [h0, mul_zero] at this
    exact nonpos_iff_eq_zero.mp this
  have hup : μ.rnDeriv ν ≤ᵐ[ν] fun _ => ENNReal.ofReal (exp C) :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv μ ν)
      fun s hs _ => by rw [Measure.setLIntegral_rnDeriv hac, setLIntegral_const]; exact hE₁ s hs
  have hlo : (fun _ => ENNReal.ofReal (exp (-C))) ≤ᵐ[ν] μ.rnDeriv ν :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_const
      fun s hs _ => by rw [Measure.setLIntegral_rnDeriv hac, setLIntegral_const]; exact hE₂ s hs
  have h := tv_le_tanh_of_rnDeriv_bounds μ ν hac (m := exp (-C)) (M := exp C)
    (R := exp (2 * C)) (exp_pos _)
    (by
      filter_upwards [hup, hlo] with x hu hl
      exact (ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu)).1 hl)
    (by
      filter_upwards [hup] with x hu
      exact ENNReal.toReal_le_of_le_ofReal (exp_pos _).le hu)
    (by rw [← exp_add]; ring_nf; exact le_rfl)
  rw [log_exp] at h
  convert h using 2; ring

/-- The bound `tanh (C/2)` of `tv_le_tanh_half_of_ratio` is never worse than `lgt`'s
`influenceBound`-shaped `1 - e^{-C}` (for `C ≥ 0`). -/
theorem tanh_half_le_lgt {C : ℝ} (hC : 0 ≤ C) : tanh (C / 2) ≤ 1 - exp (-C) := by
  rw [tanh_eq_exp, show 2 * (C / 2) = C by ring, exp_neg]
  have h1 : 1 ≤ exp C := one_le_exp hC
  rw [div_le_iff₀ (by linarith)]
  field_simp
  nlinarith

/-- **Single-link application, factor 4** (LGT-NOTE.md §2, "influence ≤ tanh(nβ)").
Abstract form of one link's conditional law in Wilson lattice gauge theory: `ν` is the Haar
(probability) measure on the link variable, `ψ` collects the plaquette terms that do not change,
and `fᵢ` is the one plaquette term that changes (`Re tr` of the plaquette with the old/new
neighbour value, so `|fᵢ| ≤ n` for an `n`-dimensional unitary representation). With
`φᵢ = β fᵢ + ψ`, `β ≥ 0`, the conditional laws satisfy `TV(μ₁, μ₂) ≤ tanh (n β)`.

Proof: `φ₁ - φ₂ = β (f₁ - f₂)` takes values in `[-2nβ, 2nβ]`, oscillation `D = 4nβ`; apply
`tv_gibbs_le_tanh`. -/
theorem tv_single_link_le_tanh (ν : Measure α) [IsProbabilityMeasure ν] {f₁ f₂ ψ : α → ℝ}
    (hf₁ : Measurable f₁) (hf₂ : Measurable f₂) (hψ : Measurable ψ) {n β K : ℝ}
    (hβ : 0 ≤ β) (hn₁ : ∀ x, |f₁ x| ≤ n) (hn₂ : ∀ x, |f₂ x| ≤ n) (hψK : ∀ x, |ψ x| ≤ K) :
    tv (gibbs ν fun x => β * f₁ x + ψ x) (gibbs ν fun x => β * f₂ x + ψ x) ≤ tanh (n * β) := by
  have hb : ∀ f : α → ℝ, (∀ x, |f x| ≤ n) → ∀ x, |β * f x + ψ x| ≤ β * n + K := by
    intro f hf x
    calc |β * f x + ψ x| ≤ |β * f x| + |ψ x| := abs_add_le _ _
      _ = β * |f x| + |ψ x| := by rw [abs_mul, abs_of_nonneg hβ]
      _ ≤ β * n + K := add_le_add (mul_le_mul_of_nonneg_left (hf x) hβ) (hψK x)
  have h := tv_gibbs_le_tanh ν (φ₁ := fun x => β * f₁ x + ψ x) (φ₂ := fun x => β * f₂ x + ψ x)
    ((hf₁.const_mul β).add hψ) ((hf₂.const_mul β).add hψ)
    (hb f₁ hn₁) (hb f₂ hn₂) (c := -(2 * n * β)) (D := 4 * n * β) (fun x => by
      have a1 := abs_le.1 (hn₁ x)
      have a2 := abs_le.1 (hn₂ x)
      constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2])
  convert h using 2; ring

/-- A Dobrushin column sum of `k` influences, each at most `b`, is below one when `k · b < 1`. -/
theorem dobrushin_sum_lt_one {k : ℕ} {b : ℝ} (hk : (k : ℝ) * b < 1) (a : Fin k → ℝ)
    (ha : ∀ j, a j ≤ b) : ∑ j, a j < 1 := by
  calc ∑ j, a j ≤ ∑ _j : Fin k, b := Finset.sum_le_sum fun j _ => ha j
    _ = (k : ℝ) * b := by simp
    _ < 1 := hk

/-- **Dobrushin threshold with the tight neighbour count** (LGT-NOTE.md §2 + §3).
A link in `d` dimensions has `6(d - 1)` neighbouring links. If every neighbour's influence `a j` is
at most `tanh (n β)` (`tv_single_link_le_tanh`) and `6(d - 1) · tanh (n β) < 1`, then the Dobrushin
sum `∑ⱼ a j` is below one. (The trivial inequality it is; the content is the threshold.) -/
theorem dobrushin_single_link {d : ℕ} {n β : ℝ}
    (h : ((6 * (d - 1) : ℕ) : ℝ) * tanh (n * β) < 1) (a : Fin (6 * (d - 1)) → ℝ)
    (ha : ∀ j, a j ≤ tanh (n * β)) : ∑ j, a j < 1 :=
  dobrushin_sum_lt_one h a ha

end Influence
