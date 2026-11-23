/-
RH-YM bridge, Part 1, module 3: the general form, Pringsheim-Landau for the Laplace transform of a non-negative
measure on [0, inf) (2026-11-23). Released under Apache 2.0.

Note: `docs/rh-guide/bridge/BRIDGE.md`.
-/

import ProofPhase.Bridge.Pringsheim
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Pringsheim-Landau for Laplace transforms of non-negative measures

`μ` is a (non-negative) measure on `ℝ` living on `[0, ∞)` (`∀ᵐ t ∂μ, 0 ≤ t`). Its Laplace transform is
`lap μ s = ∫ e^{-s t} dμ(t)`. `LapConv μ x` says the integral converges (absolutely) at the real point `x`; since the
weights are non-negative, convergence at `x` gives convergence at every `y ≥ x` (`LapConv.mono`) and on the whole
half-plane `Re s ≥ x`.

**Main results.**
* `hasDerivAt_lapN`, `iteratedDeriv_lap`: on `Re s > σ` (when the integral converges for every real `x > σ`) the
  transform is holomorphic and its `n`-th derivative is `∫ (-t)^n e^{-s t} dμ` (differentiation under the integral).
* `laplace_conv_left`: **extension form.** If the integral converges for all real `x > x₀` and `lap μ` agrees, right of
  `x₀`, with a function holomorphic on a disc about `x₀`, then it converges at a real point left of `x₀`.
* `laplace_landau`: **singularity at the abscissa.** If `x₀` is the abscissa (convergence for `x > x₀`, divergence for
  `x < x₀`), then `lap μ` has no holomorphic extension to any disc about `x₀`.
* `laplace_ray`: **the one-sided usable form.** If the integral converges somewhere and `lap μ` continues
  holomorphically around every real point `x > θ` (right of which it converges), then it converges for every real
  `x > θ`, hence is holomorphic on `Re s > θ`.

**From Mathlib:** `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (differentiation under the integral sign),
`Real.pow_div_factorial_le_exp`, `NormedSpace.expSeries_div_hasSum_exp`, `lintegral_tsum`,
`ofReal_integral_eq_lintegral_ofReal`, `hasFiniteIntegral_iff_ofReal`. Mathlib has no Laplace transform of measures
and no Pringsheim or Landau theorem; this file adds them. The analytic step is the shared
`ProofPhase.Bridge.pringsheim_extension`.
-/

open Complex Nat MeasureTheory Filter Topology Set

noncomputable section

namespace ProofPhase.Bridge

variable {μ : Measure ℝ}

/-- Convergence (absolute) of the Laplace integral at the real point `x`. -/
def LapConv (μ : Measure ℝ) (x : ℝ) : Prop := Integrable (fun t => Real.exp (-(x * t))) μ

/-- The `n`-th derivative candidate `∫ (-t)^n e^{-s t} dμ`. -/
def lapN (μ : Measure ℝ) (n : ℕ) (s : ℂ) : ℂ := ∫ t, (-(t : ℂ)) ^ n * Complex.exp (-(s * t)) ∂μ

/-- The Laplace transform `∫ e^{-s t} dμ(t)`. -/
def lap (μ : Measure ℝ) (s : ℂ) : ℂ := ∫ t, Complex.exp (-(s * t)) ∂μ

theorem lap_eq_lapN_zero : lap μ = lapN μ 0 := by
  funext s; simp [lap, lapN]

theorem LapConv.mono (hμ : ∀ᵐ t ∂μ, 0 ≤ t) {x y : ℝ} (hx : LapConv μ x) (hxy : x ≤ y) : LapConv μ y := by
  refine hx.mono' (by fun_prop) (hμ.mono fun t ht => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- `t^k ≤ k! δ^{-k} e^{δ t}` for `t ≥ 0`, `δ > 0`. -/
theorem pow_le_factorial_mul_exp {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) (k : ℕ) :
    t ^ k ≤ k ! / δ ^ k * Real.exp (δ * t) := by
  have h := Real.pow_div_factorial_le_exp (x := δ * t) (mul_nonneg hδ.le ht) k
  have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have hδk : 0 < δ ^ k := pow_pos hδ k
  rw [mul_pow, div_le_iff₀ hk] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hδk]
  nlinarith [h]

/-- The pointwise bound on the integrand of `lapN`. -/
theorem norm_lapTerm_le {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) (k : ℕ) (z : ℂ) :
    ‖(-(t : ℂ)) ^ k * Complex.exp (-(z * t))‖ ≤ k ! / δ ^ k * Real.exp (-((z.re - δ) * t)) := by
  rw [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_of_nonneg ht, Complex.norm_exp]
  have hre : (-(z * (t : ℂ))).re = -(z.re * t) := by simp
  rw [hre]
  calc t ^ k * Real.exp (-(z.re * t)) ≤ (k ! / δ ^ k * Real.exp (δ * t)) * Real.exp (-(z.re * t)) :=
        mul_le_mul_of_nonneg_right (pow_le_factorial_mul_exp ht hδ k) (Real.exp_pos _).le
    _ = k ! / δ ^ k * Real.exp (-((z.re - δ) * t)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem integrable_lapTerm (hμ : ∀ᵐ t ∂μ, 0 ≤ t) {σ : ℝ} (hconv : ∀ x > σ, LapConv μ x) (k : ℕ) {z : ℂ}
    (hz : σ < z.re) : Integrable (fun t : ℝ => (-(t : ℂ)) ^ k * Complex.exp (-(z * t))) μ := by
  set δ := (z.re - σ) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  refine ((hconv (z.re - δ) (by rw [hδ]; linarith)).const_mul (k ! / δ ^ k)).mono' (by fun_prop) ?_
  exact hμ.mono fun t ht => norm_lapTerm_le ht hδpos k z

/-- **Differentiation under the integral.** On `Re s > σ`, `d/ds lapN μ n = lapN μ (n+1)`. -/
theorem hasDerivAt_lapN (hμ : ∀ᵐ t ∂μ, 0 ≤ t) {σ : ℝ} (hconv : ∀ x > σ, LapConv μ x) (n : ℕ) {s : ℂ}
    (hs : σ < s.re) : HasDerivAt (lapN μ n) (lapN μ (n + 1) s) s := by
  set δ := (s.re - σ) / 3 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := s)
    (F := fun z t => (-(t : ℂ)) ^ n * Complex.exp (-(z * t)))
    (F' := fun z t => (-(t : ℂ)) ^ (n + 1) * Complex.exp (-(z * t)))
    (bound := fun t => (n + 1) ! / δ ^ (n + 1) * Real.exp (-((σ + δ) * t)))
    (Metric.ball_mem_nhds s hδpos)
    (Eventually.of_forall fun z => (by fun_prop : Continuous fun t : ℝ =>
      (-(t : ℂ)) ^ n * Complex.exp (-(z * t))).aestronglyMeasurable)
    (integrable_lapTerm hμ hconv n hs)
    ((by fun_prop : Continuous fun t : ℝ =>
      (-(t : ℂ)) ^ (n + 1) * Complex.exp (-(s * t))).aestronglyMeasurable)
    (hμ.mono fun t ht z hz => by
      have hzre : s.re - δ < z.re := by
        have h1 := Complex.abs_re_le_norm (z - s)
        rw [Metric.mem_ball, Complex.dist_eq] at hz
        rw [Complex.sub_re] at h1
        linarith [abs_lt.mp (lt_of_le_of_lt h1 hz)]
      refine (norm_lapTerm_le ht hδpos (n + 1) z).trans ?_
      gcongr
      · nlinarith)
    ((hconv (σ + δ) (by linarith)).const_mul _)
    (Eventually.of_forall fun t z _ => by
      have h1 : HasDerivAt (fun w : ℂ => -(w * (t : ℂ))) (-(t : ℂ)) z :=
        (hasDerivAt_mul_const (t : ℂ)).neg
      have h2 := (h1.cexp).const_mul ((-(t : ℂ)) ^ n)
      convert h2 using 1
      ring)
  exact key.2

/-- **The derivatives of the Laplace transform**: `iteratedDeriv k (lap μ) s = lapN μ k s` on `Re s > σ`. -/
theorem iteratedDeriv_lap (hμ : ∀ᵐ t ∂μ, 0 ≤ t) {σ : ℝ} (hconv : ∀ x > σ, LapConv μ x) (k : ℕ) :
    ∀ s : ℂ, σ < s.re → iteratedDeriv k (lap μ) s = lapN μ k s := by
  have hU : IsOpen {s : ℂ | σ < s.re} := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  induction k with
  | zero => intro s _; simp [lap_eq_lapN_zero]
  | succ k ih =>
      intro s hs
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv k (lap μ) =ᶠ[𝓝 s] lapN μ k := by
        filter_upwards [hU.mem_nhds hs] with z hz using ih z hz
      rw [hev.deriv_eq]
      exact (hasDerivAt_lapN hμ hconv k hs).deriv

/-- The real moments `∫ t^n e^{-c t} dμ`. -/
def lapMoment (μ : Measure ℝ) (c : ℝ) (n : ℕ) : ℝ := ∫ t, t ^ n * Real.exp (-(c * t)) ∂μ

theorem lapN_ofReal (μ : Measure ℝ) (c : ℝ) (n : ℕ) :
    lapN μ n (c : ℂ) = (-1) ^ n * (lapMoment μ c n : ℂ) := by
  have e : (fun t : ℝ => (-(t : ℂ)) ^ n * Complex.exp (-((c : ℂ) * t)))
      = fun t : ℝ => (-1) ^ n * ((t ^ n * Real.exp (-(c * t)) : ℝ) : ℂ) := by
    funext t
    push_cast
    rw [neg_pow]
    ring
  rw [lapN, e, integral_const_mul, integral_complex_ofReal, lapMoment]

theorem integrable_moment (hμ : ∀ᵐ t ∂μ, 0 ≤ t) {σ : ℝ} (hconv : ∀ x > σ, LapConv μ x) {c : ℝ} (hc : σ < c)
    (n : ℕ) : Integrable (fun t => t ^ n * Real.exp (-(c * t))) μ := by
  have h := (integrable_lapTerm hμ hconv n (z := (c : ℂ)) (by simpa using hc)).norm
  refine h.congr (hμ.mono fun t ht => ?_)
  simp only [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_of_nonneg ht, Complex.norm_exp]
  congr 2
  simp

/-- **Tonelli step for measures.** If `∑ M n h^n / n!` converges, `M n = ∫ t^n e^{-c t} dμ`, then the Laplace integral
converges at `c - h`. -/
theorem lapConv_of_taylor (hμ : ∀ᵐ t ∂μ, 0 ≤ t) {σ : ℝ} (hconv : ∀ x > σ, LapConv μ x) {c h : ℝ} (hc : σ < c)
    (h0 : 0 ≤ h) (hsum : Summable (fun n => lapMoment μ c n * h ^ n / n !)) : LapConv μ (c - h) := by
  have hmom := integrable_moment hμ hconv hc
  have hMnn : ∀ n, 0 ≤ lapMoment μ c n := fun n =>
    integral_nonneg_of_ae (hμ.mono fun t ht => mul_nonneg (pow_nonneg ht n) (Real.exp_pos _).le)
  -- pointwise expansion of the integrand
  have hpt : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal (Real.exp (-((c - h) * t)))
      = ∑' n : ℕ, ENNReal.ofReal (t ^ n * Real.exp (-(c * t))) * ENNReal.ofReal (h ^ n / n !) := by
    intro t ht
    have hexp : HasSum (fun n : ℕ => (h * t) ^ n / n !) (Real.exp (h * t)) := by
      rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp (h * t)
    have hs : HasSum (fun n : ℕ => t ^ n * Real.exp (-(c * t)) * (h ^ n / n !)) (Real.exp (-((c - h) * t))) := by
      have := hexp.mul_left (Real.exp (-(c * t)))
      convert this using 1
      · funext n; rw [mul_pow]; ring
      · rw [← Real.exp_add]; congr 1; ring
    rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable]
    congr 1; funext n
    rw [ENNReal.ofReal_mul (by positivity)]
  have hlin : ∫⁻ t, ENNReal.ofReal (Real.exp (-((c - h) * t))) ∂μ
      = ∑' n : ℕ, ENNReal.ofReal (lapMoment μ c n * h ^ n / n !) := by
    rw [lintegral_congr_ae (hμ.mono fun t ht => hpt t ht)]
    rw [lintegral_tsum (fun n => by fun_prop)]
    congr 1; funext n
    rw [lintegral_mul_const _ (by fun_prop), ← ofReal_integral_eq_lintegral_ofReal (hmom n)
      (hμ.mono fun t ht => mul_nonneg (pow_nonneg ht n) (Real.exp_pos _).le)]
    show ENNReal.ofReal (lapMoment μ c n) * _ = _
    rw [← ENNReal.ofReal_mul (hMnn n), mul_div_assoc]
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun t => (Real.exp_pos _).le), hlin,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => by have := hMnn n; positivity) hsum]
  exact ENNReal.ofReal_lt_top

/-- **Extension form.** Convergence for all real `x > x₀`, and `lap μ` agrees right of `x₀` with a function
holomorphic on a disc about `x₀`: then the integral converges at a real point left of `x₀`. -/
theorem laplace_conv_left (hμ : ∀ᵐ t ∂μ, 0 ≤ t) {x₀ r : ℝ} (hr : 0 < r) (hconv : ∀ x > x₀, LapConv μ x)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.ball (x₀ : ℂ) r))
    (hgeq : ∀ s ∈ Metric.ball (x₀ : ℂ) r, x₀ < s.re → g s = lap μ s) :
    ∃ y : ℝ, y < x₀ ∧ LapConv μ y := by
  have hF : ∀ s : ℂ, x₀ < s.re → DifferentiableAt ℂ (lap μ) s := fun s hs => by
    rw [lap_eq_lapN_zero]; exact (hasDerivAt_lapN hμ hconv 0 hs).differentiableAt
  have hder : ∀ c : ℝ, x₀ < c → ∀ n, iteratedDeriv n (lap μ) c = (-1) ^ n * (lapMoment μ c n : ℂ) :=
    fun c hc n => by rw [iteratedDeriv_lap hμ hconv n c (by simpa using hc), lapN_ofReal]
  obtain ⟨c, h, hxc, h0, hlt, hsum⟩ := pringsheim_extension hr hF hder hg hgeq
  exact ⟨c - h, hlt, lapConv_of_taylor hμ hconv hxc h0 hsum⟩

/-- **Pringsheim-Landau for measures: the abscissa is a singularity.** If the Laplace integral of a non-negative
measure on `[0, ∞)` converges for `x > x₀` and diverges for `x < x₀`, then `lap μ` has no holomorphic extension to
any disc about the real point `x₀`. -/
theorem laplace_landau (hμ : ∀ᵐ t ∂μ, 0 ≤ t) {x₀ : ℝ} (hconv : ∀ x > x₀, LapConv μ x)
    (hdiv : ∀ x < x₀, ¬ LapConv μ x) :
    ¬ ∃ (r : ℝ) (g : ℂ → ℂ), 0 < r ∧ DifferentiableOn ℂ g (Metric.ball (x₀ : ℂ) r) ∧
      ∀ s ∈ Metric.ball (x₀ : ℂ) r, x₀ < s.re → g s = lap μ s := by
  rintro ⟨r, g, hr, hg, hgeq⟩
  obtain ⟨y, hy, hconvy⟩ := laplace_conv_left hμ hr hconv hg hgeq
  exact hdiv y hy hconvy

/-- **One-sided usable form.** The Laplace integral of a non-negative measure on `[0, ∞)` converges somewhere, and
around every real `x > θ` right of which it converges, `lap μ` continues holomorphically to a disc. Then it converges
at every real `x > θ` (so `lap μ` is holomorphic on `Re s > θ`, `hasDerivAt_lapN`). -/
theorem laplace_ray (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hne : ∃ x, LapConv μ x) {θ : ℝ}
    (hext : ∀ x : ℝ, θ < x → (∀ y > x, LapConv μ y) → ∃ (r : ℝ) (g : ℂ → ℂ), 0 < r ∧
      DifferentiableOn ℂ g (Metric.ball (x : ℂ) r) ∧
      ∀ s ∈ Metric.ball (x : ℂ) r, x < s.re → g s = lap μ s) :
    ∀ x > θ, LapConv μ x := by
  set S : Set ℝ := {x | LapConv μ x} with hS
  have hup : ∀ x ∈ S, ∀ y, x ≤ y → y ∈ S := fun x hx y hxy => LapConv.mono hμ hx hxy
  by_cases hbdd : BddBelow S
  · have hSne : S.Nonempty := hne
    set x₀ := sInf S with hx₀
    have hright : ∀ y > x₀, LapConv μ y := fun y hy => by
      obtain ⟨z, hzS, hzy⟩ := exists_lt_of_csInf_lt hSne hy
      exact hup z hzS y hzy.le
    by_cases hθ : x₀ ≤ θ
    · intro x hx; exact hright x (lt_of_le_of_lt hθ hx)
    · push Not at hθ
      obtain ⟨r, g, hr, hg, hgeq⟩ := hext x₀ hθ hright
      obtain ⟨y, hy, hyS⟩ := laplace_conv_left hμ hr hright hg hgeq
      exact absurd (csInf_le hbdd hyS) (not_le.mpr hy)
  · intro x _
    rw [not_bddBelow_iff] at hbdd
    obtain ⟨z, hzS, hzx⟩ := hbdd x
    exact hup z hzS x hzx.le

end ProofPhase.Bridge
