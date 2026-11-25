/-
RH-YM bridge, step 1, module 5: the sign argument. A Laplace transform (or Dirichlet series) with non-negative
weights cannot have a pole of negative residue at a real point right of which it converges (2026-11-23). Released
under Apache 2.0.

Note: `docs/rh-guide/bridge/BRIDGE.md`, section 1.4 and the addendum.
-/

import ProofPhase.Bridge.Landau
import ProofPhase.Bridge.Spectral

/-!
# Poles of negative residue are impossible for positive transforms

**Abstract lemma (`residue_nonneg_of_re_nonneg`).** If `Re F(σ) ≥ 0` for real `σ` just right of `x₀`, and there
`F(s) = g(s) + R/(s - x₀)` with `g` continuous at `x₀`, then `R ≥ 0`: as `σ ↓ x₀`, a negative `R` would drive the real
part to `-∞`.

**Instances.**
* `laplace_residue_nonneg`: the Laplace transform of any measure on `ℝ` has non-negative real part at real points
  (it is an integral of `e^{-σ t} > 0`), so a pole of the form `R/(s - x₀)` approached from the right has `R ≥ 0`.
* `lseries_residue_nonneg`: the same for `LSeries a` with `0 ≤ a`.

**Ray forms (`laplace_ray_poles`, `landau_ray_poles`).** If the transform converges somewhere and, around every real
point `x > θ` right of which it converges, it is `g(s) + R/(s - x)` with `g` holomorphic on a disc and `R ≤ 0` (a pole
of non-positive residue, or `R = 0`: no pole), then it converges on all of `(θ, ∞)`, hence is holomorphic on
`Re s > θ`: the poles of negative residue were never there. This is the formal content of BRIDGE.md 1.4: in the RH
setting a real zero `β ∈ (θ, 1)` would be such a pole of the Mellin transform of the non-negative `C x^θ - G(x)`
(residue `-m/(β(1 - β))`, from the explicit formula), so it is excluded together with the complex zeros. The
residue computation itself (the Mellin transform of the weighted prime sum) is not formalized here.
-/

open Complex Filter Topology Set MeasureTheory

open scoped ComplexOrder

noncomputable section

namespace ProofPhase.Bridge

/-- **Abstract sign lemma.** Non-negative real part just right of `x₀` and `F = g + R/(s - x₀)` there, `g`
continuous at `x₀`: then `R ≥ 0`. -/
theorem residue_nonneg_of_re_nonneg {F g : ℂ → ℂ} {x₀ r R : ℝ} (hr : 0 < r)
    (hg : ContinuousAt g (x₀ : ℂ))
    (hpos : ∀ σ : ℝ, x₀ < σ → σ < x₀ + r → 0 ≤ (F σ).re)
    (heq : ∀ σ : ℝ, x₀ < σ → σ < x₀ + r → F σ = g σ + (R : ℂ) / ((σ : ℂ) - x₀)) : 0 ≤ R := by
  by_contra hR
  rw [not_le] at hR
  have h1 : Tendsto (fun σ : ℝ => σ - x₀) (𝓝[>] x₀) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun σ : ℝ => σ - x₀) (𝓝 x₀) (𝓝 (x₀ - x₀)) :=
        (continuous_id.sub continuous_const).tendsto x₀
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact sub_pos.mpr (mem_Ioi.mp hσ)
  have h2 : Tendsto (fun σ : ℝ => R * (σ - x₀)⁻¹) (𝓝[>] x₀) atBot :=
    (h1.inv_tendsto_nhdsGT_zero).const_mul_atTop_of_neg hR
  have h3 : Tendsto (fun σ : ℝ => (g σ).re) (𝓝[>] x₀) (𝓝 (g x₀).re) :=
    ((Complex.continuous_re.continuousAt.comp
      (hg.comp Complex.continuous_ofReal.continuousAt)).tendsto).mono_left nhdsWithin_le_nhds
  have h4 : Tendsto (fun σ : ℝ => (g σ).re + R * (σ - x₀)⁻¹) (𝓝[>] x₀) atBot := h3.add_atBot h2
  have hev1 : ∀ᶠ σ : ℝ in 𝓝[>] x₀, (g (σ : ℂ)).re + R * (σ - x₀)⁻¹ < 0 := h4.eventually (eventually_lt_atBot 0)
  have hev2 : ∀ᶠ σ : ℝ in 𝓝[>] x₀, x₀ < σ ∧ σ < x₀ + r := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by linarith : x₀ < x₀ + r))] with σ ha hb using ⟨ha, hb⟩
  obtain ⟨σ, hσ1, hσ2, hσ3⟩ := (hev1.and hev2).exists
  have hp := hpos σ hσ2 hσ3
  rw [heq σ hσ2 hσ3] at hp
  have hre : (g σ + (R : ℂ) / ((σ : ℂ) - x₀)).re = (g σ).re + R * (σ - x₀)⁻¹ := by
    rw [Complex.add_re, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re, div_eq_mul_inv]
  rw [hre] at hp
  linarith

theorem mem_ball_of_real {x₀ r σ : ℝ} (h1 : x₀ < σ) (h2 : σ < x₀ + r) :
    (σ : ℂ) ∈ Metric.ball (x₀ : ℂ) r := by
  rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith)]
  linarith

/-- The Laplace transform of any measure has non-negative real part at real points. -/
theorem lap_re_nonneg (μ : Measure ℝ) (σ : ℝ) : 0 ≤ (lap μ σ).re := by
  rw [lap_ofReal_eq_corr, Complex.ofReal_re, corr]
  exact integral_nonneg fun _ => (Real.exp_pos _).le

/-- **No pole of negative residue for a Laplace transform** (approached from the right of a real point). -/
theorem laplace_residue_nonneg {μ : Measure ℝ} {x₀ r R : ℝ} (hr : 0 < r) {g : ℂ → ℂ}
    (hg : ContinuousAt g (x₀ : ℂ))
    (heq : ∀ s ∈ Metric.ball (x₀ : ℂ) r, x₀ < s.re → lap μ s = g s + (R : ℂ) / (s - x₀)) : 0 ≤ R :=
  residue_nonneg_of_re_nonneg hr hg (fun σ _ _ => lap_re_nonneg μ σ)
    (fun σ h1 h2 => heq σ (mem_ball_of_real h1 h2) (by simpa using h1))

/-- **Ray form with poles, Laplace.** Around every real `x > θ` right of which the integral converges, `lap μ` is
`g + R/(s - x)` with `g` holomorphic on a disc and `R ≤ 0`. Then the integral converges on all of `(θ, ∞)`. -/
theorem laplace_ray_poles {μ : Measure ℝ} (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hne : ∃ x, LapConv μ x) {θ : ℝ}
    (hext : ∀ x : ℝ, θ < x → (∀ y > x, LapConv μ y) → ∃ (r : ℝ) (g : ℂ → ℂ) (R : ℝ), 0 < r ∧ R ≤ 0 ∧
      DifferentiableOn ℂ g (Metric.ball (x : ℂ) r) ∧
      ∀ s ∈ Metric.ball (x : ℂ) r, x < s.re → lap μ s = g s + (R : ℂ) / (s - x)) :
    ∀ x > θ, LapConv μ x := by
  refine laplace_ray hμ hne fun x hx hright => ?_
  obtain ⟨r, g, R, hr, hR, hg, heq⟩ := hext x hx hright
  have hR0 : R = 0 := le_antisymm hR (laplace_residue_nonneg hr
    (hg.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).continuousAt heq)
  exact ⟨r, g, hr, hg, fun s hs hre => by rw [heq s hs hre, hR0]; simp⟩

/-- An L-series with non-negative coefficients has non-negative real part at real points. -/
theorem lseries_re_nonneg {a : ℕ → ℂ} (ha : 0 ≤ a) (σ : ℝ) : 0 ≤ (LSeries a σ).re := by
  have h : (0 : ℂ) ≤ LSeries a σ := tsum_nonneg fun n => LSeries.term_nonneg (ha n) σ
  exact (Complex.nonneg_iff.mp h).1

/-- **No pole of negative residue for an L-series with non-negative coefficients.** -/
theorem lseries_residue_nonneg {a : ℕ → ℂ} (ha : 0 ≤ a) {x₀ r R : ℝ} (hr : 0 < r) {g : ℂ → ℂ}
    (hg : ContinuousAt g (x₀ : ℂ))
    (heq : ∀ s ∈ Metric.ball (x₀ : ℂ) r, x₀ < s.re → LSeries a s = g s + (R : ℂ) / (s - x₀)) : 0 ≤ R :=
  residue_nonneg_of_re_nonneg hr hg (fun σ _ _ => lseries_re_nonneg ha σ)
    (fun σ h1 h2 => heq σ (mem_ball_of_real h1 h2) (by simpa using h1))

/-- **Ray form with poles, L-series (Landau plus the sign).** Non-negative coefficients, convergence somewhere, and
around every real `x > θ` (at or right of the abscissa) the series is `g + R/(s - x)` with `g` holomorphic on a disc
and `R ≤ 0`. Then the abscissa is at most `θ`. -/
theorem landau_ray_poles {a : ℕ → ℂ} (ha : 0 ≤ a) (hfin : LSeries.abscissaOfAbsConv a < ⊤) {θ : ℝ}
    (hext : ∀ x : ℝ, θ < x → LSeries.abscissaOfAbsConv a ≤ x → ∃ (r : ℝ) (g : ℂ → ℂ) (R : ℝ), 0 < r ∧ R ≤ 0 ∧
      DifferentiableOn ℂ g (Metric.ball (x : ℂ) r) ∧
      ∀ s ∈ Metric.ball (x : ℂ) r, x < s.re → LSeries a s = g s + (R : ℂ) / (s - x)) :
    LSeries.abscissaOfAbsConv a ≤ θ := by
  refine landau_ray ha hfin fun x hx habs => ?_
  obtain ⟨r, g, R, hr, hR, hg, heq⟩ := hext x hx habs
  have hR0 : R = 0 := le_antisymm hR (lseries_residue_nonneg ha hr
    (hg.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).continuousAt heq)
  exact ⟨r, g, hr, hg, fun s hs hre => by rw [heq s hs hre, hR0]; simp⟩

end ProofPhase.Bridge
