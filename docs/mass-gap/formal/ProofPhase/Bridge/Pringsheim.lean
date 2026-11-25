/-
RH-YM bridge, Part 1, module 1: the shared lemma "positive weights locate the singularities" (Pringsheim-Landau),
in its power-series core (2026-11-23). Released under Apache 2.0.

Note: `docs/rh-guide/bridge/BRIDGE.md`.
-/

import Mathlib.Analysis.Complex.TaylorSeries

/-!
# The Pringsheim core

**Statement (`pringsheim_hasSum`).** Let `G` be holomorphic on the open disc of radius `R` about a real point `c`,
and suppose its Taylor coefficients at `c` alternate in sign with non-negative size:
`iteratedDeriv n G c = (-1)^n * M n` with `M n ≥ 0` real. Then for every real `0 ≤ h < R` the series
`∑ M n * h^n / n!` converges, with sum `Re G (c - h)`.

This is the analytic heart of Pringsheim's theorem (a power series with non-negative coefficients is singular at the
real point of its circle of convergence) and of Landau's theorem (a Dirichlet series or Laplace transform with
non-negative weights is singular at the real point of its abscissa). The two instances use it like this: the Taylor
coefficients `M n` are themselves sums (or integrals) of non-negative terms, so the convergent double series may be
summed in the other order (Tonelli), which gives convergence of the original series or integral at `c - h`. If `G`
is holomorphic in a disc reaching past the abscissa, the original series therefore converges past the abscissa,
which is absurd. See `ProofPhase.Bridge.Landau` (Dirichlet series) and `ProofPhase.Bridge.Laplace` (measures).

**Extension form (`pringsheim_extension`).** The shared theorem both instances use. Let `F` be holomorphic on the
half-plane `Re s > x₀`, with alternating non-negative Taylor coefficients at every real `c > x₀`, and suppose `F`
agrees there with a function `g` holomorphic on a disc about the real point `x₀`. Then for some real `c > x₀` and
`h ≥ 0` with `c - h < x₀`, the series `∑ M c n h^n / n!` converges: the Taylor series reaches past `x₀`.

The only Mathlib input is `Complex.hasSum_taylorSeries_on_ball` (Cauchy's theorem in Taylor form).
-/

open Complex Nat Filter Topology

noncomputable section

namespace ProofPhase.Bridge

/-- **Pringsheim core.** A function holomorphic on `ball c R` (with `c` real) whose Taylor coefficients at `c` are
`(-1)^n M n`, `M n ≥ 0`, has `∑ M n h^n / n! = Re G (c - h)` for every real `h ∈ [0, R)`. -/
theorem pringsheim_hasSum {G : ℂ → ℂ} {c R : ℝ} (hG : DifferentiableOn ℂ G (Metric.ball (c : ℂ) R))
    {M : ℕ → ℝ} (hder : ∀ n, iteratedDeriv n G c = (-1) ^ n * (M n : ℂ)) {h : ℝ} (h0 : 0 ≤ h)
    (hR : h < R) :
    HasSum (fun n => M n * h ^ n / n !) (G ((c - h : ℝ) : ℂ)).re := by
  have hz : ((c - h : ℝ) : ℂ) ∈ Metric.ball (c : ℂ) R := by
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [show c - h - c = -h by ring, abs_neg, abs_of_nonneg h0]
    exact hR
  have H := Complex.hasSum_taylorSeries_on_ball hG hz
  have hterm : ∀ n : ℕ, (n ! : ℂ)⁻¹ • (((c - h : ℝ) : ℂ) - c) ^ n • iteratedDeriv n G c
      = ((M n * h ^ n / n ! : ℝ) : ℂ) := by
    intro n
    rw [hder n, smul_eq_mul, smul_eq_mul]
    have e1 : (((c - h : ℝ) : ℂ) - c) = (-1) * (h : ℂ) := by push_cast; ring
    rw [e1, mul_pow]
    have e2 : ((-1 : ℂ) ^ n * (h : ℂ) ^ n) * ((-1) ^ n * (M n : ℂ))
        = ((-1 : ℂ) ^ n * (-1) ^ n) * ((h : ℂ) ^ n * M n) := by ring
    rw [e2, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    push_cast
    field_simp
  simp_rw [hterm] at H
  have H' := Complex.hasSum_re H
  simpa only [Complex.ofReal_re] using H'

/-- The summability form of the core, the shape used by both instances. -/
theorem pringsheim_summable {G : ℂ → ℂ} {c R : ℝ} (hG : DifferentiableOn ℂ G (Metric.ball (c : ℂ) R))
    {M : ℕ → ℝ} (hder : ∀ n, iteratedDeriv n G c = (-1) ^ n * (M n : ℂ)) {h : ℝ} (h0 : 0 ≤ h)
    (hR : h < R) :
    Summable (fun n => M n * h ^ n / n !) :=
  (pringsheim_hasSum hG hder h0 hR).summable

/-- **Gluing.** If `F` is holomorphic on `Re s > x₀` and agrees there with `g`, holomorphic on `ball x₀ r`, then the
function equal to `F` right of `x₀` and to `g` elsewhere is holomorphic on `ball (x₀ + r/4) (r/2)`. -/
theorem glue_differentiableOn {F g : ℂ → ℂ} {x₀ r : ℝ}
    (hF : ∀ s : ℂ, x₀ < s.re → DifferentiableAt ℂ F s)
    (hg : DifferentiableOn ℂ g (Metric.ball (x₀ : ℂ) r))
    (hgeq : ∀ s ∈ Metric.ball (x₀ : ℂ) r, x₀ < s.re → g s = F s) :
    DifferentiableOn ℂ (fun s => if x₀ < s.re then F s else g s)
      (Metric.ball ((x₀ + r / 4 : ℝ) : ℂ) (r / 2)) := by
  set G : ℂ → ℂ := fun s => if x₀ < s.re then F s else g s with hG
  have hU : IsOpen {s : ℂ | x₀ < s.re} := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  by_cases hre : x₀ < s.re
  · have hev : G =ᶠ[𝓝 s] F := by
      filter_upwards [hU.mem_nhds hre] with t ht
      simp only [hG, show x₀ < t.re from ht, ↓reduceIte]
    exact (hF s hre).congr_of_eventuallyEq hev
  · have hsb : s ∈ Metric.ball (x₀ : ℂ) r := by
      rw [Metric.mem_ball] at hs ⊢
      have hr : 0 < r := by
        have := dist_nonneg.trans_lt hs; linarith
      have h1 : dist ((x₀ + r / 4 : ℝ) : ℂ) (x₀ : ℂ) = r / 4 := by
        rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        rw [show x₀ + r / 4 - x₀ = r / 4 by ring, abs_of_pos (by linarith)]
      calc dist s x₀ ≤ dist s ((x₀ + r / 4 : ℝ) : ℂ) + dist ((x₀ + r / 4 : ℝ) : ℂ) x₀ :=
            dist_triangle _ _ _
        _ < r / 2 + r / 4 := by rw [h1]; linarith
        _ < r := by linarith
    have hev : G =ᶠ[𝓝 s] g := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hsb] with t ht
      simp only [hG]
      split_ifs with h
      · exact (hgeq t ht h).symm
      · rfl
    exact (hg.differentiableAt (Metric.isOpen_ball.mem_nhds hsb)).congr_of_eventuallyEq hev

/-- **Pringsheim-Landau, extension form (the shared theorem).** `F` holomorphic on `Re s > x₀` with Taylor
coefficients `(-1)^n M c n`, `M c n ≥ 0`, at every real `c > x₀`; `F` agrees right of `x₀` with `g`, holomorphic on a
disc about `x₀`. Then the Taylor series at some real `c > x₀` converges at a real point `c - h < x₀`, in the sense
that `∑ M c n h^n / n!` is summable. (Each instance then sums its double series the other way.) -/
theorem pringsheim_extension {F g : ℂ → ℂ} {x₀ r : ℝ} (hr : 0 < r)
    (hF : ∀ s : ℂ, x₀ < s.re → DifferentiableAt ℂ F s)
    {M : ℝ → ℕ → ℝ} (hder : ∀ c : ℝ, x₀ < c → ∀ n, iteratedDeriv n F c = (-1) ^ n * (M c n : ℂ))
    (hg : DifferentiableOn ℂ g (Metric.ball (x₀ : ℂ) r))
    (hgeq : ∀ s ∈ Metric.ball (x₀ : ℂ) r, x₀ < s.re → g s = F s) :
    ∃ c h : ℝ, x₀ < c ∧ 0 ≤ h ∧ c - h < x₀ ∧ Summable (fun n => M c n * h ^ n / n !) := by
  set c : ℝ := x₀ + r / 4 with hcdef
  have hGd := glue_differentiableOn hF hg hgeq
  set G : ℂ → ℂ := fun s => if x₀ < s.re then F s else g s with hG
  have hU : IsOpen {s : ℂ | x₀ < s.re} := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hEq : Set.EqOn G F {s : ℂ | x₀ < s.re} := fun s hs => by
    simp only [hG, show x₀ < s.re from hs, ↓reduceIte]
  have hxc : x₀ < c := by linarith
  have hcU : (c : ℂ) ∈ {s : ℂ | x₀ < s.re} := by
    show x₀ < (c : ℂ).re
    rw [Complex.ofReal_re]; exact hxc
  have hderG : ∀ n, iteratedDeriv n G c = (-1) ^ n * (M c n : ℂ) := fun n => by
    rw [hEq.iteratedDeriv_of_isOpen hU n hcU, hder c hxc n]
  exact ⟨c, 3 * r / 8, hxc, by positivity, by linarith,
    pringsheim_summable hGd hderG (by positivity) (by linarith)⟩

end ProofPhase.Bridge
