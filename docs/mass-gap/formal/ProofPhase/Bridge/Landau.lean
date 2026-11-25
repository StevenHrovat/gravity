/-
RH-YM bridge, Part 1, module 2: Instance A, Landau's theorem for Dirichlet series with non-negative coefficients
(2026-11-23). Released under Apache 2.0.

Note: `docs/rh-guide/bridge/BRIDGE.md`.
-/

import ProofPhase.Bridge.Pringsheim
import Mathlib.NumberTheory.LSeries.Positivity

/-!
# Landau's theorem for L-series with non-negative coefficients

Mathlib's `LSeries a s = ∑ a n / n^s` with abscissa of absolute convergence `LSeries.abscissaOfAbsConv a` (an
`EReal`). For non-negative coefficients absolute and ordinary convergence agree, so this is the abscissa.

**Main results.**
* `landau_summable_left`: if `LSeries a` (with `0 ≤ a`) agrees, to the right of a real point `x₀ ≥` abscissa, with a
  function holomorphic on a disc about `x₀`, then the series already converges at some real point left of `x₀`.
* `landau`: **Landau's theorem.** If the abscissa is a real number `x₀`, then `LSeries a` has no holomorphic
  extension to any disc about `x₀`: the real point of the abscissa is a singularity.
* `landau_ray`: **the one-sided usable form.** If `LSeries a` converges somewhere and continues holomorphically
  around every real point `x > θ`, then it converges absolutely for every `s` with `Re s > θ`.

**From Mathlib:** `LSeries_iteratedDeriv` (the derivatives of an L-series), `LSeries.iteratedDeriv_alternating` (their
signs for non-negative coefficients), `LSeriesSummable_of_abscissaOfAbsConv_lt_re`,
`LSeriesSummable.abscissaOfAbsConv_le`, `LSeries.abscissaOfAbsConv_logMul`, `Complex.hasSum_taylorSeries_on_ball`.
Mathlib has no form of Landau's theorem; this file adds it. The analytic step is the shared
`ProofPhase.Bridge.pringsheim_summable`; the rest is the swap of a non-negative double series
(`summable_prod_of_nonneg`).
-/

open Complex Nat LSeries Filter Topology

open scoped ComplexOrder

noncomputable section

namespace ProofPhase.Bridge

/-- The iterated `logMul`. -/
theorem logMul_iterate_apply (a : ℕ → ℂ) (n k : ℕ) :
    (LSeries.logMul^[n] a) k = (Complex.log k) ^ n * a k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', LSeries.logMul, ih, pow_succ]
      ring

theorem abscissaOfAbsConv_logMul_iterate (a : ℕ → ℂ) (n : ℕ) :
    LSeries.abscissaOfAbsConv (LSeries.logMul^[n] a) = LSeries.abscissaOfAbsConv a := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', LSeries.abscissaOfAbsConv_logMul, ih]

/-- A non-negative complex coefficient is the cast of its real part. -/
theorem eq_ofReal_re_of_nonneg {z : ℂ} (hz : 0 ≤ z) : z = (z.re : ℂ) :=
  Complex.eq_re_of_ofReal_le (r := 0) (by simpa using hz)

/-- The term of `logMul^[n] a` at a real point, as a real number. -/
theorem term_logMul_iterate {a : ℕ → ℂ} (ha : 0 ≤ a) (n k : ℕ) (x : ℝ) :
    LSeries.term (LSeries.logMul^[n] a) (x : ℂ) k
      = ((if k = 0 then 0 else (a k).re * Real.log k ^ n * ((k : ℝ) ^ x)⁻¹ : ℝ) : ℂ) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · simp only [hk, ↓reduceIte]
    rw [LSeries.term_of_ne_zero hk, logMul_iterate_apply, ← Complex.natCast_log]
    conv_lhs => rw [eq_ofReal_re_of_nonneg (ha k)]
    have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [show ((k : ℂ)) = ((k : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_cpow hk']
    push_cast
    ring

/-- The `n`-th Taylor coefficient size of an L-series at a real point. -/
def landauCoeff (a : ℕ → ℂ) (x : ℝ) (n : ℕ) : ℝ :=
  ∑' k : ℕ, (if k = 0 then 0 else (a k).re * Real.log k ^ n * ((k : ℝ) ^ x)⁻¹)

theorem landauCoeff_term_nonneg {a : ℕ → ℂ} (ha : 0 ≤ a) (x : ℝ) (n k : ℕ) :
    0 ≤ (if k = 0 then 0 else (a k).re * Real.log k ^ n * ((k : ℝ) ^ x)⁻¹ : ℝ) := by
  split_ifs with hk
  · exact le_rfl
  · have h1 : 0 ≤ (a k).re := (Complex.nonneg_iff.mp (ha k)).1
    have h2 : 0 ≤ Real.log k := Real.log_natCast_nonneg k
    have h3 : 0 ≤ ((k : ℝ) ^ x)⁻¹ := inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg k) x)
    positivity

theorem landauCoeff_summable {a : ℕ → ℂ} (ha : 0 ≤ a) {x : ℝ}
    (hx : LSeries.abscissaOfAbsConv a < x) (n : ℕ) :
    Summable (fun k : ℕ => (if k = 0 then 0 else (a k).re * Real.log k ^ n * ((k : ℝ) ^ x)⁻¹ : ℝ)) := by
  have hs : LSeriesSummable (LSeries.logMul^[n] a) (x : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      rw [abscissaOfAbsConv_logMul_iterate]; simpa using hx)
  have := hs.norm
  refine this.congr fun k => ?_
  rw [term_logMul_iterate ha, Complex.norm_real, Real.norm_of_nonneg (landauCoeff_term_nonneg ha x n k)]

/-- The derivatives of an L-series with non-negative coefficients, at a real point right of the abscissa. -/
theorem iteratedDeriv_LSeries_eq {a : ℕ → ℂ} (ha : 0 ≤ a) {x : ℝ}
    (hx : LSeries.abscissaOfAbsConv a < x) (n : ℕ) :
    iteratedDeriv n (LSeries a) (x : ℂ) = (-1) ^ n * (landauCoeff a x n : ℂ) := by
  rw [LSeries_iteratedDeriv _ (by simpa using hx), LSeries]
  congr 1
  rw [landauCoeff, Complex.ofReal_tsum]
  exact tsum_congr fun k => term_logMul_iterate ha n k x

/-- The double series of the Tonelli step: `k`-th coefficient times the `n`-th exponential term. -/
def landauDouble (a : ℕ → ℂ) (c h : ℝ) (k n : ℕ) : ℝ :=
  (if k = 0 then 0 else (a k).re * Real.log k ^ n * ((k : ℝ) ^ c)⁻¹) * (h ^ n / n !)

theorem landauDouble_nonneg {a : ℕ → ℂ} (ha : 0 ≤ a) (c : ℝ) {h : ℝ} (h0 : 0 ≤ h) (k n : ℕ) :
    0 ≤ landauDouble a c h k n :=
  mul_nonneg (landauCoeff_term_nonneg ha c n k) (by positivity)

theorem landauDouble_row (a : ℕ → ℂ) (c h : ℝ) (n : ℕ) :
    ∑' k : ℕ, landauDouble a c h k n = landauCoeff a c n * h ^ n / n ! := by
  unfold landauDouble landauCoeff
  rw [tsum_mul_right]
  ring

theorem landauDouble_col {a : ℕ → ℂ} (ha : 0 ≤ a) (c h : ℝ) (k : ℕ) :
    ∑' n : ℕ, landauDouble a c h k n = ‖LSeries.term a ((c - h : ℝ) : ℂ) k‖ := by
  rcases eq_or_ne k 0 with rfl | hk0
  · simp [landauDouble]
  · have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
    have hexp : HasSum (fun n : ℕ => (h * Real.log k) ^ n / n !) (Real.exp (h * Real.log k)) := by
      rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp (h * Real.log k)
    have e : (fun n : ℕ => landauDouble a c h k n)
        = fun n : ℕ => ((a k).re * ((k : ℝ) ^ c)⁻¹) * ((h * Real.log k) ^ n / n !) := by
      funext n
      simp only [landauDouble, hk0, ↓reduceIte]
      rw [mul_pow]; ring
    have hnorm : ‖a k‖ = (a k).re := by
      conv_lhs => rw [eq_ofReal_re_of_nonneg (ha k)]
      rw [Complex.norm_real, Real.norm_of_nonneg (Complex.nonneg_iff.mp (ha k)).1]
    rw [e, (hexp.mul_left _).tsum_eq, LSeries.norm_term_eq]
    simp only [hk0, ↓reduceIte]
    rw [Complex.ofReal_re, hnorm, mul_comm h, Real.exp_mul, Real.exp_log hkpos, Real.rpow_sub hkpos]
    field_simp

/-- **Tonelli step.** If `∑ M n h^n / n!` converges, where `M n` are the Taylor sizes at `c`, then the L-series
converges absolutely at `c - h`. -/
theorem lseriesSummable_of_taylor {a : ℕ → ℂ} (ha : 0 ≤ a) {c h : ℝ} (h0 : 0 ≤ h)
    (hc : LSeries.abscissaOfAbsConv a < c)
    (hsum : Summable (fun n => landauCoeff a c n * h ^ n / n !)) :
    LSeriesSummable a ((c - h : ℝ) : ℂ) := by
  have hprod : Summable (fun p : ℕ × ℕ => landauDouble a c h p.2 p.1) := by
    rw [summable_prod_of_nonneg (fun p => landauDouble_nonneg ha c h0 p.2 p.1)]
    refine ⟨fun n => ?_, ?_⟩
    · show Summable (fun k => landauDouble a c h k n)
      unfold landauDouble
      exact (landauCoeff_summable ha hc n).mul_right _
    · show Summable (fun n => ∑' k, landauDouble a c h k n)
      exact hsum.congr fun n => (landauDouble_row a c h n).symm
  have hk : Summable (fun k : ℕ => ∑' n : ℕ, landauDouble a c h k n) := hprod.prod_symm.prod
  have : Summable (fun k : ℕ => ‖LSeries.term a ((c - h : ℝ) : ℂ) k‖) :=
    hk.congr (landauDouble_col ha c h)
  exact this.of_norm

/-- **Landau, extension form.** If `LSeries a` (with `0 ≤ a`) agrees, right of a real point `x₀ ≥` abscissa, with a
function holomorphic on a disc about `x₀`, then it converges absolutely at a real point left of `x₀`. This is the
shared `pringsheim_extension` plus the Tonelli step `lseriesSummable_of_taylor`. -/
theorem landau_summable_left {a : ℕ → ℂ} (ha : 0 ≤ a) {x₀ r : ℝ} (hr : 0 < r)
    (hx₀ : LSeries.abscissaOfAbsConv a ≤ x₀) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball (x₀ : ℂ) r))
    (hgeq : ∀ s ∈ Metric.ball (x₀ : ℂ) r, x₀ < s.re → g s = LSeries a s) :
    ∃ y : ℝ, y < x₀ ∧ LSeriesSummable a (y : ℂ) := by
  have hcx : ∀ c : ℝ, x₀ < c → LSeries.abscissaOfAbsConv a < c := fun c hc =>
    lt_of_le_of_lt hx₀ (by exact_mod_cast hc)
  have hF : ∀ s : ℂ, x₀ < s.re → DifferentiableAt ℂ (LSeries a) s := fun s hs =>
    (LSeries_hasDerivAt (lt_of_le_of_lt hx₀ (by exact_mod_cast hs))).differentiableAt
  obtain ⟨c, h, hxc, h0, hlt, hsum⟩ := pringsheim_extension hr hF
    (fun c hc n => iteratedDeriv_LSeries_eq ha (hcx c hc) n) hg hgeq
  exact ⟨c - h, hlt, lseriesSummable_of_taylor ha h0 (hcx c hxc) hsum⟩

/-- **Landau's theorem.** For non-negative coefficients with real abscissa `x₀`, the L-series has no holomorphic
extension to any disc about `x₀`: the real point of the abscissa is a singularity. -/
theorem landau {a : ℕ → ℂ} (ha : 0 ≤ a) {x₀ : ℝ} (hx₀ : LSeries.abscissaOfAbsConv a = x₀) :
    ¬ ∃ (r : ℝ) (g : ℂ → ℂ), 0 < r ∧ DifferentiableOn ℂ g (Metric.ball (x₀ : ℂ) r) ∧
      ∀ s ∈ Metric.ball (x₀ : ℂ) r, x₀ < s.re → g s = LSeries a s := by
  rintro ⟨r, g, hr, hg, hgeq⟩
  obtain ⟨y, hy, hs⟩ := landau_summable_left ha hr hx₀.le hg hgeq
  have := hs.abscissaOfAbsConv_le
  rw [hx₀, Complex.ofReal_re] at this
  exact absurd (EReal.coe_le_coe_iff.mp this) (not_le.mpr hy)

/-- **Landau, one-sided usable form.** Non-negative coefficients; the L-series converges somewhere, and around every
real point `x > θ` it agrees (right of `x`, where it converges) with a function holomorphic on a disc about `x`.
Then the abscissa is at most `θ`: the series converges absolutely, hence is holomorphic, on `Re s > θ`. -/
theorem landau_ray {a : ℕ → ℂ} (ha : 0 ≤ a) (hfin : LSeries.abscissaOfAbsConv a < ⊤) {θ : ℝ}
    (hext : ∀ x : ℝ, θ < x → LSeries.abscissaOfAbsConv a ≤ x → ∃ (r : ℝ) (g : ℂ → ℂ), 0 < r ∧
      DifferentiableOn ℂ g (Metric.ball (x : ℂ) r) ∧
      ∀ s ∈ Metric.ball (x : ℂ) r, x < s.re → g s = LSeries a s) :
    LSeries.abscissaOfAbsConv a ≤ θ := by
  by_contra hlt
  rw [not_le] at hlt
  -- the abscissa is a real number `x₀ > θ`
  have hbot : LSeries.abscissaOfAbsConv a ≠ ⊥ := ne_bot_of_gt hlt
  set x₀ : ℝ := (LSeries.abscissaOfAbsConv a).toReal with hx₀def
  have hx₀ : LSeries.abscissaOfAbsConv a = x₀ := (EReal.coe_toReal hfin.ne hbot).symm
  have hθ : θ < x₀ := by rw [hx₀] at hlt; exact_mod_cast hlt
  obtain ⟨r, g, hr, hg, hgeq⟩ := hext x₀ hθ hx₀.le
  exact landau ha hx₀ ⟨r, g, hr, hg, hgeq⟩

/-- **Landau, zero-free corollary.** In the shape the RH proof's stage A uses: if the series has non-negative
coefficients and continues holomorphically along the real ray `(θ, ∞)`, then on `Re s > θ` it is the holomorphic
function `LSeries a` itself (no pole, hence no zero of whatever denominator produced it, can sit there). -/
theorem landau_ray_differentiable {a : ℕ → ℂ} (ha : 0 ≤ a) (hfin : LSeries.abscissaOfAbsConv a < ⊤) {θ : ℝ}
    (hext : ∀ x : ℝ, θ < x → LSeries.abscissaOfAbsConv a ≤ x → ∃ (r : ℝ) (g : ℂ → ℂ), 0 < r ∧
      DifferentiableOn ℂ g (Metric.ball (x : ℂ) r) ∧
      ∀ s ∈ Metric.ball (x : ℂ) r, x < s.re → g s = LSeries a s)
    {s : ℂ} (hs : θ < s.re) :
    LSeriesSummable a s ∧ DifferentiableAt ℂ (LSeries a) s := by
  have h := landau_ray ha hfin hext
  have hlt : LSeries.abscissaOfAbsConv a < s.re := lt_of_le_of_lt h (by exact_mod_cast hs)
  exact ⟨LSeriesSummable_of_abscissaOfAbsConv_lt_re hlt, (LSeries_hasDerivAt hlt).differentiableAt⟩

end ProofPhase.Bridge
