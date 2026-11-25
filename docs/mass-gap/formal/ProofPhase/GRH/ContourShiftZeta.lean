/-
The contour shift, layer (b)/(c) for zeta: polynomial bounds for the logarithmic derivative of the completed zeta on
vertical lines and on horizontal segments at good heights, and a zero count per unit window (2026-11-24).
Released under Apache 2.0.

Paper: `docs/unified/CONTOUR-SHIFT.md`, section 5.
-/

import ProofPhase.GRH.ContourShiftLandau
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# Zeta: the entire function `ξ`, its growth, its zeros, and `Λ'/Λ`

* `xiF s = s (s - 1) Λ₀(s) + 1 = s (s - 1) Λ(s)`: entire, `xiF 0 = xiF 1 = 1`, zeros exactly the nontrivial zeros of
  `ζ` with the same orders (`xiF_eq_zero_iff`, `analyticOrderAt_xiF`).
* `exists_bound_completedZeta₀`: `Λ₀` is bounded on every vertical strip. This is immediate from Mathlib's definition of
  `Λ₀` as a Mellin transform (`|∫ t^{s-1} f(t) dt| ≤ ∫ (t^{a-1} + t^{b-1}) |f(t)| dt` for `a ≤ Re s ≤ b`); no convexity
  bound or Stirling formula for `ζ` is needed.
* `norm_Gamma_one_add_I_mul`: `|Γ(1 + ix)| ≥ e^{-π|x|/2}` (reflection formula: `|Γ(1 + ix)|² = πx / sinh(πx)`), and
  `norm_zeta_two_add`: `|ζ(2 + iy)| ≥ 2 - π²/6`; together a lower bound `|ξ(2 + iy)| ≥ c e^{-π|y|/4}`.
* `xi_data`: on the disc of radius `R` around `2 + iy`, `log(max|ξ| / |ξ(2 + iy)|) ≤ A (1 + |y|)²`.
* With Landau's lemma (`ContourShiftLandau.lean`): **`zero_count`** (the zeros within distance `R/3` of `2 + iy`,
  counted with multiplicity, number at most `B (1 + |y|)²`), **`logDeriv_vline_bound`** (`|Λ'/Λ| ≤ B (1 + |y|)²` on the
  lines `Re s = c` and `Re s = 1 - c`), and **`exists_good_height`** (in every interval `[a, a + 1]` with `|a| ≥ 1`
  there is a height `T` with no zero on the segment `[1 - c, c] + iT` and `|Λ'/Λ| ≤ B (1 + |a|)⁴` on it).

All bounds are polynomial; that is all the contour shift needs, because the transform of a smooth compactly supported
test function decays faster than any power (`ContourShiftTest.lean`). Standard axioms only.
-/

open Complex Metric Set Filter Topology MeasureTheory
open scoped Real ComplexConjugate

noncomputable section

namespace ProofPhase.GRH.CS

/-! ### 1. The completed zeta is bounded on vertical strips -/

/-- A Mellin transform convergent at `a` and `b` is bounded on the strip `a ≤ Re s ≤ b`. -/
theorem norm_mellin_le_of_strip {f : ℝ → ℂ} {a b : ℝ} (ha : MellinConvergent f a) (hb : MellinConvergent f b)
    {s : ℂ} (h1 : a ≤ s.re) (h2 : s.re ≤ b) :
    ‖mellin f s‖ ≤ (∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ ((a : ℂ) - 1) • f t‖) +
      ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ ((b : ℂ) - 1) • f t‖ := by
  rw [← integral_add ha.norm hb.norm]
  refine norm_integral_le_of_norm_le (ha.norm.add hb.norm) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : (0 : ℝ) < t := ht
  simp only [norm_smul, norm_cpow_eq_rpow_re_of_pos ht', sub_re, ofReal_re, one_re]
  rw [← add_mul]
  gcongr
  rcases le_total t 1 with h | h
  · have : t ^ (s.re - 1) ≤ t ^ (a - 1) := Real.rpow_le_rpow_of_exponent_ge ht' h (by linarith)
    linarith [Real.rpow_nonneg ht'.le (b - 1)]
  · have : t ^ (s.re - 1) ≤ t ^ (b - 1) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
    linarith [Real.rpow_nonneg ht'.le (a - 1)]

/-- **`Λ₀` is bounded on vertical strips.** -/
theorem exists_bound_completedZeta₀ (K : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, |s.re| ≤ K → ‖completedRiemannZeta₀ s‖ ≤ C := by
  set P := HurwitzZeta.hurwitzEvenFEPair 0 with hP
  have hconv : ∀ t : ℂ, MellinConvergent P.f_modif t := fun t =>
    (P.isStrongFEPair_toStrongFEPair.hasMellin t).1
  set C0 := (∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (((-K / 2 : ℝ) : ℂ) - 1) • P.f_modif t‖) +
      ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (((K / 2 : ℝ) : ℂ) - 1) • P.f_modif t‖ with hC0
  refine ⟨C0 / 2, by positivity, fun s hs => ?_⟩
  have h1 : completedRiemannZeta₀ s = mellin P.f_modif (s / 2) / 2 := rfl
  rw [h1, norm_div, Complex.norm_ofNat]
  gcongr
  have hre : (s / 2).re = s.re / 2 := by simp
  exact norm_mellin_le_of_strip (hconv _) (hconv _) (by rw [hre]; linarith [neg_abs_le s.re])
    (by rw [hre]; linarith [le_abs_self s.re])

/-! ### 2. The entire function `ξ` -/

theorem Gammaℝ_eq' : Gammaℝ = fun s : ℂ => (π : ℂ) ^ (-s / 2) * Gamma (s / 2) := by
  funext s; exact Gammaℝ_def s

/-- `Γ_ℝ` is differentiable on `Re s > 0` (the same short proof as `EF.differentiableAt_Gammaℝ` in
`ExplicitFormulaPrime.lean`, repeated so that this file needs only Mathlib). -/
theorem differentiableAt_Gammaℝ' {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℝ s := by
  rw [Gammaℝ_eq']
  refine DifferentiableAt.mul ?_ ?_
  · exact ((differentiableAt_id.neg).div_const 2).const_cpow (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  · refine (differentiableAt_Gamma _ fun m hm => ?_).comp s (differentiableAt_id.div_const 2)
    have := congrArg Complex.re hm
    simp only [Complex.div_re, Complex.neg_re, Complex.natCast_re] at this
    norm_num at this
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]


/-- `ξ(s) = s (s - 1) Λ₀(s) + 1`, which equals `s (s - 1) Λ(s)`. -/
def xiF (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1

theorem differentiable_xiF : Differentiable ℂ xiF := by
  unfold xiF
  have := differentiable_completedZeta₀
  fun_prop

theorem xiF_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : xiF s = s * (s - 1) * completedRiemannZeta s := by
  have h1' : 1 - s ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have h1'' : s - 1 ≠ 0 := sub_ne_zero.2 h1
  rw [xiF, completedRiemannZeta_eq]
  field_simp
  ring

theorem xiF_zero : xiF 0 = 1 := by simp [xiF]

theorem xiF_one : xiF 1 = 1 := by simp [xiF]

/-- `Λ = Γ_ℝ ζ` on `Re s > 0`. -/
theorem completedZeta_eq_mul {s : ℂ} (hs : 0 < s.re) : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  rw [riemannZeta_def_of_ne_zero hs0]
  field_simp [Gammaℝ_ne_zero_of_re_pos hs]

theorem completedZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : completedRiemannZeta s ≠ 0 := by
  rw [completedZeta_eq_mul (by linarith)]
  exact mul_ne_zero (Gammaℝ_ne_zero_of_re_pos (by linarith)) (riemannZeta_ne_zero_of_one_le_re hs)

/-- **The zeros of `ξ` are the nontrivial zeros of `ζ`.** -/
theorem xiF_eq_zero_iff (s : ℂ) : xiF s = 0 ↔ 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 := by
  constructor
  · intro h
    have h0 : s ≠ 0 := fun h' => by rw [h', xiF_zero] at h; exact one_ne_zero h
    have h1 : s ≠ 1 := fun h' => by rw [h', xiF_one] at h; exact one_ne_zero h
    have hΛ : completedRiemannZeta s = 0 := by
      rw [xiF_eq h0 h1] at h
      rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h h0
        · exact absurd (sub_eq_zero.1 h) h1
      · exact h
    have hlt : s.re < 1 := by
      by_contra hc
      exact completedZeta_ne_zero_of_one_le_re (not_lt.1 hc) hΛ
    have hgt : 0 < s.re := by
      by_contra hc
      have : 1 ≤ (1 - s).re := by simp; linarith [not_lt.1 hc]
      exact completedZeta_ne_zero_of_one_le_re this (by rw [completedRiemannZeta_one_sub]; exact hΛ)
    refine ⟨hgt, hlt, ?_⟩
    rw [riemannZeta_def_of_ne_zero h0, hΛ, zero_div]
  · rintro ⟨h1, h2, h3⟩
    have h0 : s ≠ 0 := fun h => by simp [h] at h1
    have h1' : s ≠ 1 := fun h => by simp [h] at h2
    rw [xiF_eq h0 h1', completedZeta_eq_mul h1, h3, mul_zero, mul_zero]

/-- The zeros of `ξ` lie in the open critical strip. -/
theorem re_of_xiF_eq_zero {s : ℂ} (h : xiF s = 0) : 0 < s.re ∧ s.re < 1 :=
  ⟨((xiF_eq_zero_iff s).1 h).1, ((xiF_eq_zero_iff s).1 h).2.1⟩

/-- In the strip, `ξ` and `ζ` have the same order at every point. -/
theorem analyticOrderAt_xiF {s : ℂ} (h1 : 0 < s.re) (h2 : s.re < 1) :
    analyticOrderAt xiF s = analyticOrderAt riemannZeta s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at h1
  have hs1 : s ≠ 1 := fun h => by simp [h] at h2
  set e : ℂ → ℂ := fun t => t * (t - 1) * Gammaℝ t with he
  have hopen : IsOpen {t : ℂ | 0 < t.re ∧ t ≠ 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have hev : xiF =ᶠ[𝓝 s] fun t => e t * riemannZeta t := by
    filter_upwards [hopen.mem_nhds ⟨h1, hs1⟩] with t ht
    have ht0 : t ≠ 0 := fun h => by simp [h] at ht
    rw [xiF_eq ht0 ht.2, completedZeta_eq_mul ht.1, he]
    ring
  have hGa : AnalyticAt ℂ Gammaℝ s := by
    have hd : DifferentiableOn ℂ Gammaℝ {t : ℂ | 0 < t.re} := fun t ht =>
      (differentiableAt_Gammaℝ' ht).differentiableWithinAt
    exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1)
  have hea : AnalyticAt ℂ e s := by
    rw [he]
    exact ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul hGa)
  have hza : AnalyticAt ℂ riemannZeta s := by
    have hd : DifferentiableOn ℂ riemannZeta {t : ℂ | t ≠ 1} := fun t ht =>
      (differentiableAt_riemannZeta ht).differentiableWithinAt
    exact hd.analyticAt (isOpen_ne.mem_nhds hs1)
  have he0 : e s ≠ 0 := by
    rw [he]
    exact mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.2 hs1)) (Gammaℝ_ne_zero_of_re_pos h1)
  rw [analyticOrderAt_congr hev, show (fun t => e t * riemannZeta t) = e * riemannZeta from rfl,
    analyticOrderAt_mul hea hza, hea.analyticOrderAt_eq_zero.2 he0, zero_add]

/-- `Λ'/Λ = ξ'/ξ - 1/s - 1/(s - 1)` away from `0`, `1` and the zeros. -/
theorem logDeriv_completedZeta_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (hx : xiF s ≠ 0) :
    logDeriv completedRiemannZeta s = logDeriv xiF s - s⁻¹ - (s - 1)⁻¹ := by
  have hev : completedRiemannZeta =ᶠ[𝓝 s] fun t => xiF t / (t * (t - 1)) := by
    filter_upwards [isOpen_ne.mem_nhds h0, isOpen_ne.mem_nhds h1] with t ht0 ht1
    rw [xiF_eq ht0 ht1]
    field_simp [sub_ne_zero.2 ht1]
  have hp : s * (s - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.2 h1)
  rw [(logDeriv_congr_nhds hev).eq_of_nhds, logDeriv_fun_div s hx hp (differentiable_xiF s) (by fun_prop),
    logDeriv_fun_mul (f := fun t : ℂ => t) (g := fun t : ℂ => t - 1) s h0 (sub_ne_zero.2 h1) (by fun_prop)
      (by fun_prop)]
  have e1 : logDeriv (fun t : ℂ => t) s = s⁻¹ := by
    rw [logDeriv_apply, deriv_id'', one_div]
  have e2 : logDeriv (fun t : ℂ => t - 1) s = (s - 1)⁻¹ := by
    rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
  rw [e1, e2]
  ring

/-! ### 3. A lower bound at `2 + iy` -/

theorem sinh_le_mul_exp (u : ℝ) : Real.exp (-u) * Real.sinh u ≤ u := by
  rw [Real.sinh_eq]
  have h := Real.add_one_le_exp (-2 * u)
  have e : Real.exp (-u) * ((Real.exp u - Real.exp (-u)) / 2) = (1 - Real.exp (-2 * u)) / 2 := by
    rw [mul_div_assoc', mul_sub, ← Real.exp_add, ← Real.exp_add, show -u + u = 0 by ring,
      show -u + -u = -2 * u by ring, Real.exp_zero]
  rw [e]
  linarith

/-- `|Γ(1 + ix)|² = πx / sinh(πx)` for `x ≠ 0`. -/
theorem norm_sq_Gamma_one_add_I_mul {x : ℝ} (hx : x ≠ 0) :
    ‖Gamma (1 + I * x)‖ ^ 2 = π * x / Real.sinh (π * x) := by
  have hIx : I * (x : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.2 hx)
  have h1 : Gamma (1 + I * x) = I * x * Gamma (I * x) := by rw [add_comm, Gamma_add_one _ hIx]
  have h2 : Gamma (1 - I * x) = conj (Gamma (1 + I * x)) := by
    rw [← Gamma_conj]; congr 1; simp [map_add, map_mul, conj_ofReal]; ring
  have h3 := Gamma_mul_Gamma_one_sub (I * x)
  have h4 : Complex.sin (π * (I * x)) = Real.sinh (π * x) * I := by
    rw [show (π : ℂ) * (I * x) = ((π * x : ℝ) : ℂ) * I by push_cast; ring, sin_mul_I, ofReal_sinh]
  have hsinh : Real.sinh (π * x) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_ne_zero hx
  have key : ((‖Gamma (1 + I * x)‖ ^ 2 : ℝ) : ℂ) = ((π * x / Real.sinh (π * x) : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, ← h2, h1, mul_assoc, h3, h4]
    push_cast
    field_simp
  exact_mod_cast key

/-- **`|Γ(1 + ix)| ≥ e^{-π|x|/2}`.** -/
theorem norm_Gamma_one_add_I_mul (x : ℝ) : Real.exp (-(π * |x|) / 2) ≤ ‖Gamma (1 + I * x)‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hsq := norm_sq_Gamma_one_add_I_mul hx
  have hu : 0 < π * |x| := mul_pos Real.pi_pos (abs_pos.2 hx)
  have heven : π * x / Real.sinh (π * x) = π * |x| / Real.sinh (π * |x|) := by
    rcases lt_or_gt_of_ne hx with h | h
    · rw [abs_of_neg h, mul_neg, Real.sinh_neg, div_neg, neg_div, neg_neg]
    · rw [abs_of_pos h]
  have hlow : Real.exp (-(π * |x|)) ≤ π * |x| / Real.sinh (π * |x|) := by
    have hs : 0 < Real.sinh (π * |x|) := Real.sinh_pos_iff.2 hu
    rw [le_div_iff₀ hs]
    exact sinh_le_mul_exp _
  have h2 : Real.exp (-(π * |x|) / 2) ^ 2 ≤ ‖Gamma (1 + I * x)‖ ^ 2 := by
    rw [hsq, heven, ← Real.exp_nat_mul]
    convert hlow using 2
    push_cast; ring
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (norm_nonneg _) two_ne_zero).1 h2

/-- **`|ζ(2 + iy)| ≥ 2 - π²/6`.** -/
theorem norm_zeta_two_add (y : ℝ) : 2 - π ^ 2 / 6 ≤ ‖riemannZeta (2 + y * I)‖ := by
  set s : ℂ := 2 + y * I with hs
  have hre : s.re = 2 := by simp [hs]
  have hsum : HasSum (fun n : ℕ => (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2) (π ^ 2 / 6 - 1) := by
    have := (hasSum_nat_add_iff' 2).2 hasSum_zeta_two
    convert this using 1
    simp [Finset.sum_range_succ]
  have hnorm : ∀ n : ℕ, ‖(1 : ℂ) / ((n + 2 : ℕ) : ℂ) ^ s‖ = (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2 := by
    intro n
    have hpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
    rw [norm_div, norm_one, show (((n + 2 : ℕ) : ℂ)) = (((n + 2 : ℕ) : ℝ) : ℂ) by push_cast; ring,
      norm_cpow_eq_rpow_re_of_pos hpos, hre]
    norm_cast
  have hsumm : Summable fun n : ℕ => (1 : ℂ) / ((n + 2 : ℕ) : ℂ) ^ s :=
    Summable.of_norm (by simp_rw [hnorm]; exact hsum.summable)
  have hz : riemannZeta s = 1 + ∑' n : ℕ, (1 : ℂ) / ((n + 2 : ℕ) : ℂ) ^ s := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by rw [hre]; norm_num)]
    have hs1 : Summable fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1) ^ s := by
      have := (summable_nat_add_iff 1).2 hsumm
      refine (summable_nat_add_iff 1).1 ?_
      convert hsumm using 2 with n
      push_cast; ring_nf
    rw [hs1.tsum_eq_zero_add]
    congr 1
    · simp
    · refine tsum_congr fun n => ?_
      push_cast; ring_nf
  have hbound : ‖∑' n : ℕ, (1 : ℂ) / ((n + 2 : ℕ) : ℂ) ^ s‖ ≤ π ^ 2 / 6 - 1 := by
    refine (norm_tsum_le_tsum_norm (by simp_rw [hnorm]; exact hsum.summable)).trans (le_of_eq ?_)
    simp_rw [hnorm]
    exact hsum.tsum_eq
  rw [hz]
  have := norm_sub_le (1 + ∑' n : ℕ, (1 : ℂ) / ((n + 2 : ℕ) : ℂ) ^ s) (∑' n : ℕ, (1 : ℂ) / ((n + 2 : ℕ) : ℂ) ^ s)
  rw [add_sub_cancel_right, norm_one] at this
  linarith

/-- **The lower bound at `2 + iy`.** `|ξ(2 + iy)| ≥ (2/π)(2 - π²/6) e^{-π|y|/4}`. -/
theorem norm_xiF_two_add (y : ℝ) :
    2 / π * (2 - π ^ 2 / 6) * Real.exp (-(π * |y / 2|) / 2) ≤ ‖xiF (2 + y * I)‖ := by
  set s : ℂ := 2 + y * I with hs
  have hre : s.re = 2 := by simp [hs]
  have hs0 : s ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have hs1 : s ≠ 1 := fun h => by rw [h] at hre; simp at hre
  have hpi : 0 < 2 - π ^ 2 / 6 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  rw [xiF_eq hs0 hs1, completedZeta_eq_mul (by rw [hre]; norm_num), Gammaℝ_def]
  have hhalf : s / 2 = 1 + I * ((y / 2 : ℝ) : ℂ) := by rw [hs]; push_cast; ring
  rw [hhalf]
  have hcp : ‖(π : ℂ) ^ (-s / 2)‖ = π⁻¹ := by
    rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have : (-s / 2).re = -1 := by simp [hs]
    rw [this, Real.rpow_neg_one]
  simp only [norm_mul]
  have h1 : 2 ≤ ‖s‖ := by rw [← hre]; exact re_le_norm s
  have h2 : 1 ≤ ‖s - 1‖ := by
    have : (s - 1).re = 1 := by simp [hre]; norm_num
    rw [← this]; exact re_le_norm _
  have h3 := norm_Gamma_one_add_I_mul (y / 2)
  have h4 := norm_zeta_two_add y
  rw [← hs] at h4
  have hcp' : ‖(π : ℂ) ^ (-s / 2)‖ = π⁻¹ := hcp
  rw [hcp']
  have hE : 0 ≤ Real.exp (-(π * |y / 2|) / 2) := (Real.exp_pos _).le
  calc 2 / π * (2 - π ^ 2 / 6) * Real.exp (-(π * |y / 2|) / 2)
      = 2 * 1 * π⁻¹ * Real.exp (-(π * |y / 2|) / 2) * (2 - π ^ 2 / 6) := by ring
    _ ≤ ‖s‖ * ‖s - 1‖ * π⁻¹ * ‖Gamma (1 + I * ((y / 2 : ℝ) : ℂ))‖ * ‖riemannZeta s‖ := by
      gcongr
    _ = ‖s‖ * ‖s - 1‖ * (π⁻¹ * ‖Gamma (1 + I * ((y / 2 : ℝ) : ℂ))‖ * ‖riemannZeta s‖) := by ring

/-! ### 4. Growth data on discs around `2 + iy` -/

/-- **Growth data.** For every radius `R`, there is `A` with: for each height `y` some `M` bounds `|ξ|` on the disc of
radius `R` around `2 + iy`, and `log(M/|ξ(2 + iy)|) ≤ A (1 + |y|)²`. -/
theorem xi_data {R : ℝ} (hR : 0 < R) : ∃ A : ℝ, 0 < A ∧ ∀ y : ℝ, ∃ M : ℝ,
    (∀ z ∈ closedBall (2 + y * I) R, ‖xiF z‖ ≤ M) ∧ Real.log (M / ‖xiF (2 + y * I)‖) ≤ A * (1 + |y|) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_completedZeta₀ (R + 2)
  have hpi : 0 < 2 - π ^ 2 / 6 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  set κ := |Real.log (2 / π * (2 - π ^ 2 / 6))| with hκ
  refine ⟨(3 + R) ^ 2 * C + 2 + κ, by positivity, fun y => ⟨(3 + |y| + R) ^ 2 * C + 1, ?_, ?_⟩⟩
  · intro z hz
    have hz' : ‖z - (2 + y * I)‖ ≤ R := by rw [← dist_eq_norm]; exact mem_closedBall.1 hz
    have hc : ‖(2 + y * I : ℂ)‖ ≤ 2 + |y| := by
      refine (norm_add_le _ _).trans ?_
      simp [Complex.norm_real]
    have hzn : ‖z‖ ≤ 2 + |y| + R := by
      have := norm_le_norm_add_norm_sub' z (2 + y * I)
      linarith
    have hzn1 : ‖z - 1‖ ≤ 3 + |y| + R := by
      have := norm_sub_le z 1; simp at this; linarith
    have hre : |z.re| ≤ R + 2 := by
      have h1 : |(z - (2 + y * I)).re| ≤ R := (abs_re_le_norm _).trans hz'
      have h2 : (z - (2 + y * I)).re = z.re - 2 := by simp
      rw [h2] at h1
      have := abs_sub_abs_le_abs_sub z.re 2
      rw [abs_two] at this
      linarith
    calc ‖xiF z‖ ≤ ‖z * (z - 1) * completedRiemannZeta₀ z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ * ‖z - 1‖ * ‖completedRiemannZeta₀ z‖ + 1 := by rw [norm_mul, norm_mul, norm_one]
      _ ≤ (3 + |y| + R) * (3 + |y| + R) * C + 1 := by
          gcongr
          · linarith
          · exact hC z hre
      _ = (3 + |y| + R) ^ 2 * C + 1 := by ring
  · have hlow := norm_xiF_two_add y
    have hlb : 0 < 2 / π * (2 - π ^ 2 / 6) * Real.exp (-(π * |y / 2|) / 2) := by
      have := Real.pi_pos; positivity
    have hxpos : 0 < ‖xiF (2 + y * I)‖ := hlb.trans_le hlow
    have hM : 0 < (3 + |y| + R) ^ 2 * C + 1 := by positivity
    rw [Real.log_div hM.ne' hxpos.ne']
    have hlogM : Real.log ((3 + |y| + R) ^ 2 * C + 1) ≤ (3 + |y| + R) ^ 2 * C := by
      have := Real.log_le_sub_one_of_pos hM; linarith
    have hlogx : Real.log (2 / π * (2 - π ^ 2 / 6) * Real.exp (-(π * |y / 2|) / 2)) ≤
        Real.log ‖xiF (2 + y * I)‖ := Real.log_le_log hlb hlow
    have hlpos : 0 < 2 / π * (2 - π ^ 2 / 6) := by have := Real.pi_pos; positivity
    rw [Real.log_mul hlpos.ne' (Real.exp_pos _).ne', Real.log_exp] at hlogx
    have hk : -κ ≤ Real.log (2 / π * (2 - π ^ 2 / 6)) := neg_abs_le _
    have hy2 : |y / 2| = |y| / 2 := by rw [abs_div, abs_two]
    rw [hy2] at hlogx
    have hy0 : 0 ≤ |y| := abs_nonneg y
    have hpi4 : π * (|y| / 2) / 2 ≤ (1 + |y|) ^ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have hsq : (3 + |y| + R) ^ 2 ≤ (3 + R) ^ 2 * (1 + |y|) ^ 2 := by
      rw [← mul_pow]; gcongr; nlinarith
    have h1 : 1 ≤ (1 + |y|) ^ 2 := by nlinarith
    have hκ0 : 0 ≤ κ := abs_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hsq hC0]

/-- **The zero count on a disc.** The zeros of `ξ` within distance `R/3` of `2 + iy`, counted with multiplicity, number
at most `B (1 + |y|)²`. -/
theorem zero_count_ball {R : ℝ} (hR : 0 < R) : ∃ B : ℝ, 0 < B ∧ ∀ y : ℝ, ∀ T : Finset ℂ,
    (∀ u ∈ T, u ∈ closedBall (2 + y * I) (R / 3) ∧ xiF u = 0) →
      ∑ u ∈ T, (analyticOrderNatAt xiF u : ℝ) ≤ B * (1 + |y|) ^ 2 := by
  obtain ⟨A, hA, hdata⟩ := xi_data hR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨A / Real.log 2, by positivity, fun y T hT => ?_⟩
  obtain ⟨M, hM, hL⟩ := hdata y
  have hx0 : xiF (2 + y * I) ≠ 0 := fun h => by
    have := norm_xiF_two_add y
    rw [h, norm_zero] at this
    have hp := Real.pi_pos
    have hq : 0 < 2 - π ^ 2 / 6 := by nlinarith [Real.pi_lt_d2]
    have : 0 < 2 / π * (2 - π ^ 2 / 6) * Real.exp (-(π * |y / 2|) / 2) := by positivity
    linarith
  obtain ⟨S, hS, hcount, -⟩ := landau differentiable_xiF hR hx0 hM
  have hTS : T ⊆ S := fun u hu => (hS u).2 (hT u hu)
  calc ∑ u ∈ T, (analyticOrderNatAt xiF u : ℝ) ≤ ∑ u ∈ S, (analyticOrderNatAt xiF u : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hTS fun _ _ _ => Nat.cast_nonneg _
    _ ≤ Real.log (M / ‖xiF (2 + y * I)‖) / Real.log 2 := by rw [le_div_iff₀ hlog2]; exact hcount
    _ ≤ A * (1 + |y|) ^ 2 / Real.log 2 := by gcongr
    _ = A / Real.log 2 * (1 + |y|) ^ 2 := by ring

theorem xiF_two_add_ne_zero (y : ℝ) : xiF (2 + y * I) ≠ 0 := fun h => by
  have := norm_xiF_two_add y
  rw [h, norm_zero] at this
  have hp := Real.pi_pos
  have hq : 0 < 2 - π ^ 2 / 6 := by nlinarith [Real.pi_lt_d2]
  have : 0 < 2 / π * (2 - π ^ 2 / 6) * Real.exp (-(π * |y / 2|) / 2) := by positivity
  linarith

/-- **`|ξ'/ξ|` on a disc, away from the zeros.** -/
theorem logDeriv_xi_ball {R : ℝ} (hR : 0 < R) : ∃ B : ℝ, 0 < B ∧ ∀ (y δ : ℝ) (z : ℂ), 0 < δ →
    z ∈ closedBall (2 + y * I) (R / 12) → (∀ u, xiF u = 0 → δ ≤ ‖z - u‖) →
      ‖logDeriv xiF z‖ ≤ B * (1 + |y|) ^ 2 * (1 + 1 / δ) := by
  obtain ⟨A, hA, hdata⟩ := xi_data hR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨24 * (A + 1) / R + A / Real.log 2, by positivity, fun y δ z hδ hz hfar => ?_⟩
  obtain ⟨M, hM, hL⟩ := hdata y
  have h := norm_logDeriv_le differentiable_xiF hR (xiF_two_add_ne_zero y) hM hδ hz fun u _ hu => hfar u hu
  set L := Real.log (M / ‖xiF (2 + y * I)‖)
  have hW : 1 ≤ (1 + |y|) ^ 2 := by nlinarith [abs_nonneg y]
  have h1 : 24 * (L + 1) / R ≤ 24 * (A + 1) / R * (1 + |y|) ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hR]; nlinarith
  have h2 : L / (δ * Real.log 2) ≤ A / Real.log 2 * (1 + |y|) ^ 2 * (1 / δ) := by
    rw [div_le_iff₀ (by positivity)]
    have : A / Real.log 2 * (1 + |y|) ^ 2 * (1 / δ) * (δ * Real.log 2) = A * (1 + |y|) ^ 2 := by
      field_simp
    rw [this]; exact hL
  have hp1 : 0 ≤ 24 * (A + 1) / R * (1 + |y|) ^ 2 * (1 / δ) := by positivity
  have hp2 : 0 ≤ A / Real.log 2 * (1 + |y|) ^ 2 := by positivity
  have e : (24 * (A + 1) / R + A / Real.log 2) * (1 + |y|) ^ 2 * (1 + 1 / δ) =
      24 * (A + 1) / R * (1 + |y|) ^ 2 + A / Real.log 2 * (1 + |y|) ^ 2 * (1 / δ) +
        (24 * (A + 1) / R * (1 + |y|) ^ 2 * (1 / δ) + A / Real.log 2 * (1 + |y|) ^ 2) := by ring
  rw [e]
  linarith

/-- `|Λ'/Λ(z)| ≤ |ξ'/ξ(z)| + 2/r` when `|z|, |z - 1| ≥ r` and `ξ(z) ≠ 0`. -/
theorem norm_logDeriv_completed_le {z : ℂ} {r : ℝ} (hr : 0 < r) (h0 : r ≤ ‖z‖) (h1 : r ≤ ‖z - 1‖)
    (hx : xiF z ≠ 0) : ‖logDeriv completedRiemannZeta z‖ ≤ ‖logDeriv xiF z‖ + 2 / r := by
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at h0; linarith
  have hz1 : z ≠ 1 := fun h => by rw [h, sub_self, norm_zero] at h1; linarith
  rw [logDeriv_completedZeta_eq hz0 hz1 hx]
  have e1 : ‖z⁻¹‖ ≤ 1 / r := by rw [norm_inv, one_div]; exact inv_anti₀ hr h0
  have e2 : ‖(z - 1)⁻¹‖ ≤ 1 / r := by rw [norm_inv, one_div]; exact inv_anti₀ hr h1
  have := norm_sub_le (logDeriv xiF z - z⁻¹) (z - 1)⁻¹
  have := norm_sub_le (logDeriv xiF z) z⁻¹
  have e : (2 : ℝ) / r = 1 / r + 1 / r := by ring
  linarith

theorem norm_sub_le_re_im (z w : ℂ) : ‖z - w‖ ≤ |z.re - w.re| + |z.im - w.im| := by
  have := Complex.norm_le_abs_re_add_abs_im (z - w)
  simpa using this

theorem abs_im_le_norm_sub (z w : ℂ) : |z.im - w.im| ≤ ‖z - w‖ := by
  have := abs_im_le_norm (z - w); simpa using this

theorem abs_re_le_norm_sub (z w : ℂ) : |z.re - w.re| ≤ ‖z - w‖ := by
  have := abs_re_le_norm (z - w); simpa using this

/-- **`Λ'/Λ` on the two vertical lines.** For `c > 1`: `|Λ'/Λ(c + iy)|, |Λ'/Λ(1 - c + iy)| ≤ B (1 + |y|)²`. -/
theorem logDeriv_vline_bound {c : ℝ} (hc : 1 < c) : ∃ B : ℝ, 0 < B ∧ ∀ y : ℝ,
    ‖logDeriv completedRiemannZeta (c + y * I)‖ ≤ B * (1 + |y|) ^ 2 ∧
      ‖logDeriv completedRiemannZeta ((1 - c : ℝ) + y * I)‖ ≤ B * (1 + |y|) ^ 2 := by
  obtain ⟨B₀, hB₀, hb⟩ := logDeriv_xi_ball (R := 12 * (c + 2)) (by positivity)
  have hc1 : 0 < c - 1 := by linarith
  refine ⟨B₀ * (1 + 1 / (c - 1)) + 2 / (c - 1), by positivity, fun y => ?_⟩
  have hW : 1 ≤ (1 + |y|) ^ 2 := by nlinarith [abs_nonneg y]
  have key : ∀ x : ℝ, |x - 2| ≤ c + 1 → (∀ u : ℂ, 0 < u.re → u.re < 1 → c - 1 ≤ |x - u.re|) →
      c - 1 ≤ |x| → c - 1 ≤ |x - 1| →
      ‖logDeriv completedRiemannZeta (x + y * I)‖ ≤ (B₀ * (1 + 1 / (c - 1)) + 2 / (c - 1)) * (1 + |y|) ^ 2 := by
    intro x hx2 hzeros hx0 hx1
    set z : ℂ := x + y * I with hz
    have hfar : ∀ u, xiF u = 0 → c - 1 ≤ ‖z - u‖ := fun u hu => by
      obtain ⟨h1, h2⟩ := re_of_xiF_eq_zero hu
      refine (hzeros u h1 h2).trans ?_
      have := abs_re_le_norm_sub z u
      simpa [hz] using this
    have hzb : z ∈ closedBall (2 + y * I) (12 * (c + 2) / 12) := by
      rw [mem_closedBall, dist_eq_norm]
      refine (norm_sub_le_re_im _ _).trans ?_
      simp [hz]; linarith
    have hxz : xiF z ≠ 0 := fun h => by
      have := hfar z h; rw [sub_self, norm_zero] at this; linarith
    have h0 : c - 1 ≤ ‖z‖ := hx0.trans (by have := abs_re_le_norm z; simpa [hz] using this)
    have h1 : c - 1 ≤ ‖z - 1‖ := hx1.trans (by have := abs_re_le_norm (z - 1); simpa [hz] using this)
    have hl := hb y (c - 1) z hc1 hzb hfar
    have := norm_logDeriv_completed_le hc1 h0 h1 hxz
    have e : (B₀ * (1 + 1 / (c - 1)) + 2 / (c - 1)) * (1 + |y|) ^ 2 =
        B₀ * (1 + |y|) ^ 2 * (1 + 1 / (c - 1)) + 2 / (c - 1) * (1 + |y|) ^ 2 := by ring
    rw [e]
    have : 2 / (c - 1) ≤ 2 / (c - 1) * (1 + |y|) ^ 2 := le_mul_of_one_le_right (by positivity) hW
    linarith
  constructor
  · refine key c (by rw [abs_le]; constructor <;> linarith) (fun u h1 h2 => ?_) ?_ ?_
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]
  · refine key (1 - c) (by rw [abs_le]; constructor <;> linarith) (fun u h1 h2 => ?_) ?_ ?_
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_neg (by linarith)]; linarith

/-- The zeros of `ξ` in a compact set form a finite set. -/
theorem exists_zero_finset (K : Set ℂ) (hK : IsCompact K) :
    ∃ S : Finset ℂ, ∀ u, u ∈ S ↔ u ∈ K ∧ xiF u = 0 := by
  classical
  have hfin := hK.inter_riemannZetaZeros_finite
  refine ⟨hfin.toFinset.filter fun u => xiF u = 0, fun u => ?_⟩
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_inter_iff, mem_riemannZetaZeros]
  constructor
  · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h1, ((xiF_eq_zero_iff u).1 h3).2.2⟩, h3⟩

/-- **Good heights.** For `c > 1` there is `B` such that every interval `[a, a + 1]` with `a ≥ 1` or `a ≤ -2` contains a
height `T` where the segment `[1 - c, c] + iT` meets no zero and `|Λ'/Λ| ≤ B (1 + |a|)⁴` on it. -/
theorem exists_good_height {c : ℝ} (hc : 1 < c) : ∃ B : ℝ, 0 < B ∧ ∀ a : ℝ, (1 ≤ a ∨ a ≤ -2) →
    ∃ T ∈ Icc a (a + 1), ∀ σ ∈ Icc (1 - c) c, xiF (σ + T * I) ≠ 0 ∧
      ‖logDeriv completedRiemannZeta (σ + T * I)‖ ≤ B * (1 + |a|) ^ 4 := by
  classical
  set R : ℝ := 12 * (c + 2) with hR
  have hRpos : 0 < R := by positivity
  obtain ⟨B₀, hB₀, hb⟩ := logDeriv_xi_ball hRpos
  obtain ⟨B₁, hB₁, hcount⟩ := zero_count_ball hRpos
  refine ⟨12 * B₀ + 32 * B₀ * B₁ + 2, by positivity, fun a ha => ?_⟩
  set y₀ : ℝ := a + 1 / 2 with hy₀
  obtain ⟨S, hS⟩ := exists_zero_finset (closedBall (2 + y₀ * I) (R / 3)) (isCompact_closedBall _ _)
  have hcardS : (S.card : ℝ) ≤ B₁ * (1 + |y₀|) ^ 2 := by
    refine le_trans ?_ (hcount y₀ S fun u hu => (hS u).1 hu)
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun u hu => ?_
    have := analyticOrderNatAt_ne_zero differentiable_xiF (z₀ := 0) (by rw [xiF_zero]; exact one_ne_zero)
      ((hS u).1 hu).2
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  set Z := S.image Complex.im with hZ
  have hcardZ : (Z.card : ℝ) ≤ B₁ * (1 + |y₀|) ^ 2 :=
    (Nat.cast_le.2 Finset.card_image_le).trans hcardS
  obtain ⟨T, hT, hTfar⟩ := exists_far_point Z a
  set δ : ℝ := 1 / (2 * (B₁ * (1 + |y₀|) ^ 2 + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hδZ : δ ≤ 1 / (2 * (Z.card + 1)) := by
    rw [hδ]; gcongr
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]; nlinarith [mul_nonneg hB₁.le (sq_nonneg (1 + |y₀|))]
  have hT1 : 1 ≤ |T| := by
    rcases ha with ha | ha
    · rw [abs_of_pos (by linarith [hT.1])]; linarith [hT.1]
    · rw [abs_of_neg (by linarith [hT.2])]; linarith [hT.2]
  refine ⟨T, hT, fun σ hσ => ?_⟩
  set z : ℂ := σ + T * I with hz
  have hfar : ∀ u, xiF u = 0 → δ ≤ ‖z - u‖ := by
    intro u hu
    have him : |T - u.im| ≤ ‖z - u‖ := by have := abs_im_le_norm_sub z u; simpa [hz] using this
    by_cases h : 1 ≤ |T - u.im|
    · linarith
    · push Not at h
      have huS : u ∈ S := by
        refine (hS u).2 ⟨?_, hu⟩
        rw [mem_closedBall, dist_eq_norm]
        refine (norm_sub_le_re_im _ _).trans ?_
        obtain ⟨h1, h2⟩ := re_of_xiF_eq_zero hu
        have hy : |u.im - y₀| ≤ 3 / 2 := by
          rw [abs_lt] at h; rw [abs_le]; constructor <;> linarith [hT.1, hT.2]
        have e1 : u.re - (2 + (y₀ : ℂ) * I).re = u.re - 2 := by simp
        have e2 : u.im - (2 + (y₀ : ℂ) * I).im = u.im - y₀ := by simp
        rw [e1, e2, abs_of_neg (by linarith), hR]
        linarith
      have := hTfar u.im (Finset.mem_image_of_mem _ huS)
      linarith
  have hxz : xiF z ≠ 0 := fun h => by
    have := hfar z h; rw [sub_self, norm_zero] at this; linarith
  refine ⟨hxz, ?_⟩
  have hzb : z ∈ closedBall (2 + y₀ * I) (R / 12) := by
    rw [mem_closedBall, dist_eq_norm]
    refine (norm_sub_le_re_im _ _).trans ?_
    have e1 : z.re - (2 + (y₀ : ℂ) * I).re = σ - 2 := by simp [hz]
    have e2 : z.im - (2 + (y₀ : ℂ) * I).im = T - y₀ := by simp [hz]
    have h1 : |σ - 2| ≤ c + 1 := by rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2]
    have h2 : |T - y₀| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hT.1, hT.2]
    rw [e1, e2, hR]; linarith
  have h0 : 1 ≤ ‖z‖ := hT1.trans (by have := abs_im_le_norm z; simpa [hz] using this)
  have h1 : 1 ≤ ‖z - 1‖ := hT1.trans (by have := abs_im_le_norm (z - 1); simpa [hz] using this)
  have hl := hb y₀ δ z hδpos hzb hfar
  have hc2 := norm_logDeriv_completed_le one_pos h0 h1 hxz
  have hya : 1 + |y₀| ≤ 2 * (1 + |a|) := by
    have := abs_add_le a (1 / 2)
    rw [hy₀]
    have e : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    rw [e] at this
    linarith [abs_nonneg a]
  set W := (1 + |a|) ^ 2 with hWdef
  have hW : 1 ≤ W := by nlinarith [abs_nonneg a]
  have hX : (1 + |y₀|) ^ 2 ≤ 4 * W := by
    rw [hWdef]; nlinarith [abs_nonneg y₀, abs_nonneg a]
  have hX0 : 0 ≤ (1 + |y₀|) ^ 2 := sq_nonneg _
  have hinv : 1 / δ = 2 * (B₁ * (1 + |y₀|) ^ 2 + 1) := by rw [hδ, one_div_one_div]
  rw [hinv] at hl
  have hfin : B₀ * (1 + |y₀|) ^ 2 * (1 + 2 * (B₁ * (1 + |y₀|) ^ 2 + 1)) ≤ (12 * B₀ + 32 * B₀ * B₁) * W ^ 2 := by
    have e : B₀ * (1 + |y₀|) ^ 2 * (1 + 2 * (B₁ * (1 + |y₀|) ^ 2 + 1)) =
        3 * B₀ * (1 + |y₀|) ^ 2 + 2 * B₀ * B₁ * ((1 + |y₀|) ^ 2) ^ 2 := by ring
    rw [e]
    have hX2 : ((1 + |y₀|) ^ 2) ^ 2 ≤ 16 * W ^ 2 := by nlinarith
    have hWW : W ≤ W ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hX hB₀.le, mul_le_mul_of_nonneg_left hX2 (mul_pos hB₀ hB₁).le]
  have : (1 + |a|) ^ 4 = W ^ 2 := by rw [hWdef]; ring
  rw [this]
  nlinarith

/-- **The zero count per unit window.** The zeros of `ξ` with `|Im ρ - y| ≤ 1`, counted with multiplicity, number at most
`B (1 + |y|)²`. -/
theorem zero_count_window : ∃ B : ℝ, 0 < B ∧ ∀ y : ℝ, ∀ T : Finset ℂ,
    (∀ u ∈ T, xiF u = 0 ∧ |u.im - y| ≤ 1) → ∑ u ∈ T, (analyticOrderNatAt xiF u : ℝ) ≤ B * (1 + |y|) ^ 2 := by
  obtain ⟨B, hB, hcount⟩ := zero_count_ball (R := 12) (by norm_num)
  refine ⟨B, hB, fun y T hT => hcount y T fun u hu => ⟨?_, (hT u hu).1⟩⟩
  rw [mem_closedBall, dist_eq_norm]
  refine (norm_sub_le_re_im _ _).trans ?_
  obtain ⟨h1, h2⟩ := re_of_xiF_eq_zero (hT u hu).1
  have h3 := (hT u hu).2
  simp only [add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero, add_im,
    im_ofNat, zero_add]
  rw [abs_of_neg (by linarith)]
  norm_num
  linarith

end ProofPhase.GRH.CS
