/-
The explicit formula, layer (a): the prime side and the real place, from Mathlib's pieces (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/EXPLICIT-FORMULA.md`, section 2.
-/

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv
import Mathlib.Analysis.Fourier.Inversion

/-!
# The explicit formula, layer (a): the prime side on a vertical line, and the completed log-derivative

**What Mathlib has** (Mathlib v4.34.0, checked before writing):
* `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`: `L(Λ, s) = -ζ'(s)/ζ(s)` for `Re s > 1`;
* `logDeriv_riemannZeta_one_sub`: the functional equation of `ζ'/ζ` with the digamma function;
* `completedRiemannZeta_one_sub`, `riemannZeta_def_of_ne_zero`, `Gammaℝ_def`: the completed zeta `Λ(s) = Γ_ℝ(s) ζ(s)`,
  `Γ_ℝ(s) = π^{-s/2} Γ(s/2)`, and `Λ(1 - s) = Λ(s)`;
* `MeasureTheory.Integrable.fourierInv_fourier_eq`: Fourier inversion; `integral_tsum_of_summable_integral_norm`: Fubini
  for a sum and an integral.

**What is proved here.**
* `neg_logDeriv_zeta`: `-ζ'/ζ = L(Λ, ·)` on `Re s > 1`, in `logDeriv` form.
* `logDeriv_Gammaℝ`: `Γ_ℝ'/Γ_ℝ (s) = -(log π)/2 + ψ(s/2)/2` for `Re s > 0` (the real place).
* `logDeriv_completedZeta`: `Λ'/Λ = ζ'/ζ + Γ_ℝ'/Γ_ℝ` on `Re s > 1`.
* `logDeriv_completedZeta_one_sub`: `Λ'/Λ (1 - s) = -Λ'/Λ (s)` for `s ≠ 0, 1` (the functional equation, differentiated).
* **`lineIntegral_LSeries_vonMangoldt`** (the prime side as a line integral): for `c > 1` and a continuous integrable `φ`
  with integrable Fourier transform `𝓕 φ`,
  `∫ L(Λ, c - 2πiτ) 𝓕φ(τ) dτ = ∑ₙ Λ(n) n^{-c} φ(log n)`.
* **`lineIntegral_primeSide`**: the same in the explicit formula's normalisation, `φ(x) = g(x) e^{(c - 1/2) x}`: the right
  side becomes `∑ₙ Λ(n) n^{-1/2} g(log n)`, independent of `c`.

Standard axioms only.
-/

open Complex MeasureTheory FourierTransform
open scoped Real

noncomputable section

namespace ProofPhase.GRH.EF

/-- The von Mangoldt function as a complex sequence (Mathlib's `↗Λ`). -/
abbrev vM : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)

/-! ### 1. Log-derivatives: zeta, the real place, the completed zeta -/

/-- `-ζ'/ζ = L(Λ, ·)` on `Re s > 1` (Mathlib's statement in `logDeriv` form). -/
theorem neg_logDeriv_zeta {s : ℂ} (hs : 1 < s.re) : -logDeriv riemannZeta s = LSeries vM s := by
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, logDeriv_apply, neg_div]

theorem Gammaℝ_eq : Gammaℝ = fun s : ℂ => (π : ℂ) ^ (-s / 2) * Gamma (s / 2) := by
  funext s; exact Gammaℝ_def s

theorem differentiableAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℝ s := by
  rw [Gammaℝ_eq]
  refine DifferentiableAt.mul ?_ ?_
  · exact ((differentiableAt_id.neg).div_const 2).const_cpow (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  · refine (differentiableAt_Gamma _ fun m hm => ?_).comp s (differentiableAt_id.div_const 2)
    have := congrArg Complex.re hm
    simp only [Complex.div_re, Complex.neg_re, Complex.natCast_re] at this
    norm_num at this
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- **The real place.** `Γ_ℝ'/Γ_ℝ (s) = -(log π)/2 + ψ(s/2)/2` for `Re s > 0`, `ψ` the digamma function. -/
theorem logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Gammaℝ s = -Complex.log π / 2 + digamma (s / 2) / 2 := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs2 : 0 < (s / 2).re := by simp; linarith
  have hG : Gamma (s / 2) ≠ 0 := Gamma_ne_zero_of_re_pos hs2
  have hGd : DifferentiableAt ℂ Gamma (s / 2) := by
    refine differentiableAt_Gamma _ fun m hm => ?_
    have := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at this
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h1 : HasDerivAt (fun z : ℂ => (π : ℂ) ^ (-z / 2)) ((π : ℂ) ^ (-s / 2) * Complex.log π * (-1 / 2)) s := by
    have := ((hasDerivAt_id s).neg.div_const 2).const_cpow (c := (π : ℂ)) (Or.inl hpi)
    simpa [id, neg_div] using this
  have h2 : HasDerivAt (fun z : ℂ => Gamma (z / 2)) (deriv Gamma (s / 2) * (1 / 2)) s :=
    hGd.hasDerivAt.comp s ((hasDerivAt_id' s).div_const 2)
  have hD : HasDerivAt (fun z : ℂ => (π : ℂ) ^ (-z / 2) * Gamma (z / 2))
      ((π : ℂ) ^ (-s / 2) * Complex.log π * (-1 / 2) * Gamma (s / 2) +
        (π : ℂ) ^ (-s / 2) * (deriv Gamma (s / 2) * (1 / 2))) s := h1.mul h2
  rw [logDeriv_apply, Gammaℝ_eq, hD.deriv, digamma_def, logDeriv_apply]
  have hc : (π : ℂ) ^ (-s / 2) ≠ 0 := by rw [cpow_def_of_ne_zero hpi]; exact Complex.exp_ne_zero _
  field_simp

/-- **The completed zeta.** `Λ'/Λ = ζ'/ζ + Γ_ℝ'/Γ_ℝ` on `Re s > 1` (where neither factor vanishes). -/
theorem logDeriv_completedZeta {s : ℂ} (hs : 1 < s.re) :
    logDeriv completedRiemannZeta s = logDeriv riemannZeta s + logDeriv Gammaℝ s := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := fun h => by simp [h] at hs
  have hev : completedRiemannZeta =ᶠ[nhds s] fun z => Gammaℝ z * riemannZeta z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs0] with z hz
    have hz0 : z ≠ 0 := fun h => by simp [h] at hz
    rw [riemannZeta_def_of_ne_zero hz0]
    field_simp [Gammaℝ_ne_zero_of_re_pos hz]
  rw [(logDeriv_congr_nhds hev).eq_of_nhds, logDeriv_fun_mul s (Gammaℝ_ne_zero_of_re_pos hs0)
    (riemannZeta_ne_zero_of_one_le_re hs.le) (differentiableAt_Gammaℝ hs0) (differentiableAt_riemannZeta hs1),
    add_comm]

/-- **The functional equation, differentiated.** `Λ'/Λ (1 - s) = -Λ'/Λ (s)` for `s ≠ 0, 1`. -/
theorem logDeriv_completedZeta_one_sub {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv completedRiemannZeta (1 - s) = -logDeriv completedRiemannZeta s := by
  have h0 : 1 - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
  have h1 : 1 - s ≠ 1 := by intro h; apply hs0; linear_combination -h
  have hd : HasDerivAt (fun z => completedRiemannZeta (1 - z)) (deriv completedRiemannZeta (1 - s) * (-1)) s :=
    (differentiableAt_completedZeta h0 h1).hasDerivAt.comp s ((hasDerivAt_id' s).const_sub 1)
  have hfun : (fun z => completedRiemannZeta (1 - z)) = completedRiemannZeta :=
    funext completedRiemannZeta_one_sub
  rw [hfun] at hd
  rw [logDeriv_apply, logDeriv_apply, completedRiemannZeta_one_sub, hd.deriv]
  ring

/-! ### 2. The prime side as a line integral -/

/-- The vertical line `Re s = c`, parametrised in Mathlib's Fourier convention: `s(τ) = c - 2π i τ`. With this
parametrisation `∫ f(s(τ)) dτ = (1/2πi) ∫_{(c)} f(s) ds`. -/
def vpt (c τ : ℝ) : ℂ := c - 2 * π * I * τ

@[simp] theorem vpt_re (c τ : ℝ) : (vpt c τ).re = c := by simp [vpt]

/-- The weight `Λ(n) n^{-c}` (real, nonnegative). -/
def aw (c : ℝ) (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c)

/-- The phase `n^{2π i τ}`, written as Mathlib's Fourier character at `-log n`. -/
def ew (τ : ℝ) (n : ℕ) : ℂ := Complex.exp (↑(-2 * π * τ * -Real.log n) * I)

theorem aw_nonneg (c : ℝ) (n : ℕ) : 0 ≤ aw c n :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem norm_ew (τ : ℝ) (n : ℕ) : ‖ew τ n‖ = 1 := Complex.norm_exp_ofReal_mul_I _

/-- The terms of `L(Λ, s)` on the line `Re s = c`: `Λ(n) n^{-c} · n^{2π i τ}`. -/
theorem term_vM_vpt (c τ : ℝ) (n : ℕ) : LSeries.term vM (vpt c τ) n = (aw c n : ℂ) * ew τ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [aw]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg _), Complex.ofReal_natCast]
  rw [LSeries.term_of_ne_zero hn, cpow_def_of_ne_zero (Nat.cast_ne_zero.2 hn), hlog, aw, ew,
    Real.rpow_def_of_pos hn', div_eq_mul_inv, ← Complex.exp_neg]
  push_cast
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [vpt]
  ring

theorem summable_aw {c : ℝ} (hc : 1 < c) : Summable (aw c) := by
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (c : ℂ)) (by simpa using hc)
  have heq : ∀ n, LSeries.term vM (c : ℂ) n = ((aw c n : ℝ) : ℂ) := fun n => by
    have := term_vM_vpt c 0 n
    simpa [vpt, ew] using this
  have h' : Summable fun n => ((aw c n : ℝ) : ℂ) := h.congr heq
  exact Complex.summable_ofReal.mp h'

/-- `L(Λ, ·)` on the line `Re s = c`, as a sum of phases. -/
theorem LSeries_vM_vpt (c τ : ℝ) : LSeries vM (vpt c τ) = ∑' n, (aw c n : ℂ) * ew τ n := by
  rw [LSeries]
  exact tsum_congr fun n => term_vM_vpt c τ n

theorem continuous_ew (n : ℕ) : Continuous fun τ : ℝ => ew τ n := by
  unfold ew; fun_prop

theorem norm_aw_ew (c τ : ℝ) (n : ℕ) : ‖(aw c n : ℂ) * ew τ n‖ = aw c n := by
  rw [norm_mul, norm_ew, mul_one, Complex.norm_real, Real.norm_of_nonneg (aw_nonneg c n)]

/-- `τ ↦ L(Λ, c - 2πiτ)` is continuous for `c > 1`. -/
theorem continuous_LSeries_vM_vpt {c : ℝ} (hc : 1 < c) : Continuous fun τ : ℝ => LSeries vM (vpt c τ) := by
  simp_rw [LSeries_vM_vpt]
  exact continuous_tsum (fun n => continuous_const.mul (continuous_ew n)) (summable_aw hc)
    fun n τ => le_of_eq (norm_aw_ew c τ n)

/-- `L(Λ, ·)` is bounded on the line `Re s = c > 1` by `∑ Λ(n) n^{-c}`. -/
theorem norm_LSeries_vM_vpt_le {c : ℝ} (hc : 1 < c) (τ : ℝ) : ‖LSeries vM (vpt c τ)‖ ≤ ∑' n, aw c n := by
  rw [LSeries_vM_vpt]
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · exact (summable_aw hc).congr fun n => (norm_aw_ew c τ n).symm
  · exact tsum_congr fun n => norm_aw_ew c τ n

/-- **The prime side as a line integral.** For `c > 1` and a continuous integrable `φ` whose Fourier transform is
integrable: `∫ L(Λ, c - 2πiτ) 𝓕φ(τ) dτ = ∑ₙ Λ(n) n^{-c} φ(log n)`. (Fourier inversion termwise, and Fubini for the sum
and the integral; the sum converges absolutely.) -/
theorem lineIntegral_LSeries_vonMangoldt {c : ℝ} (hc : 1 < c) {φ : ℝ → ℂ} (hφc : Continuous φ)
    (hφ : Integrable φ) (hFφ : Integrable (𝓕 φ)) :
    ∫ τ : ℝ, LSeries vM (vpt c τ) * 𝓕 φ τ = ∑' n : ℕ, (aw c n : ℂ) * φ (Real.log n) := by
  have hinv : ∀ n : ℕ, ∫ τ : ℝ, ew τ n * 𝓕 φ τ = φ (Real.log n) := by
    intro n
    have h := hφ.fourierInv_fourier_eq hFφ (hφc.continuousAt (x := Real.log n))
    rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at h
    simpa only [ew, smul_eq_mul] using h
  have hint0 : ∀ n, Integrable (fun τ : ℝ => ew τ n * 𝓕 φ τ) := fun n =>
    hFφ.norm.mono' ((continuous_ew n).aestronglyMeasurable.mul hFφ.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun τ => le_of_eq (by rw [norm_mul, norm_ew, one_mul]))
  have hint : ∀ n, Integrable (fun τ : ℝ => (aw c n : ℂ) * (ew τ n * 𝓕 φ τ)) := fun n =>
    (hint0 n).const_mul _
  have hsum : Summable fun n => ∫ τ : ℝ, ‖(aw c n : ℂ) * (ew τ n * 𝓕 φ τ)‖ := by
    have h : ∀ n, ∫ τ : ℝ, ‖(aw c n : ℂ) * (ew τ n * 𝓕 φ τ)‖ = aw c n * ∫ τ : ℝ, ‖𝓕 φ τ‖ := fun n => by
      simp_rw [norm_mul, norm_ew, one_mul, Complex.norm_real, Real.norm_of_nonneg (aw_nonneg c n)]
      exact integral_const_mul _ _
    simp_rw [h]
    exact (summable_aw hc).mul_right _
  calc ∫ τ : ℝ, LSeries vM (vpt c τ) * 𝓕 φ τ
      = ∫ τ : ℝ, ∑' n, (aw c n : ℂ) * (ew τ n * 𝓕 φ τ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
        simp only
        rw [LSeries_vM_vpt, ← tsum_mul_right]
        exact tsum_congr fun n => by ring
    _ = ∑' n, ∫ τ : ℝ, (aw c n : ℂ) * (ew τ n * 𝓕 φ τ) :=
        (integral_tsum_of_summable_integral_norm hint hsum).symm
    _ = ∑' n : ℕ, (aw c n : ℂ) * φ (Real.log n) :=
        tsum_congr fun n => by rw [integral_const_mul, hinv]

/-- The prime weight of the explicit formula, `Λ(n) n^{-1/2}`. -/
def pw (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2 : ℝ))

/-- The test function in log scale, tilted to the line `Re s = c`: `φ_c(x) = g(x) e^{(c - 1/2) x}`. -/
def tilt (c : ℝ) (g : ℝ → ℂ) : ℝ → ℂ := fun x => g x * Complex.exp (((c - 1 / 2 : ℝ) : ℂ) * x)

theorem continuous_tilt (c : ℝ) {g : ℝ → ℂ} (hg : Continuous g) : Continuous (tilt c g) := by
  unfold tilt; fun_prop

theorem integrable_tilt (c : ℝ) {g : ℝ → ℂ} (hg : Continuous g) (hgs : HasCompactSupport g) :
    Integrable (tilt c g) :=
  (continuous_tilt c hg).integrable_of_hasCompactSupport hgs.mul_right

/-- **The prime side of the explicit formula as a line integral.** For `c > 1`, `g` continuous with compact support (the
test function in log scale), and `𝓕 φ_c` integrable: `∫ L(Λ, c - 2πiτ) 𝓕φ_c(τ) dτ = ∑ₙ Λ(n) n^{-1/2} g(log n)`. The
right side does not depend on `c`. -/
theorem lineIntegral_primeSide {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hF : Integrable (𝓕 (tilt c g))) :
    ∫ τ : ℝ, LSeries vM (vpt c τ) * 𝓕 (tilt c g) τ = ∑' n : ℕ, (pw n : ℂ) * g (Real.log n) := by
  rw [lineIntegral_LSeries_vonMangoldt hc (continuous_tilt c hg) (integrable_tilt c hg hgs) hF]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [aw, pw]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have key : (n : ℝ) ^ (-c) * Real.exp ((c - 1 / 2) * Real.log n) = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [mul_comm (c - 1 / 2), ← Real.rpow_def_of_pos hn', ← Real.rpow_add hn']
    ring_nf
  calc (aw c n : ℂ) * tilt c g (Real.log n)
      = ((ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ (-c) * Real.exp ((c - 1 / 2) * Real.log n)) : ℝ) : ℂ) *
          g (Real.log n) := by
        simp only [aw, tilt]
        push_cast
        ring
    _ = (pw n : ℂ) * g (Real.log n) := by rw [key, pw]

end ProofPhase.GRH.EF
