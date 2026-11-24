/-
The contour shift, test functions: the transform `H` of a smooth compactly supported test function is entire and decays
faster than any power in vertical strips (2026-11-24). Released under Apache 2.0.

Paper: `docs/unified/CONTOUR-SHIFT.md`, section 6.
-/

import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# The transform of a test function: entire, and rapidly decreasing in vertical strips

For `g : ℝ → ℂ` continuous with compact support, `H(s) = ∫ g(x) e^{(s - 1/2) x} dx` (`laplace`; the same
definition as `EF.laplace` in `ExplicitFormula.lean`, repeated so that this file needs only Mathlib).

* `differentiable_laplace`: `H` is entire (differentiation under the integral sign; the support is compact).
* `norm_laplace_le`: `|H(s)| ≤ ∫ |g(x)| e^{K|x|} dx` on the strip `|Re s - 1/2| ≤ K`.
* `laplace_deriv`: `(s - 1/2) H_g(s) = -H_{g'}(s)` (integration by parts on the line), and by induction
  `laplace_iteratedDeriv`: `(s - 1/2)^k H_g(s) = (-1)^k H_{g^{(k)}}(s)` for `g` smooth.
* **`laplace_decay`**: for `g` smooth with compact support, every `k` and every strip `|Re s - 1/2| ≤ K`:
  `|H(s)| (1 + |Im s|)^k ≤ C(k, K)`.

Standard axioms only.
-/

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

noncomputable section

namespace ProofPhase.GRH.CS

/-- The transform of a test function in log scale, `H(s) = ∫ g(x) e^{(s - 1/2) x} dx`. -/
def laplace (g : ℝ → ℂ) (s : ℂ) : ℂ := ∫ x : ℝ, g x * Complex.exp ((s - 1 / 2) * x)

theorem norm_cexp_mul_le (w : ℂ) (x : ℝ) {K : ℝ} (hK : |w.re| ≤ K) : ‖Complex.exp (w * x)‖ ≤ Real.exp (K * |x|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have : (w * (x : ℂ)).re = w.re * x := by simp
  rw [this]
  calc w.re * x ≤ |w.re * x| := le_abs_self _
    _ = |w.re| * |x| := abs_mul _ _
    _ ≤ K * |x| := mul_le_mul_of_nonneg_right hK (abs_nonneg x)

theorem integrable_mul_cexp {h : ℝ → ℂ} (hc : Continuous h) (hs : HasCompactSupport h) (w : ℂ) :
    Integrable (fun x : ℝ => h x * Complex.exp (w * x)) :=
  (hc.mul (by fun_prop)).integrable_of_hasCompactSupport hs.mul_right

theorem integrable_norm_mul_exp {h : ℝ → ℂ} (hc : Continuous h) (hs : HasCompactSupport h) (K : ℝ) :
    Integrable (fun x : ℝ => ‖h x‖ * Real.exp (K * |x|)) :=
  ((by fun_prop : Continuous fun x : ℝ => ‖h x‖ * Real.exp (K * |x|))).integrable_of_hasCompactSupport
    hs.norm.mul_right

/-- `|H(s)| ≤ ∫ |g| e^{K|x|}` on the strip `|Re s - 1/2| ≤ K`. -/
theorem norm_laplace_le {h : ℝ → ℂ} (hc : Continuous h) (hs : HasCompactSupport h) {K : ℝ} {s : ℂ}
    (hK : |s.re - 1 / 2| ≤ K) : ‖laplace h s‖ ≤ ∫ x, ‖h x‖ * Real.exp (K * |x|) := by
  refine norm_integral_le_of_norm_le (integrable_norm_mul_exp hc hs K) (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  gcongr
  exact norm_cexp_mul_le _ _ (by simpa using hK)

/-- **`H` is entire.** -/
theorem differentiable_laplace {g : ℝ → ℂ} (hg : Continuous g) (hgs : HasCompactSupport g) :
    Differentiable ℂ (laplace g) := by
  intro s₀
  set K := |s₀.re - 1 / 2| + 1 with hK
  have hb : Integrable (fun x : ℝ => ‖g x‖ * (|x| * Real.exp (K * |x|))) :=
    ((by fun_prop : Continuous fun x : ℝ => ‖g x‖ * (|x| * Real.exp (K * |x|)))).integrable_of_hasCompactSupport
      hgs.norm.mul_right
  have hbound : ∀ x : ℝ, ∀ s ∈ ball s₀ 1,
      ‖g x * ((x : ℂ) * Complex.exp ((s - 1 / 2) * x))‖ ≤ ‖g x‖ * (|x| * Real.exp (K * |x|)) := by
    intro x s hs
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    refine norm_cexp_mul_le _ _ ?_
    have h1 : |s.re - s₀.re| ≤ 1 := by
      have h2 : ‖s - s₀‖ < 1 := mem_ball_iff_norm.1 hs
      have h3 : |(s - s₀).re| ≤ ‖s - s₀‖ := abs_re_le_norm _
      have h4 : (s - s₀).re = s.re - s₀.re := by simp
      rw [h4] at h3
      linarith
    have h5 : (s - 1 / 2).re = s.re - 1 / 2 := by simp
    rw [h5, hK]
    have h6 : |s.re - 1 / 2| ≤ |s.re - s₀.re| + |s₀.re - 1 / 2| := by
      have := abs_add_le (s.re - s₀.re) (s₀.re - 1 / 2)
      have e : s.re - s₀.re + (s₀.re - 1 / 2) = s.re - 1 / 2 := by ring
      rwa [e] at this
    linarith
  have hdiff : ∀ x : ℝ, ∀ s ∈ ball s₀ 1, HasDerivAt (fun s : ℂ => g x * Complex.exp ((s - 1 / 2) * x))
      (g x * ((x : ℂ) * Complex.exp ((s - 1 / 2) * x))) s := by
    intro x s _
    have h := (((hasDerivAt_id' s).sub_const (1 / 2 : ℂ)).mul_const (x : ℂ)).cexp.const_mul (g x)
    convert h using 1
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := s₀)
    (F := fun s x => g x * Complex.exp ((s - 1 / 2) * x))
    (F' := fun s x => g x * ((x : ℂ) * Complex.exp ((s - 1 / 2) * x)))
    (bound := fun x => ‖g x‖ * (|x| * Real.exp (K * |x|))) (ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s => (integrable_mul_cexp hg hgs (s - 1 / 2)).aestronglyMeasurable)
    (integrable_mul_cexp hg hgs (s₀ - 1 / 2))
    ((hg.mul (by fun_prop)).aestronglyMeasurable)
    (ae_of_all _ hbound) hb (ae_of_all _ hdiff)
  exact key.2.differentiableAt

/-- **Integration by parts.** `(s - 1/2) H_h(s) = -H_{h'}(s)` for `h` differentiable with continuous derivative and
compact support. -/
theorem laplace_deriv {h : ℝ → ℂ} (hd : Differentiable ℝ h) (hc' : Continuous (deriv h)) (hs : HasCompactSupport h)
    (s : ℂ) : (s - 1 / 2) * laplace h s = -laplace (deriv h) s := by
  set w := s - 1 / 2 with hw
  have hu : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.exp (w * x)) (w * Complex.exp (w * x)) x := fun x => by
    have := ((hasDerivAt_id (x : ℂ)).const_mul w).cexp.comp_ofReal
    simp only [id, mul_one] at this
    convert this using 1
    ring
  have hs' : HasCompactSupport (deriv h) := hs.deriv
  have i1 : Integrable ((fun x : ℝ => Complex.exp (w * x)) * deriv h) := by
    have := integrable_mul_cexp hc' hs' w
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp [mul_comm]
  have i2 : Integrable ((fun x : ℝ => w * Complex.exp (w * x)) * h) := by
    have := (integrable_mul_cexp hd.continuous hs w).const_mul w
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]
    ring
  have i3 : Integrable ((fun x : ℝ => Complex.exp (w * x)) * h) := by
    have := integrable_mul_cexp hd.continuous hs w
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp [mul_comm]
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hu x) (fun x _ => (hd x).hasDerivAt)
    i1 i2 i3
  unfold laplace
  rw [← hw, ← integral_const_mul]
  have e1 : ∫ x : ℝ, w * (h x * Complex.exp (w * x)) = ∫ x : ℝ, w * Complex.exp (w * x) * h x :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
  have e2 : ∫ x : ℝ, deriv h x * Complex.exp (w * x) = ∫ x : ℝ, Complex.exp (w * x) * deriv h x :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [e1, e2, key, neg_neg]

theorem hasCompactSupport_iteratedDeriv {g : ℝ → ℂ} (hgs : HasCompactSupport g) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k g) := by
  induction k with
  | zero => simpa using hgs
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- `(s - 1/2)^k H_g(s) = (-1)^k H_{g^{(k)}}(s)` for `g` smooth with compact support. -/
theorem laplace_iteratedDeriv {g : ℝ → ℂ} (hg : ∀ k : ℕ, ContDiff ℝ k g) (hgs : HasCompactSupport g) (k : ℕ)
    (s : ℂ) : (s - 1 / 2) ^ k * laplace g s = (-1) ^ k * laplace (iteratedDeriv k g) s := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hd : Differentiable ℝ (iteratedDeriv k g) := (hg (k + 1)).differentiable_iteratedDeriv' k
    have hc : Continuous (deriv (iteratedDeriv k g)) := by
      rw [← iteratedDeriv_succ]; exact (hg (k + 1)).continuous_iteratedDeriv' (k + 1)
    have h1 := laplace_deriv hd hc (hasCompactSupport_iteratedDeriv hgs k) s
    rw [pow_succ, mul_comm ((s - 1 / 2) ^ k), mul_assoc, ih, iteratedDeriv_succ]
    calc (s - 1 / 2) * ((-1) ^ k * laplace (iteratedDeriv k g) s)
        = (-1) ^ k * ((s - 1 / 2) * laplace (iteratedDeriv k g) s) := by ring
      _ = (-1) ^ (k + 1) * laplace (deriv (iteratedDeriv k g)) s := by rw [h1]; ring

theorem one_add_pow_le (t : ℝ) (ht : 0 ≤ t) (k : ℕ) : (1 + t) ^ k ≤ 2 ^ k * (1 + t ^ k) := by
  rcases le_total t 1 with h | h
  · calc (1 + t) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ ≤ 2 ^ k * (1 + t ^ k) := le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg ht k])
  · calc (1 + t) ^ k ≤ (2 * t) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ = 2 ^ k * t ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (1 + t ^ k) := by gcongr; linarith

/-- **Rapid decay.** For `g` smooth with compact support, every `k` and every strip `|Re s - 1/2| ≤ K`:
`|H(s)| (1 + |Im s|)^k ≤ C`. -/
theorem laplace_decay {g : ℝ → ℂ} (hg : ∀ k : ℕ, ContDiff ℝ k g) (hgs : HasCompactSupport g) (k : ℕ) (K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, |s.re - 1 / 2| ≤ K → ‖laplace g s‖ * (1 + |s.im|) ^ k ≤ C := by
  have hc0 : Continuous g := (hg 0).continuous
  have hck : Continuous (iteratedDeriv k g) := (hg k).continuous_iteratedDeriv' k
  set C₀ := ∫ x, ‖g x‖ * Real.exp (K * |x|)
  set Ck := ∫ x, ‖iteratedDeriv k g x‖ * Real.exp (K * |x|)
  have hC₀ : 0 ≤ C₀ := integral_nonneg fun x => by positivity
  have hCk : 0 ≤ Ck := integral_nonneg fun x => by positivity
  refine ⟨2 ^ k * (C₀ + Ck), by positivity, fun s hs => ?_⟩
  have h0 : ‖laplace g s‖ ≤ C₀ := norm_laplace_le hc0 hgs hs
  have h1 : ‖laplace g s‖ * ‖s - 1 / 2‖ ^ k ≤ Ck := by
    have := congrArg norm (laplace_iteratedDeriv hg hgs k s)
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul, mul_comm] at this
    rw [this]
    exact norm_laplace_le hck (hasCompactSupport_iteratedDeriv hgs k) hs
  have him : |s.im| ≤ ‖s - 1 / 2‖ := by
    have := abs_im_le_norm (s - 1 / 2); simpa using this
  calc ‖laplace g s‖ * (1 + |s.im|) ^ k ≤ ‖laplace g s‖ * (2 ^ k * (1 + ‖s - 1 / 2‖ ^ k)) := by
        gcongr
        exact (pow_le_pow_left₀ (by positivity) (by linarith) k).trans (one_add_pow_le _ (norm_nonneg _) k)
    _ = 2 ^ k * (‖laplace g s‖ + ‖laplace g s‖ * ‖s - 1 / 2‖ ^ k) := by ring
    _ ≤ 2 ^ k * (C₀ + Ck) := by gcongr

end ProofPhase.GRH.CS
