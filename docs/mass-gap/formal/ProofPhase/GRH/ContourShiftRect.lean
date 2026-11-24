/-
The contour shift, layer (a): the residue theorem on rectangles in the form the explicit formula needs (2026-11-24).
Released under Apache 2.0.

Paper: `docs/unified/CONTOUR-SHIFT.md`, section 3.
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Rectangles: the integral of `1/(s - a)`, Cauchy's formula, and the argument principle

Mathlib has Cauchy's theorem on rectangles (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`, and the
version off a countable set) but no residue theorem. This file adds the pieces the contour shift needs.

* `rectInt f z w`: the counterclockwise integral of `f` around the rectangle with corners `z` (bottom left) and `w`
  (top right), in exactly the four-sided form of Mathlib's Cauchy theorem.
* `rectInt_inv_sub`: `∮ (s - a)⁻¹ ds = 2πi` for `a` strictly inside (four principal logarithms, the argument jumps by
  `π` twice on the left side).
* `rectInt_div_sub`: Cauchy's formula `∮ H(s)/(s - a) ds = 2πi H(a)` for `H` entire (subtract the removable part,
  `dslope`).
* `exists_factor`: an entire function that is not identically zero is, on a compact convex set `K`, a polynomial with
  its zeros in `K` (with multiplicity, the divisor of `F` on `K`) times an analytic function without zeros on `K`
  (Mathlib's `MeromorphicOn.extract_zeros_poles`, made pointwise by the identity theorem).
* **`rectInt_logDeriv_mul`** (the argument principle with a weight): for `F` entire with no zero on the boundary and
  `H` entire, `∮ (F'/F)·H = 2πi ∑_ρ ord_ρ(F) H(ρ)`, the sum over the zeros inside.

Standard axioms only.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

namespace ProofPhase.GRH.CS

/-! ### 1. The rectangle integral -/

/-- The counterclockwise integral of `f` around the rectangle with corners `z` and `w` (Mathlib's four-sided form). -/
def rectInt (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-- The boundary of the rectangle with corners `z` and `w`. -/
def rectBorder (z w : ℂ) : Set ℂ :=
  ([[z.re, w.re]] ×ℂ {z.im, w.im}) ∪ ({z.re, w.re} ×ℂ [[z.im, w.im]])

theorem mem_border_bot {z w : ℂ} {x : ℝ} (hx : x ∈ [[z.re, w.re]]) : (x + z.im * I : ℂ) ∈ rectBorder z w :=
  Or.inl ⟨by simpa using hx, by simp⟩

theorem mem_border_top {z w : ℂ} {x : ℝ} (hx : x ∈ [[z.re, w.re]]) : (x + w.im * I : ℂ) ∈ rectBorder z w :=
  Or.inl ⟨by simpa using hx, by simp⟩

theorem mem_border_right {z w : ℂ} {y : ℝ} (hy : y ∈ [[z.im, w.im]]) : (w.re + y * I : ℂ) ∈ rectBorder z w :=
  Or.inr ⟨by simp, by simpa using hy⟩

theorem mem_border_left {z w : ℂ} {y : ℝ} (hy : y ∈ [[z.im, w.im]]) : (z.re + y * I : ℂ) ∈ rectBorder z w :=
  Or.inr ⟨by simp, by simpa using hy⟩

theorem rectBorder_subset {z w : ℂ} : rectBorder z w ⊆ [[z.re, w.re]] ×ℂ [[z.im, w.im]] := by
  rintro s (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · refine ⟨h1, ?_⟩
    have h2' : s.im = z.im ∨ s.im = w.im := h2
    show s.im ∈ [[z.im, w.im]]
    rcases h2' with h2' | h2' <;> rw [h2'] <;> simp
  · refine ⟨?_, h2⟩
    have h1' : s.re = z.re ∨ s.re = w.re := h1
    show s.re ∈ [[z.re, w.re]]
    rcases h1' with h1' | h1' <;> rw [h1'] <;> simp

/-- Functions that agree on the boundary have the same rectangle integral. -/
theorem rectInt_congr {f g : ℂ → ℂ} {z w : ℂ} (h : EqOn f g (rectBorder z w)) : rectInt f z w = rectInt g z w := by
  unfold rectInt
  rw [intervalIntegral.integral_congr (fun x hx => h (mem_border_bot hx)),
    intervalIntegral.integral_congr (fun x hx => h (mem_border_top hx)),
    intervalIntegral.integral_congr (fun y hy => h (mem_border_right hy)),
    intervalIntegral.integral_congr (fun y hy => h (mem_border_left hy))]

section linear

variable {f g : ℂ → ℂ} {z w : ℂ}

theorem ii_bot (hf : ContinuousOn f (rectBorder z w)) :
    IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re :=
  (hf.comp (by fun_prop : Continuous fun x : ℝ => (x + z.im * I : ℂ)).continuousOn
    fun _ hx => mem_border_bot hx).intervalIntegrable

theorem ii_top (hf : ContinuousOn f (rectBorder z w)) :
    IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re :=
  (hf.comp (by fun_prop : Continuous fun x : ℝ => (x + w.im * I : ℂ)).continuousOn
    fun _ hx => mem_border_top hx).intervalIntegrable

theorem ii_right (hf : ContinuousOn f (rectBorder z w)) :
    IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im :=
  (hf.comp (by fun_prop : Continuous fun y : ℝ => (w.re + y * I : ℂ)).continuousOn
    fun _ hy => mem_border_right hy).intervalIntegrable

theorem ii_left (hf : ContinuousOn f (rectBorder z w)) :
    IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im :=
  (hf.comp (by fun_prop : Continuous fun y : ℝ => (z.re + y * I : ℂ)).continuousOn
    fun _ hy => mem_border_left hy).intervalIntegrable

theorem rectInt_add (hf : ContinuousOn f (rectBorder z w)) (hg : ContinuousOn g (rectBorder z w)) :
    rectInt (fun s => f s + g s) z w = rectInt f z w + rectInt g z w := by
  unfold rectInt
  rw [intervalIntegral.integral_add (ii_bot hf) (ii_bot hg), intervalIntegral.integral_add (ii_top hf) (ii_top hg),
    intervalIntegral.integral_add (ii_right hf) (ii_right hg),
    intervalIntegral.integral_add (ii_left hf) (ii_left hg)]
  ring

theorem rectInt_const_mul (c : ℂ) : rectInt (fun s => c * f s) z w = c * rectInt f z w := by
  unfold rectInt
  simp only [intervalIntegral.integral_const_mul]
  ring

theorem rectInt_neg : rectInt (fun s => -f s) z w = -rectInt f z w := by
  have := rectInt_const_mul (f := f) (z := z) (w := w) (-1)
  simpa using this

theorem rectInt_sum {ι : Type*} (S : Finset ι) {F : ι → ℂ → ℂ} (hF : ∀ i ∈ S, ContinuousOn (F i) (rectBorder z w)) :
    rectInt (fun s => ∑ i ∈ S, F i s) z w = ∑ i ∈ S, rectInt (F i) z w := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [rectInt]
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    rw [rectInt_add (hF a (Finset.mem_insert_self a S))
      (continuousOn_finsetSum _ fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

end linear

/-- Cauchy's theorem in the `rectInt` form. -/
theorem rectInt_eq_zero {f : ℂ → ℂ} {z w : ℂ} (hf : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    rectInt f z w = 0 := by
  have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hf
  simpa only [rectInt, smul_eq_mul] using this

/-! ### 2. The integral of `1/(s - a)` -/

theorem hasDerivAt_log_horiz (c : ℂ) (x : ℝ) (hc : (x + c : ℂ) ∈ slitPlane) :
    HasDerivAt (fun t : ℝ => Complex.log (t + c)) ((x + c : ℂ)⁻¹) x := by
  have h := ((hasDerivAt_id (x : ℂ)).add_const c).clog hc
  simpa [one_div] using h.comp_ofReal

theorem hasDerivAt_log_vert (c : ℂ) (y : ℝ) (hc : (c + y * I : ℂ) ∈ slitPlane) :
    HasDerivAt (fun t : ℝ => Complex.log (c + t * I)) (I * (c + y * I : ℂ)⁻¹) y := by
  have h := (((hasDerivAt_id (y : ℂ)).mul_const I).const_add c).clog hc
  have h2 := h.comp_ofReal
  simp only [id, one_mul] at h2
  rwa [div_eq_mul_inv] at h2

theorem hasDerivAt_log_vert_neg (c : ℂ) (y : ℝ) (hc : (-(c + y * I) : ℂ) ∈ slitPlane) :
    HasDerivAt (fun t : ℝ => Complex.log (-(c + t * I))) (I * (c + y * I : ℂ)⁻¹) y := by
  have h0 : HasDerivAt (fun u : ℂ => -(c + u * I)) (-I) (y : ℂ) := by
    have := (((hasDerivAt_id (y : ℂ)).mul_const I).const_add c).neg
    simp only [one_mul] at this
    exact this
  have h2 := (h0.clog hc).comp_ofReal
  convert h2 using 1
  rw [neg_div_neg_eq, div_eq_mul_inv]

/-- A horizontal side: `∫_{x₁}^{x₂} (x + c)⁻¹ dx = log(x₂ + c) - log(x₁ + c)` when `Im c ≠ 0`. -/
theorem integral_horiz {c : ℂ} (hc : c.im ≠ 0) (x₁ x₂ : ℝ) :
    ∫ x : ℝ in x₁..x₂, ((x : ℂ) + c)⁻¹ = Complex.log (x₂ + c) - Complex.log (x₁ + c) := by
  have hs : ∀ x : ℝ, (x + c : ℂ) ∈ slitPlane := fun x => by
    rw [mem_slitPlane_iff]; right; simpa using hc
  have hne : ∀ x : ℝ, (x + c : ℂ) ≠ 0 := fun x => slitPlane_ne_zero (hs x)
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_log_horiz c x (hs x)) ?_
  exact (Continuous.continuousOn (by fun_prop (disch := exact hne _))).intervalIntegrable

/-- A vertical side with `Re c > 0`: `I ∫_{y₁}^{y₂} (c + y i)⁻¹ dy = log(c + y₂ i) - log(c + y₁ i)`. -/
theorem integral_vert_pos {c : ℂ} (hc : 0 < c.re) (y₁ y₂ : ℝ) :
    I * ∫ y : ℝ in y₁..y₂, (c + y * I : ℂ)⁻¹ = Complex.log (c + y₂ * I) - Complex.log (c + y₁ * I) := by
  have hs : ∀ y : ℝ, (c + y * I : ℂ) ∈ slitPlane := fun y => by
    rw [mem_slitPlane_iff]; left; simpa using hc
  have hne : ∀ y : ℝ, (c + y * I : ℂ) ≠ 0 := fun y => slitPlane_ne_zero (hs y)
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_log_vert c y (hs y)) ?_
  exact (Continuous.continuousOn (by fun_prop (disch := exact hne _))).intervalIntegrable

/-- A vertical side with `Re c < 0`: `I ∫_{y₁}^{y₂} (c + y i)⁻¹ dy = log(-(c + y₂ i)) - log(-(c + y₁ i))`. -/
theorem integral_vert_neg {c : ℂ} (hc : c.re < 0) (y₁ y₂ : ℝ) :
    I * ∫ y : ℝ in y₁..y₂, (c + y * I : ℂ)⁻¹ = Complex.log (-(c + y₂ * I)) - Complex.log (-(c + y₁ * I)) := by
  have hs : ∀ y : ℝ, (-(c + y * I) : ℂ) ∈ slitPlane := fun y => by
    rw [mem_slitPlane_iff]; left; simpa using hc
  have hne : ∀ y : ℝ, (c + y * I : ℂ) ≠ 0 := fun y h => by
    have := slitPlane_ne_zero (hs y); rw [h, neg_zero] at this; exact this rfl
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_log_vert_neg c y (hs y)) ?_
  exact (Continuous.continuousOn (by fun_prop (disch := exact hne _))).intervalIntegrable

/-- **The winding integral.** For `a` strictly inside the rectangle, `∮ (s - a)⁻¹ ds = 2πi`. -/
theorem rectInt_inv_sub {z w a : ℂ} (h1 : z.re < a.re) (h2 : a.re < w.re) (h3 : z.im < a.im) (h4 : a.im < w.im) :
    rectInt (fun s => (s - a)⁻¹) z w = 2 * π * I := by
  unfold rectInt
  have eb : ∀ x : ℝ, ((x : ℂ) + z.im * I - a) = x + (z.im * I - a) := fun x => by ring
  have et : ∀ x : ℝ, ((x : ℂ) + w.im * I - a) = x + (w.im * I - a) := fun x => by ring
  have er : ∀ y : ℝ, ((w.re : ℂ) + y * I - a) = (w.re - a) + y * I := fun y => by ring
  have el : ∀ y : ℝ, ((z.re : ℂ) + y * I - a) = (z.re - a) + y * I := fun y => by ring
  simp_rw [eb, et, er, el]
  rw [integral_horiz (c := z.im * I - a) (by simp; linarith),
    integral_horiz (c := w.im * I - a) (by simp; linarith),
    integral_vert_pos (c := (w.re : ℂ) - a) (by simp; linarith),
    integral_vert_neg (c := (z.re : ℂ) - a) (by simp; linarith)]
  -- the four corners
  set c1 : ℂ := (z.re : ℂ) + (z.im * I - a) with hc1
  set c4 : ℂ := (z.re : ℂ) + (w.im * I - a) with hc4
  have e1 : ((z.re : ℂ) - a + z.im * I) = c1 := by rw [hc1]; ring
  have e4 : ((z.re : ℂ) - a + w.im * I) = c4 := by rw [hc4]; ring
  have e2 : ((w.re : ℂ) - a + z.im * I) = (w.re : ℂ) + (z.im * I - a) := by ring
  have e3 : ((w.re : ℂ) - a + w.im * I) = (w.re : ℂ) + (w.im * I - a) := by ring
  rw [e1, e4, e2, e3]
  have hi1 : c1.im < 0 := by simp [hc1]; linarith
  have hi4 : 0 < c4.im := by simp [hc4]; linarith
  have key : Complex.log c4 - Complex.log c1 - Complex.log (-c4) + Complex.log (-c1) = 2 * π * I := by
    apply Complex.ext
    · simp only [sub_re, add_re, Complex.log_re, norm_neg]
      simp
    · rw [show (2 * (π : ℂ) * I).im = 2 * π by simp]
      simp only [sub_im, add_im, Complex.log_im]
      rw [arg_neg_eq_arg_sub_pi_of_im_pos hi4, arg_neg_eq_arg_add_pi_of_im_neg hi1]
      ring
  rw [← key]
  ring

/-! ### 3. Cauchy's formula on a rectangle -/

/-- **Cauchy's formula.** For `H` entire and `a` strictly inside: `∮ H(s)/(s - a) ds = 2πi H(a)`. -/
theorem rectInt_div_sub {H : ℂ → ℂ} (hH : Differentiable ℂ H) {z w a : ℂ} (h1 : z.re < a.re) (h2 : a.re < w.re)
    (h3 : z.im < a.im) (h4 : a.im < w.im) :
    rectInt (fun s => H s * (s - a)⁻¹) z w = 2 * π * I * H a := by
  have hnot : a ∉ rectBorder z w := by
    rintro (⟨-, h⟩ | ⟨h, -⟩)
    · have h' : a.im = z.im ∨ a.im = w.im := h
      rcases h' with h' | h' <;> linarith
    · have h' : a.re = z.re ∨ a.re = w.re := h
      rcases h' with h' | h' <;> linarith
  have heq : EqOn (fun s => H s * (s - a)⁻¹) (fun s => dslope H a s + H a * (s - a)⁻¹) (rectBorder z w) := by
    intro s hs
    have hsa : s ≠ a := fun h => hnot (h ▸ hs)
    have hsa' : s - a ≠ 0 := sub_ne_zero.2 hsa
    simp only [dslope_of_ne _ hsa, slope_def_field]
    field_simp
    ring
  have hd : Differentiable ℂ (dslope H a) := fun s =>
    ((differentiableOn_dslope (Filter.univ_mem)).2 hH.differentiableOn s (mem_univ s)).differentiableAt
      Filter.univ_mem
  have hc1 : ContinuousOn (dslope H a) (rectBorder z w) := hd.continuous.continuousOn
  have hc2 : ContinuousOn (fun s => H a * (s - a)⁻¹) (rectBorder z w) := by
    refine continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun s hs h => hnot ?_)
    rwa [sub_eq_zero.1 h] at hs
  rw [rectInt_congr heq, rectInt_add hc1 hc2, rectInt_eq_zero hd.differentiableOn, rectInt_const_mul,
    rectInt_inv_sub h1 h2 h3 h4]
  ring

/-! ### 4. Factoring out the zeros on a compact convex set -/

/-- An entire function that is not identically zero has finite order everywhere. -/
theorem analyticOrderAt_ne_top_of_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) {z₀ : ℂ} (h0 : F z₀ ≠ 0) (u : ℂ) :
    analyticOrderAt F u ≠ ⊤ :=
  AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (fun x _ => hF.analyticAt x) isPreconnected_univ (mem_univ z₀)
    (mem_univ u) (by rw [(hF.analyticAt z₀).analyticOrderAt_eq_zero.2 h0]; exact ENat.zero_ne_top)

/-- At a zero of an entire function that is not identically zero, the order is at least one. -/
theorem analyticOrderNatAt_ne_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F) {z₀ : ℂ} (h0 : F z₀ ≠ 0) {u : ℂ}
    (hu : F u = 0) : analyticOrderNatAt F u ≠ 0 := by
  intro h
  rcases ENat.toNat_eq_zero.1 h with h | h
  · exact ((hF.analyticAt u).analyticOrderAt_eq_zero.1 h) hu
  · exact analyticOrderAt_ne_top_of_entire hF h0 u h

/-- **Factoring out the zeros.** An entire function `F` that is not identically zero is, on a compact convex set `K`
with nonempty interior, the product of `∏_ρ (s - ρ)^{ord_ρ F}` over its zeros in `K` and a function analytic near `K`
without zeros on `K`. (Mathlib's `MeromorphicOn.extract_zeros_poles`, made pointwise by the identity theorem.) -/
theorem exists_factor {F : ℂ → ℂ} (hF : Differentiable ℂ F) {z₀ : ℂ} (h0 : F z₀ ≠ 0) {K : Set ℂ} (hK : IsCompact K)
    (hKc : Convex ℝ K) (hKi : (interior K).Nonempty) :
    ∃ (S : Finset ℂ) (q : ℂ → ℂ), (∀ u, u ∈ S ↔ u ∈ K ∧ F u = 0) ∧ AnalyticOnNhd ℂ q K ∧ (∀ u ∈ K, q u ≠ 0) ∧
      ∀ s ∈ K, F s = (∏ u ∈ S, (s - u) ^ analyticOrderNatAt F u) * q s := by
  classical
  have hA : AnalyticOnNhd ℂ F K := fun x _ => hF.analyticAt x
  have htop := analyticOrderAt_ne_top_of_entire hF h0
  set D := MeromorphicOn.divisor F K with hD
  have hfin : D.support.Finite := D.finiteSupport hK
  obtain ⟨g, hg, hgne, heq⟩ := hA.meromorphicOn.extract_zeros_poles
    (fun u => by rw [(hF.analyticAt u).meromorphicOrderAt_eq]; simpa using htop u) hfin
  have hDu : ∀ u ∈ K, D u = (analyticOrderNatAt F u : ℤ) := fun u hu => by
    rw [hD, MeromorphicOn.AnalyticOnNhd.divisor_apply hA hu]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (htop u)
    rw [analyticOrderNatAt, ← hn]
    simp
  have hDout : ∀ u ∉ K, D u = 0 := fun u hu => D.apply_eq_zero_of_notMem hu
  set S := hfin.toFinset with hSdef
  have hSK : ∀ u ∈ S, u ∈ K := fun u hu => by
    by_contra h
    exact (Set.Finite.mem_toFinset hfin).1 hu (hDout u h)
  have hS : ∀ u, u ∈ S ↔ u ∈ K ∧ F u = 0 := by
    intro u
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    constructor
    · intro h
      by_cases hu : u ∈ K
      · refine ⟨hu, ?_⟩
        by_contra hne
        apply h
        rw [hDu u hu, analyticOrderNatAt, (hF.analyticAt u).analyticOrderAt_eq_zero.2 hne]
        simp
      · exact absurd (hDout u hu) h
    · rintro ⟨hu, hz⟩
      rw [hDu u hu]
      exact_mod_cast analyticOrderNatAt_ne_zero hF h0 hz
  -- the factorized rational function, evaluated
  have hP : ∀ s, (∏ᶠ u, (· - u) ^ D u) s = ∏ u ∈ S, (s - u) ^ analyticOrderNatAt F u := by
    intro s
    rw [Function.FactorizedRational.finprod_eq_fun hfin]
    simp only
    rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
    · refine Finset.prod_congr rfl fun u hu => ?_
      rw [hDu u (hSK u hu), zpow_natCast]
    · intro u hu
      rw [Function.mem_mulSupport] at hu
      rw [hSdef, Set.Finite.coe_toFinset]
      intro h0'
      exact hu (by rw [h0', zpow_zero])
  set P : ℂ → ℂ := fun s => ∏ u ∈ S, (s - u) ^ analyticOrderNatAt F u with hPdef
  have hPg : AnalyticOnNhd ℂ (fun s => P s * g s) K := fun s hs =>
    ((Differentiable.analyticAt (by fun_prop) s).mul (hg s hs))
  obtain ⟨z₁, hz₁⟩ := hKi
  have hev : ∀ᶠ y in 𝓝[≠] z₁, F y = P y * g y := by
    have h1 := (mem_codiscreteWithin.1 heq) z₁ (interior_subset hz₁)
    rw [Filter.disjoint_principal_right] at h1
    have h2 : ∀ᶠ y in 𝓝[≠] z₁, y ∈ K := mem_nhdsWithin_of_mem_nhds (mem_interior_iff_mem_nhds.1 hz₁)
    filter_upwards [h1, h2] with y hy1 hy2
    have : F y = ((∏ᶠ u, (· - u) ^ D u) • g) y := by
      by_contra hne
      exact hy1 ⟨hy2, hne⟩
    rw [this, Pi.smul_apply', smul_eq_mul, hP]
  have hEq := hA.eqOn_of_preconnected_of_frequently_eq hPg hKc.isPreconnected (interior_subset hz₁)
    hev.frequently
  exact ⟨S, g, hS, hg, fun u hu => hgne ⟨u, hu⟩, fun s hs => hEq hs⟩

/-! ### 5. The argument principle with a weight -/

theorem logDeriv_prod_pow_mul {S : Finset ℂ} {n : ℂ → ℕ} {q : ℂ → ℂ} {s : ℂ} (hs : ∀ u ∈ S, s ≠ u) (hq : q s ≠ 0)
    (hqd : DifferentiableAt ℂ q s) :
    logDeriv (fun t => (∏ u ∈ S, (t - u) ^ n u) * q t) s = (∑ u ∈ S, (n u : ℂ) * (s - u)⁻¹) + logDeriv q s := by
  have hP : (∏ u ∈ S, (s - u) ^ n u) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun u hu => pow_ne_zero _ (sub_ne_zero.2 (hs u hu))
  rw [logDeriv_fun_mul (f := fun t => ∏ u ∈ S, (t - u) ^ n u) s hP hq (by fun_prop) hqd]
  congr 1
  rw [logDeriv_fun_prod (f := fun u t => (t - u) ^ n u) (x := s) (fun u hu => pow_ne_zero _ (sub_ne_zero.2 (hs u hu))) (fun u _ => by fun_prop)]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hsu : s - u ≠ 0 := sub_ne_zero.2 (hs u hu)
  rw [logDeriv_fun_pow (by fun_prop), logDeriv_apply]
  have hd : deriv (fun t : ℂ => t - u) s = 1 := by
    rw [deriv_sub_const, deriv_id'']
  rw [hd]
  field_simp

theorem mem_rect_of_not_border {z w u : ℂ} (hzw1 : z.re < w.re) (hzw2 : z.im < w.im)
    (hu : u ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]]) (hb : u ∉ rectBorder z w) :
    z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im := by
  obtain ⟨h1, h2⟩ := hu
  have h1' : u.re ∈ Icc z.re w.re := by simpa [uIcc_of_le hzw1.le] using h1
  have h2' : u.im ∈ Icc z.im w.im := by simpa [uIcc_of_le hzw2.le] using h2
  refine ⟨lt_of_le_of_ne h1'.1 fun h => hb (Or.inr ⟨Or.inl h.symm, h2⟩),
    lt_of_le_of_ne h1'.2 fun h => hb (Or.inr ⟨Or.inr h, h2⟩),
    lt_of_le_of_ne h2'.1 fun h => hb (Or.inl ⟨h1, Or.inl h.symm⟩),
    lt_of_le_of_ne h2'.2 fun h => hb (Or.inl ⟨h1, Or.inr h⟩)⟩

theorem abs_le_of_mem_uIcc {a b x : ℝ} (h : x ∈ [[a, b]]) : |x| ≤ |a| + |b| := by
  rcases mem_uIcc.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    exact abs_le.2 ⟨by linarith [neg_abs_le a, neg_abs_le b, abs_nonneg a, abs_nonneg b],
      by linarith [le_abs_self a, le_abs_self b, abs_nonneg a, abs_nonneg b]⟩

theorem rect_subset_ball {z w : ℂ} :
    [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ Metric.ball (0 : ℂ) (2 * (‖z‖ + ‖w‖) + 1) := by
  intro s ⟨h1, h2⟩
  rw [mem_preimage] at h1 h2
  rw [Metric.mem_ball, dist_zero_right]
  have := Complex.norm_le_abs_re_add_abs_im s
  linarith [abs_le_of_mem_uIcc h1, abs_le_of_mem_uIcc h2, abs_re_le_norm z, abs_re_le_norm w,
    abs_im_le_norm z, abs_im_le_norm w]

/-- **The argument principle with a weight.** For `F` entire, not vanishing on the boundary of the rectangle, and `H`
entire: `∮ (F'/F)·H = 2πi ∑_ρ ord_ρ(F) H(ρ)`, the sum over the zeros of `F` in the closed rectangle (all of them
strictly inside). -/
theorem rectInt_logDeriv_mul {F H : ℂ → ℂ} (hF : Differentiable ℂ F) (hH : Differentiable ℂ H) {z w : ℂ}
    (hzw1 : z.re < w.re) (hzw2 : z.im < w.im) (hb : ∀ s ∈ rectBorder z w, F s ≠ 0) (T : Finset ℂ)
    (hT : ∀ u, u ∈ T ↔ u ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] ∧ F u = 0) :
    rectInt (fun s => logDeriv F s * H s) z w = 2 * π * I * ∑ u ∈ T, (analyticOrderNatAt F u : ℂ) * H u := by
  classical
  set K := [[z.re, w.re]] ×ℂ [[z.im, w.im]] with hKdef
  have hzb : z ∈ rectBorder z w := Or.inl ⟨by simp, by simp⟩
  have hz0 : F z ≠ 0 := hb z hzb
  set R : ℝ := 2 * (‖z‖ + ‖w‖) + 1 with hR
  have hRpos : 0 < R := by positivity
  obtain ⟨S, q, hS, hq, hqne, hfac⟩ := exists_factor hF hz0 (isCompact_closedBall (0 : ℂ) R)
    (convex_closedBall 0 R) ⟨0, by rw [interior_closedBall _ hRpos.ne']; exact Metric.mem_ball_self hRpos⟩
  have hKB : K ⊆ Metric.ball 0 R := rect_subset_ball
  have hbK : rectBorder z w ⊆ K := rectBorder_subset
  -- on the boundary, `F'/F = ∑ ord/(s - ρ) + q'/q`
  have hlog : ∀ s ∈ rectBorder z w, logDeriv F s =
      (∑ u ∈ S, (analyticOrderNatAt F u : ℂ) * (s - u)⁻¹) + logDeriv q s := by
    intro s hs
    have hsB : s ∈ Metric.ball (0 : ℂ) R := hKB (hbK hs)
    have hev : F =ᶠ[𝓝 s] fun t => (∏ u ∈ S, (t - u) ^ analyticOrderNatAt F u) * q t :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hsB) fun t ht =>
        hfac t (Metric.ball_subset_closedBall ht)
    rw [(logDeriv_congr_nhds hev).eq_of_nhds]
    have hsS : ∀ u ∈ S, s ≠ u := fun u hu h => hb s hs (h ▸ ((hS u).1 hu).2)
    exact logDeriv_prod_pow_mul hsS (hqne s (Metric.ball_subset_closedBall hsB))
      (hq s (Metric.ball_subset_closedBall hsB)).differentiableAt
  have hq' : ∀ s ∈ K, DifferentiableAt ℂ (fun t => logDeriv q t * H t) s := fun s hs => by
    have hsB := Metric.ball_subset_closedBall (hKB hs)
    have h1 : AnalyticAt ℂ (deriv q) s := (hq s hsB).deriv
    exact ((h1.differentiableAt.div (hq s hsB).differentiableAt (hqne s hsB)).mul (hH s))
  have hcq : ContinuousOn (fun t => logDeriv q t * H t) (rectBorder z w) := fun s hs =>
    (hq' s (hbK hs)).continuousAt.continuousWithinAt
  have hcu : ∀ u ∈ S, ContinuousOn (fun t => (analyticOrderNatAt F u : ℂ) * (H t * (t - u)⁻¹)) (rectBorder z w) := by
    intro u hu
    refine continuousOn_const.mul (hH.continuous.continuousOn.mul (ContinuousOn.inv₀ (by fun_prop) fun t ht h => ?_))
    rw [sub_eq_zero] at h
    exact hb t ht (h ▸ ((hS u).1 hu).2)
  have heq : EqOn (fun s => logDeriv F s * H s)
      (fun s => (∑ u ∈ S, (analyticOrderNatAt F u : ℂ) * (H s * (s - u)⁻¹)) + logDeriv q s * H s)
      (rectBorder z w) := by
    intro s hs
    simp only
    rw [hlog s hs, add_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [rectInt_congr heq, rectInt_add (continuousOn_finsetSum _ hcu) hcq, rectInt_sum _ hcu,
    rectInt_eq_zero (fun s hs => (hq' s hs).differentiableWithinAt), add_zero]
  -- each zero: inside gives `2πi H(ρ)`, outside gives `0`
  have hterm : ∀ u ∈ S, rectInt (fun t => (analyticOrderNatAt F u : ℂ) * (H t * (t - u)⁻¹)) z w =
      if u ∈ T then 2 * π * I * ((analyticOrderNatAt F u : ℂ) * H u) else 0 := by
    intro u hu
    rw [rectInt_const_mul]
    split_ifs with huT
    · have huK := ((hT u).1 huT).1
      have hub : u ∉ rectBorder z w := fun h => hb u h ((hS u).1 hu).2
      obtain ⟨h1, h2, h3, h4⟩ := mem_rect_of_not_border hzw1 hzw2 huK hub
      rw [rectInt_div_sub hH h1 h2 h3 h4]
      ring
    · have huK : u ∉ K := fun h => huT ((hT u).2 ⟨h, ((hS u).1 hu).2⟩)
      rw [rectInt_eq_zero, mul_zero]
      intro t ht
      have htu : t - u ≠ 0 := sub_ne_zero.2 fun h => huK (h ▸ ht)
      exact ((hH t).mul ((differentiableAt_id.sub_const u).inv htu)).differentiableWithinAt
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_mem, ← Finset.mul_sum]
  congr 2
  ext u
  simp only [Finset.mem_inter]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨(hS u).2 ⟨Metric.ball_subset_closedBall (hKB ((hT u).1 h).1), ((hT u).1 h).2⟩, h⟩

end ProofPhase.GRH.CS
