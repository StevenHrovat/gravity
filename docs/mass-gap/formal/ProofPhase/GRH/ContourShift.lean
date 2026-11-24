/-
The contour shift for zeta, proved (2026-11-24). Released under Apache 2.0.

Paper: `docs/unified/CONTOUR-SHIFT.md`, section 7.
-/

import ProofPhase.GRH.ContourShiftZeta
import ProofPhase.GRH.ContourShiftTest
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# The contour shift for `ζ`, proved

For `c > 1` and `g` smooth with compact support, the contour shift holds (`contourShift`). This file and the four it
builds on (`ContourShiftRect`, `ContourShiftLandau`, `ContourShiftZeta`, `ContourShiftTest`) import only Mathlib; they
are the core destined for the public IM repository. `ContourShiftTie.lean` identifies the statement with the project's
`EF.ContourShift c g` and derives Weil's explicit formula with no named step.

Proof, for an enumeration `ρ_i = 1/2 + iγ_i` of the nontrivial zeros with multiplicity:
1. `rect_identity`: on the rectangle `[1 - c, c] × [b, t]` whose horizontal sides avoid the zeros, the argument principle
   (`ContourShiftRect.lean`) applied to `-Λ'/Λ · H = -ξ'/ξ · H + H/s + H/(s - 1)` gives
   `∮ (-Λ'/Λ) H = 2πi (H(1) + H(0) - ∑_ρ ord_ρ H(ρ))`, the sum over the zeros inside.
2. Heights `t_n ∈ [n + 1, n + 2]` and `b_n ∈ [-(n + 2), -(n + 1)]` with `|Λ'/Λ| ≤ B n⁴` on the horizontal sides
   (`exists_good_height`); since `|H| ≤ C/(1 + |Im s|)⁶` there (`laplace_decay`), the horizontal sides tend to `0`.
3. On the vertical lines `|Λ'/Λ| ≤ B (1 + |y|)²` (`logDeriv_vline_bound`), so the integrand is integrable and the vertical
   sides tend to `2π` times the line integrals `vline`.
4. `zf_summable`, `zf_tendsto`: the zero count per window (`zero_count_window`) and the decay of `H` make
   `∑_i H(ρ_i)` absolutely summable, and the sums over the zeros in the growing rectangles tend to it.

Standard axioms only. This proves the explicit formula for `ζ`; it does not prove RH or GRH.
-/

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

noncomputable section

namespace ProofPhase.GRH.CS

/-! ### 0. The vocabulary of the contour shift

The same definitions as `ExplicitFormulaPrime.lean` and `ExplicitFormula.lean` (`EF.vpt`, `EF.vline`, `EF.wInt`,
`EF.NontrivialZeroFamily`), repeated so that this file needs only Mathlib; `ContourShiftTie.lean` identifies them. -/

/-- The vertical line `Re s = c`, parametrised as `s(τ) = c - 2π i τ`. -/
def vpt (c τ : ℝ) : ℂ := c - 2 * π * I * τ

/-- The line integral `(1/2πi) ∫_{(c)} f(s) ds = ∫ f(c - 2πiτ) dτ`. -/
def vline (f : ℂ → ℂ) (c : ℝ) : ℂ := ∫ τ : ℝ, f (vpt c τ)

/-- The integrand of the explicit formula, `-Λ'/Λ (s) · H(s)`. -/
def wInt (g : ℝ → ℂ) : ℂ → ℂ := fun s => -logDeriv completedRiemannZeta s * laplace g s

/-- The nontrivial zeros of `ζ` with multiplicity, in the coordinate `ρ = 1/2 + iγ`. -/
def ZeroFamily {ι : Type} (γ : ι → ℂ) : Prop :=
  (∀ i, 0 < (1 / 2 + I * γ i).re ∧ (1 / 2 + I * γ i).re < 1 ∧ riemannZeta (1 / 2 + I * γ i) = 0) ∧
    ∀ z : ℂ, 0 < z.re → z.re < 1 → {i | 1 / 2 + I * γ i = z}.encard = analyticOrderAt riemannZeta z

/-! ### 1. The integrand near the lines and segments -/

theorem completedZeta_ne_zero_of_xiF {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (hx : xiF s ≠ 0) :
    completedRiemannZeta s ≠ 0 := fun h => hx (by rw [xiF_eq h0 h1, h, mul_zero])

theorem continuousAt_logDeriv_completed {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (hx : xiF s ≠ 0) :
    ContinuousAt (logDeriv completedRiemannZeta) s := by
  set U : Set ℂ := {0}ᶜ ∩ {1}ᶜ with hU
  have hUo : IsOpen U := isOpen_compl_singleton.inter isOpen_compl_singleton
  have hd : DifferentiableOn ℂ completedRiemannZeta U := fun t ht =>
    (differentiableAt_completedZeta ht.1 ht.2).differentiableWithinAt
  have hs : s ∈ U := ⟨h0, h1⟩
  have hder := ((hd.deriv hUo) s hs).differentiableAt (hUo.mem_nhds hs)
  exact hder.continuousAt.div ((hd s hs).differentiableAt (hUo.mem_nhds hs)).continuousAt
    (completedZeta_ne_zero_of_xiF h0 h1 hx)

theorem continuousAt_logDeriv_xiF {s : ℂ} (hx : xiF s ≠ 0) : ContinuousAt (logDeriv xiF) s := by
  have hder := (differentiable_xiF.differentiableOn.deriv isOpen_univ) s (mem_univ s)
  exact (hder.differentiableAt (isOpen_univ.mem_nhds (mem_univ s))).continuousAt.div
    (differentiable_xiF s).continuousAt hx

theorem continuousAt_wInt {g : ℝ → ℂ} (hg : Continuous g) (hgs : HasCompactSupport g) {s : ℂ} (h0 : s ≠ 0)
    (h1 : s ≠ 1) (hx : xiF s ≠ 0) : ContinuousAt (wInt g) s :=
  (continuousAt_logDeriv_completed h0 h1 hx).neg.mul (differentiable_laplace hg hgs s).continuousAt

/-- Points off the critical strip are not zeros of `ξ`. -/
theorem xiF_ne_zero_of_re {s : ℂ} (h : s.re ≤ 0 ∨ 1 ≤ s.re) : xiF s ≠ 0 := fun hx => by
  have := re_of_xiF_eq_zero hx
  rcases h with h | h <;> linarith [this.1, this.2]

/-! ### 2. The rectangle identity -/

/-- **The rectangle identity.** For `c > 1`, heights `b ≤ -1 < 1 ≤ t` whose horizontal sides avoid the zeros, and `T` the
zeros of `ξ` in the closed rectangle: `∮ (-Λ'/Λ) H = 2πi (H(1) + H(0) - ∑_{ρ ∈ T} ord_ρ H(ρ))`. -/
theorem rect_identity {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} (hg : Continuous g) (hgs : HasCompactSupport g) {b t : ℝ}
    (hb : b ≤ -1) (ht : 1 ≤ t) (hbot : ∀ σ ∈ Icc (1 - c) c, xiF (σ + b * I) ≠ 0)
    (htop : ∀ σ ∈ Icc (1 - c) c, xiF (σ + t * I) ≠ 0) (T : Finset ℂ)
    (hT : ∀ u, u ∈ T ↔ u ∈ [[1 - c, c]] ×ℂ [[b, t]] ∧ xiF u = 0) :
    rectInt (wInt g) (((1 - c : ℝ) : ℂ) + b * I) (c + t * I) =
      2 * π * I * (laplace g 1 + laplace g 0 - ∑ u ∈ T, (analyticOrderNatAt xiF u : ℂ) * laplace g u) := by
  set z : ℂ := ((1 - c : ℝ) : ℂ) + b * I with hz
  set w : ℂ := (c : ℂ) + t * I with hw
  have hzr : z.re = 1 - c := by simp [hz]
  have hzi : z.im = b := by simp [hz]
  have hwr : w.re = c := by simp [hw]
  have hwi : w.im = t := by simp [hw]
  set H := laplace g with hH
  have hHd : Differentiable ℂ H := differentiable_laplace hg hgs
  -- every boundary point: `ξ ≠ 0`, `≠ 0`, `≠ 1`
  have hbd : ∀ s ∈ rectBorder z w, xiF s ≠ 0 ∧ s ≠ 0 ∧ s ≠ 1 := by
    rintro s (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · -- horizontal sides
      have h2' : s.im = z.im ∨ s.im = w.im := h2
      rw [hzi, hwi] at h2'
      have hre : s.re ∈ Icc (1 - c) c := by
        have : s.re ∈ [[z.re, w.re]] := h1
        rwa [hzr, hwr, uIcc_of_le (by linarith)] at this
      have hs : s = (s.re : ℂ) + s.im * I := (re_add_im s).symm
      have him1 : 1 ≤ |s.im| := by
        rcases h2' with h | h <;> rw [h]
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact ht
      have hne0 : s ≠ 0 := by
        intro h; rw [h] at him1; simp at him1; linarith
      have hne1 : s ≠ 1 := by
        intro h; rw [h] at him1; simp at him1; linarith
      refine ⟨?_, hne0, hne1⟩
      rcases h2' with h | h
      · rw [hs, h]; exact hbot _ hre
      · rw [hs, h]; exact htop _ hre
    · -- vertical sides
      have h1' : s.re = z.re ∨ s.re = w.re := h1
      rw [hzr, hwr] at h1'
      refine ⟨xiF_ne_zero_of_re ?_, fun h => ?_, fun h => ?_⟩
      · rcases h1' with h | h <;> rw [h]
        · left; linarith
        · right; linarith
      · rw [h] at h1'; simp at h1'; rcases h1' with h | h <;> linarith
      · rw [h] at h1'; simp at h1'; rcases h1' with h | h <;> linarith
  have heq : EqOn (wInt g) (fun s => (-(logDeriv xiF s * H s) + H s * (s - 0)⁻¹) + H s * (s - 1)⁻¹)
      (rectBorder z w) := by
    intro s hs
    obtain ⟨hx, h0, h1⟩ := hbd s hs
    simp only [wInt, hH]
    rw [logDeriv_completedZeta_eq h0 h1 hx, sub_zero]
    ring
  have hc1 : ContinuousOn (fun s => -(logDeriv xiF s * H s)) (rectBorder z w) := fun s hs =>
    ((continuousAt_logDeriv_xiF (hbd s hs).1).mul (hHd s).continuousAt).neg.continuousWithinAt
  have hc2 : ∀ a : ℂ, (∀ s ∈ rectBorder z w, s ≠ a) → ContinuousOn (fun s => H s * (s - a)⁻¹) (rectBorder z w) :=
    fun a ha s hs => ((hHd s).continuousAt.mul ((continuousAt_id.sub continuousAt_const).inv₀
      (sub_ne_zero.2 (ha s hs)))).continuousWithinAt
  have h0 : ∀ s ∈ rectBorder z w, s ≠ 0 := fun s hs => (hbd s hs).2.1
  have h1 : ∀ s ∈ rectBorder z w, s ≠ 1 := fun s hs => (hbd s hs).2.2
  have hsplit : rectInt (fun s => (-(logDeriv xiF s * H s) + H s * (s - 0)⁻¹) + H s * (s - 1)⁻¹) z w =
      -rectInt (fun s => logDeriv xiF s * H s) z w + rectInt (fun s => H s * (s - 0)⁻¹) z w +
        rectInt (fun s => H s * (s - 1)⁻¹) z w := by
    rw [rectInt_add (f := fun s => -(logDeriv xiF s * H s) + H s * (s - 0)⁻¹) (g := fun s => H s * (s - 1)⁻¹)
      (hc1.add (hc2 0 h0)) (hc2 1 h1),
      rectInt_add (f := fun s => -(logDeriv xiF s * H s)) (g := fun s => H s * (s - 0)⁻¹) hc1 (hc2 0 h0),
      rectInt_neg (f := fun s => logDeriv xiF s * H s)]
  rw [rectInt_congr heq, hsplit]
  have hzw1 : z.re < w.re := by rw [hzr, hwr]; linarith
  have hzw2 : z.im < w.im := by rw [hzi, hwi]; linarith
  rw [rectInt_logDeriv_mul differentiable_xiF hHd hzw1 hzw2 (fun s hs => (hbd s hs).1) T
      (fun u => by rw [hzr, hwr, hzi, hwi]; exact hT u),
    rectInt_div_sub hHd (by rw [hzr]; simp; linarith) (by rw [hwr]; simp; linarith)
      (by rw [hzi]; simp; linarith) (by rw [hwi]; simp; linarith),
    rectInt_div_sub hHd (by rw [hzr]; simp; linarith) (by rw [hwr]; simp; linarith)
      (by rw [hzi]; simp; linarith) (by rw [hwi]; simp; linarith)]
  ring

/-! ### 3. The vertical lines -/

/-- `∫ f(x + iy) dy = 2π · (1/2πi) ∫_{(x)} f = 2π vline f x`. -/
theorem integral_line_eq_vline (f : ℂ → ℂ) (x : ℝ) : ∫ y : ℝ, f (x + y * I) = 2 * π * vline f x := by
  have h := Measure.integral_comp_mul_left (fun y : ℝ => f (x + y * I)) (-2 * π)
  have hv : vline f x = ∫ τ : ℝ, f (x + ((-2 * π * τ : ℝ) : ℂ) * I) := by
    unfold vline
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only [vpt]
    congr 1
    push_cast
    ring
  rw [hv, h, Complex.real_smul]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have habs : |(-2 * π)⁻¹| = (2 * π)⁻¹ := by
    rw [abs_inv, abs_mul, abs_neg, abs_two, abs_of_pos Real.pi_pos]
  rw [habs]
  have h2 : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hpi
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul]

/-- On the lines `Re s = c` and `Re s = 1 - c`, the integrand is bounded by `B C/(1 + |y|)²`, hence integrable. -/
theorem integrable_wInt_line {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} (hg : ∀ k : ℕ, ContDiff ℝ k g)
    (hgs : HasCompactSupport g) {x : ℝ} (hx : x = c ∨ x = 1 - c) :
    Integrable (fun y : ℝ => wInt g (x + y * I)) := by
  obtain ⟨B, hB, hvl⟩ := logDeriv_vline_bound hc
  obtain ⟨C, hC, hdec⟩ := laplace_decay hg hgs 4 c
  have hgc : Continuous g := (hg 0).continuous
  have hxre : x ≤ 0 ∨ 1 ≤ x := by rcases hx with rfl | rfl <;> [right; left] <;> linarith
  have hcont : Continuous fun y : ℝ => wInt g (x + y * I) := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    have hs : ((x : ℂ) + y * I).re = x := by simp
    have h0 : (x : ℂ) + y * I ≠ 0 := fun h => by
      have := congrArg Complex.re h; rw [hs] at this; simp at this; rcases hx with rfl | rfl <;> linarith
    have h1 : (x : ℂ) + y * I ≠ 1 := fun h => by
      have := congrArg Complex.re h; rw [hs] at this; simp at this; rcases hx with rfl | rfl <;> linarith
    have hxi : xiF ((x : ℂ) + y * I) ≠ 0 := xiF_ne_zero_of_re (by rw [hs]; exact hxre)
    exact ContinuousAt.comp (f := fun y : ℝ => (x : ℂ) + y * I) (continuousAt_wInt hgc hgs h0 h1 hxi)
      (Continuous.continuousAt (by fun_prop))
  have hint := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).const_mul (B * C)
  refine hint.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hlog : ‖logDeriv completedRiemannZeta (x + y * I)‖ ≤ B * (1 + |y|) ^ 2 := by
    rcases hx with rfl | rfl
    · exact (hvl y).1
    · exact (hvl y).2
  have hH : ‖laplace g (x + y * I)‖ * (1 + |y|) ^ 4 ≤ C := by
    have := hdec ((x : ℂ) + y * I) (by
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero]
      rcases hx with rfl | rfl <;> rw [abs_le] <;> constructor <;> linarith)
    simpa using this
  have hpos : 0 < 1 + |y| := by positivity
  rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two]
  simp only [wInt, norm_mul, norm_neg]
  have h4 : ‖laplace g (x + y * I)‖ ≤ C / (1 + |y|) ^ 4 := by rw [le_div_iff₀ (by positivity)]; exact hH
  calc ‖logDeriv completedRiemannZeta (x + y * I)‖ * ‖laplace g (x + y * I)‖
      ≤ B * (1 + |y|) ^ 2 * (C / (1 + |y|) ^ 4) := by gcongr
    _ = B * C * ((1 + |y|) ^ 2)⁻¹ := by field_simp

/-! ### 4. The zero family: fibres, summability, and the limit of the partial sums -/

section ZeroFamily

variable {ι : Type} {γ : ι → ℂ}

theorem zf_xiF (hZ : ZeroFamily γ) (i : ι) : xiF (1 / 2 + I * γ i) = 0 :=
  (xiF_eq_zero_iff _).2 (hZ.1 i)

theorem analyticOrderAt_xiF_ne_top (u : ℂ) : analyticOrderAt xiF u ≠ ⊤ :=
  analyticOrderAt_ne_top_of_entire differentiable_xiF (z₀ := 0) (by rw [xiF_zero]; exact one_ne_zero) u

theorem zf_fiber_finite (hZ : ZeroFamily γ) (u : ℂ) : {i | 1 / 2 + I * γ i = u}.Finite := by
  by_cases hu : 0 < u.re ∧ u.re < 1
  · rw [← Set.encard_ne_top_iff, hZ.2 u hu.1 hu.2, ← analyticOrderAt_xiF hu.1 hu.2]
    exact analyticOrderAt_xiF_ne_top u
  · convert Set.finite_empty
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    exact hu (h ▸ ⟨(hZ.1 i).1, (hZ.1 i).2.1⟩)

theorem zf_fiber_card (hZ : ZeroFamily γ) {u : ℂ} (hu : xiF u = 0) :
    (zf_fiber_finite hZ u).toFinset.card = analyticOrderNatAt xiF u := by
  obtain ⟨h1, h2⟩ := re_of_xiF_eq_zero hu
  have h := hZ.2 u h1 h2
  rw [(zf_fiber_finite hZ u).encard_eq_coe_toFinset_card, ← analyticOrderAt_xiF h1 h2] at h
  rw [analyticOrderNatAt, ← h]
  rfl

theorem zf_pre_finite (hZ : ZeroFamily γ) (Z : Finset ℂ) : {i | 1 / 2 + I * γ i ∈ Z}.Finite := by
  have : {i | 1 / 2 + I * γ i ∈ Z} = ⋃ u ∈ Z, {i | 1 / 2 + I * γ i = u} := by ext i; simp
  rw [this]
  exact Z.finite_toSet.biUnion fun u _ => zf_fiber_finite hZ u

/-- Summing over the family on the indices that land in `Z` is summing over `Z` with multiplicities. -/
theorem zf_sum (hZ : ZeroFamily γ) (Z : Finset ℂ) (hZ0 : ∀ u ∈ Z, xiF u = 0) {M : Type*}
    [AddCommMonoid M] (F : ℂ → M) :
    ∑ i ∈ (zf_pre_finite hZ Z).toFinset, F (1 / 2 + I * γ i) = ∑ u ∈ Z, analyticOrderNatAt xiF u • F u := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun i => 1 / 2 + I * γ i) (t := Z)
    (fun i hi => by simpa using hi)]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hset : (zf_pre_finite hZ Z).toFinset.filter (fun i => 1 / 2 + I * γ i = u) =
      (zf_fiber_finite hZ u).toFinset := by
    ext i
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hu, h⟩
  rw [hset, Finset.sum_congr rfl (g := fun _ => F u) (fun i hi => by
      have h' : 1 / 2 + I * γ i = u := by simpa using hi
      rw [h']),
    Finset.sum_const, zf_fiber_card hZ (hZ0 u hu)]

theorem summable_inv_one_add_sq : Summable fun n : ℕ => 1 / (1 + (n : ℝ)) ^ 2 := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  refine h.congr fun n => ?_
  push_cast; ring_nf

/-- **Absolute summability over the zeros.** If `|F(s)| (1 + |Im s|)⁴ ≤ C` on the critical strip, then `∑_i F(ρ_i)`
converges absolutely (with the zero count per window, `zero_count_window`). -/
theorem zf_summable (hZ : ZeroFamily γ) {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s : ℂ, 0 < s.re → s.re < 1 → ‖F s‖ * (1 + |s.im|) ^ 4 ≤ C) :
    Summable fun i => F (1 / 2 + I * γ i) := by
  classical
  obtain ⟨B, hB, hwin⟩ := zero_count_window
  set G : ℕ → ℝ := fun n => 2 * B * C * (1 / (1 + (n : ℝ)) ^ 2) with hG
  have hGs : Summable G := summable_inv_one_add_sq.mul_left _
  have hG0 : ∀ n, 0 ≤ G n := fun n => by rw [hG]; positivity
  refine Summable.of_norm (summable_of_sum_le (c := ∑' n, G n) (fun i => norm_nonneg _) fun u => ?_)
  set Zu := u.image fun i => 1 / 2 + I * γ i with hZu
  have hZu0 : ∀ z ∈ Zu, xiF z = 0 := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    exact zf_xiF hZ i
  have hsub : u ⊆ (zf_pre_finite hZ Zu).toFinset := fun i hi => by
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact Finset.mem_image_of_mem _ hi
  calc ∑ i ∈ u, ‖F (1 / 2 + I * γ i)‖ ≤ ∑ i ∈ (zf_pre_finite hZ Zu).toFinset, ‖F (1 / 2 + I * γ i)‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => norm_nonneg _
    _ = ∑ z ∈ Zu, analyticOrderNatAt xiF z • ‖F z‖ := zf_sum hZ Zu hZu0 (fun z => ‖F z‖)
    _ = ∑ z ∈ Zu, (analyticOrderNatAt xiF z : ℝ) * ‖F z‖ := by simp [nsmul_eq_mul]
    _ ≤ ∑' n, G n := by
      set N : ℂ → ℕ := fun z => ⌊|z.im|⌋₊ with hN
      rw [← Finset.sum_fiberwise_of_maps_to (g := N) (t := Zu.image N) (fun z hz => Finset.mem_image_of_mem _ hz)]
      refine le_trans (Finset.sum_le_sum fun n _ => ?_) (hGs.sum_le_tsum _ fun n _ => hG0 n)
      -- one shell `⌊|Im z|⌋ = n`
      set Sh := Zu.filter fun z => N z = n with hSh
      have hdec : ∀ z ∈ Sh, ‖F z‖ ≤ C * (1 / (1 + (n : ℝ)) ^ 4) := by
        intro z hz
        obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
        obtain ⟨h1, h2⟩ := re_of_xiF_eq_zero (hZu0 z hz1)
        have hz2' : ⌊|z.im|⌋₊ = n := hz2
        have hn : (n : ℝ) ≤ |z.im| := by rw [← hz2']; exact Nat.floor_le (abs_nonneg _)
        have hF' := hF z h1 h2
        have hpos : 0 < 1 + (n : ℝ) := by positivity
        rw [mul_one_div, le_div_iff₀ (by positivity)]
        calc ‖F z‖ * (1 + (n : ℝ)) ^ 4 ≤ ‖F z‖ * (1 + |z.im|) ^ 4 := by gcongr
          _ ≤ C := hF'
      have hcount : ∑ z ∈ Sh, (analyticOrderNatAt xiF z : ℝ) ≤ 2 * B * (1 + (n : ℝ)) ^ 2 := by
        rw [← Finset.sum_filter_add_sum_filter_not Sh (fun z => 0 ≤ z.im)]
        have hw : ∀ (y : ℝ), |y| = n → ∀ T : Finset ℂ, (∀ z ∈ T, xiF z = 0 ∧ |z.im - y| ≤ 1) →
            ∑ z ∈ T, (analyticOrderNatAt xiF z : ℝ) ≤ B * (1 + (n : ℝ)) ^ 2 := fun y hy T hT => by
          rw [← hy]; exact hwin y T hT
        have hlt : ∀ z ∈ Sh, |z.im| < n + 1 := fun z hz => by
          have := Nat.lt_floor_add_one (|z.im|)
          have hn : ⌊|z.im|⌋₊ = n := (Finset.mem_filter.1 hz).2
          rw [hn] at this
          exact this
        have hge : ∀ z ∈ Sh, (n : ℝ) ≤ |z.im| := fun z hz => by
          have hn : ⌊|z.im|⌋₊ = n := (Finset.mem_filter.1 hz).2
          rw [← hn]; exact Nat.floor_le (abs_nonneg _)
        have e1 := hw n (by simp) (Sh.filter fun z => 0 ≤ z.im) fun z hz => by
          obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
          refine ⟨hZu0 z (Finset.mem_filter.1 hz1).1, ?_⟩
          have a1 := hlt z hz1; have a2 := hge z hz1
          rw [abs_of_nonneg hz2] at a1 a2
          rw [abs_le]; constructor <;> linarith
        have e2 := hw (-(n : ℝ)) (by simp) (Sh.filter fun z => ¬ 0 ≤ z.im) fun z hz => by
          obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
          refine ⟨hZu0 z (Finset.mem_filter.1 hz1).1, ?_⟩
          have a1 := hlt z hz1; have a2 := hge z hz1
          rw [abs_of_neg (not_le.1 hz2)] at a1 a2
          rw [abs_le]; constructor <;> linarith
        linarith
      calc ∑ z ∈ Sh, (analyticOrderNatAt xiF z : ℝ) * ‖F z‖
          ≤ ∑ z ∈ Sh, (analyticOrderNatAt xiF z : ℝ) * (C * (1 / (1 + (n : ℝ)) ^ 4)) :=
            Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (hdec z hz) (Nat.cast_nonneg _)
        _ = (∑ z ∈ Sh, (analyticOrderNatAt xiF z : ℝ)) * (C * (1 / (1 + (n : ℝ)) ^ 4)) := by
            rw [Finset.sum_mul]
        _ ≤ 2 * B * (1 + (n : ℝ)) ^ 2 * (C * (1 / (1 + (n : ℝ)) ^ 4)) := by gcongr
        _ = G n := by
            rw [hG]
            have : (1 + (n : ℝ)) ≠ 0 := by positivity
            field_simp

/-- **The partial sums over growing sets of zeros tend to the sum over the family.** -/
theorem zf_tendsto (hZ : ZeroFamily γ) {F : ℂ → ℂ} (hs : Summable fun i => F (1 / 2 + I * γ i))
    (Z : ℕ → Finset ℂ) (hZ0 : ∀ n, ∀ u ∈ Z n, xiF u = 0) (hmono : ∀ n, Z n ⊆ Z (n + 1))
    (hexh : ∀ u, xiF u = 0 → ∃ n, u ∈ Z n) :
    Tendsto (fun n => ∑ u ∈ Z n, (analyticOrderNatAt xiF u : ℂ) * F u) atTop
      (𝓝 (∑' i, F (1 / 2 + I * γ i))) := by
  set P : ℕ → Finset ι := fun n => (zf_pre_finite hZ (Z n)).toFinset with hP
  have hPm : Monotone P := by
    refine monotone_nat_of_le_succ fun n i hi => ?_
    simp only [hP, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hi ⊢
    exact hmono n hi
  have hPe : ∀ i, ∃ n, i ∈ P n := fun i => by
    obtain ⟨n, hn⟩ := hexh _ (zf_xiF hZ i)
    exact ⟨n, by simp only [hP, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]; exact hn⟩
  have h := hs.hasSum.comp (tendsto_atTop_finset_of_monotone hPm hPe)
  refine h.congr fun n => ?_
  simp only [Function.comp, hP]
  rw [zf_sum hZ (Z n) (hZ0 n) F]
  simp [nsmul_eq_mul]

end ZeroFamily

/-! ### 5. The contour shift -/

theorem tendsto_const_div_sq {K : ℝ} : Tendsto (fun n : ℕ => K * (1 / ((n : ℝ) + 1) ^ 2)) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat.pow 2).const_mul K
  simp only [zero_pow two_ne_zero, mul_zero] at h
  refine h.congr fun n => ?_
  rw [one_div_pow]

/-- A horizontal side is small: on `[1 - c, c] + iT`, `|Λ'/Λ| ≤ B (1 + |a|)⁴` and `|H| (1 + |Im|)⁶ ≤ C` with
`1 + |a| ≤ 2 (1 + |T|)` give `|∫ (-Λ'/Λ) H| ≤ 64 B C (2c - 1) / (1 + |a|)²`. -/
theorem horiz_side_le {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} {C B T a : ℝ} (hB : 0 ≤ B)
    (hC : ∀ s : ℂ, |s.re - 1 / 2| ≤ c → ‖laplace g s‖ * (1 + |s.im|) ^ 6 ≤ C)
    (hlog : ∀ σ ∈ Icc (1 - c) c, ‖logDeriv completedRiemannZeta (σ + T * I)‖ ≤ B * (1 + |a|) ^ 4)
    (haT : 1 + |a| ≤ 2 * (1 + |T|)) :
    ‖∫ x in (1 - c)..c, wInt g (x + T * I)‖ ≤ 64 * B * C * (2 * c - 1) * (1 / (1 + |a|) ^ 2) := by
  have hpa : 0 < 1 + |a| := by positivity
  have hpT : 0 < 1 + |T| := by positivity
  have hle : ‖∫ x in (1 - c)..c, wInt g (x + T * I)‖ ≤ 64 * B * C / (1 + |a|) ^ 2 * |c - (1 - c)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le (by linarith)] at hx
    have hx' : x ∈ Icc (1 - c) c := ⟨hx.1.le, hx.2⟩
    have hl := hlog x hx'
    have hH := hC (x + T * I) (by
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero]
      rw [abs_le]; constructor <;> linarith [hx'.1, hx'.2])
    have him : ((x : ℂ) + T * I).im = T := by simp
    rw [him] at hH
    have hH' : ‖laplace g (x + T * I)‖ ≤ C / (1 + |T|) ^ 6 := by rw [le_div_iff₀ (by positivity)]; exact hH
    have hC0 : 0 ≤ C := le_trans (by positivity) hH
    have h6 : (1 + |a|) ^ 6 ≤ 64 * (1 + |T|) ^ 6 := by
      have := pow_le_pow_left₀ hpa.le haT 6
      calc (1 + |a|) ^ 6 ≤ (2 * (1 + |T|)) ^ 6 := this
        _ = 64 * (1 + |T|) ^ 6 := by ring
    simp only [wInt, norm_mul, norm_neg]
    calc ‖logDeriv completedRiemannZeta (x + T * I)‖ * ‖laplace g (x + T * I)‖
        ≤ B * (1 + |a|) ^ 4 * (C / (1 + |T|) ^ 6) := by gcongr
      _ ≤ B * (1 + |a|) ^ 4 * (64 * C / (1 + |a|) ^ 6) := by
          have h' : C / (1 + |T|) ^ 6 ≤ 64 * C / (1 + |a|) ^ 6 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
          exact mul_le_mul_of_nonneg_left h' (by positivity)
      _ = 64 * B * C / (1 + |a|) ^ 2 := by field_simp
  calc _ ≤ 64 * B * C / (1 + |a|) ^ 2 * |c - (1 - c)| := hle
    _ = 64 * B * C * (2 * c - 1) * (1 / (1 + |a|) ^ 2) := by
        rw [show |c - (1 - c)| = 2 * c - 1 by rw [abs_of_pos (by linarith)]; ring]
        ring

theorem mem_rect_iff {u : ℂ} {x₁ x₂ y₁ y₂ : ℝ} : u ∈ [[x₁, x₂]] ×ℂ [[y₁, y₂]] ↔ u.re ∈ [[x₁, x₂]] ∧ u.im ∈ [[y₁, y₂]] :=
  Iff.rfl

/-- **The contour shift for `ζ`.** For `c > 1` and `g` smooth with compact support: for every enumeration of the
nontrivial zeros with multiplicity, `∑ H(ρ)` converges absolutely and
`(1/2πi) ∫_{(c)} (-Λ'/Λ) H - (1/2πi) ∫_{(1-c)} (-Λ'/Λ) H = H(1) + H(0) - ∑_ρ H(ρ)`. (This is `EF.ContourShift c g`;
see `ContourShiftTie.lean`.) -/
theorem contourShift {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} (hg : ∀ k : ℕ, ContDiff ℝ k g) (hgs : HasCompactSupport g) :
    ∀ (ι : Type) (γ : ι → ℂ), ZeroFamily γ →
      Summable (fun i => laplace g (1 / 2 + I * γ i)) ∧
        vline (wInt g) c - vline (wInt g) (1 - c) = laplace g 1 + laplace g 0 - ∑' i, laplace g (1 / 2 + I * γ i) := by
  intro ι γ hZ
  have hgc : Continuous g := (hg 0).continuous
  set H := laplace g with hH
  set f := wInt g with hf
  obtain ⟨C₄, hC₄0, hC₄⟩ := laplace_decay hg hgs 4 1
  obtain ⟨C₆, hC₆0, hC₆⟩ := laplace_decay hg hgs 6 c
  obtain ⟨Bh, hBh, hgood⟩ := exists_good_height hc
  have hn0 : ∀ n : ℕ, (0 : ℝ) ≤ n := fun n => Nat.cast_nonneg n
  choose t ht htg using fun n : ℕ => hgood ((n : ℝ) + 1) (Or.inl (by linarith [hn0 n]))
  choose b hb hbg using fun n : ℕ => hgood (-((n : ℝ) + 2)) (Or.inr (by linarith [hn0 n]))
  have ht1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ t n := fun n => (ht n).1
  have ht2 : ∀ n : ℕ, t n ≤ (n : ℝ) + 2 := fun n => by linarith [(ht n).2]
  have hb1 : ∀ n : ℕ, b n ≤ -((n : ℝ) + 1) := fun n => by linarith [(hb n).2]
  have hb2 : ∀ n : ℕ, -((n : ℝ) + 2) ≤ b n := fun n => (hb n).1
  choose Z hZ' using fun n : ℕ =>
    exists_zero_finset ([[1 - c, c]] ×ℂ [[b n, t n]]) (isCompact_uIcc.reProdIm isCompact_uIcc)
  -- summability over the zeros
  have hsum : Summable fun i => H (1 / 2 + I * γ i) :=
    zf_summable hZ hC₄0 fun s h1 h2 => hC₄ s (by rw [abs_le]; constructor <;> linarith)
  refine ⟨hsum, ?_⟩
  -- the rectangle identity, side by side
  have hrect : ∀ n : ℕ, (∫ x in (1 - c)..c, f (x + b n * I)) - (∫ x in (1 - c)..c, f (x + t n * I)) +
      I * (∫ y in b n..t n, f (c + y * I)) - I * (∫ y in b n..t n, f ((1 - c : ℝ) + y * I)) =
        2 * π * I * (H 1 + H 0 - ∑ u ∈ Z n, (analyticOrderNatAt xiF u : ℂ) * H u) := by
    intro n
    have h := rect_identity hc hgc hgs (by linarith [hb1 n, hn0 n]) (by linarith [ht1 n, hn0 n])
      (fun σ hσ => (hbg n σ hσ).1) (fun σ hσ => (htg n σ hσ).1) (Z n) (hZ' n)
    have hzr : (((1 - c : ℝ) : ℂ) + b n * I).re = 1 - c := by simp
    have hzi : (((1 - c : ℝ) : ℂ) + b n * I).im = b n := by simp
    have hwr : ((c : ℂ) + t n * I).re = c := by simp
    have hwi : ((c : ℂ) + t n * I).im = t n := by simp
    unfold rectInt at h
    rw [hzr, hzi, hwr, hwi] at h
    exact h
  -- the horizontal sides vanish
  have hK := tendsto_const_div_sq (K := 64 * Bh * C₆ * (2 * c - 1))
  have hlimB : Tendsto (fun n : ℕ => ∫ x in (1 - c)..c, f (x + b n * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hK
    have hle := horiz_side_le hc (g := g) (a := -((n : ℝ) + 2)) hBh.le hC₆ (fun σ hσ => (hbg n σ hσ).2) (by
      rw [abs_neg, abs_of_pos (by linarith [hn0 n]), abs_of_neg (by linarith [hb1 n, hn0 n])]
      linarith [hb1 n])
    refine hle.trans ?_
    have hp : 0 ≤ 64 * Bh * C₆ * (2 * c - 1) := by
      have : 0 ≤ 2 * c - 1 := by linarith
      positivity
    have hq : 1 / (1 + |-((n : ℝ) + 2)|) ^ 2 ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
      rw [abs_neg, abs_of_pos (by linarith [hn0 n])]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 2)
    exact mul_le_mul_of_nonneg_left hq hp
  have hlimT : Tendsto (fun n : ℕ => ∫ x in (1 - c)..c, f (x + t n * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hK
    have hle := horiz_side_le hc (g := g) (a := (n : ℝ) + 1) hBh.le hC₆ (fun σ hσ => (htg n σ hσ).2) (by
      rw [abs_of_pos (by linarith [hn0 n]), abs_of_pos (by linarith [ht1 n, hn0 n])]
      linarith [ht1 n])
    refine hle.trans ?_
    have hp : 0 ≤ 64 * Bh * C₆ * (2 * c - 1) := by
      have : 0 ≤ 2 * c - 1 := by linarith
      positivity
    have hq : 1 / (1 + |(n : ℝ) + 1|) ^ 2 ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
      rw [abs_of_pos (by linarith [hn0 n])]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 2)
    exact mul_le_mul_of_nonneg_left hq hp
  -- the vertical sides converge to the line integrals
  have hbB : Tendsto b atTop atBot :=
    tendsto_atBot_mono hb1 (tendsto_neg_atTop_atBot.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
  have htT : Tendsto t atTop atTop :=
    tendsto_atTop_mono ht1 (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hlimR : Tendsto (fun n : ℕ => ∫ y in b n..t n, f (c + y * I)) atTop (𝓝 (2 * π * vline f c)) := by
    rw [← integral_line_eq_vline]
    exact intervalIntegral_tendsto_integral (integrable_wInt_line hc hg hgs (Or.inl rfl)) hbB htT
  have hlimL : Tendsto (fun n : ℕ => ∫ y in b n..t n, f ((1 - c : ℝ) + y * I)) atTop
      (𝓝 (2 * π * vline f (1 - c))) := by
    rw [← integral_line_eq_vline]
    exact intervalIntegral_tendsto_integral (integrable_wInt_line hc hg hgs (Or.inr rfl)) hbB htT
  -- the zero sums converge to the sum over the family
  have hlimS : Tendsto (fun n => ∑ u ∈ Z n, (analyticOrderNatAt xiF u : ℂ) * H u) atTop
      (𝓝 (∑' i, H (1 / 2 + I * γ i))) := by
    refine zf_tendsto hZ hsum Z (fun n u hu => ((hZ' n u).1 hu).2) (fun n u hu => ?_) (fun u hu => ?_)
    · obtain ⟨⟨h1, h2⟩, h3⟩ := (hZ' n u).1 hu
      refine (hZ' (n + 1) u).2 ⟨⟨h1, ?_⟩, h3⟩
      rw [uIcc_of_le (by linarith [hb1 n, ht1 n, hn0 n])] at h2
      rw [uIcc_of_le (by linarith [hb1 (n + 1), ht1 (n + 1), hn0 (n + 1)])]
      have e1 := hb1 (n + 1); have e2 := ht1 (n + 1)
      push_cast at e1 e2
      exact ⟨by linarith [h2.1, hb2 n], by linarith [h2.2, ht2 n]⟩
    · obtain ⟨hu1, hu2⟩ := re_of_xiF_eq_zero hu
      refine ⟨⌈|u.im|⌉₊, (hZ' _ u).2 ⟨⟨?_, ?_⟩, hu⟩⟩
      · show u.re ∈ [[1 - c, c]]
        rw [uIcc_of_le (by linarith)]; exact ⟨by linarith, by linarith⟩
      · show u.im ∈ [[b ⌈|u.im|⌉₊, t ⌈|u.im|⌉₊]]
        have hceil := Nat.le_ceil (|u.im|)
        have e1 := hb1 ⌈|u.im|⌉₊; have e2 := ht1 ⌈|u.im|⌉₊
        rw [uIcc_of_le (by linarith)]
        constructor <;> linarith [neg_abs_le u.im, le_abs_self u.im]
  -- compare the two limits of the same sequence
  have hL : Tendsto (fun n : ℕ => (∫ x in (1 - c)..c, f (x + b n * I)) - (∫ x in (1 - c)..c, f (x + t n * I)) +
      I * (∫ y in b n..t n, f (c + y * I)) - I * (∫ y in b n..t n, f ((1 - c : ℝ) + y * I))) atTop
      (𝓝 (0 - 0 + I * (2 * π * vline f c) - I * (2 * π * vline f (1 - c)))) :=
    ((hlimB.sub hlimT).add (hlimR.const_mul I)).sub (hlimL.const_mul I)
  have hR : Tendsto (fun n : ℕ => (∫ x in (1 - c)..c, f (x + b n * I)) - (∫ x in (1 - c)..c, f (x + t n * I)) +
      I * (∫ y in b n..t n, f (c + y * I)) - I * (∫ y in b n..t n, f ((1 - c : ℝ) + y * I))) atTop
      (𝓝 (2 * π * I * (H 1 + H 0 - ∑' i, H (1 / 2 + I * γ i)))) := by
    simp_rw [hrect]
    exact tendsto_const_nhds.mul (tendsto_const_nhds.sub hlimS)
  have heq := tendsto_nhds_unique hL hR
  have h2 : (2 * (π : ℂ) * I) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  apply mul_left_cancel₀ h2
  linear_combination heq

end ProofPhase.GRH.CS
