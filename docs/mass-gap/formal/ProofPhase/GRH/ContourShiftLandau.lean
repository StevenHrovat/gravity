/-
The contour shift, layer (b) generic part: Landau's bound for the logarithmic derivative near the zeros, and a zero
count, from the maximum principle and the Borel-Caratheodory theorem (2026-11-24). Released under Apache 2.0.

Paper: `docs/unified/CONTOUR-SHIFT.md`, section 4.
-/

import ProofPhase.GRH.ContourShiftRect
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Liouville

/-!
# Landau's lemma: the logarithmic derivative of an entire function near its zeros

For `f` entire with `f(z₀) ≠ 0` and `|f| ≤ M` on the disc `|z - z₀| ≤ R`, put `L = log(M / |f(z₀)|)`. Then
(Landau's lemma; Titchmarsh, *The Theory of the Riemann Zeta-Function*, section 3.9):

* **`landau`**: the zeros `ρ` of `f` with `|ρ - z₀| ≤ R/3`, counted with multiplicity, number at most `L / log 2`, and
  for `|z - z₀| ≤ R/12` with `f(z) ≠ 0`: `|f'/f(z) - ∑_ρ ord_ρ/(z - ρ)| ≤ 24 (L + 1) / R`.
* `norm_logDeriv_le`: hence `|f'/f(z)| ≤ 24 (L + 1)/R + L / (δ log 2)` when `z` keeps distance `δ` from those zeros.
* `exists_far_point`: among `N` points of `ℝ`, some point of `[a, a + 1]` keeps distance `1/(2(N + 1))` from all of
  them (the choice of the heights of the horizontal sides).

Proof: factor out the zeros (`exists_factor`); the quotient `q` satisfies `|q(z)/q(z₀)| ≤ e^L` on the disc by the
maximum principle (the factors `|z - ρ|` are at least `2R/3` on the circle and at most `R/3` at the centre, which also
gives the count); a holomorphic logarithm of `q` on the disc of radius `R/3` (Mathlib's primitives on discs) has real
part at most `L`, so Borel-Caratheodory (in Mathlib) bounds it by `2(L + 1)` on radius `R/6`, and Cauchy's estimate
bounds its derivative `q'/q` by `24 (L + 1)/R` on radius `R/12`.

No step uses the Hadamard product. Standard axioms only.
-/

open Complex Metric Set Filter Topology
open scoped Real

noncomputable section

namespace ProofPhase.GRH.CS

/-! ### 1. A holomorphic logarithm on a disc -/

/-- A holomorphic function without zeros on a disc has a holomorphic logarithm there: `q = q(z₀) e^Φ`, `Φ(z₀) = 0`,
`Φ' = q'/q`. -/
theorem exists_log_ball {q : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hq : DifferentiableOn ℂ q (ball z₀ r))
    (hq0 : ∀ z ∈ ball z₀ r, q z ≠ 0) :
    ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ (ball z₀ r) ∧ Φ z₀ = 0 ∧ (∀ z ∈ ball z₀ r, q z = q z₀ * exp (Φ z)) ∧
      ∀ z ∈ ball z₀ r, deriv Φ z = logDeriv q z := by
  have hd : DifferentiableOn ℂ (logDeriv q) (ball z₀ r) := by
    intro z hz
    have h1 := (hq.deriv isOpen_ball) z hz
    have h2 := (h1.differentiableAt (isOpen_ball.mem_nhds hz)).div
      ((hq z hz).differentiableAt (isOpen_ball.mem_nhds hz)) (hq0 z hz)
    exact h2.differentiableWithinAt
  obtain ⟨Ψ, hΨ⟩ := hd.isExactOn_ball
  set Φ : ℂ → ℂ := fun z => Ψ z - Ψ z₀ with hΦ
  have hΦd : ∀ z ∈ ball z₀ r, HasDerivAt Φ (logDeriv q z) z := fun z hz => (hΨ z hz).sub_const _
  refine ⟨Φ, fun z hz => (hΦd z hz).differentiableAt.differentiableWithinAt, by simp [hΦ], ?_,
    fun z hz => (hΦd z hz).deriv⟩
  set G : ℂ → ℂ := fun z => q z * exp (-Φ z) with hGdef
  have hG : ∀ z ∈ ball z₀ r, HasDerivAt G 0 z := by
    intro z hz
    have hqd : HasDerivAt q (deriv q z) z :=
      ((hq z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have := hqd.mul ((hΦd z hz).neg.cexp)
    convert this using 1
    rw [logDeriv_apply]
    field_simp [hq0 z hz]
    ring
  intro z hz
  have h := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z₀ r).isPreconnected
    (fun z hz => (hG z hz).differentiableAt.differentiableWithinAt) (fun z hz => (hG z hz).deriv) hz
    (mem_ball_self hr)
  have hΦ0 : Φ z₀ = 0 := by simp [hΦ]
  simp only [hGdef, hΦ0, neg_zero, Complex.exp_zero, mul_one] at h
  calc q z = q z * exp (-Φ z) * exp (Φ z) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = q z₀ * exp (Φ z) := by rw [h]

/-! ### 2. Landau's lemma -/

theorem prod_pow_le {S : Finset ℂ} {m : ℂ → ℕ} {z : ℂ} {a : ℝ} (h : ∀ u ∈ S, ‖z - u‖ ≤ a) :
    ‖∏ u ∈ S, (z - u) ^ m u‖ ≤ a ^ (∑ u ∈ S, m u) := by
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (h0 := fun u _ => by positivity) (h1 := fun u hu => by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (h u hu) _)

theorem le_prod_pow {S : Finset ℂ} {m : ℂ → ℕ} {z : ℂ} {a : ℝ} (ha : 0 ≤ a) (h : ∀ u ∈ S, a ≤ ‖z - u‖) :
    a ^ (∑ u ∈ S, m u) ≤ ‖∏ u ∈ S, (z - u) ^ m u‖ := by
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (h0 := fun u _ => by positivity) (h1 := fun u hu => by
    rw [norm_pow]; exact pow_le_pow_left₀ ha (h u hu) _)

/-- **Landau's lemma.** For `f` entire, `f(z₀) ≠ 0`, `|f| ≤ M` on `|z - z₀| ≤ R`, and `L = log(M/|f(z₀)|)`: the zeros
in `|ρ - z₀| ≤ R/3`, counted with multiplicity, number at most `L / log 2`, and for `|z - z₀| ≤ R/12`, `f(z) ≠ 0`:
`|f'/f(z) - ∑_ρ ord_ρ/(z - ρ)| ≤ 24 (L + 1)/R`. -/
theorem landau {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ} {R M : ℝ} (hR : 0 < R) (hf0 : f z₀ ≠ 0)
    (hM : ∀ z ∈ closedBall z₀ R, ‖f z‖ ≤ M) :
    ∃ S : Finset ℂ, (∀ u, u ∈ S ↔ u ∈ closedBall z₀ (R / 3) ∧ f u = 0) ∧
      (∑ u ∈ S, (analyticOrderNatAt f u : ℝ)) * Real.log 2 ≤ Real.log (M / ‖f z₀‖) ∧
      ∀ z ∈ closedBall z₀ (R / 12), f z ≠ 0 →
        ‖logDeriv f z - ∑ u ∈ S, (analyticOrderNatAt f u : ℂ) * (z - u)⁻¹‖ ≤
          24 * (Real.log (M / ‖f z₀‖) + 1) / R := by
  classical
  set K := closedBall z₀ R with hK
  obtain ⟨SR, qR, hSR, hqR, hqRne, hfac⟩ := exists_factor hf hf0 (isCompact_closedBall z₀ R) (convex_closedBall z₀ R)
    ⟨z₀, by rw [interior_closedBall _ hR.ne']; exact mem_ball_self hR⟩
  set m : ℂ → ℕ := fun u => analyticOrderNatAt f u with hm
  set Sin := SR.filter (fun u => dist u z₀ ≤ R / 3) with hSin
  set Sout := SR.filter (fun u => ¬ dist u z₀ ≤ R / 3) with hSout
  set q : ℂ → ℂ := fun s => (∏ u ∈ Sout, (s - u) ^ m u) * qR s with hq
  set P : ℂ → ℂ := fun s => ∏ u ∈ Sin, (s - u) ^ m u with hP
  set N : ℕ := ∑ u ∈ Sin, m u with hN
  have hfPq : ∀ s ∈ K, f s = P s * q s := by
    intro s hs
    rw [hfac s hs, hP, hq, ← mul_assoc, Finset.prod_filter_mul_prod_filter_not]
  have hqA : AnalyticOnNhd ℂ q K := fun s hs =>
    (Differentiable.analyticAt (by fun_prop) s).mul (hqR s hs)
  have hS : ∀ u, u ∈ Sin ↔ u ∈ closedBall z₀ (R / 3) ∧ f u = 0 := by
    intro u
    rw [hSin, Finset.mem_filter, hSR, mem_closedBall, mem_closedBall]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨⟨by linarith, h1⟩, h2⟩
  have hR3 : closedBall z₀ (R / 3) ⊆ K := closedBall_subset_closedBall (by linarith)
  have hqne : ∀ s ∈ closedBall z₀ (R / 3), q s ≠ 0 := by
    intro s hs
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun u hu => pow_ne_zero _ (sub_ne_zero.2 ?_)) (hqRne s (hR3 hs))
    rintro rfl
    exact (Finset.mem_filter.1 hu).2 (mem_closedBall.1 hs)
  have hf0' : 0 < ‖f z₀‖ := norm_pos_iff.2 hf0
  have hMf : ‖f z₀‖ ≤ M := hM z₀ (mem_closedBall_self hR.le)
  have hMpos : 0 < M := hf0'.trans_le hMf
  set L := Real.log (M / ‖f z₀‖) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg ((one_le_div hf0').2 hMf)
  -- the bound on the circle, then on the disc
  have hPcirc : ∀ s ∈ sphere z₀ R, (2 * R / 3) ^ N ≤ ‖P s‖ := fun s hs =>
    le_prod_pow (by positivity) fun u hu => by
      have h1 := mem_closedBall.1 ((hS u).1 hu).1
      have h2 : dist s z₀ = R := mem_sphere.1 hs
      have := dist_triangle s u z₀
      rw [← dist_eq_norm]; linarith
  have hqcirc : ∀ s ∈ sphere z₀ R, ‖q s‖ ≤ M / (2 * R / 3) ^ N := by
    intro s hs
    have hsK : s ∈ K := sphere_subset_closedBall hs
    have hPs : 0 < ‖P s‖ := lt_of_lt_of_le (by positivity) (hPcirc s hs)
    rw [le_div_iff₀ (by positivity)]
    calc ‖q s‖ * (2 * R / 3) ^ N ≤ ‖q s‖ * ‖P s‖ := by gcongr; exact hPcirc s hs
      _ = ‖f s‖ := by rw [hfPq s hsK, norm_mul (P s), mul_comm]
      _ ≤ M := hM s hsK
  have hqdisc : ∀ s ∈ K, ‖q s‖ ≤ M / (2 * R / 3) ^ N := by
    intro s hs
    have hd : DiffContOnCl ℂ q (ball z₀ R) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball z₀ hR.ne']
      exact fun x hx => (hqA x hx).differentiableAt.differentiableWithinAt
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd (fun z hz => ?_) ?_
    · rw [frontier_ball z₀ hR.ne'] at hz; exact hqcirc z hz
    · rwa [closure_ball z₀ hR.ne']
  have hPz₀ : ‖P z₀‖ ≤ (R / 3) ^ N := prod_pow_le fun u hu => by
    have := mem_closedBall.1 ((hS u).1 hu).1
    rw [← dist_eq_norm, dist_comm]; exact this
  have hPz₀pos : 0 < ‖P z₀‖ := by
    have : P z₀ * q z₀ ≠ 0 := by rw [← hfPq z₀ (mem_closedBall_self hR.le)]; exact hf0
    exact norm_pos_iff.2 (left_ne_zero_of_mul this)
  have hqz₀ : ‖f z₀‖ = ‖P z₀‖ * ‖q z₀‖ := by rw [hfPq z₀ (mem_closedBall_self hR.le), norm_mul]
  have hqz₀pos : 0 < ‖q z₀‖ := norm_pos_iff.2 (hqne z₀ (mem_closedBall_self (by positivity)))
  -- the ratio bound: `2^N |q(s)| ≤ (M/|f(z₀)|) |q(z₀)|` on the disc
  have hratio : ∀ s ∈ K, 2 ^ N * ‖q s‖ ≤ M / ‖f z₀‖ * ‖q z₀‖ := by
    intro s hs
    have h1 := hqdisc s hs
    have h3 : (2 : ℝ) ^ N * (R / 3) ^ N = (2 * R / 3) ^ N := by rw [← mul_pow]; ring_nf
    rw [div_mul_eq_mul_div, le_div_iff₀ hf0', hqz₀]
    calc 2 ^ N * ‖q s‖ * (‖P z₀‖ * ‖q z₀‖) ≤ 2 ^ N * ‖q s‖ * ((R / 3) ^ N * ‖q z₀‖) := by gcongr
      _ = ((2 * R / 3) ^ N * ‖q s‖) * ‖q z₀‖ := by rw [← h3]; ring
      _ ≤ M * ‖q z₀‖ := by
        gcongr
        rwa [le_div_iff₀ (by positivity), mul_comm] at h1
  refine ⟨Sin, hS, ?_, ?_⟩
  · -- the count: `2^N ≤ M/|f(z₀)|`
    have h := hratio z₀ (mem_closedBall_self hR.le)
    have h2N : (2 : ℝ) ^ N ≤ M / ‖f z₀‖ := le_of_mul_le_mul_right (by linarith) hqz₀pos
    have hcast : (∑ u ∈ Sin, (analyticOrderNatAt f u : ℝ)) = (N : ℝ) := by rw [hN]; push_cast; rfl
    rw [hcast, hL, ← Real.log_pow]
    exact Real.log_le_log (by positivity) h2N
  · -- the logarithmic derivative
    obtain ⟨Φ, hΦd, hΦ0, hΦq, hΦderiv⟩ := exists_log_ball (q := q) (z₀ := z₀) (r := R / 3) (by positivity)
      (fun x hx => (hqA x (hR3 (ball_subset_closedBall hx))).differentiableAt.differentiableWithinAt)
      (fun x hx => hqne x (ball_subset_closedBall hx))
    -- `Re Φ ≤ L`
    have hre : ∀ x ∈ ball z₀ (R / 3), (Φ x).re ≤ L + 1 := by
      intro x hx
      have hx' := hΦq x hx
      have hn : ‖q x‖ = ‖q z₀‖ * Real.exp (Φ x).re := by rw [hx', norm_mul, Complex.norm_exp]
      have h1 := hratio x (hR3 (ball_subset_closedBall hx))
      have h2 : Real.exp (Φ x).re ≤ M / ‖f z₀‖ := by
        have : ‖q z₀‖ * Real.exp (Φ x).re ≤ M / ‖f z₀‖ * ‖q z₀‖ := by
          rw [← hn]; exact le_trans (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by norm_num))) h1
        nlinarith
      have h3 : (Φ x).re ≤ L := by
        rw [hL]; exact (Real.le_log_iff_exp_le (by positivity)).2 h2
      linarith
    -- Borel-Caratheodory on radius `R/3`, evaluated on radius `R/6`
    have hBC : ∀ x ∈ closedBall z₀ (R / 6), ‖Φ x‖ ≤ 2 * (L + 1) := by
      intro x hx
      have hx' : x - z₀ ∈ ball (0 : ℂ) (R / 3) := by
        rw [mem_ball, dist_zero_right, ← dist_eq_norm]
        have := mem_closedBall.1 hx; linarith
      have hdiff : DifferentiableOn ℂ (fun ζ => Φ (z₀ + ζ)) (ball 0 (R / 3)) := by
        intro ζ hζ
        have hmem : z₀ + ζ ∈ ball z₀ (R / 3) := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; rwa [mem_ball, dist_zero_right] at hζ
        exact (((hΦd _ hmem).differentiableAt (isOpen_ball.mem_nhds hmem)).comp ζ
          ((differentiableAt_const z₀).add differentiableAt_id)).differentiableWithinAt
      have hmaps : MapsTo (fun ζ => Φ (z₀ + ζ)) (ball 0 (R / 3)) {w | w.re ≤ L + 1} := by
        intro ζ hζ
        have hmem : z₀ + ζ ∈ ball z₀ (R / 3) := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; rwa [mem_ball, dist_zero_right] at hζ
        exact hre _ hmem
      have h := Complex.borelCaratheodory (by linarith) hdiff hmaps (by positivity) hx'
      simp only [add_zero, hΦ0, norm_zero, zero_mul, zero_div, add_sub_cancel] at h
      have hn : ‖x - z₀‖ ≤ R / 6 := by rw [← dist_eq_norm]; exact mem_closedBall.1 hx
      calc ‖Φ x‖ ≤ 2 * (L + 1) * ‖x - z₀‖ / (R / 3 - ‖x - z₀‖) := h
        _ ≤ 2 * (L + 1) := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
    intro z hz hfz
    have hzB : z ∈ ball z₀ (R / 3) := mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hz) (by linarith))
    -- Cauchy's estimate for `Φ' = q'/q`
    have hcl : closedBall z (R / 12) ⊆ ball z₀ (R / 3) := by
      intro x hx
      rw [mem_ball]
      have := dist_triangle x z z₀
      have := mem_closedBall.1 hx
      have := mem_closedBall.1 hz
      linarith
    have hderiv : ‖deriv Φ z‖ ≤ 2 * (L + 1) / (R / 12) := by
      refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) (hΦd.diffContOnCl_ball hcl)
        fun x hx => hBC x ?_
      rw [mem_closedBall]
      have := dist_triangle x z z₀
      have := mem_sphere.1 hx
      have := mem_closedBall.1 hz
      linarith
    rw [hΦderiv z hzB] at hderiv
    -- `f'/f = ∑ ord/(z - ρ) + q'/q`
    have hzK : z ∈ ball z₀ R := mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hz) (by linarith))
    have hev : f =ᶠ[𝓝 z] fun t => (∏ u ∈ Sin, (t - u) ^ m u) * q t :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hzK) fun t ht => hfPq t (ball_subset_closedBall ht)
    have hzS : ∀ u ∈ Sin, z ≠ u := fun u hu h => hfz (h ▸ ((hS u).1 hu).2)
    rw [(logDeriv_congr_nhds hev).eq_of_nhds,
      logDeriv_prod_pow_mul hzS (hqne z (ball_subset_closedBall hzB))
        (hqA z (hR3 (ball_subset_closedBall hzB))).differentiableAt, add_sub_cancel_left]
    calc ‖logDeriv q z‖ ≤ 2 * (L + 1) / (R / 12) := hderiv
      _ = 24 * (L + 1) / R := by field_simp; ring

/-- **The bound away from the zeros.** Under the hypotheses of `landau`, if `|z - z₀| ≤ R/12` and `z` keeps distance
`δ > 0` from the zeros in `|ρ - z₀| ≤ R/3`, then `|f'/f(z)| ≤ 24 (L + 1)/R + L/(δ log 2)`. -/
theorem norm_logDeriv_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ} {R M δ : ℝ} (hR : 0 < R) (hf0 : f z₀ ≠ 0)
    (hM : ∀ z ∈ closedBall z₀ R, ‖f z‖ ≤ M) (hδ : 0 < δ) {z : ℂ} (hz : z ∈ closedBall z₀ (R / 12))
    (hfar : ∀ u ∈ closedBall z₀ (R / 3), f u = 0 → δ ≤ ‖z - u‖) :
    ‖logDeriv f z‖ ≤ 24 * (Real.log (M / ‖f z₀‖) + 1) / R + Real.log (M / ‖f z₀‖) / (δ * Real.log 2) := by
  obtain ⟨S, hS, hcount, hld⟩ := landau hf hR hf0 hM
  have hfz : f z ≠ 0 := by
    intro h
    have hz3 : z ∈ closedBall z₀ (R / 3) := closedBall_subset_closedBall (by linarith) hz
    have := hfar z hz3 h
    rw [sub_self, norm_zero] at this
    linarith
  have hsum : ‖∑ u ∈ S, (analyticOrderNatAt f u : ℂ) * (z - u)⁻¹‖ ≤
      (∑ u ∈ S, (analyticOrderNatAt f u : ℝ)) / δ := by
    rw [Finset.sum_div]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u hu => ?_)
    rw [norm_mul, norm_inv, Complex.norm_natCast, div_eq_mul_inv]
    gcongr
    exact hfar u ((hS u).1 hu).1 ((hS u).1 hu).2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcount' : (∑ u ∈ S, (analyticOrderNatAt f u : ℝ)) / δ ≤ Real.log (M / ‖f z₀‖) / (δ * Real.log 2) := by
    rw [div_le_div_iff₀ hδ (by positivity)]
    nlinarith
  calc ‖logDeriv f z‖
      ≤ ‖logDeriv f z - ∑ u ∈ S, (analyticOrderNatAt f u : ℂ) * (z - u)⁻¹‖ +
          ‖∑ u ∈ S, (analyticOrderNatAt f u : ℂ) * (z - u)⁻¹‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := add_le_add (hld z hz hfz) (hsum.trans hcount')

/-! ### 3. Choosing a height away from finitely many ordinates -/

/-- Among `N` real numbers, some point of `[a, a + 1]` keeps distance at least `1/(2(N + 1))` from all of them. -/
theorem exists_far_point (Z : Finset ℝ) (a : ℝ) :
    ∃ T ∈ Icc a (a + 1), ∀ γ ∈ Z, 1 / (2 * (Z.card + 1)) ≤ |T - γ| := by
  classical
  set N := Z.card with hN
  set h : ℝ := 1 / (N + 1) with hh
  have hpos : 0 < h := by positivity
  by_contra hcon
  push Not at hcon
  -- every candidate `a + j h`, `j ≤ N`, is blocked by some ordinate
  have hblock : ∀ j ∈ Finset.range (N + 1), ∃ γ ∈ Z, |a + j * h - γ| < 1 / (2 * (N + 1)) := by
    intro j hj
    have hj' : (j : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    refine hcon _ ⟨by have := mul_nonneg (Nat.cast_nonneg j) hpos.le; linarith, ?_⟩
    have : (j : ℝ) * h ≤ 1 := by
      rw [hh, mul_one_div, div_le_one (by positivity)]; linarith
    linarith
  choose! γ hγZ hγ using hblock
  have hinj : Set.InjOn γ (Finset.range (N + 1)) := by
    intro i hi j hj hij
    have h1 := hγ i hi
    have h2 := hγ j hj
    rw [hij] at h1
    have h3 : |(i : ℝ) * h - j * h| < 1 / (N + 1) := by
      have e : 1 / (2 * ((N : ℝ) + 1)) + 1 / (2 * (N + 1)) = 1 / (N + 1) := by field_simp; ring
      have := abs_sub_lt_iff.1 h1
      have := abs_sub_lt_iff.1 h2
      rw [abs_lt]; constructor <;> linarith
    rw [← sub_mul, abs_mul, abs_of_pos hpos, hh] at h3
    have h4 : |(i : ℝ) - j| < 1 := by
      have := (mul_lt_iff_lt_one_left (by positivity : (0 : ℝ) < 1 / (N + 1))).1 (by linarith)
      exact this
    have : (i : ℤ) = j := by
      have h5 : |((i : ℤ) - j : ℤ)| < 1 := by exact_mod_cast h4
      have := Int.abs_lt_one_iff.1 h5
      omega
    exact_mod_cast this
  have hcard := Finset.card_le_card_of_injOn γ (fun j hj => hγZ j hj) hinj
  simp only [Finset.card_range] at hcard
  omega

end ProofPhase.GRH.CS
