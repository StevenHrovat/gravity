/-
Attempt round 2 (2026-11-21), attempt D: the step-scaling recursion. Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/r2-stepscaling/NOTE.md` (sections 2 and 3).
-/

import Mathlib

/-!
# The two-loop step-scaling recursion: layer count, asymptotic scaling, sharpness, photon

Let `u_j` be an inverse coupling of a box of side `2^j ℓ₀` (lattice units). Any normalisation works: `u = 1/g²`,
`u = β = 2N/g²`, or `u = 1/α_s = 4π/g²` (`phi_rescale`: a change of normalisation `u ↦ s u` maps the coefficients
`(c₀, c₁) ↦ (s c₀, s² c₁)` and shifts the scale function by a constant). The **step-scaling recursion** is

  `u_{j+1} = u_j - c₀ - c₁/u_j + r_j`,   `|r_j| ≤ K/u_j² + η_j`,

with `c₀, c₁` the one- and two-loop coefficients, `K/u²` the three-loop and higher remainder, and `η_j` lattice
artefacts (`O(a/L) = O(2^{-j})`, summable).

**Results.**
* `phi c₀ c₁ u = u/c₀ - (c₁/c₀²) log u`, the two-loop scale function (in units of doublings);
  `log₂(1/(aΛ)) = phi(u₀) + const` is two-loop asymptotic scaling.
* `phi_step`: one step changes `phi` by `-1` up to `|r|/c₀ (1 + |c₁|/(c₀u)) + (c₁² + 2|c₁|X²)/(c₀²u²)`: the `1/u` terms
  cancel **exactly because the two-loop coefficient in `phi` is the one in the recursion**.
* `count_two_loop`: summing (telescoping `1/u_j² ≤ (1/x_min)(1/u_{j+1} - 1/u_j)`), the number of layers `J` from `u₀`
  down to `u_J` satisfies `|phi(u_J) - phi(u₀) + J| ≤ (A/x_min)(1/u_J - 1/u₀) + B ∑ η_j`, **uniformly in `u₀`**.
* `crossing_exists`: with a decrement `≥ x_min > 0` above a threshold, the first layer below it exists.
* `scaling_window`: the crossing layer of the weak-coupling threshold `U`, plus a bounded number `N` of further layers,
  stays within a bounded distance of `phi(u₀)`, uniformly in `u₀` (asymptotic scaling of the scale-setting layer).
* `phi_diff_tendsto`, `scaling_drift`: **sharpness**: with any other two-loop coefficient `c₁' ≠ c₁` the distance grows
  like `|c₁' - c₁|/c₀² · log u₀ → ∞`. (The one-loop analogue is `Attempts.SelfCharge.scale_unbounded`.)
* `floor_of_steps`, `photon_never_reaches`: **photon test**: if the coupling never runs (`u_j - u_{j+1} ≤ η_j`,
  `∑ η_j ≤ H`: zero running, or screening, plus summable artefacts), then `u_n ≥ u₀ - H` for all `n`: from a weak bare
  coupling the inverse coupling never comes down to an `O(1)` value `u*`.

Nothing here is about gauge theory: these are statements about real sequences. Their use is in
`Attempts.R2.StepScalingH1` and in the note.
-/

open Finset Filter Topology

noncomputable section

namespace Attempts.R2

/-! ## The scale function -/

/-- **Two-loop scale function** (in doublings): `phi(u) = u/c₀ - (c₁/c₀²) log u`. -/
def phi (c₀ c₁ u : ℝ) : ℝ := u / c₀ - c₁ / c₀ ^ 2 * Real.log u

/-- **Normalisation does not matter.** Rescaling the inverse coupling `u ↦ s u` (e.g. `1/g² ↦ 1/α_s = 4π/g²`, `s = 4π`)
maps the coefficients to `(s c₀, s² c₁)` and shifts `phi` by the constant `-(c₁/c₀²) log s`. -/
theorem phi_rescale {c₀ c₁ s u : ℝ} (hc₀ : c₀ ≠ 0) (hs : 0 < s) (hu : 0 < u) :
    phi (s * c₀) (s ^ 2 * c₁) (s * u) = phi c₀ c₁ u - c₁ / c₀ ^ 2 * Real.log s := by
  unfold phi
  rw [Real.log_mul hs.ne' hu.ne']
  field_simp
  ring

/-- The recursion is invariant in form under rescaling: `s u` obeys the recursion with `(s c₀, s² c₁)` and remainder
`s r`. -/
theorem step_rescale {c₀ c₁ s u u' r : ℝ} (hs : 0 < s) (hu : 0 < u) (h : u' = u - c₀ - c₁ / u + r) :
    s * u' = s * u - s * c₀ - s ^ 2 * c₁ / (s * u) + s * r := by
  rw [h]
  field_simp

/-! ## One step -/

/-- `|log(1 - t) + t| ≤ t²/(1 - t)` for `t < 1`. -/
theorem abs_log_one_sub_add_le {t : ℝ} (ht : t < 1) : |Real.log (1 - t) + t| ≤ t ^ 2 / (1 - t) := by
  have hpos : 0 < 1 - t := by linarith
  have h1 : Real.log (1 - t) ≤ (1 - t) - 1 := Real.log_le_sub_one_of_pos hpos
  have h2 : 1 - (1 - t)⁻¹ ≤ Real.log (1 - t) := Real.one_sub_inv_le_log_of_pos hpos
  have e : 1 - (1 - t)⁻¹ = -t - t ^ 2 / (1 - t) := by field_simp; ring
  have hq : 0 ≤ t ^ 2 / (1 - t) := div_nonneg (sq_nonneg t) hpos.le
  rw [abs_le]
  constructor <;> linarith

/-- For `|t| ≤ 1/2`: `|log(1 - t) + t| ≤ 2 t²`. -/
theorem abs_log_one_sub_add_le_two {t : ℝ} (ht : |t| ≤ 1 / 2) : |Real.log (1 - t) + t| ≤ 2 * t ^ 2 := by
  have ht' : t ≤ 1 / 2 := (le_abs_self t).trans ht
  have hpos : 0 < 1 - t := by linarith
  refine (abs_log_one_sub_add_le (by linarith)).trans ?_
  rw [div_le_iff₀ hpos]
  nlinarith [sq_nonneg t]

/-- **One step of the recursion moves `phi` by `-1`, up to second order.** If `u > 0`, the step `x = u - u'` obeys
`|x| ≤ X ≤ u/2` and `x = c₀ + c₁/u - r`, then
`|phi(u - x) - phi(u) + 1| ≤ |r|/c₀ + |c₁||r|/(c₀²u) + (c₁² + 2|c₁|X²)/(c₀²u²)`.
The `1/u` terms cancel because `phi` carries the same `c₁` as the recursion. -/
theorem phi_step {c₀ c₁ u x r X : ℝ} (hc₀ : 0 < c₀) (hu : 0 < u) (hX : |x| ≤ X) (huX : 2 * X ≤ u)
    (hx : x = c₀ + c₁ / u - r) :
    |phi c₀ c₁ (u - x) - phi c₀ c₁ u + 1| ≤
      |r| / c₀ + |c₁| * |r| / (c₀ ^ 2 * u) + (c₁ ^ 2 + 2 * |c₁| * X ^ 2) / (c₀ ^ 2 * u ^ 2) := by
  have hu0 : u ≠ 0 := hu.ne'
  have htabs : |x / u| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hu, div_le_iff₀ hu]; linarith
  have ht1 : x / u < 1 := by linarith [le_abs_self (x / u)]
  have h1t : 0 < 1 - x / u := by linarith
  have hux : u - x = u * (1 - x / u) := by field_simp
  have hlog : Real.log (u - x) = Real.log u + Real.log (1 - x / u) := by
    rw [hux, Real.log_mul hu0 h1t.ne']
  have hE := abs_log_one_sub_add_le_two htabs
  have key : phi c₀ c₁ (u - x) - phi c₀ c₁ u + 1 =
      r / c₀ + c₁ ^ 2 / (c₀ ^ 2 * u ^ 2) - c₁ * r / (c₀ ^ 2 * u) -
        c₁ / c₀ ^ 2 * (Real.log (1 - x / u) + x / u) := by
    unfold phi
    rw [hlog]
    generalize Real.log (1 - x / u) = Lg
    subst hx
    field_simp
    ring
  rw [key]
  set E := Real.log (1 - x / u) + x / u
  have hx2 : (x / u) ^ 2 ≤ X ^ 2 / u ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_right (by nlinarith [abs_nonneg x, sq_abs x]) (by positivity)
  have hc2 : 0 < c₀ ^ 2 := by positivity
  have hEb : |c₁ / c₀ ^ 2 * E| ≤ 2 * |c₁| * X ^ 2 / (c₀ ^ 2 * u ^ 2) := by
    rw [abs_mul, abs_div, abs_of_pos hc2]
    calc |c₁| / c₀ ^ 2 * |E| ≤ |c₁| / c₀ ^ 2 * (2 * (X ^ 2 / u ^ 2)) :=
          mul_le_mul_of_nonneg_left (hE.trans (by linarith)) (by positivity)
      _ = 2 * |c₁| * X ^ 2 / (c₀ ^ 2 * u ^ 2) := by field_simp
  have hr1 : |r / c₀| = |r| / c₀ := by rw [abs_div, abs_of_pos hc₀]
  have hr2 : |c₁ * r / (c₀ ^ 2 * u)| = |c₁| * |r| / (c₀ ^ 2 * u) := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < c₀ ^ 2 * u)]
  have hr3 : |c₁ ^ 2 / (c₀ ^ 2 * u ^ 2)| = c₁ ^ 2 / (c₀ ^ 2 * u ^ 2) :=
    abs_of_nonneg (by positivity)
  have hsplit : (c₁ ^ 2 + 2 * |c₁| * X ^ 2) / (c₀ ^ 2 * u ^ 2) =
      c₁ ^ 2 / (c₀ ^ 2 * u ^ 2) + 2 * |c₁| * X ^ 2 / (c₀ ^ 2 * u ^ 2) := add_div _ _ _
  calc |r / c₀ + c₁ ^ 2 / (c₀ ^ 2 * u ^ 2) - c₁ * r / (c₀ ^ 2 * u) - c₁ / c₀ ^ 2 * E|
      ≤ |r / c₀| + |c₁ ^ 2 / (c₀ ^ 2 * u ^ 2)| + |c₁ * r / (c₀ ^ 2 * u)| + |c₁ / c₀ ^ 2 * E| := by
        have a1 := abs_sub (r / c₀ + c₁ ^ 2 / (c₀ ^ 2 * u ^ 2) - c₁ * r / (c₀ ^ 2 * u)) (c₁ / c₀ ^ 2 * E)
        have a2 := abs_sub (r / c₀ + c₁ ^ 2 / (c₀ ^ 2 * u ^ 2)) (c₁ * r / (c₀ ^ 2 * u))
        have a3 := abs_add_le (r / c₀) (c₁ ^ 2 / (c₀ ^ 2 * u ^ 2))
        linarith
    _ ≤ |r| / c₀ + |c₁| * |r| / (c₀ ^ 2 * u) + (c₁ ^ 2 + 2 * |c₁| * X ^ 2) / (c₀ ^ 2 * u ^ 2) := by
        rw [hr1, hr2, hr3, hsplit]; linarith

/-! ## Summing the steps -/

/-- Telescoping: for `0 < b ≤ a` with `a - b ≥ x_min`, `x_min/a² ≤ 1/b - 1/a`. -/
theorem inv_sq_le_tele {a b xmin : ℝ} (hb : 0 < b) (hab : b ≤ a) (hx : xmin ≤ a - b) :
    xmin / a ^ 2 ≤ 1 / b - 1 / a := by
  have ha : 0 < a := hb.trans_le hab
  rw [div_sub_div _ _ hb.ne' ha.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hab ha.le, mul_pos ha hb]

/-- The constants of the count: `B = (1 + |c₁|/(c₀U))/c₀` multiplies the remainders, `A = B K + (c₁² + 2|c₁|X²)/c₀²`
multiplies `∑ 1/u_j²`. -/
def cB (c₀ c₁ U : ℝ) : ℝ := (1 + |c₁| / (c₀ * U)) / c₀

def cA (c₀ c₁ K X U : ℝ) : ℝ := cB c₀ c₁ U * K + (c₁ ^ 2 + 2 * |c₁| * X ^ 2) / c₀ ^ 2

/-- **The layer count (two loops).** Hypotheses for the layers `j < J`: the inverse coupling stays above the threshold
`U`, each step `x_j = u_j - u_{j+1}` lies in `[x_min, X]` with `0 < x_min`, `2X ≤ U`, and the recursion holds with
`|r_j| = |c₀ + c₁/u_j - x_j| ≤ K/u_j² + η_j`. Then
`|phi(u_J) - phi(u₀) + J| ≤ (A/x_min)(1/u_J - 1/u₀) + B ∑_{j<J} η_j`. -/
theorem count_two_loop {c₀ c₁ K X xmin U : ℝ} (hc₀ : 0 < c₀) (hK : 0 ≤ K) (hxmin : 0 < xmin) (hUX : 2 * X ≤ U)
    (hU : 0 < U) (u η : ℕ → ℝ) (J : ℕ) (hge : ∀ j < J, U ≤ u j)
    (hstep : ∀ j < J, xmin ≤ u j - u (j + 1) ∧ u j - u (j + 1) ≤ X)
    (hr : ∀ j < J, |c₀ + c₁ / u j - (u j - u (j + 1))| ≤ K / u j ^ 2 + η j) :
    |phi c₀ c₁ (u J) - phi c₀ c₁ (u 0) + J| ≤
      cA c₀ c₁ K X U / xmin * (1 / u J - 1 / u 0) + cB c₀ c₁ U * ∑ j ∈ range J, η j := by
  have hB : 0 ≤ cB c₀ c₁ U := div_nonneg (by positivity) hc₀.le
  suffices H : ∀ n ≤ J, |phi c₀ c₁ (u n) - phi c₀ c₁ (u 0) + n| ≤
      cA c₀ c₁ K X U / xmin * (1 / u n - 1 / u 0) + cB c₀ c₁ U * ∑ j ∈ range n, η j from H J le_rfl
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hnJ : n < J := hn
    have ih := ih hnJ.le
    obtain ⟨hs1, hs2⟩ := hstep n hnJ
    have hun : U ≤ u n := hge n hnJ
    have hupos : 0 < u n := hU.trans_le hun
    have hXpos : 0 < X := hxmin.trans_le (hs1.trans hs2)
    have hu1 : 0 < u (n + 1) := by linarith
    -- one step
    have hstep1 := phi_step (c₁ := c₁) (r := c₀ + c₁ / u n - (u n - u (n + 1))) hc₀ hupos
      (abs_le.2 ⟨by linarith, hs2⟩) (by linarith) (by ring)
    rw [show u n - (u n - u (n + 1)) = u (n + 1) by ring] at hstep1
    set r := c₀ + c₁ / u n - (u n - u (n + 1))
    have hrn := hr n hnJ
    -- per-step error ≤ A/u_n² + B η_n
    have hfac : |r| / c₀ + |c₁| * |r| / (c₀ ^ 2 * u n) ≤ cB c₀ c₁ U * |r| := by
      unfold cB
      have h1 : |c₁| / (c₀ * u n) ≤ |c₁| / (c₀ * U) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (mul_le_mul_of_nonneg_left hun hc₀.le)
      have e : |r| / c₀ + |c₁| * |r| / (c₀ ^ 2 * u n) = (1 + |c₁| / (c₀ * u n)) / c₀ * |r| := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) hc₀.le) (abs_nonneg _)
    have hXu : (c₁ ^ 2 + 2 * |c₁| * X ^ 2) / (c₀ ^ 2 * u n ^ 2) =
        (c₁ ^ 2 + 2 * |c₁| * X ^ 2) / c₀ ^ 2 * (1 / u n ^ 2) := by field_simp
    have herr : |phi c₀ c₁ (u (n + 1)) - phi c₀ c₁ (u n) + 1| ≤
        cA c₀ c₁ K X U * (1 / u n ^ 2) + cB c₀ c₁ U * η n := by
      refine hstep1.trans ?_
      rw [hXu]
      have h2 : cB c₀ c₁ U * |r| ≤ cB c₀ c₁ U * (K * (1 / u n ^ 2)) + cB c₀ c₁ U * η n := by
        rw [← mul_add]; refine mul_le_mul_of_nonneg_left (hrn.trans_eq ?_) hB; field_simp
      unfold cA; nlinarith [hfac, h2]
    have htele : 1 / u n ^ 2 ≤ 1 / xmin * (1 / u (n + 1) - 1 / u n) := by
      have := inv_sq_le_tele hu1 (by linarith) hs1
      calc 1 / u n ^ 2 = 1 / xmin * (xmin / u n ^ 2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
    have hA : 0 ≤ cA c₀ c₁ K X U := by unfold cA; positivity
    rw [Finset.sum_range_succ, Nat.cast_succ]
    have e1 : phi c₀ c₁ (u (n + 1)) - phi c₀ c₁ (u 0) + (n + 1 : ℝ) =
        (phi c₀ c₁ (u n) - phi c₀ c₁ (u 0) + n) + (phi c₀ c₁ (u (n + 1)) - phi c₀ c₁ (u n) + 1) := by ring
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    have h3 : cA c₀ c₁ K X U * (1 / u n ^ 2) ≤
        cA c₀ c₁ K X U / xmin * (1 / u (n + 1) - 1 / u n) := by
      calc cA c₀ c₁ K X U * (1 / u n ^ 2) ≤ cA c₀ c₁ K X U * (1 / xmin * (1 / u (n + 1) - 1 / u n)) :=
            mul_le_mul_of_nonneg_left htele hA
        _ = _ := by ring
    have e2 : cA c₀ c₁ K X U / xmin * (1 / u (n + 1) - 1 / u 0) =
        cA c₀ c₁ K X U / xmin * (1 / u n - 1 / u 0) + cA c₀ c₁ K X U / xmin * (1 / u (n + 1) - 1 / u n) := by
      ring
    rw [e2, mul_add]
    linarith [ih, herr, h3]

/-! ## The crossing layer -/

/-- **The crossing layer exists.** If above the threshold `U` every step decreases `u` by at least `x_min > 0`, then
there is a first layer `J` with `u_J < U`, and all earlier layers are `≥ U`. -/
theorem crossing_exists {U xmin : ℝ} (hxmin : 0 < xmin) (u : ℕ → ℝ)
    (hdec : ∀ j, U ≤ u j → u (j + 1) ≤ u j - xmin) :
    ∃ J, u J < U ∧ ∀ j < J, U ≤ u j := by
  have hex : ∃ n, u n < U := by
    by_contra hne
    simp only [not_exists, not_lt] at hne
    have hlin : ∀ n : ℕ, u n ≤ u 0 - n * xmin := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => have := hdec n (hne n); push_cast; linarith
    obtain ⟨n, hn⟩ := exists_nat_gt ((u 0 - U) / xmin)
    have h1 := hlin n
    have h2 := hne n
    rw [div_lt_iff₀ hxmin] at hn
    linarith
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, fun j hj => ?_⟩
  exact not_lt.1 (Nat.find_min hex hj)

/-- The phi values on a bounded window are bounded: for `0 < w₁ ≤ w ≤ w₂`,
`|phi(w)| ≤ w₂/c₀ + |c₁|/c₀² (|log w₁| + |log w₂|)`. -/
theorem abs_phi_le {c₀ c₁ w w₁ w₂ : ℝ} (hc₀ : 0 < c₀) (hw₁ : 0 < w₁) (h1 : w₁ ≤ w) (h2 : w ≤ w₂) :
    |phi c₀ c₁ w| ≤ w₂ / c₀ + |c₁| / c₀ ^ 2 * (|Real.log w₁| + |Real.log w₂|) := by
  have hw : 0 < w := hw₁.trans_le h1
  have hl1 : Real.log w₁ ≤ Real.log w := Real.log_le_log hw₁ h1
  have hl2 : Real.log w ≤ Real.log w₂ := Real.log_le_log hw h2
  have hlog : |Real.log w| ≤ |Real.log w₁| + |Real.log w₂| := by
    rw [abs_le]; constructor
    · linarith [neg_abs_le (Real.log w₁), abs_nonneg (Real.log w₂)]
    · linarith [le_abs_self (Real.log w₂), abs_nonneg (Real.log w₁)]
  unfold phi
  have hc2 : 0 < c₀ ^ 2 := by positivity
  calc |w / c₀ - c₁ / c₀ ^ 2 * Real.log w| ≤ |w / c₀| + |c₁ / c₀ ^ 2 * Real.log w| := abs_sub _ _
    _ = w / c₀ + |c₁| / c₀ ^ 2 * |Real.log w| := by
        rw [abs_of_pos (div_pos hw hc₀), abs_mul, abs_div, abs_of_pos hc2]
    _ ≤ w₂ / c₀ + |c₁| / c₀ ^ 2 * (|Real.log w₁| + |Real.log w₂|) := by
        gcongr

/-- **Asymptotic scaling of the scale-setting layer (exact coefficients).** Let `J_p ≤ J_t` with: the two-loop count
hypotheses on the layers `j < J_p` (threshold `U`), the crossing `u_{J_p} < U`, and at most `N` further layers
`J_t - J_p ≤ N` (the non-perturbative stretch from `U` down to the target value). Then
`|J_t - phi(u₀)| ≤ N + M`, with `M` depending only on `c₀, c₁, K, X, x_min, U` and `∑ η` (**not on `u₀`**). -/
theorem scaling_window {c₀ c₁ K X xmin U H : ℝ} (hc₀ : 0 < c₀) (hK : 0 ≤ K) (hxmin : 0 < xmin)
    (hUX : 2 * X ≤ U) (hU : 0 < U) (u η : ℕ → ℝ)
    (hH : ∀ n, ∑ j ∈ range n, η j ≤ H) (Jp Jt N : ℕ) (hJp0 : 0 < Jp) (hge : ∀ j < Jp, U ≤ u j)
    (hstep : ∀ j < Jp, xmin ≤ u j - u (j + 1) ∧ u j - u (j + 1) ≤ X)
    (hr : ∀ j < Jp, |c₀ + c₁ / u j - (u j - u (j + 1))| ≤ K / u j ^ 2 + η j)
    (hcross : u Jp < U) (hJt : Jp ≤ Jt) (hN : Jt - Jp ≤ N) :
    |(Jt : ℝ) - phi c₀ c₁ (u 0)| ≤ N + (cA c₀ c₁ K X U / xmin * (1 / (U - X)) + cB c₀ c₁ U * H +
      (U / c₀ + |c₁| / c₀ ^ 2 * (|Real.log (U - X)| + |Real.log U|))) := by
  have hcount := count_two_loop hc₀ hK hxmin hUX hU u η Jp hge hstep hr
  have hXpos : 0 < X := by
    obtain ⟨h1, h2⟩ := hstep 0 hJp0; linarith
  -- `u_{J_p} ∈ [U - X, U)`
  obtain ⟨_, hs2⟩ := hstep (Jp - 1) (Nat.sub_lt hJp0 one_pos)
  have hprev := hge (Jp - 1) (Nat.sub_lt hJp0 one_pos)
  have e1 : Jp - 1 + 1 = Jp := Nat.sub_add_cancel hJp0
  rw [e1] at hs2
  have hlow : U - X ≤ u Jp := by linarith
  have hUXpos : 0 < U - X := by linarith
  have hupos : 0 < u Jp := hUXpos.trans_le hlow
  have hu0 : 0 < u 0 := hU.trans_le (hge 0 hJp0)
  have hinv : 1 / u Jp - 1 / u 0 ≤ 1 / (U - X) := by
    have : 1 / u Jp ≤ 1 / (U - X) := one_div_le_one_div_of_le hUXpos hlow
    have : 0 < 1 / u 0 := by positivity
    linarith
  have hA : 0 ≤ cA c₀ c₁ K X U := by unfold cA cB; positivity
  have hB : 0 ≤ cB c₀ c₁ U := by unfold cB; positivity
  have hc1 : cA c₀ c₁ K X U / xmin * (1 / u Jp - 1 / u 0) ≤ cA c₀ c₁ K X U / xmin * (1 / (U - X)) :=
    mul_le_mul_of_nonneg_left hinv (div_nonneg hA hxmin.le)
  have hc2 : cB c₀ c₁ U * ∑ j ∈ range Jp, η j ≤ cB c₀ c₁ U * H := mul_le_mul_of_nonneg_left (hH Jp) hB
  have hphi := abs_phi_le (c₁ := c₁) hc₀ hUXpos hlow hcross.le
  have hJ : |(Jp : ℝ) - phi c₀ c₁ (u 0)| ≤ cA c₀ c₁ K X U / xmin * (1 / (U - X)) + cB c₀ c₁ U * H +
      (U / c₀ + |c₁| / c₀ ^ 2 * (|Real.log (U - X)| + |Real.log U|)) := by
    have e : (Jp : ℝ) - phi c₀ c₁ (u 0) = (phi c₀ c₁ (u Jp) - phi c₀ c₁ (u 0) + Jp) - phi c₀ c₁ (u Jp) := by ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    linarith
  have hd : ((Jt : ℝ) - Jp) ≤ N := by
    have : Jt - Jp + Jp = Jt := Nat.sub_add_cancel hJt
    have h' : ((Jt - Jp : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    rw [Nat.cast_sub hJt] at h'
    exact h'
  have hJt' : (Jp : ℝ) ≤ Jt := by exact_mod_cast hJt
  have hd0 : (0 : ℝ) ≤ (Jt : ℝ) - Jp := by linarith
  have e : (Jt : ℝ) - phi c₀ c₁ (u 0) = ((Jt : ℝ) - Jp) + ((Jp : ℝ) - phi c₀ c₁ (u 0)) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg hd0]
  linarith

/-! ## Sharpness: the two-loop coefficient must be exact -/

/-- Two scale functions with different two-loop coefficients drift apart like `log u`. -/
theorem phi_sub {c₀ c₁ c₁' u : ℝ} : phi c₀ c₁ u - phi c₀ c₁' u = (c₁' - c₁) / c₀ ^ 2 * Real.log u := by
  unfold phi; ring

theorem phi_diff_tendsto {c₀ c₁ c₁' : ℝ} (hc₀ : 0 < c₀) (hne : c₁ ≠ c₁') :
    Tendsto (fun u => |phi c₀ c₁ u - phi c₀ c₁' u|) atTop atTop := by
  simp_rw [phi_sub, abs_mul]
  have hpos : 0 < |(c₁' - c₁) / c₀ ^ 2| := abs_pos.2 (div_ne_zero (sub_ne_zero.2 hne.symm) (by positivity))
  refine Tendsto.const_mul_atTop hpos ?_
  exact tendsto_abs_atTop_atTop.comp Real.tendsto_log_atTop

/-- **Sharpness.** If the scale-setting layers `J_k` stay within `W` of `phi_{c₀,c₁}(u_k)` (`scaling_window`) and
`u_k → ∞`, then for any other two-loop coefficient `c₁' ≠ c₁` the distance `|J_k - phi_{c₀,c₁'}(u_k)|` is unbounded:
an asymptotic-scaling law with a wrong two-loop coefficient puts the scale-setting layer at an unbounded physical
scale. -/
theorem scaling_drift {c₀ c₁ c₁' W : ℝ} (hc₀ : 0 < c₀) (hne : c₁ ≠ c₁') (u : ℕ → ℝ) (J : ℕ → ℕ)
    (hu : Tendsto u atTop atTop) (hW : ∀ k, |(J k : ℝ) - phi c₀ c₁ (u k)| ≤ W) :
    Tendsto (fun k => |(J k : ℝ) - phi c₀ c₁' (u k)|) atTop atTop := by
  have hd := (phi_diff_tendsto hc₀ hne).comp hu
  refine tendsto_atTop_mono (fun k => ?_) (tendsto_atTop_add_const_right _ (-W) hd)
  simp only [Function.comp]
  have h1 := hW k
  have : |phi c₀ c₁ (u k) - phi c₀ c₁' (u k)| ≤ |(J k : ℝ) - phi c₀ c₁ (u k)| + |(J k : ℝ) - phi c₀ c₁' (u k)| := by
    have e : phi c₀ c₁ (u k) - phi c₀ c₁' (u k) =
        -((J k : ℝ) - phi c₀ c₁ (u k)) + ((J k : ℝ) - phi c₀ c₁' (u k)) := by ring
    rw [e]; exact (abs_add_le _ _).trans (by rw [abs_neg])
  linarith

/-! ## Photon test -/

/-- If the inverse coupling never decreases by more than the artefacts (`u_j - u_{j+1} ≤ η_j`: zero running, or
screening), then `u_n ≥ u₀ - ∑_{j<n} η_j`. -/
theorem floor_of_steps (u η : ℕ → ℝ) (h : ∀ j, u j - u (j + 1) ≤ η j) (n : ℕ) :
    u 0 - ∑ j ∈ range n, η j ≤ u n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ]; linarith [h n]

/-- **Photon test.** With no running and summable artefacts (`∑ η ≤ H`), a coupling that starts weak
(`u₀ > u* + H`) never reaches the value `u*` at any layer. -/
theorem photon_never_reaches {H ustar : ℝ} (u η : ℕ → ℝ) (h : ∀ j, u j - u (j + 1) ≤ η j)
    (hH : ∀ n, ∑ j ∈ range n, η j ≤ H) (h0 : ustar + H < u 0) (n : ℕ) : ustar < u n := by
  have := floor_of_steps u η h n
  linarith [hH n]

end Attempts.R2
