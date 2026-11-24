/-
Attempt r3-monotone (round 3, attempt 2), 2026-11-21. Released under Apache 2.0.

# From "no fixed point" to "the coupling reaches order one in a bounded number of doublings"

Note: `docs/mass-gap/weak-coupling/attempts/r3-monotone/NOTE.md`, sections 2 and 6.

Notation as in attempt D (`Attempts/R2/StepScaling.lean`): `u j` is an inverse coupling of the box of side `2^j ℓ₀` (large = weak
coupling), `σ` a step-scaling function (`u (j+1) = σ (u j)` up to lattice artefacts), `a` the target value `u*` (α_s = α*), `b` the
upper end of the crossover stretch (where perturbative bookkeeping, attempt D's `count_two_loop`, hands over).

What is proved:
1. `uniform_decrement`: a continuous step-scaling function with **no fixed point** on the compact stretch `[a, b]` (`σ u < u`) lowers
   the inverse coupling by a **uniform** `δ > 0` per doubling there (compactness).
2. `crossing_within`: a uniform decrement brings every start `u 0 ≤ b` below `a` within `⌈(b − a)/δ⌉ + 1` doublings.
3. `reach_of_noFixedPoint`: 1 and 2 together, with lattice artefacts `η j ≤ δ/2`: the number of doublings through the crossover is
   bounded uniformly in the starting point and in the sequence. This is hypothesis (ii)(c) of attempt D in quantitative form.
4. `monotone_not_enough`: monotone running alone (`u (j+1) ≤ u j`) does **not** give a crossing (a frozen coupling, the photon's
   case, is monotone).
5. `dual_dual`: the 't Hooft duality map `F ↦ −log((1 − e^{−F})/(1 + e^{−F}))` between the magnetic (twist) and the electric flux
   free energies is an involution, and it reverses order (`dual_strictAntiOn`): "the twist free energy decreases" and "the electric
   flux free energy increases" are the same statement.
6. `grid_certificate`: a Lipschitz bound plus a `2δ` decrement at finitely many grid points (spacing `h`, `(K + 1)h ≤ δ`) gives the
   uniform decrement `δ` of item 1: the form in which numbers (certified step-scaling values) could enter.
-/

import Mathlib

namespace Attempts.R3.Monotone

open Set

/-- No fixed point on a compact stretch gives a uniform decrement (compactness). -/
theorem uniform_decrement {σ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hσ : ContinuousOn σ (Icc a b))
    (hnf : ∀ u ∈ Icc a b, σ u < u) : ∃ δ > 0, ∀ u ∈ Icc a b, σ u ≤ u - δ := by
  have hc : ContinuousOn (fun u => u - σ u) (Icc a b) := continuousOn_id.sub hσ
  obtain ⟨u0, hu0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hc
  refine ⟨u0 - σ u0, by linarith [hnf u0 hu0], fun u hu => ?_⟩
  have h := hmin hu
  simp only [Set.mem_ofPred_eq] at h
  linarith

/-- A uniform decrement on `[a, b]` brings every start `u 0 ≤ b` below `a` within `⌈(b − a)/δ⌉ + 1` steps. -/
theorem crossing_within {u : ℕ → ℝ} {a b δ : ℝ} (hδ : 0 < δ) (h0 : u 0 ≤ b)
    (hstep : ∀ j, a ≤ u j → u j ≤ b → u (j + 1) ≤ u j - δ) :
    ∃ J, J ≤ ⌈(b - a) / δ⌉₊ + 1 ∧ u J < a := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have key : ∀ j : ℕ, j ≤ ⌈(b - a) / δ⌉₊ + 1 → u j ≤ b - j * δ := by
    intro j
    induction j with
    | zero => intro _; simpa using h0
    | succ k ih =>
      intro hk
      have hk' : k ≤ ⌈(b - a) / δ⌉₊ + 1 := Nat.le_of_succ_le hk
      have hu := ih hk'
      have ha := hcon k hk'
      have hkδ : (0 : ℝ) ≤ k * δ := by positivity
      have hb : u k ≤ b := by linarith
      have hs := hstep k ha hb
      push_cast
      linarith
  have h1 := key _ le_rfl
  have h2 := hcon _ le_rfl
  have h3 : (b - a) / δ ≤ (⌈(b - a) / δ⌉₊ : ℝ) := Nat.le_ceil _
  have h4 : (b - a) / δ * δ = b - a := by field_simp
  have h5 : ((⌈(b - a) / δ⌉₊ + 1 : ℕ) : ℝ) * δ > b - a := by
    push_cast
    nlinarith
  linarith

/-- **No fixed point ⇒ bounded crossing, artefacts included.** If the step-scaling function is continuous and has no fixed point
on `[a, b]`, there is `δ > 0` such that every inverse-coupling sequence that follows `σ` up to artefacts `η j ≤ δ/2` while in
`[a, b]`, and starts at most at `b`, falls below `a` within `⌈(b − a)/(δ/2)⌉ + 1` doublings. The bound does not depend on the
sequence (uniform in the bare coupling). -/
theorem reach_of_noFixedPoint {σ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hσ : ContinuousOn σ (Icc a b))
    (hnf : ∀ u ∈ Icc a b, σ u < u) :
    ∃ δ > 0, ∀ (u η : ℕ → ℝ), (∀ j, η j ≤ δ / 2) → u 0 ≤ b →
      (∀ j, a ≤ u j → u j ≤ b → u (j + 1) ≤ σ (u j) + η j) →
      ∃ J, J ≤ ⌈(b - a) / (δ / 2)⌉₊ + 1 ∧ u J < a := by
  obtain ⟨δ, hδ, hdec⟩ := uniform_decrement hab hσ hnf
  refine ⟨δ, hδ, fun u η hη h0 hstep => crossing_within (by linarith) h0 (fun j ha hb => ?_)⟩
  have := hstep j ha hb
  have := hdec (u j) ⟨ha, hb⟩
  linarith [hη j]

/-- **A finite certificate suffices.** If `σ` is `K`-Lipschitz on `[a, b]` and, at grid points `g i ∈ [a, b]` that come within `h`
of every point of `[a, b]`, it lowers the inverse coupling by `2δ`, with `(K + 1) h ≤ δ`, then it lowers it by `δ` on all of
`[a, b]`. So finitely many certified step-scaling values plus a Lipschitz bound give the uniform decrement of
`reach_of_noFixedPoint` (with `crossing_within`). -/
theorem grid_certificate {σ : ℝ → ℝ} {a b K h δ : ℝ} {ι : Type*} (g : ι → ℝ)
    (hLip : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |σ u - σ v| ≤ K * |u - v|)
    (hg : ∀ i, g i ∈ Icc a b) (hcov : ∀ u ∈ Icc a b, ∃ i, |u - g i| ≤ h)
    (hcert : ∀ i, σ (g i) ≤ g i - 2 * δ) (hK : 0 ≤ K) (hh : (K + 1) * h ≤ δ) :
    ∀ u ∈ Icc a b, σ u ≤ u - δ := by
  intro u hu
  obtain ⟨i, hi⟩ := hcov u hu
  have h1 := hLip u hu (g i) (hg i)
  have h2 := hcert i
  have h3 : σ u - σ (g i) ≤ K * |u - g i| := le_trans (le_abs_self _) h1
  have h4 : K * |u - g i| ≤ K * h := mul_le_mul_of_nonneg_left hi hK
  have h5 : g i - u ≤ |u - g i| := by rw [abs_sub_comm]; exact le_abs_self _
  nlinarith

/-- **Monotone running is not enough.** For every `a ≤ b` there is a non-increasing inverse-coupling sequence starting at `b`
that never falls below `a` (a frozen coupling: the photon, or an infrared fixed point). -/
theorem monotone_not_enough {a b : ℝ} (hab : a ≤ b) :
    ∃ u : ℕ → ℝ, u 0 = b ∧ (∀ j, u (j + 1) ≤ u j) ∧ ∀ j, a ≤ u j :=
  ⟨fun _ => b, rfl, fun _ => le_rfl, fun _ => hab⟩

/-! ## The 't Hooft duality between magnetic and electric flux free energies -/

/-- `dual F = −log((1 − e^{−F})/(1 + e^{−F})) = −log tanh(F/2)`. With `F_m = −log(Z_tw/Z)` and a single twist direction,
`F_e = dual F_m` is the electric flux free energy `−log(Z_e(1)/Z_e(0))`, `Z_e(1), Z_e(0) = (Z ∓ Z_tw)/2`. -/
noncomputable def dual (x : ℝ) : ℝ := -Real.log ((1 - Real.exp (-x)) / (1 + Real.exp (-x)))

theorem dual_ratio_pos {x : ℝ} (hx : 0 < x) : 0 < (1 - Real.exp (-x)) / (1 + Real.exp (-x)) := by
  have ht1 : Real.exp (-x) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  exact div_pos (by linarith) (by linarith [Real.exp_pos (-x)])

theorem dual_ratio_lt_one {x : ℝ} : (1 - Real.exp (-x)) / (1 + Real.exp (-x)) < 1 := by
  have ht : 0 < Real.exp (-x) := Real.exp_pos _
  rw [div_lt_one (by linarith)]
  linarith

theorem dual_pos {x : ℝ} (hx : 0 < x) : 0 < dual x := by
  unfold dual
  have := Real.log_neg (dual_ratio_pos hx) dual_ratio_lt_one
  linarith

/-- The duality is an involution on `(0, ∞)`. -/
theorem dual_dual {x : ℝ} (hx : 0 < x) : dual (dual x) = x := by
  have hs := dual_ratio_pos hx
  set t := Real.exp (-x) with htdef
  have ht : 0 < t := Real.exp_pos _
  set s := (1 - t) / (1 + t) with hsdef
  have hdual : dual x = -Real.log s := rfl
  have hexp : Real.exp (-dual x) = s := by rw [hdual, neg_neg, Real.exp_log hs]
  have hst : (1 - s) / (1 + s) = t := by
    rw [hsdef]
    have h1 : (1 + t) ≠ 0 := by linarith
    field_simp
    ring
  have hdd : dual (dual x) = -Real.log ((1 - Real.exp (-dual x)) / (1 + Real.exp (-dual x))) := rfl
  rw [hdd, hexp, hst, htdef, Real.log_exp, neg_neg]

/-- The duality reverses order: a decreasing twist free energy is an increasing electric flux free energy. -/
theorem dual_strictAntiOn : StrictAntiOn dual (Ioi 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  unfold dual
  rw [neg_lt_neg_iff]
  apply Real.log_lt_log (dual_ratio_pos hx)
  have hex : Real.exp (-y) < Real.exp (-x) := Real.exp_lt_exp.mpr (by linarith)
  have hx0 : 0 < Real.exp (-x) := Real.exp_pos _
  have hy0 : 0 < Real.exp (-y) := Real.exp_pos _
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end Attempts.R3.Monotone
