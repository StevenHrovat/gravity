/-
The one-scale reduction, Theorem C (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/PROOF-NOTE.md`, §6.3 (Lemma 6.2), §6.4 (Theorem C), §6.5 (Corollary C1).
-/

import Mathlib

/-!
# Doubling and the prefactor-free limit (real analysis)

* `doubling` (**Lemma 6.2**): if `H(j + k)² ≤ H(2j) H(2k)` and `H(2j) ≥ 0` for `j, k ≤ K` (Cauchy–Schwarz for a
  reflection-positive form with Hankel structure), then for `r ≥ 1` and `2^{r-1} m ≤ K`:
  `|H(m)| ≤ H(0)^{1 - 2^{-r}} · H(2^r m)^{2^{-r}}`.
* `doubling_decay` (**Theorem C**, abstract): if moreover `|H(2^r m)| ≤ C e^{-λ 2^r m}`, then
  `|H(m)| ≤ H(0)^{1 - 2^{-r}} · C^{2^{-r}} · e^{-λ m}`.
* `prefactor_free` (**Corollary C1**): if `a_k → a`, `b_k → b`, `a_k ≥ 0`, and for every `r ≥ 1` eventually
  `|b_k| ≤ a_k^{1 - 2^{-r}} C^{2^{-r}} E`, then `|b| ≤ a E`. Applied with `a_k = H_{N_k}(0)`, `b_k = H_{N_k}(m)`,
  `E = e^{-λ m}`: `|h(m)| ≤ h(0) e^{-λ m}` for limit points, with no prefactor.

The doubling argument for reflection-positive correlations is standard (Osterwalder–Seiler 1978; Glimm–Jaffe ch. 6, 10).
Formalised here from scratch.
-/

open Real Filter Topology

noncomputable section

namespace OneScale

/-- **Lemma 6.2 (doubling).** -/
theorem doubling {H : ℕ → ℝ} {K : ℕ}
    (hcs : ∀ j k, j ≤ K → k ≤ K → H (j + k) ^ 2 ≤ H (2 * j) * H (2 * k))
    (hpos : ∀ j, j ≤ K → 0 ≤ H (2 * j)) {m : ℕ} :
    ∀ r : ℕ, 1 ≤ r → 2 ^ (r - 1) * m ≤ K →
      |H m| ≤ H 0 ^ (1 - (1 / 2 : ℝ) ^ r) * H (2 ^ r * m) ^ ((1 / 2 : ℝ) ^ r) := by
  have hH0 : 0 ≤ H 0 := by simpa using hpos 0 (Nat.zero_le _)
  -- one Cauchy–Schwarz step from `0` to `k`: `H k ≤ (H 0 · H (2k))^{1/2}`
  have step : ∀ k, k ≤ K → |H k| ≤ (H 0 * H (2 * k)) ^ (1 / 2 : ℝ) := by
    intro k hk
    have h := hcs 0 k (Nat.zero_le _) hk
    simp only [zero_add, mul_zero] at h
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    intro hmK
    simp only [pow_one, Nat.sub_self, pow_zero, one_mul] at hmK ⊢
    have := step m hmK
    rw [Real.mul_rpow hH0 (hpos m hmK)] at this
    norm_num at this ⊢
    exact this
  | succ r hr ih =>
    intro hmK
    have hr1 : 2 ^ (r - 1) * m ≤ 2 ^ r * m := by
      apply Nat.mul_le_mul_right
      exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    have hrK : 2 ^ r * m ≤ K := by simpa using hmK
    have hIH := ih (hr1.trans hrK)
    set a : ℝ := (1 / 2 : ℝ) ^ r
    have ha0 : 0 ≤ a := by positivity
    have ha1 : a ≤ 1 / 2 := by
      have : (1 / 2 : ℝ) ^ r ≤ (1 / 2 : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hr
      simpa [a] using this
    -- `H(2^r m) ≥ 0` and `H(2^{r+1} m) ≥ 0`
    have hpos_r : 0 ≤ H (2 ^ r * m) := by
      have := hpos (2 ^ (r - 1) * m) (hr1.trans hrK)
      have e : 2 * (2 ^ (r - 1) * m) = 2 ^ r * m := by
        rw [← mul_assoc, ← pow_succ']; congr 2; omega
      rwa [e] at this
    have hpos_r1 : 0 ≤ H (2 ^ (r + 1) * m) := by
      have := hpos (2 ^ r * m) hrK
      rwa [← mul_assoc, ← pow_succ'] at this
    have hs := step (2 ^ r * m) hrK
    rw [← mul_assoc, ← pow_succ', abs_of_nonneg hpos_r] at hs
    -- raise to the power `a`
    have hs' : H (2 ^ r * m) ^ a ≤ H 0 ^ (a / 2) * H (2 ^ (r + 1) * m) ^ (a / 2) := by
      calc H (2 ^ r * m) ^ a ≤ ((H 0 * H (2 ^ (r + 1) * m)) ^ (1 / 2 : ℝ)) ^ a :=
            Real.rpow_le_rpow hpos_r hs ha0
        _ = H 0 ^ (a / 2) * H (2 ^ (r + 1) * m) ^ (a / 2) := by
            rw [← Real.rpow_mul (mul_nonneg hH0 hpos_r1), Real.mul_rpow hH0 hpos_r1]
            congr 2 <;> ring
    calc |H m| ≤ H 0 ^ (1 - a) * H (2 ^ r * m) ^ a := hIH
      _ ≤ H 0 ^ (1 - a) * (H 0 ^ (a / 2) * H (2 ^ (r + 1) * m) ^ (a / 2)) :=
          mul_le_mul_of_nonneg_left hs' (Real.rpow_nonneg hH0 _)
      _ = H 0 ^ (1 - a + a / 2) * H (2 ^ (r + 1) * m) ^ (a / 2) := by
          rw [Real.rpow_add' hH0 (by linarith)]; ring
      _ = H 0 ^ (1 - (1 / 2 : ℝ) ^ (r + 1)) * H (2 ^ (r + 1) * m) ^ ((1 / 2 : ℝ) ^ (r + 1)) := by
          congr 2 <;> simp only [a, pow_succ] <;> ring

/-- **Theorem C (abstract form).** Doubling plus a decay bound at the doubled distance `2^r m`. -/
theorem doubling_decay {H : ℕ → ℝ} {K : ℕ}
    (hcs : ∀ j k, j ≤ K → k ≤ K → H (j + k) ^ 2 ≤ H (2 * j) * H (2 * k))
    (hpos : ∀ j, j ≤ K → 0 ≤ H (2 * j)) {m r : ℕ} (hr : 1 ≤ r) (hmK : 2 ^ (r - 1) * m ≤ K)
    {C lam : ℝ} (hC : 0 ≤ C) (hdecay : |H (2 ^ r * m)| ≤ C * Real.exp (-(lam * (2 ^ r * m : ℕ)))) :
    |H m| ≤ H 0 ^ (1 - (1 / 2 : ℝ) ^ r) * C ^ ((1 / 2 : ℝ) ^ r) * Real.exp (-(lam * m)) := by
  have hH0 : 0 ≤ H 0 := by simpa using hpos 0 (Nat.zero_le _)
  have hd := doubling hcs hpos r hr hmK
  set a : ℝ := (1 / 2 : ℝ) ^ r
  have ha0 : 0 ≤ a := by positivity
  have hHr : 0 ≤ H (2 ^ r * m) := by
    have := hpos (2 ^ (r - 1) * m) hmK
    have e : 2 * (2 ^ (r - 1) * m) = 2 ^ r * m := by
      rw [← mul_assoc, ← pow_succ']; congr 2; omega
    rwa [e] at this
  rw [abs_of_nonneg hHr] at hdecay
  have h2 : H (2 ^ r * m) ^ a ≤ C ^ a * Real.exp (-(lam * m)) := by
    calc H (2 ^ r * m) ^ a ≤ (C * Real.exp (-(lam * (2 ^ r * m : ℕ)))) ^ a :=
          Real.rpow_le_rpow hHr hdecay ha0
      _ = C ^ a * Real.exp (-(lam * m)) := by
          rw [Real.mul_rpow hC (Real.exp_pos _).le, ← Real.exp_mul]
          congr 2
          simp only [a]
          push_cast
          rw [show (-(lam * (2 ^ r * (m : ℝ)))) * (1 / 2 : ℝ) ^ r = -(lam * m) * ((2 : ℝ) ^ r * (1 / 2) ^ r) by ring,
            ← mul_pow]
          norm_num
  calc |H m| ≤ H 0 ^ (1 - a) * H (2 ^ r * m) ^ a := hd
    _ ≤ H 0 ^ (1 - a) * (C ^ a * Real.exp (-(lam * m))) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hH0 _)
    _ = _ := by ring

/-- **Corollary C1 (prefactor-free limit).** -/
theorem prefactor_free {a b : ℕ → ℝ} {a₀ b₀ : ℝ} (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀))
    (ha0 : ∀ k, 0 ≤ a k) {C E : ℝ} (hE : 0 ≤ E)
    (h : ∀ r : ℕ, 1 ≤ r → ∀ᶠ k in atTop, |b k| ≤ a k ^ (1 - (1 / 2 : ℝ) ^ r) * C ^ ((1 / 2 : ℝ) ^ r) * E) :
    |b₀| ≤ a₀ * E := by
  have ha₀ : 0 ≤ a₀ := ge_of_tendsto' ha ha0
  -- at fixed `r`, pass to the limit in `k`
  have hr : ∀ r : ℕ, 1 ≤ r → |b₀| ≤ a₀ ^ (1 - (1 / 2 : ℝ) ^ r) * C ^ ((1 / 2 : ℝ) ^ r) * E := by
    intro r hr1
    have hp : 0 ≤ 1 - (1 / 2 : ℝ) ^ r := by
      have : (1 / 2 : ℝ) ^ r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    have hlim : Tendsto (fun k => a k ^ (1 - (1 / 2 : ℝ) ^ r) * C ^ ((1 / 2 : ℝ) ^ r) * E) atTop
        (𝓝 (a₀ ^ (1 - (1 / 2 : ℝ) ^ r) * C ^ ((1 / 2 : ℝ) ^ r) * E)) :=
      ((ha.rpow_const (Or.inr hp)).mul_const _).mul_const _
    exact le_of_tendsto_of_tendsto hb.abs hlim (h r hr1)
  -- degenerate cases: the bound at `r = 1` is `0`
  by_cases hdeg : C = 0 ∨ a₀ = 0
  · have h1 := hr 1 le_rfl
    have hz : a₀ ^ (1 - (1 / 2 : ℝ) ^ 1) * C ^ ((1 / 2 : ℝ) ^ 1) = 0 := by
      rcases hdeg with h0 | h0
      · rw [h0, Real.zero_rpow (by norm_num), mul_zero]
      · rw [h0, Real.zero_rpow (by norm_num), zero_mul]
    rw [hz, zero_mul] at h1
    exact h1.trans (mul_nonneg ha₀ hE)
  push Not at hdeg
  obtain ⟨hC0, ha0'⟩ := hdeg
  -- let `r → ∞`
  have hq : Tendsto (fun r : ℕ => (1 / 2 : ℝ) ^ r) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hA : Tendsto (fun r : ℕ => a₀ ^ (1 - (1 / 2 : ℝ) ^ r)) atTop (𝓝 (a₀ ^ (1 - (0 : ℝ)))) :=
    ((Real.continuousAt_const_rpow ha0').tendsto).comp (tendsto_const_nhds.sub hq)
  have hCt : Tendsto (fun r : ℕ => C ^ ((1 / 2 : ℝ) ^ r)) atTop (𝓝 (C ^ (0 : ℝ))) :=
    ((Real.continuousAt_const_rpow hC0).tendsto).comp hq
  have hlim : Tendsto (fun r : ℕ => a₀ ^ (1 - (1 / 2 : ℝ) ^ r) * C ^ ((1 / 2 : ℝ) ^ r) * E) atTop
      (𝓝 (a₀ ^ (1 - (0 : ℝ)) * C ^ (0 : ℝ) * E)) := (hA.mul hCt).mul_const E
  rw [sub_zero, Real.rpow_one, Real.rpow_zero, mul_one] at hlim
  exact ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun r hr1 => hr r hr1⟩)

end OneScale
