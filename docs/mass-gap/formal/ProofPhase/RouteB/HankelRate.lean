/-
Proof phase, workstream 2 (Route B): the decay rate of a reflection-positive time correlation (2026-11-22).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/ws2-routeB/NOTE.md`, section 1.
-/

import Mathlib

/-!
# Effective masses and the decay rate of a reflection-positive Hankel sequence (real analysis)

A time correlation `h(t) = ⟨F_t, Θ F⟩` of a reflection-positive, time-translation invariant measure has the Hankel
Cauchy–Schwarz structure `h(j + k)² ≤ h(2j) h(2k)`, `h(2j) ≥ 0`, and it is bounded (`RPSeq`). This file proves, for every
such sequence, the facts that make "the energy of the lowest state the observable creates" a well-defined number:

* `RPSeq.logconvex`: the even subsequence `g(s) = h(2s)` is log-convex.
* `RPSeq.eq_zero_of_le`: if `g(s₀) = 0` then `h(t) = 0` for all `t ≥ 2 s₀` (the "infinite energy" alternative).
* For `g > 0` (the other alternative), with the **effective mass** `m(s) = (log g(s) − log g(s+1))/2`:
  `effMass_antitone` (effective masses decrease), `effMass_nonneg` (they stay `≥ 0`; this uses boundedness),
  `tendsto_effMass` (they converge to the **rate** `E = inf_s m(s) ≥ 0`, `rate_nonneg`), `rate_le_effMass`
  (every effective mass is an upper bound for `E`: effective masses approach from above).
* `abs_le_rate`: **the no-prefactor bound** `|h(t)| ≤ h(0) e^{−E t}` for every `t`.
* `lower_effMass`, `rate_sharp`: `g(s) ≥ g(0) e^{−2 m(0) s}`, and for every `ε > 0` eventually
  `g(s) ≥ g(s₀) e^{−2(E+ε)(s−s₀)}`: `E` is the exact exponential rate.
* `rpSeq_of_limit`: pointwise limits of finite-range Hankel families (the time extent going to infinity) are `RPSeq`.
* `exists_limit`: every uniformly bounded family of sequences has a pointwise convergent subsequence.

**Claim discipline.** All statements are real analysis about sequences: they hold for the time correlations of every
reflection-positive, time-translation invariant system (any group, any coupling, U(1) and Z₂ included). Nothing here is
Yang–Mills-specific and nothing here says `E > 0`; it is the machinery that makes `E` a well-defined, RP-controlled
number (used in `ProofPhase.RouteB.FluxEnergy` for the real 4D SU(2) Wilson measure).
-/

open Real Filter Topology Finset

noncomputable section

namespace ProofPhase.RouteB

/-- **A reflection-positive Hankel sequence**: Hankel Cauchy–Schwarz on all of `ℕ`, nonnegative even terms, bounded. -/
structure RPSeq (h : ℕ → ℝ) : Prop where
  cs : ∀ j k, h (j + k) ^ 2 ≤ h (2 * j) * h (2 * k)
  nonneg : ∀ j, 0 ≤ h (2 * j)
  bdd : ∃ C, ∀ t, |h t| ≤ C

/-- The effective mass at even time `2s`: `m(s) = (log h(2s) − log h(2s+2))/2`. -/
def effMass (h : ℕ → ℝ) (s : ℕ) : ℝ := (Real.log (h (2 * s)) - Real.log (h (2 * (s + 1)))) / 2

/-- The decay rate: the infimum of the effective masses. -/
def rate (h : ℕ → ℝ) : ℝ := ⨅ s, effMass h s

namespace RPSeq

variable {h : ℕ → ℝ} (H : RPSeq h)
include H

theorem logconvex (s : ℕ) : h (2 * (s + 1)) ^ 2 ≤ h (2 * s) * h (2 * (s + 2)) := by
  have := H.cs s (s + 2)
  rwa [show s + (s + 2) = 2 * (s + 1) by ring] at this

theorem odd_sq (s : ℕ) : h (2 * s + 1) ^ 2 ≤ h (2 * s) * h (2 * (s + 1)) := by
  have := H.cs s (s + 1)
  rwa [show s + (s + 1) = 2 * s + 1 by ring] at this

theorem zero_succ {s : ℕ} (h0 : h (2 * s) = 0) : h (2 * (s + 1)) = 0 := by
  have := H.logconvex s
  rw [h0, zero_mul] at this
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg _))

theorem zero_add' {s : ℕ} (h0 : h (2 * s) = 0) (n : ℕ) : h (2 * (s + n)) = 0 := by
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [← add_assoc]; exact H.zero_succ ih

/-- **The "infinite energy" alternative**: once an even term vanishes, the sequence vanishes from there on. -/
theorem eq_zero_of_le {s : ℕ} (h0 : h (2 * s) = 0) {t : ℕ} (ht : 2 * s ≤ t) : h t = 0 := by
  obtain ⟨u, hu⟩ := Nat.even_or_odd' t
  rcases hu with rfl | rfl
  · obtain ⟨n, rfl⟩ : ∃ n, u = s + n := ⟨u - s, by omega⟩
    exact H.zero_add' h0 n
  · obtain ⟨n, rfl⟩ : ∃ n, u = s + n := ⟨u - s, by omega⟩
    have h1 := H.odd_sq (s + n)
    rw [H.zero_add' h0 n, zero_mul] at h1
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h1 (sq_nonneg _))

/-! ## The positive alternative: effective masses -/

variable (hp : ∀ s, 0 < h (2 * s))
include hp

theorem effMass_succ_le (s : ℕ) : effMass h (s + 1) ≤ effMass h s := by
  unfold effMass
  have h1 := H.logconvex s
  have hl := Real.log_le_log (by have := hp (s + 1); positivity) h1
  rw [Real.log_pow, Real.log_mul (hp s).ne' (hp (s + 2)).ne'] at hl
  rw [show 2 * (s + 1 + 1) = 2 * (s + 2) by ring]
  push_cast at hl
  linarith

theorem effMass_antitone : Antitone (effMass h) := antitone_nat_of_succ_le (H.effMass_succ_le hp)

theorem log_telescope (s : ℕ) :
    Real.log (h (2 * s)) = Real.log (h 0) - 2 * ∑ i ∈ range s, effMass h i := by
  induction s with
  | zero => simp
  | succ s ih =>
    have e : Real.log (h (2 * (s + 1))) = Real.log (h (2 * s)) - 2 * effMass h s := by unfold effMass; ring
    rw [sum_range_succ, e, ih]; ring

theorem log_telescope' (s₀ n : ℕ) :
    Real.log (h (2 * (s₀ + n))) = Real.log (h (2 * s₀)) - 2 * ∑ i ∈ range n, effMass h (s₀ + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : Real.log (h (2 * (s₀ + (n + 1)))) = Real.log (h (2 * (s₀ + n))) - 2 * effMass h (s₀ + n) := by
      unfold effMass; rw [← add_assoc]; ring
    rw [sum_range_succ, e, ih]; ring

/-- **Effective masses are nonnegative** (boundedness of the correlation). -/
theorem effMass_nonneg (s₀ : ℕ) : 0 ≤ effMass h s₀ := by
  by_contra hneg
  push Not at hneg
  obtain ⟨C, hC⟩ := H.bdd
  have hC0 : 0 < C := (hp 0).trans_le ((le_abs_self _).trans (hC 0))
  have hgrow : ∀ n : ℕ, Real.log (h (2 * s₀)) - 2 * n * effMass h s₀ ≤ Real.log C := by
    intro n
    have hsum : ∑ i ∈ range n, effMass h (s₀ + i) ≤ n * effMass h s₀ := by
      calc ∑ i ∈ range n, effMass h (s₀ + i) ≤ ∑ _i ∈ range n, effMass h s₀ :=
            sum_le_sum fun i _ => H.effMass_antitone hp (Nat.le_add_right s₀ i)
        _ = n * effMass h s₀ := by rw [sum_const, card_range, nsmul_eq_mul]
    have hle : Real.log (h (2 * (s₀ + n))) ≤ Real.log C :=
      Real.log_le_log (hp _) ((le_abs_self _).trans (hC _))
    rw [H.log_telescope' hp s₀ n] at hle
    linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((Real.log C - Real.log (h (2 * s₀))) / (-2 * effMass h s₀))
  have hd : 0 < -2 * effMass h s₀ := by linarith
  rw [div_lt_iff₀ hd] at hn
  have := hgrow n
  nlinarith

theorem bddBelow_effMass : BddBelow (Set.range (effMass h)) :=
  ⟨0, by rintro _ ⟨s, rfl⟩; exact H.effMass_nonneg hp s⟩

/-- **The rate is nonnegative.** -/
theorem rate_nonneg : 0 ≤ rate h := le_ciInf fun s => H.effMass_nonneg hp s

/-- **Effective masses approach the rate from above.** -/
theorem rate_le_effMass (s : ℕ) : rate h ≤ effMass h s := ciInf_le (H.bddBelow_effMass hp) s

/-- **The effective masses converge to the rate.** -/
theorem tendsto_effMass : Tendsto (effMass h) atTop (𝓝 (rate h)) :=
  tendsto_atTop_ciInf (H.effMass_antitone hp) (H.bddBelow_effMass hp)

theorem even_le (s : ℕ) : h (2 * s) ≤ h 0 * Real.exp (-(rate h * (2 * s))) := by
  have hl := H.log_telescope hp s
  have hsum : (s : ℝ) * rate h ≤ ∑ i ∈ range s, effMass h i := by
    calc (s : ℝ) * rate h = ∑ _i ∈ range s, rate h := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ ∑ i ∈ range s, effMass h i := sum_le_sum fun i _ => H.rate_le_effMass hp i
  have h0 : 0 < h 0 := by simpa using hp 0
  calc h (2 * s) = Real.exp (Real.log (h (2 * s))) := (Real.exp_log (hp s)).symm
    _ ≤ Real.exp (Real.log (h 0) - 2 * (s * rate h)) := by
        rw [hl]; exact Real.exp_le_exp.2 (by linarith)
    _ = h 0 * Real.exp (-(rate h * (2 * s))) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log h0]; congr 2; ring

/-- **The no-prefactor bound**: `|h(t)| ≤ h(0) e^{−E t}` for every `t`. -/
theorem abs_le_rate (t : ℕ) : |h t| ≤ h 0 * Real.exp (-(rate h * t)) := by
  have h0 : 0 < h 0 := by simpa using hp 0
  obtain ⟨s, hs⟩ := Nat.even_or_odd' t
  rcases hs with rfl | rfl
  · rw [abs_of_pos (hp s)]; push_cast; exact H.even_le hp s
  · have h1 := H.odd_sq s
    have e1 := H.even_le hp s
    have e2 := H.even_le hp (s + 1)
    have hb : h (2 * s) * h (2 * (s + 1)) ≤ (h 0 * Real.exp (-(rate h * ((2 * s + 1 : ℕ) : ℝ)))) ^ 2 := by
      calc h (2 * s) * h (2 * (s + 1))
          ≤ (h 0 * Real.exp (-(rate h * (2 * s)))) * (h 0 * Real.exp (-(rate h * (2 * (s + 1 : ℕ))))) :=
            mul_le_mul e1 e2 (hp _).le (by positivity)
        _ = (h 0 * Real.exp (-(rate h * ((2 * s + 1 : ℕ) : ℝ)))) ^ 2 := by
            rw [mul_pow, ← Real.exp_nat_mul]; push_cast
            rw [show h 0 * Real.exp (-(rate h * (2 * s))) * (h 0 * Real.exp (-(rate h * (2 * (s + 1))))) =
              h 0 ^ 2 * (Real.exp (-(rate h * (2 * s))) * Real.exp (-(rate h * (2 * (s + 1))))) by ring,
              ← Real.exp_add]
            congr 2; ring
    exact abs_le_of_sq_le_sq (h1.trans hb) (by positivity)

/-- **Lower bound from the first effective mass**: `h(2s) ≥ h(0) e^{−2 m(0) s}`. -/
theorem lower_effMass (s : ℕ) : h 0 * Real.exp (-(2 * effMass h 0 * s)) ≤ h (2 * s) := by
  have h0 : 0 < h 0 := by simpa using hp 0
  have hl := H.log_telescope hp s
  have hsum : ∑ i ∈ range s, effMass h i ≤ s * effMass h 0 := by
    calc ∑ i ∈ range s, effMass h i ≤ ∑ _i ∈ range s, effMass h 0 :=
          sum_le_sum fun i _ => H.effMass_antitone hp (Nat.zero_le i)
      _ = s * effMass h 0 := by rw [sum_const, card_range, nsmul_eq_mul]
  calc h 0 * Real.exp (-(2 * effMass h 0 * s)) = Real.exp (Real.log (h 0) - 2 * (s * effMass h 0)) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log h0]; congr 2; ring
    _ ≤ Real.exp (Real.log (h (2 * s))) := Real.exp_le_exp.2 (by rw [hl]; linarith)
    _ = h (2 * s) := Real.exp_log (hp s)

/-- **The rate is sharp**: for every `ε > 0` there is `s₀` with `h(2(s₀+n)) ≥ h(2s₀) e^{−2(E+ε)n}` for all `n`. -/
theorem rate_sharp {ε : ℝ} (hε : 0 < ε) :
    ∃ s₀ : ℕ, ∀ n : ℕ, h (2 * s₀) * Real.exp (-(2 * (rate h + ε) * n)) ≤ h (2 * (s₀ + n)) := by
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 ((tendsto_order.1 (H.tendsto_effMass hp)).2 _ (by linarith : rate h < rate h + ε))
  refine ⟨s₀, fun n => ?_⟩
  have hl := H.log_telescope' hp s₀ n
  have hsum : ∑ i ∈ range n, effMass h (s₀ + i) ≤ n * (rate h + ε) := by
    calc ∑ i ∈ range n, effMass h (s₀ + i) ≤ ∑ _i ∈ range n, (rate h + ε) :=
          sum_le_sum fun i _ => (hs₀ (s₀ + i) (Nat.le_add_right _ _)).le
      _ = n * (rate h + ε) := by rw [sum_const, card_range, nsmul_eq_mul]
  calc h (2 * s₀) * Real.exp (-(2 * (rate h + ε) * n))
      = Real.exp (Real.log (h (2 * s₀)) - 2 * (n * (rate h + ε))) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (hp s₀)]; congr 2; ring
    _ ≤ Real.exp (Real.log (h (2 * (s₀ + n)))) := Real.exp_le_exp.2 (by rw [hl]; linarith)
    _ = h (2 * (s₀ + n)) := Real.exp_log (hp _)

end RPSeq

/-! ## Limits of finite-range families -/

/-- **Pointwise limits of finite-range reflection-positive families are `RPSeq`.** If at stage `n` the Hankel
Cauchy–Schwarz inequalities hold for `j, k ≤ K n` with `K n → ∞`, the sequences are uniformly bounded, and they converge
pointwise along a subsequence `φ`, the limit is an `RPSeq`. -/
theorem rpSeq_of_limit {H : ℕ → ℕ → ℝ} {K : ℕ → ℕ} (hK : Tendsto K atTop atTop) {C : ℝ}
    (hcs : ∀ n j k, j ≤ K n → k ≤ K n → H n (j + k) ^ 2 ≤ H n (2 * j) * H n (2 * k))
    (hpos : ∀ n j, j ≤ K n → 0 ≤ H n (2 * j)) (hb : ∀ n t, |H n t| ≤ C)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {h : ℕ → ℝ} (hlim : ∀ t, Tendsto (fun n => H (φ n) t) atTop (𝓝 (h t))) :
    RPSeq h where
  cs j k := by
    have hev : ∀ᶠ n in atTop, j ≤ K (φ n) ∧ k ≤ K (φ n) :=
      ((hK.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop (max j k))).mono
        fun n hn => ⟨(le_max_left _ _).trans hn, (le_max_right _ _).trans hn⟩
    exact le_of_tendsto_of_tendsto ((hlim _).pow 2) ((hlim _).mul (hlim _))
      (hev.mono fun n hn => hcs _ j k hn.1 hn.2)
  nonneg j :=
    ge_of_tendsto (hlim _) (((hK.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop j)).mono
      fun n hn => hpos _ j hn)
  bdd := ⟨C, fun t => le_of_tendsto ((hlim t).abs) (Eventually.of_forall fun n => hb _ t)⟩

/-- **Existence of limit points**: a uniformly bounded family of real sequences has a pointwise convergent subsequence
(compactness of `[−C, C]^ℕ`). -/
theorem exists_limit {H : ℕ → ℕ → ℝ} {C : ℝ} (hb : ∀ n t, |H n t| ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ h : ℕ → ℝ, ∀ t, Tendsto (fun n => H (φ n) t) atTop (𝓝 (h t)) := by
  have hcpt : IsCompact (Set.pi Set.univ fun _ : ℕ => Set.Icc (-C) C) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ n, H n ∈ Set.pi Set.univ fun _ : ℕ => Set.Icc (-C) C :=
    fun n t _ => abs_le.1 (hb n t)
  obtain ⟨h, -, φ, hφ, ht⟩ := hcpt.tendsto_subseq hmem
  exact ⟨φ, hφ, h, fun t => (tendsto_pi_nhds.1 ht) t⟩

end ProofPhase.RouteB
