/-
Proof phase, M1 tools (m1-tools): the elementary part of Lemma D (core dilution) in its corrected, moderate-core form
(2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/NOTE.md`, section 2.
-/

import Mathlib

/-!
# Lemma D, moderate cores: contraction of the block average on the star of a block centre

Linearised around a regular background, Balaban's bond average ([I] (0.4)) acts on the perturbations `a b` (Lie
algebra values) carried by the `2d` fine bonds `b` of the star of a coarse site `y` as a weighted sum
`a' c = ∑_b F c b • a b`, with rows summing to one (`NOTE.md` 2.2; checked numerically by `star_weights.py`). The
gauge part (all `a b` equal) passes unchanged; what is visible in plaquettes is the **spread** `‖a b − a b'‖`.

* **`norm_wsum_sub_wsum_le`** (proved): `‖∑ w i • a i − ∑ w' i • a i‖ ≤ ½ ∑ |w i − w' i| · D` whenever
  `∑ w = ∑ w'` and all `‖a i − a j‖ ≤ D` (any real normed space; no sign condition on the weights).
* **`spread_avg_le`**: a row-normalised average contracts the spread by its Dobrushin coefficient
  `τ ≥ ½ ∑_b |F c b − F c' b|`.
* **`spread_iterate_le`**: `n` steps (possibly different weights each step) contract by `τⁿ`.
* **`geom_of_quadratic`, `spread_iterate_quadratic`**: the nonlinear corrections (BCH terms `O(spread²)`,
  `NOTE.md` 2.3) are absorbed: `d (n+1) ≤ τ d n + K (d n)²` with `d 0 ≤ r`, `τ + K r ≤ θ` gives `d n ≤ θⁿ d 0`.
* **`starW`, `starW_tv_le`, `balaban_star_tv`**: Balaban's star weights have the exact form
  `F c b = q + e₁ [b = c] − e₂ [b = −c]`, `e₁ = (L+1)/(2Lᵈ)`, `e₂ = (L−1)/(2Lᵈ)`, so `τ ≤ e₁ + e₂ = L/Lᵈ = L^{1−d}`
  (`1/2197` for `L = 13`, `d = 4`).

**Claim level.** Everything here is proved. What is *not* in this file: that Balaban's average has these linear
weights (paper computation `NOTE.md` 2.2, exact-fraction check `star_weights.py`), the size `K` of the nonlinear terms
(paper, `NOTE.md` 2.3), and the fact that the deterministic all-cores Lemma D is **false** (`ProofPhase.M1.Vortex`).
-/

open Finset

noncomputable section

namespace ProofPhase.M1

variable {ι κ : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Total-variation bound for two weightings of the same points.** -/
theorem norm_wsum_sub_wsum_le (w w' : ι → ℝ) (hsum : ∑ i, w i = ∑ i, w' i) (a : ι → E) {D : ℝ}
    (hD : ∀ i j, ‖a i - a j‖ ≤ D) :
    ‖∑ i, w i • a i - ∑ i, w' i • a i‖ ≤ (∑ i, |w i - w' i|) / 2 * D := by
  set p : ι → ℝ := fun i => max (w i - w' i) 0
  set n : ι → ℝ := fun i => max (w' i - w i) 0
  have hp0 : ∀ i, 0 ≤ p i := fun i => le_max_right _ _
  have hn0 : ∀ i, 0 ≤ n i := fun i => le_max_right _ _
  have hpn : ∀ i, p i - n i = w i - w' i := by
    intro i; simp only [p, n]
    rcases le_total (w i) (w' i) with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have habs : ∀ i, |w i - w' i| = p i + n i := by
    intro i; simp only [p, n]
    rcases le_total (w i) (w' i) with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonneg (by linarith)]; ring
  set t := ∑ i, p i
  have hnt : ∑ i, n i = t := by
    have : ∑ i, (p i - n i) = 0 := by simp only [hpn, sum_sub_distrib, hsum, sub_self]
    rw [sum_sub_distrib] at this; linarith
  have hsumabs : (∑ i, |w i - w' i|) / 2 = t := by
    simp only [habs, sum_add_distrib, hnt]; ring
  rw [hsumabs]
  have hX : ∑ i, w i • a i - ∑ i, w' i • a i = ∑ i, p i • a i - ∑ i, n i • a i := by
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl (fun i _ => ?_)
    rw [← sub_smul, ← sub_smul, hpn]
  rw [hX]
  have ht0 : 0 ≤ t := sum_nonneg (fun i _ => hp0 i)
  rcases ht0.eq_or_lt with ht | ht
  · -- all weights differences vanish
    have hp : ∀ i, p i = 0 := by
      intro i; have := (sum_eq_zero_iff_of_nonneg (fun j _ => hp0 j)).1 ht.symm i (mem_univ i); exact this
    have hn : ∀ i, n i = 0 := by
      intro i
      have := (sum_eq_zero_iff_of_nonneg (fun j _ => hn0 j)).1 (hnt.trans ht.symm) i (mem_univ i); exact this
    simp [hp, hn, ← ht]
  · -- the double-sum identity `t • X = ∑∑ p i n j • (a i - a j)`
    have hkey : t • (∑ i, p i • a i - ∑ i, n i • a i) = ∑ i, ∑ j, (p i * n j) • (a i - a j) := by
      have h1 : ∑ i, ∑ j, (p i * n j) • a i = t • ∑ i, p i • a i := by
        rw [smul_sum]
        refine sum_congr rfl (fun i _ => ?_)
        rw [← sum_smul, ← mul_sum, hnt, smul_smul, mul_comm]
      have h2 : ∑ i, ∑ j, (p i * n j) • a j = t • ∑ j, n j • a j := by
        rw [sum_comm, smul_sum]
        refine sum_congr rfl (fun j _ => ?_)
        rw [← sum_smul, ← sum_mul, smul_smul]
      simp only [smul_sub, sum_sub_distrib, h1, h2]
    have hbound : ‖∑ i, ∑ j, (p i * n j) • (a i - a j)‖ ≤ t * (t * D) := by
      calc ‖∑ i, ∑ j, (p i * n j) • (a i - a j)‖ ≤ ∑ i, ∑ j, ‖(p i * n j) • (a i - a j)‖ :=
            (norm_sum_le _ _).trans (sum_le_sum (fun i _ => norm_sum_le _ _))
        _ ≤ ∑ i, ∑ j, (p i * n j) * D := by
            refine sum_le_sum (fun i _ => sum_le_sum (fun j _ => ?_))
            rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (hp0 i) (hn0 j))]
            exact mul_le_mul_of_nonneg_left (hD i j) (mul_nonneg (hp0 i) (hn0 j))
        _ = t * (t * D) := by
            simp only [mul_assoc, ← mul_sum, ← sum_mul, hnt]
            rfl
    have hnorm : t * ‖∑ i, p i • a i - ∑ i, n i • a i‖ ≤ t * (t * D) := by
      rw [← Real.norm_of_nonneg ht0, ← norm_smul, hkey, Real.norm_of_nonneg ht0]; exact hbound
    exact le_of_mul_le_mul_left hnorm ht

/-- **One averaging step contracts the spread** by the Dobrushin coefficient of the weights. -/
theorem spread_avg_le (F : κ → ι → ℝ) (hrow : ∀ c, ∑ b, F c b = 1) {τ : ℝ}
    (hτ : ∀ c c', (∑ b, |F c b - F c' b|) / 2 ≤ τ) (a : ι → E) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ i j, ‖a i - a j‖ ≤ D) (c c' : κ) :
    ‖∑ b, F c b • a b - ∑ b, F c' b • a b‖ ≤ τ * D :=
  (norm_wsum_sub_wsum_le (F c) (F c') ((hrow c).trans (hrow c').symm) a hD).trans
    (mul_le_mul_of_nonneg_right (hτ c c') hD0)

/-- **Iterated averaging.** If at each step the star is replaced by row-normalised averages with Dobrushin
coefficient at most `τ`, the spread after `n` steps is at most `τⁿ` times the initial one. -/
theorem spread_iterate_le (F : ℕ → ι → ι → ℝ) (hrow : ∀ m c, ∑ b, F m c b = 1) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (hτ : ∀ m c c', (∑ b, |F m c b - F m c' b|) / 2 ≤ τ) (a : ℕ → ι → E)
    (hstep : ∀ m c, a (m + 1) c = ∑ b, F m c b • a m b) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ i j, ‖a 0 i - a 0 j‖ ≤ D) (n : ℕ) : ∀ i j, ‖a n i - a n j‖ ≤ τ ^ n * D := by
  induction n with
  | zero => simpa using hD
  | succ n ih =>
    intro i j
    rw [hstep, hstep, pow_succ, mul_comm (τ ^ n) τ, mul_assoc]
    exact spread_avg_le (F n) (hrow n) (hτ n) (a n) (mul_nonneg (pow_nonneg hτ0 n) hD0) ih i j

/-- **The quadratic recursion.** `d (n+1) ≤ τ d n + K (d n)²`, `0 ≤ d n`, `d 0 ≤ r` and `τ + K r ≤ θ ≤ 1` give the
geometric bound `d n ≤ θⁿ d 0`. -/
theorem geom_of_quadratic (d : ℕ → ℝ) {τ K r θ : ℝ} (hτ : 0 ≤ τ) (hK : 0 ≤ K) (hθ1 : θ ≤ 1)
    (hθ : τ + K * r ≤ θ) (hd : ∀ n, 0 ≤ d n) (hr : d 0 ≤ r)
    (hrec : ∀ n, d (n + 1) ≤ τ * d n + K * d n ^ 2) (n : ℕ) : d n ≤ θ ^ n * d 0 := by
  have hθ0 : 0 ≤ θ := le_trans (add_nonneg hτ (mul_nonneg hK ((hd 0).trans hr))) hθ
  induction n with
  | zero => simp
  | succ n ih =>
    have hdn : d n ≤ r := ih.trans ((mul_le_of_le_one_left (hd 0) (pow_le_one₀ hθ0 hθ1)).trans hr)
    calc d (n + 1) ≤ τ * d n + K * d n ^ 2 := hrec n
      _ = (τ + K * d n) * d n := by ring
      _ ≤ θ * d n := by
          refine mul_le_mul_of_nonneg_right ?_ (hd n)
          have := mul_le_mul_of_nonneg_left hdn hK
          linarith
      _ ≤ θ * (θ ^ n * d 0) := mul_le_mul_of_nonneg_left ih hθ0
      _ = θ ^ (n + 1) * d 0 := by ring

/-- **Iterated nonlinear averaging (the form Lemma D uses).** If every step maps a star of spread `≤ s` to a star
of spread `≤ τ s + K s²`, then from spread `≤ D ≤ r` the spread after `n` steps is `≤ θⁿ D`, `θ ≥ τ + K r`. -/
theorem spread_iterate_quadratic (a : ℕ → ι → E) {τ K r θ D : ℝ} (hτ : 0 ≤ τ) (hK : 0 ≤ K) (hθ1 : θ ≤ 1)
    (hθ : τ + K * r ≤ θ) (hD0 : 0 ≤ D) (hDr : D ≤ r) (hD : ∀ i j, ‖a 0 i - a 0 j‖ ≤ D)
    (hstep : ∀ m (s : ℝ), 0 ≤ s → (∀ i j, ‖a m i - a m j‖ ≤ s) →
      ∀ i j, ‖a (m + 1) i - a (m + 1) j‖ ≤ τ * s + K * s ^ 2) (n : ℕ) :
    ∀ i j, ‖a n i - a n j‖ ≤ θ ^ n * D := by
  have hθ0 : 0 ≤ θ := le_trans (add_nonneg hτ (mul_nonneg hK (hD0.trans hDr))) hθ
  induction n with
  | zero => simpa using hD
  | succ n ih =>
    have hs0 : 0 ≤ θ ^ n * D := mul_nonneg (pow_nonneg hθ0 n) hD0
    have hsr : θ ^ n * D ≤ r := (mul_le_of_le_one_left hD0 (pow_le_one₀ hθ0 hθ1)).trans hDr
    intro i j
    refine (hstep n _ hs0 ih i j).trans ?_
    calc τ * (θ ^ n * D) + K * (θ ^ n * D) ^ 2 = (τ + K * (θ ^ n * D)) * (θ ^ n * D) := by ring
      _ ≤ θ * (θ ^ n * D) := by
          refine mul_le_mul_of_nonneg_right ?_ hs0
          have := mul_le_mul_of_nonneg_left hsr hK
          linarith
      _ = θ ^ (n + 1) * D := by ring

/-! ## Balaban's star weights -/

/-- The linear star weights of Balaban's bond average at a block centre (`NOTE.md` 2.2):
`F c b = q + e₁ [b = c] − e₂ [b = opp c]`, `opp` the reversed direction. -/
def starW [DecidableEq ι] (q e₁ e₂ : ℝ) (opp : ι → ι) (c b : ι) : ℝ :=
  q + (if b = c then e₁ else 0) - (if b = opp c then e₂ else 0)

omit [Fintype ι] in
theorem starW_sub [DecidableEq ι] (q e₁ e₂ : ℝ) (opp : ι → ι) (c c' b : ι) :
    starW q e₁ e₂ opp c b - starW q e₁ e₂ opp c' b
      = ((if b = c then e₁ else 0) - (if b = c' then e₁ else 0))
        - ((if b = opp c then e₂ else 0) - (if b = opp c' then e₂ else 0)) := by
  unfold starW; ring

theorem starW_rowsum [DecidableEq ι] (q e₁ e₂ : ℝ) (opp : ι → ι) (c : ι) :
    ∑ b, starW q e₁ e₂ opp c b = Fintype.card ι * q + e₁ - e₂ := by
  simp [starW, sum_add_distrib, sum_sub_distrib]

/-- **Dobrushin coefficient of the star weights:** `½ ∑_b |F c b − F c' b| ≤ e₁ + e₂`. -/
theorem starW_tv_le [DecidableEq ι] (q : ℝ) {e₁ e₂ : ℝ} (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) (opp : ι → ι) (c c' : ι) :
    (∑ b, |starW q e₁ e₂ opp c b - starW q e₁ e₂ opp c' b|) / 2 ≤ e₁ + e₂ := by
  have hb : ∀ b, |starW q e₁ e₂ opp c b - starW q e₁ e₂ opp c' b|
      ≤ ((if b = c then e₁ else 0) + (if b = c' then e₁ else 0))
        + ((if b = opp c then e₂ else 0) + (if b = opp c' then e₂ else 0)) := by
    intro b
    rw [starW_sub]
    have i1 : 0 ≤ (if b = c then e₁ else 0) := by split_ifs <;> simp [he₁]
    have i2 : 0 ≤ (if b = c' then e₁ else 0) := by split_ifs <;> simp [he₁]
    have i3 : 0 ≤ (if b = opp c then e₂ else 0) := by split_ifs <;> simp [he₂]
    have i4 : 0 ≤ (if b = opp c' then e₂ else 0) := by split_ifs <;> simp [he₂]
    refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans ?_) ((abs_sub _ _).trans ?_))
    · rw [abs_of_nonneg i1, abs_of_nonneg i2]
    · rw [abs_of_nonneg i3, abs_of_nonneg i4]
  have hs := sum_le_sum (fun b (_ : b ∈ univ) => hb b)
  simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true] at hs
  linarith

/-- The two corrections for Balaban's contour family: `e₁ + e₂ = L / Lᵈ = L^{1−d}`. -/
theorem balaban_e_sum (L : ℝ) (d : ℕ) (hL : 0 < L) :
    (L + 1) / (2 * L ^ d) + (L - 1) / (2 * L ^ d) = L / L ^ d := by
  have : (0 : ℝ) < L ^ d := pow_pos hL d
  field_simp; ring

/-- **Balaban's star average contracts the spread by `L^{1−d}` per step** (linear part). -/
theorem balaban_star_tv [DecidableEq ι] (q L : ℝ) (d : ℕ) (hL : 1 ≤ L) (opp : ι → ι) (c c' : ι) :
    (∑ b, |starW q ((L + 1) / (2 * L ^ d)) ((L - 1) / (2 * L ^ d)) opp c b
        - starW q ((L + 1) / (2 * L ^ d)) ((L - 1) / (2 * L ^ d)) opp c' b|) / 2 ≤ L / L ^ d := by
  have hL0 : 0 < L := by linarith
  have hp : (0 : ℝ) < 2 * L ^ d := by positivity
  rw [← balaban_e_sum L d hL0]
  exact starW_tv_le q (div_nonneg (by linarith) hp.le) (div_nonneg (by linarith) hp.le) opp c c'

/-- **Corollary (moderate Lemma D, linear part):** `n` steps of Balaban's star average (row sums one) shrink the
spread of the star by `(L^{1−d})ⁿ`. -/
theorem balaban_star_dilution [DecidableEq ι] (q L : ℝ) (d : ℕ) (hL : 1 ≤ L) (opp : ι → ι)
    (hrow : Fintype.card ι * q + (L + 1) / (2 * L ^ d) - (L - 1) / (2 * L ^ d) = 1) (a : ℕ → ι → E)
    (hstep : ∀ m c, a (m + 1) c = ∑ b, starW q ((L + 1) / (2 * L ^ d)) ((L - 1) / (2 * L ^ d)) opp c b • a m b)
    {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ i j, ‖a 0 i - a 0 j‖ ≤ D) (n : ℕ) :
    ∀ i j, ‖a n i - a n j‖ ≤ (L / L ^ d) ^ n * D :=
  spread_iterate_le (fun _ => starW q _ _ opp) (fun _ c => (starW_rowsum q _ _ opp c).trans hrow)
    (div_nonneg (by linarith) (pow_nonneg (by linarith) d)) (fun _ => balaban_star_tv q L d hL opp) a hstep hD0
    hD n

end ProofPhase.M1
