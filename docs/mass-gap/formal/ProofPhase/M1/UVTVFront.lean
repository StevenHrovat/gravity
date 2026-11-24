/-
Proof phase, M1 tools (m1-tools), Lean phase, module 2: the front advance over the scales of Lemma UV-TV
(2026-11-23). Released under Apache 2.0.

Paper: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/UV-TV.md`, sections 30.3-30.4.
-/

import Mathlib

/-!
# The front advance over the scales

`UV-TV.md` 30 runs the one-scale statement (module 1, `UVTVScale`) from the top scale `ℓ` down to `0`. Index the
scales by `k = ℓ - j` (`k = 0` is the top). `D k` is the front distance at depth `k`, in that scale's units.

* `front_lower`: **the recursion** `D (k+1) ≥ min(L · D k, L^(k+1) · D 0) - e k` (the inherited front moves out by the
  factor `L`, the outside of the local ball stays at `L^(k+1) D 0`, and one scale costs `e k = a_j + C ℓ_B L`) gives
  `D k ≥ L^k (D 0 - Σ_{i<k} L^{-(i+1)} e i)`.
* `front_half`: if `D 0 ≥ 2 Σ_{i<n} L^{-(i+1)} e i`, the front stays intact: `D k ≥ L^k D 0 / 2 > 0` for `k ≤ n`.
* `measure_compl_le_chain`: **the union over scales.** For events `G k` ("the copies agree inside the front at depth
  `k`"), `P(G n)ᶜ ≤ P(G 0)ᶜ + Σ_{k<n} P((G (k+1))ᶜ ∩ G k)`.
* `sum_geom_le`: per-scale failure bounds `ε_k ≤ c ρ^k x^{-r}` (`ρ = L^{-d C_2} < 1`, `x = t/ℓ`, `c` the polylog factor)
  sum to `c x^{-r}/(1 - ρ)`.
* `front_advance`: the conclusion of 30.4,
  `P(the fine fields differ on B) ≤ P(start fails) + c (t/ℓ)^{-r}/(1 - ρ)`,
  from the per-scale statements as hypotheses, and the recursion's condition as the guarantee that the target lies in
  the last front.

The one-scale statements are module 1's `scale_front` (conditional on the coarser scales); here they enter as the
hypotheses `step`.
-/

open MeasureTheory Finset

open scoped ENNReal

noncomputable section

namespace ProofPhase.M1.UVTV

/-! ### The recursion -/

/-- The bracket `Σ_{i<k} L^{-(i+1)} e i`. -/
def bracket (L : ℝ) (e : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ range k, (L ^ (i + 1))⁻¹ * e i

theorem bracket_nonneg {L : ℝ} (hL : 0 < L) {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) (k : ℕ) : 0 ≤ bracket L e k :=
  Finset.sum_nonneg fun i _ => mul_nonneg (inv_nonneg.mpr (pow_pos hL _).le) (he i)

theorem bracket_mono {L : ℝ} (hL : 0 < L) {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) {k n : ℕ} (hkn : k ≤ n) :
    bracket L e k ≤ bracket L e n :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkn)
    fun i _ _ => mul_nonneg (inv_nonneg.mpr (pow_pos hL _).le) (he i)

/-- **The front recursion** (`UV-TV.md` 30.3). From `D (k+1) ≥ min(L · D k, L^(k+1) · D 0) - e k` with `L > 0` and
`e ≥ 0`: `D k ≥ L^k (D 0 - Σ_{i<k} L^{-(i+1)} e i)`. -/
theorem front_lower {L : ℝ} (hL : 0 < L) {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) {D : ℕ → ℝ}
    (hrec : ∀ k, min (L * D k) (L ^ (k + 1) * D 0) - e k ≤ D (k + 1)) (k : ℕ) :
    L ^ k * (D 0 - bracket L e k) ≤ D k := by
  induction k with
  | zero => simp [bracket]
  | succ k ih =>
      have hb := bracket_nonneg hL he k
      have hLk : 0 < L ^ (k + 1) := pow_pos hL _
      have h1 : L ^ (k + 1) * (D 0 - bracket L e k) ≤ L * D k := by
        rw [pow_succ, mul_comm (L ^ k) L, mul_assoc]
        exact mul_le_mul_of_nonneg_left ih hL.le
      have h2 : L ^ (k + 1) * (D 0 - bracket L e k) ≤ L ^ (k + 1) * D 0 :=
        mul_le_mul_of_nonneg_left (by linarith) hLk.le
      have hmin := le_min h1 h2
      have hsplit : bracket L e (k + 1) = bracket L e k + (L ^ (k + 1))⁻¹ * e k := by
        simp [bracket, Finset.sum_range_succ]
      have hcancel : L ^ (k + 1) * ((L ^ (k + 1))⁻¹ * e k) = e k := by
        rw [← mul_assoc, mul_inv_cancel₀ hLk.ne', one_mul]
      calc L ^ (k + 1) * (D 0 - bracket L e (k + 1))
          = L ^ (k + 1) * (D 0 - bracket L e k) - e k := by rw [hsplit, mul_sub, mul_add, hcancel]; ring
        _ ≤ min (L * D k) (L ^ (k + 1) * D 0) - e k := by linarith
        _ ≤ D (k + 1) := hrec k

/-- **The front stays intact** (`UV-TV.md` 30.3, condition `Δ_ℓ ≥ 2(A_ℓ + C ℓ_B L)`): if `D 0 ≥ 2 Σ_{i<n} L^{-(i+1)} e i`
then `D k ≥ L^k D 0 / 2` for every `k ≤ n`; in particular `D k > 0` when `D 0 > 0`. -/
theorem front_half {L : ℝ} (hL : 0 < L) {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) {D : ℕ → ℝ}
    (hrec : ∀ k, min (L * D k) (L ^ (k + 1) * D 0) - e k ≤ D (k + 1)) {n : ℕ}
    (hcond : 2 * bracket L e n ≤ D 0) {k : ℕ} (hk : k ≤ n) :
    L ^ k * D 0 / 2 ≤ D k := by
  have h := front_lower hL he hrec k
  have hb := bracket_mono hL he hk
  have hLk : 0 < L ^ k := pow_pos hL _
  have : L ^ k * D 0 / 2 ≤ L ^ k * (D 0 - bracket L e k) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (by linarith) hLk.le
  linarith

/-! ### The union over scales -/

/-- **Union over scales.** For events `G k`, `P(G n)ᶜ ≤ P(G 0)ᶜ + Σ_{k<n} P((G (k+1))ᶜ ∩ G k)`. -/
theorem measure_compl_le_chain {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (G : ℕ → Set Ω) (n : ℕ) :
    P (G n)ᶜ ≤ P (G 0)ᶜ + ∑ k ∈ range n, P ((G (k + 1))ᶜ ∩ G k) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsub : (G (n + 1))ᶜ ⊆ ((G (n + 1))ᶜ ∩ G n) ∪ (G n)ᶜ := by
        intro ω hω
        by_cases h : ω ∈ G n
        · exact Or.inl ⟨hω, h⟩
        · exact Or.inr h
      calc P (G (n + 1))ᶜ ≤ P ((G (n + 1))ᶜ ∩ G n) + P (G n)ᶜ := (measure_mono hsub).trans (measure_union_le _ _)
        _ ≤ P ((G (n + 1))ᶜ ∩ G n) + (P (G 0)ᶜ + ∑ k ∈ range n, P ((G (k + 1))ᶜ ∩ G k)) := by gcongr
        _ = P (G 0)ᶜ + ∑ k ∈ range (n + 1), P ((G (k + 1))ᶜ ∩ G k) := by
          rw [Finset.sum_range_succ]; ring

/-- `Σ_{k<n} ρ^k ≤ 1/(1 - ρ)` for `0 ≤ ρ < 1`. -/
theorem geom_sum_le_inv {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (n : ℕ) : ∑ k ∈ range n, ρ ^ k ≤ 1 / (1 - ρ) := by
  rw [le_div_iff₀ (by linarith), geom_sum_mul_neg]
  linarith [pow_nonneg hρ0 n]

/-- **The geometric sum over scales** (`UV-TV.md` 30.4): `Σ_{k<n} c ρ^k x^{-r} ≤ c x^{-r}/(1 - ρ)` for `0 ≤ ρ < 1`,
`c ≥ 0`, `x > 0`. -/
theorem sum_geom_le {ρ c x r : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hc : 0 ≤ c) (hx : 0 < x) (n : ℕ) :
    ∑ k ∈ range n, c * ρ ^ k * x ^ (-r) ≤ c * x ^ (-r) / (1 - ρ) := by
  have hxr : 0 ≤ x ^ (-r) := Real.rpow_nonneg hx.le _
  calc ∑ k ∈ range n, c * ρ ^ k * x ^ (-r) = c * x ^ (-r) * ∑ k ∈ range n, ρ ^ k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ c * x ^ (-r) * (1 / (1 - ρ)) := mul_le_mul_of_nonneg_left (geom_sum_le_inv hρ0 hρ1 n) (mul_nonneg hc hxr)
    _ = c * x ^ (-r) / (1 - ρ) := by ring

/-- The per-scale rate: `(L^k x)^{-r} = (L^{-r})^k x^{-r}`, so `ρ = L^{-r} < 1` for `L > 1`, `r > 0`. -/
theorem rpow_scale {L x r : ℝ} (hL : 0 < L) (hx : 0 < x) (k : ℕ) :
    (L ^ k * x) ^ (-r) = (L ^ (-r)) ^ k * x ^ (-r) := by
  rw [Real.mul_rpow (pow_nonneg hL.le k) hx.le, ← Real.rpow_natCast, ← Real.rpow_mul hL.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hL.le, mul_comm (k : ℝ) (-r)]

theorem rpow_neg_lt_one {L r : ℝ} (hL : 1 < L) (hr : 0 < r) : L ^ (-r) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)

/-- **The front advance, assembled** (`UV-TV.md` 30.4).

* `P` is the tower coupling (the coupled copies at all scales), `G k` the event that the copies agree inside the front
  at depth `k` (scale `ℓ - k`), `G 0` the start at the top scale.
* `step` (module 1, `scale_front`, integrated over the coarser scales): one scale fails with probability at most
  `c ρ^k x^{-r}`, where `x = t/ℓ`, `ρ = L^{-d C_2}`, and `c` carries the polylog factors.
* `hB`: the target is inside the last front, so differing on it means the last agreement event failed. (The recursion
  `front_half` guarantees that the last front still has positive radius.)

Then `P(differ on B) ≤ P(start fails) + c x^{-r}/(1 - ρ)`. -/
theorem front_advance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (G : ℕ → Set Ω) (n : ℕ) (Bdiff : Set Ω)
    (hB : Bdiff ⊆ (G n)ᶜ) {ρ c x r : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hc : 0 ≤ c) (hx : 0 < x)
    (step : ∀ k < n, P ((G (k + 1))ᶜ ∩ G k) ≤ ENNReal.ofReal (c * ρ ^ k * x ^ (-r))) :
    P Bdiff ≤ P (G 0)ᶜ + ENNReal.ofReal (c * x ^ (-r) / (1 - ρ)) := by
  have hxr : 0 ≤ x ^ (-r) := Real.rpow_nonneg hx.le _
  calc P Bdiff ≤ P (G n)ᶜ := measure_mono hB
    _ ≤ P (G 0)ᶜ + ∑ k ∈ range n, P ((G (k + 1))ᶜ ∩ G k) := measure_compl_le_chain P G n
    _ ≤ P (G 0)ᶜ + ∑ k ∈ range n, ENNReal.ofReal (c * ρ ^ k * x ^ (-r)) := by
        gcongr with k hk
        exact step k (Finset.mem_range.mp hk)
    _ = P (G 0)ᶜ + ENNReal.ofReal (∑ k ∈ range n, c * ρ ^ k * x ^ (-r)) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun k _ => mul_nonneg (mul_nonneg hc (pow_nonneg hρ0 k)) hxr]
    _ ≤ P (G 0)ᶜ + ENNReal.ofReal (c * x ^ (-r) / (1 - ρ)) := by
        gcongr
        exact sum_geom_le hρ0 hρ1 hc hx n

/-- **The front advance with the scale rate written out**: per-scale failures `≤ c (L^k x)^{-r}` with `L > 1`, `r > 0`
give `P(differ on B) ≤ P(start fails) + c x^{-r}/(1 - L^{-r})`. -/
theorem front_advance_rpow {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (G : ℕ → Set Ω) (n : ℕ) (Bdiff : Set Ω)
    (hB : Bdiff ⊆ (G n)ᶜ) {L c x r : ℝ} (hL : 1 < L) (hr : 0 < r) (hc : 0 ≤ c) (hx : 0 < x)
    (step : ∀ k < n, P ((G (k + 1))ᶜ ∩ G k) ≤ ENNReal.ofReal (c * (L ^ k * x) ^ (-r))) :
    P Bdiff ≤ P (G 0)ᶜ + ENNReal.ofReal (c * x ^ (-r) / (1 - L ^ (-r))) := by
  have hL0 : 0 < L := by linarith
  refine front_advance P G n Bdiff hB (Real.rpow_nonneg hL0.le _) (rpow_neg_lt_one hL hr) hc hx fun k hk => ?_
  have h := step k hk
  rwa [rpow_scale hL0 hx k, ← mul_assoc] at h

end ProofPhase.M1.UVTV
