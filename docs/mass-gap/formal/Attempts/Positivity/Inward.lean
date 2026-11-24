/-
Attempt (b), the positivity route (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/positivity/NOTE.md`, §2 (inward only) and §3 (one distance, ratio form).
-/

import OneScale.Doubling

/-!
# What reflection positivity can transport: inward only, and one distance only in ratio form

Reflection positivity (site RP, `Positivity.rp_plaquette_weight_gram`) and time translation
(`OneScale.TimeShift.hankel_corr`) give the connected reflected correlation `H(m) = Cov(F_m, F ∘ Θ)` the Hankel
Cauchy–Schwarz structure `H(j + k)² ≤ H(2j) H(2k)`, `H(2j) ≥ 0` (`OneScale.TorusRP.hankel_cs`). In infinite volume this
holds for all `j, k`; we package it as `RPHankel`. Everything below is real analysis on such sequences.

* `twoLevel_rpHankel`, `rp_no_outward`: **RP alone cannot carry decay outward.** For every rate `λ > 0` and every range
  `M` there is a sequence with the full RP Hankel structure (the moment sequence of `(1 - η) δ_x + η δ_1`) that decays at
  rate `λ` on `[0, M]` (`|H(m)| ≤ H(0) e^{-λ m}`) and does not decay exponentially at all: for every prefactor `C` and
  every rate `λ' > 0` some `m` has `H(m) > C e^{-λ' m}`. Theorem C (`OneScale.doubling_decay`) carries decay from
  large to small distances; this is the converse failure. Halving the lattice spacing at fixed physical size doubles the
  number of lattice steps, i.e. it asks for outward transport, which RP cannot supply.
* `even_bound`, `one_distance_ratio`: **one distance suffices in ratio form.** If the ratio bound
  `H(2(p + j)) ≤ ε H(2j)` holds for every shift `j` (i.e. `Cov(G_M, ΘG) ≤ ε Cov(G, ΘG)` at the one distance `M = 2p`
  for every time translate `G = F_j` of `F`), then `|H(m)| ≤ H(0) ε^{m/M}` for every `m`, with no prefactor. The
  shift-uniformity cannot be dropped: the two-level model satisfies the bound for `F` alone up to `M` but violates it
  for large shifts.

Osterwalder–Seiler (1978) for the RP structure; the moment-sequence and log-convexity facts are classical. Formalised
here from scratch.
-/

open Real Filter Topology

noncomputable section

namespace Attempts.Positivity

/-- The Hankel Cauchy–Schwarz structure that site reflection positivity and time translation give the reflected
correlation `H(m) = Cov(F_m, F ∘ Θ)` (infinite volume: all distances). -/
structure RPHankel (H : ℕ → ℝ) : Prop where
  cs : ∀ j k, H (j + k) ^ 2 ≤ H (2 * j) * H (2 * k)
  pos : ∀ j, 0 ≤ H (2 * j)

/-! ## 1. No outward transport -/

/-- The two-level model `H(m) = (1 - η) x^m + η`: the moment sequence of `(1 - η) δ_x + η δ_1`. The atom at `1` is a
mode that never decays (in a gauge theory: the massless photon's spectral weight near the top of the spectrum). -/
def twoLevel (η x : ℝ) (m : ℕ) : ℝ := (1 - η) * x ^ m + η

theorem twoLevel_rpHankel {η x : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hx : 0 ≤ x) : RPHankel (twoLevel η x) where
  cs j k := by
    simp only [twoLevel]
    have hp : 0 ≤ 1 - η := by linarith
    rw [pow_add, pow_mul', pow_mul']
    have h := mul_nonneg (mul_nonneg hp hη0) (sq_nonneg (x ^ j - x ^ k))
    nlinarith [h]
  pos j := by
    simp only [twoLevel]
    have hp : 0 ≤ 1 - η := by linarith
    exact add_nonneg (mul_nonneg hp (pow_nonneg hx _)) hη0

/-- A sequence bounded below by a positive constant decays at no exponential rate, whatever the prefactor. -/
theorem no_exp_decay_of_floor {H : ℕ → ℝ} {η : ℝ} (hη : 0 < η) (hfl : ∀ m, η ≤ H m) (C lam' : ℝ) (hlam' : 0 < lam') :
    ∃ m : ℕ, C * Real.exp (-(lam' * m)) < H m := by
  rcases le_or_gt C 0 with hC | hC
  · refine ⟨0, ?_⟩
    simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
    linarith [hfl 0]
  · have hq1 : Real.exp (-lam') < 1 := Real.exp_lt_one_iff.2 (by linarith)
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hη hC) hq1
    refine ⟨m, ?_⟩
    have e : Real.exp (-(lam' * m)) = Real.exp (-lam') ^ m := by
      rw [show -(lam' * (m : ℝ)) = (m : ℝ) * (-lam') by ring, Real.exp_nat_mul]
    rw [e]
    calc C * Real.exp (-lam') ^ m < C * (η / C) := mul_lt_mul_of_pos_left hm hC
      _ = η := by field_simp
      _ ≤ H m := hfl m

/-- **RP alone cannot carry decay outward.** For every rate `λ > 0` and range `M` there is a sequence with the RP Hankel
structure, `H(0) = 1`, decaying at rate `λ` on `[0, M]`, and decaying at no exponential rate at all. -/
theorem rp_no_outward {lam : ℝ} (hlam : 0 < lam) (M : ℕ) :
    ∃ H : ℕ → ℝ, RPHankel H ∧ H 0 = 1 ∧
      (∀ m, m ≤ M → |H m| ≤ H 0 * Real.exp (-(lam * m))) ∧
      (∀ C lam' : ℝ, 0 < lam' → ∃ m : ℕ, C * Real.exp (-(lam' * m)) < H m) := by
  set q := Real.exp (-lam) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
  set η := q ^ M * (1 - q) with hηdef
  have hη0 : 0 < η := mul_pos (pow_pos hq0 M) (by linarith)
  have hη1 : η ≤ 1 := by
    have h1 : q ^ M ≤ 1 := pow_le_one₀ hq0.le hq1.le
    have h2 : 1 - q ≤ 1 := by linarith
    calc η = q ^ M * (1 - q) := rfl
      _ ≤ 1 * 1 := mul_le_mul h1 h2 (by linarith) zero_le_one
      _ = 1 := one_mul 1
  have hfl : ∀ m, η ≤ twoLevel η (q ^ 2) m := by
    intro m
    simp only [twoLevel]
    have : 0 ≤ (1 - η) * (q ^ 2) ^ m := mul_nonneg (by linarith) (by positivity)
    linarith
  have hH0 : twoLevel η (q ^ 2) 0 = 1 := by simp [twoLevel]
  refine ⟨twoLevel η (q ^ 2), twoLevel_rpHankel hη0.le hη1 (by positivity), hH0, ?_,
    fun C lam' hlam' => no_exp_decay_of_floor hη0 hfl C lam' hlam'⟩
  intro m hm
  have hpos : 0 ≤ twoLevel η (q ^ 2) m := hη0.le.trans (hfl m)
  rw [abs_of_nonneg hpos, hH0, one_mul]
  have e : Real.exp (-(lam * m)) = q ^ m := by
    rw [hq, show -(lam * (m : ℝ)) = (m : ℝ) * (-lam) by ring, Real.exp_nat_mul]
  rw [e]
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; simp [twoLevel]
  · -- `η ≤ q^m (1 - q^m)` for `1 ≤ m ≤ M`
    have hqm0 : 0 ≤ q ^ m := by positivity
    have hA : q ^ M ≤ q ^ m := pow_le_pow_of_le_one hq0.le hq1.le hm
    have hB : q ^ m ≤ q := pow_le_of_le_one hq0.le hq1.le (Nat.pos_iff_ne_zero.1 h0)
    have hη' : η ≤ q ^ m * (1 - q ^ m) := by
      calc η = q ^ M * (1 - q) := rfl
        _ ≤ q ^ m * (1 - q ^ m) := mul_le_mul hA (by linarith) (by linarith) hqm0
    have hsq : (q ^ 2) ^ m = q ^ m * q ^ m := by rw [← pow_mul, mul_comm, pow_mul, sq]
    simp only [twoLevel]
    rw [hsq]
    have : 0 ≤ η * (q ^ m * q ^ m) := mul_nonneg hη0.le (mul_nonneg hqm0 hqm0)
    nlinarith [this, hη']

/-! ## 2. One distance suffices, in ratio form -/

/-- Iterating the ratio bound along shifts: if `H(2(p + j)) ≤ ε H(2j)` for every `j`, then
`H(2i) ≤ ε^{⌊i/p⌋} · C` with `C = ∑_{r < p} H(2r)`. -/
theorem even_bound {H : ℕ → ℝ} (hpos : ∀ j, 0 ≤ H (2 * j)) {p : ℕ} (hp : 0 < p) {ε : ℝ} (hε : 0 ≤ ε)
    (hrat : ∀ j, H (2 * (p + j)) ≤ ε * H (2 * j)) :
    ∀ i, H (2 * i) ≤ ε ^ (i / p) * ∑ r ∈ Finset.range p, H (2 * r) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hi : i < p
    · rw [Nat.div_eq_of_lt hi, pow_zero, one_mul]
      exact Finset.single_le_sum (fun r _ => hpos r) (Finset.mem_range.2 hi)
    · obtain ⟨j, rfl⟩ : ∃ j, i = p + j := ⟨i - p, by omega⟩
      have hj : j < p + j := by omega
      calc H (2 * (p + j)) ≤ ε * H (2 * j) := hrat j
        _ ≤ ε * (ε ^ (j / p) * ∑ r ∈ Finset.range p, H (2 * r)) := mul_le_mul_of_nonneg_left (ih j hj) hε
        _ = ε ^ ((p + j) / p) * ∑ r ∈ Finset.range p, H (2 * r) := by
            rw [Nat.add_comm p j, Nat.add_div_right j hp, pow_succ]
            ring

/-- **One distance suffices, in ratio form, with no prefactor.** If `H` has the RP Hankel structure and the ratio bound
`H(2(p + j)) ≤ ε H(2j)` holds for every shift `j` (one distance `M = 2p`, uniformly over the time translates of the
observable), then `|H(m)| ≤ H(0) ε^{m/(2p)}` for every `m`. -/
theorem one_distance_ratio {H : ℕ → ℝ} (hH : RPHankel H) {p : ℕ} (hp : 0 < p) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hrat : ∀ j, H (2 * (p + j)) ≤ ε * H (2 * j)) (m : ℕ) :
    |H m| ≤ H 0 * ε ^ ((m : ℝ) / (2 * p)) := by
  set C := ∑ r ∈ Finset.range p, H (2 * r) with hCdef
  have hC : 0 ≤ C := Finset.sum_nonneg fun r _ => hH.pos r
  have hH0 : 0 ≤ H 0 := by simpa using hH.pos 0
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have key : ∀ r : ℕ, 1 ≤ r →
      |H m| ≤ H 0 ^ (1 - (1 / 2 : ℝ) ^ r) * (C / ε) ^ ((1 / 2 : ℝ) ^ r) * ε ^ ((m : ℝ) / (2 * p)) := by
    intro r hr
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    set i := 2 ^ s * m with hi
    have hK : 2 ^ (s + 1 - 1) * m ≤ i := by simp [i]
    have hd := OneScale.doubling (H := H) (K := i) (m := m) (fun j k _ _ => hH.cs j k) (fun j _ => hH.pos j)
      (s + 1) (by omega) hK
    have e : 2 ^ (s + 1) * m = 2 * i := by simp only [i]; ring
    have hb := even_bound hH.pos hp hε0.le hrat i
    have hfl : (i : ℝ) / p - 1 ≤ ((i / p : ℕ) : ℝ) := by
      have h1 := Nat.div_add_mod i p
      have h2 := Nat.mod_lt i hp
      have h1' : (i : ℝ) = p * ((i / p : ℕ) : ℝ) + ((i % p : ℕ) : ℝ) := by exact_mod_cast h1.symm
      have h2' : ((i % p : ℕ) : ℝ) < p := by exact_mod_cast h2
      rw [div_sub_one hp'.ne', div_le_iff₀ hp']
      nlinarith
    have hpow : ε ^ (i / p) ≤ ε ^ ((i : ℝ) / p - 1) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 hfl
    have hHr : 0 ≤ H (2 ^ (s + 1) * m) := by rw [e]; exact hH.pos i
    have hb' : H (2 ^ (s + 1) * m) ≤ C / ε * ε ^ ((i : ℝ) / p) := by
      rw [e]
      calc H (2 * i) ≤ ε ^ (i / p) * C := hb
        _ ≤ ε ^ ((i : ℝ) / p - 1) * C := mul_le_mul_of_nonneg_right hpow hC
        _ = C / ε * ε ^ ((i : ℝ) / p) := by
            rw [Real.rpow_sub hε0, Real.rpow_one]; ring
    have hexp : (i : ℝ) / p * (1 / 2 : ℝ) ^ (s + 1) = (m : ℝ) / (2 * p) := by
      simp only [i]; push_cast
      rw [pow_succ]
      have h2 : (2 : ℝ) ^ s * (1 / 2 : ℝ) ^ s = 1 := by rw [← mul_pow]; norm_num
      field_simp
      linear_combination (m : ℝ) * h2
    have hq : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (s + 1) := by positivity
    calc |H m| ≤ H 0 ^ (1 - (1 / 2 : ℝ) ^ (s + 1)) * H (2 ^ (s + 1) * m) ^ ((1 / 2 : ℝ) ^ (s + 1)) := hd
      _ ≤ H 0 ^ (1 - (1 / 2 : ℝ) ^ (s + 1)) * (C / ε * ε ^ ((i : ℝ) / p)) ^ ((1 / 2 : ℝ) ^ (s + 1)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hHr hb' hq) (Real.rpow_nonneg hH0 _)
      _ = H 0 ^ (1 - (1 / 2 : ℝ) ^ (s + 1)) * (C / ε) ^ ((1 / 2 : ℝ) ^ (s + 1)) *
            ε ^ ((m : ℝ) / (2 * p)) := by
          rw [Real.mul_rpow (div_nonneg hC hε0.le) (Real.rpow_nonneg hε0.le _), ← Real.rpow_mul hε0.le, hexp]
          ring
  exact OneScale.prefactor_free (a := fun _ => H 0) (b := fun _ => H m) tendsto_const_nhds tendsto_const_nhds
    (fun _ => hH0) (Real.rpow_nonneg hε0.le _) (fun r hr => Filter.Eventually.of_forall fun _ => key r hr)

/-- The two-level model violates the shift-uniform ratio bound for every `ε < 1`: the ratio `H(2(p + j))/H(2j)` tends
to `1` along shifts. Stated as: for every `ε < 1` and `p` there is a shift `j` with `H(2(p + j)) > ε H(2j)`. -/
theorem twoLevel_not_ratio {η x : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hx0 : 0 ≤ x) (hx1 : x < 1) {ε : ℝ} (hε : ε < 1)
    (p : ℕ) : ∃ j, ε * twoLevel η x (2 * j) < twoLevel η x (2 * (p + j)) := by
  -- for large `j` the decaying part is below `δ := η (1 - ε) / 2`
  have hε' : 0 < 1 - ε := by linarith
  have hδ : 0 < η * (1 - ε) / 2 := div_pos (mul_pos hη0 hε') two_pos
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hδ (show x ^ 2 < 1 by nlinarith)
  refine ⟨j, ?_⟩
  simp only [twoLevel]
  have hp : 0 ≤ 1 - η := by linarith
  have hxj : x ^ (2 * j) < η * (1 - ε) / 2 := by rw [pow_mul]; exact hj
  have hxj0 : 0 ≤ x ^ (2 * j) := by positivity
  have hxpj : 0 ≤ x ^ (2 * (p + j)) := by positivity
  rcases le_or_gt ε 0 with hε0 | hε0
  · have : ε * ((1 - η) * x ^ (2 * j) + η) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hε0 (add_nonneg (mul_nonneg hp hxj0) hη0.le)
    nlinarith [mul_nonneg hp hxpj]
  · have h1 : (1 - η) * x ^ (2 * j) ≤ x ^ (2 * j) := by nlinarith
    have h3 : 0 ≤ η * ((1 - ε) * (2 - ε)) := mul_nonneg hη0.le (mul_nonneg (by linarith) (by linarith))
    calc ε * ((1 - η) * x ^ (2 * j) + η) ≤ ε * (x ^ (2 * j) + η) := by nlinarith
      _ < ε * (η * (1 - ε) / 2 + η) := by nlinarith
      _ ≤ η := by nlinarith
      _ ≤ (1 - η) * x ^ (2 * (p + j)) + η := by nlinarith [mul_nonneg hp hxpj]

end Attempts.Positivity
