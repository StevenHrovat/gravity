/-
Proof phase, cycle 8, workstream 1 (c8a-saturation): the abstract energy–entropy (Peierls / chessboard) lemma, the entropy
threshold of one placement, and the area-rate form of the saturation bound (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c8a-saturation/NOTE.md`, section 2.
-/

import ProofPhase.Saturation.Vortex

/-!
# The energy–entropy balance, abstractly

* **`energy_entropy`** (the Peierls lemma with pointwise activities): configurations `A` of a finite set, a nonnegative activity
  `h` with `h ≤ p (1 + h)` **pointwise**, and a family of witnesses (contours) `X i` such that every "bad" `A` contains one. If the
  witnesses of size `n` number at most `C Kⁿ` (entropy `log K` per element), every witness has size at least `r`, and `K p < 1`
  (energy `−log p` per element beats the entropy), then `∑_{A bad} ∏_A h ≤ C (K p)^r/(1 − K p) · ∏ (1 + h)`.
* **`peierls_of_chessboard`** (the same balance in probability form): if a chessboard-type estimate bounds the probability of
  each contour by `z^{|γ|}` (a named input: the Froehlich–Israel–Lieb–Simon estimate for reflection-positive torus measures,
  not formalised here), the probability that some contour of size `≥ r` is present is at most `C (K z)^r/(1 − K z)`. The
  estimate is a bound for **every** pattern on the torus, but it is an annealed torus statement: it does not condition on an
  arbitrary outside. Uniformity over outsides needs the pointwise form above (NOTE, section 4).
* **`satQ_lt_one_iff`**: the window of `vortex_saturation` is exactly **one placement costs less than the entropy threshold**:
  `2(d − 1)(1 − e^{−E}) < 1 ⇔ E < log(K/(K − 1))`, `K = 2(d − 1)`.
* **`tanh_half_le_satP`**: the activity `1 − e^{−E}` of the positive expansion dominates the dual (character-expansion)
  activity `tanh(E/2)` of a centre flip of cost `E`; the window is conservative, not sharp.
* **`satB_eq`**: `B = (N^d p/(q(1 − q)))^N · q^{N²}`: the area rate `q^{N²}` times a factor `e^{O(N log N)}`.
-/

open Finset MeasureTheory

open scoped Classical

noncomputable section

namespace ProofPhase.Saturation

/-! ## 1. The abstract Peierls lemma -/

/-- Grouping a sum by sizes against a geometric count: `∑_{i ∈ W} p^{size i} ≤ C (K p)^r/(1 − K p)`. -/
theorem sum_pow_size_le {ι : Type*} (W : Finset ι) (size : ι → ℕ) {p C K : ℝ} {r : ℕ} (hp : 0 ≤ p) (hC : 0 ≤ C)
    (hK : 0 ≤ K) (hKp : K * p < 1) (hr : ∀ i ∈ W, r ≤ size i)
    (hcount : ∀ n, ((W.filter fun i => size i = n).card : ℝ) ≤ C * K ^ n) :
    ∑ i ∈ W, p ^ size i ≤ C * ((K * p) ^ r / (1 - K * p)) := by
  have hq0 : 0 ≤ K * p := mul_nonneg hK hp
  have h1q : 0 < 1 - K * p := by linarith
  set M := W.sup size + 1
  have hfib : ∑ i ∈ W, p ^ size i = ∑ n ∈ range M, ((W.filter fun i => size i = n).card : ℝ) * p ^ n := by
    rw [← sum_fiberwise_of_maps_to (g := size) (t := range M)]
    · refine sum_congr rfl fun n _ => ?_
      rw [sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2], sum_const, nsmul_eq_mul]
    · intro i hi; exact mem_range.mpr (Nat.lt_succ_of_le (le_sup hi))
  rw [hfib]
  calc ∑ n ∈ range M, ((W.filter fun i => size i = n).card : ℝ) * p ^ n
      ≤ ∑ n ∈ range M, (if r ≤ n then C * (K * p) ^ n else 0) := by
        refine sum_le_sum fun n _ => ?_
        by_cases hn : r ≤ n
        · rw [ite_eq_left hn, mul_pow, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (hcount n) (pow_nonneg hp n)
        · rw [ite_eq_right hn]
          have : (W.filter fun i => size i = n) = ∅ := by
            refine filter_eq_empty_iff.mpr fun i hi he => hn ?_
            rw [← he]; exact hr i hi
          rw [this, card_empty, Nat.cast_zero, zero_mul]
    _ = C * ∑ n ∈ range M, (if r ≤ n then (K * p) ^ n else 0) := by
        rw [mul_sum]; refine sum_congr rfl fun n _ => ?_; split_ifs <;> simp
    _ ≤ C * ((K * p) ^ r / (1 - K * p)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        have hgeo : ∀ m, ∑ n ∈ range m, (if r ≤ n then (K * p) ^ n else 0) ≤ (K * p) ^ r / (1 - K * p) := by
          intro m
          calc ∑ n ∈ range m, (if r ≤ n then (K * p) ^ n else 0)
              ≤ ∑ n ∈ range (r + m), (if r ≤ n then (K * p) ^ n else 0) :=
                sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) fun n _ _ => by
                  split_ifs <;> positivity
            _ = ∑ k ∈ range m, (K * p) ^ (r + k) := by
                rw [sum_range_add]
                have : ∑ n ∈ range r, (if r ≤ n then (K * p) ^ n else 0) = 0 :=
                  sum_eq_zero fun n hn => ite_eq_right (by simp at hn; omega)
                rw [this, zero_add]
                exact sum_congr rfl fun k _ => ite_eq_left (by omega)
            _ = (K * p) ^ r * ∑ k ∈ range m, (K * p) ^ k := by rw [mul_sum]; simp_rw [pow_add]
            _ ≤ (K * p) ^ r * (1 / (1 - K * p)) := by
                refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hq0 r)
                rw [geom_sum_eq (by linarith : K * p ≠ 1), le_div_iff₀ h1q]
                rw [div_mul_eq_mul_div, div_le_one_of_neg (by linarith)] <;> nlinarith [pow_nonneg hq0 m]
            _ = (K * p) ^ r / (1 - K * p) := by ring
        exact hgeo M

/-- **The abstract energy–entropy (Peierls) lemma**, with pointwise activities. -/
theorem energy_entropy {V ι : Type*} [Fintype V] [DecidableEq V] (h : V → ℝ) {p : ℝ} (hp : 0 ≤ p) (h0 : ∀ v, 0 ≤ h v)
    (hle : ∀ v, h v ≤ p * (1 + h v)) (Bad : Finset V → Prop) [DecidablePred Bad] (W : Finset ι) (X : ι → Finset V)
    (hw : ∀ A, Bad A → ∃ i ∈ W, X i ⊆ A) (size : ι → ℕ) (hsize : ∀ i ∈ W, size i ≤ (X i).card) {C K : ℝ} {r : ℕ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hKp : K * p < 1) (hp1 : p ≤ 1) (hr : ∀ i ∈ W, r ≤ size i)
    (hcount : ∀ n, ((W.filter fun i => size i = n).card : ℝ) ≤ C * K ^ n) :
    ∑ A ∈ (univ : Finset V).powerset.filter Bad, ∏ v ∈ A, h v ≤ C * ((K * p) ^ r / (1 - K * p)) * ∏ v, (1 + h v) := by
  have hmain := AreaLaw.Twist.sum_surv_le h h0 hle Bad W X hw
  have hW : ∑ i ∈ W, p ^ (X i).card ≤ ∑ i ∈ W, p ^ size i :=
    sum_le_sum fun i hi => pow_le_pow_of_le_one hp hp1 (hsize i hi)
  refine hmain.trans (mul_le_mul_of_nonneg_right (hW.trans (sum_pow_size_le W size hp hC hK hKp hr hcount))
    (prod_nonneg fun v _ => by linarith [h0 v]))

/-- **Peierls from a chessboard-type estimate** (probability form). If every contour `γ ∈ W` is present with probability
    at most `z^{size γ}` (the named chessboard input), contours number at most `C Kⁿ` by size and have size `≥ r`, and `K z < 1`,
    then some contour is present with probability at most `C (K z)^r/(1 − K z)`. -/
theorem peierls_of_chessboard {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : Finset ι) (present : ι → Set Ω)
    (size : ι → ℕ) {z C K : ℝ} {r : ℕ} (hz : 0 ≤ z) (hC : 0 ≤ C) (hK : 0 ≤ K) (hKz : K * z < 1)
    (hchess : ∀ i ∈ W, P.real (present i) ≤ z ^ size i) (hr : ∀ i ∈ W, r ≤ size i)
    (hcount : ∀ n, ((W.filter fun i => size i = n).card : ℝ) ≤ C * K ^ n) :
    P.real (⋃ i ∈ W, present i) ≤ C * ((K * z) ^ r / (1 - K * z)) := by
  calc P.real (⋃ i ∈ W, present i) ≤ ∑ i ∈ W, P.real (present i) := measureReal_biUnion_finset_le W present
    _ ≤ ∑ i ∈ W, z ^ size i := sum_le_sum hchess
    _ ≤ _ := sum_pow_size_le W size hz hC hK hKz hr hcount

/-! ## 2. The entropy threshold of one placement -/

/-- **The window is "one placement costs less than the entropy threshold"**: for `K = 2(d − 1) > 1`,
    `K (1 − e^{−E}) < 1 ⇔ E < log(K/(K − 1))`. -/
theorem satQ_lt_one_iff {d : ℕ} (hd : 2 ≤ d) (E : ℝ) :
    satQ d E < 1 ↔ E < Real.log (2 * ((d : ℝ) - 1) / (2 * ((d : ℝ) - 1) - 1)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set K := 2 * ((d : ℝ) - 1) with hK
  have hK1 : 1 < K := by rw [hK]; linarith
  have hKpos : 0 < K - 1 := by linarith
  unfold satQ satP
  rw [← hK]
  rw [Real.lt_log_iff_exp_lt (div_pos (by linarith) hKpos)]
  constructor
  · intro h
    have h1 : (K - 1) / K < Real.exp (-E) := by
      rw [div_lt_iff₀ (by linarith)]; nlinarith
    have h2 : Real.exp E = 1 / Real.exp (-E) := by rw [Real.exp_neg, one_div, inv_inv]
    rw [h2, div_lt_div_iff₀ (Real.exp_pos _) hKpos, one_mul]
    rw [div_lt_iff₀ (by linarith)] at h1
    linarith
  · intro h
    have h2 : Real.exp E = 1 / Real.exp (-E) := by rw [Real.exp_neg, one_div, inv_inv]
    rw [h2, div_lt_div_iff₀ (Real.exp_pos _) hKpos, one_mul] at h
    nlinarith

/-- The dual (character-expansion) activity of a centre flip of cost `E`, `tanh(E/2)`, is at most the positive-expansion
    activity `1 − e^{−E}` used by `vortex_saturation`. -/
theorem tanh_half_le_satP {E : ℝ} (hE : 0 ≤ E) : Real.tanh (E / 2) ≤ satP E := by
  unfold satP
  have ht : Real.tanh (E / 2) = (1 - Real.exp (-E)) / (1 + Real.exp (-E)) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    have he : Real.exp (-E) = Real.exp (-(E / 2)) * Real.exp (-(E / 2)) := by rw [← Real.exp_add]; ring_nf
    have hp : 0 < Real.exp (E / 2) := Real.exp_pos _
    have hm : Real.exp (E / 2) * Real.exp (-(E / 2)) = 1 := by rw [← Real.exp_add]; simp
    rw [he]
    field_simp
    nlinarith [hm]
  rw [ht]
  have h0 : 0 ≤ 1 - Real.exp (-E) := by linarith [Real.exp_le_one_iff.mpr (show -E ≤ 0 by linarith)]
  exact div_le_self h0 (by linarith [Real.exp_pos (-E)])

/-! ## 3. The area rate -/

/-- **The area-rate form**: `B = (N^d p/(q(1 − q)))^N · q^{N·N}` for `q ≠ 0`, `N ≥ 1`. -/
theorem satB_eq {d N : ℕ} {E : ℝ} (hN : 1 ≤ N) (hq : satQ d E ≠ 0) :
    satB d N E = ((N : ℝ) ^ d * satP E / (satQ d E * (1 - satQ d E))) ^ N * satQ d E ^ (N * N) := by
  unfold satB
  have h1 : satQ d E ^ (N - 1) = satQ d E ^ N / satQ d E := by
    rw [eq_div_iff hq, ← pow_succ]; congr 1; omega
  rw [h1, pow_mul, ← mul_pow]
  congr 1
  field_simp

end ProofPhase.Saturation
