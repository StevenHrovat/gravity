/-
Proof phase, crossover workstream (c9a-crossover): the one-box statement as twist-sector equidistribution, the `(ℤ/2)ⁿ`
Fourier lemma with explicit characters (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/EQUIDIST.md`.
-/

import Mathlib

/-!
# Equidistributed twist sectors give a small electric weight, and conversely

Sectors are `k, e : Fin n → ℤ/2`; the character is `χ(k, e) = ∏ᵢ (−1)^{kᵢ eᵢ}` (`chi`). For twist partition functions `Z k`, the
electric ones are `Z_e(e) = 2^{−n} Σ_k χ(k, e) Z k` (`elecZ`), 't Hooft's relation.

* **`sum_chi`** (S): `Σ_e χ(k, e) = 2ⁿ` if `k = 0`, else `0` (orthogonality).
* **`sum_elecZ`**, **`elecZ_zero`** (S): `Σ_e Z_e(e) = Z 0` and `Z_e(0) = 2^{−n} Σ_k Z k`.
* **`sector_product`** (S): `(Σ_k Z k / Z 0) (Σ_e Z_e(e) / Z_e(0)) = 2ⁿ`, i.e. `(1 + S_tw)(1 + S_e) = 2ⁿ` (`TRANSFER.md` 1, now
  proved from the characters).
* **`electric_sum_le_of_equidist`** (S): if every twist ratio satisfies `Z k / Z 0 ≥ 1 − δ`, then the summed electric weight
  `S_e = Σ_e Z_e(e)/Z_e(0) − 1 ≤ (2ⁿ − 1) δ / (2ⁿ − (2ⁿ − 1) δ)` (sharp: equality when every nonzero ratio equals `1 − δ`).
* **`elecZ_le_deficit`** (S): for `e ≠ 0`, `Z_e(e) ≤ 2^{−n} Σ_k |Z 0 − Z k|`: each electric sector is bounded by the summed
  twist deficits.
-/

open Finset

noncomputable section

namespace ProofPhase.Crossover

/-- The sign `(−1)^x` of `x ∈ ℤ/2`. -/
def sgn2 (x : ZMod 2) : ℝ := if x = 0 then 1 else -1

/-- The character `χ(k, e) = ∏ᵢ (−1)^{kᵢ eᵢ}` of `(ℤ/2)ⁿ`. -/
def chi {n : ℕ} (k e : Fin n → ZMod 2) : ℝ := ∏ i, sgn2 (k i * e i)

theorem univ_zmod2 : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide

theorem sum_sgn2 (a : ZMod 2) : ∑ x : ZMod 2, sgn2 (a * x) = if a = 0 then 2 else 0 := by
  rw [univ_zmod2, Finset.sum_pair (by decide)]
  fin_cases a <;> simp (config := { decide := true }) [sgn2] <;> norm_num
  all_goals first | rfl | exact one_ne_zero

theorem chi_comm {n : ℕ} (k e : Fin n → ZMod 2) : chi k e = chi e k := by
  unfold chi
  exact Finset.prod_congr rfl fun i _ => by rw [mul_comm]

theorem chi_zero_right {n : ℕ} (k : Fin n → ZMod 2) : chi k 0 = 1 := by
  simp [chi, sgn2]

theorem abs_chi {n : ℕ} (k e : Fin n → ZMod 2) : |chi k e| = 1 := by
  unfold chi
  rw [Finset.abs_prod]
  exact Finset.prod_eq_one fun i _ => by unfold sgn2; split_ifs <;> simp

/-- **Orthogonality** (S). -/
theorem sum_chi {n : ℕ} (k : Fin n → ZMod 2) : ∑ e, chi k e = if k = 0 then (2 : ℝ) ^ n else 0 := by
  unfold chi
  have h := Finset.prod_univ_sum (t := fun _ : Fin n => (Finset.univ : Finset (ZMod 2)))
    (f := fun i x => sgn2 (k i * x))
  simp only [Fintype.piFinset_univ] at h
  rw [← h]
  simp only [sum_sgn2]
  by_cases hk : k = 0
  · subst hk
    simp
  · simp only [hk, ↓reduceIte]
    obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
      by_contra h
      exact hk (funext fun i => by_contra fun hi => h ⟨i, hi⟩)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The electric partition functions from the twisted ones ('t Hooft). -/
def elecZ {n : ℕ} (Z : (Fin n → ZMod 2) → ℝ) (e : Fin n → ZMod 2) : ℝ := (∑ k, chi k e * Z k) / 2 ^ n

theorem sum_elecZ {n : ℕ} (Z : (Fin n → ZMod 2) → ℝ) : ∑ e, elecZ Z e = Z 0 := by
  unfold elecZ
  rw [← Finset.sum_div, Finset.sum_comm]
  have : ∀ k, ∑ e, chi k e * Z k = (if k = 0 then (2 : ℝ) ^ n else 0) * Z k := by
    intro k
    rw [← Finset.sum_mul, sum_chi]
  simp_rw [this]
  simp

theorem elecZ_zero {n : ℕ} (Z : (Fin n → ZMod 2) → ℝ) : elecZ Z 0 = (∑ k, Z k) / 2 ^ n := by
  unfold elecZ
  simp [chi_zero_right]

/-- **The sector product** (S): `(1 + S_tw)(1 + S_e) = 2ⁿ`. -/
theorem sector_product {n : ℕ} (Z : (Fin n → ZMod 2) → ℝ) (h0 : 0 < Z 0) (hs : 0 < ∑ k, Z k) :
    ((∑ k, Z k) / Z 0) * ((∑ e, elecZ Z e) / elecZ Z 0) = 2 ^ n := by
  rw [sum_elecZ, elecZ_zero]
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  field_simp

/-- **Equidistribution ⟹ electric suppression** (S), sharp. -/
theorem electric_sum_le_of_equidist {n : ℕ} (Z : (Fin n → ZMod 2) → ℝ) (h0 : 0 < Z 0) {δ : ℝ}
    (hδ : ∀ k, k ≠ 0 → (1 - δ) * Z 0 ≤ Z k) (hδ1 : ((2 : ℝ) ^ n - 1) * δ < 2 ^ n) :
    (∑ e, elecZ Z e) / elecZ Z 0 - 1 ≤ ((2 : ℝ) ^ n - 1) * δ / (2 ^ n - (2 ^ n - 1) * δ) := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  -- Σ_k Z k ≥ Z 0 (2ⁿ − (2ⁿ − 1) δ)
  have hcard : (Finset.univ.erase (0 : Fin n → ZMod 2)).card = 2 ^ n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hsplit : ∑ k, Z k = Z 0 + ∑ k ∈ Finset.univ.erase 0, Z k := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
  have hlow : ∑ k ∈ Finset.univ.erase (0 : Fin n → ZMod 2), (1 - δ) * Z 0 ≤ ∑ k ∈ Finset.univ.erase 0, Z k :=
    Finset.sum_le_sum fun k hk => hδ k (Finset.ne_of_mem_erase hk)
  rw [Finset.sum_const, hcard, nsmul_eq_mul] at hlow
  have hpow : ((2 ^ n - 1 : ℕ) : ℝ) = (2 : ℝ) ^ n - 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  rw [hpow] at hlow
  have hS : Z 0 * (2 ^ n - (2 ^ n - 1) * δ) ≤ ∑ k, Z k := by rw [hsplit]; nlinarith
  have hden : 0 < 2 ^ n - ((2 : ℝ) ^ n - 1) * δ := by linarith
  have hSpos : 0 < ∑ k, Z k := lt_of_lt_of_le (mul_pos h0 hden) hS
  rw [sum_elecZ, elecZ_zero, div_div_eq_mul_div]
  rw [div_sub_one hSpos.ne', div_le_div_iff₀ hSpos hden]
  have e1 : (Z 0 * 2 ^ n - ∑ k, Z k) ≤ Z 0 * ((2 : ℝ) ^ n - 1) * δ := by nlinarith
  have hδ0 : 0 ≤ ((2 : ℝ) ^ n - 1) * δ * (∑ k, Z k) - (Z 0 * 2 ^ n - ∑ k, Z k) * (2 ^ n - (2 ^ n - 1) * δ) := by
    nlinarith [hS, e1, hden]
  nlinarith

/-- **Each electric sector is bounded by the summed twist deficits** (S). -/
theorem elecZ_le_deficit {n : ℕ} (Z : (Fin n → ZMod 2) → ℝ) {e : Fin n → ZMod 2} (he : e ≠ 0) :
    elecZ Z e ≤ (∑ k, |Z 0 - Z k|) / 2 ^ n := by
  unfold elecZ
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  apply div_le_div_of_nonneg_right _ h2.le
  have hz : ∑ k, chi k e = 0 := by
    simp_rw [chi_comm _ e]
    rw [sum_chi]
    simp only [he, ↓reduceIte]
  have : ∑ k, chi k e * Z k = ∑ k, chi k e * (Z k - Z 0) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hz, zero_mul, sub_zero]
  rw [this]
  calc ∑ k, chi k e * (Z k - Z 0) ≤ |∑ k, chi k e * (Z k - Z 0)| := le_abs_self _
    _ ≤ ∑ k, |chi k e * (Z k - Z 0)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |Z 0 - Z k| := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [abs_mul, abs_chi, one_mul, abs_sub_comm]

end ProofPhase.Crossover
