/-
SU(N) primes round (sun-primes): the `Z_N` electric sectors and the Fourier matrix (2026-11-23). Released under
Apache 2.0.

Note: `docs/unified/SUN-PRIMES.md`, section 3.
-/

import Mathlib.Analysis.Fourier.ZMod

/-!
# Electric sectors of `Z_N`: the discrete Fourier transform, a half-turn for `N = 2` and a quarter-turn for `N ≥ 3`

**Setting.** `Z : ZMod N → ℝ`, the twisted partition functions `Z_k` (twist by the centre element `ω^k`,
`ω = e^{2πi/N}`), even: `Z_{−k} = Z_k` (proved for the SU(N) Wilson chain in `SUNTwistWilson`). `ψ` is Mathlib's standard
additive character `ψ(x) = e^{2πi x/N}` and `𝓕` the discrete Fourier transform `𝓕Φ(e) = Σ_k ψ(−k e) Φ(k)`.

**1. Electric sectors (`elecZ`).** `Z_e = (1/N) Σ_k ω^{−ek} Z_k = (1/N) 𝓕Z(e)`. For even `Z`:
* `Z_e` is real (`elecZ_im`) and `Z_e = Z_{−e}` (`elecZ_neg`), i.e. `Z_e = Z_{N−e}`;
* inversion: `Z_k = Σ_e ω^{ek} Z_e` (`twisted_eq_sum_elec`), and `Σ_e Z_e = Z_0` (`sum_elecZ`).
Nonnegativity of `Z_e` on the SU(N) Wilson chain is a theorem (reflection positivity, `ZFam.elec_nonneg`), not a
hypothesis.

**2. The Fourier matrix (`fourierMat`, `F_{jk} = ω^{jk}/√N`).**
* `F` is unitary (`fourierMat_unitary`: `F Fᴴ = 1`);
* `F² = C`, the conjugation matrix `C_{jk} = [j + k = 0]`, i.e. `k ↦ −k` (`fourierMat_mul_self`);
* `C² = 1`, so `F⁴ = 1` (`fourierMat_pow_four`);
* `N = 2`: `C = 1` and `F² = 1`, a **half-turn** (`fourierMat_two_sq`, the Hadamard matrix);
* `N ≥ 3`: `F² = C ≠ 1`, so `F` has order exactly 4, a **quarter-turn** whose square is the N-ality pairing
  (`fourierMat_sq_ne_one`).

**Claim discipline.** Classical (discrete Fourier analysis on `ℤ/Nℤ`), formalised for every `N`. Reading the Fourier
matrix as the electric-magnetic duality of SU(N), its square as charge conjugation, is the standard 't Hooft picture
[classical]; the transfer-matrix reading `Z_e / Z_0 = e^{−T (E_e − E_0)}` is not formalised here (`zn_tunnel_check.py`,
numerical, in the tunnelling model).
-/

open Finset ZMod

open scoped ComplexConjugate

noncomputable section

namespace ProofPhase.General

section ZNFourier

variable {N : ℕ} [NeZero N]

/-- **The electric-sector partition function** `Z_e = (1/N) Σ_k ω^{−e k} Z_k`. -/
def elecZ (Z : ZMod N → ℝ) (e : ZMod N) : ℂ := (N : ℂ)⁻¹ * 𝓕 (fun k => (Z k : ℂ)) e

theorem elecZ_eq (Z : ZMod N → ℝ) (e : ZMod N) :
    elecZ Z e = (N : ℂ)⁻¹ * ∑ k, stdAddChar (-(k * e)) * (Z k : ℂ) := by
  rw [elecZ, dft_apply]; simp only [smul_eq_mul]

theorem dft_even_conj (Z : ZMod N → ℝ) (hZ : ∀ k, Z (-k) = Z k) (e : ZMod N) :
    conj (𝓕 (fun k => (Z k : ℂ)) e) = 𝓕 (fun k => (Z k : ℂ)) e := by
  rw [dft_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ fun k => ?_
  simp only [smul_eq_mul, map_mul, Complex.conj_ofReal, Equiv.neg_apply]
  rw [← AddChar.map_neg_eq_conj, hZ]
  congr 2; ring

/-- **`Z_e` is real** for even `Z`. -/
theorem elecZ_im (Z : ZMod N → ℝ) (hZ : ∀ k, Z (-k) = Z k) (e : ZMod N) : (elecZ Z e).im = 0 := by
  have h := dft_even_conj Z hZ e
  have hi := congrArg Complex.im h
  rw [Complex.conj_im] at hi
  have h0 : (𝓕 (fun k => (Z k : ℂ)) e).im = 0 := by linarith
  rw [elecZ, Complex.mul_im, h0, mul_zero, zero_add]
  have : ((N : ℂ)⁻¹).im = 0 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_im]
  rw [this, zero_mul]

/-- **`Z_e = Z_{−e}`** (`= Z_{N−e}`) for even `Z`. -/
theorem elecZ_neg (Z : ZMod N → ℝ) (hZ : ∀ k, Z (-k) = Z k) (e : ZMod N) : elecZ Z (-e) = elecZ Z e := by
  have h := congrFun (dft_comp_neg (fun k => (Z k : ℂ))) e
  simp only [hZ] at h
  rw [elecZ, elecZ, ← h]

/-- **Inversion**: `Z_k = Σ_e ω^{e k} Z_e`. -/
theorem twisted_eq_sum_elec (Z : ZMod N → ℝ) (k : ZMod N) :
    (Z k : ℂ) = ∑ e, stdAddChar (e * k) * elecZ Z e := by
  have h := congrFun (LinearEquiv.symm_apply_apply (dft (N := N) (E := ℂ)) (fun k => (Z k : ℂ))) k
  rw [invDFT_apply] at h
  rw [← h, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun e _ => ?_
  rw [elecZ, smul_eq_mul]; ring

/-- **`Σ_e Z_e = Z_0`.** -/
theorem sum_elecZ (Z : ZMod N → ℝ) : ∑ e, elecZ Z e = (Z 0 : ℂ) := by
  rw [twisted_eq_sum_elec Z 0]
  simp only [mul_zero, AddChar.map_zero_eq_one, one_mul]

/-! ## The Fourier matrix -/

/-- `√N` as a complex number. -/
def sqrtN (N : ℕ) : ℂ := ((Real.sqrt N : ℝ) : ℂ)

theorem sqrtN_mul_self : sqrtN N * sqrtN N = N := by
  rw [sqrtN, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]

theorem sqrtN_ne_zero : sqrtN N ≠ 0 := by
  intro h
  have := sqrtN_mul_self (N := N)
  rw [h, zero_mul] at this
  exact NeZero.ne (N : ℂ) this.symm

theorem conj_sqrtN : conj (sqrtN N) = sqrtN N := Complex.conj_ofReal _

/-- **The Fourier matrix** `F_{jk} = ω^{jk}/√N`. -/
def fourierMat (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ := fun j k => (sqrtN N)⁻¹ * stdAddChar (j * k)

/-- **The conjugation matrix** `C_{jk} = [j + k = 0]` (`k ↦ −k`, the N-ality pairing). -/
def conjMat (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ := fun j k => if j + k = 0 then 1 else 0

theorem sum_char_mul (b : ZMod N) : ∑ k : ZMod N, (stdAddChar (k * b) : ℂ) = if b = 0 then (N : ℂ) else 0 := by
  rw [AddChar.sum_mulShift b (isPrimitive_stdAddChar N), ZMod.card]
  split_ifs <;> simp

theorem inv_sqrtN_sq : (sqrtN N)⁻¹ * (sqrtN N)⁻¹ = (N : ℂ)⁻¹ := by
  rw [← mul_inv, sqrtN_mul_self]

/-- **`F² = C`.** -/
theorem fourierMat_mul_self : fourierMat N * fourierMat N = conjMat N := by
  ext j l
  rw [Matrix.mul_apply]
  have e : ∀ k, fourierMat N j k * fourierMat N k l = (N : ℂ)⁻¹ * stdAddChar (k * (j + l)) := by
    intro k
    simp only [fourierMat]
    rw [← inv_sqrtN_sq, mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
    congr 2; ring
  simp_rw [e]
  rw [← mul_sum, sum_char_mul, conjMat]
  split_ifs
  · exact inv_mul_cancel₀ (NeZero.ne _)
  · rw [mul_zero]

/-- **`F` is unitary**: `F Fᴴ = 1`. -/
theorem fourierMat_unitary : fourierMat N * (fourierMat N).conjTranspose = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have e : ∀ k, fourierMat N j k * (fourierMat N).conjTranspose k l = (N : ℂ)⁻¹ * stdAddChar (k * (j - l)) := by
    intro k
    simp only [fourierMat, Matrix.conjTranspose_apply, star_mul', RCLike.star_def, map_inv₀]
    rw [conj_sqrtN, ← AddChar.map_neg_eq_conj, ← inv_sqrtN_sq, mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
    congr 2; ring
  simp_rw [e]
  rw [← mul_sum, sum_char_mul, Matrix.one_apply]
  by_cases h : j = l
  · rw [if_pos (sub_eq_zero.2 h), if_pos h]; exact inv_mul_cancel₀ (NeZero.ne _)
  · rw [if_neg (sub_ne_zero.2 h), if_neg h, mul_zero]

/-- **`C² = 1`.** -/
theorem conjMat_mul_self : conjMat N * conjMat N = 1 := by
  ext j l
  rw [Matrix.mul_apply, sum_eq_single (-j)]
  · simp only [conjMat, add_neg_cancel, if_true, one_mul, Matrix.one_apply, neg_add_eq_zero]
  · intro k _ hk
    simp only [conjMat]
    rw [if_neg (fun h => hk (eq_neg_of_add_eq_zero_right h)), zero_mul]
  · intro h; exact absurd (mem_univ _) h

/-- **`F⁴ = 1`.** -/
theorem fourierMat_pow_four : fourierMat N ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, fourierMat_mul_self, conjMat_mul_self]

/-- **`N = 2`: the Fourier matrix is a half-turn**, `F² = 1` (Hadamard). -/
theorem fourierMat_two_sq : fourierMat 2 * fourierMat 2 = 1 := by
  rw [fourierMat_mul_self]
  have h2 : ∀ j k : ZMod 2, (j + k = 0 ↔ j = k) := by decide
  ext j k
  simp only [conjMat, Matrix.one_apply, h2]

/-- **`N ≥ 3`: the Fourier matrix is a quarter-turn**, `F² = C ≠ 1` (order exactly 4). -/
theorem fourierMat_sq_ne_one [Fact (2 < N)] : fourierMat N * fourierMat N ≠ 1 := by
  rw [fourierMat_mul_self]
  intro h
  have := congrFun (congrFun h 1) (-1)
  simp only [conjMat, add_neg_cancel, if_true, Matrix.one_apply] at this
  rw [if_neg (fun h1 => ZMod.neg_one_ne_one h1.symm)] at this
  exact one_ne_zero this

end ZNFourier

end ProofPhase.General
