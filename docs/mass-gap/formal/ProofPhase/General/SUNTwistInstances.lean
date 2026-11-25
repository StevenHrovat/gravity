/-
SU(N) primes round (sun-primes): the owner's candidates N = 2, 3, 5, 11 as explicit instances (2026-11-23). Released
under Apache 2.0.

Note: `docs/unified/SUN-PRIMES.md`, section 5.
-/

import ProofPhase.General.SUNTwistWilson
import ProofPhase.General.SUNTwistPrimes

/-!
# Instances: SU(2), SU(3), SU(5), SU(11)

Every `N` in between (and beyond) is covered by the general theorems of `SUNTwistWilson`, `SUNTwistSectors` and
`SUNTwistPrimes`; this file only instantiates them, so that each candidate is checked by the kernel with its own `N`.

For each `N ∈ {2, 3, 5, 11}`, every `L ≥ 1`, every even `T`, every spatial background twist `P`, every plane `c`:
* `0 < Z_tw,k < Z` for every `β ≠ 0` and every `k ≠ 0` (`suN_Ztw_lt`, `suN_ratio`), `Z_tw,k = Z_tw,N−k` (`suN_pairs`);
* the electric sectors are real, nonnegative, sum to `Z`, and some `e ≠ 0` has `Z_e > 0` (`suN_elec`);
* `N` is prime: every nontrivial sector generates the centre, `|(ZMod N)ˣ| = N − 1` (`suN_prime`);
* the Fourier matrix is a half-turn for `N = 2` and a quarter-turn (`F² = C ≠ 1`, `F⁴ = 1`) for `N = 3, 5, 11`;
* every nontrivial Dirichlet character mod `N` is primitive and its electric transform is `χ⁻¹(−e) τ(χ)`.

In-between composite examples: `ZMod 6 ≃+* ZMod 2 × ZMod 3`, `ZMod 10 ≃+* ZMod 2 × ZMod 5` (`centre6`, `centre10`), and
for `N = 4, 6, 8, 9, 10` a nontrivial sector generates a proper sub-centre (`composite_examples`).
-/

open MeasureTheory Finset AreaLaw.Concrete ProofPhase.RouteB ProofPhase.Flip

noncomputable section

namespace ProofPhase.General

instance fact_one_lt_two : Fact (1 < 2) := ⟨by norm_num⟩
instance fact_one_lt_three : Fact (1 < 3) := ⟨by norm_num⟩
instance fact_one_lt_five : Fact (1 < 5) := ⟨by norm_num⟩
instance fact_one_lt_eleven : Fact (1 < 11) := ⟨by norm_num⟩
instance fact_two_lt_three : Fact (2 < 3) := ⟨by norm_num⟩
instance fact_two_lt_five : Fact (2 < 5) := ⟨by norm_num⟩
instance fact_two_lt_eleven : Fact (2 < 11) := ⟨by norm_num⟩
instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
instance fact_prime_three : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance fact_prime_eleven : Fact (Nat.Prime 11) := ⟨by norm_num⟩

section Instances

variable (L : ℕ) [NeZero L] (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) {T : ℕ} [NeZero T]

/-! ## The strict twist bound -/

/-- **SU(2): `Z_tw,1 < Z`** (`β ≠ 0`, `T` even), by the `Z_N` route. This is the statement of `su2_Ztw_lt_Z`
(`Flip/Strict`), proved independently; the identification of `zN 1 = e^{πi} · 1` with `negOneSU2` and of the two
SU(2) chain weights is not formalised here. -/
theorem su2N_Ztw_lt {β : ℝ} (hβ : β ≠ 0) (hT : Even T) : sunZtw 2 L β P c T 1 < sunZ 2 L β P T :=
  sunZtw_lt 2 L hβ P c hT one_ne_zero

/-- **SU(3): `Z_tw,k < Z` for `k = 1, 2`**, and `Z_tw,1 = Z_tw,2`. -/
theorem su3_Ztw_lt {β : ℝ} (hβ : β ≠ 0) (hT : Even T) {k : ZMod 3} (hk : k ≠ 0) :
    sunZtw 3 L β P c T k < sunZ 3 L β P T :=
  sunZtw_lt 3 L hβ P c hT hk

theorem su3_pairs (β : ℝ) (hT : Even T) : sunZtw 3 L β P c T 1 = sunZtw 3 L β P c T 2 := by
  rw [← sunZtw_neg 3 L β P c hT 2]; rfl

/-- **SU(5): `Z_tw,k < Z` for `k = 1, …, 4`**, and `Z_tw,1 = Z_tw,4`, `Z_tw,2 = Z_tw,3`. -/
theorem su5_Ztw_lt {β : ℝ} (hβ : β ≠ 0) (hT : Even T) {k : ZMod 5} (hk : k ≠ 0) :
    sunZtw 5 L β P c T k < sunZ 5 L β P T :=
  sunZtw_lt 5 L hβ P c hT hk

theorem su5_pairs (β : ℝ) (hT : Even T) :
    sunZtw 5 L β P c T 1 = sunZtw 5 L β P c T 4 ∧ sunZtw 5 L β P c T 2 = sunZtw 5 L β P c T 3 :=
  ⟨by rw [← sunZtw_neg 5 L β P c hT 4]; rfl, by rw [← sunZtw_neg 5 L β P c hT 3]; rfl⟩

/-- **SU(11): `Z_tw,k < Z` for `k = 1, …, 10`**, and `Z_tw,k = Z_tw,11−k`. -/
theorem su11_Ztw_lt {β : ℝ} (hβ : β ≠ 0) (hT : Even T) {k : ZMod 11} (hk : k ≠ 0) :
    sunZtw 11 L β P c T k < sunZ 11 L β P T :=
  sunZtw_lt 11 L hβ P c hT hk

theorem su11_pairs (β : ℝ) (hT : Even T) (k : ZMod 11) : sunZtw 11 L β P c T k = sunZtw 11 L β P c T (11 - k) := by
  rw [show (11 : ZMod 11) - k = -k by rw [show (11 : ZMod 11) = 0 from rfl, zero_sub], sunZtw_neg 11 L β P c hT]

/-- **The twist ratio `c_k ∈ (0, 1)`** for the four candidates. -/
theorem suN_ratio {β : ℝ} (hβ : β ≠ 0) (hT : Even T) :
    (∀ k : ZMod 2, k ≠ 0 → 0 < sunZtw 2 L β P c T k / sunZ 2 L β P T ∧ sunZtw 2 L β P c T k / sunZ 2 L β P T < 1) ∧
    (∀ k : ZMod 3, k ≠ 0 → 0 < sunZtw 3 L β P c T k / sunZ 3 L β P T ∧ sunZtw 3 L β P c T k / sunZ 3 L β P T < 1) ∧
    (∀ k : ZMod 5, k ≠ 0 → 0 < sunZtw 5 L β P c T k / sunZ 5 L β P T ∧ sunZtw 5 L β P c T k / sunZ 5 L β P T < 1) ∧
    (∀ k : ZMod 11, k ≠ 0 →
      0 < sunZtw 11 L β P c T k / sunZ 11 L β P T ∧ sunZtw 11 L β P c T k / sunZ 11 L β P T < 1) :=
  ⟨fun _ hk => sunTwistRatio_mem 2 L hβ P c hT hk, fun _ hk => sunTwistRatio_mem 3 L hβ P c hT hk,
    fun _ hk => sunTwistRatio_mem 5 L hβ P c hT hk, fun _ hk => sunTwistRatio_mem 11 L hβ P c hT hk⟩

/-! ## Electric sectors -/

/-- **Electric sectors of SU(5) and SU(11)**: real, nonnegative, `Z_e = Z_{N−e}`, summing to `Z`, and some `e ≠ 0`
carries a strictly positive weight (`β ≠ 0`). -/
theorem suN_elec {β : ℝ} (hβ : β ≠ 0) (hT : Even T) :
    (∀ e : ZMod 5, (sunZe 5 L β P c T e).im = 0 ∧ 0 ≤ (sunZe 5 L β P c T e).re ∧
      sunZe 5 L β P c T (-e) = sunZe 5 L β P c T e) ∧
    ∑ e, sunZe 5 L β P c T e = (sunZ 5 L β P T : ℂ) ∧ (∃ e : ZMod 5, e ≠ 0 ∧ 0 < (sunZe 5 L β P c T e).re) ∧
    (∀ e : ZMod 11, (sunZe 11 L β P c T e).im = 0 ∧ 0 ≤ (sunZe 11 L β P c T e).re ∧
      sunZe 11 L β P c T (-e) = sunZe 11 L β P c T e) ∧
    ∑ e, sunZe 11 L β P c T e = (sunZ 11 L β P T : ℂ) ∧ (∃ e : ZMod 11, e ≠ 0 ∧ 0 < (sunZe 11 L β P c T e).re) :=
  ⟨fun e => ⟨sunZe_im 5 L β P c hT e, sunZe_nonneg 5 L β P c hT e, sunZe_neg 5 L β P c hT e⟩,
    sum_sunZe 5 L β P c T, exists_sunZe_pos 5 L hβ P c hT,
    fun e => ⟨sunZe_im 11 L β P c hT e, sunZe_nonneg 11 L β P c hT e, sunZe_neg 11 L β P c hT e⟩,
    sum_sunZe 11 L β P c T, exists_sunZe_pos 11 L hβ P c hT⟩

end Instances

/-! ## Fourier matrix: half-turn for SU(2), quarter-turn for SU(3), SU(5), SU(11) -/

theorem suN_fourier :
    fourierMat 2 * fourierMat 2 = 1 ∧
    (fourierMat 3 * fourierMat 3 = conjMat 3 ∧ fourierMat 3 * fourierMat 3 ≠ 1 ∧ fourierMat 3 ^ 4 = 1) ∧
    (fourierMat 5 * fourierMat 5 = conjMat 5 ∧ fourierMat 5 * fourierMat 5 ≠ 1 ∧ fourierMat 5 ^ 4 = 1) ∧
    (fourierMat 11 * fourierMat 11 = conjMat 11 ∧ fourierMat 11 * fourierMat 11 ≠ 1 ∧ fourierMat 11 ^ 4 = 1) :=
  ⟨fourierMat_two_sq, ⟨fourierMat_mul_self, fourierMat_sq_ne_one, fourierMat_pow_four⟩,
    ⟨fourierMat_mul_self, fourierMat_sq_ne_one, fourierMat_pow_four⟩,
    ⟨fourierMat_mul_self, fourierMat_sq_ne_one, fourierMat_pow_four⟩⟩

/-! ## Prime structure -/

/-- **2, 3, 5, 11 are prime**: every nontrivial sector generates the centre, and the sector automorphism group
`(ZMod N)ˣ` has `N − 1` elements (1, 2, 4, 10). -/
theorem suN_prime :
    (∀ k : ZMod 2, k ≠ 0 → AddSubgroup.zmultiples k = ⊤) ∧ (∀ k : ZMod 3, k ≠ 0 → AddSubgroup.zmultiples k = ⊤) ∧
    (∀ k : ZMod 5, k ≠ 0 → AddSubgroup.zmultiples k = ⊤) ∧ (∀ k : ZMod 11, k ≠ 0 → AddSubgroup.zmultiples k = ⊤) ∧
    Fintype.card (ZMod 2)ˣ = 1 ∧ Fintype.card (ZMod 3)ˣ = 2 ∧ Fintype.card (ZMod 5)ˣ = 4 ∧
    Fintype.card (ZMod 11)ˣ = 10 :=
  ⟨fun _ hk => prime_generates 2 hk, fun _ hk => prime_generates 3 hk, fun _ hk => prime_generates 5 hk,
    fun _ hk => prime_generates 11 hk, by rw [ZMod.card_units 2], by rw [ZMod.card_units 3],
    by rw [ZMod.card_units 5], by rw [ZMod.card_units 11]⟩

/-- **SU(3): the sector automorphisms are `{1, −1}`, i.e. the identity and charge conjugation.** -/
theorem su3_units (m : (ZMod 3)ˣ) : m = 1 ∨ m = -1 := by
  fin_cases m <;> simp <;> decide

/-- **The Dirichlet bridge for SU(5) and SU(11)**: every nontrivial Dirichlet character mod 5 (mod 11) is primitive and
the electric transform carries it to `χ⁻¹(−e) τ(χ)`, with `τ(χ) τ(χ⁻¹, ψ⁻¹) = 5` (`= 11`). -/
theorem suN_dirichlet :
    (∀ χ : DirichletCharacter ℂ 5, χ ≠ 1 → χ.IsPrimitive ∧
      (∀ e : ZMod 5, ∑ k : ZMod 5, ZMod.stdAddChar (-(k * e)) * χ k = χ⁻¹ (-e) * gaussSum χ ZMod.stdAddChar) ∧
      gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ (ZMod.stdAddChar)⁻¹ = 5) ∧
    (∀ χ : DirichletCharacter ℂ 11, χ ≠ 1 → χ.IsPrimitive ∧
      (∀ e : ZMod 11, ∑ k : ZMod 11, ZMod.stdAddChar (-(k * e)) * χ k = χ⁻¹ (-e) * gaussSum χ ZMod.stdAddChar) ∧
      gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ (ZMod.stdAddChar)⁻¹ = 11) :=
  ⟨fun _ hχ => ⟨isPrimitive_of_prime 5 hχ, elec_dirichlet_prime 5 hχ, by exact_mod_cast gaussSum_prime 5 hχ⟩,
    fun _ hχ => ⟨isPrimitive_of_prime 11 hχ, elec_dirichlet_prime 11 hχ, by exact_mod_cast gaussSum_prime 11 hχ⟩⟩

/-- **In-between composite `N`**: a nontrivial sector generates a proper sub-centre (`N = 4, 6, 8, 9, 10`). -/
theorem composite_examples :
    (∃ k : ZMod 4, k ≠ 0 ∧ AddSubgroup.zmultiples k ≠ ⊤) ∧ (∃ k : ZMod 6, k ≠ 0 ∧ AddSubgroup.zmultiples k ≠ ⊤) ∧
    (∃ k : ZMod 8, k ≠ 0 ∧ AddSubgroup.zmultiples k ≠ ⊤) ∧ (∃ k : ZMod 9, k ≠ 0 ∧ AddSubgroup.zmultiples k ≠ ⊤) ∧
    (∃ k : ZMod 10, k ≠ 0 ∧ AddSubgroup.zmultiples k ≠ ⊤) :=
  ⟨composite_subcentre (by norm_num) (by norm_num), composite_subcentre (by norm_num) (by norm_num),
    composite_subcentre (by norm_num) (by norm_num), composite_subcentre (by norm_num) (by norm_num),
    composite_subcentre (by norm_num) (by norm_num)⟩

end ProofPhase.General
