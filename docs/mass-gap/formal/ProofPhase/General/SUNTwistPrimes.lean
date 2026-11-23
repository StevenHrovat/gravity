/-
SU(N) primes round (sun-primes): the centre `Z_N` over the primes, its automorphisms and the Dirichlet bridge
(2026-11-23). Released under Apache 2.0.

Note: `docs/unified/SUN-PRIMES.md`, section 4.
-/

import ProofPhase.General.SUNTwistSectors
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.GaussSum
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.Finite.Basic

/-!
# Primes as the base: CRT, the sector automorphisms and the Gauss sums

Every item is **classical** mathematics, formalised here for the centre `Z_N = ZMod N` of SU(N). What is the owner's
reading (and not a theorem) is said in `docs/unified/SUN-PRIMES.md`.

**1. The centre factorises over the prime powers of `N` (`centreCRT`).** `ZMod N ≃+* Π_{p | N} ZMod (p^{v_p(N)})`
(Chinese remainder theorem, Mathlib's `ZMod.prodEquivPi`). The pieces are prime powers, not primes (`ZMod 4` is not
`ZMod 2 × ZMod 2`). The **Fourier kernel factorises** with the pieces (`stdAddChar_crt`): for coprime `m`, `n` with
`m a + n b = 1`, `ω_{mn}^j = ω_m^{b j} ω_n^{a j}`, so the electric transform of `Z_{mn}` is the tensor product of those of
`Z_m` and `Z_n`, up to the unit relabellings `j ↦ b j`, `j ↦ a j`.

**2. Prime centres.** For prime `N = p` every nontrivial sector generates the whole centre (`prime_generates`), and the
unit group `(ZMod p)ˣ` acts transitively on the nontrivial sectors (`prime_units_transitive`). For composite `N ≥ 2`
some nontrivial sector generates a proper sub-centre (`composite_subcentre`): the divisibility structure of the
N-alities.

**3. The sector automorphisms are Dirichlet's group.** A unit `m ∈ (ZMod N)ˣ` permutes the sectors `k ↦ m k` and
fixes `0` (`unitPerm`); the electric transform intertwines it with `e ↦ m⁻¹ e` (`dft_comp_unit`). Charge conjugation
`k ↦ −k` (the square of the Fourier matrix, `SUNTwistSectors`) is the unit `−1` (`unitPerm_neg_one`). The characters of
this group are the Dirichlet characters mod `N`; for a primitive one, the electric transform is the Gauss sum times the
inverse character (`elec_dirichlet`, Mathlib's `IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`):
`Σ_k ω^{−e k} χ(k) = χ⁻¹(−e) τ(χ)`. For prime `p` every nontrivial character is primitive (`isPrimitive_of_prime`) and
`τ(χ) τ(χ⁻¹, ψ⁻¹) = p` (`gaussSum_prime`), so `τ(χ)/√p` is a phase in the case `|τ(χ)|² = p`.
-/

open Finset ZMod

open scoped ComplexConjugate

noncomputable section

namespace ProofPhase.General

/-! ## 1. CRT -/

section CRT

theorem primePow_coprime (N : ℕ) :
    Pairwise (Function.onFun Nat.Coprime fun p : N.primeFactors => (p : ℕ) ^ N.factorization p) := by
  intro p q hpq
  have hp := Nat.prime_of_mem_primeFactors p.2
  have hq := Nat.prime_of_mem_primeFactors q.2
  have hne : (p : ℕ) ≠ q := fun h => hpq (Subtype.ext h)
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).2 hne)

theorem prod_primePow {N : ℕ} (hN : N ≠ 0) : ∏ p : N.primeFactors, (p : ℕ) ^ N.factorization p = N := by
  rw [Finset.prod_coe_sort N.primeFactors (fun p => p ^ N.factorization p)]
  exact Nat.factorization_prod_pow_eq_self hN

/-- **The centre factorises over the prime powers of `N`** (CRT). -/
def centreCRT (N : ℕ) (hN : N ≠ 0) : ZMod N ≃+* Π p : N.primeFactors, ZMod ((p : ℕ) ^ N.factorization p) :=
  (ZMod.ringEquivCongr (prod_primePow hN).symm).trans (ZMod.prodEquivPi _ (primePow_coprime N))

/-- `ZMod 6 ≃+* ZMod 2 × ZMod 3`, `ZMod 10 ≃+* ZMod 2 × ZMod 5` (two of the in-between `N`). -/
def centre6 : ZMod 6 ≃+* ZMod 2 × ZMod 3 := ZMod.chineseRemainder (by norm_num : Nat.Coprime 2 3)

def centre10 : ZMod 10 ≃+* ZMod 2 × ZMod 5 := ZMod.chineseRemainder (by norm_num : Nat.Coprime 2 5)

/-- **The Fourier kernel factorises over coprime parts**: `ω_{mn}^j = ω_m^{b j} ω_n^{a j}` when `m a + n b = 1`. -/
theorem stdAddChar_crt (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m * n)] (a b : ℤ) (hab : m * a + n * b = 1) (j : ℤ) :
    (stdAddChar (j : ZMod (m * n)) : ℂ) = stdAddChar ((b * j : ℤ) : ZMod m) * stdAddChar ((a * j : ℤ) : ZMod n) := by
  rw [stdAddChar_coe, stdAddChar_coe, stdAddChar_coe, ← Complex.exp_add]
  congr 1
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hab' : (m : ℂ) * a + n * b = 1 := by exact_mod_cast hab
  push_cast
  field_simp
  linear_combination (-(j : ℂ)) * hab'

end CRT

/-! ## 2. Prime centres -/

section Prime

/-- **For prime `p`, every nontrivial sector generates the centre.** -/
theorem prime_generates (p : ℕ) [Fact p.Prime] {k : ZMod p} (hk : k ≠ 0) :
    AddSubgroup.zmultiples k = ⊤ := by
  refine eq_top_iff.2 fun j _ => ?_
  refine ⟨((j * k⁻¹ : ZMod p).val : ℤ), ?_⟩
  show (((j * k⁻¹ : ZMod p).val : ℤ)) • k = j
  rw [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hk, mul_one]

/-- **For prime `p`, the units act transitively on the nontrivial sectors.** -/
theorem prime_units_transitive (p : ℕ) [Fact p.Prime] {k l : ZMod p} (hk : k ≠ 0) (hl : l ≠ 0) :
    ∃ m : (ZMod p)ˣ, (m : ZMod p) * k = l :=
  ⟨Units.mk0 (l * k⁻¹) (mul_ne_zero hl (inv_ne_zero hk)), by
    rw [Units.val_mk0, mul_assoc, inv_mul_cancel₀ hk, mul_one]⟩

/-- **For composite `N ≥ 2`, some nontrivial sector generates a proper sub-centre** (the smallest prime factor). -/
theorem composite_subcentre {N : ℕ} (hN : 2 ≤ N) (hnp : ¬ N.Prime) :
    ∃ k : ZMod N, k ≠ 0 ∧ AddSubgroup.zmultiples k ≠ ⊤ := by
  have hN1 : N ≠ 1 := by omega
  set d := N.minFac with hd
  have hdp : d.Prime := Nat.minFac_prime hN1
  have hdN : d ∣ N := Nat.minFac_dvd N
  have hdlt : d < N := by
    rcases (Nat.minFac_le (by omega : 0 < N)).lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hdp) hnp
  refine ⟨(d : ZMod N), ?_, ?_⟩
  · intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact absurd (Nat.le_of_dvd hdp.pos h0) (by omega)
  · intro htop
    have h1 : (1 : ZMod N) ∈ AddSubgroup.zmultiples (d : ZMod N) := htop ▸ AddSubgroup.mem_top _
    obtain ⟨z, hz⟩ := h1
    replace hz : z • (d : ZMod N) = 1 := hz
    have hc := congrArg (ZMod.castHom hdN (ZMod d)) hz
    rw [map_one, zsmul_eq_mul, map_mul, map_intCast, map_natCast, ZMod.natCast_self, mul_zero] at hc
    haveI : Fact (1 < d) := ⟨hdp.one_lt⟩
    exact one_ne_zero hc.symm

end Prime

/-! ## 3. Sector automorphisms and Dirichlet characters -/

section Dirichlet

variable {N : ℕ} [NeZero N]

/-- **A unit permutes the sectors**: `k ↦ m k`. -/
def unitPerm (m : (ZMod N)ˣ) : Equiv.Perm (ZMod N) := Units.mulLeft m

theorem unitPerm_apply (m : (ZMod N)ˣ) (k : ZMod N) : unitPerm m k = m * k := rfl

theorem unitPerm_zero (m : (ZMod N)ˣ) : unitPerm m 0 = 0 := mul_zero _

/-- Charge conjugation `k ↦ −k` is the unit `−1`. -/
theorem unitPerm_neg_one (k : ZMod N) : unitPerm (-1) k = -k := by
  rw [unitPerm_apply, Units.val_neg, Units.val_one, neg_one_mul]

/-- **The electric transform intertwines the sector automorphisms**: `𝓕(Φ ∘ m·)(e) = 𝓕Φ(m⁻¹ e)`. -/
theorem dft_comp_unit (Φ : ZMod N → ℂ) (m : (ZMod N)ˣ) (e : ZMod N) :
    𝓕 (fun j => Φ ((m : ZMod N) * j)) e = 𝓕 Φ (((m⁻¹ : (ZMod N)ˣ) : ZMod N) * e) := by
  rw [dft_apply, dft_apply]
  refine Fintype.sum_equiv (unitPerm m) _ _ fun j => ?_
  have hu : (m : ZMod N) * ((m⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 := Units.mul_inv m
  have h : -(j * e) = -(((m : ZMod N) * j) * (((m⁻¹ : (ZMod N)ˣ) : ZMod N) * e)) := by
    linear_combination (j * e) * hu
  rw [unitPerm_apply, h]

/-- **The electric transform of a primitive Dirichlet character is the Gauss sum times the inverse character**:
`Σ_k ω^{−e k} χ(k) = χ⁻¹(−e) τ(χ)` (Mathlib). -/
theorem elec_dirichlet {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (e : ZMod N) :
    ∑ k : ZMod N, stdAddChar (-(k * e)) * χ k = χ⁻¹ (-e) * gaussSum χ stdAddChar := by
  have h := DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum hχ e
  rw [dft_apply] at h
  simpa only [smul_eq_mul] using h

/-- **For prime `p`, every nontrivial Dirichlet character is primitive.** -/
theorem isPrimitive_of_prime (p : ℕ) [Fact p.Prime] {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    χ.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ (DirichletCharacter.conductor_dvd_level χ) with h | h
  · exact absurd ((DirichletCharacter.eq_one_iff_conductor_eq_one).2 h) hχ
  · exact h

/-- **The Gauss sum of a nontrivial character mod a prime**: `τ(χ, ψ) τ(χ⁻¹, ψ⁻¹) = p` (Mathlib). -/
theorem gaussSum_prime (p : ℕ) [Fact p.Prime] {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    gaussSum χ stdAddChar * gaussSum χ⁻¹ (stdAddChar)⁻¹ = p := by
  rw [gaussSum_mul_gaussSum_eq_card hχ (isPrimitive_stdAddChar p), ZMod.card]

/-- **For prime `p`, every nontrivial Dirichlet character is carried by the electric transform to its inverse,
times the Gauss sum.** -/
theorem elec_dirichlet_prime (p : ℕ) [Fact p.Prime] {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) (e : ZMod p) :
    ∑ k : ZMod p, stdAddChar (-(k * e)) * χ k = χ⁻¹ (-e) * gaussSum χ stdAddChar :=
  elec_dirichlet (isPrimitive_of_prime p hχ) e

end Dirichlet

end ProofPhase.General
