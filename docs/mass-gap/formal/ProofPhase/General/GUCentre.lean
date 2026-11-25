/-
Grand Unified scoping round (gu-scoping): the centre of SU(3) x SU(2) x U(1), the Z_6 that acts trivially on the
Standard Model hypercharges, charge quantisation in thirds, and the kernel of the SU(5) embedding (2026-11-23).
Released under Apache 2.0.

Note: `docs/unified/GU-SCOPING.md`, section 4.
-/

import Mathlib

/-!
# The Standard Model centre and its Z_6

Every item is **classical** mathematics (the global structure of the Standard Model gauge group; e.g. Hucks 1991,
Tong 2017), formalised here. Nothing in this file is new physics, and nothing here derives the hypercharges: they
are an **input** (`smFields`).

**Set-up.** A centre element of `SU(3) x SU(2) x U(1)` is a triple `(u, v, z)` of complex numbers: `u • 1` in SU(3)
(`u^3 = 1`), `v • 1` in SU(2) (`v^2 = 1`), and the phase `z` of U(1)_Y. It acts on a field with SU(3) triality `t`
(0 or 1), SU(2) duality `d` (0 or 1) and hypercharge `Y = q/6` by the phase `u^t v^d z^q` (`centrePhase`).

**1. The kernel is Z_6 (`sm_kernel`, `sm_kernel_cyclic`).** On the six Standard Model fields `Q_L, u_R, d_R, L_L,
e_R, H` with `q = 1, 4, -2, -3, -6, 3`, the centre elements acting trivially are exactly `(z^2, z^3, z)` with
`z^6 = 1`: the powers of `(ζ^2, ζ^3, ζ)`, `ζ = e^{2πi/6}`, a cyclic group of order 6. The generator is
`(ω, -1, ζ)` with `ω = ζ^2` a primitive cube root of unity and `ζ^3 = -1` (`gen_parts`).

**2. Its CRT split (`sm_kernel_two`, `sm_kernel_three`).** The order-2 part `(1, -1, -1)` lives on SU(2) x U(1),
the order-3 part `(ω^2, 1, ω)` on SU(3) x U(1): `Z_6 = Z_2 x Z_3` (the ring version is `centre6`, `SUNTwistPrimes`).

**3. Charge in thirds (`gen_trivial_iff`, `charge_thirds`).** The generator acts trivially on a field iff
`6 ∣ 2t + 3d + q`. Then every component (`2 T_3 = s`, `s ≡ d mod 2`) has electric charge `Q = T_3 + Y` with
`Q + t/3 ∈ ℤ`: colour singlets carry integer charge, colour triplets charge in `-1/3 + ℤ`. Conversely a colour-singlet
field with a fractional charge would not be invariant (`fractional_singlet_breaks`): the falsifiable side.

**4. SU(5) contains the quotient (`su5_embed_kernel`, `su5_embed_det`).** The map
`(A, B, z) ↦ diag(z^{-2} A, z^3 B)` into 5 x 5 matrices has determinant 1 and its kernel is exactly
`{(z^2 • 1, z^3 • 1, z) : z^6 = 1}`, the same Z_6. So the image is `(SU(3) x SU(2) x U(1)) / Z_6`.
-/

open Matrix

noncomputable section

namespace ProofPhase.General

namespace GU

/-- Centre data of a field: SU(3) triality `t` (0 or 1), SU(2) duality `d` (0 or 1), hypercharge `q = 6 Y`. -/
structure SMField where
  t : ℕ
  d : ℕ
  q : ℤ

/-- One Standard Model generation and the Higgs, convention `Q = T_3 + Y`:
`Q_L (3,2)_{1/6}`, `u_R (3,1)_{2/3}`, `d_R (3,1)_{-1/3}`, `L_L (1,2)_{-1/2}`, `e_R (1,1)_{-1}`, `H (1,2)_{1/2}`. -/
def smFields : List SMField :=
  [⟨1, 1, 1⟩, ⟨1, 0, 4⟩, ⟨1, 0, -2⟩, ⟨0, 1, -3⟩, ⟨0, 0, -6⟩, ⟨0, 1, 3⟩]

/-- The phase by which the centre element `(u, v, z)` acts on a field. -/
def centrePhase (u v z : ℂ) (f : SMField) : ℂ := u ^ f.t * v ^ f.d * z ^ f.q

/-- `(u, v, z)` acts trivially on every Standard Model field. -/
def SMTrivial (u v z : ℂ) : Prop := ∀ f ∈ smFields, centrePhase u v z f = 1

/-- **The kernel.** A centre element acts trivially on the Standard Model fields iff it is `(z^2, z^3, z)` with
`z^6 = 1`. (Then `u^3 = 1` and `v^2 = 1` hold automatically.) -/
theorem sm_kernel (u v z : ℂ) (hz : z ≠ 0) :
    SMTrivial u v z ↔ z ^ 6 = 1 ∧ u = z ^ 2 ∧ v = z ^ 3 := by
  have h2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have h3 : z ^ 3 ≠ 0 := pow_ne_zero 3 hz
  constructor
  · intro h
    have hQ := h ⟨1, 0, -2⟩ (by simp [smFields])
    have hL := h ⟨0, 1, -3⟩ (by simp [smFields])
    have hE := h ⟨0, 0, -6⟩ (by simp [smFields])
    simp only [centrePhase, pow_zero, pow_one, one_mul, mul_one, _root_.zpow_neg, zpow_ofNat] at hQ hL hE
    have hQ' : u * (z ^ 2)⁻¹ = 1 := by simpa using hQ
    have hL' : v * (z ^ 3)⁻¹ = 1 := by simpa using hL
    have hE' : (z ^ 6)⁻¹ = 1 := by simpa using hE
    exact ⟨inv_eq_one.mp hE', (mul_inv_eq_one₀ h2).mp hQ', (mul_inv_eq_one₀ h3).mp hL'⟩
  · rintro ⟨h6, rfl, rfl⟩ f hf
    simp only [smFields, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [centrePhase, pow_zero, pow_one, one_mul, mul_one, _root_.zpow_neg, zpow_ofNat]
    · rw [← h6]; ring
    · rw [← h6]; ring
    · exact mul_inv_cancel₀ h2
    · exact mul_inv_cancel₀ h3
    · rw [h6, inv_one]
    · rw [← h6]; ring

/-- The primitive sixth root of unity `ζ = e^{2πi/6}`. -/
def zeta6 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 6)

theorem zeta6_prim : IsPrimitiveRoot zeta6 6 := Complex.isPrimitiveRoot_exp 6 (by norm_num)

theorem zeta6_ne_zero : zeta6 ≠ 0 := Complex.exp_ne_zero _

/-- The generator `(ω, -1, ζ)`: `ω = ζ^2` is a primitive cube root of unity and `ζ^3 = -1`. -/
theorem gen_parts : IsPrimitiveRoot (zeta6 ^ 2) 3 ∧ zeta6 ^ 3 = -1 := by
  refine ⟨zeta6_prim.pow_of_dvd (by norm_num) (by norm_num), ?_⟩
  exact (zeta6_prim.pow_of_dvd (by norm_num : (3 : ℕ) ≠ 0) (by norm_num)).eq_neg_one_of_two_right

/-- **The kernel is cyclic of order 6**, generated by `(ζ^2, ζ^3, ζ)`. -/
theorem sm_kernel_cyclic (u v z : ℂ) (hz : z ≠ 0) :
    SMTrivial u v z ↔ ∃ k < 6, u = zeta6 ^ (2 * k) ∧ v = zeta6 ^ (3 * k) ∧ z = zeta6 ^ k := by
  rw [sm_kernel u v z hz]
  constructor
  · rintro ⟨h6, rfl, rfl⟩
    obtain ⟨k, hk, rfl⟩ := zeta6_prim.eq_pow_of_pow_eq_one h6
    exact ⟨k, hk, by ring, by ring, rfl⟩
  · rintro ⟨k, -, rfl, rfl, rfl⟩
    refine ⟨?_, by ring, by ring⟩
    rw [← pow_mul, mul_comm, pow_mul, zeta6_prim.pow_eq_one, one_pow]

/-- The generator has order exactly 6: no smaller power acts as the identity on U(1)_Y. -/
theorem gen_order : orderOf zeta6 = 6 := zeta6_prim.eq_orderOf.symm

/-- **The order-2 part** `(1, -1, -1)` (on SU(2) x U(1) only) acts trivially. -/
theorem sm_kernel_two : SMTrivial 1 (-1) (-1) := by
  rw [sm_kernel 1 (-1) (-1) (by norm_num)]; norm_num

/-- **The order-3 part** `(ω^2, 1, ω)`, `ω = ζ^2` (on SU(3) x U(1) only) acts trivially. -/
theorem sm_kernel_three : SMTrivial (zeta6 ^ 4) 1 (zeta6 ^ 2) := by
  rw [sm_kernel _ _ _ (pow_ne_zero 2 zeta6_ne_zero)]
  refine ⟨?_, by ring, ?_⟩
  · rw [← pow_mul, show 2 * 6 = 6 * 2 by rfl, pow_mul, zeta6_prim.pow_eq_one, one_pow]
  · rw [← pow_mul, show 2 * 3 = 6 by rfl, zeta6_prim.pow_eq_one]

/-- The generator acts on a field by `ζ^{2t + 3d + q}`; it is trivial iff `6 ∣ 2t + 3d + q`. -/
theorem gen_trivial_iff (f : SMField) :
    centrePhase (zeta6 ^ 2) (zeta6 ^ 3) zeta6 f = 1 ↔ (6 : ℤ) ∣ 2 * f.t + 3 * f.d + f.q := by
  have hz := zeta6_ne_zero
  have e : centrePhase (zeta6 ^ 2) (zeta6 ^ 3) zeta6 f = zeta6 ^ (2 * (f.t : ℤ) + 3 * f.d + f.q) := by
    rw [centrePhase, ← pow_mul, ← pow_mul, ← zpow_natCast zeta6 (2 * f.t), ← zpow_natCast zeta6 (3 * f.d),
      ← zpow_add₀ hz, ← zpow_add₀ hz]
    congr 1
  rw [e]
  exact_mod_cast zeta6_prim.zpow_eq_one_iff_dvd _

/-- The generator acts trivially on each Standard Model field (also a corollary of `sm_kernel_cyclic`). -/
theorem gen_trivial_sm : ∀ f ∈ smFields, (6 : ℤ) ∣ 2 * f.t + 3 * f.d + f.q := by
  intro f hf
  simp only [smFields, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- **Charge in thirds.** If `6 ∣ 2t + 3d + q`, every component with `2 T_3 = s`, `s ≡ d mod 2`, has electric
charge `Q = (3 s + q)/6` with `Q + t/3` an integer. -/
theorem charge_thirds (t d q s : ℤ) (h : 6 ∣ 2 * t + 3 * d + q) (hs : 2 ∣ s - d) :
    ∃ n : ℤ, ((3 * s + q : ℤ) : ℚ) / 6 + (t : ℚ) / 3 = n := by
  obtain ⟨n, hn⟩ : 6 ∣ 3 * s + q + 2 * t := by omega
  refine ⟨n, ?_⟩
  have : ((3 * s + q + 2 * t : ℤ) : ℚ) = 6 * n := by exact_mod_cast hn
  push_cast at this ⊢
  linarith

/-- **Charge in thirds for the Standard Model.** Every component of every Standard Model field has
`Q + t/3 ∈ ℤ`: integer charge for colour singlets, `-1/3 + ℤ` for triplets. -/
theorem charge_thirds_sm (f : SMField) (hf : f ∈ smFields) (s : ℤ) (hs : 2 ∣ s - f.d) :
    ∃ n : ℤ, ((3 * s + f.q : ℤ) : ℚ) / 6 + (f.t : ℚ) / 3 = n :=
  charge_thirds f.t f.d f.q s (gen_trivial_sm f hf) hs

/-- **The falsifiable side.** A colour-singlet field (`t = 0`) with a component of non-integer electric charge
(`6 ∤ 3 s + q`) is not invariant under the generator, so it cannot exist if the gauge group is the Z_6 quotient. -/
theorem fractional_singlet_breaks (f : SMField) (ht : f.t = 0) (s : ℤ) (hs : 2 ∣ s - f.d)
    (hfrac : ¬ (6 : ℤ) ∣ 3 * s + f.q) : centrePhase (zeta6 ^ 2) (zeta6 ^ 3) zeta6 f ≠ 1 := by
  rw [Ne, gen_trivial_iff, ht]
  intro h
  apply hfrac
  push_cast at h
  omega

/-- The SU(5) embedding `(A, B, z) ↦ diag(z^{-2} A, z^3 B)`. -/
def su5Embed (A : Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    Matrix (Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 2) ℂ :=
  fromBlocks ((z ^ 2)⁻¹ • A) 0 0 (z ^ 3 • B)

/-- The embedding lands in determinant 1. -/
theorem su5_embed_det (A : Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) (hz : z ≠ 0)
    (hA : A.det = 1) (hB : B.det = 1) : (su5Embed A B z).det = 1 := by
  rw [su5Embed, det_fromBlocks_zero₂₁, det_smul, det_smul, hA, hB]
  simp only [Fintype.card_fin, mul_one]
  rw [inv_pow, ← pow_mul, ← pow_mul]
  exact inv_mul_cancel₀ (pow_ne_zero _ hz)

/-- **The kernel of the SU(5) embedding is the same Z_6**: `diag(z^{-2} A, z^3 B) = 1` with `det A = 1` iff
`z^6 = 1`, `A = z^2 • 1`, `B = z^3 • 1`. -/
theorem su5_embed_kernel (A : Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) (hz : z ≠ 0)
    (hA : A.det = 1) : su5Embed A B z = 1 ↔ z ^ 6 = 1 ∧ A = z ^ 2 • 1 ∧ B = z ^ 3 • 1 := by
  have h2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have h3 : z ^ 3 ≠ 0 := pow_ne_zero 3 hz
  rw [su5Embed, ← fromBlocks_one, fromBlocks_inj]
  constructor
  · rintro ⟨hA1, -, -, hB1⟩
    have eA : A = z ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
      rw [← hA1, smul_smul, mul_inv_cancel₀ h2, one_smul]
    have eB : B = (z ^ 3)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [← hB1, smul_smul, inv_mul_cancel₀ h3, one_smul]
    have h6 : z ^ 6 = 1 := by
      have := hA
      rw [eA, det_smul, det_one, Fintype.card_fin, mul_one, ← pow_mul] at this
      exact this
    refine ⟨h6, eA, ?_⟩
    rw [eB]
    congr 1
    rw [inv_eq_iff_eq_inv, eq_comm, inv_eq_of_mul_eq_one_right]
    rw [← pow_add]; exact h6
  · rintro ⟨h6, rfl, rfl⟩
    refine ⟨?_, rfl, rfl, ?_⟩
    · rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
    · rw [smul_smul, show z ^ 3 * z ^ 3 = z ^ 6 by ring, h6, one_smul]

end GU

end ProofPhase.General
