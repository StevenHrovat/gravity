/-
Attempt r3-monotone (round 3, attempt 2), 2026-11-21. Released under Apache 2.0.

# Twist eaters: the centre twist is classically free exactly when the centre element is a commutator

Note: `docs/mass-gap/weak-coupling/attempts/r3-monotone/NOTE.md`, section 4.

The 't Hooft twist with centre element `c` in the `(p, q)` plane of a periodic lattice (sites `Fin d → ZMod L`) multiplies one
`(p, q)` plaquette per transverse position, the one at `x p = x q = −1`, by `c⁻¹` (the reverse orientation by `c`). A configuration
is *twisted-flat* if every twisted plaquette variable is `1`; for any plaquette action with its minimum at the identity
(Wilson's included) a twisted-flat configuration has action zero.

What is proved:
1. `prod_plaq2_comm`, `no_flat_twist_comm`: in an **abelian** group, the product of the plaquette variables over a periodic
   two-dimensional cross-section is `1`, so a twisted-flat configuration forces `c = 1`. For U(1) and Z₂ every twist with `c ≠ 1`
   costs action in every cross-section.
2. `eater_plaq`, `eater_twisted_flat`: in **any** group, if `c = a b a⁻¹ b⁻¹`, the *twist eater* (`a` on the `p`-links of the slice
   `x p = −1`, `b` on the `q`-links of the slice `x q = −1`, `1` elsewhere) is twisted-flat, in every dimension `d` and every size `L`.
3. `su2_commutator`: in SU(2), `−1` is a commutator (`A = diag(i, −i)`, `B = ((0, 1), (−1, 0))`), hence `su2_twist_eater`: the
   SU(2) twisted torus has a configuration of zero action.

Reading (NOTE section 4): gluons carry the charge they transmit, and here that is exactly "the centre element is a commutator": the
twist is absorbed by two non-commuting holonomies, which no abelian group has.
-/

import Mathlib

namespace Attempts.R3.Monotone

/-! ## The two-dimensional cross-section and the abelian obstruction -/

section TwoD

variable {L : ℕ} [NeZero L]

/-- The plaquette variable of a periodic two-dimensional lattice. -/
def plaq2 {G : Type*} [Group G] (U0 U1 : ZMod L × ZMod L → G) (x : ZMod L × ZMod L) : G :=
  U0 x * U1 (x + (1, 0)) * (U0 (x + (0, 1)))⁻¹ * (U1 x)⁻¹

/-- Abelian Stokes on the torus: the product of all plaquette variables is `1`. -/
theorem prod_plaq2_comm {G : Type*} [CommGroup G] (U0 U1 : ZMod L × ZMod L → G) :
    ∏ x, plaq2 U0 U1 x = 1 := by
  simp only [plaq2, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have h1 : ∏ x, U1 (x + (1, 0)) = ∏ x, U1 x :=
    Fintype.prod_equiv (Equiv.addRight (1, 0)) _ _ (fun _ => rfl)
  have h2 : ∏ x, U0 (x + (0, 1)) = ∏ x, U0 x :=
    Fintype.prod_equiv (Equiv.addRight (0, 1)) _ _ (fun _ => rfl)
  rw [h1, h2]
  simp [mul_assoc]

/-- **Abelian obstruction.** In an abelian group a twisted-flat cross-section (all plaquettes `1` except the corner one, which
equals `c`) forces `c = 1`. -/
theorem no_flat_twist_comm {G : Type*} [CommGroup G] (c : G) (U0 U1 : ZMod L × ZMod L → G)
    (h : ∀ x, plaq2 U0 U1 x = if x = (-1, -1) then c else 1) : c = 1 := by
  have hp := prod_plaq2_comm U0 U1
  rw [Finset.prod_congr rfl (fun x _ => h x)] at hp
  simpa [Finset.prod_ite_eq'] using hp

end TwoD

/-! ## The twist eater in `d` dimensions -/

section Eater

variable {G : Type*} [Group G] {d L : ℕ}

/-- Unit shift in direction `μ`. -/
def shift (μ : Fin d) (x : Fin d → ZMod L) : Fin d → ZMod L := x + Pi.single μ 1

theorem shift_apply_ne {μ ν : Fin d} (h : ν ≠ μ) (x : Fin d → ZMod L) : shift μ x ν = x ν := by
  simp [shift, Pi.single_eq_of_ne h]

/-- The plaquette variable in the `(μ, ν)` plane at `x`. -/
def plaq (U : Fin d → (Fin d → ZMod L) → G) (μ ν : Fin d) (x : Fin d → ZMod L) : G :=
  U μ x * U ν (shift μ x) * (U μ (shift ν x))⁻¹ * (U ν x)⁻¹

/-- The twist eater: `a` on the `p`-links of the slice `x p = −1`, `b` on the `q`-links of the slice `x q = −1`, `1` elsewhere. -/
def eater (p q : Fin d) (a b : G) (μ : Fin d) (x : Fin d → ZMod L) : G :=
  if μ = p then (if x p = -1 then a else 1) else if μ = q then (if x q = -1 then b else 1) else 1

/-- The corner of the twist sheet. -/
def corner (p q : Fin d) (x : Fin d → ZMod L) : Prop := x p = -1 ∧ x q = -1

instance (p q : Fin d) (x : Fin d → ZMod L) : Decidable (corner p q x) := by
  unfold corner; infer_instance

theorem eater_p (p q : Fin d) (a b : G) (x : Fin d → ZMod L) :
    eater p q a b p x = if x p = -1 then a else 1 := by simp [eater]

theorem eater_q {p q : Fin d} (hqp : q ≠ p) (a b : G) (x : Fin d → ZMod L) :
    eater p q a b q x = if x q = -1 then b else 1 := by simp [eater, hqp]

theorem eater_other {p q μ : Fin d} (hp : μ ≠ p) (hq : μ ≠ q) (a b : G) (x : Fin d → ZMod L) :
    eater p q a b μ x = 1 := by simp [eater, hp, hq]

/-- The plaquettes of the twist eater: trivial except the corner `(p, q)` plaquettes (one per transverse position), which carry
the commutator. -/
theorem eater_plaq (p q : Fin d) (hpq : p ≠ q) (a b : G) (μ ν : Fin d) (hμν : μ ≠ ν) (x : Fin d → ZMod L) :
    plaq (eater p q a b) μ ν x =
      if μ = p ∧ ν = q ∧ corner p q x then a * b * a⁻¹ * b⁻¹
      else if μ = q ∧ ν = p ∧ corner p q x then b * a * b⁻¹ * a⁻¹ else 1 := by
  have hqp : q ≠ p := Ne.symm hpq
  have hνμ : ν ≠ μ := Ne.symm hμν
  unfold plaq corner
  by_cases h1 : μ = p
  · subst h1
    by_cases h2 : ν = q
    · subst h2
      simp only [eater_p, eater_q hqp, shift_apply_ne hqp, shift_apply_ne hpq]
      by_cases hx : x μ = -1 <;> by_cases hy : x ν = -1 <;> simp [hx, hy, hpq]
    · simp only [eater_p, eater_other hνμ h2, shift_apply_ne hμν]
      by_cases hx : x μ = -1 <;> simp [hx, h2, hνμ]
  · by_cases h2 : μ = q
    · subst h2
      by_cases h3 : ν = p
      · subst h3
        simp only [eater_p, eater_q hqp, shift_apply_ne hpq, shift_apply_ne hqp]
        by_cases hx : x ν = -1 <;> by_cases hy : x μ = -1 <;> simp [hx, hy, hpq, hqp]
      · have h4 : ν ≠ μ := hνμ
        simp only [eater_q hqp, eater_other h3 h4, shift_apply_ne hμν]
        by_cases hy : x μ = -1 <;> simp [hy, h1, h3]
    · by_cases h3 : ν = p
      · subst h3
        simp only [eater_p, eater_other h1 h2, shift_apply_ne hνμ]
        by_cases hx : x ν = -1 <;> simp [hx, h1, h2]
      · by_cases h4 : ν = q
        · subst h4
          simp only [eater_q h3, eater_other h1 h2, shift_apply_ne hνμ]
          by_cases hy : x ν = -1 <;> simp [hy, h1, h2, h3]
        · simp [eater_other h1 h2, eater_other h3 h4, h1, h3]

/-- The twisted plaquette variable: the corner `(p, q)` plaquettes multiplied by `c⁻¹`, the reversed ones by `c`. -/
def twistedPlaq (c : G) (p q : Fin d) (U : Fin d → (Fin d → ZMod L) → G) (μ ν : Fin d) (x : Fin d → ZMod L) : G :=
  (if μ = p ∧ ν = q ∧ corner p q x then c⁻¹ else if μ = q ∧ ν = p ∧ corner p q x then c else 1) * plaq U μ ν x

/-- **Twist eater.** If `c = a b a⁻¹ b⁻¹`, the twist eater is twisted-flat: every twisted plaquette variable is `1`. -/
theorem eater_twisted_flat (c : G) (p q : Fin d) (hpq : p ≠ q) (a b : G) (hc : a * b * a⁻¹ * b⁻¹ = c)
    (μ ν : Fin d) (hμν : μ ≠ ν) (x : Fin d → ZMod L) :
    twistedPlaq c p q (eater p q a b) μ ν x = 1 := by
  unfold twistedPlaq
  rw [eater_plaq p q hpq a b μ ν hμν x]
  have hrev : b * a * b⁻¹ * a⁻¹ = c⁻¹ := by rw [← hc]; group
  by_cases h1 : μ = p ∧ ν = q ∧ corner p q x
  · simp [h1, hc]
  · by_cases h2 : μ = q ∧ ν = p ∧ corner p q x
    · obtain ⟨rfl, rfl, hx⟩ := h2
      simp [hpq, hx, hrev]
    · simp [h1, h2]

end Eater

/-! ## SU(2): `−1` is a commutator -/

section SU2

open Matrix Complex

/-- `diag(i, −i)`. -/
def suA : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ⟨!![I, 0; 0, -I], by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    · simp [Matrix.det_fin_two]⟩

/-- `((0, 1), (−1, 0))`. -/
def suB : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ⟨!![0, 1; -1, 0], by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    · simp [Matrix.det_fin_two]⟩

/-- The centre element `−1` of SU(2). -/
def suMinusOne : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ⟨-1, Matrix.mem_specialUnitaryGroup_iff.mpr ⟨by simp [Matrix.mem_unitaryGroup_iff], by simp [Matrix.det_neg]⟩⟩

/-- In SU(2), `−1 = A B A⁻¹ B⁻¹`. -/
theorem su2_commutator : suA * suB * suA⁻¹ * suB⁻¹ = suMinusOne := by
  apply Subtype.ext
  show !![I, 0; 0, -I] * !![0, 1; -1, 0] * star !![I, 0; 0, -I] * star !![(0 : ℂ), 1; -1, 0] = -1
  have hA : star !![I, 0; 0, -I] = !![-I, 0; 0, (I : ℂ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply]
  have hB : star !![(0 : ℂ), 1; -1, 0] = !![(0 : ℂ), -1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply]
  rw [hA, hB, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- **The SU(2) twisted torus has a zero-action configuration**: the twist eater with `A`, `B` makes every twisted plaquette
variable equal to the identity, in every dimension and every lattice size. -/
theorem su2_twist_eater {d L : ℕ} (p q : Fin d) (hpq : p ≠ q) (μ ν : Fin d) (hμν : μ ≠ ν) (x : Fin d → ZMod L) :
    twistedPlaq suMinusOne p q (eater p q suA suB) μ ν x = 1 :=
  eater_twisted_flat suMinusOne p q hpq suA suB su2_commutator μ ν hμν x

/-- The abelian contrast in one line: in a commutative group every commutator is trivial, so `c ≠ 1` is never one. -/
theorem commutator_trivial_of_comm {H : Type*} [CommGroup H] (a b : H) : a * b * a⁻¹ * b⁻¹ = 1 := by
  rw [mul_comm a b]; group

end SU2

end Attempts.R3.Monotone
