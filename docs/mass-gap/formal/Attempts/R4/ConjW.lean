/-
Round 4, attempt 3 (r4-conjw, 2026-11-21). Released under Apache 2.0.

# Conjecture W: the bookkeeping, as toys

Note: `docs/mass-gap/weak-coupling/attempts/r4-conjw/NOTE.md`. **These are toys**: real arithmetic about a positive function
`E (Lx, Ly, Lz)` (the energy of one unit of centre flux along z in a box with sides Lx, Ly, Lz, time extent already infinite). No
theorem here contains Yang–Mills; each states what a Yang–Mills input would have to supply, or a consequence of one.

1. `four_move_identity`: one doubling of the cube is the product of four one-direction moves (lengthen z, widen x, widen y; time does
   not change an energy): `z(2L)/z(L) = 2 · ℓ · w_x · w_y` with `z(L) = L · E(L, L, L)`.
2. `conjW_doubling`: Conjecture W in its per-move form (`ℓ ≥ 2`, `w_x, w_y ≥ (1 + δ)/2`) gives `z(2L) ≥ (1 + δ)² z(L)`.
3. `coulomb_moves`, `coulomb_frozen_box`: the free photon's box energy `E = c · Lz/(Lx Ly)` (proved exactly in the note, lattice and
   continuum) has `ℓ = 2`, `w = 1/2`, and a frozen act number: the marginal case, no margin.
4. `scale_invariant_frozen`: any box energy homogeneous of degree −1 (classical scale invariance, no running) has a frozen act number.
   Growth of z needs the scale anomaly (b₀).
5. `sandwich_certifies`, `power_sandwich_certifies`: two-sided bounds certify one doubling exactly when the lower bound at 2L beats the
   upper bound at L; for power-law bounds `C₁ L^p ≤ z ≤ C₂ L^p` this is `C₂/C₁ < 2^p`.
6. `relief_exponential`: if widening forces an exponentially larger minimal action (finite gauge groups, Z₂: `2μA` against `μA + b`),
   the widening ratio drops below light's 1/2 for all large β (the finite-group failure of W, in its abstract form).
7. `self_dual_point`, `self_dual_unique`: the fixed point of 't Hooft's duality `F ↦ −log tanh(F/2)` is `log(1 + √2)`, and it is the
   only positive one (the "inversion box" of the note, §6).
-/

import Mathlib
import Attempts.R3.MonotoneCrossing

namespace Attempts.R4.ConjW

open Real

/-- **Four one-direction moves.** `z(2L) = 2 · ℓ · w_x · w_y · z(L)` with `ℓ = E(L,L,2L)/E(L,L,L)`,
`w_x = E(2L,L,2L)/E(L,L,2L)`, `w_y = E(2L,2L,2L)/E(2L,L,2L)`. -/
theorem four_move_identity (E : ℝ → ℝ → ℝ → ℝ) (L : ℝ) (h0 : E L L L ≠ 0) (h1 : E L L (2 * L) ≠ 0)
    (h2 : E (2 * L) L (2 * L) ≠ 0) :
    (2 * L) * E (2 * L) (2 * L) (2 * L) =
      2 * (E L L (2 * L) / E L L L) * (E (2 * L) L (2 * L) / E L L (2 * L)) *
        (E (2 * L) (2 * L) (2 * L) / E (2 * L) L (2 * L)) * (L * E L L L) := by
  field_simp

/-- **Conjecture W, per move, gives growth of the act number.** -/
theorem conjW_doubling (E : ℝ → ℝ → ℝ → ℝ) {L δ : ℝ} (hL : 0 < L) (hδ : 0 ≤ δ)
    (hlen : 2 * E L L L ≤ E L L (2 * L))
    (hwx : (1 + δ) / 2 * E L L (2 * L) ≤ E (2 * L) L (2 * L))
    (hwy : (1 + δ) / 2 * E (2 * L) L (2 * L) ≤ E (2 * L) (2 * L) (2 * L)) :
    (1 + δ) ^ 2 * (L * E L L L) ≤ (2 * L) * E (2 * L) (2 * L) (2 * L) := by
  have hc : 0 ≤ (1 + δ) / 2 := by linarith
  have h1 : (1 + δ) / 2 * (2 * E L L L) ≤ (1 + δ) / 2 * E L L (2 * L) := mul_le_mul_of_nonneg_left hlen hc
  have h2 : (1 + δ) / 2 * ((1 + δ) / 2 * (2 * E L L L)) ≤ (1 + δ) / 2 * E (2 * L) L (2 * L) :=
    mul_le_mul_of_nonneg_left (le_trans h1 hwx) hc
  have h3 : (1 + δ) / 2 * ((1 + δ) / 2 * (2 * E L L L)) ≤ E (2 * L) (2 * L) (2 * L) := le_trans h2 hwy
  have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 2 * L)
  calc (1 + δ) ^ 2 * (L * E L L L) = (2 * L) * ((1 + δ) / 2 * ((1 + δ) / 2 * (2 * E L L L))) := by ring
    _ ≤ (2 * L) * E (2 * L) (2 * L) (2 * L) := h4

/-- The free photon's box energy `c · Lz/(Lx Ly)`: lengthening doubles it, widening halves it. -/
theorem coulomb_moves (c L : ℝ) (hL : L ≠ 0) :
    c * (2 * L) / (L * L) = 2 * (c * L / (L * L)) ∧
      c * (2 * L) / ((2 * L) * L) = (1 / 2) * (c * (2 * L) / (L * L)) ∧
      c * (2 * L) / ((2 * L) * (2 * L)) = (1 / 2) * (c * (2 * L) / ((2 * L) * L)) := by
  refine ⟨?_, ?_, ?_⟩ <;> field_simp

/-- The free photon's act number is frozen under doubling (no margin: the marginal case of Conjecture W). -/
theorem coulomb_frozen_box (c L : ℝ) (hL : L ≠ 0) :
    (2 * L) * (c * (2 * L) / ((2 * L) * (2 * L))) = L * (c * L / (L * L)) := by
  field_simp

/-- **Classical scale invariance freezes the act number.** If the box energy is homogeneous of degree −1 (no running coupling),
`z(2L) = z(L)` for every L. Growth needs the scale anomaly. -/
theorem scale_invariant_frozen (E : ℝ → ℝ → ℝ → ℝ) (hE : ∀ a b c, E (2 * a) (2 * b) (2 * c) = E a b c / 2) (L : ℝ) :
    (2 * L) * E (2 * L) (2 * L) (2 * L) = L * E L L L := by
  rw [hE]; ring

/-- **A sandwich certifies one doubling** when the lower bound at `2L` beats the upper bound at `L`. -/
theorem sandwich_certifies {zlo z zup : ℝ → ℝ} {L : ℝ} (hlo : zlo (2 * L) ≤ z (2 * L)) (hup : z L ≤ zup L)
    (hcert : zup L < zlo (2 * L)) : z L < z (2 * L) :=
  lt_of_le_of_lt hup (lt_of_lt_of_le hcert hlo)

/-- **Power-law sandwich.** `C₁ L^p ≤ z(L) ≤ C₂ L^p` at `L` and `2L` with `C₂ < 2^p C₁` certifies `z(L) < z(2L)`. The ratio of the
two constants must be below the doubling factor `2^p` (for SU(2) at small L, `p ≈ 11/3`, `2^p ≈ 12.7`). -/
theorem power_sandwich_certifies {z : ℝ → ℝ} {C₁ C₂ p L : ℝ} (hL : 0 < L)
    (hlo : C₁ * (2 * L) ^ p ≤ z (2 * L)) (hup : z L ≤ C₂ * L ^ p) (hC : C₂ < 2 ^ p * C₁) :
    z L < z (2 * L) := by
  have hLp : 0 < L ^ p := Real.rpow_pos_of_pos hL p
  have h2 : (2 * L) ^ p = 2 ^ p * L ^ p := Real.mul_rpow (by norm_num) hL.le
  calc z L ≤ C₂ * L ^ p := hup
    _ < 2 ^ p * C₁ * L ^ p := mul_lt_mul_of_pos_right hC hLp
    _ = C₁ * (2 * L) ^ p := by rw [h2]; ring
    _ ≤ z (2 * L) := hlo

/-- **Exponential relief (finite groups, Z₂).** If the wide box's flux energy is at most `A e^{−2βμa}` and the narrow box's at least
`B e^{−β(μa + b)}` with `b < μa`, then for all large β the widening ratio is below light's `1/2`. -/
theorem relief_exponential {E1 E2 : ℝ → ℝ} {A B μa b : ℝ} (hA : 0 < A) (hB : 0 < B) (hgap : b < μa)
    (hup : ∀ β, E2 β ≤ A * exp (-(β * (2 * μa)))) (hlo : ∀ β, B * exp (-(β * (μa + b))) ≤ E1 β) :
    ∃ β₀, ∀ β, β₀ ≤ β → E2 β < (1 / 2) * E1 β := by
  have hd : 0 < μa - b := by linarith
  refine ⟨Real.log (2 * A / B) / (μa - b) + 1, fun β hβ => ?_⟩
  have hβ' : Real.log (2 * A / B) < β * (μa - b) := by
    have : Real.log (2 * A / B) / (μa - b) < β := by linarith
    rwa [div_lt_iff₀ hd] at this
  have hexp : exp (-(β * (μa - b))) < B / (2 * A) := by
    have h2A : 0 < 2 * A / B := by positivity
    have : -(β * (μa - b)) < Real.log (B / (2 * A)) := by
      rw [show B / (2 * A) = (2 * A / B)⁻¹ by field_simp, Real.log_inv]; linarith
    calc exp (-(β * (μa - b))) < exp (Real.log (B / (2 * A))) := exp_lt_exp.mpr this
      _ = B / (2 * A) := exp_log (by positivity)
  have hsplit : exp (-(β * (2 * μa))) = exp (-(β * (μa - b))) * exp (-(β * (μa + b))) := by
    rw [← exp_add]; ring_nf
  have hpos : 0 < exp (-(β * (μa + b))) := exp_pos _
  calc E2 β ≤ A * exp (-(β * (2 * μa))) := hup β
    _ = A * exp (-(β * (μa - b))) * exp (-(β * (μa + b))) := by rw [hsplit]; ring
    _ < A * (B / (2 * A)) * exp (-(β * (μa + b))) := by
        apply mul_lt_mul_of_pos_right _ hpos; exact mul_lt_mul_of_pos_left hexp hA
    _ = (1 / 2) * (B * exp (-(β * (μa + b)))) := by field_simp
    _ ≤ (1 / 2) * E1 β := by linarith [hlo β]

/-- **The self-dual point of 't Hooft's duality** `F ↦ −log tanh(F/2)` (round 3's `dual`) is `log(1 + √2) ≈ 0.8814`. -/
theorem self_dual_point : Attempts.R3.Monotone.dual (Real.log (1 + √2)) = Real.log (1 + √2) := by
  have hs : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg 2
  have hpos : (0 : ℝ) < 1 + √2 := by linarith
  have hsq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold Attempts.R3.Monotone.dual
  rw [Real.exp_neg, Real.exp_log hpos]
  have hr : (1 - (1 + √2)⁻¹) / (1 + (1 + √2)⁻¹) = (1 + √2)⁻¹ := by
    have h2 : (2 + √2) ≠ 0 := by linarith
    field_simp
    nlinarith [hsq]
  rw [hr, Real.log_inv, neg_neg]

/-- It is the only positive fixed point (the duality is strictly decreasing). -/
theorem self_dual_unique {x : ℝ} (hx : 0 < x) (hfix : Attempts.R3.Monotone.dual x = x) : x = Real.log (1 + √2) := by
  have hs : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg 2
  have hstar : 0 < Real.log (1 + √2) := Real.log_pos (by
    have : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
    linarith)
  rcases lt_trichotomy x (Real.log (1 + √2)) with h | h | h
  · have := Attempts.R3.Monotone.dual_strictAntiOn (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hstar) h
    rw [hfix, self_dual_point] at this; linarith
  · exact h
  · have := Attempts.R3.Monotone.dual_strictAntiOn (Set.mem_Ioi.mpr hstar) (Set.mem_Ioi.mpr hx) h
    rw [hfix, self_dual_point] at this; linarith

end Attempts.R4.ConjW
