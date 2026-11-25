/-
Attempt (b), the positivity route (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/positivity/NOTE.md`, §5 (where the non-abelian input enters).
-/

import Mathlib

/-!
# The adjoint action sees everything except the centre

The self-charge of the gauge field (the gluon carries the charge it transmits) is the statement that the field's own
fluctuations are transported by the **adjoint** action `x ↦ g x g⁻¹` of the link variables. This file records the group
theory that makes any bound driven by adjoint transport pass the photon and the Z₂ tests by construction:

* `conj_trivial_iff_mem_center`: conjugation by `g` is the identity iff `g` is central.
* `conj_eq_conj_iff`: `g` and `h` have the same adjoint action iff `h⁻¹ g` is central (the adjoint image of a link is
  the link modulo the centre: `SU(2) → SO(3) = SU(2)/Z₂`).
* `AdjointOnly`: a functional of link variables that reads each link only through its adjoint action.
  `AdjointOnly.centre_invariant`: it cannot see centre multiplications of links (the MG3 twists / vortices).
  `AdjointOnly.const_of_comm`: for an abelian group (U(1), Z₂) it is **constant**: it carries no information at all.

So a contraction factor built from adjoint transport is identically trivial for U(1) and Z₂ (the photon and Z₂ tests
pass by construction), and for SU(2) it is blind exactly to the centre sector, which must be handled separately.
-/

namespace Attempts.Positivity

section Group

variable {G : Type*} [Group G]

/-- Conjugation by `g` is trivial iff `g` lies in the centre. -/
theorem conj_trivial_iff_mem_center (g : G) : (∀ x : G, g * x * g⁻¹ = x) ↔ g ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h x
    calc x * g = g * x * g⁻¹ * g := by rw [h x]
      _ = g * x := by group
  · intro h x
    calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [h x]
      _ = x := by group

/-- Two elements have the same adjoint action iff they differ by a central element. -/
theorem conj_eq_conj_iff (g h : G) :
    (∀ x : G, g * x * g⁻¹ = h * x * h⁻¹) ↔ h⁻¹ * g ∈ Subgroup.center G := by
  rw [← conj_trivial_iff_mem_center]
  constructor
  · intro H x
    calc h⁻¹ * g * x * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * x * g⁻¹) * h := by group
      _ = h⁻¹ * (h * x * h⁻¹) * h := by rw [H x]
      _ = x := by group
  · intro H x
    calc g * x * g⁻¹ = h * (h⁻¹ * g * x * (h⁻¹ * g)⁻¹) * h⁻¹ := by group
      _ = h * x * h⁻¹ := by rw [H x]

/-- A functional of link variables `U : ι → G` that reads each link only through its adjoint action. -/
def AdjointOnly {ι : Type*} (F : (ι → G) → ℝ) : Prop :=
  ∀ U V : ι → G, (∀ i x, U i * x * (U i)⁻¹ = V i * x * (V i)⁻¹) → F U = F V

/-- An adjoint-only functional is blind to multiplying links by central elements (centre twists). -/
theorem AdjointOnly.centre_invariant {ι : Type*} {F : (ι → G) → ℝ} (hF : AdjointOnly F) (U z : ι → G)
    (hz : ∀ i, z i ∈ Subgroup.center G) : F (fun i => U i * z i) = F U := by
  refine hF _ _ fun i x => ?_
  have hc := (conj_trivial_iff_mem_center (z i)).2 (hz i) x
  calc U i * z i * x * (U i * z i)⁻¹ = U i * (z i * x * (z i)⁻¹) * (U i)⁻¹ := by group
    _ = U i * x * (U i)⁻¹ := by rw [hc]

end Group

/-- **For an abelian gauge group an adjoint-only functional is constant**: adjoint transport carries no information
for U(1) or Z₂. -/
theorem AdjointOnly.const_of_comm {G : Type*} [CommGroup G] {ι : Type*} {F : (ι → G) → ℝ} (hF : AdjointOnly F)
    (U V : ι → G) : F U = F V :=
  hF U V fun i x => by
    rw [mul_comm (U i) x, mul_assoc, mul_inv_cancel, mul_one, mul_comm (V i) x, mul_assoc, mul_inv_cancel, mul_one]

end Attempts.Positivity
