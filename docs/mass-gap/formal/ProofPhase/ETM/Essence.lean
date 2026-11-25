/-
The essence chain 2 + 2 = 5 = 4 = 0 = 1, its exact core (2026-11-24).
Released under Apache 2.0.

Paper: `docs/paper/draft/13-appendix-r-readings.md`, R.5 (the first author's reading, with this proved core); Draft 5 adds the hash,
`docs/paper/D5/draft/13-appendix-r-readings.md`, R.6a.
-/

import Mathlib

/-!
# The essence chain

The first author's essence line reads `2 + 2 = 5 = 4 = 0 = 1`. Its exact core:

* `two_add_two_ne_five`: over the natural numbers `2 + 2 = 5` is refuted by one kernel evaluation (`decide`): a certified
  "it does not exist", with no assumption behind it.
* `essence_zmod_one`: in `ZMod 1`, the ring with one element, the whole chain holds, again by one `decide`.
* `subsingleton_of_essence`: in any ring the chain forces a single element; already its last link `0 = 1` does
  (Mathlib's `subsingleton_iff_zero_eq_one`).
* `essence_of_subsingleton`: conversely, in a ring with one element the chain holds.

So the chain names exactly one ring up to isomorphism, the zero ring, where existence and non-existence coincide. That
reading is the paper's; the four theorems are all that is claimed here. No axioms beyond the standard ones.
-/

namespace ProofPhase.ETM

/-- The essence chain in a ring `R`. -/
def EssenceChain (R : Type*) [Ring R] : Prop :=
  (2 + 2 : R) = 5 ∧ (5 : R) = 4 ∧ (4 : R) = 0 ∧ (0 : R) = 1

/-- Over the natural numbers, `2 + 2 = 5` is refuted by one kernel evaluation. -/
theorem two_add_two_ne_five : (2 + 2 : ℕ) ≠ 5 := by decide

/-- In `ZMod 1` the whole chain holds, checked by one `decide`. -/
theorem essence_zmod_one : EssenceChain (ZMod 1) := by
  unfold EssenceChain
  decide

/-- In any ring the chain forces a single element (its last link `0 = 1` already does). -/
theorem subsingleton_of_essence {R : Type*} [Ring R] (h : EssenceChain R) : Subsingleton R :=
  subsingleton_iff_zero_eq_one.mp h.2.2.2

/-- In a ring with one element the chain holds. -/
theorem essence_of_subsingleton {R : Type*} [Ring R] [Subsingleton R] : EssenceChain R :=
  ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- The chain holds in a ring exactly when the ring has one element. -/
theorem essence_iff_subsingleton {R : Type*} [Ring R] : EssenceChain R ↔ Subsingleton R :=
  ⟨subsingleton_of_essence, fun _ => essence_of_subsingleton⟩

/-! ## Only `= 1.5` is assumed: every other link is decided

The first author's sharper form is `2 + 2 ? 5 ? 4 ? 0 ? 1 ? SU(5) = 1.5`: one equation is assumed, `1.5`, and every `?` is to be
decided from its definition. `1.5 = 3/2` exists in a commutative ring exactly when `2` is a unit. Then each of the four ring links
is equivalent to `0 = 1`, so one bit decides them all, the same way (`essence_decided`). Without `1.5` the link `4 ? 0` splits
off: in `ZMod 2` it holds while `0 = 1` does not (`four_eq_zero_without_half`). -/

/-- `1.5 = 3/2` in the rationals. -/
theorem one_point_five : (1.5 : ℚ) = 3 / 2 := by norm_num

/-- **Once `1.5` is defined (`2` a unit), every link of the chain is decided by the one bit `0 = 1`.** -/
theorem essence_decided {R : Type*} [CommRing R] (h2 : IsUnit (2 : R)) :
    ((2 + 2 : R) = 5 ↔ (0 : R) = 1) ∧ ((5 : R) = 4 ↔ (0 : R) = 1) ∧ ((4 : R) = 0 ↔ (0 : R) = 1) := by
  refine ⟨⟨fun h => by linear_combination h, fun h => by linear_combination h⟩,
    ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩, ⟨fun h => ?_, fun h => by linear_combination (-4 : R) * h⟩⟩
  obtain ⟨u, hu⟩ := h2
  have h22 : (u : R) * u = 0 := by rw [hu]; linear_combination h
  have h1 : (1 : R) = 0 := by
    have := congrArg (fun x => (↑u⁻¹ : R) * ((↑u⁻¹ : R) * x)) h22
    simpa [← mul_assoc] using this
  exact h1.symm

/-- **The same, with the ring's size:** once `1.5` is defined, the chain holds exactly in the one-element ring, and in every
other such ring each link fails. -/
theorem essence_decided_subsingleton {R : Type*} [CommRing R] (h2 : IsUnit (2 : R)) :
    ((2 + 2 : R) = 5 ↔ Subsingleton R) ∧ ((5 : R) = 4 ↔ Subsingleton R) ∧ ((4 : R) = 0 ↔ Subsingleton R) ∧
      ((0 : R) = 1 ↔ Subsingleton R) := by
  have h := essence_decided h2
  have hs : (0 : R) = 1 ↔ Subsingleton R := subsingleton_iff_zero_eq_one
  exact ⟨h.1.trans hs, h.2.1.trans hs, h.2.2.trans hs, hs⟩

/-- **Without `1.5` the link `4 ? 0` is not decided by `0 = 1`:** in `ZMod 2` (where `2` is not a unit) `4 = 0` holds and
`0 = 1` fails. -/
theorem four_eq_zero_without_half : (4 : ZMod 2) = 0 ∧ (0 : ZMod 2) ≠ 1 ∧ ¬ IsUnit (2 : ZMod 2) := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have : (2 : ZMod 2) = 0 := by decide
  rw [this] at h
  exact not_isUnit_zero h

/-! ## A hash certifies origin, not identity (draft 5, R.6) -/

/-- **Every hash has collisions**: a map from an infinite type (all messages) to a finite one (all digests) is never injective.
So a digest cannot certify which message it came from, only that a message consistent with the claimed origin exists. -/
theorem hash_collision {α β : Type*} [Infinite α] [Finite β] (h : α → β) : ∃ a b, a ≠ b ∧ h a = h b :=
  Finite.exists_ne_map_eq_of_infinite h

/-- **The sha256 shape**: any map from bit strings to 256-bit digests has a collision. -/
theorem digest_collision (h : List Bool → Fin (2 ^ 256)) : ∃ a b, a ≠ b ∧ h a = h b :=
  hash_collision h

end ProofPhase.ETM
