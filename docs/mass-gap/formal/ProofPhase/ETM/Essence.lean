/-
The essence chain 2 + 2 = 5 = 4 = 0 = 1, its exact core (2026-11-24).
Released under Apache 2.0.

Paper: `docs/paper/draft/01-part-I-dmp.md`, I.7 (the first author's reading, with this proved core).
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

end ProofPhase.ETM
