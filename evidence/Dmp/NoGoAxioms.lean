/-
The owner's axioms, as stated (2026-10-27). In general: "1. Information that interacts with existence must exist in an existence field
consisting of space vectors and a time vector, that is able to propagate a field through itself. 2. For information to be real it has to
exist, for anything to exist, there has to be information about it." Applied to quantum gravity: "1. Existence is made of three spatial
vectors and one time vector that moves forward in space. 2. [the first general axiom] 3. [the second general axiom]."

The decisive test of an axiom system that claims to be a theory of gravity is whether a world without gravity satisfies it. This one does:
flat spacetime with electrons and photons and nothing else (quantum electrodynamics with the gravitational coupling zero) has three space
directions and a forward time, fields that propagate through it, information that interacts with existence and exists in the field, and
nothing that exists without information about it. Every axiom holds and there is no gravity. An axiom system that a gravity-free world
satisfies cannot entail gravity, let alone quantum gravity: to be a theory of gravity it would have to be false of that world. The kernel
records the independence in the smallest form: a world is its three axioms and the one number they would have to fix, the axioms hold
with that number zero and with it nonzero, so they fix nothing about it (docs/qg-attempt.md section 4.12).
-/
namespace Dmp

/-- A world as the owner's axioms see it, with the one number they would have to fix to be a theory of gravity: the gravitational coupling,
    in thousandths, zero being no gravity. -/
structure World where
  spaceVectors : Nat
  timeForward : Bool
  fieldPropagates : Bool
  coupled : Bool
  G : Nat

/-- The owner's three axioms as predicates on a world: three spatial vectors, a forward time vector, a field propagated through the
    existence field, and information coupled to the existence it occupies (the second axiom in both directions). -/
def satisfiesAxioms (w : World) : Prop :=
  w.spaceVectors = 3 ∧ w.timeForward = true ∧ w.fieldPropagates = true ∧ w.coupled = true

/-- Flat spacetime with electrons and photons and no gravity satisfies every axiom. -/
theorem axioms_hold_without_gravity : ∃ w : World, satisfiesAxioms w ∧ w.G = 0 :=
  ⟨⟨3, true, true, true, 0⟩, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩

/-- So does a world with gravity. -/
theorem axioms_hold_with_gravity : ∃ w : World, satisfiesAxioms w ∧ 0 < w.G :=
  ⟨⟨3, true, true, true, 1⟩, ⟨rfl, rfl, rfl, rfl⟩, Nat.zero_lt_one⟩

/-- The axioms fix nothing about gravity: two worlds satisfy them with different couplings, so no value of the coupling and no law for it
    follows from them. -/
theorem axioms_do_not_fix_gravity : ¬ (∀ w w' : World, satisfiesAxioms w → satisfiesAxioms w' → w.G = w'.G) := by
  intro h
  have := h ⟨3, true, true, true, 0⟩ ⟨3, true, true, true, 1⟩ ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩
  exact Nat.zero_ne_one this

end Dmp
