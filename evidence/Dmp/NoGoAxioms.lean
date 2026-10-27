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

/-! ## 2. The owner's reading: "interacts with existence" means "warps it"

The owner's rebuttal (2026-10-27): "Gravity is simply what we call the warping of the existence dimension. [...] plug in the layers of
information that are possible (the universal forces) within our current existence, the warping of the resulting existence space is what we
call gravity. Beings one layer up the information decay chain might have called it Bruce." So the first axiom is read strongly: information
warps the existence it occupies, a coupling greater than zero. The gravity-free world of section 1 is then excluded, by stipulation
(`strong_axioms_exclude_no_gravity`). What stays free is everything that makes gravity gravity rather than Bruce: the law of the warping,
scalar (Nordstroem 1913, which bends no light) or tensor (Einstein 1915, 1.75 arcseconds at the Sun), and its constant
(`strong_axioms_admit_scalar_and_tensor`, `strong_axioms_do_not_fix_the_constant`). With a metric, second-order dynamics and local
conservation added, Lovelock (1971) makes the law Einstein's with G and Λ free; nothing in the axioms adds them. -/

/-- The two shapes a warping of existence by information can take. -/
inductive Warping where
  | scalar
  | tensor
  deriving DecidableEq

/-- A world under the strong reading: the axioms, and the law of the warping. -/
structure WarpedWorld where
  axioms : World
  law : Warping

/-- The strong reading: the axioms, and information warps existence (the coupling is not zero). -/
def satisfiesStrongAxioms (w : WarpedWorld) : Prop := satisfiesAxioms w.axioms ∧ 0 < w.axioms.G

/-- Under the strong reading the gravity-free world is excluded, by the stipulation itself. -/
theorem strong_axioms_exclude_no_gravity (w : WarpedWorld) (h : satisfiesStrongAxioms w) : w.axioms.G ≠ 0 := by
  have := h.2
  omega

/-- The strong reading admits a scalar warping and a tensor warping alike: the law is not fixed, and the sky had to choose. -/
theorem strong_axioms_admit_scalar_and_tensor :
    (∃ w, satisfiesStrongAxioms w ∧ w.law = .scalar) ∧ (∃ w, satisfiesStrongAxioms w ∧ w.law = .tensor) :=
  ⟨⟨⟨⟨3, true, true, true, 1⟩, .scalar⟩, ⟨⟨rfl, rfl, rfl, rfl⟩, Nat.zero_lt_one⟩, rfl⟩,
   ⟨⟨⟨3, true, true, true, 1⟩, .tensor⟩, ⟨⟨rfl, rfl, rfl, rfl⟩, Nat.zero_lt_one⟩, rfl⟩⟩

/-- Even with the law fixed, the constant is not: two worlds with the same warping and different couplings satisfy the strong reading. -/
theorem strong_axioms_do_not_fix_the_constant :
    ∃ w w' : WarpedWorld, satisfiesStrongAxioms w ∧ satisfiesStrongAxioms w' ∧ w.law = w'.law ∧ w.axioms.G ≠ w'.axioms.G :=
  ⟨⟨⟨3, true, true, true, 1⟩, .tensor⟩, ⟨⟨3, true, true, true, 2⟩, .tensor⟩,
   ⟨⟨rfl, rfl, rfl, rfl⟩, Nat.zero_lt_one⟩, ⟨⟨rfl, rfl, rfl, rfl⟩, by decide⟩, rfl, by decide⟩

end Dmp
