/-
The owner's quantum (2026-10-27): "It is a quantum gravity if the field that projects the inflation is the information in the other
constituent of each quantum. Those are the universal forces. Their interaction with the existence field is what actually drives evolution,
which also explains quantum effects. If you force a singularity to give up one of its constituent parts, either its existence in the space,
or information about it, the DoE dissolves, ending the wave particle duality. [...] Backwards in the scalar direction past decay chains can
be seen by their imprint, since only one possible configuration can evolve into the current system."

Two of these sentences cannot both hold, and the kernel says so in the smallest model (docs/qg-attempt.md section 4.11). A quantum is its
existence half and its information half. Forcing it to give up one half is a map onto the other, and such a map is many-to-one: from what
remains after a dissolution, the quantum before it is not unique (`dissolution_forgets`). "Only one possible configuration can evolve into
the current system" is the uniqueness of the past from the present, which is the injectivity of the evolution; a dissolution is the loss of
that injectivity (`unique_past_forbids_dissolution`). So the owner has to choose: an evolution that never forgets, under which nothing
dissolves and the duality never ends, or one that dissolves, under which the backward chain branches at every dissolution. Physics made the
same choice explicit in 1932: von Neumann's process 2 (unitary, reversible) and process 1 (measurement, irreversible) are two different
things, and a theory needs to say which one it means.
-/
namespace Dmp

/-- The owner's quantum: a duality of its existence (where it is) and the information about it (the owner's force half). -/
structure Quantum where
  existence : Nat
  information : Nat
  deriving DecidableEq

/-- Forcing a quantum to give up its information: what remains is its existence. -/
def giveUpInformation (q : Quantum) : Nat := q.existence

/-- Forcing a quantum to give up its existence: what remains is its information. -/
def giveUpExistence (q : Quantum) : Nat := q.information

/-- A dissolution forgets: two different quanta leave the same remainder, whichever half is given up. From the remainder, the quantum
    before the dissolution is not unique. -/
theorem dissolution_forgets :
    (∃ q q' : Quantum, q ≠ q' ∧ giveUpInformation q = giveUpInformation q') ∧
    (∃ q q' : Quantum, q ≠ q' ∧ giveUpExistence q = giveUpExistence q') :=
  ⟨⟨⟨0, 0⟩, ⟨0, 1⟩, by decide, rfl⟩, ⟨⟨0, 0⟩, ⟨1, 0⟩, by decide, rfl⟩⟩

/-- A unique past is an evolution that never forgets: if from every state the state before is unique, no step of it is the giving up of
    either half. "Only one configuration can evolve into the current system" and "the duality dissolves" exclude each other. -/
theorem unique_past_forbids_dissolution (step : Quantum → Quantum) (hunique : ∀ q q', step q = step q' → q = q') :
    ¬ (∀ q, step q = ⟨giveUpInformation q, 0⟩) ∧ ¬ (∀ q, step q = ⟨0, giveUpExistence q⟩) := by
  constructor
  · intro h
    have := hunique ⟨0, 0⟩ ⟨0, 1⟩ (by simp [h, giveUpInformation])
    exact absurd this (by decide)
  · intro h
    have := hunique ⟨0, 0⟩ ⟨1, 0⟩ (by simp [h, giveUpExistence])
    exact absurd this (by decide)

end Dmp
