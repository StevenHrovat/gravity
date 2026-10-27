/-
Break model for C3 (part 2 of the verifying session). The axioms as modelled in Gate.lean and Record.lean (K1 the dual gate, K2 live
evidence, K3 the record) hold, and C3's sentence fails: a value is delivered to a part that is not trusted for its class, with both
witnesses passing on live evidence and the act performed and recorded, because the gate's signature has no class and no part in it. This
is why C3's Coverage line says undershoot: the modelled axioms cannot refuse what they cannot see. Flow.lean states and proves the theorem
C3 needs in a model that has the class.
-/
import Dmp.Record
import Dmp.Flow

namespace Dmp

/-- Live evidence at step 7: read at 7, inside its window. -/
def liveAt7 : Evidence := ⟨7, 0, 100, true⟩

theorem liveAt7_ok : liveAt7.ok 7 = true := by decide

/-- Two witnesses that pass whatever is in front of them (the content is not an argument of their judgment). -/
def passAll : Evidence → Verdict := fun _ => .pass

/-- A part no admission names for the class, and a value of that class. -/
def nobodyTrusted : Part → Class → Bool := fun _ _ => false
def secret : Value := ⟨42, 3⟩

/-- The act "deliver `secret` to part 5" passes the modelled gate and is performed and recorded, while part 5 is not trusted for the value's
    class: the modelled axioms allow it. -/
theorem c3_breaks_in_the_modelled_axioms :
    (step passAll passAll ⟨[], 0⟩ ⟨7, liveAt7, liveAt7⟩).performed = 1 ∧ nobodyTrusted 5 secret.cls = false := by
  constructor
  · decide
  · rfl

/-- And Flow.lean's shield refuses the same delivery: part 5 receives the count, never the value. -/
theorem c3_holds_with_the_class : deliver nobodyTrusted 5 secret = .count 3 := by decide

end Dmp
