/-
C3 (a value reaches only parts trusted for its class), the missing theorem of its Coverage line, stated and proven in the smallest model
that has a class: a value carries its class wherever it goes; at every border a part trusted for the class receives the value and any
other part receives its count; so every holder along any path is trusted for the class, and widening the class (revealing to a further
class) is a loosening that needs both witnesses (T16, `Standing.update`). Prior art: Denning's lattice (1976), in which a flow is allowed
only where every class on the path allows it; here the lattice is the trust relation itself (which parts the admission names for the class).
-/
import Dmp.Standing

namespace Dmp

abbrev Class := Nat
abbrev Part := Nat

/-- A value carries its class wherever it goes (C3: the class and the provenance its admission named). -/
structure Value where
  content : Nat
  cls : Class
  deriving DecidableEq, Repr

/-- What a part receives at a border: the value, or only its count (its existence, Axiom 3). -/
inductive Received where
  | value (v : Value)
  | count (cls : Class)
  deriving DecidableEq, Repr

/-- The shield at a border: a part trusted for the class receives the value; any other part receives the count. `trustedFor` is what the
    admissions say (the words: parts trusted for that class may act on it). -/
def deliver (trustedFor : Part → Class → Bool) (p : Part) (v : Value) : Received :=
  if trustedFor p v.cls then .value v else .count v.cls

/-- A value reaches only a part trusted for its class, and reaches it unchanged (the class travels with it). -/
theorem value_reaches_only_trusted (tf : Part → Class → Bool) (p : Part) (v v' : Value) (h : deliver tf p v = .value v') :
    tf p v.cls = true ∧ v' = v := by
  unfold deliver at h
  split at h
  · rename_i ht; simp only [Received.value.injEq] at h; exact ⟨ht, h.symm⟩
  · cases h

/-- A part not trusted for the class receives the count and never the value. -/
theorem untrusted_gets_count (tf : Part → Class → Bool) (p : Part) (v : Value) (h : tf p v.cls = false) : deliver tf p v = .count v.cls := by
  simp [deliver, h]

/-- A path forwards the value hop by hop: it carries the value only when every part on it received the value. -/
def pathCarries (tf : Part → Class → Bool) (path : List Part) (v : Value) : Bool :=
  path.all fun p => decide (deliver tf p v = .value v)

/-- No path delivers a value to a part outside its class: every holder along a path that carries the value is trusted for its class. -/
theorem no_delivery_outside_class (tf : Part → Class → Bool) (path : List Part) (v : Value) (h : pathCarries tf path v = true) :
    ∀ p ∈ path, tf p v.cls = true := by
  intro p hp
  have := (List.all_eq_true.mp h) p hp
  simp only [decide_eq_true_eq] at this
  exact (value_reaches_only_trusted tf p v v this).1

/-- The width of a class: how many parts its admission names. Widening (revealing to a further class) is a loosening: it needs both
    witnesses (T16); narrowing is a tightening one witness may make. -/
theorem class_never_widened_by_one (old new : Nat) (w : Bool) : update old new w false ≤ old ∧ update old new false w ≤ old :=
  one_witness_never_loosens old new w

theorem widening_needs_both (old new : Nat) (w1 w2 : Bool) (h : old < update old new w1 w2) : w1 = true ∧ w2 = true :=
  loosening_needs_both old new w1 w2 h

end Dmp
