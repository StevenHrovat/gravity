/-
Axiom 3's existence clause, applied to the record (gravity#23 second pass, docs/qg-verdict.md section 10).

DMP, Axiom 3: "From trust nothing can be derived about information but its existence: a standing, a refusal or a count says that
information is there, never what it says."

Read on the gate of Record.lean: what each witness reads is a function of the content's existence and the time, never of the content.
Then the whole record and the count of performed acts are the same for any two contents that agree on existence. In the quantum reading
(docs/qg-verdict/assembly.py, check [7]) that is the step that keeps the record from saying which branch the content is in, so content
(and gravity's quantum part carried as content) can stay coherent while every act is recorded. The converse shows the clause is the
whole reason: a witness allowed to read one content observable writes that observable into the record.
-/
import Dmp.Record

namespace Dmp

/-- One act in front of the gate: its time and the content it concerns. -/
structure ContentAct (C : Type) where
  t : Nat
  c : C

/-- The request the gate sees, when each witness's evidence depends on existence and time only (Axiom 3's clause). -/
def blindRequest {C : Type} (ex : C → Bool) (ev1 ev2 : Bool → Nat → Evidence) (a : ContentAct C) : Request :=
  ⟨a.t, ev1 (ex a.c) a.t, ev2 (ex a.c) a.t⟩

/-- Two act lists agree on existence: same times, and each act's content exists in both or in neither. -/
def SameExistence {C : Type} (ex : C → Bool) : List (ContentAct C) → List (ContentAct C) → Prop
  | [], [] => True
  | a :: as, b :: bs => a.t = b.t ∧ ex a.c = ex b.c ∧ SameExistence ex as bs
  | _, _ => False

/-- Axiom 3 on the record: two runs whose contents agree on existence leave the same record and the same count of performed acts,
    whatever the contents are. -/
theorem blind_record_same {C : Type} (ex : C → Bool) (ev1 ev2 : Bool → Nat → Evidence) (j1 j2 : Evidence → Verdict) :
    ∀ (as bs : List (ContentAct C)) (s : State), SameExistence ex as bs →
      run j1 j2 s (as.map (blindRequest ex ev1 ev2)) = run j1 j2 s (bs.map (blindRequest ex ev1 ev2)) := by
  intro as
  induction as with
  | nil =>
    intro bs s h
    cases bs with
    | nil => rfl
    | cons b bs => exact absurd h (by simp [SameExistence])
  | cons a as ih =>
    intro bs s h
    cases bs with
    | nil => exact absurd h (by simp [SameExistence])
    | cons b bs =>
      simp only [SameExistence] at h
      obtain ⟨ht, hex, hrest⟩ := h
      have hr : blindRequest ex ev1 ev2 a = blindRequest ex ev1 ev2 b := by
        simp [blindRequest, ht, hex]
      simp only [List.map, run, hr]
      exact ih bs _ hrest

/-- The record says which content it was only through existence: for one act, the record entry is the same for every two contents
    that both exist. -/
theorem blind_entry_same {C : Type} (ex : C → Bool) (ev1 ev2 : Bool → Nat → Evidence) (j1 j2 : Evidence → Verdict)
    (s : State) (t : Nat) (c1 c2 : C) (h1 : ex c1 = true) (h2 : ex c2 = true) :
    (step j1 j2 s (blindRequest ex ev1 ev2 ⟨t, c1⟩)).log = (step j1 j2 s (blindRequest ex ev1 ev2 ⟨t, c2⟩)).log := by
  simp [blindRequest, h1, h2]

/-- The converse: drop the clause and let a witness's evidence depend on one content observable `f`. Then there are judges for which
    the record entry differs exactly when `f` differs, so the record carries `f` (in the quantum reading, which branch). -/
theorem sighted_record_carries {C : Type} (f : C → Bool) (c1 c2 : C) (hf : f c1 ≠ f c2) (t : Nat) :
    let ev : Bool → Evidence := fun b => ⟨t, 0, t + 1, b⟩
    let r1 : Request := ⟨t, ev (f c1), ev true⟩
    let r2 : Request := ⟨t, ev (f c2), ev true⟩
    (step (fun _ => .pass) (fun _ => .pass) ⟨[], 0⟩ r1).log ≠ (step (fun _ => .pass) (fun _ => .pass) ⟨[], 0⟩ r2).log := by
  intro ev r1 r2
  cases h1 : f c1 <;> cases h2 : f c2 <;> simp_all [step, guard, Evidence.ok, ev, r1, r2]

end Dmp
