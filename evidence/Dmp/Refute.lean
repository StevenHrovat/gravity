/-
Team Fable, the adversary (docs/refutation.md): counter-models against claims made for DMP 0.9.8 and for the Lean of this chain.
Nothing here changes a theorem that exists; each theorem below is the smallest model in which a claim fails, or in which a named
Lean theorem says less than its name. Every name carries the prefix `rf_` (theorems) or `Rf` (objects) so that nothing collides with the
files of gravity#17.

1. **The axioms as modelled have a model in which nothing ever happens.** With both judges refusing everything, no request is ever
   performed, and every theorem of Gate.lean, Record.lean, Standing.lean and Theory.lean holds of that run, because each is universally
   quantified over the judges (`rf_nothing_ever_performed`). Together with `Cmb.empty_recipe_proven` (finding F9): the empty
   configuration and the inert configuration are both "proven". The chain states no liveness; it cannot distinguish a working CMOS
   from a switched-off one.
2. **`Ground.pressed_collapse` has no pressing in it.** Its statement names no pair; it holds of a minted pair word for word
   (`rf_collapse_needs_no_pressing`). What it proves is that an all-passing judge passes good evidence, which is true of every pair.
3. **The CHSH bound is a property of the encoding, not of the gate.** `NoGo.gateModel` (gravity#17) lets each half see its own setting
   only. Axiom 1 gives each half "full reach over the act". A gate whose halves see the whole act reaches S = 4 at every hidden state
   (`rf_full_reach_reaches_four`): above Bell's 2 and above Tsirelson's 2√2. So the gate is not a Bell experiment at all, and
   `gate_obeys_chsh` decides nothing about DMP; it decides something about `gateModel`.
4. **The `live` bit is a claim.** `Evidence.live` is a field of the record the witness reads; the guard admits any record that says it
   is live, read now and inside its window, whoever wrote it (`rf_guard_trusts_the_live_bit`). Axiom 2's "never a claim" has no
   counterpart in the model: the model's evidence is the claim.
5. **Axiom 2 as modelled passes a replay.** The same token window, verified live at two points of use, passes both times
   (`rf_axiom2_passes_a_replay`). C2.L3 ("the same message is never acted on twice") is not a consequence of K2; the replay memory of
   `R1Model.lean` is construction.
6. **DMP-complete is the ledger.** Under an all-yes ledger `Recipe.dmpComplete` is well-formedness of a parent array and nothing more
   (`rf_dmpComplete_is_the_ledger`). "Both chains prove it" and "every dependency pinned inside" are the input `agree`, not a theorem.
7. **The trap is its definition.** On a contained item `Floor.offered` is the constant the definition wrote (`rf_trap_is_definitional`);
   `Floor.road_gate` unfolds it.
8. **Axiom 3's order is a tree: the past of every line is a chain** (`rf_past_is_a_chain`). In a causal set that embeds faithfully in a
   Lorentzian manifold of two or more dimensions the past of an element holds unrelated pairs, and the fraction of related pairs is a
   constant of the dimension (Myrheim 1978; Meyer 1988); in a tree it falls to zero as the tree grows. So the "causal set" reading of
   gravity#19 level 0k does not hold of DMP's hierarchy.
-/
import Dmp.Gate
import Dmp.Record
import Dmp.Ground
import Dmp.Floor
import Dmp.Complete

namespace Dmp

/-! ## 1. A model in which nothing ever happens -/

/-- A judge that refuses everything refuses behind the guard too. -/
theorem rf_refuse_guard (e : Evidence) (t : Nat) : guard (fun _ => .refuse) e t = .refuse := by
  unfold guard
  split <;> rfl

theorem rf_refuse_gate_not_pass : gate .refuse .refuse ≠ .pass := by
  intro h
  exact absurd ((gate_pass_iff _ _).mp h).1 (by decide)

/-- One step under two refusing judges performs nothing. -/
theorem rf_step_refuse (s : State) (r : Request) :
    (step (fun _ => .refuse) (fun _ => .refuse) s r).performed = s.performed := by
  simp [step, rf_refuse_guard, rf_refuse_gate_not_pass]

/-- The inert configuration: under two refusing judges no run ever performs an act. Every theorem of the chain holds of it. -/
theorem rf_nothing_ever_performed (rs : List Request) :
    ∀ s : State, (run (fun _ => .refuse) (fun _ => .refuse) s rs).performed = s.performed := by
  induction rs with
  | nil => intro s; rfl
  | cons r rs ih =>
    intro s
    simp only [run]
    rw [ih, rf_step_refuse]

/-! ## 2. `pressed_collapse` has no pressing in it -/

/-- The statement of `Ground.pressed_collapse` names no pair, so it holds of a minted pair word for word: what it proves is that an
    all-passing judge passes good evidence, on any pair. -/
theorem rf_collapse_needs_no_pressing (_p : Pair) (_hm : _p.minted) (e1 e2 : Evidence) (t : Nat)
    (h1 : e1.ok t = true) (h2 : e2.ok t = true) :
    ∃ j : Evidence → Verdict, gate (guard j e1 t) (guard j e2 t) = .pass :=
  pressed_collapse e1 e2 t h1 h2

/-! ## 3. The CHSH bound is a property of the encoding -/

/-- A ±1-valued outcome. -/
def rfPm (b : Bool) : Int := if b then 1 else -1

/-- A model whose halves have full reach over the act (Axiom 1): each outcome may read both settings and the hidden state. -/
structure RfFullReachModel (Λ : Type) where
  A : Bool → Bool → Λ → Bool
  B : Bool → Bool → Λ → Bool

/-- The CHSH combination with both settings visible to both halves. -/
def RfFullReachModel.S {Λ : Type} (m : RfFullReachModel Λ) (l : Λ) : Int :=
  rfPm (m.A false false l) * rfPm (m.B false false l) + rfPm (m.A false true l) * rfPm (m.B false true l) +
  rfPm (m.A true false l) * rfPm (m.B true false l) - rfPm (m.A true true l) * rfPm (m.B true true l)

/-- Two halves that see the whole act: the trust half always passes, the information half refuses exactly the act both settings mark. -/
def rfFullReachGate : RfFullReachModel Unit :=
  { A := fun _ _ _ => true, B := fun x y _ => !(x && y) }

/-- With full reach the gate reaches the algebraic maximum 4, above Bell's 2 and Tsirelson's 2√2: the gate is no Bell experiment, and
    `NoGo.gate_obeys_chsh` (gravity#17) is a theorem about its encoding `gateModel`, in which each half sees its own setting only. -/
theorem rf_full_reach_reaches_four : rfFullReachGate.S () = 4 := by decide

/-! ## 4. The `live` bit is a claim -/

/-- A record that says it is live, read at 7, inside a window: whoever wrote it, the guard admits it and the judge decides. -/
theorem rf_guard_trusts_the_live_bit (judge : Evidence → Verdict) :
    guard judge ⟨7, 0, 10, true⟩ 7 = judge ⟨7, 0, 10, true⟩ := by
  have h : (⟨7, 0, 10, true⟩ : Evidence).ok 7 = true := by decide
  simp [guard, h]

/-! ## 5. Axiom 2 as modelled passes a replay -/

/-- The same token window, verified live at two points of use, passes at both: K2 alone does not give C2.L3. -/
theorem rf_axiom2_passes_a_replay (judge : Evidence → Verdict) (hj : ∀ e, judge e = .pass) :
    guard judge ⟨7, 0, 10, true⟩ 7 = .pass ∧ guard judge ⟨8, 0, 10, true⟩ 8 = .pass := by
  have h7 : (⟨7, 0, 10, true⟩ : Evidence).ok 7 = true := by decide
  have h8 : (⟨8, 0, 10, true⟩ : Evidence).ok 8 = true := by decide
  simp [guard, h7, h8, hj]

/-! ## 6. DMP-complete is the ledger -/

/-- Under an all-yes ledger, DMP-complete is well-formedness of the parent array and nothing more. -/
theorem rf_dmpComplete_is_the_ledger (fcl : List FailureClass) (r : Recipe) :
    r.dmpComplete fcl (fun _ => true) ↔ r.wf fcl := by
  unfold Recipe.dmpComplete
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, fun _ _ => rfl⟩

/-! ## 7. The trap is its definition -/

/-- On a contained item the offer is the constant the definition wrote. -/
theorem rf_trap_is_definitional (i : Item) (h : i.contained = true) (op : Op) :
    offered i op = (op == .readmit || op == .destroy) := by
  simp [offered, h]

/-! ## 8. Axiom 3's order is a tree -/

/-- The past of every line is a chain: any two lines on one chain lie on each other's. A causal set that embeds in a Lorentzian manifold
    of two or more dimensions has unrelated pairs in every past; this one has none. -/
theorem rf_past_is_a_chain (fcl : List FailureClass) (r : Recipe) (hwf : r.wf fcl) :
    ∀ i, i < r.n → ∀ j k, j ∈ r.chain i → k ∈ r.chain i → j ∈ r.chain k ∨ k ∈ r.chain j := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi j k hj hk
    rw [r.chain_unfold fcl hwf i hi] at hj hk
    simp only [List.mem_cons] at hj hk
    cases hj with
    | inl hji =>
      right
      rw [hji, r.chain_unfold fcl hwf i hi]
      simp only [List.mem_cons]
      exact hk
    | inr hj' =>
      cases hk with
      | inl hki =>
        left
        rw [hki, r.chain_unfold fcl hwf i hi]
        simp only [List.mem_cons]
        exact Or.inr hj'
      | inr hk' =>
        cases hp : (r.line i).parent with
        | none => simp [hp] at hj'
        | some p =>
          simp only [hp] at hj' hk'
          have hok := (hwf i hi).1
          rw [hp] at hok
          exact ih p hok.1 (by omega) j k hj' hk'

end Dmp
