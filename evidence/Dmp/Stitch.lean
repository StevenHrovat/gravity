/-
The stitch (part 1 of the verifying session, dmp docs/proposals/c-constraints.md section 6, the batch 0 claims a to i): the three axioms,
T39 (trust and information gate each other) and T40 (a minting needs G0 and a DMP-complete state), stated in Lean where they can be, each
as the owner asked. Section numbers are those of the vendored DMP (0.9.8); the renumbering of part 1 maps T39 to T1 and T40 to T2.

None of the claims breaks, so there is no Break file; what holds only by construction says so in its comment, and the one claim whose
strongest wording is false of the IM verifier (claim b) is stated in the form that is true.

- (f) T39: a part acts on an item only through the gate of its layer and only under a valid admission for the item; no admission, no act;
  no standing, no act (`actOnItem`, `no_admission_no_act`, `no_standing_no_act`, `act_on_item_needs_both_and_admission`, `inside_iff`).
- T37: containment derived, not flagged: an item with no valid admission is contained and offers nothing (`containedAt`,
  `collapse_of_no_admission`, `collapse_of_lapse`, `contained_offers_nothing`). Floor.lean takes `contained` as a flag of the item; here it
  follows from the absence of a valid admission, as the owner asked T37 to.
- (a) typed halves: a Duality holds one trust half and one information half, and a pass needs a verdict of each kind on live evidence
  (`TypedDoT`, `typed_gate_needs_each_kind`).
- (b) no information is ever trusted: a judge may read a message's content (C2's verifier reads the token), and the guard still stands in
  front, so content never suffices for a pass (`content_never_suffices`); where the judge ignores content the decision does, by `rfl`
  (`content_free_judge`). The stronger claim "the gate takes no content as an argument" is false of C2's verifier and is not the right form.
- (c) from trust only existence: what a reader without a grant sees of the record is its count, blind to every verdict (`readout`,
  `readout_blind_to_verdicts`, `readout_step`); with `Physics.Entry.ext` the record has no field a content could hide in.
- (d) T3d under the balance: a balance step is an act and goes through the gate; with a half at hold nothing moves and nothing loosens, and
  the potential never rises (`balanceStep`, `safe_not_live`, `balance_never_raises`).
- (g) a Duality all the way down: a part is two halves, each a part, grounded in the constituents of the minting; the same part twice is
  not minted; every inner node has exactly two children (`PartTree`, `same_part_twice_not_minted`, `duality_has_two_children`,
  `minted_has_two_constituents`).
- (i) T40: a minting record is minted only with at least five constituents and the verdict proven; fewer than five never mint, and an
  unproven line never mints (`Minting`, `fewer_than_five_never_mints`, `unproven_line_never_mints`, `five_without_proof_never_mints`).
  By construction: `Minting.minted` states T40; what is derived is that one uncarried line blocks it (`Recipe.one_unproven_line_unproves`).
- (e) the hierarchy and (h) the owner as a Duality are text findings (docs/findings.md); nothing new is needed in Lean for them.
-/
import Dmp.Gate
import Dmp.Record
import Dmp.Standing
import Dmp.Floor
import Dmp.Field
import Dmp.Layer
import Dmp.Complete
import Dmp.Physics

namespace Dmp

/-! ## (f) T39: trust and information gate each other -/

/-- A part acts on an item only through its layer's gate (both halves on live evidence, K1 and K2) and only under a valid admission for the
    item (the words: information is inside while its admission is valid; an admission is evidence with a validity). -/
def actOnItem (j1 j2 : Evidence → Verdict) (e1 e2 : Evidence) (t : Nat) (adm : Option Evidence) : Bool :=
  (gate (guard j1 e1 t) (guard j2 e2 t) == .pass) &&
  (match adm with
   | none => false
   | some a => a.ok t)

/-- No information without trust, the first half: with no admission, no act, whatever the standings. -/
theorem no_admission_no_act (j1 j2 : Evidence → Verdict) (e1 e2 : Evidence) (t : Nat) : actOnItem j1 j2 e1 e2 t none = false := by
  simp [actOnItem]

/-- No trust without information, the other half: with the gate not passing, no act, whatever the admission. -/
theorem no_standing_no_act (j1 j2 : Evidence → Verdict) (e1 e2 : Evidence) (t : Nat) (adm : Option Evidence)
    (h : gate (guard j1 e1 t) (guard j2 e2 t) ≠ .pass) : actOnItem j1 j2 e1 e2 t adm = false := by
  unfold actOnItem
  have : (gate (guard j1 e1 t) (guard j2 e2 t) == Verdict.pass) = false := by
    cases hg : gate (guard j1 e1 t) (guard j2 e2 t) <;> simp_all
  simp [this]

/-- T39 as one statement: an act on an item was passed by both halves on live evidence and holds a valid admission. -/
theorem act_on_item_needs_both_and_admission (j1 j2 : Evidence → Verdict) (e1 e2 : Evidence) (t : Nat) (adm : Option Evidence)
    (h : actOnItem j1 j2 e1 e2 t adm = true) :
    e1.ok t = true ∧ e2.ok t = true ∧ guard j1 e1 t = .pass ∧ guard j2 e2 t = .pass ∧ ∃ a, adm = some a ∧ a.ok t = true := by
  unfold actOnItem at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hg, ha⟩ := h
  have hpass : gate (guard j1 e1 t) (guard j2 e2 t) = .pass := by
    cases hg' : gate (guard j1 e1 t) (guard j2 e2 t) <;> simp_all
  obtain ⟨h1, h2, g1, g2⟩ := act_needs_both_with_evidence j1 j2 e1 e2 t hpass
  refine ⟨h1, h2, g1, g2, ?_⟩
  cases adm with
  | none => simp at ha
  | some a => exact ⟨a, rfl, ha⟩

/-- Inside, for one item: both standings live and the admission valid. The two conditions are conjoined by construction; the content of
    T39 is that neither alone is inside. -/
theorem inside_iff (j1 j2 : Evidence → Verdict) (e1 e2 : Evidence) (t : Nat) (a : Evidence) :
    actOnItem j1 j2 e1 e2 t (some a) = true ↔ gate (guard j1 e1 t) (guard j2 e2 t) = .pass ∧ a.ok t = true := by
  unfold actOnItem
  cases hg : gate (guard j1 e1 t) (guard j2 e2 t) <;> simp

/-! ## T37: containment derived from the absence of a valid admission -/

/-- An item is contained at `t` when no admission for it is valid then: nothing defines this boundary, it follows (T37). -/
def containedAt (adm : Option Evidence) (t : Nat) : Bool :=
  match adm with
  | none => true
  | some a => !a.ok t

/-- The collapse: an item no admission names is contained. -/
theorem collapse_of_no_admission (t : Nat) : containedAt none t = true := rfl

/-- A lapse contains: when the admission's validity has run out, the item is contained without any act (T27: a lapse is not an act). -/
theorem collapse_of_lapse (a : Evidence) (t : Nat) (h : a.validUntil ≤ t) : containedAt (some a) t = true := by
  simp [containedAt, lapsed_never_ok a t h]

/-- A contained item offers nothing: no act on it passes, whatever the gate says (the trap of T31, from the admission alone). -/
theorem contained_offers_nothing (j1 j2 : Evidence → Verdict) (e1 e2 : Evidence) (t : Nat) (adm : Option Evidence)
    (h : containedAt adm t = true) : actOnItem j1 j2 e1 e2 t adm = false := by
  cases adm with
  | none => exact no_admission_no_act j1 j2 e1 e2 t
  | some a =>
    simp only [containedAt, Bool.not_eq_true'] at h
    simp [actOnItem, h]

/-! ## (a) Typed halves -/

/-- The two kinds of half (Axiom 1): one owns trust, one owns information. -/
inductive Half where
  | trust
  | information
  deriving DecidableEq, Repr

/-- A Duality whose halves are typed, one of each kind. -/
structure TypedDoT where
  dot : DoT
  kind : Witness → Half
  typed : kind dot.w1 ≠ kind dot.w2

/-- The typed gate: each half judges as its kind does (the trust half whether the act may happen, the information half whether it is meant
    and right), behind the evidence guard; the dual gate decides. -/
def TypedDoT.gate (d : TypedDoT) (judge : Half → Evidence → Verdict) (e1 e2 : Evidence) (t : Nat) : Verdict :=
  Dmp.gate (guard (judge (d.kind d.dot.w1)) e1 t) (guard (judge (d.kind d.dot.w2)) e2 t)

/-- A pass needs a verdict of each kind on live evidence: neither half can discharge the other's check, because the halves are of
    different kinds and the gate needs both. -/
theorem typed_gate_needs_each_kind (d : TypedDoT) (judge : Half → Evidence → Verdict) (e1 e2 : Evidence) (t : Nat)
    (h : d.gate judge e1 e2 t = .pass) :
    (∃ e, e.ok t = true ∧ guard (judge .trust) e t = .pass) ∧ (∃ e, e.ok t = true ∧ guard (judge .information) e t = .pass) := by
  unfold TypedDoT.gate at h
  obtain ⟨h1, h2, g1, g2⟩ := act_needs_both_with_evidence _ _ e1 e2 t h
  have hne := d.typed
  cases hk1 : d.kind d.dot.w1 <;> cases hk2 : d.kind d.dot.w2 <;> rw [hk1] at g1 <;> rw [hk2] at g2
  · exact absurd (hk1.trans hk2.symm) hne
  · exact ⟨⟨e1, h1, g1⟩, ⟨e2, h2, g2⟩⟩
  · exact ⟨⟨e2, h2, g2⟩, ⟨e1, h1, g1⟩⟩
  · exact absurd (hk1.trans hk2.symm) hne

/-! ## (b) No information is ever trusted: content never suffices -/

/-- A message as a witness reads it: its content, and the evidence the witness verified itself about it (its own roots, the live register,
    its clock). The content is the thing verified, never the verifier. -/
structure Message (Content : Type) where
  content : Content
  evidence : Evidence

/-- A judge may read the content (C2's verifier reads the token in the message); the guard stands in front of it all the same. -/
def judgeMessage {Content : Type} (judge : Content → Evidence → Verdict) (m : Message Content) (t : Nat) : Verdict :=
  guard (judge m.content) m.evidence t

/-- Content never suffices: a pass on a message rests on evidence the witness verified itself, live, at the step. -/
theorem content_never_suffices {Content : Type} (judge : Content → Evidence → Verdict) (m : Message Content) (t : Nat)
    (h : judgeMessage judge m t = .pass) : m.evidence.ok t = true :=
  guard_pass_needs_evidence _ _ _ h

/-- Where the judge does not read the content, the decision does not depend on it, by the shape of the signature. -/
theorem content_free_judge {Content : Type} (j : Evidence → Verdict) (c c' : Content) (e : Evidence) (t : Nat) :
    judgeMessage (fun _ => j) ⟨c, e⟩ t = judgeMessage (fun _ => j) ⟨c', e⟩ t := rfl

/-! ## (c) From trust only existence: the readout -/

/-- What a reader without a grant sees of a record: its count. -/
def readout (s : State) : Nat := s.log.length

/-- The readout is blind to every verdict: two records of the same length read the same. -/
theorem readout_blind_to_verdicts (s s' : State) (h : s.log.length = s'.log.length) : readout s = readout s' := h

/-- Every act, passed or refused, moves the readout by exactly one: existence, never content. -/
theorem readout_step (j1 j2 : Evidence → Verdict) (s : State) (r : Request) : readout (step j1 j2 s r) = readout s + 1 :=
  step_records_once j1 j2 s r

/-! ## (d) T3d: safety before liveness under the balance -/

/-- A balance step: the witnesses propose to refresh standing `i`; the refresh is an act and goes through the gate. -/
def balanceStep (v1 v2 : Verdict) (i : Nat) (l : List Held) : List Held :=
  if gate v1 v2 = .pass then refreshAt i l else l

/-- With a whole half at hold or refusing, the balance waits: nothing moves, nothing loosens, the potential stays. Safe, not live. -/
theorem safe_not_live (v : Verdict) (hv : v ≠ .pass) (i : Nat) (l : List Held) :
    balanceStep v .pass i l = l ∧ balanceStep .pass v i l = l := by
  have h := one_witness_never_acts v hv
  unfold balanceStep
  simp [h.1, h.2]

/-- K4 with the gate in front: a balance step never raises the potential, passed or not. -/
theorem balance_never_raises (v1 v2 : Verdict) (i : Nat) (l : List Held) : phi (balanceStep v1 v2 i l) ≤ phi l := by
  unfold balanceStep
  split
  · exact k4_refresh_never_raises i l
  · exact Nat.le_refl _

/-! ## (g) A Duality all the way down, grounded in G0's constituents -/

/-- A part is a Duality of two halves, each a part, down to the constituents of the minting (the words, 2026-10-26 23:28Z; G0). -/
inductive PartTree where
  | constituent (id : Nat)
  | duality (trust : PartTree) (information : PartTree)

/-- The constituents a part is made of. -/
def PartTree.constituents : PartTree → List Nat
  | .constituent i => [i]
  | .duality a b => a.constituents ++ b.constituents

/-- The halves of a part. -/
def PartTree.children : PartTree → List PartTree
  | .constituent _ => []
  | .duality a b => [a, b]

/-- Minted: the two halves share no constituent (independence under the person class, at the grain of G0). A constituent alone is no
    Duality. -/
def PartTree.minted : PartTree → Prop
  | .constituent _ => False
  | .duality a b => ∀ i ∈ a.constituents, i ∉ b.constituents

theorem PartTree.constituents_ne_nil : ∀ p : PartTree, p.constituents ≠ []
  | .constituent _ => by simp [PartTree.constituents]
  | .duality a b => by
    simp only [PartTree.constituents]
    intro h
    exact PartTree.constituents_ne_nil a (List.append_eq_nil_iff.mp h).1

/-- The same part twice is never minted (T38, Layer.lean's `same_part_is_no_duality` at this grain). -/
theorem same_part_twice_not_minted (p : PartTree) : ¬ (PartTree.duality p p).minted := by
  intro h
  cases hc : p.constituents with
  | nil => exact PartTree.constituents_ne_nil p hc
  | cons i rest =>
    have hi : i ∈ p.constituents := by rw [hc]; exact List.mem_cons_self
    exact h i hi hi

/-- Every inner node has exactly two children: the trust tree is binary by the words (docs/physics.md, section 2). -/
theorem duality_has_two_children (a b : PartTree) : (PartTree.duality a b).children.length = 2 := rfl

/-- A minted part rests on at least two constituents: G0's ground is never one. -/
theorem minted_has_two_constituents (p : PartTree) (h : p.minted) : 2 ≤ p.constituents.length := by
  cases p with
  | constituent _ => exact absurd h id
  | duality a b =>
    simp only [PartTree.constituents, List.length_append]
    have ha := List.length_pos_iff.mpr (PartTree.constituents_ne_nil a)
    have hb := List.length_pos_iff.mpr (PartTree.constituents_ne_nil b)
    omega

/-! ## (i) T40: a minting needs G0 and a DMP-complete state -/

/-- A minting record: the constituents that become the White Key Holders (G0: at least five) and Gravity's verdict on the configuration. -/
structure Minting where
  constituents : List Nat
  verdict : Verdict3

/-- Minted only with both sources. By construction: this definition states T40; what is derived is that each source alone fails. -/
def Minting.minted (m : Minting) : Prop := 5 ≤ m.constituents.length ∧ m.verdict = .proven

/-- A proven state with fewer than five constituents never mints: G0 is not derived from the proof. -/
theorem fewer_than_five_never_mints (m : Minting) (h : m.constituents.length < 5) : ¬ m.minted :=
  fun hm => absurd hm.1 (Nat.not_le.mpr h)

/-- Five constituents without a proven state never mint: the ground does not stand in for the proof. -/
theorem five_without_proof_never_mints (m : Minting) (h : m.verdict ≠ .proven) : ¬ m.minted :=
  fun hm => h hm.2

/-- One line the chains do not carry unproves the configuration (`Recipe.one_unproven_line_unproves`), so it never mints, however many
    constituents stand ready. -/
theorem unproven_line_never_mints (fcl : List FailureClass) (r : Recipe) (agree : Nat → Bool) (i : Nat) (hi : i < r.n)
    (ha : agree i = false) (m : Minting) (hv : m.verdict = r.verdict fcl agree) : ¬ m.minted :=
  five_without_proof_never_mints m (by rw [hv]; exact r.one_unproven_line_unproves fcl agree i hi ha)

end Dmp
