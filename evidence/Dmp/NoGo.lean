/-
The owner's approach, tried on quantum gravity, and the theorems that stop it (docs/qg-attempt.md).

The approach (the owner, 2026-10-27): two axioms, Information and "no information without existence in a self-propagating duality",
with a vector field that spans the possibility space, always going forward until the most optimal possibility space can be extended for
the existence-defining vector; "for QG it is gravity and for DMP it is trust". The instantiation is DMP's own field (depth, mass, freshness,
the potential of Field.lean and Theory.lean) read as the gravitational field, the gate read as the measurement, the record as the entropy.
What follows from it is in docs/qg-attempt.md section 3; what stops it is here, four theorems, each on the axioms as modelled:

1. **The field of the axioms is uncoupled.** The potential is a sum of one term per standing, and the system's act on one standing
   changes no other standing's term (member isolation, T32; the frame rule). A gravitational field is coupled: the field at one place
   changes when the mass at another does (Newton's potential; the Einstein equations). Isolated is the negation of coupled, so no
   instantiation of the axioms' field is gravitational (`dmp_field_uncoupled`, `refresh_touches_only_its_own`, `isolated_iff_not_coupled`,
   `newton_coupled`).
2. **The gate is a local deterministic model, so it obeys the CHSH bound.** A witness's verdict is a function of the evidence it read itself
   and its own judge (Axiom 2); two gates on shared evidence are therefore a local hidden-variable model in Bell's sense, and every such
   model satisfies |S| ≤ 2 (Bell 1964; Clauser, Horne, Shimony and Holt 1969). Quantum mechanics reaches 2√2 (Tsirelson 1980) and
   experiment reaches it (Aspect 1982; Hensen et al. 2015), so no theory whose outcomes are gate verdicts reproduces quantum mechanics, and
   a theory that does not reproduce quantum mechanics is not quantum gravity (`chsh_pointwise`, `chsh_bound`, `gate_obeys_chsh`).
3. **No equation of state.** The forward direction's one equation (Jacobson 1995: heat across a horizon equals temperature times entropy
   change) reads in DMP's objects "the potential drop per record entry is one temperature". Per check the record grows by exactly one entry
   and the potential drops by the refreshed standing's mass times its staleness, which differs from standing to standing, so no single
   temperature exists except in the uniform case (`no_single_temperature`, `clausius_fails`).
4. **A spanning field fixes the support, not the measure.** Two weightings of the same support, both spanned, have different optimal
   layouts, so "proving existence in the DoE with a spanning field" does not solve the probability space; the measure stays an input
   (`spanning_does_not_fix_optimum`).

Nothing here is invented: 1 is the frame rule against the superposition of fields, 2 is Bell's theorem, 3 is Clausius, 4 is Huffman.
-/
import Dmp.Gate
import Dmp.Field

namespace Dmp

/-! ## 1. The field of the axioms is uncoupled -/

/-- Two field states that differ only at position `j`. -/
def differOnlyAt (l l' : List Held) (j : Nat) : Prop := ∀ i, i ≠ j → l[i]? = l'[i]?

/-- The potential's term at position `i`: mass times shortfall (Field.lean's `phi` is their sum). -/
def term (l : List Held) (i : Nat) : Nat :=
  match l[i]? with
  | some h => h.mass * (1000 - h.fresh)
  | none => 0

/-- A field over positions is coupled when some position's value depends on another position's state. -/
def Coupled {S : Type} (differ : S → S → Nat → Prop) (F : S → Nat → Nat) : Prop :=
  ∃ i j s s', i ≠ j ∧ differ s s' j ∧ F s i ≠ F s' i

/-- Isolated: no position's value depends on another's (T32, member isolation: nothing done to one member's nodes changes what another
    member's nodes receive). -/
def Isolated {S : Type} (differ : S → S → Nat → Prop) (F : S → Nat → Nat) : Prop :=
  ∀ i j s s', i ≠ j → differ s s' j → F s i = F s' i

theorem isolated_iff_not_coupled {S : Type} (differ : S → S → Nat → Prop) (F : S → Nat → Nat) : Isolated differ F ↔ ¬ Coupled differ F := by
  constructor
  · rintro h ⟨i, j, s, s', hij, hd, hne⟩
    exact hne (h i j s s' hij hd)
  · intro h i j s s' hij hd
    apply Classical.byContradiction
    intro hne
    exact h ⟨i, j, s, s', hij, hd, hne⟩

/-- DMP's field is isolated: a term depends on its own standing and on nothing else. -/
theorem dmp_field_isolated : Isolated differOnlyAt term := by
  intro i j s s' hij hd
  unfold term
  rw [hd i hij]

theorem dmp_field_uncoupled : ¬ Coupled differOnlyAt term :=
  (isolated_iff_not_coupled differOnlyAt term).mp dmp_field_isolated

/-- The system's own act, a refresh at `j`, touches only position `j`. -/
theorem refresh_touches_only_its_own (j : Nat) : ∀ (l : List Held) (i : Nat), i ≠ j → (refreshAt j l)[i]? = l[i]? := by
  induction j with
  | zero =>
    intro l i hi
    cases l with
    | nil => simp [refreshAt]
    | cons h hs =>
      cases i with
      | zero => exact absurd rfl hi
      | succ n => simp [refreshAt]
  | succ j ih =>
    intro l i hi
    cases l with
    | nil => simp [refreshAt]
    | cons h hs =>
      cases i with
      | zero => simp [refreshAt]
      | succ n =>
        simp only [refreshAt, List.getElem?_cons_succ]
        exact ih hs n (fun h' => hi (by rw [h']))

/-- So a refresh at `j` is a change only at `j`, and by isolation leaves every other term as it was. -/
theorem refresh_changes_no_other_term (j : Nat) (l : List Held) (i : Nat) (hi : i ≠ j) : term (refreshAt j l) i = term l i :=
  dmp_field_isolated i j (refreshAt j l) l hi (fun k hk => refresh_touches_only_its_own j l k hk)

/-- A toy Newtonian potential at `i` (unit distances): the sum of every other mass. It is coupled: the field at 0 changes when the mass at
    1 does. The real one, with the inverse distances, is coupled the same way; so is the Einstein equation, which ties curvature everywhere
    to matter everywhere. -/
def newton (masses : List Nat) (i : Nat) : Nat :=
  (List.range masses.length).foldl (fun acc j => if j = i then acc else acc + masses.getD j 0) 0

def differOnlyAtN (l l' : List Nat) (j : Nat) : Prop := ∀ i, i ≠ j → l[i]? = l'[i]?

theorem newton_coupled : Coupled differOnlyAtN newton := by
  refine ⟨0, 1, [1, 1], [1, 2], by decide, ?_, by decide⟩
  intro i hi
  match i with
  | 0 => rfl
  | 1 => exact absurd rfl hi
  | n + 2 => rfl

/-! ## 2. The gate is a local deterministic model: the CHSH bound -/

/-- A ±1-valued outcome. -/
def pm (b : Bool) : Int := if b then 1 else -1

/-- The CHSH combination at one hidden state: two settings per side. -/
def chsh (a a' b b' : Bool) : Int := pm a * pm b + pm a * pm b' + pm a' * pm b - pm a' * pm b'

/-- At every hidden state the combination is 2 or −2 (the sixteen cases). -/
theorem chsh_pointwise (a a' b b' : Bool) : chsh a a' b b' = 2 ∨ chsh a a' b b' = -2 := by
  cases a <;> cases a' <;> cases b <;> cases b' <;> decide

/-- A local deterministic model: each side's outcome is a function of the hidden state and its own setting only. -/
structure LocalModel (Λ : Type) where
  A : Bool → Λ → Bool
  B : Bool → Λ → Bool

def LocalModel.S {Λ : Type} (m : LocalModel Λ) (l : Λ) : Int := chsh (m.A false l) (m.A true l) (m.B false l) (m.B true l)

/-- The sum of S over a sample of hidden states (a finite measure with rational weights is a sample with repetitions). -/
def LocalModel.ssum {Λ : Type} (m : LocalModel Λ) : List Λ → Int
  | [] => 0
  | l :: rest => m.S l + m.ssum rest

/-- The CHSH bound (Bell 1964; Clauser, Horne, Shimony and Holt 1969): for every local deterministic model and every sample, the average of
    S lies in [−2, 2]. Quantum mechanics reaches 2√2 (Tsirelson 1980); experiment does too (Aspect 1982; Hensen et al. 2015). -/
theorem chsh_bound {Λ : Type} (m : LocalModel Λ) :
    ∀ ls : List Λ, -2 * (ls.length : Int) ≤ m.ssum ls ∧ m.ssum ls ≤ 2 * (ls.length : Int) := by
  intro ls
  induction ls with
  | nil => simp [LocalModel.ssum]
  | cons l rest ih =>
    simp only [LocalModel.ssum, List.length_cons]
    have hs : m.S l = 2 ∨ m.S l = -2 := chsh_pointwise (m.A false l) (m.A true l) (m.B false l) (m.B true l)
    rcases hs with h | h <;> omega

/-- Two gates as a measurement: each side's outcome is its verdict, a function of the evidence it read itself and its own judge (Axiom 2),
    on a shared hidden state (what both read). This is a local deterministic model. -/
def gateModel (judgeA judgeB : Bool → Evidence → Verdict) (t : Nat) : LocalModel (Evidence × Evidence) :=
  { A := fun s l => decide (guard (judgeA s) l.1 t = .pass)
    B := fun s l => decide (guard (judgeB s) l.2 t = .pass) }

/-- Every pair of gates obeys the CHSH bound, whatever the judges and the evidence: the axioms as modelled cannot reproduce the
    correlations of quantum mechanics. -/
theorem gate_obeys_chsh (judgeA judgeB : Bool → Evidence → Verdict) (t : Nat) (ls : List (Evidence × Evidence)) :
    -2 * (ls.length : Int) ≤ (gateModel judgeA judgeB t).ssum ls ∧ (gateModel judgeA judgeB t).ssum ls ≤ 2 * (ls.length : Int) :=
  chsh_bound _ ls

/-! ## 3. No equation of state -/

/-- The potential's drop when a standing is refreshed (its term goes to zero): mass times staleness. The record grows by one entry. -/
def dropPerEntry (h : Held) : Nat := h.mass * (1000 - h.fresh)

/-- Two standings with different drops per entry. -/
theorem no_single_temperature : ∃ h h' : Held, dropPerEntry h ≠ dropPerEntry h' :=
  ⟨⟨1, 0⟩, ⟨3, 500⟩, by decide⟩

/-- A Clausius relation with one temperature would need every refresh to drop the potential by the same amount per entry; with two standings
    that differ, no temperature serves. -/
theorem clausius_fails (l : List Held) (h1 h2 : Held) (hm1 : h1 ∈ l) (hm2 : h2 ∈ l) (hne : dropPerEntry h1 ≠ dropPerEntry h2) :
    ¬ ∃ Θ : Nat, ∀ h ∈ l, dropPerEntry h = Θ := by
  rintro ⟨Θ, hΘ⟩
  exact hne ((hΘ h1 hm1).trans (hΘ h2 hm2).symm)

/-! ## 4. A spanning field fixes the support, not the measure -/

/-- Root-directed cost of a two-item chain: the first item sits at depth 1, the second at depth 2; each costs its weight times its depth. -/
def chainCost (w1 w2 : Nat) (firstIs1 : Bool) : Nat := if firstIs1 then w1 * 1 + w2 * 2 else w2 * 1 + w1 * 2

/-- The same support (both items present, both reachable) under two weightings has two different optimal orders: the field spans the
    support either way, and the measure decides the optimum. -/
theorem spanning_does_not_fix_optimum :
    chainCost 3 1 true < chainCost 3 1 false ∧ chainCost 1 3 false < chainCost 1 3 true := by decide

end Dmp
