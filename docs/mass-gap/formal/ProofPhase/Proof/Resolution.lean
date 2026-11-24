/-
P vs NP, proof systems, Lean part 1: resolution and the flux of falsifying assignments (2026-11-23).
Released under Apache 2.0.

Paper: `docs/pnp/PROOF-SYSTEMS.md`, sections 3 and 4.
-/

import Mathlib

/-!
# Resolution, and the flux of falsifying assignments through a refutation

**Setting.** A literal is a pair `(x, b)`: `b = true` is the variable `x`, `b = false` its negation; `nl` is the
complementary literal. A clause is a finite set of literals (their disjunction), a CNF a finite set of clauses. The
resolution rule derives `(P \ {y}) ∪ (Q \ {¬y})` from `P ∋ y` and `Q ∋ ¬y`; a refutation derives the empty clause.

`TL F C s`: the clause `C` has a **tree-like** derivation from `F` with `s` leaves (each leaf an axiom of `F`).

**The flux.** Fix a finite set `T` of total assignments. The flux of `T` through a clause `C` is the number of `a ∈ T`
that falsify `C` (`flux T C`). Three facts make it a conserved quantity with loss along a refutation:
* at the root the flux is everything: `flux T ∅ = |T|` (`flux_empty`);
* across one resolution step it can only be lost, never created: `flux (conclusion) ≤ flux P + flux Q`
  (`flux_res`), because an assignment falsifying the conclusion falsifies one of the premises (`falsifies_res`);
* at a leaf it is at most what the axiom absorbs.

Hence (`TL.card_le`): if every axiom absorbs at most `k` assignments of `T`, every tree-like refutation has at least
`|T| / k` leaves. This is the leaf form of **bottleneck counting** (Haken 1985): the flux that enters at the root has to
leave through the axioms, and a line can pass on only what it absorbs. The path of a single assignment is the
**search** reading (`TL.exists_falsified`): following the falsified premise from the root ends at an axiom falsified by
`a`; this is also soundness (`TL.unsat`).

**A worked case (toy, fully proved):** the complete CNF on a finite variable set (all `2^n` clauses that each use every
variable) needs at least `2^n` leaves in every tree-like refutation (`fullCNF_leaves`): each axiom absorbs exactly one
assignment. The input itself has `2^n` clauses, so this is not a superpolynomial bound; it shows the mechanism.

**Restriction** (`TL.restrict`): fixing a literal `ℓ` true turns a tree-like derivation of `C` (with `ℓ ∉ C`) from `F`
into one of a subclause of `C \ {¬ℓ}` from `F|ℓ`, with no more leaves. This is the step the size-width theorem
(`SizeWidth.lean`) needs.

**New here:** everything in this file (Mathlib has no resolution calculus).
-/

namespace ProofPhase.Proof

section Basic

variable {α : Type*}

/-- The complementary literal. -/
def nl (l : α × Bool) : α × Bool := (l.1, !l.2)

@[simp] theorem nl_nl (l : α × Bool) : nl (nl l) = l := by
  obtain ⟨x, b⟩ := l; cases b <;> rfl

theorem nl_ne (l : α × Bool) : nl l ≠ l := by
  obtain ⟨x, b⟩ := l; cases b <;> simp [nl]

theorem ne_nl (l : α × Bool) : l ≠ nl l := (nl_ne l).symm

/-- A clause: a finite set of literals, read as their disjunction. -/
abbrev Clause (α : Type*) := Finset (α × Bool)

/-- A CNF: a finite set of clauses, read as their conjunction. -/
abbrev CNF (α : Type*) := Finset (Clause α)

/-- The assignment `a` falsifies the clause `C`: every literal of `C` is false under `a`. -/
def Falsifies (a : α → Bool) (C : Clause α) : Prop := ∀ l ∈ C, a l.1 ≠ l.2

instance (a : α → Bool) (C : Clause α) : Decidable (Falsifies a C) :=
  inferInstanceAs (Decidable (∀ l ∈ C, a l.1 ≠ l.2))

theorem falsifies_empty (a : α → Bool) : Falsifies a ∅ := fun _ h => absurd h (Finset.notMem_empty _)

end Basic

variable {α : Type*} [DecidableEq α]

/-- **One resolution step loses no falsifying assignment.** An assignment that falsifies the resolvent falsifies one of
the two premises. -/
theorem falsifies_res {a : α → Bool} {P Q : Clause α} {y : α × Bool}
    (h : Falsifies a (P.erase y ∪ Q.erase (nl y))) : Falsifies a P ∨ Falsifies a Q := by
  by_cases hya : a y.1 = y.2
  · right
    intro l hl
    by_cases hl' : l = nl y
    · subst hl'
      simp only [nl]
      rw [hya]
      cases y.2 <;> decide
    · exact h l (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hl', hl⟩))
  · left
    intro l hl
    by_cases hl' : l = y
    · subst hl'; exact hya
    · exact h l (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hl', hl⟩))

/-- `TL F C s`: a tree-like resolution derivation of `C` from `F` with `s` leaves. -/
inductive TL (F : CNF α) : Clause α → ℕ → Prop
  | ax {A : Clause α} : A ∈ F → TL F A 1
  | res {P Q : Clause α} {s t : ℕ} (y : α × Bool) : TL F P s → TL F Q t → y ∈ P → nl y ∈ Q →
      TL F (P.erase y ∪ Q.erase (nl y)) (s + t)

/-- All literals occurring in `F`. -/
def lits (F : CNF α) : Finset (α × Bool) := F.biUnion id

theorem subset_lits {F : CNF α} {A : Clause α} (hA : A ∈ F) : A ⊆ lits F := fun _ hz =>
  Finset.mem_biUnion.mpr ⟨A, hA, hz⟩

namespace TL

variable {F : CNF α}

theorem pos {C : Clause α} {s : ℕ} (h : TL F C s) : 1 ≤ s := by
  induction h with
  | ax _ => exact le_rfl
  | res _ _ _ _ _ ihP _ => omega

/-- A derived clause uses only literals of the axioms. -/
theorem subset_lits' {C : Clause α} {s : ℕ} (h : TL F C s) : C ⊆ lits F := by
  induction h with
  | ax hA => exact subset_lits hA
  | res y _ _ _ _ ihP ihQ =>
    exact Finset.union_subset ((Finset.erase_subset _ _).trans ihP) ((Finset.erase_subset _ _).trans ihQ)

/-- **The path of one assignment (search reading).** An assignment falsifying a derived clause falsifies an axiom:
follow the falsified premise down the tree. -/
theorem exists_falsified {C : Clause α} {s : ℕ} (h : TL F C s) (a : α → Bool) (hC : Falsifies a C) :
    ∃ A ∈ F, Falsifies a A := by
  induction h with
  | ax hA => exact ⟨_, hA, hC⟩
  | res y _ _ _ _ ihP ihQ =>
    rcases falsifies_res hC with h | h
    · exact ihP h
    · exact ihQ h

/-- **Soundness.** A CNF with a tree-like refutation is unsatisfiable: every assignment falsifies an axiom. -/
theorem unsat {s : ℕ} (h : TL F ∅ s) (a : α → Bool) : ∃ A ∈ F, Falsifies a A :=
  h.exists_falsified a (falsifies_empty a)

end TL

/-! ### The flux -/

/-- The flux of the assignment set `T` through the clause `C`: how many `a ∈ T` falsify `C`. -/
def flux (T : Finset (α → Bool)) (C : Clause α) : ℕ := (T.filter (fun a => Falsifies a C)).card

omit [DecidableEq α] in
/-- **At the root the flux is everything.** -/
theorem flux_empty (T : Finset (α → Bool)) : flux T (∅ : Clause α) = T.card := by
  rw [flux, Finset.filter_true_of_mem fun a _ => falsifies_empty a]

/-- **Flux is never created by a resolution step**: the flux through the resolvent is at most the sum of the fluxes
through the premises. The slack is the loss. -/
theorem flux_res (T : Finset (α → Bool)) (P Q : Clause α) (y : α × Bool) :
    flux T (P.erase y ∪ Q.erase (nl y)) ≤ flux T P + flux T Q := by
  classical
  unfold flux
  refine (Finset.card_le_card fun a ha => ?_).trans (Finset.card_union_le _ _)
  rw [Finset.mem_filter] at ha
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  rcases falsifies_res ha.2 with h | h
  · exact Or.inl ⟨ha.1, h⟩
  · exact Or.inr ⟨ha.1, h⟩

/-- **Flux bound along a tree.** If each axiom absorbs at most `k` assignments of `T`, a clause derived with `s` leaves
carries flux at most `k s`. -/
theorem TL.flux_le {F : CNF α} {T : Finset (α → Bool)} {k : ℕ} (hk : ∀ A ∈ F, flux T A ≤ k) {C : Clause α} {s : ℕ}
    (h : TL F C s) : flux T C ≤ k * s := by
  induction h with
  | ax hA => simpa using hk _ hA
  | res y _ _ _ _ ihP ihQ =>
    rw [mul_add]
    exact (flux_res T _ _ y).trans (add_le_add ihP ihQ)

/-- **Leaf form of bottleneck counting.** If each axiom is falsified by at most `k` assignments of `T`, every tree-like
refutation has at least `|T| / k` leaves: `|T| ≤ k s`. -/
theorem TL.card_le {F : CNF α} {T : Finset (α → Bool)} {k : ℕ} (hk : ∀ A ∈ F, flux T A ≤ k) {s : ℕ}
    (h : TL F ∅ s) : T.card ≤ k * s := by
  rw [← flux_empty T]
  exact h.flux_le hk

/-! ### A worked case: the complete CNF -/

section Full

variable [Fintype α]

/-- The clause falsified exactly by `b`: every variable, with the sign opposite to `b`. -/
def fullClause (b : α → Bool) : Clause α := Finset.univ.image fun x => (x, !b x)

theorem falsifies_fullClause (a b : α → Bool) : Falsifies a (fullClause b) ↔ a = b := by
  simp only [Falsifies, fullClause, Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index]
  constructor
  · intro h
    funext x
    have := h (x, !b x) x rfl
    revert this
    cases a x <;> cases b x <;> simp
  · rintro rfl l x rfl
    cases a x <;> simp

/-- The complete CNF: all `2^n` full clauses. -/
def fullCNF : CNF α := Finset.univ.image fullClause

theorem flux_fullClause (b : α → Bool) : flux Finset.univ (fullClause b) ≤ 1 := by
  unfold flux
  refine Finset.card_le_one.mpr fun a ha a' ha' => ?_
  rw [Finset.mem_filter, falsifies_fullClause] at ha ha'
  rw [ha.2, ha'.2]

/-- **Toy lower bound by flux.** Every tree-like refutation of the complete CNF on `n` variables has at least `2^n`
leaves. -/
theorem fullCNF_leaves {s : ℕ} (h : TL (fullCNF : CNF α) ∅ s) : 2 ^ Fintype.card α ≤ s := by
  have hk : ∀ A ∈ (fullCNF : CNF α), flux Finset.univ A ≤ 1 := by
    intro A hA
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hA
    exact flux_fullClause b
  have := h.card_le hk
  rwa [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, one_mul] at this

end Full

/-! ### Restriction -/

/-- `F|ℓ`: set the literal `ℓ` true. Clauses containing `ℓ` are satisfied and dropped; `¬ℓ` is deleted from the rest. -/
def restrict (ℓ : α × Bool) (F : CNF α) : CNF α := (F.filter fun A => ℓ ∉ A).image fun A => A.erase (nl ℓ)

theorem mem_restrict {ℓ : α × Bool} {F : CNF α} {B : Clause α} :
    B ∈ restrict ℓ F ↔ ∃ A ∈ F, ℓ ∉ A ∧ A.erase (nl ℓ) = B := by
  simp [restrict, and_assoc]

theorem lits_restrict (ℓ : α × Bool) (F : CNF α) : lits (restrict ℓ F) ⊆ (lits F).erase (nl ℓ) := by
  intro z hz
  obtain ⟨B, hB, hzB⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨A, hA, -, rfl⟩ := mem_restrict.mp hB
  obtain ⟨hz1, hz2⟩ := Finset.mem_erase.mp hzB
  exact Finset.mem_erase.mpr ⟨hz1, subset_lits hA hz2⟩

theorem card_restrict_le {ℓ : α × Bool} {F : CNF α} {w : ℕ} (hw : ∀ A ∈ F, A.card ≤ w) :
    ∀ B ∈ restrict ℓ F, B.card ≤ w := by
  intro B hB
  obtain ⟨A, hA, -, rfl⟩ := mem_restrict.mp hB
  exact (Finset.card_erase_le).trans (hw A hA)

/-- Helper: a subset of `P \ {x}` without `y` lies in `D \ {x}` when `P \ {y} ⊆ D`. -/
theorem sub_erase_of {X P D : Clause α} {x y : α × Bool} (hX : X ⊆ P.erase x) (hD : P.erase y ⊆ D) (hy : y ∉ X) :
    X ⊆ D.erase x := by
  intro z hz
  obtain ⟨h1, h2⟩ := Finset.mem_erase.mp (hX hz)
  have hzy : z ≠ y := fun h => hy (h ▸ hz)
  exact Finset.mem_erase.mpr ⟨h1, hD (Finset.mem_erase.mpr ⟨hzy, h2⟩)⟩

/-- **Restriction of a tree-like derivation.** If `ℓ ∉ C` and `C` has a tree-like derivation from `F` with `s` leaves,
then a subclause of `C \ {¬ℓ}` has one from `F|ℓ` with at most `s` leaves. -/
theorem TL.restrict {F : CNF α} {C : Clause α} {s : ℕ} (h : TL F C s) (ℓ : α × Bool) (hℓ : ℓ ∉ C) :
    ∃ C' ⊆ C.erase (nl ℓ), ∃ s' ≤ s, TL (ProofPhase.Proof.restrict ℓ F) C' s' := by
  induction h with
  | ax hA => exact ⟨_, subset_rfl, 1, le_rfl, TL.ax (mem_restrict.mpr ⟨_, hA, hℓ, rfl⟩)⟩
  | @res P Q s t y hP hQ hy hny ihP ihQ =>
    have hPC : P.erase y ⊆ P.erase y ∪ Q.erase (nl y) := Finset.subset_union_left
    have hQC : Q.erase (nl y) ⊆ P.erase y ∪ Q.erase (nl y) := Finset.subset_union_right
    by_cases h1 : y = ℓ
    · subst h1
      have hQ' : y ∉ Q := fun h => hℓ (hQC (Finset.mem_erase.mpr ⟨ne_nl y, h⟩))
      obtain ⟨Q', hQ's, t', ht', hQ'd⟩ := ihQ hQ'
      refine ⟨Q', ?_, t', by omega, hQ'd⟩
      intro z hz
      obtain ⟨h1, h2⟩ := Finset.mem_erase.mp (hQ's hz)
      exact Finset.mem_erase.mpr ⟨h1, hQC (Finset.mem_erase.mpr ⟨h1, h2⟩)⟩
    by_cases h2 : y = nl ℓ
    · subst h2
      have hP' : ℓ ∉ P := fun h => hℓ (hPC (Finset.mem_erase.mpr ⟨ne_nl ℓ, h⟩))
      obtain ⟨P', hP's, s', hs', hP'd⟩ := ihP hP'
      refine ⟨P', ?_, s', by omega, hP'd⟩
      intro z hz
      obtain ⟨h1, h2⟩ := Finset.mem_erase.mp (hP's hz)
      exact Finset.mem_erase.mpr ⟨h1, hPC (Finset.mem_erase.mpr ⟨h1, h2⟩)⟩
    have hP' : ℓ ∉ P := fun h => hℓ (hPC (Finset.mem_erase.mpr ⟨fun e => h1 e.symm, h⟩))
    have hQ' : ℓ ∉ Q := fun h => hℓ (hQC (Finset.mem_erase.mpr ⟨fun e => h2 (by rw [e, nl_nl]), h⟩))
    obtain ⟨P', hP's, s', hs', hP'd⟩ := ihP hP'
    obtain ⟨Q', hQ's, t', ht', hQ'd⟩ := ihQ hQ'
    by_cases hyP : y ∈ P'
    · by_cases hyQ : nl y ∈ Q'
      · refine ⟨P'.erase y ∪ Q'.erase (nl y), Finset.union_subset ?_ ?_, s' + t', by omega,
          TL.res y hP'd hQ'd hyP hyQ⟩
        · exact sub_erase_of (fun z hz => hP's (Finset.mem_of_mem_erase hz)) hPC (Finset.notMem_erase _ _)
        · exact sub_erase_of (fun z hz => hQ's (Finset.mem_of_mem_erase hz)) hQC (Finset.notMem_erase _ _)
      · exact ⟨Q', sub_erase_of hQ's hQC hyQ, t', by omega, hQ'd⟩
    · exact ⟨P', sub_erase_of hP's hPC hyP, s', by omega, hP'd⟩

end ProofPhase.Proof
