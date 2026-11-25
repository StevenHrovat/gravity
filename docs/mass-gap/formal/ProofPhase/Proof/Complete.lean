/-
P vs NP, proof systems, Lean part 6: refutation completeness of resolution (2026-11-23). Released under Apache 2.0.

Paper: `docs/pnp/DICHOTOMY-TRANSFER.md`, section 7.
-/

import ProofPhase.Proof.SizeWidth

/-!
# Every contradiction is refutable: completeness of tree-like resolution

`TL.unsat` (`Resolution.lean`) is soundness: what has a refutation has no satisfying assignment, so a refutation
cannot start from something true. This file proves the converse.

* `complete`: **every unsatisfiable CNF has a tree-like resolution refutation.**

**Proof.** Induction on the number of literals.
* If there is none, the CNF can only contain the empty clause, and it must contain it, since the empty CNF is
  satisfiable.
* Otherwise pick a literal `y`. Both restrictions `F|y` and `F|¬y` are unsatisfiable (`sat_of_restrict`: a satisfying
  assignment of `F|y`, with `y` set true, satisfies `F`) and have fewer literals.
* Their refutations lift back (`TL.lift`) to derivations from `F` of a subclause of `{¬y}` and of `{y}`. If either is
  empty we are done; otherwise one resolution step on `y` gives the empty clause.

The size of the refutation this gives is up to `2^(number of variables)` leaves: completeness says a refutation
exists, not that a short one does.

**New here:** everything in this file.
-/

namespace ProofPhase.Proof

variable {α : Type*} [DecidableEq α]

/-- `a` satisfies every clause of `F`. -/
def Sat (a : α → Bool) (F : CNF α) : Prop := ∀ A ∈ F, ¬ Falsifies a A

theorem lits_restrict' (ℓ : α × Bool) (F : CNF α) : lits (restrict ℓ F) ⊆ (lits F).erase ℓ := by
  intro z hz
  obtain ⟨B, hB, hzB⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨A, hA, hℓA, rfl⟩ := mem_restrict.mp hB
  obtain ⟨-, hz2⟩ := Finset.mem_erase.mp hzB
  exact Finset.mem_erase.mpr ⟨fun e => hℓA (e ▸ hz2), subset_lits hA hz2⟩

omit [DecidableEq α] in
theorem eq_or_eq_nl_of_fst_eq {l y : α × Bool} (h : l.1 = y.1) : l = y ∨ l = nl y := by
  obtain ⟨x, b⟩ := l
  obtain ⟨x', b'⟩ := y
  simp only at h
  subst h
  cases b <;> cases b' <;> simp [nl]

/-- **A model of `F|y` gives a model of `F`**: set `y` true. -/
theorem sat_of_restrict {F : CNF α} {y : α × Bool} {a : α → Bool} (h : Sat a (restrict y F)) :
    Sat (Function.update a y.1 y.2) F := by
  intro A hA hF
  by_cases hyA : y ∈ A
  · exact hF y hyA (by simp)
  · refine h (A.erase (nl y)) (mem_restrict.mpr ⟨A, hA, hyA, rfl⟩) fun l hl => ?_
    obtain ⟨hl1, hl2⟩ := Finset.mem_erase.mp hl
    have hly : l.1 ≠ y.1 := fun e => by
      rcases eq_or_eq_nl_of_fst_eq e with h' | h'
      · exact hyA (h' ▸ hl2)
      · exact hl1 h'
    have := hF l hl2
    rwa [Function.update_of_ne hly] at this

/-- Helper: a subset of `insert x P` without `y` lies in `insert x D` when `P \ {y} ⊆ D`. -/
theorem sub_insert_of' {X P D : Clause α} {x y : α × Bool} (hX : X ⊆ insert x P) (hD : P.erase y ⊆ D) (hy : y ∉ X) :
    X ⊆ insert x D :=
  WD.sub_insert_of hX hD hy

/-- **Lifting a restricted tree-like derivation**: a derivation of `C` from `F|ℓ` gives one from `F` of a subclause
of `C ∪ {¬ℓ}`, with no more leaves. -/
theorem TL.lift {F : CNF α} {ℓ : α × Bool} {C : Clause α} {s : ℕ} (h : TL (ProofPhase.Proof.restrict ℓ F) C s) :
    ∃ C' ⊆ insert (nl ℓ) C, ∃ s' ≤ s, TL F C' s' := by
  induction h with
  | ax hB =>
    obtain ⟨A, hA, -, rfl⟩ := mem_restrict.mp hB
    refine ⟨A, fun z hz => ?_, 1, le_rfl, TL.ax hA⟩
    by_cases hz' : z = nl ℓ
    · exact hz' ▸ Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hz', hz⟩)
  | @res P Q s t y _ _ hy hny ihP ihQ =>
    obtain ⟨P', hP's, s', hs', hP'⟩ := ihP
    obtain ⟨Q', hQ's, t', ht', hQ'⟩ := ihQ
    have hPC : P.erase y ⊆ P.erase y ∪ Q.erase (nl y) := Finset.subset_union_left
    have hQC : Q.erase (nl y) ⊆ P.erase y ∪ Q.erase (nl y) := Finset.subset_union_right
    by_cases hyP : y ∈ P'
    · by_cases hyQ : nl y ∈ Q'
      · refine ⟨P'.erase y ∪ Q'.erase (nl y), Finset.union_subset ?_ ?_, s' + t', by omega,
          TL.res y hP' hQ' hyP hyQ⟩
        · exact sub_insert_of' (fun z hz => hP's (Finset.mem_of_mem_erase hz)) hPC (Finset.notMem_erase _ _)
        · exact sub_insert_of' (fun z hz => hQ's (Finset.mem_of_mem_erase hz)) hQC (Finset.notMem_erase _ _)
      · exact ⟨Q', sub_insert_of' hQ's hQC hyQ, t', by omega, hQ'⟩
    · exact ⟨P', sub_insert_of' hP's hPC hyP, s', by omega, hP'⟩

theorem complete_zero (F : CNF α) (hl : lits F = ∅) (hF : ∀ a, ¬ Sat a F) : ∃ s, TL F ∅ s := by
  have hall : ∀ A ∈ F, A = ∅ := fun A hA => Finset.subset_empty.mp (hl ▸ subset_lits hA)
  have := hF fun _ => true
  simp only [Sat, not_forall, not_not] at this
  obtain ⟨A, hA, -⟩ := this
  exact ⟨1, hall A hA ▸ TL.ax hA⟩

theorem complete_aux : ∀ N : ℕ, ∀ F : CNF α, (lits F).card ≤ N → (∀ a, ¬ Sat a F) → ∃ s, TL F ∅ s := by
  intro N
  induction N with
  | zero =>
    intro F hN hF
    exact complete_zero F (Finset.card_eq_zero.mp (Nat.le_zero.mp hN)) hF
  | succ N ih =>
    intro F hN hF
    by_cases hl : lits F = ∅
    · exact complete_zero F hl hF
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hl
    have hR1 : ∀ a, ¬ Sat a (restrict y F) := fun a h => hF _ (sat_of_restrict h)
    have hR2 : ∀ a, ¬ Sat a (restrict (nl y) F) := fun a h => hF _ (sat_of_restrict h)
    have hN1 : (lits (restrict y F)).card ≤ N := by
      have := Finset.card_le_card (lits_restrict' y F)
      rw [Finset.card_erase_of_mem hy] at this
      omega
    have hN2 : (lits (restrict (nl y) F)).card ≤ N := by
      have := Finset.card_le_card (lits_restrict (nl y) F)
      rw [nl_nl, Finset.card_erase_of_mem hy] at this
      omega
    obtain ⟨s1, h1⟩ := ih _ hN1 hR1
    obtain ⟨s2, h2⟩ := ih _ hN2 hR2
    obtain ⟨C1, hC1, s1', -, h1'⟩ := TL.lift h1
    obtain ⟨C2, hC2, s2', -, h2'⟩ := TL.lift h2
    rw [nl_nl] at hC2
    by_cases e1 : nl y ∈ C1
    · by_cases e2 : y ∈ C2
      · refine ⟨s2' + s1', ?_⟩
        have hres := TL.res y h2' h1' e2 e1
        have hE : C2.erase y ∪ C1.erase (nl y) = ∅ := by
          ext z
          simp only [Finset.mem_union, Finset.mem_erase, Finset.notMem_empty, iff_false, not_or, not_and]
          refine ⟨fun hz hzC => hz ?_, fun hz hzC => hz ?_⟩
          · simpa using hC2 hzC
          · simpa using hC1 hzC
        rwa [hE] at hres
      · have : C2 = ∅ := Finset.eq_empty_of_forall_notMem fun z hz => e2 (by have hz' := hC2 hz; simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hz'; exact hz' ▸ hz)
        exact ⟨s2', this ▸ h2'⟩
    · have : C1 = ∅ := Finset.eq_empty_of_forall_notMem fun z hz => e1 (by have hz' := hC1 hz; simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hz'; exact hz' ▸ hz)
      exact ⟨s1', this ▸ h1'⟩

/-- **Refutation completeness.** Every unsatisfiable CNF has a tree-like resolution refutation. -/
theorem complete {F : CNF α} (hF : ∀ a : α → Bool, ∃ A ∈ F, Falsifies a A) : ∃ s, TL F ∅ s :=
  complete_aux _ F le_rfl fun a h => by
    obtain ⟨A, hA, hFA⟩ := hF a
    exact h A hA hFA

/-- **Soundness and completeness together**: a CNF has a tree-like refutation exactly when no assignment satisfies
it. -/
theorem refutable_iff {F : CNF α} : (∃ s, TL F ∅ s) ↔ ∀ a : α → Bool, ∃ A ∈ F, Falsifies a A :=
  ⟨fun ⟨_, h⟩ => h.unsat, complete⟩

end ProofPhase.Proof
