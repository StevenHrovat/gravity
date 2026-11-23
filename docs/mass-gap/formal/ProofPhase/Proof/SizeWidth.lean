/-
P vs NP, proof systems, Lean part 2: the size-width relation for tree-like resolution (2026-11-23).
Released under Apache 2.0.

Paper: `docs/pnp/PROOF-SYSTEMS.md`, section 4.
-/

import ProofPhase.Proof.Resolution

/-!
# Size versus width for tree-like resolution (Ben-Sasson and Wigderson 2001, tree-like case)

`WD F W C`: the clause `C` has a resolution derivation from `F` (DAG-like: clauses may be reused) in which every
clause, axioms included, has at most `W` literals. The **width** of refuting `F` is the least `W` with `WD F W ∅`.

**Main results.**
* `tl_width`: if every axiom has at most `w` literals and `F` has a tree-like refutation with at most `2^d` leaves, then
  `F` has a refutation of width at most `w + d`.
* `tl_size_gt`, the same read backwards: **if `F` has no refutation of width `W ≥ w`, every tree-like refutation has
  more than `2^(W - w)` leaves.** A width lower bound is a size lower bound.

**Proof (the classical one, formalized).** Induction on the number of literals of `F`. The last step of a tree-like
refutation resolves `{y}` with `{¬y}`; its two subtrees, restricted by `y := false` and `y := true`
(`TL.restrict`), refute `F|¬y` and `F|y`, and one of them has at most half the leaves. The small side gets width
`w + d - 1` by induction, the large side `w + d`. The small refutation of `F|¬y` lifts to a derivation of `{y}` (or
of `∅`) from `F` with one more literal per clause (`WD.lift`); resolving that against the axioms containing `¬y`
derives every axiom of `F|y` within width `w + d`, and the refutation of `F|y` then runs on top (`WD.trans`).

**The flux reading (paper, section 4).** Width is the information a single line must hold at once. The
restriction step is the cut: the refutation must send the assertion "no assignment survives" through both sides of the
variable `y`, and the side that is cheap in size pays one literal of width for the crossing.

**What this is not:** the DAG-like bound (size at least `exp((W - w)^2 / (8 n))`) needs, in addition, a random
restriction that kills all wide clauses; it is not formalized here (named in the paper as the first open Lean step).

**New here:** everything in this file.
-/

namespace ProofPhase.Proof

variable {α : Type*} [DecidableEq α]

/-- `WD F W C`: a resolution derivation of `C` from `F` with every clause of at most `W` literals. -/
inductive WD (F : CNF α) (W : ℕ) : Clause α → Prop
  | ax {A : Clause α} : A ∈ F → A.card ≤ W → WD F W A
  | res {P Q : Clause α} (y : α × Bool) : WD F W P → WD F W Q → y ∈ P → nl y ∈ Q →
      (P.erase y ∪ Q.erase (nl y)).card ≤ W → WD F W (P.erase y ∪ Q.erase (nl y))

namespace WD

variable {F : CNF α}

theorem card_le {W : ℕ} {C : Clause α} (h : WD F W C) : C.card ≤ W := by
  cases h with
  | ax _ hc => exact hc
  | res _ _ _ _ _ hc => exact hc

/-- **Soundness**: an assignment falsifying a derived clause falsifies an axiom. -/
theorem exists_falsified {W : ℕ} {C : Clause α} (h : WD F W C) (a : α → Bool) (hC : Falsifies a C) :
    ∃ A ∈ F, Falsifies a A := by
  induction h with
  | ax hA _ => exact ⟨_, hA, hC⟩
  | res y _ _ _ _ _ ihP ihQ =>
    rcases falsifies_res hC with h | h
    · exact ihP h
    · exact ihQ h

theorem mono {W W' : ℕ} (hW : W ≤ W') {C : Clause α} (h : WD F W C) : WD F W' C := by
  induction h with
  | ax hA hc => exact ax hA (hc.trans hW)
  | res y _ _ hy hny hc ihP ihQ => exact res y ihP ihQ hy hny (hc.trans hW)

/-- **Replacing axioms by derivations.** If every axiom of `G` has a subclause derivable from `F` in width `W`, then
everything derivable from `G` in width `W` has a subclause derivable from `F` in width `W`. -/
theorem trans {G : CNF α} {W : ℕ} (hG : ∀ B ∈ G, ∃ B' ⊆ B, WD F W B') {C : Clause α} (h : WD G W C) :
    ∃ C' ⊆ C, WD F W C' := by
  induction h with
  | ax hB _ => exact hG _ hB
  | @res P Q y _ _ hy hny hc ihP ihQ =>
    obtain ⟨P', hP's, hP'⟩ := ihP
    obtain ⟨Q', hQ's, hQ'⟩ := ihQ
    by_cases hyP : y ∈ P'
    · by_cases hyQ : nl y ∈ Q'
      · have hsub : P'.erase y ∪ Q'.erase (nl y) ⊆ P.erase y ∪ Q.erase (nl y) :=
          Finset.union_subset_union (Finset.erase_subset_erase _ hP's) (Finset.erase_subset_erase _ hQ's)
        exact ⟨_, hsub, res y hP' hQ' hyP hyQ ((Finset.card_le_card hsub).trans hc)⟩
      · refine ⟨Q', fun z hz => Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨fun e => hyQ (e ▸ hz), hQ's hz⟩),
          hQ'⟩
    · exact ⟨P', fun z hz => Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun e => hyP (e ▸ hz), hP's hz⟩), hP'⟩

/-- Helper: a subset of `insert x P` without `y` lies in `insert x D` when `P \ {y} ⊆ D`. -/
theorem sub_insert_of {X P D : Clause α} {x y : α × Bool} (hX : X ⊆ insert x P) (hD : P.erase y ⊆ D) (hy : y ∉ X) :
    X ⊆ insert x D := by
  intro z hz
  rcases Finset.mem_insert.mp (hX hz) with h | h
  · exact h ▸ Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (hD (Finset.mem_erase.mpr ⟨fun e => hy (e ▸ hz), h⟩))

/-- **Lifting a restricted derivation.** A width-`W` derivation of `C` from `F|ℓ` gives a width-`(W + 1)` derivation
from `F` of a subclause of `C ∪ {¬ℓ}`. -/
theorem lift {ℓ : α × Bool} {W : ℕ} {C : Clause α} (h : WD (restrict ℓ F) W C) :
    ∃ C' ⊆ insert (nl ℓ) C, WD F (W + 1) C' := by
  induction h with
  | ax hB hc =>
    obtain ⟨A, hA, -, rfl⟩ := mem_restrict.mp hB
    refine ⟨A, fun z hz => ?_, ax hA ?_⟩
    · by_cases hz' : z = nl ℓ
      · exact hz' ▸ Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hz', hz⟩)
    · have := Finset.pred_card_le_card_erase (s := A) (a := nl ℓ)
      omega
  | @res P Q y _ _ hy hny hc ihP ihQ =>
    obtain ⟨P', hP's, hP'⟩ := ihP
    obtain ⟨Q', hQ's, hQ'⟩ := ihQ
    have hPC : P.erase y ⊆ P.erase y ∪ Q.erase (nl y) := Finset.subset_union_left
    have hQC : Q.erase (nl y) ⊆ P.erase y ∪ Q.erase (nl y) := Finset.subset_union_right
    by_cases hyP : y ∈ P'
    · by_cases hyQ : nl y ∈ Q'
      · have hsub : P'.erase y ∪ Q'.erase (nl y) ⊆ insert (nl ℓ) (P.erase y ∪ Q.erase (nl y)) :=
          Finset.union_subset
            (sub_insert_of (fun z hz => hP's (Finset.mem_of_mem_erase hz)) hPC (Finset.notMem_erase _ _))
            (sub_insert_of (fun z hz => hQ's (Finset.mem_of_mem_erase hz)) hQC (Finset.notMem_erase _ _))
        refine ⟨_, hsub, res y hP' hQ' hyP hyQ ?_⟩
        exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by omega))
      · exact ⟨Q', sub_insert_of hQ's hQC hyQ, hQ'⟩
    · exact ⟨P', sub_insert_of hP's hPC hyP, hP'⟩

/-- **Gluing the two halves.** A refutation of `F|ℓ` in width `w + e` and one of `F|¬ℓ` in width `w + e + 1` give a
refutation of `F` in width `w + e + 1`, when the axioms of `F` have at most `w` literals. -/
theorem combine {w e : ℕ} (hw : ∀ A ∈ F, A.card ≤ w) (ℓ : α × Bool) (h1 : WD (restrict ℓ F) (w + e) ∅)
    (h2 : WD (restrict (nl ℓ) F) (w + (e + 1)) ∅) : WD F (w + (e + 1)) ∅ := by
  obtain ⟨C', hC', hC'd⟩ := h1.lift
  have hC'1 : ∀ z ∈ C', z = nl ℓ := fun z hz => by simpa using hC' hz
  have hG : ∀ B ∈ restrict (nl ℓ) F, ∃ B' ⊆ B, WD F (w + (e + 1)) B' := by
    intro B hB
    obtain ⟨A, hA, -, rfl⟩ := mem_restrict.mp hB
    rw [nl_nl]
    by_cases hlA : ℓ ∈ A
    · by_cases hC : nl ℓ ∈ C'
      · have hCe : C'.erase (nl ℓ) = ∅ := by
          ext z
          simp only [Finset.mem_erase, Finset.notMem_empty, iff_false, not_and]
          exact fun hz hzC => hz (hC'1 z hzC)
        refine ⟨A.erase ℓ ∪ C'.erase (nl ℓ), by rw [hCe, Finset.union_empty],
          res ℓ (ax hA (by have := hw A hA; omega)) hC'd hlA hC ?_⟩
        rw [hCe, Finset.union_empty]
        have := hw A hA
        have := Finset.card_erase_le (s := A) (a := ℓ)
        omega
      · have : C' = ∅ := Finset.eq_empty_of_forall_notMem fun z hz => hC (hC'1 z hz ▸ hz)
        exact ⟨C', by rw [this]; exact Finset.empty_subset _, hC'd⟩
    · refine ⟨A, by rw [Finset.erase_eq_of_notMem hlA], ax hA (by have := hw A hA; omega)⟩
  obtain ⟨C'', hC'', hd⟩ := trans hG h2
  rwa [Finset.subset_empty.mp hC''] at hd

end WD

theorem tl_width_aux {w : ℕ} :
    ∀ N : ℕ, ∀ F : CNF α, (lits F).card ≤ N → (∀ A ∈ F, A.card ≤ w) →
      ∀ d s : ℕ, TL F ∅ s → s ≤ 2 ^ d → WD F (w + d) ∅ := by
  intro N
  induction N with
  | zero =>
    intro F hN hw d s h hs
    generalize hC : (∅ : Clause α) = C at h
    cases h with
    | ax hA => subst hC; exact WD.ax hA (by simp)
    | res y hP _ hy _ =>
      have hl : lits F = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hN)
      have := hP.subset_lits' hy
      rw [hl] at this
      exact absurd this (Finset.notMem_empty _)
  | succ N ih =>
    intro F hN hw d s h hs
    generalize hC : (∅ : Clause α) = C at h
    cases h with
    | ax hA => subst hC; exact WD.ax hA (by simp)
    | @res P Q s1 t1 y hP hQ hy hny =>
      have hE := Finset.union_eq_empty.mp hC.symm
      have hnyP : nl y ∉ P := fun h => by
        have : nl y ∈ P.erase y := Finset.mem_erase.mpr ⟨nl_ne y, h⟩
        rw [hE.1] at this; exact Finset.notMem_empty _ this
      have hyQ : y ∉ Q := fun h => by
        have : y ∈ Q.erase (nl y) := Finset.mem_erase.mpr ⟨ne_nl y, h⟩
        rw [hE.2] at this; exact Finset.notMem_empty _ this
      obtain ⟨C1, hC1, s', hs', h1⟩ := hP.restrict (nl y) hnyP
      rw [nl_nl, hE.1, Finset.subset_empty] at hC1
      subst hC1
      obtain ⟨C2, hC2, t', ht', h2⟩ := hQ.restrict y hyQ
      rw [hE.2, Finset.subset_empty] at hC2
      subst hC2
      have hs1 := hP.pos
      have ht1 := hQ.pos
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hs; omega)
      rw [pow_succ] at hs
      have hyL : y ∈ lits F := hP.subset_lits' hy
      have hnyL : nl y ∈ lits F := hQ.subset_lits' hny
      have hN1 : (lits (restrict (nl y) F)).card ≤ N := by
        have := Finset.card_le_card (lits_restrict (nl y) F)
        rw [nl_nl, Finset.card_erase_of_mem hyL] at this
        omega
      have hN2 : (lits (restrict y F)).card ≤ N := by
        have := Finset.card_le_card (lits_restrict y F)
        rw [Finset.card_erase_of_mem hnyL] at this
        omega
      have hw1 := card_restrict_le (ℓ := nl y) hw
      have hw2 := card_restrict_le (ℓ := y) hw
      have h2e : 2 ^ e * 2 = 2 ^ (e + 1) := (pow_succ 2 e).symm
      rcases le_or_gt s1 (2 ^ e) with hsmall | hbig
      · have W1 := ih _ hN1 hw1 e s' h1 (by omega)
        have W2 := ih _ hN2 hw2 (e + 1) t' h2 (by omega)
        rw [← hC]
        exact WD.combine hw (nl y) W1 (by rwa [nl_nl])
      · have W1 := ih _ hN2 hw2 e t' h2 (by omega)
        have W2 := ih _ hN1 hw1 (e + 1) s' h1 (by omega)
        rw [← hC]
        exact WD.combine hw y W1 W2

/-- **Size-width, tree-like.** Axioms of at most `w` literals and a tree-like refutation with at most `2^d` leaves
give a refutation of width at most `w + d`. -/
theorem tl_width {F : CNF α} {w : ℕ} (hw : ∀ A ∈ F, A.card ≤ w) {d s : ℕ} (h : TL F ∅ s) (hs : s ≤ 2 ^ d) :
    WD F (w + d) ∅ :=
  tl_width_aux _ F le_rfl hw d s h hs

/-- **A width lower bound is a size lower bound.** If `F` (axioms of at most `w` literals) has no refutation of
width `W ≥ w`, every tree-like refutation of `F` has more than `2^(W - w)` leaves. -/
theorem tl_size_gt {F : CNF α} {w W : ℕ} (hw : ∀ A ∈ F, A.card ≤ w) (hwW : w ≤ W) (hW : ¬ WD F W ∅) {s : ℕ}
    (h : TL F ∅ s) : 2 ^ (W - w) < s := by
  by_contra hlt
  have := tl_width hw h (not_lt.mp hlt)
  rw [Nat.add_sub_cancel' hwW] at this
  exact hW this

end ProofPhase.Proof
