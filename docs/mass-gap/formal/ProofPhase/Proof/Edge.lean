/-
P vs NP, the edge: where the crossing argument stops for cutting planes on random 3-CNF (2026-11-23).
Released under Apache 2.0.

Paper: `docs/pnp/EDGE.md`.
-/

import ProofPhase.Proof.Crossing

/-!
# The crossing line is cheap in cutting planes

`Crossing.lean` (`cross_any_system`) shows that every refutation of an expanding system, in every sound proof system
with at most two premises per rule, contains a line sensitive to at least `e` variables. For resolution the next step
is the size-width step (`SizeWidth.lean`): a line sensitive to `e` variables is a clause of width `e`, and a clause is
killed (made true) by fixing any one of its literals (`clause_killed`), so restrictions remove wide clauses and wide
clauses cost size.

This file shows that the same step fails for cutting planes, with one explicit line.
* `thr B k`: the cutting-planes line "at least `k` of the variables in `B` are true", the inequality
  `Σ_{x ∈ B} x ≥ k` with unit coefficients (`thr_iff_cp`).
* `thr_sensitive`: for `1 ≤ k ≤ |B|` it is sensitive to **every** variable of `B` in the sense of `cross_any_system`.
* `thr_survives`: no restriction of fewer than `k` variables kills it: whatever values they get, some extension falsifies
  the line.
* `majority_line`: for every nonempty `B` there is one cutting-planes line that is sensitive to every variable of `B`
  and survives every restriction of fewer than `|B| / 2` variables.

So in cutting planes a single line can carry the whole crossing, and the restriction step that turns width into size
has nothing to remove. The crossing argument stops exactly here (`EDGE.md`, section 3).

**New here:** everything in this file.
-/

namespace ProofPhase.Proof.Edge

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- For contrast: a clause is made true by fixing any one of its literals. -/
theorem clause_killed {C : Clause α} {l : α × Bool} (hl : l ∈ C) (a : α → Bool) (ha : a l.1 = l.2) :
    ¬ Falsifies a C :=
  fun h => h l hl ha

/-- The cutting-planes line "at least `k` of the variables in `B` are true". -/
def thr (B : Finset α) (k : ℕ) (a : α → Bool) : Prop := k ≤ (B.filter fun x => a x = true).card

omit [DecidableEq α] in
/-- `thr B k` is the inequality `Σ_{x ∈ B} 1 · x ≥ k` over the integers. -/
theorem thr_iff_cp (B : Finset α) (k : ℕ) (a : α → Bool) :
    thr B k a ↔ (k : ℤ) ≤ ∑ x ∈ B, (1 : ℤ) * (if a x = true then 1 else 0) := by
  simp only [one_mul, Finset.sum_boole, thr]
  exact_mod_cast Iff.rfl

/-- The indicator assignment of a finite set. -/
def ind (T : Finset α) : α → Bool := fun x => decide (x ∈ T)

theorem filter_ind {B T : Finset α} (hT : T ⊆ B) : (B.filter fun x => ind T x = true) = T := by
  ext x
  simp only [Finset.mem_filter, ind, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hT h, h⟩⟩

theorem flip_ind {T : Finset α} {x : α} (hx : x ∉ T) : ProofPhase.Proof.flip x (ind T) = ind (insert x T) := by
  funext y
  by_cases hy : y = x
  · subst hy
    simp [ProofPhase.Proof.flip, ind, hx]
  · simp [ProofPhase.Proof.flip, ind, hy]

/-- **The threshold line is sensitive to every variable of `B`.** -/
theorem thr_sensitive {B : Finset α} {k : ℕ} (hk : 1 ≤ k) (hkB : k ≤ B.card) {x : α} (hx : x ∈ B) :
    ∃ a, ¬ thr B k a ∧ thr B k (ProofPhase.Proof.flip x a) := by
  have hcard : k - 1 ≤ (B.erase x).card := by
    rw [Finset.card_erase_of_mem hx]
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcard
  have hxT : x ∉ T := fun h => (Finset.notMem_erase x B) (hTsub h)
  have hTB : T ⊆ B := hTsub.trans (Finset.erase_subset x B)
  refine ⟨ind T, ?_, ?_⟩
  · simp only [thr, filter_ind hTB]
    omega
  · rw [flip_ind hxT]
    simp only [thr, filter_ind (Finset.insert_subset hx hTB), Finset.card_insert_of_notMem hxT]
    omega

/-- **No restriction of fewer than `k` variables kills the threshold line.** Whatever values `ρ` the variables of `D`
get, setting all others to false falsifies `thr B k`. -/
theorem thr_survives (B : Finset α) {k : ℕ} (D : Finset α) (hD : D.card < k) (ρ : α → Bool) :
    ∃ a, (∀ x ∈ D, a x = ρ x) ∧ ¬ thr B k a := by
  refine ⟨fun x => if x ∈ D then ρ x else false, fun x hx => by simp [hx], ?_⟩
  have hsub : (B.filter fun x => (if x ∈ D then ρ x else false) = true) ⊆ D := by
    intro x hx
    rw [Finset.mem_filter] at hx
    by_contra hxD
    simp [hxD] at hx
  have := Finset.card_le_card hsub
  simp only [thr]
  omega

/-- **One cutting-planes line carries the whole crossing.** For every nonempty `B` the majority line is sensitive to
every variable of `B` and survives every restriction of fewer than `|B| / 2` variables. -/
theorem majority_line {B : Finset α} (hB : B.Nonempty) :
    ∃ L : (α → Bool) → Prop, (∀ x ∈ B, ∃ a, ¬ L a ∧ L (ProofPhase.Proof.flip x a)) ∧
      ∀ D : Finset α, 2 * D.card < B.card → ∀ ρ : α → Bool, ∃ a, (∀ x ∈ D, a x = ρ x) ∧ ¬ L a := by
  have hB1 : 1 ≤ B.card := Finset.card_pos.mpr hB
  refine ⟨thr B (B.card / 2 + 1), fun x hx => thr_sensitive (by omega) (by omega) hx, fun D hD ρ => ?_⟩
  exact thr_survives B D (by omega) ρ

end ProofPhase.Proof.Edge
