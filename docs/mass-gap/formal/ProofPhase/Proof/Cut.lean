/-
P vs NP, proof systems, Lean part 3: the cut principle, width from the boundary of what a clause asserts
(2026-11-23). Released under Apache 2.0.

Paper: `docs/pnp/PROOF-SYSTEMS.md`, section 5.
-/

import ProofPhase.Proof.SizeWidth

/-!
# The cut principle: a clause pays one literal for every variable on the boundary of what it asserts

**Setting.** The CNF is a union of blocks `Ax v`, one per node `v` of a finite set `V` (for Tseitin formulas: one
parity constraint per vertex of a graph, the variables being the edges). `Implies S C`: the blocks in `S` together
force the clause `C` (every assignment satisfying them satisfies `C`).

**The measure of a clause** (Ben-Sasson and Wigderson 2001): `mu C`, the least number of blocks that force `C`. It
is the size of the region whose existence the clause asserts. Along a derivation it behaves like a flux with loss:
* an axiom asserts at most one block (`mu_ax`);
* one resolution step does not create assertion: `mu (resolvent) ≤ mu P + mu Q` (`mu_res`);
* the empty clause asserts everything when every proper part is satisfiable (`mu_empty`): `mu ∅ = |V|`.

So a refutation must pass through a clause asserting a region of middle size (`exists_middle`): between `K / 2` and `K`
blocks, for any `1 ≤ K < |V|`.

**The boundary lemma** (`mem_of_boundary`). Let `S` be a smallest region forcing `C`, `u ∈ S`, and `x` a variable that
toggles the block at `u` (flipping `x` turns `u` from satisfied to violated and back) and is invisible to the other
blocks of `S`. Then `x` occurs in `C`. Physically: the assertion "the region `S` exists as a whole" is only carried
across the boundary by naming each boundary variable; nothing else crosses.

**Main result** (`width_ge`): if every region of middle size has at least `e` such boundary variables (an expansion
hypothesis on the block structure), every refutation has width at least `e`, and (`tl_size_ge`) every tree-like
refutation has more than `2^(e - 1 - w)` leaves.

**Hypotheses, stated:** satisfiability of every proper sub-system (`hsat`; for Tseitin formulas on a connected graph
with odd total charge it is classical) and the boundary count (`hexp`; for Tseitin formulas on an expander graph it is
the edge expansion). Both are statements about the input, not about proofs; the Tseitin encoding and an explicit
expander family are not formalized here.

**New here:** everything in this file.
-/

namespace ProofPhase.Proof

variable {α V : Type*} [DecidableEq α] [Fintype V] [DecidableEq V] (Ax : V → CNF α)

/-- The assignment `a` satisfies every clause of the block at `v`. -/
def SatB (a : α → Bool) (v : V) : Prop := ∀ A ∈ Ax v, ¬ Falsifies a A

/-- The blocks in `S` force the clause `C`. -/
def Implies (S : Finset V) (C : Clause α) : Prop := ∀ a : α → Bool, (∀ v ∈ S, SatB Ax a v) → ¬ Falsifies a C

/-- The whole CNF: the union of all blocks. -/
def allAx : CNF α := Finset.univ.biUnion Ax

/-- The measure of a clause: the least number of blocks that force it. -/
noncomputable def mu (C : Clause α) : ℕ := sInf {n | ∃ S : Finset V, S.card = n ∧ Implies Ax S C}

/-- Flip the variable `x`. -/
def flip (x : α) (a : α → Bool) : α → Bool := Function.update a x (!a x)

variable {Ax}

omit [Fintype V] in
theorem implies_res {S₁ S₂ : Finset V} {P Q : Clause α} (y : α × Bool) (h₁ : Implies Ax S₁ P)
    (h₂ : Implies Ax S₂ Q) : Implies Ax (S₁ ∪ S₂) (P.erase y ∪ Q.erase (nl y)) := by
  intro a ha hF
  rcases falsifies_res hF with h | h
  · exact h₁ a (fun v hv => ha v (Finset.mem_union_left _ hv)) h
  · exact h₂ a (fun v hv => ha v (Finset.mem_union_right _ hv)) h

omit [DecidableEq V] in
/-- A derived clause is forced by all blocks together (soundness). -/
theorem WD.implies_univ {W : ℕ} {C : Clause α} (h : WD (allAx Ax) W C) : Implies Ax Finset.univ C := by
  intro a ha hF
  obtain ⟨A, hA, hFA⟩ := h.exists_falsified a hF
  obtain ⟨v, -, hAv⟩ := Finset.mem_biUnion.mp hA
  exact ha v (Finset.mem_univ _) A hAv hFA

omit [DecidableEq α] [Fintype V] [DecidableEq V] in
theorem mu_le {S : Finset V} {C : Clause α} (h : Implies Ax S C) : mu Ax C ≤ S.card :=
  Nat.sInf_le ⟨S, rfl, h⟩

omit [DecidableEq α] [DecidableEq V] in
theorem mu_spec {C : Clause α} (h : Implies Ax Finset.univ C) : ∃ S : Finset V, S.card = mu Ax C ∧ Implies Ax S C :=
  Nat.sInf_mem (s := {n | ∃ S : Finset V, S.card = n ∧ Implies Ax S C}) ⟨_, _, rfl, h⟩

omit [DecidableEq α] [Fintype V] [DecidableEq V] in
/-- **An axiom asserts at most one block.** -/
theorem mu_ax {v : V} {A : Clause α} (hA : A ∈ Ax v) : mu Ax A ≤ 1 := by
  refine (mu_le (S := {v}) ?_).trans (by simp)
  intro a ha hF
  exact ha v (Finset.mem_singleton_self v) A hA hF

/-- **Assertion is not created by resolution**: `mu (resolvent) ≤ mu P + mu Q`. -/
theorem mu_res {P Q : Clause α} (y : α × Bool) (hP : Implies Ax Finset.univ P) (hQ : Implies Ax Finset.univ Q) :
    mu Ax (P.erase y ∪ Q.erase (nl y)) ≤ mu Ax P + mu Ax Q := by
  obtain ⟨S₁, h1, hS₁⟩ := mu_spec hP
  obtain ⟨S₂, h2, hS₂⟩ := mu_spec hQ
  exact (mu_le (implies_res y hS₁ hS₂)).trans ((Finset.card_union_le _ _).trans (by omega))

omit [DecidableEq α] in
/-- **The empty clause asserts the whole system** when every proper sub-system is satisfiable. -/
theorem mu_empty (hsat : ∀ S : Finset V, S ≠ Finset.univ → ¬ Implies Ax S ∅) (h : Implies Ax Finset.univ ∅) :
    mu Ax (∅ : Clause α) = Fintype.card V := by
  obtain ⟨S, hS, hSi⟩ := mu_spec h
  have : S = Finset.univ := by
    by_contra hne
    exact hsat S hne hSi
  rw [← hS, this, Finset.card_univ]

/-- **A middle clause exists.** In a derivation of a clause asserting more than `K ≥ 1` blocks there is a derived clause
asserting more than `K / 2` and at most `K` blocks. -/
theorem exists_middle {W K : ℕ} (hK : 1 ≤ K) {C : Clause α} (h : WD (allAx Ax) W C) (hC : K < mu Ax C) :
    ∃ D, WD (allAx Ax) W D ∧ K < 2 * mu Ax D ∧ mu Ax D ≤ K := by
  induction h with
  | ax hA _ =>
    obtain ⟨v, -, hAv⟩ := Finset.mem_biUnion.mp hA
    have := mu_ax hAv
    omega
  | @res P Q y hP hQ _ _ _ ihP ihQ =>
    have hsum := mu_res y hP.implies_univ hQ.implies_univ
    by_cases h1 : K < mu Ax P
    · exact ihP h1
    by_cases h2 : K < mu Ax Q
    · exact ihQ h2
    rcases le_total (mu Ax Q) (mu Ax P) with hle | hle
    · exact ⟨P, hP, by omega, by omega⟩
    · exact ⟨Q, hQ, by omega, by omega⟩

omit [Fintype V] in
/-- **The boundary lemma.** If `S` is a smallest set of blocks forcing `C`, and the variable `x` toggles the block at
`u ∈ S` while leaving the other blocks of `S` unchanged, then `x` occurs in `C`. -/
theorem mem_of_boundary {S : Finset V} {C : Clause α} (hS : Implies Ax S C)
    (hmin : ∀ S' : Finset V, Implies Ax S' C → S.card ≤ S'.card) {x : α} {u : V} (hu : u ∈ S)
    (htog : ∀ a, SatB Ax (flip x a) u ↔ ¬ SatB Ax a u)
    (hinv : ∀ v ∈ S, v ≠ u → ∀ a, SatB Ax (flip x a) v ↔ SatB Ax a v) : ∃ b, (x, b) ∈ C := by
  by_contra hx
  push Not at hx
  have hnot : ¬ Implies Ax (S.erase u) C := fun h => by
    have h1 := hmin _ h
    rw [Finset.card_erase_of_mem hu] at h1
    have h2 := Finset.card_pos.mpr ⟨u, hu⟩
    omega
  simp only [Implies, not_forall, not_not] at hnot
  obtain ⟨a, ha, hFa⟩ := hnot
  have hau : ¬ SatB Ax a u := fun hsu => by
    refine hS a (fun v hv => ?_) hFa
    by_cases hvu : v = u
    · exact hvu ▸ hsu
    · exact ha v (Finset.mem_erase.mpr ⟨hvu, hv⟩)
  refine hS (flip x a) (fun v hv => ?_) (fun l hl => ?_)
  · by_cases hvu : v = u
    · rw [hvu]; exact (htog a).mpr hau
    · exact (hinv v hv hvu a).mpr (ha v (Finset.mem_erase.mpr ⟨hvu, hv⟩))
  · have hlx : l.1 ≠ x := fun e => hx l.2 (by rw [← e]; exact hl)
    simp only [flip, Function.update_of_ne hlx]
    exact hFa l hl

/-- **The cut principle: width is at least the boundary.** Assume every proper sub-system is satisfiable, and every
region `S` of middle size (`K < 2 |S|`, `|S| ≤ K`, for some `1 ≤ K < |V|`) has at least `e` boundary variables (each
toggles one block of `S` and is invisible to the others). Then every resolution refutation has width at least `e`. -/
theorem width_ge {K e W : ℕ} (hK : 1 ≤ K) (hKV : K < Fintype.card V)
    (hsat : ∀ S : Finset V, S ≠ Finset.univ → ¬ Implies Ax S ∅)
    (hexp : ∀ S : Finset V, K < 2 * S.card → S.card ≤ K → ∃ B : Finset α, e ≤ B.card ∧
      ∀ x ∈ B, ∃ u ∈ S, (∀ a, SatB Ax (flip x a) u ↔ ¬ SatB Ax a u) ∧
        ∀ v ∈ S, v ≠ u → ∀ a, SatB Ax (flip x a) v ↔ SatB Ax a v)
    (h : WD (allAx Ax) W ∅) : e ≤ W := by
  have hroot : K < mu Ax (∅ : Clause α) := by rw [mu_empty hsat h.implies_univ]; exact hKV
  obtain ⟨D, hD, hD1, hD2⟩ := exists_middle hK h hroot
  obtain ⟨S, hS, hSi⟩ := mu_spec hD.implies_univ
  obtain ⟨B, hB, hBx⟩ := hexp S (by rw [hS]; exact hD1) (by rw [hS]; exact hD2)
  have hsub : B ⊆ D.image Prod.fst := by
    intro x hx
    obtain ⟨u, hu, htog, hinv⟩ := hBx x hx
    obtain ⟨b, hb⟩ := mem_of_boundary hSi (fun S' h' => hS ▸ mu_le h') hu htog hinv
    exact Finset.mem_image.mpr ⟨(x, b), hb, rfl⟩
  calc e ≤ B.card := hB
    _ ≤ (D.image Prod.fst).card := Finset.card_le_card hsub
    _ ≤ D.card := Finset.card_image_le
    _ ≤ W := hD.card_le

/-- **The cut principle as a size bound.** Under the same hypotheses, with blocks of clauses of at most `w < e`
literals, every tree-like refutation has more than `2^(e - 1 - w)` leaves. -/
theorem tl_size_ge {K e w : ℕ} (hK : 1 ≤ K) (hKV : K < Fintype.card V)
    (hsat : ∀ S : Finset V, S ≠ Finset.univ → ¬ Implies Ax S ∅)
    (hexp : ∀ S : Finset V, K < 2 * S.card → S.card ≤ K → ∃ B : Finset α, e ≤ B.card ∧
      ∀ x ∈ B, ∃ u ∈ S, (∀ a, SatB Ax (flip x a) u ↔ ¬ SatB Ax a u) ∧
        ∀ v ∈ S, v ≠ u → ∀ a, SatB Ax (flip x a) v ↔ SatB Ax a v)
    (hw : ∀ A ∈ allAx Ax, A.card ≤ w) (hwe : w < e) {s : ℕ} (h : TL (allAx Ax) ∅ s) :
    2 ^ (e - 1 - w) < s := by
  refine tl_size_gt hw (by omega) (fun hW => ?_) h
  have := width_ge hK hKV hsat hexp hW
  omega

end ProofPhase.Proof
