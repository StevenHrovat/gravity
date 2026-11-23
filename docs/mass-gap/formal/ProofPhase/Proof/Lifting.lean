/-
NP vs coNP, lifting, part 1: the gadget composition `F ∘ g` as a CNF, a size-counting cutting-planes refutation, and the
creative pair on lifted formulas (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/NP-LIFTING.md`, sections 3 and 5.
-/

import ProofPhase.Proof.CPPairs
import ProofPhase.Proof.SizeWidth

/-!
# Gadget composition `F ∘ g`, as a CNF, and what it does to cutting planes

**The composition** (`comp`). A gadget `g` has Alice's `a` bits, Bob's `b` bits and one output bit. In `F ∘ g` every
variable `i` of `F` is replaced by a block of `a + b` fresh bits, and the value of `i` is `g` of the block. As a CNF: a
clause `D` of `F` is falsified exactly when each of its literals is falsified, and a literal on `i` is falsified by a
block value `(x, y)` with `g x y = ¬ sign`. So for every clause `D ∈ F` and every choice `ch` of such a block value for
each literal of `D`, `F ∘ g` has the clause that is falsified exactly by the assignments agreeing with all chosen block
values. (Full block values are used as certificates, so a clause of width `k` becomes a clause of width at most
`k (a + b)`. The source's Index construction uses smaller certificates of width `k (log m + 1)`; both are
instances of the one reduction "a falsified clause names a falsified clause of `F`", see the paper.)

* `comp_falsified_iff` (proved): an assignment falsifies a clause of `F ∘ g` iff the decoded assignment
  `i ↦ g (block i)` falsifies a clause of `F`. This pins the definition: the composition is the right formula.
* `comp_unsat` / `unsat_of_comp_unsat` (proved): `F ∘ g` is unsatisfiable iff `F` is (for a gadget taking both values).
* `card_compClause_le`, `two_le_card_comp` (proved): widths.

**Cutting planes with a size** (`CPR`). The existing `CPD` (`CPPairs.lean`) says "derivable". `CPR V Ax P` says derivable
with every line (axioms included) in the finite line set `P`, so `P.card` is the proof size. Every `CPR` is a `CPD`.

**The creative pair on lifted formulas** (`lifted_needs_pair`, proved, every `F`, every gadget with both parties holding
a bit): every line of `F ∘ g` has width at least `2` (`two_le_card_comp`), so the all-1/2 point satisfies every axiom
(`half_clause`), so by `refutation_needs_pair` (`CPPairs.lean`) every cutting-planes refutation of `F ∘ g` contains a
rounding of a combination of at least two lines. The lifted formula therefore has the same two-line step as every
other formula with a common fractional solution; lifting does not change that step, it prices it (`LiftingNP.lean`).

**Gadgets.** `xorGadget` (the 2-bit XOR: one bit each) and `indGadget t` (the Index gadget: a `t`-bit pointer, a `2^t`-bit
table). Hiding (`AliceBalanced`, `BobBalanced`): the output is uniform given one party's input. XOR hides against both
parties; Index only against the pointer holder (`ind1_not_bobBalanced`).

**New here:** everything in this file.
-/

namespace ProofPhase.Proof.Lifting

open Finset ProofPhase.Proof ProofPhase.Proof.Edge

/-- A gadget on bit blocks: Alice holds `a` bits, Bob holds `b` bits, the output is one bit. -/
structure Gadget where
  a : ℕ
  b : ℕ
  g : (Fin a → Bool) → (Fin b → Bool) → Bool

/-- The variables of `F ∘ g`: a block of `a` Alice bits and `b` Bob bits for each variable of `F`. -/
abbrev LV (α : Type*) (G : Gadget) := α × (Fin G.a ⊕ Fin G.b)

theorem card_LV (α : Type*) [Fintype α] (G : Gadget) : Fintype.card (LV α G) = Fintype.card α * (G.a + G.b) := by
  simp [LV]

section Compose

variable {α : Type*} [DecidableEq α] (G : Gadget)

/-- Alice's part of the block of variable `i`. -/
def Xof (u : LV α G → Bool) (i : α) : Fin G.a → Bool := fun j => u (i, Sum.inl j)

/-- Bob's part of the block of variable `i`. -/
def Yof (u : LV α G → Bool) (i : α) : Fin G.b → Bool := fun j => u (i, Sum.inr j)

/-- The decoded assignment of `F`: each variable is `g` of its block. -/
def dec (u : LV α G → Bool) : α → Bool := fun i => G.g (Xof G u i) (Yof G u i)

/-- The clause falsified exactly by the assignments whose block `i` is `(x, y)`. -/
def certClause (i : α) (x : Fin G.a → Bool) (y : Fin G.b → Bool) : Clause (LV α G) :=
  (univ.image fun j : Fin G.a => ((i, Sum.inl j), !x j)) ∪ (univ.image fun j : Fin G.b => ((i, Sum.inr j), !y j))

theorem bne_not_iff (p q : Bool) : p ≠ !q ↔ p = q := by cases p <;> cases q <;> simp

theorem ne_iff_eq_not (p q : Bool) : p ≠ q ↔ p = !q := by cases p <;> cases q <;> simp

theorem falsifies_certClause {u : LV α G → Bool} {i : α} {x : Fin G.a → Bool} {y : Fin G.b → Bool} :
    Falsifies u (certClause G i x y) ↔ Xof G u i = x ∧ Yof G u i = y := by
  unfold Falsifies certClause
  constructor
  · intro h
    refine ⟨funext fun j => ?_, funext fun j => ?_⟩
    · have := h ((i, Sum.inl j), !x j) (mem_union_left _ (mem_image.2 ⟨j, mem_univ _, rfl⟩))
      exact (bne_not_iff _ _).1 this
    · have := h ((i, Sum.inr j), !y j) (mem_union_right _ (mem_image.2 ⟨j, mem_univ _, rfl⟩))
      exact (bne_not_iff _ _).1 this
  · rintro ⟨hx, hy⟩ l hl
    rcases mem_union.1 hl with hl | hl
    · obtain ⟨j, -, rfl⟩ := mem_image.1 hl
      exact (bne_not_iff _ _).2 (congrFun hx j)
    · obtain ⟨j, -, rfl⟩ := mem_image.1 hl
      exact (bne_not_iff _ _).2 (congrFun hy j)

/-- A choice of one block value for each literal. -/
abbrev Ch (α : Type*) (G : Gadget) := α × Bool → (Fin G.a → Bool) × (Fin G.b → Bool)

/-- The clause of `F ∘ g` for the clause `D` and the choice `ch`. -/
def compClause (D : Clause α) (ch : Ch α G) : Clause (LV α G) :=
  D.biUnion fun l => certClause G l.1 (ch l).1 (ch l).2

variable [Fintype α]

/-- **The composition `F ∘ g` as a CNF.** One clause for every clause `D` of `F` and every choice of block values that
falsify the literals of `D`. -/
def comp (F : CNF α) : CNF (LV α G) :=
  ((F ×ˢ (univ : Finset (Ch α G))).filter fun p => ∀ l ∈ p.1, G.g (p.2 l).1 (p.2 l).2 = !l.2).image
    fun p => compClause G p.1 p.2

theorem mem_comp {F : CNF α} {A : Clause (LV α G)} :
    A ∈ comp G F ↔ ∃ D ∈ F, ∃ ch : Ch α G, (∀ l ∈ D, G.g (ch l).1 (ch l).2 = !l.2) ∧ compClause G D ch = A := by
  unfold comp
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := mem_image.1 h
    obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
    exact ⟨p.1, (mem_product.1 hp1).1, p.2, hp2, rfl⟩
  · rintro ⟨D, hD, ch, hch, rfl⟩
    exact mem_image.2 ⟨(D, ch), mem_filter.2 ⟨mem_product.2 ⟨hD, mem_univ _⟩, hch⟩, rfl⟩

/-- **The composition is the right formula.** An assignment falsifies a clause of `F ∘ g` exactly when the decoded
assignment falsifies a clause of `F`. -/
theorem comp_falsified_iff (F : CNF α) (u : LV α G → Bool) :
    (∃ A ∈ comp G F, Falsifies u A) ↔ ∃ D ∈ F, Falsifies (dec G u) D := by
  constructor
  · rintro ⟨A, hA, hf⟩
    obtain ⟨D, hD, ch, hch, rfl⟩ := (mem_comp G).1 hA
    refine ⟨D, hD, fun l hl => ?_⟩
    have h1 : Falsifies u (certClause G l.1 (ch l).1 (ch l).2) := fun l' hl' =>
      hf l' (mem_biUnion.2 ⟨l, hl, hl'⟩)
    obtain ⟨hx, hy⟩ := (falsifies_certClause G).1 h1
    have : dec G u l.1 = !l.2 := by
      unfold dec
      rw [hx, hy]
      exact hch l hl
    exact (ne_iff_eq_not _ _).2 this
  · rintro ⟨D, hD, hf⟩
    refine ⟨compClause G D (fun l => (Xof G u l.1, Yof G u l.1)), ?_, ?_⟩
    · refine (mem_comp G).2 ⟨D, hD, fun l => (Xof G u l.1, Yof G u l.1), fun l hl => ?_, rfl⟩
      exact (ne_iff_eq_not _ _).1 (hf l hl)
    · intro l' hl'
      obtain ⟨l, hl, hl''⟩ := mem_biUnion.1 hl'
      have hc : Falsifies u (certClause G l.1 (Xof G u l.1) (Yof G u l.1)) := (falsifies_certClause G).2 ⟨rfl, rfl⟩
      exact hc l' hl''

/-- **Unsatisfiable lifts to unsatisfiable.** -/
theorem comp_unsat {F : CNF α} (hF : ∀ z : α → Bool, ∃ D ∈ F, Falsifies z D) :
    ∀ u : LV α G → Bool, ∃ A ∈ comp G F, Falsifies u A := fun u => (comp_falsified_iff G F u).2 (hF (dec G u))

/-- **And back**, for a gadget that takes both values. -/
theorem unsat_of_comp_unsat {F : CNF α} (ht : ∃ x y, G.g x y = true) (hf : ∃ x y, G.g x y = false)
    (h : ∀ u : LV α G → Bool, ∃ A ∈ comp G F, Falsifies u A) : ∀ z : α → Bool, ∃ D ∈ F, Falsifies z D := by
  have hp : ∀ c : Bool, ∃ p : (Fin G.a → Bool) × (Fin G.b → Bool), G.g p.1 p.2 = c := by
    intro c
    cases c
    · obtain ⟨x, y, hxy⟩ := hf; exact ⟨(x, y), hxy⟩
    · obtain ⟨x, y, hxy⟩ := ht; exact ⟨(x, y), hxy⟩
  choose pick hpick using hp
  intro z
  let u : LV α G → Bool := fun v => match v.2 with
    | Sum.inl j => (pick (z v.1)).1 j
    | Sum.inr j => (pick (z v.1)).2 j
  have hdec : dec G u = z := by
    funext i
    have hX : Xof G u i = (pick (z i)).1 := rfl
    have hY : Yof G u i = (pick (z i)).2 := rfl
    show G.g (Xof G u i) (Yof G u i) = z i
    rw [hX, hY]
    exact hpick (z i)
  obtain ⟨D, hD, hfD⟩ := (comp_falsified_iff G F u).1 (h u)
  exact ⟨D, hD, hdec ▸ hfD⟩

/-! ### Widths -/

omit [Fintype α] in
theorem card_certClause_le (i : α) (x : Fin G.a → Bool) (y : Fin G.b → Bool) :
    (certClause G i x y).card ≤ G.a + G.b := by
  unfold certClause
  calc _ ≤ _ := card_union_le _ _
    _ ≤ (univ : Finset (Fin G.a)).card + (univ : Finset (Fin G.b)).card :=
        add_le_add card_image_le card_image_le
    _ = G.a + G.b := by simp

omit [Fintype α] in
/-- A clause of `F ∘ g` has width at most `|D| (a + b)`. -/
theorem card_compClause_le (D : Clause α) (ch : Ch α G) : (compClause G D ch).card ≤ D.card * (G.a + G.b) := by
  unfold compClause
  refine card_biUnion_le.trans ?_
  rw [← smul_eq_mul]
  exact sum_le_card_nsmul _ _ _ fun l _ => card_certClause_le G _ _ _

/-- **Constant width stays constant for a constant gadget**: if every clause of `F` has width at most `k`, every clause
of `F ∘ g` has width at most `k (a + b)`. -/
theorem card_comp_le {F : CNF α} {k : ℕ} (hk : ∀ D ∈ F, D.card ≤ k) {A : Clause (LV α G)} (hA : A ∈ comp G F) :
    A.card ≤ k * (G.a + G.b) := by
  obtain ⟨D, hD, ch, -, rfl⟩ := (mem_comp G).1 hA
  exact (card_compClause_le G D ch).trans (Nat.mul_le_mul_right _ (hk D hD))

/-- **Every clause of `F ∘ g` has at least two literals**, when both parties hold a bit and no clause of `F` is empty. -/
theorem two_le_card_comp {F : CNF α} (hF : ∀ D ∈ F, D.Nonempty) (ha : 0 < G.a) (hb : 0 < G.b)
    {A : Clause (LV α G)} (hA : A ∈ comp G F) : 2 ≤ A.card := by
  obtain ⟨D, hD, ch, -, rfl⟩ := (mem_comp G).1 hA
  obtain ⟨l, hl⟩ := hF D hD
  have h1 : ((l.1, Sum.inl ⟨0, ha⟩), !(ch l).1 ⟨0, ha⟩) ∈ compClause G D ch :=
    mem_biUnion.2 ⟨l, hl, mem_union_left _ (mem_image.2 ⟨⟨0, ha⟩, mem_univ _, rfl⟩)⟩
  have h2 : ((l.1, Sum.inr ⟨0, hb⟩), !(ch l).2 ⟨0, hb⟩) ∈ compClause G D ch :=
    mem_biUnion.2 ⟨l, hl, mem_union_right _ (mem_image.2 ⟨⟨0, hb⟩, mem_univ _, rfl⟩)⟩
  exact Finset.one_lt_card.2 ⟨_, h1, _, h2, by simp⟩

end Compose

/-! ### Cutting planes lines of a CNF, and refutations with a size -/

section CP

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The sign of a literal: `+1` for a positive one, `−1` for a negated one. -/
def sgn (l : α × Bool) : ℤ := if l.2 then 1 else -1

/-- The clause `C` as the CP line `Σ_{positive} x_v + Σ_{negative} (1 − x_v) ≥ 1`, i.e. `Σ s_l x_l ≥ 1 − #negative`. -/
def clauseLine (C : Clause α) : CPLine α :=
  (fun v => ∑ l ∈ C.filter (fun l => l.1 = v), sgn l,
    1 - ((C.filter fun l => l.2 = false).card : ℤ))

/-- The axioms of a CNF as CP lines (tautological clauses, which say nothing, are left out). -/
def cnfAx (F : CNF α) : Set (CPLine α) := {L | ∃ C ∈ F, (∀ l ∈ C, nl l ∉ C) ∧ L = clauseLine C}

/-- **A clause line holds at a point iff the clause's linear value is at least 1.** -/
theorem holds_clauseLine (p : α → ℚ) (C : Clause α) :
    HoldsAt (univ : Finset α) p (clauseLine C) ↔ 1 ≤ lpVal p C := by
  have hsum : ∑ i : α, ((∑ l ∈ C.filter (fun l => l.1 = i), sgn l : ℤ) : ℚ) * p i =
      ∑ l ∈ C, (sgn l : ℚ) * p l.1 := by
    calc _ = ∑ i : α, ∑ l ∈ C.filter (fun l => l.1 = i), (sgn l : ℚ) * p l.1 := by
          refine sum_congr rfl fun i _ => ?_
          push_cast
          rw [sum_mul]
          refine sum_congr rfl fun l hl => ?_
          rw [(mem_filter.1 hl).2]
      _ = _ := sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) (fun l : α × Bool => (sgn l : ℚ) * p l.1)
  have hl : lpVal p C = ∑ l ∈ C, (sgn l : ℚ) * p l.1 + ((C.filter fun l => l.2 = false).card : ℚ) := by
    unfold lpVal
    have : ∀ l ∈ C, (if l.2 then p l.1 else 1 - p l.1) =
        (sgn l : ℚ) * p l.1 + (if l.2 = false then 1 else 0) := by
      intro l _
      unfold sgn
      cases h : l.2
      all_goals simp
      all_goals ring
    rw [sum_congr rfl this, sum_add_distrib, sum_boole]
  unfold HoldsAt clauseLine
  rw [hl]
  simp only
  rw [hsum]
  push_cast
  constructor <;> intro h <;> linarith

/-- A nonempty clause without a variable in both signs has a coefficient `±1` in its line. -/
theorem clauseLine_unit {C : Clause α} (hne : C.Nonempty) (hnt : ∀ l ∈ C, nl l ∉ C) :
    ∃ j ∈ (univ : Finset α), (clauseLine C).1 j = 1 ∨ (clauseLine C).1 j = -1 := by
  obtain ⟨l, hl⟩ := hne
  refine ⟨l.1, mem_univ _, ?_⟩
  have hfil : C.filter (fun l' => l'.1 = l.1) = {l} := by
    ext l'
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hl', h1⟩
      by_contra hne
      have : l' = nl l := by
        obtain ⟨v, b⟩ := l
        obtain ⟨v', b'⟩ := l'
        simp only at h1
        subst h1
        cases b <;> cases b' <;> simp_all [nl]
      exact hnt l hl (this ▸ hl')
    · rintro rfl
      exact ⟨hl, rfl⟩
  have : (clauseLine C).1 l.1 = sgn l := by
    show ∑ l' ∈ C.filter (fun l' => l'.1 = l.1), sgn l' = sgn l
    rw [hfil, sum_singleton]
  rw [this]
  unfold sgn
  cases l.2 <;> simp

/-- Cutting-planes derivation from the axioms `Ax` with every line (axioms included) in the finite set `P`:
`P.card` is the size of the refutation. -/
inductive CPR (V : Finset α) (Ax : Set (CPLine α)) (P : Finset (CPLine α)) : CPLine α → Prop
  | ax {L : CPLine α} : L ∈ Ax → L ∈ P → CPR V Ax P L
  | add {L₁ L₂ : CPLine α} : CPR V Ax P L₁ → CPR V Ax P L₂ → addL L₁ L₂ ∈ P → CPR V Ax P (addL L₁ L₂)
  | scale {L : CPLine α} (c : ℕ) : 0 < c → CPR V Ax P L → scaleL c L ∈ P → CPR V Ax P (scaleL c L)
  | round {L : CPLine α} (d : ℕ) : 0 < d → (∀ i ∈ V, (d : ℤ) ∣ L.1 i) → CPR V Ax P L → roundL d L ∈ P →
      CPR V Ax P (roundL d L)

omit [DecidableEq α] [Fintype α] in
theorem CPR.toCPD {V : Finset α} {Ax : Set (CPLine α)} {P : Finset (CPLine α)} {L : CPLine α}
    (h : CPR V Ax P L) : CPD V Ax L := by
  induction h with
  | ax hA _ => exact CPD.ax hA
  | add _ _ _ ih1 ih2 => exact CPD.add ih1 ih2
  | scale c hc _ _ ih => exact CPD.scale c hc ih
  | round d hd hdiv _ _ ih => exact CPD.round d hd hdiv ih

/-- **`P` is a cutting-planes refutation of `F`**: the line `0 ≥ 1` is derived from the clauses of `F` with all lines in
`P`. -/
def CPRefutes (F : CNF α) (P : Finset (CPLine α)) : Prop :=
  CPR (univ : Finset α) (cnfAx F) P (fun _ => 0, 1)

/-- **The all-1/2 point satisfies every axiom of a CNF whose clauses have at least two literals.** -/
theorem half_satisfies_cnfAx {F : CNF α} (hF : ∀ C ∈ F, 2 ≤ C.card) :
    ∀ A ∈ cnfAx F, HoldsAt (univ : Finset α) (fun _ => (1 / 2 : ℚ)) A := by
  rintro A ⟨C, hC, -, rfl⟩
  exact (holds_clauseLine _ C).2 (half_clause (hF C hC))

/-- **The creative pair on lifted formulas.** For every CNF `F` without empty clause and every gadget in which both
parties hold a bit, every cutting-planes refutation of `F ∘ g` contains a rounding step whose premise holds at the
all-1/2 point, whose result fails there, and whose premise is not a positive multiple of a single axiom. -/
theorem lifted_needs_pair (G : Gadget) {F : CNF α} (hF : ∀ D ∈ F, D.Nonempty) (ha : 0 < G.a) (hb : 0 < G.b)
    {P : Finset (CPLine (LV α G))} (h : CPRefutes (comp G F) P) :
    ∃ (L₀ : CPLine (LV α G)) (d : ℕ), CPD (univ : Finset (LV α G)) (cnfAx (comp G F)) L₀ ∧ 0 < d ∧
      (∀ i ∈ (univ : Finset (LV α G)), (d : ℤ) ∣ L₀.1 i) ∧
      HoldsAt (univ : Finset (LV α G)) (fun _ => (1 / 2 : ℚ)) L₀ ∧
      ¬ HoldsAt (univ : Finset (LV α G)) (fun _ => (1 / 2 : ℚ)) (roundL d L₀) ∧
      ¬ ∃ A ∈ cnfAx (comp G F), ∃ c : ℕ, 0 < c ∧ L₀ = scaleL c A := by
  have h2 : ∀ C ∈ comp G F, 2 ≤ C.card := fun C hC => two_le_card_comp G hF ha hb hC
  refine refutation_needs_pair (half_satisfies_cnfAx h2) ?_ h.toCPD
  rintro A ⟨C, hC, hnt, rfl⟩
  exact clauseLine_unit (Finset.card_pos.1 (by have := h2 C hC; omega)) hnt

end CP

/-! ### The two gadgets -/

/-- The 2-bit XOR gadget: one bit each. -/
def xorGadget : Gadget := ⟨1, 1, fun x y => xor (x 0) (y 0)⟩

/-- The Index gadget on a `t`-bit pointer and a `2^t`-bit table. -/
def indGadget (t : ℕ) : Gadget :=
  ⟨t, 2 ^ t, fun x y => y (finFunctionFinEquiv (fun j => finTwoEquiv.symm (x j)))⟩

/-- Alice's input alone leaves the output uniform: for every `x`, half of Bob's inputs give `true`. -/
def AliceBalanced (G : Gadget) : Prop :=
  ∀ x : Fin G.a → Bool, 2 * (univ.filter fun y : Fin G.b → Bool => G.g x y = true).card = Fintype.card (Fin G.b → Bool)

/-- Bob's input alone leaves the output uniform: for every `y`, half of Alice's inputs give `true`. -/
def BobBalanced (G : Gadget) : Prop :=
  ∀ y : Fin G.b → Bool, 2 * (univ.filter fun x : Fin G.a → Bool => G.g x y = true).card = Fintype.card (Fin G.a → Bool)

/-- **XOR hides against both parties.** -/
theorem xor_balanced : AliceBalanced xorGadget ∧ BobBalanced xorGadget := by
  unfold AliceBalanced BobBalanced xorGadget
  constructor <;> decide

/-- **Index hides against the pointer holder** (checked at `t = 1`). -/
theorem ind1_aliceBalanced : AliceBalanced (indGadget 1) := by
  unfold AliceBalanced indGadget
  decide

/-- **Index does not hide against the table holder**: the table `0000…` fixes the output, so the output is uniform only
on average over tables (checked at `t = 1`). -/
theorem ind1_not_bobBalanced : ¬ BobBalanced (indGadget 1) := by
  unfold BobBalanced indGadget
  decide

end ProofPhase.Proof.Lifting
