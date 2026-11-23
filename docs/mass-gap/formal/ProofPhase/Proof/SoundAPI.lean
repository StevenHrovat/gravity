/-
NP vs coNP, sound APIs: the extraction interface of a constant-gadget lifting theorem (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/NP-SOUND-APIS.md`, sections 3 and 4.
-/

import ProofPhase.Proof.LiftingNP

/-!
# The interface of `LiftCPConst`: what a constant-gadget lifting proof has to deliver

Every known lifting proof (Garg, Goos, Kamath, Sokolov; Lovett et al.; de Rezende, Fleming, Janett, Nordstrom) has the same
shape: from a refutation `P` of `F ∘ g`, build for every line a set of narrow clauses of `F`, such that the leaves are
weakenings of clauses of `F`, the root contains the empty clause, and each step of the refutation is simulated inside
resolution of bounded width. The gadget is needed only to build these sets, and the *size of the refutation* (through a
union bound over its lines) is needed only for this construction to succeed.

This file makes that interface exact, as a Lean proposition next to `LiftCPConst`:

* `Labeling G F w P Γ` (a structure): the labels `Γ` along `P` are narrow (width at most `w`), leaves are weakenings of
  `F`-clauses derivable in width `w`, every step of `P` is simulated by a width-`w` resolution derivation from the
  labels of its premises, and the root carries the empty clause.
* `labeling_refutes`: **a labeling gives a width-`w` resolution refutation of `F`.** (Induction over the cutting-planes
  derivation; the replacement of axioms by derivations is `WD.trans`.)
* `ExtractAPI G c`: **the sound API.** Every cutting-planes refutation of `F ∘ G` of size below `exp (c (w + 1))` admits
  such a labeling at width `w`.
* `liftCPConst_iff_extract`: **`ExtractAPI G c` and `LiftCPConst G c` are equivalent.** The first is the second in the
  form in which every lifting proof proves it; neither is easier than the other, and the Lean proof shows that nothing
  is lost by working with the labeling form. What the route has to supply is the labeling, with a bounded error, for a
  gadget of constant size: that is where known proofs need a gadget that grows with `n`.
* `liftCPConst_mono`, `liftCPConst_zero`: `c ↦ LiftCPConst G c` is downward closed, and `c = 0` is the trivial case
  (a refutation has at least one line). So the content of `LiftCPConst` is `c > 0`.

**What is not proved.** `ExtractAPI G c` for any constant gadget `G` and `c > 0`. Nothing here is a lower bound.

**New here:** everything in this file.
-/

namespace ProofPhase.Proof.Lifting

open Finset ProofPhase.Proof ProofPhase.Proof.Edge ProofPhase.Unified

section Basic

variable {α : Type*} [DecidableEq α] [Fintype α] {G : Gadget}

/-- **Every line of a size-counting derivation is in the line set.** -/
theorem CPR.mem_P {V : Finset (LV α G)} {Ax : Set (CPLine (LV α G))} {P : Finset (CPLine (LV α G))}
    {L : CPLine (LV α G)} (h : CPR V Ax P L) : L ∈ P := by
  cases h <;> assumption

/-- **A refutation has at least one line.** -/
theorem CPRefutes.card_pos {F : CNF (LV α G)} {P : Finset (CPLine (LV α G))} (h : CPRefutes F P) :
    0 < P.card :=
  Finset.card_pos.2 ⟨_, CPR.mem_P h⟩

end Basic

/-! ### 1. `LiftCPConst` is downward closed in `c`, and `c = 0` is trivial -/

/-- **A smaller constant is easier.** -/
theorem liftCPConst_mono {G : Gadget} {c c' : ℝ} (hc : c' ≤ c) (h : LiftCPConst G c) : LiftCPConst G c' := by
  intro α _ _ F w hF hw P hP
  refine le_trans (Real.exp_le_exp.2 ?_) (h α F w hF hw P hP)
  exact mul_le_mul_of_nonneg_right hc (by positivity)

/-- **`c = 0` is trivial**: a refutation has at least one line. The content of `LiftCPConst` is `c > 0`. -/
theorem liftCPConst_zero (G : Gadget) : LiftCPConst G 0 := by
  intro α _ _ F w hF hw P hP
  rw [zero_mul, Real.exp_zero]
  exact_mod_cast hP.card_pos

/-! ### 2. The labeling interface -/

section Labeling

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- **A narrow clause labeling of a refutation.** `Γ L` is the set of clauses of `F` attached to the line `L`:
all of width at most `w`; at an axiom line each clause contains a clause derivable from `F` in width `w` (a weakening of
an axiom of `F`, by `comp_falsified_iff`); at an addition, scaling or rounding step inside `P` each clause contains a
clause derivable in width `w` from the labels of the premises; the root `0 ≥ 1` carries the empty clause. -/
structure Labeling (G : Gadget) (F : CNF α) (w : ℕ) (P : Finset (CPLine (LV α G)))
    (Γ : CPLine (LV α G) → Finset (Clause α)) : Prop where
  width : ∀ L ∈ P, ∀ C ∈ Γ L, C.card ≤ w
  leaf : ∀ L ∈ P, L ∈ cnfAx (comp G F) → ∀ C ∈ Γ L, ∃ C' ⊆ C, WD F w C'
  add : ∀ L₁ L₂, L₁ ∈ P → L₂ ∈ P → addL L₁ L₂ ∈ P →
    ∀ C ∈ Γ (addL L₁ L₂), ∃ C' ⊆ C, WD (Γ L₁ ∪ Γ L₂) w C'
  scale : ∀ L (c : ℕ), 0 < c → L ∈ P → scaleL c L ∈ P → ∀ C ∈ Γ (scaleL c L), ∃ C' ⊆ C, WD (Γ L) w C'
  round : ∀ L (d : ℕ), 0 < d → L ∈ P → roundL d L ∈ P → ∀ C ∈ Γ (roundL d L), ∃ C' ⊆ C, WD (Γ L) w C'
  root : (∅ : Clause α) ∈ Γ ((fun _ => 0), 1)

variable {G : Gadget} {F : CNF α} {w : ℕ} {P : Finset (CPLine (LV α G))} {Γ : CPLine (LV α G) → Finset (Clause α)}

/-- **Soundness of a labeling, line by line**: along a derivation inside `P`, every label contains a clause derivable
from `F` in width `w`. (Induction on the cutting-planes derivation; axioms are replaced by derivations with `WD.trans`.) -/
theorem Labeling.derivable (hΓ : Labeling G F w P Γ) {V : Finset (LV α G)} {L : CPLine (LV α G)}
    (h : CPR V (cnfAx (comp G F)) P L) : ∀ C ∈ Γ L, ∃ C' ⊆ C, WD F w C' := by
  induction h with
  | ax hA hP => exact hΓ.leaf _ hP hA
  | add h₁ h₂ hP ih₁ ih₂ =>
    intro C hC
    obtain ⟨C', hC'C, hC'⟩ := hΓ.add _ _ h₁.mem_P h₂.mem_P hP C hC
    obtain ⟨C'', hC''C', hC''⟩ := WD.trans (F := F) (G := Γ _ ∪ Γ _) (W := w) (fun B hB => by
      rcases Finset.mem_union.1 hB with hB | hB
      · exact ih₁ B hB
      · exact ih₂ B hB) hC'
    exact ⟨C'', hC''C'.trans hC'C, hC''⟩
  | scale c hc h hP ih =>
    intro C hC
    obtain ⟨C', hC'C, hC'⟩ := hΓ.scale _ c hc h.mem_P hP C hC
    obtain ⟨C'', hC''C', hC''⟩ := WD.trans (F := F) (G := Γ _) (W := w) ih hC'
    exact ⟨C'', hC''C'.trans hC'C, hC''⟩
  | round d hd hdiv h hP ih =>
    intro C hC
    obtain ⟨C', hC'C, hC'⟩ := hΓ.round _ d hd h.mem_P hP C hC
    obtain ⟨C'', hC''C', hC''⟩ := WD.trans (F := F) (G := Γ _) (W := w) ih hC'
    exact ⟨C'', hC''C'.trans hC'C, hC''⟩

/-- **A labeling gives a width-`w` resolution refutation of `F`.** The lifting step of every known proof, in Lean. -/
theorem labeling_refutes (hΓ : Labeling G F w P Γ) (hP : CPRefutes (comp G F) P) : WD F w ∅ := by
  obtain ⟨C', hC', hWD⟩ := hΓ.derivable hP _ hΓ.root
  rwa [Finset.subset_empty.1 hC'] at hWD

end Labeling

/-! ### 3. The sound API, and its equivalence with `LiftCPConst` -/

/-- **`ExtractAPI G c`: the extraction form of a constant-gadget lifting theorem.** Every cutting-planes refutation `P`
of `F ∘ G` with fewer than `exp (c (w + 1))` lines admits a narrow clause labeling at width `w`. This is the interface
of the route: a proof must construct `Γ` from `P` using only that `G` hides (and, in the known proofs, a union bound over
the lines of `P`, which is where the size bound is spent). **Open for every constant-size gadget.** -/
def ExtractAPI (G : Gadget) (c : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (F : CNF α) (w : ℕ), (∀ D ∈ F, D.Nonempty) →
    ∀ P : Finset (CPLine (LV α G)), CPRefutes (comp G F) P → (P.card : ℝ) < Real.exp (c * (w + 1)) →
      ∃ Γ : CPLine (LV α G) → Finset (Clause α), Labeling G F w P Γ

/-- **The labeling form implies the size form.** If a small refutation always carries a labeling, then a formula
without a width-`w` refutation has only large refutations. -/
theorem extract_to_lift {G : Gadget} {c : ℝ} (h : ExtractAPI G c) : LiftCPConst G c := by
  intro α _ _ F w hF hw P hP
  by_contra hlt
  have hlt := not_le.1 hlt
  obtain ⟨Γ, hΓ⟩ := h α F w hF P hP hlt
  exact hw (labeling_refutes hΓ hP)

/-- **The size form implies the labeling form.** (The labeling is trivial once `F` has a width-`w` refutation: label every
line with the empty clause.) So the interface loses nothing. -/
theorem lift_to_extract {G : Gadget} {c : ℝ} (h : LiftCPConst G c) : ExtractAPI G c := by
  intro α _ _ F w hF P hP hlt
  by_cases hw : WD F w ∅
  · refine ⟨fun _ => {∅}, ?_⟩
    have h0 : WD ({∅} : CNF α) w ∅ := WD.ax (Finset.mem_singleton_self _) (by simp)
    have h1 : WD (({∅} : CNF α) ∪ {∅}) w ∅ := WD.ax (by simp) (by simp)
    exact
      { width := fun L _ C hC => by rw [Finset.mem_singleton.1 hC]; simp
        leaf := fun L _ _ C hC => ⟨∅, by rw [Finset.mem_singleton.1 hC], hw⟩
        add := fun L₁ L₂ _ _ _ C hC => ⟨∅, by rw [Finset.mem_singleton.1 hC], h1⟩
        scale := fun L c _ _ _ C hC => ⟨∅, by rw [Finset.mem_singleton.1 hC], h0⟩
        round := fun L d _ _ _ C hC => ⟨∅, by rw [Finset.mem_singleton.1 hC], h0⟩
        root := Finset.mem_singleton_self _ }
  · exact absurd (h α F w hF hw P hP) (not_le.2 hlt)

/-- **`LiftCPConst` and the extraction interface are the same statement.** -/
theorem liftCPConst_iff_extract (G : Gadget) (c : ℝ) : LiftCPConst G c ↔ ExtractAPI G c :=
  ⟨lift_to_extract, extract_to_lift⟩

/-- **The extraction form of the bound**: under `LiftCPConst`, a refutation of `F ∘ G` with fewer than `exp (c (w + 1))`
lines gives a resolution refutation of `F` of width `w`. (The contrapositive of the hypothesis; this is the form used in
the width-to-size reading of the ledger.) -/
theorem width_of_small_refutation {G : Gadget} {c : ℝ} (h : LiftCPConst G c) {α : Type} [Fintype α] [DecidableEq α]
    {F : CNF α} (hF : ∀ D ∈ F, D.Nonempty) {w : ℕ} {P : Finset (CPLine (LV α G))}
    (hP : CPRefutes (comp G F) P) (hlt : (P.card : ℝ) < Real.exp (c * (w + 1))) : WD F w ∅ := by
  obtain ⟨Γ, hΓ⟩ := lift_to_extract h α F w hF P hP hlt
  exact labeling_refutes hΓ hP

end ProofPhase.Proof.Lifting
