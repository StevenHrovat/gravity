/-
P vs NP, proof systems, Lean part 7: a native reorganization of the cut principle (2026-11-23).
Released under Apache 2.0.

Paper: `docs/pnp/NATIVE-OPTIMIZATION.md`, section 4.
-/

import ProofPhase.Proof.Crossing

/-!
# One middle-line argument instead of two

`Cut.lean` (resolution, measure `mu`) and `Crossing.lean` (every proof system, measure `muL`) each prove the same
argument:
* no step creates assertion;
* so a middle line exists;
* that line sees the boundary.

The two developments are parallel copies: `mu`/`muL`, `exists_middle`/`exists_middleL`,
`mem_of_boundary`/`sensitive_of_boundary`. This file is the native reorganization: one derivation predicate `SDG`
whose lines carry a property `G` ("is a clause of width at most `W`", or nothing), one middle-line theorem `crossG`, and
the two earlier main theorems recovered with **the same statements**:

* `width_ge'` has the statement of `ProofPhase.Proof.width_ge` (resolution width at least the boundary count);
* `cross_any_system'` has the statement of `ProofPhase.Proof.cross_any_system` (every proof system crosses).

Neither uses `Cut.lean`'s measure `mu` or its lemmas. Only the general lemmas of `Crossing.lean` (`muL_le`, `muL_spec`,
`muL_ax`, `muL_inf`, `sensitive_of_boundary`) are used. The resolution-specific half of the argument reduces to one
translation (`WD.toSDG`: a resolution derivation is a derivation whose lines are clauses) and one fact about clauses
(`mem_of_sensitive`: a clause that changes value when `x` flips contains `x`).

**New here:** everything in this file. Existing files are not changed.
-/

namespace ProofPhase.Proof

namespace Native

variable {α V : Type*} [DecidableEq α] [Fintype V] [DecidableEq V] {Ax : V → CNF α}

/-- Derivations whose every line has the property `G`: `SDG Ax G L`. With `G := SD Ax` it is `SD`; with
`G L := L is a clause of at most W literals` it is resolution of width `W`. -/
inductive SDG (Ax : V → CNF α) (G : ((α → Bool) → Prop) → Prop) : ((α → Bool) → Prop) → Prop
  | ax {v : V} {A : Clause α} : A ∈ Ax v → G (fun a => ¬ Falsifies a A) → SDG Ax G fun a => ¬ Falsifies a A
  | inf {P Q R : (α → Bool) → Prop} : SDG Ax G P → SDG Ax G Q → (∀ a, P a → Q a → R a) → G R → SDG Ax G R

variable {G : ((α → Bool) → Prop) → Prop}

omit [DecidableEq α] [Fintype V] [DecidableEq V] in
theorem SDG.good {L : (α → Bool) → Prop} (h : SDG Ax G L) : G L := by
  cases h with
  | ax _ hg => exact hg
  | inf _ _ _ hg => exact hg

omit [DecidableEq α] [DecidableEq V] in
theorem SDG.impliesL_univ {L : (α → Bool) → Prop} (h : SDG Ax G L) : ImpliesL Ax Finset.univ L := by
  induction h with
  | ax hA _ => exact fun a ha => ha _ (Finset.mem_univ _) _ hA
  | inf _ _ hPQR _ ihP ihQ => exact fun a ha => hPQR a (ihP a ha) (ihQ a ha)

omit [DecidableEq α] in
/-- **The one middle-line argument.** -/
theorem exists_middleG {K : ℕ} (hK : 1 ≤ K) {L : (α → Bool) → Prop} (h : SDG Ax G L) (hL : K < muL Ax L) :
    ∃ M, SDG Ax G M ∧ K < 2 * muL Ax M ∧ muL Ax M ≤ K := by
  induction h with
  | ax hA _ =>
    have := muL_ax hA
    omega
  | @inf P Q R hP hQ hPQR _ ihP ihQ =>
    have hsum := muL_inf hP.impliesL_univ hQ.impliesL_univ hPQR
    by_cases h1 : K < muL Ax P
    · exact ihP h1
    by_cases h2 : K < muL Ax Q
    · exact ihQ h2
    rcases le_total (muL Ax Q) (muL Ax P) with hle | hle
    · exact ⟨P, hP, by omega, by omega⟩
    · exact ⟨Q, hQ, by omega, by omega⟩

/-- **The one crossing theorem.** A refutation (a derivation of a line `L₀` true nowhere) whose lines all have the
property `G` contains a line with the property `G` that is sensitive to at least `e` variables. -/
theorem crossG {K e : ℕ} (hK : 1 ≤ K) (hKV : K < Fintype.card V)
    (hsat : ∀ S : Finset V, S ≠ Finset.univ → ¬ ImpliesL Ax S (fun _ => False))
    (hexp : ∀ S : Finset V, K < 2 * S.card → S.card ≤ K → ∃ B : Finset α, e ≤ B.card ∧
      ∀ x ∈ B, ∃ u ∈ S, (∀ a, SatB Ax (flip x a) u ↔ ¬ SatB Ax a u) ∧
        ∀ v ∈ S, v ≠ u → ∀ a, SatB Ax (flip x a) v ↔ SatB Ax a v)
    {L₀ : (α → Bool) → Prop} (hL₀ : ∀ a, ¬ L₀ a) (h : SDG Ax G L₀) :
    ∃ L, G L ∧ ∃ B : Finset α, e ≤ B.card ∧ ∀ x ∈ B, ∃ a, ¬ L a ∧ L (flip x a) := by
  have hroot : K < muL Ax L₀ := by
    obtain ⟨S, hS, hSi⟩ := muL_spec h.impliesL_univ
    have : S = Finset.univ := by
      by_contra hne
      exact hsat S hne fun a ha => hL₀ a (hSi a ha)
    rw [← hS, this, Finset.card_univ]
    exact hKV
  obtain ⟨M, hM, hM1, hM2⟩ := exists_middleG hK h hroot
  obtain ⟨S, hS, hSi⟩ := muL_spec hM.impliesL_univ
  obtain ⟨B, hB, hBx⟩ := hexp S (by rw [hS]; exact hM1) (by rw [hS]; exact hM2)
  refine ⟨M, hM.good, B, hB, fun x hx => ?_⟩
  obtain ⟨u, hu, htog, hinv⟩ := hBx x hx
  exact sensitive_of_boundary hSi (fun S' h' => hS ▸ muL_le h') hu htog hinv

/-- The property "is a clause of at most `W` literals". -/
def ClauseLine (W : ℕ) (L : (α → Bool) → Prop) : Prop := ∃ C : Clause α, C.card ≤ W ∧ L = fun a => ¬ Falsifies a C

omit [DecidableEq V] in
/-- **The resolution translation.** A width-`W` resolution derivation is a derivation whose lines are clauses of
width at most `W`. -/
theorem WD.toSDG {W : ℕ} {C : Clause α} (h : WD (allAx Ax) W C) : SDG Ax (ClauseLine W) fun a => ¬ Falsifies a C := by
  induction h with
  | ax hA hc =>
    obtain ⟨v, -, hAv⟩ := Finset.mem_biUnion.mp hA
    exact SDG.ax hAv ⟨_, hc, rfl⟩
  | res y _ _ _ _ hc ihP ihQ =>
    exact SDG.inf ihP ihQ (fun a hP hQ hF => (falsifies_res hF).elim hP hQ) ⟨_, hc, rfl⟩

omit [Fintype V] [DecidableEq V] in
/-- **A clause that sees `x` names `x`.** -/
theorem mem_of_sensitive {C : Clause α} {x : α} {a : α → Bool} (h1 : ¬ ¬ Falsifies a C)
    (h2 : ¬ Falsifies (flip x a) C) : ∃ b, (x, b) ∈ C := by
  by_contra hx
  push Not at hx
  apply h2
  intro l hl
  have hlx : l.1 ≠ x := fun e => hx l.2 (by rw [← e]; exact hl)
  simp only [flip, Function.update_of_ne hlx]
  exact (not_not.mp h1) l hl

/-- **Same statement as `ProofPhase.Proof.width_ge`**, proved through the one crossing theorem. -/
theorem width_ge' {K e W : ℕ} (hK : 1 ≤ K) (hKV : K < Fintype.card V)
    (hsat : ∀ S : Finset V, S ≠ Finset.univ → ¬ Implies Ax S ∅)
    (hexp : ∀ S : Finset V, K < 2 * S.card → S.card ≤ K → ∃ B : Finset α, e ≤ B.card ∧
      ∀ x ∈ B, ∃ u ∈ S, (∀ a, SatB Ax (flip x a) u ↔ ¬ SatB Ax a u) ∧
        ∀ v ∈ S, v ≠ u → ∀ a, SatB Ax (flip x a) v ↔ SatB Ax a v)
    (h : WD (allAx Ax) W ∅) : e ≤ W := by
  have hsat' : ∀ S : Finset V, S ≠ Finset.univ → ¬ ImpliesL Ax S (fun _ => False) :=
    fun S hS hI => hsat S hS fun a ha _ => hI a ha
  obtain ⟨L, ⟨C, hC, rfl⟩, B, hB, hBx⟩ :=
    crossG (G := ClauseLine W) hK hKV hsat' hexp (fun a h => h (falsifies_empty a)) (WD.toSDG h)
  have hsub : B ⊆ C.image Prod.fst := by
    intro x hx
    obtain ⟨a, h1, h2⟩ := hBx x hx
    obtain ⟨b, hb⟩ := mem_of_sensitive h1 h2
    exact Finset.mem_image.mpr ⟨(x, b), hb, rfl⟩
  calc e ≤ B.card := hB
    _ ≤ (C.image Prod.fst).card := Finset.card_le_card hsub
    _ ≤ C.card := Finset.card_image_le
    _ ≤ W := hC

omit [DecidableEq α] [Fintype V] [DecidableEq V] in
/-- **The all-systems translation.** An `SD` derivation is a derivation whose lines are `SD` lines. -/
theorem SD.toSDG {L : (α → Bool) → Prop} (h : SD Ax L) : SDG Ax (SD Ax) L := by
  induction h with
  | ax hA => exact SDG.ax hA (SD.ax hA)
  | inf hP hQ hPQR ihP ihQ => exact SDG.inf ihP ihQ hPQR (SD.inf hP hQ hPQR)

/-- **Same statement as `ProofPhase.Proof.cross_any_system`**, proved through the one crossing theorem. -/
theorem cross_any_system' {K e : ℕ} (hK : 1 ≤ K) (hKV : K < Fintype.card V)
    (hsat : ∀ S : Finset V, S ≠ Finset.univ → ¬ ImpliesL Ax S (fun _ => False))
    (hexp : ∀ S : Finset V, K < 2 * S.card → S.card ≤ K → ∃ B : Finset α, e ≤ B.card ∧
      ∀ x ∈ B, ∃ u ∈ S, (∀ a, SatB Ax (flip x a) u ↔ ¬ SatB Ax a u) ∧
        ∀ v ∈ S, v ≠ u → ∀ a, SatB Ax (flip x a) v ↔ SatB Ax a v)
    (h : SD Ax (fun _ => False)) :
    ∃ L, SD Ax L ∧ ∃ B : Finset α, e ≤ B.card ∧ ∀ x ∈ B, ∃ a, ¬ L a ∧ L (flip x a) := by
  exact crossG hK hKV hsat hexp (fun _ h => h) (SD.toSDG h)

end Native

end ProofPhase.Proof
