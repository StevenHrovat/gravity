/-
Proof phase, crossover workstream (c9a-crossover): the integer-flux route to a rate (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/RATE.md`.
-/

import ProofPhase.Crossover.Dichotomy

/-!
# A flux-carrying outside forces sheet plaquettes in the box, with an area bound

Setting of `Dichotomy.lean`: a `ℤ/2` cochain `τ` on plaquettes `P` (M1's centre layer), cells `Q` with face sets `inc q`,
a box `R ⊆ P`. The **flux cells** of `R` are the cells where the restriction of `τ` to `R` has nonzero coboundary; for a
closed `τ` they are boundary cells (`boundaryCell_of_cob_restrict`), and the flux is the same seen from outside
(`cob_restrict_eq_cob_restrict_compl`). The **sheet plaquettes in `R`** are the plaquettes of `R` with `τ p ≠ 0`.

* **`exists_sheet_of_flux`** (S): a flux cell has a face in `R` carrying the sheet. Pure counting, no closedness.
* **`exists_sheet_both_sides`** (S): for closed `τ`, a flux cell has a sheet face inside `R` and one outside: the sheet
  crosses the boundary there (it is boundary-attached).
* **`card_fluxCells_le`** (S): if every plaquette is a face of at most `c` cells, then
  `#(flux cells) ≤ c · #(sheet plaquettes in R)` (double counting).
* **`even_card_fluxCells`** (S): if every plaquette is a face of an even number of cells (true on the periodic hypercubic
  lattice: `2(d-2)` cubes per plaquette), the number of flux cells is even.
* **`two_le_card_fluxCells`**, **`two_le_mul_card_sheetIn`** (S): a nonempty flux has at least two flux cells, so
  `2 ≤ c · #(sheet plaquettes in R)`: at least `⌈2/c⌉` sheet plaquettes, for free.
* **`cost_ge_threshold_count`** (S): for nonnegative costs, `ε · #{p ∈ S | ε ≤ cost p} ≤ ∑_{p ∈ S} cost p`: the cost of a
  sheet is at least `ε` times the number of its plaquettes that are not `ε`-near the cut (the quenched form, RATE.md 3).
* **`sheet_cost_ge`** (S): if every sheet plaquette in `R` costs at least `ε ≥ 0` and the flux is nonempty, then
  `2ε ≤ c · (sheet cost in R)`.

**Claim level.** Lean, combinatorial. What it does **not** give (RATE.md 3-4): a rate. The cost bound needs `ε` on the
sheet plaquettes actually present; the cost `β|tr U_p|` has essential infimum `0` (`WellDefined.lean`), so `ε` is not
uniform in the outside, and the counting bound alone gives at least one plaquette's worth of cost, not one per unit of
area spanned.
-/

open Finset

set_option linter.unusedSectionVars false

namespace ProofPhase.Crossover

section Flux

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

/-- The flux cells of the box `R`: cells where the restriction of `τ` to `R` has nonzero coboundary. -/
def fluxCells (inc : Q → Finset P) (τ : P → ZMod 2) (R : Finset P) : Finset Q :=
  univ.filter fun q => cob inc (restrictTo R τ) q ≠ 0

/-- The sheet plaquettes of `τ` in the box `R`. -/
def sheetIn (τ : P → ZMod 2) (R : Finset P) : Finset P := R.filter fun p => τ p ≠ 0

/-- **A flux cell carries a sheet face in the box** (S). -/
theorem exists_sheet_of_flux (inc : Q → Finset P) (τ : P → ZMod 2) (R : Finset P) {q : Q}
    (hq : cob inc (restrictTo R τ) q ≠ 0) : ∃ p ∈ inc q, p ∈ R ∧ τ p ≠ 0 := by
  by_contra h
  apply hq
  unfold cob
  refine Finset.sum_eq_zero fun p hp => ?_
  unfold restrictTo
  split_ifs with hR
  · by_contra hne
    exact h ⟨p, hp, hR, hne⟩
  · rfl

/-- **For a closed layer the sheet crosses the boundary at every flux cell** (S): a sheet face inside and one outside. -/
theorem exists_sheet_both_sides {inc : Q → Finset P} {τ : P → ZMod 2} (h : Closed inc τ) (R : Finset P) {q : Q}
    (hq : cob inc (restrictTo R τ) q ≠ 0) :
    (∃ p ∈ inc q, p ∈ R ∧ τ p ≠ 0) ∧ (∃ p ∈ inc q, p ∉ R ∧ τ p ≠ 0) := by
  refine ⟨exists_sheet_of_flux inc τ R hq, ?_⟩
  rw [cob_restrict_eq_cob_restrict_compl h R q] at hq
  obtain ⟨p, hp, hR, hne⟩ := exists_sheet_of_flux inc τ Rᶜ hq
  exact ⟨p, hp, Finset.mem_compl.1 hR, hne⟩

/-- **Area bound by double counting** (S): `#(flux cells) ≤ c · #(sheet plaquettes in R)` when every plaquette is a face of
at most `c` cells. -/
theorem card_fluxCells_le (inc : Q → Finset P) (τ : P → ZMod 2) (R : Finset P) {c : ℕ}
    (hc : ∀ p, (univ.filter fun q => p ∈ inc q).card ≤ c) :
    (fluxCells inc τ R).card ≤ c * (sheetIn τ R).card := by
  have hsub : fluxCells inc τ R ⊆ (sheetIn τ R).biUnion fun p => univ.filter fun q => p ∈ inc q := by
    intro q hq
    simp only [fluxCells, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨p, hp, hR, hne⟩ := exists_sheet_of_flux inc τ R hq
    simp only [Finset.mem_biUnion, sheetIn, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨p, ⟨hR, hne⟩, hp⟩
  calc (fluxCells inc τ R).card
      ≤ ((sheetIn τ R).biUnion fun p => univ.filter fun q => p ∈ inc q).card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ sheetIn τ R, (univ.filter fun q => p ∈ inc q).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ sheetIn τ R, c := Finset.sum_le_sum fun p _ => hc p
    _ = c * (sheetIn τ R).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **The number of flux cells is even** (S), when every plaquette is a face of an even number of cells. -/
theorem even_card_fluxCells (inc : Q → Finset P) (hev : ∀ p, Even ((univ.filter fun q => p ∈ inc q).card))
    (τ : P → ZMod 2) (R : Finset P) : Even (fluxCells inc τ R).card := by
  have h0 := sum_cob_restrict_eq_zero inc hev τ R
  have hsplit : ∑ q ∈ fluxCells inc τ R, cob inc (restrictTo R τ) q = ∑ q, cob inc (restrictTo R τ) q := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro q _ hq
    simp only [fluxCells, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hq
    exact hq
  have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  have hone : ∀ q ∈ fluxCells inc τ R, cob inc (restrictTo R τ) q = 1 := by
    intro q hq
    simp only [fluxCells, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    exact key _ hq
  rw [← hsplit, Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one] at h0
  exact ZMod.natCast_eq_zero_iff_even.1 h0

/-- **A nonempty flux has at least two flux cells** (S). -/
theorem two_le_card_fluxCells (inc : Q → Finset P) (hev : ∀ p, Even ((univ.filter fun q => p ∈ inc q).card))
    (τ : P → ZMod 2) (R : Finset P) (hne : (fluxCells inc τ R).Nonempty) : 2 ≤ (fluxCells inc τ R).card := by
  obtain ⟨k, hk⟩ := even_card_fluxCells inc hev τ R
  have := hne.card_pos
  omega

/-- **Minimal area for free** (S): a nonempty flux forces `2 ≤ c · #(sheet plaquettes in R)`. -/
theorem two_le_mul_card_sheetIn (inc : Q → Finset P) (hev : ∀ p, Even ((univ.filter fun q => p ∈ inc q).card))
    (τ : P → ZMod 2) (R : Finset P) {c : ℕ} (hc : ∀ p, (univ.filter fun q => p ∈ inc q).card ≤ c)
    (hne : (fluxCells inc τ R).Nonempty) : 2 ≤ c * (sheetIn τ R).card :=
  (two_le_card_fluxCells inc hev τ R hne).trans (card_fluxCells_le inc τ R hc)

end Flux

section Cost

variable {P : Type*}

/-- **Quenched cost lower bound** (S): for nonnegative costs, the cost of `S` is at least `ε` times the number of its
plaquettes that cost at least `ε`. -/
theorem cost_ge_threshold_count (cost : P → ℝ) (hc : ∀ p, 0 ≤ cost p) (S : Finset P) (ε : ℝ)
    [DecidablePred fun p => ε ≤ cost p] :
    ε * (S.filter fun p => ε ≤ cost p).card ≤ ∑ p ∈ S, cost p := by
  calc ε * (S.filter fun p => ε ≤ cost p).card = ∑ _p ∈ S.filter (fun p => ε ≤ cost p), ε := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ p ∈ S.filter (fun p => ε ≤ cost p), cost p := Finset.sum_le_sum fun p hp => (Finset.mem_filter.1 hp).2
    _ ≤ ∑ p ∈ S, cost p := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p _ _ => hc p

end Cost

section Combined

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

/-- **Cost of a forced sheet when every sheet plaquette in the box is `ε`-costly** (S): `2ε ≤ c · (sheet cost in R)`. -/
theorem sheet_cost_ge (inc : Q → Finset P) (hev : ∀ p, Even ((univ.filter fun q => p ∈ inc q).card))
    (τ : P → ZMod 2) (R : Finset P) {c : ℕ} (hc : ∀ p, (univ.filter fun q => p ∈ inc q).card ≤ c)
    (hne : (fluxCells inc τ R).Nonempty) (cost : P → ℝ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ p ∈ sheetIn τ R, ε ≤ cost p) :
    ε * 2 ≤ c * ∑ p ∈ sheetIn τ R, cost p := by
  have h2 : (2 : ℝ) ≤ c * (sheetIn τ R).card := by exact_mod_cast two_le_mul_card_sheetIn inc hev τ R hc hne
  have hS : ε * (sheetIn τ R).card ≤ ∑ p ∈ sheetIn τ R, cost p := by
    calc ε * (sheetIn τ R).card = ∑ _p ∈ sheetIn τ R, ε := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ p ∈ sheetIn τ R, cost p := Finset.sum_le_sum hε
  calc ε * 2 ≤ ε * (c * (sheetIn τ R).card) := mul_le_mul_of_nonneg_left h2 hε0
    _ = c * (ε * (sheetIn τ R).card) := by ring
    _ ≤ c * ∑ p ∈ sheetIn τ R, cost p := mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg c)

end Combined

end ProofPhase.Crossover
