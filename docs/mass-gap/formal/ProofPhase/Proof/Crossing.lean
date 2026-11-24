/-
P vs NP, proof systems, Lean part 5: the worst-case dichotomy transferred to refutations (2026-11-23).
Released under Apache 2.0.

Paper: `docs/pnp/DICHOTOMY-TRANSFER.md`.
-/

import ProofPhase.Proof.Tseitin

/-!
# Crossing flux in refutations: conserved, unscreenable, and universal across proof systems

The Yang-Mills dichotomy (`c9a-crossover/DICHOTOMY.md`) splits every obstruction into local pieces behind a collar
(attenuated), conserved crossing flux (not screenable), and a residue inside one region (a percolation question). This
file proves the exact parts of the same split for refutations.

**1. Conservation (Gauss's law mod 2).** For a Tseitin system (every edge at exactly two vertices):
* `gauss`: for every vertex set `S` and every assignment, the sum over `S` of the parities at the vertices equals the
  parity of the true boundary edges of `S` (mod 2). Interior edges are counted twice and drop out.
* `flux_fixed`: if the constraints of `S` hold, the boundary parity is the total charge of `S`, **whatever the
  interior does**: the crossing flux is fixed by what is inside and cannot be screened.
* `unsat_of_odd`: odd total charge makes the whole system unsatisfiable (Tseitin's formulas are contradictions).
* `summary`: the constraints of `S` imply the single line "boundary parity = charge of `S`": a cheap name for the
  crossing flux (an exclusive or of the boundary edges).

**2. The crossing step holds in every proof system.** `SD Ax L`: the line `L` (any property of assignments) is
derivable by sound rules with at most two premises: every Frege, extended Frege, cutting-planes or resolution proof
is such a derivation. With the semantic measure `muL` (how many blocks force the line):
* `exists_middleL`: every refutation contains a line asserting a region of middle size;
* `sensitive_of_boundary`: such a line, for a smallest region, changes value when any boundary variable flips;
* `cross_any_system`: under an expansion count `e`, **every refutation in every such system contains a line sensitive
  to at least `e` variables**; `Tseitin.cross_any_system`: the same for Tseitin formulas.

So the crossing is universal; its cost is not. A resolution line sensitive to `e` variables has width `e` (`Cut.lean`).
A Frege line can be sensitive to `e` variables at size about `e`, and `summary` shows that one exclusive or carries the
whole crossing flux of a Tseitin region.

**3. Expansion gives crossing variables** (`unique_neighbors`): for constraints with variable sets `I v`, the variables
of `S` that occur in exactly one constraint of `S` number at least `2 |N(S)| - Σ_{v ∈ S} |I v|`. Vertex expansion of
the constraint hypergraph gives the toggle variables that the cut principle needs.

**New here:** everything in this file.
-/

namespace ProofPhase.Proof

/-! ### 1. Conservation: Gauss's law mod 2 for Tseitin systems -/

namespace Tseitin

variable {E V : Type*} [DecidableEq E] [Fintype E] [Fintype V] [DecidableEq V] {I : V → Finset E}

/-- The edges at exactly one vertex of `S`. -/
def bd1 (I : V → Finset E) (S : Finset V) : Finset E :=
  Finset.univ.filter fun x => (S.filter fun v => x ∈ I v).card = 1

theorem bd1_eq_boundary (S : Finset V) : bd1 I S = boundary I S := by
  ext x
  simp only [bd1, boundary, Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_eq_one]
  constructor
  · rintro ⟨u, hu⟩
    have hu' : u ∈ S.filter (fun v => x ∈ I v) := hu ▸ Finset.mem_singleton_self u
    rw [Finset.mem_filter] at hu'
    refine ⟨u, hu'.1, hu'.2, fun v hv hvu hxv => hvu ?_⟩
    have : v ∈ S.filter (fun v => x ∈ I v) := Finset.mem_filter.mpr ⟨hv, hxv⟩
    rw [hu] at this
    exact Finset.mem_singleton.mp this
  · rintro ⟨u, hu, hxu, hrest⟩
    refine ⟨u, ?_⟩
    ext v
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hv, hxv⟩
      by_contra h
      exact hrest v hv h hxv
    · rintro rfl
      exact ⟨hu, hxu⟩

theorem zmod2_natCast (n : ℕ) : (n : ZMod 2) = if n % 2 = 1 then 1 else 0 := by
  rw [← ZMod.natCast_mod]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem zmod2_small {k : ℕ} (hk : k ≤ 2) : (k : ZMod 2) = if k = 1 then 1 else 0 := by
  interval_cases k <;> decide

omit [DecidableEq V] in
/-- **Gauss's law mod 2.** If every edge lies at exactly two vertices, then for every vertex set `S` and every
assignment, the sum over `S` of the numbers of true edges at each vertex equals, mod 2, the number of true edges on the
boundary of `S`. -/
theorem gauss (hI2 : ∀ e, (Finset.univ.filter fun v => e ∈ I v).card = 2) (S : Finset V) (a : E → Bool) :
    (∑ v ∈ S, (((I v).filter fun e => a e = true).card : ZMod 2)) =
      (((bd1 I S).filter fun e => a e = true).card : ZMod 2) := by
  have hcount : ∑ v ∈ S, ((I v).filter fun e => a e = true).card =
      ∑ e ∈ Finset.univ.filter (fun e => a e = true), (S.filter fun v => e ∈ I v).card := by
    calc ∑ v ∈ S, ((I v).filter fun e => a e = true).card
        = ∑ v ∈ S, ((Finset.univ.filter fun e => a e = true).bipartiteAbove (fun v e => e ∈ I v) v).card :=
          Finset.sum_congr rfl fun v _ => by
            congr 1
            ext e
            simp [Finset.bipartiteAbove, and_comm]
      _ = _ := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
  rw [← Nat.cast_sum, hcount, Nat.cast_sum]
  have hsmall : ∀ e ∈ Finset.univ.filter (fun e => a e = true),
      ((S.filter fun v => e ∈ I v).card : ZMod 2) = if (S.filter fun v => e ∈ I v).card = 1 then 1 else 0 := by
    intro e _
    refine zmod2_small ?_
    rw [← hI2 e]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))
  rw [Finset.sum_congr rfl hsmall, Finset.sum_boole]
  congr 2
  ext e
  simp [bd1, and_comm]

omit [DecidableEq E] [Fintype E] [DecidableEq V] [Fintype V] in
theorem odd_cast (a : E → Bool) (v : V) :
    ((((I v).filter fun e => a e = true).card : ℕ) : ZMod 2) = if odd I a v = true then 1 else 0 := by
  rw [zmod2_natCast, odd]
  by_cases h : ((I v).filter fun e => a e = true).card % 2 = 1 <;> simp [h]

omit [DecidableEq V] in
/-- **The crossing flux is fixed by what is inside.** If the constraints of `S` hold, the parity of the true boundary
edges is the total charge of `S`, whatever the interior does. -/
theorem flux_fixed (hI2 : ∀ e, (Finset.univ.filter fun v => e ∈ I v).card = 2) {S : Finset V} {a : E → Bool}
    {c : V → Bool} (ha : ∀ v ∈ S, odd I a v = c v) :
    (((bd1 I S).filter fun e => a e = true).card : ZMod 2) = ∑ v ∈ S, (if c v = true then 1 else 0 : ZMod 2) := by
  rw [← gauss hI2]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [odd_cast, ha v hv]

omit [DecidableEq V] in
theorem bd1_univ (hI2 : ∀ e, (Finset.univ.filter fun v => e ∈ I v).card = 2) : bd1 I Finset.univ = ∅ := by
  ext x
  simp [bd1, hI2 x]

omit [DecidableEq V] in
/-- **Tseitin's contradiction.** With odd total charge no assignment satisfies every vertex. -/
theorem unsat_of_odd (hI2 : ∀ e, (Finset.univ.filter fun v => e ∈ I v).card = 2) {c : V → Bool}
    (hc : ∑ v, (if c v = true then 1 else 0 : ZMod 2) = 1) (a : E → Bool) : ∃ v, odd I a v ≠ c v := by
  by_contra h
  push Not at h
  have := flux_fixed hI2 (S := Finset.univ) (a := a) (c := c) (fun v _ => h v)
  rw [bd1_univ hI2, Finset.filter_empty, Finset.card_empty, Nat.cast_zero, hc] at this
  exact zero_ne_one this

end Tseitin

/-! ### 2. The crossing step in every proof system -/

section Semantic

variable {α V : Type*} [DecidableEq α] [Fintype V] [DecidableEq V] (Ax : V → CNF α)

/-- `SD Ax L`: the line `L` (any property of assignments) is derivable from the blocks by sound rules with at most two
premises. Every Frege, extended Frege, cutting-planes or resolution derivation is one (read each line as the set of
assignments satisfying it). -/
inductive SD : ((α → Bool) → Prop) → Prop
  | ax {v : V} {A : Clause α} : A ∈ Ax v → SD fun a => ¬ Falsifies a A
  | inf {P Q R : (α → Bool) → Prop} : SD P → SD Q → (∀ a, P a → Q a → R a) → SD R

/-- The blocks in `S` force the line `L`. -/
def ImpliesL (S : Finset V) (L : (α → Bool) → Prop) : Prop := ∀ a : α → Bool, (∀ v ∈ S, SatB Ax a v) → L a

/-- The measure of a line: the least number of blocks that force it. -/
noncomputable def muL (L : (α → Bool) → Prop) : ℕ := sInf {n | ∃ S : Finset V, S.card = n ∧ ImpliesL Ax S L}

variable {Ax}

omit [DecidableEq α] [DecidableEq V] in
theorem SD.impliesL_univ {L : (α → Bool) → Prop} (h : SD Ax L) : ImpliesL Ax Finset.univ L := by
  induction h with
  | ax hA => exact fun a ha => ha _ (Finset.mem_univ _) _ hA
  | inf _ _ hPQR ihP ihQ => exact fun a ha => hPQR a (ihP a ha) (ihQ a ha)

omit [DecidableEq α] [Fintype V] [DecidableEq V] in
theorem muL_le {S : Finset V} {L : (α → Bool) → Prop} (h : ImpliesL Ax S L) : muL Ax L ≤ S.card :=
  Nat.sInf_le ⟨S, rfl, h⟩

omit [DecidableEq α] [DecidableEq V] in
theorem muL_spec {L : (α → Bool) → Prop} (h : ImpliesL Ax Finset.univ L) :
    ∃ S : Finset V, S.card = muL Ax L ∧ ImpliesL Ax S L :=
  Nat.sInf_mem (s := {n | ∃ S : Finset V, S.card = n ∧ ImpliesL Ax S L}) ⟨_, _, rfl, h⟩

omit [DecidableEq α] [Fintype V] [DecidableEq V] in
theorem muL_ax {v : V} {A : Clause α} (hA : A ∈ Ax v) : muL Ax (fun a => ¬ Falsifies a A) ≤ 1 := by
  refine (muL_le (S := {v}) ?_).trans (by simp)
  intro a ha
  exact ha v (Finset.mem_singleton_self v) A hA

omit [DecidableEq α] in
/-- **No inference creates assertion.** -/
theorem muL_inf {P Q R : (α → Bool) → Prop} (hP : ImpliesL Ax Finset.univ P) (hQ : ImpliesL Ax Finset.univ Q)
    (hPQR : ∀ a, P a → Q a → R a) : muL Ax R ≤ muL Ax P + muL Ax Q := by
  obtain ⟨S₁, h1, hS₁⟩ := muL_spec hP
  obtain ⟨S₂, h2, hS₂⟩ := muL_spec hQ
  have : ImpliesL Ax (S₁ ∪ S₂) R := fun a ha =>
    hPQR a (hS₁ a fun v hv => ha v (Finset.mem_union_left _ hv)) (hS₂ a fun v hv => ha v (Finset.mem_union_right _ hv))
  exact (muL_le this).trans ((Finset.card_union_le _ _).trans (by omega))

omit [DecidableEq α] in
/-- **A middle line exists in every refutation, in every proof system with at most two premises per rule.** -/
theorem exists_middleL {K : ℕ} (hK : 1 ≤ K) {L : (α → Bool) → Prop} (h : SD Ax L) (hL : K < muL Ax L) :
    ∃ M, SD Ax M ∧ K < 2 * muL Ax M ∧ muL Ax M ≤ K := by
  induction h with
  | ax hA =>
    have := muL_ax hA
    omega
  | @inf P Q R hP hQ hPQR ihP ihQ =>
    have hsum := muL_inf hP.impliesL_univ hQ.impliesL_univ hPQR
    by_cases h1 : K < muL Ax P
    · exact ihP h1
    by_cases h2 : K < muL Ax Q
    · exact ihQ h2
    rcases le_total (muL Ax Q) (muL Ax P) with hle | hle
    · exact ⟨P, hP, by omega, by omega⟩
    · exact ⟨Q, hQ, by omega, by omega⟩

omit [Fintype V] in
/-- **A crossing line is sensitive to every boundary variable (the form the proof uses).** If `S` is a smallest region
forcing `L` and flipping `x` makes the block at `u ∈ S` true wherever it is false, while the other blocks of `S` do not see
`x`, then flipping `x` changes `L` somewhere. For a clause `u` containing `x` the first hypothesis always holds: a falsified
clause has every literal false, and flipping `x` makes its literal true. -/
theorem sensitive_of_boundary_of_falsify {S : Finset V} {L : (α → Bool) → Prop} (hS : ImpliesL Ax S L)
    (hmin : ∀ S' : Finset V, ImpliesL Ax S' L → S.card ≤ S'.card) {x : α} {u : V} (hu : u ∈ S)
    (hfix : ∀ a, ¬ SatB Ax a u → SatB Ax (flip x a) u)
    (hinv : ∀ v ∈ S, v ≠ u → ∀ a, SatB Ax (flip x a) v ↔ SatB Ax a v) : ∃ a, ¬ L a ∧ L (flip x a) := by
  have hnot : ¬ ImpliesL Ax (S.erase u) L := fun h => by
    have h1 := hmin _ h
    rw [Finset.card_erase_of_mem hu] at h1
    have h2 := Finset.card_pos.mpr ⟨u, hu⟩
    omega
  simp only [ImpliesL, not_forall] at hnot
  obtain ⟨a, ha, hLa⟩ := hnot
  have hau : ¬ SatB Ax a u := fun hsu => hLa (hS a fun v hv => by
    by_cases hvu : v = u
    · exact hvu ▸ hsu
    · exact ha v (Finset.mem_erase.mpr ⟨hvu, hv⟩))
  refine ⟨a, hLa, hS (flip x a) fun v hv => ?_⟩
  by_cases hvu : v = u
  · rw [hvu]; exact hfix a hau
  · exact (hinv v hv hvu a).mpr (ha v (Finset.mem_erase.mpr ⟨hvu, hv⟩))

omit [Fintype V] in
/-- **A crossing line is sensitive to every boundary variable.** If `S` is a smallest region forcing `L` and `x`
toggles the block at `u ∈ S` while the other blocks of `S` do not see it, then flipping `x` changes `L` somewhere.
(Only one direction of the toggle is used: `sensitive_of_boundary_of_falsify`.) -/
theorem sensitive_of_boundary {S : Finset V} {L : (α → Bool) → Prop} (hS : ImpliesL Ax S L)
    (hmin : ∀ S' : Finset V, ImpliesL Ax S' L → S.card ≤ S'.card) {x : α} {u : V} (hu : u ∈ S)
    (htog : ∀ a, SatB Ax (flip x a) u ↔ ¬ SatB Ax a u)
    (hinv : ∀ v ∈ S, v ≠ u → ∀ a, SatB Ax (flip x a) v ↔ SatB Ax a v) : ∃ a, ¬ L a ∧ L (flip x a) :=
  sensitive_of_boundary_of_falsify hS hmin hu (fun a h => (htog a).mpr h) hinv

/-- **The crossing is universal, in the form the proof uses.** Every refutation, in every sound proof system with at
most two premises per rule, contains a line that is sensitive to at least `e` variables, when every middle-sized region has
at least `e` boundary variables (each makes its one block of the region true wherever that block is false, and is not seen by
the region's other blocks) and every proper sub-system is satisfiable. For clause blocks the first condition holds for every
variable the clause contains, so this covers CNF formulas whose clause-variable graph expands. -/
theorem cross_any_system_of_falsify {K e : ℕ} (hK : 1 ≤ K) (hKV : K < Fintype.card V)
    (hsat : ∀ S : Finset V, S ≠ Finset.univ → ¬ ImpliesL Ax S (fun _ => False))
    (hexp : ∀ S : Finset V, K < 2 * S.card → S.card ≤ K → ∃ B : Finset α, e ≤ B.card ∧
      ∀ x ∈ B, ∃ u ∈ S, (∀ a, ¬ SatB Ax a u → SatB Ax (flip x a) u) ∧
        ∀ v ∈ S, v ≠ u → ∀ a, SatB Ax (flip x a) v ↔ SatB Ax a v)
    (h : SD Ax (fun _ => False)) :
    ∃ L, SD Ax L ∧ ∃ B : Finset α, e ≤ B.card ∧ ∀ x ∈ B, ∃ a, ¬ L a ∧ L (flip x a) := by
  have hroot : K < muL Ax (fun _ => False) := by
    obtain ⟨S, hS, hSi⟩ := muL_spec h.impliesL_univ
    have : S = Finset.univ := by
      by_contra hne
      exact hsat S hne hSi
    rw [← hS, this, Finset.card_univ]
    exact hKV
  obtain ⟨M, hM, hM1, hM2⟩ := exists_middleL hK h hroot
  obtain ⟨S, hS, hSi⟩ := muL_spec hM.impliesL_univ
  obtain ⟨B, hB, hBx⟩ := hexp S (by rw [hS]; exact hM1) (by rw [hS]; exact hM2)
  refine ⟨M, hM, B, hB, fun x hx => ?_⟩
  obtain ⟨u, hu, hfix, hinv⟩ := hBx x hx
  exact sensitive_of_boundary_of_falsify hSi (fun S' h' => hS ▸ muL_le h') hu hfix hinv

/-- **The crossing is universal.** Every refutation, in every sound proof system with at most two premises per rule,
contains a line that is sensitive to at least `e` variables, when every middle-sized region has at least `e` boundary
variables and every proper sub-system is satisfiable. The toggle hypothesis here is the parity-type form (it holds for
Tseitin blocks); `cross_any_system_of_falsify` needs only its one direction and covers clause blocks. -/
theorem cross_any_system {K e : ℕ} (hK : 1 ≤ K) (hKV : K < Fintype.card V)
    (hsat : ∀ S : Finset V, S ≠ Finset.univ → ¬ ImpliesL Ax S (fun _ => False))
    (hexp : ∀ S : Finset V, K < 2 * S.card → S.card ≤ K → ∃ B : Finset α, e ≤ B.card ∧
      ∀ x ∈ B, ∃ u ∈ S, (∀ a, SatB Ax (flip x a) u ↔ ¬ SatB Ax a u) ∧
        ∀ v ∈ S, v ≠ u → ∀ a, SatB Ax (flip x a) v ↔ SatB Ax a v)
    (h : SD Ax (fun _ => False)) :
    ∃ L, SD Ax L ∧ ∃ B : Finset α, e ≤ B.card ∧ ∀ x ∈ B, ∃ a, ¬ L a ∧ L (flip x a) := by
  refine cross_any_system_of_falsify hK hKV hsat (fun S h1 h2 => ?_) h
  obtain ⟨B, hB, hBx⟩ := hexp S h1 h2
  refine ⟨B, hB, fun x hx => ?_⟩
  obtain ⟨u, hu, htog, hinv⟩ := hBx x hx
  exact ⟨u, hu, fun a ha => (htog a).mpr ha, hinv⟩

omit [Fintype V] [DecidableEq V] in
/-- **A clause fixes itself under a flip of one of its variables.** If the block at `u` is the single clause `C` and `x`
occurs in `C`, then flipping `x` makes the block true wherever it is false: a falsified clause has every literal false, and
the flip makes the literal of `x` true. This is the first hypothesis of `cross_any_system_of_falsify` for clause blocks. -/
theorem fixes_of_single {u : V} {C : Clause α} (hu : Ax u = {C}) {x : α} {s : Bool} (hx : (x, s) ∈ C) :
    ∀ a, ¬ SatB Ax a u → SatB Ax (flip x a) u := by
  intro a ha
  simp only [SatB, hu, Finset.mem_singleton, forall_eq, not_not] at ha ⊢
  intro hF
  have h1 := ha (x, s) hx
  have h2 := hF (x, s) hx
  simp only [flip, Function.update_self] at h2
  cases hax : a x <;> cases s <;> simp_all

omit [Fintype V] [DecidableEq V] in
/-- **A block that does not contain `x` does not see its flip.** This is the second hypothesis of
`cross_any_system_of_falsify`, for every block of the region other than the one that contains `x`. -/
theorem invisible_of_not_mem {v : V} {x : α} (hv : ∀ A ∈ Ax v, ∀ l ∈ A, l.1 ≠ x) :
    ∀ a, SatB Ax (flip x a) v ↔ SatB Ax a v := by
  intro a
  have key : ∀ A ∈ Ax v, (Falsifies (flip x a) A ↔ Falsifies a A) := by
    intro A hA
    have hl : ∀ l ∈ A, flip x a l.1 = a l.1 := fun l hl => by
      simp [flip, hv A hA l hl]
    constructor
    · intro h l hlA; rw [← hl l hlA]; exact h l hlA
    · intro h l hlA; rw [hl l hlA]; exact h l hlA
  simp only [SatB]
  constructor
  · intro h A hA; rw [← key A hA]; exact h A hA
  · intro h A hA; rw [key A hA]; exact h A hA

end Semantic

namespace Tseitin

variable {E V : Type*} [DecidableEq E] [Fintype E] [Fintype V] [DecidableEq V] {I : V → Finset E} {c : V → Bool}

/-- **Every proof system must cross a Tseitin boundary.** Under the hypotheses of `Tseitin.width_ge`, every refutation
of a Tseitin formula in every sound proof system with at most two premises per rule contains a line sensitive to at
least `e` edge variables. -/
theorem cross_any_system {K e : ℕ} (hK : 1 ≤ K) (hKV : K < Fintype.card V)
    (hsat : ∀ S : Finset V, S ≠ Finset.univ → ∃ a : E → Bool, ∀ v ∈ S, odd I a v = c v)
    (hexp : ∀ S : Finset V, K < 2 * S.card → S.card ≤ K → e ≤ (boundary I S).card)
    (h : SD (block I c) (fun _ => False)) :
    ∃ L, SD (block I c) L ∧ ∃ B : Finset E, e ≤ B.card ∧ ∀ x ∈ B, ∃ a, ¬ L a ∧ L (flip x a) := by
  refine ProofPhase.Proof.cross_any_system hK hKV (fun S hS hImp => ?_)
    (fun S h1 h2 => ⟨boundary I S, hexp S h1 h2, ?_⟩) h
  · obtain ⟨a, ha⟩ := hsat S hS
    exact hImp a fun v hv => (satB_block_iff a v).mpr (ha v hv)
  · intro x hx
    obtain ⟨u, hu, hxu, hrest⟩ := (Finset.mem_filter.mp hx).2
    exact ⟨u, hu, toggle hxu, fun v hv hvu => invisible (hrest v hv hvu)⟩

omit [DecidableEq V] in
/-- **One exclusive or carries the whole crossing flux.** The constraints of `S` force the single line "the parity of
the true boundary edges of `S` is the charge of `S`", which depends on the boundary edges only. -/
theorem summary (hI2 : ∀ e, (Finset.univ.filter fun v => e ∈ I v).card = 2) (S : Finset V) :
    ImpliesL (block I c) S fun a =>
      (((bd1 I S).filter fun e => a e = true).card : ZMod 2) = ∑ v ∈ S, (if c v = true then 1 else 0 : ZMod 2) :=
  fun a ha => flux_fixed hI2 fun v hv => (satB_block_iff a v).mp (ha v hv)

end Tseitin

/-! ### 3. Expansion gives crossing variables -/

section Expansion

variable {α V : Type*} [DecidableEq α] [DecidableEq V]

/-- The variables of the constraints in `S`. -/
def nbr (I : V → Finset α) (S : Finset V) : Finset α := S.biUnion I

/-- The variables that occur in exactly one constraint of `S` (the candidate toggle variables). -/
def uniq (I : V → Finset α) (S : Finset V) : Finset α :=
  (nbr I S).filter fun x => (S.filter fun v => x ∈ I v).card = 1

omit [DecidableEq V] in
/-- **Unique neighbours from expansion.** `2 |N(S)| ≤ Σ_{v ∈ S} |I v| + |U(S)|`: if the constraints of `S` (each with
at most `k` variables) touch at least `(k/2 + δ) |S|` variables, at least `2 δ |S|` of them occur in exactly one
constraint of `S`. -/
theorem unique_neighbors (I : V → Finset α) (S : Finset V) :
    2 * (nbr I S).card ≤ ∑ v ∈ S, (I v).card + (uniq I S).card := by
  have hcount : ∑ v ∈ S, (I v).card = ∑ x ∈ nbr I S, (S.filter fun v => x ∈ I v).card := by
    calc ∑ v ∈ S, (I v).card
        = ∑ v ∈ S, ((nbr I S).bipartiteAbove (fun v x => x ∈ I v) v).card :=
          Finset.sum_congr rfl fun v hv => by
            congr 1
            ext x
            simp only [Finset.bipartiteAbove, Finset.mem_filter, nbr, Finset.mem_biUnion]
            constructor
            · intro hx; exact ⟨⟨v, hv, hx⟩, hx⟩
            · exact fun h => h.2
      _ = _ := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
  have hdeg : ∀ x ∈ nbr I S, 1 ≤ (S.filter fun v => x ∈ I v).card := by
    intro x hx
    obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp hx
    exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hxv⟩⟩
  have huniq : (uniq I S).card =
      ∑ x ∈ nbr I S, (if (S.filter fun v => x ∈ I v).card = 1 then 1 else 0) := by
    rw [Finset.sum_boole, Nat.cast_id]
    rfl
  calc 2 * (nbr I S).card = ∑ _x ∈ nbr I S, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ x ∈ nbr I S, ((S.filter fun v => x ∈ I v).card +
          if (S.filter fun v => x ∈ I v).card = 1 then 1 else 0) := by
        refine Finset.sum_le_sum fun x hx => ?_
        have := hdeg x hx
        split_ifs with h <;> omega
    _ = ∑ v ∈ S, (I v).card + (uniq I S).card := by rw [Finset.sum_add_distrib, ← hcount, ← huniq]

end Expansion

end ProofPhase.Proof
