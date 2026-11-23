/-
NP vs coNP, lifting, part 2: the lifting theorem as a named hypothesis, the instance of `CrossingCost` and
`np_instance` for lifted formulas, and the interface of a constant-gadget version (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/NP-LIFTING.md`, sections 3 to 5.
-/

import ProofPhase.Proof.Lifting
import ProofPhase.Unified.ProofSize

/-!
# The NP column of the ledger, inhabited by lifted formulas

**What is assumed (named, external, not proved here).** `LiftCP gad c n₀` is the lifting theorem of Garg, Goos, Kamath
and Sokolov (STOC 2018, Theory of Computing 2020, Theorems 1 and 2) read for cutting planes: for a CNF `F` on `n`
variables whose resolution width exceeds `w`, every cutting-planes refutation of `F ∘ g` has at least
`exp (c (w + 1) log n) = n^{c (w + 1)}` lines, where `g = gad n` is the gadget used for `n` variables. `GGKS` is the
statement for the Index gadget of size `m = 2^⌈δ log₂ n⌉ ≈ n^δ`. The source proves it for semantic triangle-dags (lines
with real coefficients), which contain the syntactic integer-coefficient lines used here; the passage from a clause of
`F ∘ g` to a solution of the lifted search problem is `comp_falsified_iff`. Both passages are classical and not
formalised (flagged in the paper).

**What is proved (standard axioms only).**
* `crossingCost_of_size`: a size bound `2^b ≤ |P|` for every refutation is a `CrossingCost` with `θ = 1/2` and `b`
  steps. (The chain is manufactured from the size bound by halving; so a `CrossingCost` is, up to constants in the
  exponent, the same thing as an exponential size bound. See the paper, section 4.)
* `lifted_crossingCost`, `lifted_np_instance`, `lifted_theta_b`: under `LiftCP`, the NP column is inhabited by the
  class "lifted width-hard formulas": `CrossingCost` holds with `θ = 1/2` and `b = ⌊c (w + 1) log₂ n⌋`, so `θ b` is of
  order `w log n`, and `np_instance` gives `exp (θ b) ≤ |P|`.
* `LiftCPConst`: **the interface of the constant version.** The same statement for one fixed gadget, with the bound
  `exp (c (w + 1))`, free of `n`. `constGadget_interface` shows its shape: constant width, linearly many variables,
  `exp (Ω (w))` size.
* `WidthToCP K c`: the gadget-free statement for a class `K` of formulas (the project's interface question).

Nothing here proves NP vs coNP, or any lower bound: the lower bounds are the hypothesis.

**New here:** everything in this file.
-/

namespace ProofPhase.Proof.Lifting

open Finset ProofPhase.Proof ProofPhase.Proof.Edge ProofPhase.Unified

/-! ### 1. A size bound is a crossing cost -/

/-- **A size bound gives a chain.** If every refutation has at least `2^b` lines, `CrossingCost` holds with `θ = 1/2`
and `b` steps: halve the line set `b` times (a set of `⌊|P| / 2^i⌋` lines at step `i`), and one line is left at the end. -/
theorem crossingCost_of_size {Line : Type*} {Refutes : Finset Line → Prop} {b : ℕ}
    (h : ∀ P, Refutes P → 2 ^ b ≤ P.card) : CrossingCost Refutes (1 / 2) b := by
  intro P hP
  have hex : ∀ i : ℕ, ∃ t ⊆ P, t.card = P.card / 2 ^ i := fun i =>
    Finset.exists_subset_card_eq (Nat.div_le_self _ _)
  choose Q hQ hc using hex
  refine ⟨Q, hQ 0, ?_, ?_⟩
  · intro i _
    rw [hc, hc]
    have h1 : P.card / 2 ^ (i + 1) = P.card / 2 ^ i / 2 := by
      rw [Nat.div_div_eq_div_mul, pow_succ]
    rw [h1]
    have h2 := Nat.cast_div_le (α := ℝ) (m := P.card / 2 ^ i) (n := 2)
    push_cast at h2
    linarith
  · rw [← Finset.card_pos, hc]
    exact Nat.div_pos (h P hP) (by positivity)

/-- **And back**: a crossing cost is a size bound (`np_instance`), here for `θ = 1/2`. -/
theorem size_of_crossingCost_half {Line : Type*} {Refutes : Finset Line → Prop} {b : ℕ}
    (h : CrossingCost Refutes (1 / 2) b) {P : Finset Line} (hP : Refutes P) : Real.exp (b / 2) ≤ P.card := by
  have := np_instance h hP
  rwa [one_div, inv_mul_eq_div] at this

/-! ### 2. The lifting theorem as a named hypothesis -/

/-- **`LiftCP gad c n₀`** (the lifting theorem, external). For every CNF `F` on `n ≥ n₀` variables without empty clause
whose resolution width exceeds `w` (`¬ WD F w ∅`), every cutting-planes refutation `P` of `F ∘ (gad n)` has at least
`exp (c (w + 1) log n)` lines. -/
def LiftCP (gad : ℕ → Gadget) (c : ℝ) (n₀ : ℕ) : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α], n₀ ≤ Fintype.card α →
    ∀ (F : CNF α) (w : ℕ), (∀ D ∈ F, D.Nonempty) → ¬ WD F w ∅ →
      ∀ P : Finset (CPLine (LV α (gad (Fintype.card α)))), CPRefutes (comp (gad (Fintype.card α)) F) P →
        Real.exp (c * (w + 1) * Real.log (Fintype.card α)) ≤ P.card

/-- **GGKS** (external, named): the lifting theorem for the Index gadget of size `m = 2^⌈δ log₂ n⌉` (between `n^δ` and
`2 n^δ`), some constant `δ`, some constant `c > 0`. Source: Theorems 1 and 2 of Garg, Goos, Kamath, Sokolov, with the
standard reduction of a CNF to its search problem; see the paper for the exact wording and the two unformalised steps. -/
def GGKS : Prop :=
  ∃ (δ : ℕ) (c : ℝ), 0 < c ∧ ∃ n₀ : ℕ, LiftCP (fun n => indGadget (Nat.clog 2 (n ^ δ))) c n₀

/-! ### 3. The instance of the ledger -/

section Instance

variable {gad : ℕ → Gadget} {c : ℝ} {n₀ : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- **The size bound** for lifted formulas (the hypothesis read at one formula). -/
theorem lifted_size (h : LiftCP gad c n₀) (hn : n₀ ≤ Fintype.card α) {F : CNF α} (hF : ∀ D ∈ F, D.Nonempty) {w : ℕ}
    (hw : ¬ WD F w ∅) {P : Finset (CPLine (LV α (gad (Fintype.card α))))}
    (hP : CPRefutes (comp (gad (Fintype.card α)) F) P) :
    Real.exp (c * (w + 1) * Real.log (Fintype.card α)) ≤ P.card :=
  h α hn F w hF hw P hP

/-- **`CrossingCost` for lifted formulas.** Every `b` with `b log 2 ≤ c (w + 1) log n` is a number of steps. -/
theorem lifted_crossingCost (h : LiftCP gad c n₀) (hn : n₀ ≤ Fintype.card α) {F : CNF α} (hF : ∀ D ∈ F, D.Nonempty)
    {w : ℕ} (hw : ¬ WD F w ∅) {b : ℕ} (hb : (b : ℝ) * Real.log 2 ≤ c * (w + 1) * Real.log (Fintype.card α)) :
    CrossingCost (CPRefutes (comp (gad (Fintype.card α)) F)) (1 / 2) b := by
  refine crossingCost_of_size fun P hP => ?_
  have h1 := lifted_size h hn hF hw hP
  have h2 : ((2 : ℝ) ^ b) ≤ P.card := by
    calc (2 : ℝ) ^ b = Real.exp (b * Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ Real.exp (c * (w + 1) * Real.log (Fintype.card α)) := Real.exp_le_exp.2 hb
      _ ≤ _ := h1
  exact_mod_cast h2

/-- **The NP instance for lifted formulas** (`np_instance` of `Unified/ProofSize.lean`, with its hypothesis discharged by
the lifting theorem): every cutting-planes refutation of `F ∘ g` has at least `exp (θ b)` lines. -/
theorem lifted_np_instance (h : LiftCP gad c n₀) (hn : n₀ ≤ Fintype.card α) {F : CNF α} (hF : ∀ D ∈ F, D.Nonempty)
    {w : ℕ} (hw : ¬ WD F w ∅) {b : ℕ} (hb : (b : ℝ) * Real.log 2 ≤ c * (w + 1) * Real.log (Fintype.card α))
    {P : Finset (CPLine (LV α (gad (Fintype.card α))))} (hP : CPRefutes (comp (gad (Fintype.card α)) F) P) :
    Real.exp ((1 / 2 : ℝ) * b) ≤ P.card :=
  np_instance (lifted_crossingCost h hn hF hw hb) hP

/-- **`θ b` is of order `w log n`.** The largest admissible number of steps `b = ⌊c (w + 1) log n / log 2⌋` has
`θ b = b / 2 ≥ c (w + 1) log n / (2 log 2) − 1/2`. -/
theorem lifted_theta_b (h : LiftCP gad c n₀) (hc : 0 ≤ c) (hn : n₀ ≤ Fintype.card α)
    {F : CNF α} (hF : ∀ D ∈ F, D.Nonempty) {w : ℕ} (hw : ¬ WD F w ∅) :
    ∃ b : ℕ, CrossingCost (CPRefutes (comp (gad (Fintype.card α)) F)) (1 / 2) b ∧
      c * (w + 1) * Real.log (Fintype.card α) / (2 * Real.log 2) - 1 / 2 ≤ (1 / 2 : ℝ) * b := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hln : 0 ≤ Real.log (Fintype.card α) := Real.log_natCast_nonneg _
  set x : ℝ := c * (w + 1) * Real.log (Fintype.card α) / Real.log 2 with hx
  have hx0 : 0 ≤ x := by positivity
  refine ⟨⌊x⌋₊, lifted_crossingCost h hn hF hw ?_, ?_⟩
  · have := Nat.floor_le hx0
    have h3 : (⌊x⌋₊ : ℝ) * Real.log 2 ≤ x * Real.log 2 := mul_le_mul_of_nonneg_right this hl2.le
    rwa [hx, div_mul_cancel₀ _ hl2.ne'] at h3
  · have := Nat.lt_floor_add_one x
    have h4 : c * (w + 1) * Real.log (Fintype.card α) / (2 * Real.log 2) = x / 2 := by
      rw [hx]; field_simp
    rw [h4]
    linarith

end Instance

/-! ### 4. The interface of a constant-gadget version, and of a gadget-free version -/

/-- **`LiftCPConst G c`: what a constant-size-gadget lifting theorem would have to state.** One fixed gadget `G` (its size
free of `n`), every CNF `F` without empty clause, resolution width exceeding `w`: every cutting-planes refutation of
`F ∘ G` has at least `exp (c (w + 1))` lines. The only change from `LiftCP` is that `log n` is gone: the lower bound is
exponential in the width itself. **Open for every constant-size gadget** (to be read with the paper, section 5). -/
def LiftCPConst (G : Gadget) (c : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (F : CNF α) (w : ℕ), (∀ D ∈ F, D.Nonempty) → ¬ WD F w ∅ →
    ∀ P : Finset (CPLine (LV α G)), CPRefutes (comp G F) P → Real.exp (c * (w + 1)) ≤ P.card

/-- **The constant interface, in ledger form**: `CrossingCost` with `θ = 1/2` and `b = ⌊c (w + 1) / log 2⌋` steps. -/
theorem constGadget_crossingCost {G : Gadget} {c : ℝ} (h : LiftCPConst G c) {α : Type} [Fintype α] [DecidableEq α]
    {F : CNF α} (hF : ∀ D ∈ F, D.Nonempty) {w : ℕ} (hw : ¬ WD F w ∅) {b : ℕ}
    (hb : (b : ℝ) * Real.log 2 ≤ c * (w + 1)) : CrossingCost (CPRefutes (comp G F)) (1 / 2) b := by
  refine crossingCost_of_size fun P hP => ?_
  have h1 := h α F w hF hw P hP
  have h2 : ((2 : ℝ) ^ b) ≤ P.card := by
    calc (2 : ℝ) ^ b = Real.exp (b * Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ Real.exp (c * (w + 1)) := Real.exp_le_exp.2 hb
      _ ≤ _ := h1
  exact_mod_cast h2

/-- **The shape of the constant version.** For a constant gadget and a `k`-CNF `F` on `n` variables with resolution width
exceeding `w`, the lifted formula is a `k (a + b)`-CNF (constant width) on `n (a + b)` variables (linearly many), and
under `LiftCPConst` every cutting-planes refutation has at least `exp (c (w + 1))` lines: with `w = Ω(n)` this is
`exp (Ω (n))`, exponential in the number of variables. -/
theorem constGadget_interface {G : Gadget} {c : ℝ} (h : LiftCPConst G c) {α : Type} [Fintype α] [DecidableEq α]
    {F : CNF α} {k : ℕ} (hk : ∀ D ∈ F, D.card ≤ k) (hF : ∀ D ∈ F, D.Nonempty) {w : ℕ} (hw : ¬ WD F w ∅)
    {P : Finset (CPLine (LV α G))} (hP : CPRefutes (comp G F) P) :
    (∀ A ∈ comp G F, A.card ≤ k * (G.a + G.b)) ∧
      Fintype.card (LV α G) = Fintype.card α * (G.a + G.b) ∧ Real.exp (c * (w + 1)) ≤ P.card :=
  ⟨fun _ hA => card_comp_le G hk hA, card_LV α G, h α F w hF hw P hP⟩

/-- **`WidthToCP K c`: the gadget-free interface for a class `K` of formulas.** For every formula of the class, no empty
clause, resolution width exceeding `w`: every cutting-planes refutation has at least `exp (c (w + 1))` lines. For the
class of all CNFs it is **false** (pigeonhole formulas have polynomial-size cutting-planes refutations; classical,
recalled, not formalised), so any version must restrict `K`; the gadget is what lifting uses to restrict it. -/
def WidthToCP (K : ∀ (α : Type) [Fintype α] [DecidableEq α], CNF α → Prop) (c : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (F : CNF α), K α F → (∀ D ∈ F, D.Nonempty) → ∀ w : ℕ, ¬ WD F w ∅ →
    ∀ P : Finset (CPLine α), CPRefutes F P → Real.exp (c * (w + 1)) ≤ P.card

/-- **The gadget-free interface in ledger form.** -/
theorem widthToCP_crossingCost {K : ∀ (α : Type) [Fintype α] [DecidableEq α], CNF α → Prop} {c : ℝ}
    (h : WidthToCP K c) {α : Type} [Fintype α] [DecidableEq α] {F : CNF α} (hK : K α F)
    (hF : ∀ D ∈ F, D.Nonempty) {w : ℕ} (hw : ¬ WD F w ∅) {b : ℕ} (hb : (b : ℝ) * Real.log 2 ≤ c * (w + 1)) :
    CrossingCost (CPRefutes F) (1 / 2) b := by
  refine crossingCost_of_size fun P hP => ?_
  have h1 := h α F hK hF w hw P hP
  have h2 : ((2 : ℝ) ^ b) ≤ P.card := by
    calc (2 : ℝ) ^ b = Real.exp (b * Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ Real.exp (c * (w + 1)) := Real.exp_le_exp.2 hb
      _ ≤ _ := h1
  exact_mod_cast h2

/-! ### 5. The lifted formula meets the creative-pair step, whatever the lower bound -/

section Both

variable {gad : ℕ → Gadget} {c : ℝ} {n₀ : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- **Lifting does not remove the pair, it prices it.** For a lifted formula, `CrossingCost` (from `LiftCP`) and the
creative pair (`lifted_needs_pair`, unconditional) hold together: every refutation has `≥ exp (θ b)` lines and contains
a rounding of a combination of at least two lines. -/
theorem lifted_pair_and_cost (h : LiftCP gad c n₀) (hn : n₀ ≤ Fintype.card α) {F : CNF α}
    (hF : ∀ D ∈ F, D.Nonempty) {w : ℕ} (hw : ¬ WD F w ∅) (ha : 0 < (gad (Fintype.card α)).a)
    (hb' : 0 < (gad (Fintype.card α)).b) {b : ℕ} (hb : (b : ℝ) * Real.log 2 ≤ c * (w + 1) * Real.log (Fintype.card α))
    {P : Finset (CPLine (LV α (gad (Fintype.card α))))} (hP : CPRefutes (comp (gad (Fintype.card α)) F) P) :
    Real.exp ((1 / 2 : ℝ) * b) ≤ P.card ∧
      ∃ (L₀ : CPLine (LV α (gad (Fintype.card α)))) (d : ℕ),
        CPD (univ : Finset (LV α (gad (Fintype.card α)))) (cnfAx (comp (gad (Fintype.card α)) F)) L₀ ∧ 0 < d ∧
        ¬ ∃ A ∈ cnfAx (comp (gad (Fintype.card α)) F), ∃ c : ℕ, 0 < c ∧ L₀ = scaleL c A := by
  refine ⟨lifted_np_instance h hn hF hw hb hP, ?_⟩
  obtain ⟨L₀, d, h1, h2, -, -, -, h6⟩ := lifted_needs_pair (gad (Fintype.card α)) hF ha hb' hP
  exact ⟨L₀, d, h1, h2, h6⟩

end Both

end ProofPhase.Proof.Lifting
