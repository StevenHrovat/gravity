/-
GRH attempt, transfer round: chain and two-term templates (2026-11-23). Released under Apache 2.0.

Note: `docs/rh-guide/grh/TRANSFER.md`.
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Contraction, sign and two-term bounds, in finite form

**1. Contraction collapses the margin** (`prod_one_sub_le_exp`): if every step loses a fraction `c_i ∈ [0, 1]`, the
product of the factors is at most `exp(-∑ c_i)`. So when the losses are not summable the margin goes to zero. In
Yang-Mills this is the wanted decay; in the GRH induction it is the (harmless) collapse of the margin.

**2. The sign is the positivity of every factor** (`margin_pos_of_factors`): a margin that is a positive start times
a product of factors stays positive exactly as long as no factor fails. The sign concerns `f_j > 0`, not `f_j < 1`.

**3. Two-term bounds add** (`two_term_bound`): lower bounds `α` for `A` and `β` for `P` give `α + β` for `A + P`
(Weyl). A bound that sees `A` and `P` only separately cannot do better, since aligning the worst directions attains
it; positivity of `A + P` beyond `α + β` is a statement about their relative position.
-/

open Finset

open scoped Matrix

noncomputable section

namespace ProofPhase.GRH

/-- Losses `c_i ∈ [0, 1]` per step: the product of the factors is at most `exp(-∑ c_i)`. -/
theorem prod_one_sub_le_exp {ι : Type*} (s : Finset ι) (c : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ c i)
    (h1 : ∀ i ∈ s, c i ≤ 1) : ∏ i ∈ s, (1 - c i) ≤ Real.exp (-∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, neg_add, Real.exp_add]
    have hB : 1 - c a ≤ Real.exp (-c a) := by linarith [Real.add_one_le_exp (-c a)]
    have ih' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hP : 0 ≤ ∏ i ∈ s, (1 - c i) :=
      Finset.prod_nonneg (fun i hi => by linarith [h1 i (Finset.mem_insert_of_mem hi)])
    exact mul_le_mul hB ih' hP (Real.exp_pos _).le

/-- A positive start times positive factors stays positive. -/
theorem margin_pos_of_factors (E0 : ℝ) (h0 : 0 < E0) (f : ℕ → ℝ) (n : ℕ) (hf : ∀ j < n, 0 < f j) :
    0 < E0 * ∏ j ∈ Finset.range n, f j :=
  mul_pos h0 (Finset.prod_pos (fun j hj => hf j (Finset.mem_range.mp hj)))

/-- Weyl's two-term bound: lower bounds add. -/
theorem two_term_bound {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℝ) (α β : ℝ)
    (hA : ∀ x, α * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)) (hP : ∀ x, β * (x ⬝ᵥ x) ≤ x ⬝ᵥ (P *ᵥ x)) :
    ∀ x, (α + β) * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A + P) *ᵥ x) := by
  intro x
  rw [Matrix.add_mulVec, dotProduct_add, add_mul]
  linarith [hA x, hP x]

end ProofPhase.GRH
