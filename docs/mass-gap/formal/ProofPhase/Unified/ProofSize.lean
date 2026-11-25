/-
The unified lossy-step theorem: the NP vs coNP instance (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/UNIFIED.md`, section 3.3.
-/

import ProofPhase.Unified.Ledger
import ProofPhase.Proof.Dag

/-!
# NP vs coNP as a lossy chain: restrictions are the steps, the crossing cost is the price, one line is the quantum

A refutation is a finite set of lines of some proof system (`Refutes P`). The steps are restrictions (fixing a literal).
The quantity carried is the number of **costly** lines still present (for resolution: the fat lines, those wider than a
threshold). A step that kills at least a `θ` share of the costly lines pays the cost `θ` (`1 − θ ≤ e^{−θ}`). At the
end at least one costly line is left: the crossing persists. That single line is the quantum `φ = 1` of the size reading of the ledger.

* **`CrossingCost Refutes θ b`** (the named hypothesis, **open** for strong systems: cutting planes at constant width,
  Frege): every refutation admits `b` restriction steps, each leaving at most a `1 − θ` share of the costly lines, with
  a costly line left at the end.
* `crossing_pays`: such a chain pays the cost `θ` per step, floor `0`.
* **`np_instance`**: every refutation has at least `e^{θ b}` lines. The only non-proved input is `CrossingCost`.
* `resolution_meets_form` (reference, proved): for resolution the same bound holds with `θ = (w + d + 1)/2n`, by
  Ben-Sasson and Wigderson (`Proof/Dag.lean`, `size_width_exp`). There the chain runs along a path of a restriction
  tree, so this matches the conclusion; it is not a `CrossingCost` witness.

No axioms beyond the standard ones.
-/

open Finset

noncomputable section

namespace ProofPhase.Unified

/-- **The crossing cost (NP vs coNP's named hypothesis).** Every refutation `P` admits `b` restriction steps: `Q i` are
the costly lines after `i` steps, `Q 0 ⊆ P`, each step leaves at most a `1 − θ` share, and a costly line is left at the
end. -/
def CrossingCost {Line : Type*} (Refutes : Finset Line → Prop) (θ : ℝ) (b : ℕ) : Prop :=
  ∀ P, Refutes P → ∃ Q : ℕ → Finset Line, Q 0 ⊆ P ∧
    (∀ i < b, ((Q (i + 1)).card : ℝ) ≤ (1 - θ) * (Q i).card) ∧ (Q b).Nonempty

/-- A step that keeps at most a `1 − θ` share pays the cost `θ` (floor `0`). -/
theorem crossing_pays {Line : Type*} {Q : ℕ → Finset Line} {θ : ℝ} {b : ℕ}
    (h : ∀ i < b, ((Q (i + 1)).card : ℝ) ≤ (1 - θ) * (Q i).card) :
    Pays (fun i => ((Q i).card : ℝ)) (fun _ => θ) 0 b := fun i hi => by
  have h1 : 1 - θ ≤ Real.exp (0 - θ) := by rw [zero_sub]; linarith [Real.add_one_le_exp (-θ)]
  exact (h i hi).trans (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _))

/-- **The NP vs coNP instance.** Under the crossing cost every refutation has at least `e^{θ b}` lines. The only
non-proved input is `CrossingCost`. -/
theorem np_instance {Line : Type*} {Refutes : Finset Line → Prop} {θ : ℝ} {b : ℕ} (h : CrossingCost Refutes θ b)
    {P : Finset Line} (hP : Refutes P) : Real.exp (θ * b) ≤ P.card := by
  obtain ⟨Q, hQ0, hstep, hend⟩ := h P hP
  have hs := size (crossing_pays hstep) (φ := 1) (by exact_mod_cast hend.card_pos)
  rw [one_mul, sum_const, card_range, nsmul_eq_mul, mul_zero, sub_zero, mul_comm] at hs
  exact hs.trans (by exact_mod_cast card_le_card hQ0)

/-- **Size in log units**: `log |P| ≥ θ b`, the sum of the costs (floor `0`, quantum `1`). -/
theorem np_instance_log {Line : Type*} {Refutes : Finset Line → Prop} {θ : ℝ} {b : ℕ} (h : CrossingCost Refutes θ b)
    {P : Finset Line} (hP : Refutes P) : θ * b ≤ Real.log P.card := by
  have := np_instance h hP
  rw [← Real.log_exp (θ * b)]
  exact Real.log_le_log (Real.exp_pos _) this

/-- **Resolution meets the form** (reference, proved): Ben-Sasson and Wigderson give the instance's conclusion with
`θ = (w + d + 1)/2n` for every DAG-like resolution refutation of a formula without refutations of width `w + d + b`. -/
theorem resolution_meets_form {α : Type*} [DecidableEq α] [Fintype α] {F : ProofPhase.Proof.CNF α}
    {P : Finset (ProofPhase.Proof.Clause α)} {w d b : ℕ} (hw : ∀ A ∈ F, A.card ≤ w)
    (hTM : w + d + 1 ≤ 2 * Fintype.card α) (h : ProofPhase.Proof.RD F P ∅)
    (hW : ¬ ProofPhase.Proof.WD F (w + d + b) ∅) :
    Real.exp ((((w + d + 1 : ℕ) : ℝ) / ((2 * Fintype.card α : ℕ) : ℝ)) * b) ≤ P.card := by
  rw [mul_comm]
  exact ProofPhase.Proof.size_width_exp hw hTM h hW

end ProofPhase.Unified
