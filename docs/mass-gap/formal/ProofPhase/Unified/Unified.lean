/-
The unified lossy-step theorem: the three instances side by side (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/UNIFIED.md`.
-/

import ProofPhase.Unified.YangMills
import ProofPhase.Unified.GRH
import ProofPhase.Unified.ProofSize

/-!
# One ledger, three instances, three named hypotheses

`three_instances` states the three instances in one statement, each as "named hypothesis ⟹ conclusion":

| | named hypothesis (open) | conclusion (Lean, from the ledger) |
|---|---|---|
| Yang-Mills | `YMOneBox Fe μ`: the electric cost of one box exceeds the path entropy `log μ`, over every outside | the path sum decays at rate `κ − log μ > 0` and is summable |
| GRH | `ScaleSign t`: every scale step carries the margin with a nonnegative factor | every zero of the finite model on the line; Weil's pairing nonnegative |
| NP vs coNP | `CrossingCost Refutes θ b`: `b` restrictions, each killing a `θ` share of the costly lines, one left | every refutation has at least `e^{θ b}` lines |

The general theorem behind all three is `carry` (`Unified/Ledger.lean`). No axioms beyond the standard ones.
-/

open Finset

noncomputable section

namespace ProofPhase.Unified

/-- **The three instances side by side.** -/
theorem three_instances :
    -- Yang-Mills: O1 gives a positive decay rate of the path sum
    (∀ (Ω D : Type) [Fintype D] [Nonempty D] (w : Ω → D → ℝ) (Fe : Ω → ℝ), (∀ ω d, 0 ≤ w ω d) →
      (∀ ω d, w ω d ≤ Real.exp (-Fe ω)) → YMOneBox Fe (Fintype.card D) → ∀ ω : ℕ → Ω,
        ∃ κ : ℝ, Real.log (Fintype.card D) < κ ∧
          (∀ n, pathSum w ω n ≤ Real.exp (-(n * (κ - Real.log (Fintype.card D))))) ∧ Summable (pathSum w ω)) ∧
    -- GRH: the sign at every scale puts the zeros of the finite model on the line
    (∀ (k : ℕ) (Z : ZeroModel k), ScaleSign Z.t →
      (∀ i, (Z.γ i).im = 0) ∧ ∀ F ∈ ProofPhase.GRH.expSums, 0 ≤ (ProofPhase.GRH.weilSum Z.γ Z.σ F).re) ∧
    -- NP vs coNP: the crossing cost gives a size lower bound
    (∀ (Line : Type) (Refutes : Finset Line → Prop) (θ : ℝ) (b : ℕ), CrossingCost Refutes θ b →
      ∀ P, Refutes P → Real.exp (θ * b) ≤ P.card) :=
  ⟨fun _ _ _ _ _ _ hw0 hw h ω => ym_instance hw0 hw h ω,
    fun _ Z h => grh_instance Z h,
    fun _ _ _ _ h _ hP => np_instance h hP⟩

end ProofPhase.Unified
