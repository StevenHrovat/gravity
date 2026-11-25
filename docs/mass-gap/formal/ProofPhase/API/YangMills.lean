/-
The form layer as one API: the Yang-Mills instance, in the API's shape (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/API.md`, `docs/unified/UNIFIED.md` section 3.1.
-/

import ProofPhase.API
import ProofPhase.Unified.YangMills

/-!
# Yang-Mills through the API: input + structure + one named open step

* **Input** (`Input`): boxes in a chain. In each outside `ω` a box passes on one of `d` continuations (path entropy
  `log d`) with weight `w ω k`, at most `e^{−Fe ω}`, `Fe` the box's electric free energy (its cost).
* **Structure** (`chain`, proved, nothing assumed): the path sum over `n` boxes is a `Chain` with cost `Fe` and floor
  `log d` (`Unified.pathSum_pays`).
* **Open step** (`problem`, O1 = III.5.6): `YMOneBox`, the cost of one box exceeds the path entropy, over every outside.
* **Conclusion**: the path sum decays at a rate `κ − log d > 0` and is summable (influence runs in tubes). It follows
  from the `Chain` theorems `decay` and `summable`; no new proof.

The proofs live in `Unified/YangMills.lean`; this file only states them through the API.
-/

noncomputable section

namespace ProofPhase.API.YangMills

open ProofPhase.Unified

/-- **The well-defined input**: `d ≥ 1` continuations per box, box weights `w ω k ∈ [0, e^{−Fe ω}]`, and the sequence of
outsides along the chain. -/
structure Input where
  Ω : Type
  d : ℕ
  d_pos : 0 < d
  w : Ω → Fin d → ℝ
  Fe : Ω → ℝ
  w_nonneg : ∀ ω k, 0 ≤ w ω k
  w_le : ∀ ω k, w ω k ≤ Real.exp (-Fe ω)
  outsides : ℕ → Ω

instance (i : Input) : Nonempty (Fin i.d) := ⟨⟨0, i.d_pos⟩⟩

/-- **The proved structure**: the path sum is a chain with costs `Fe (outsides n)` and floor `log d`. -/
def chain (i : Input) : Chain (Real.log (Fintype.card (Fin i.d))) where
  M := pathSum i.w i.outsides
  c n := i.Fe (i.outsides n)
  M_nonneg := pathSum_nonneg i.w_nonneg i.outsides
  step n := pathSum_pays i.w_nonneg i.w_le i.outsides (n + 1) n (Nat.lt_succ_self n)

/-- **Yang-Mills as a problem card.** Open step: O1 (`YMOneBox`). Conclusion: a positive rate and summability. -/
def problem : Problem where
  name := "Yang-Mills: influence runs in tubes (O1 gives a decay rate and a summable path sum)"
  Input := Input
  Open i := OpenStep "O1: the electric cost of one box exceeds the path entropy, over every outside"
    (YMOneBox i.Fe (Fintype.card (Fin i.d)))
  Concl i := ∃ κ : ℝ, Real.log (Fintype.card (Fin i.d)) < κ ∧
    (∀ n, pathSum i.w i.outsides n ≤ Real.exp (-(n * (κ - Real.log (Fintype.card (Fin i.d)))))) ∧
      Summable (pathSum i.w i.outsides)
  proved i h := by
    obtain ⟨κ, hκ, hcost⟩ := h
    refine ⟨κ, hκ, fun n => ?_, (chain i).summable (fun k => hcost _) hκ⟩
    simpa [chain, pathSum_zero] using (chain i).decay (fun k => hcost _) n

end ProofPhase.API.YangMills
