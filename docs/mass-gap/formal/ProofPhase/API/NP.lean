/-
The form layer as one API: the NP vs coNP instance, in the API's shape (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/API.md`, `docs/unified/UNIFIED.md` section 3.3, `docs/unified/NP-LIFTING.md`.
-/

import ProofPhase.API
import ProofPhase.Unified.ProofSize
import ProofPhase.Proof.LiftingNP

/-!
# NP vs coNP through the API: input + structure + one named open step

* **Input** (`Input`): a proof system as the set of its refutations (`Refutes`, finite sets of lines), a per-step cost
  `θ` and a number of restriction steps `b`.
* **Structure** (proved, `Unified/ProofSize.lean`): restrictions are the steps; the costly lines still present are the
  carried quantity; a step keeping at most the share `1 − θ` pays the cost `θ` (`crossing_pays`, a finite-horizon
  `Pays`, floor `0`); one costly line left at the end is the quantum, and the **size** reading of the ledger (`API.size`)
  gives the line count.
* **Open step** (`problem`): `CrossingCost`, every refutation admits `b` such steps with a costly line left.
* **Conclusion**: every refutation has at least `e^{θ b}` lines (`np_instance`).
* **External input** (`lifted`): the lifting theorem of Garg-Goos-Kamath-Sokolov for cutting planes (`LiftCP`), taken as a
  hypothesis in the `External` slot, discharges the open step for lifted formulas.

The proofs live in `Unified/ProofSize.lean` and `Proof/LiftingNP.lean`.
-/

noncomputable section

namespace ProofPhase.API.NP

open ProofPhase.Unified ProofPhase.Proof ProofPhase.Proof.Edge ProofPhase.Proof.Lifting

/-- **The well-defined input**: a proof system (its refutations), a cost per restriction step, a number of steps. -/
structure Input where
  Line : Type
  Refutes : Finset Line → Prop
  θ : ℝ
  b : ℕ

/-- **NP vs coNP as a problem card.** Open step: `CrossingCost`. Conclusion: every refutation has at least `e^{θ b}` lines. -/
def problem : Problem where
  name := "NP vs coNP: a crossing cost forces long refutations"
  Input := Input
  Open i := OpenStep "CrossingCost: b restrictions, each keeping at most a 1 - θ share of the costly lines, one left"
    (CrossingCost i.Refutes i.θ i.b)
  Concl i := ∀ P, i.Refutes P → Real.exp (i.θ * i.b) ≤ P.card
  sources := ["Ben-Sasson and Wigderson (resolution, proved in Proof/Dag.lean)"]
  proved _ h _ hP := np_instance h hP

/-- **The external input in its slot**: the lifting theorem `LiftCP` (Garg, Goos, Kamath, Sokolov) for cutting planes
gives a size bound for lifted formulas, hence the card's conclusion with `θ = 1/2`. -/
theorem lifted {gad : ℕ → Gadget} {c : ℝ} {n₀ : ℕ}
    (hExt : External "Garg-Goos-Kamath-Sokolov, STOC 2018, Theorems 1 and 2 (read for cutting planes)"
      (LiftCP gad c n₀)) {α : Type} [Fintype α] [DecidableEq α] (hn : n₀ ≤ Fintype.card α) {F : CNF α}
    (hF : ∀ D ∈ F, D.Nonempty) {w : ℕ} (hw : ¬ WD F w ∅) {b : ℕ}
    (hb : (b : ℝ) * Real.log 2 ≤ c * (w + 1) * Real.log (Fintype.card α))
    {P : Finset (CPLine (LV α (gad (Fintype.card α))))} (hP : CPRefutes (comp (gad (Fintype.card α)) F) P) :
    Real.exp ((1 / 2 : ℝ) * b) ≤ P.card :=
  lifted_np_instance hExt hn hF hw hb hP

end ProofPhase.API.NP
