/-
The form layer as one API: the GRH instance, in the API's shape (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/API.md`, `docs/unified/UNIFIED.md` section 3.2, `docs/unified/GRH-TIE-IN.md`.
-/

import ProofPhase.API
import ProofPhase.Unified.GRH
import ProofPhase.GRH.TieIn

/-!
# GRH through the API: input + structure + one named open step

* **Input** (`Input`): a finite model of zeros (`ZeroModel`): finitely many zeros `1/2 + i γ`, closed under the functional
  equation, on a grid; `t` the grid moments.
* **Structure** (proved, `Unified/GRH.lean`): the margin of the Toeplitz form is carried scale by scale (a certified lower
  bound shrunk by a nonnegative share per step, `scaleSign_margin`; the survival reading of the ledger), and the sign at
  every scale is positivity of Weil's form (`scaleSign_iff`).
* **Open step** (`problem`): `ScaleSign t`, no scale step overdraws the margin.
* **Conclusion**: every zero of the model is on the line, and Weil's pairing is nonnegative on every finite exponential
  sum (`grh_instance`).
* **External input** (`tie_in`): the project's `ScaleSign` follows from Mathlib's statement of the Riemann hypothesis
  (an outside, open statement taken as a hypothesis, in the `External` slot).

The proofs live in `Unified/GRH.lean` and `GRH/TieIn.lean`.
-/

noncomputable section

namespace ProofPhase.API.GRH

open ProofPhase.Unified ProofPhase.GRH

/-- **The well-defined input**: a finite model of zeros. -/
structure Input where
  k : ℕ
  Z : ZeroModel k

/-- **GRH as a problem card.** Open step: `ScaleSign` (the sign at every scale). Conclusion: zeros on the line and Weil's
pairing nonnegative on finite exponential sums. -/
def problem : Problem where
  name := "GRH, finite model: the sign at every scale puts the zeros on the line"
  Input := Input
  Open i := OpenStep "ScaleSign: every scale step carries the margin with a nonnegative factor" (ScaleSign i.Z.t)
  Concl i := (∀ j, (i.Z.γ j).im = 0) ∧ ∀ F ∈ expSums, 0 ≤ (weilSum i.Z.γ i.Z.σ F).re
  sources := ["Weil criterion, finite exponential sums (GRH/Weil.lean, proved)"]
  proved i h := grh_instance i.Z h

/-- **The external input in its slot**: Mathlib's `RiemannHypothesis` (open) gives the sign for a model whose zeros are
zeros of zeta, with multiplicity weights; so the open step of the card follows from the external statement. -/
theorem tie_in (hExt : External "Mathlib: RiemannHypothesis (the statement; open)" ExtRH) (i : Input)
    (hw : ∀ j, ∃ r : ℝ, 0 ≤ r ∧ i.Z.w j = r) (hz : StripZeros riemannZeta i.Z.γ) :
    problem.Open i ∧ problem.Concl i :=
  have h := (zeta_tie_in_finite hExt i.Z hw hz).1
  ⟨h, problem.holds i h⟩

end ProofPhase.API.GRH
