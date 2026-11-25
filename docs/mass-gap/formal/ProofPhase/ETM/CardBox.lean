/-
Every card as a box in the one-box test (2026-11-24).
Released under Apache 2.0.

Note: the "box" sections of the problem parts (`docs/paper/draft/05` to `10`).
-/

import ProofPhase.ETM.Rotation
import ProofPhase.API.GRH
import ProofPhase.API.NP
import ProofPhase.API.Phase
import ProofPhase.Unified.BSDAPI
import ProofPhase.Unified.HodgeAPI
import Arsenal.Observable

/-!
# Every card as a box

**The tick box** (`tickBox P`). One tick per natural number; the gate reads `inside` when the tick's statement `P n` holds,
`r136a1` otherwise; the marker is the claim `inside`. It is DMP-complete exactly when every tick's statement holds
(`tickBox_complete_iff`), and one failing tick makes it fail (`tickBox_wrong`). The marker is never read off the gate.

**The card box** (`cardBox Pr i`). For a problem card of the API (`API.Problem`) and an input, every tick carries the card's one
open step. It is DMP-complete exactly when the open step holds (`cardBox_complete_iff`), and then the card's conclusion follows
(`cardBox_concl`). Like the Yang-Mills box, it restates the open step in the test's language and proves no new bound: the content
stays in the open step.

**The five boxes.**
* GRH (`grh_box_iff`, `grh_box_of_RH`): the box of a finite zero model passes exactly when the sign holds at every scale; for a
  model of zeta's zeros it passes under Mathlib's statement of the Riemann hypothesis (an `External` slot).
* P vs NP (`np_box_concl`): a passing box gives the crossing bound, every refutation of size at least `e^{θ b}`.
* BSD (`bsd_box_iff`): the box of a curve passes exactly when BSD holds for it.
* Hodge (`hodge_box_iff`, `hodge_box_divisor`): the box passes exactly when the Hodge conjecture holds for the input; for
  divisors (codimension one) it passes, from Lefschetz (1,1) with its named inputs.
* GU (`gu_box`): the box whose ticks carry charge quantisation passes, proved.

No axioms beyond the standard ones.
-/

noncomputable section

open Classical

namespace ProofPhase.ETM

/-! ## The tick box -/

/-- **The tick box**: the gate reads `inside` at tick `n` exactly when `P n` holds; the marker is the claim `inside`. -/
def tickBox (P : ℕ → Prop) : Arsenal.Rotation.Box.{0} where
  X := ℕ
  step := Nat.succ
  fac n := if P n then 0 else 1
  θ := 1 / 2
  mark _ := .inside

theorem tickBox_correct_iff (P : ℕ → Prop) (n : ℕ) : (tickBox P).Correct n ↔ P n := by
  unfold Arsenal.Rotation.Box.Correct Arsenal.Rotation.Box.gate
  by_cases h : P n
  · have h0 : (tickBox P).fac n ≤ (tickBox P).θ := by
      show (if P n then (0 : ℝ) else 1) ≤ 1 / 2
      rw [if_pos h]; norm_num
    rw [if_pos h0]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · have h1 : ¬ (tickBox P).fac n ≤ (tickBox P).θ := by
      show ¬ (if P n then (0 : ℝ) else 1) ≤ 1 / 2
      rw [if_neg h]; norm_num
    rw [if_neg h1]
    exact ⟨fun e => absurd e (fun e' => Arsenal.Rotation.Marker.noConfusion e'), fun e => absurd e h⟩

theorem tickBox_iterate (P : ℕ → Prop) (n : ℕ) : (tickBox P).step^[n] (0 : ℕ) = n := by
  show Nat.succ^[n] 0 = n
  rw [Nat.succ_iterate, zero_add]

/-- **The tick box passes exactly when every tick's statement holds.** -/
theorem tickBox_complete_iff (P : ℕ → Prop) : (tickBox P).DMPComplete (0 : ℕ) ↔ ∀ n, P n := by
  unfold Arsenal.Rotation.Box.DMPComplete
  refine forall_congr' fun n => ?_
  rw [tickBox_iterate]
  exact tickBox_correct_iff P n

/-- **The tick box is an observable system** (draft 5, II.4.1): the tick box of `P` passes from tick `0` exactly when the observable
system with the ticks as states, the successor as step and `P` as its claim has a DMP-complete one-box description
(IM, `Arsenal.Observable`). -/
theorem tickBox_observable (P : ℕ → Prop) :
    (tickBox P).DMPComplete (0 : ℕ) ↔
      (⟨ℕ, Nat.succ, P, Classical.decPred P⟩ : Arsenal.Observable).box.DMPComplete (0 : ℕ) := by
  rw [tickBox_complete_iff]
  refine Iff.trans ?_ ((⟨ℕ, Nat.succ, P, Classical.decPred P⟩ : Arsenal.Observable).box_complete_iff (0 : ℕ)).symm
  have hit : ∀ n, (Nat.succ^[n] (0 : ℕ)) = n := fun n => by rw [Nat.succ_iterate, zero_add]
  constructor
  · intro h n
    change P (Nat.succ^[n] 0)
    rw [hit]
    exact h n
  · intro h n
    have := h n
    change P (Nat.succ^[n] 0) at this
    rwa [hit] at this

/-- **One failing tick makes the box fail.** -/
theorem tickBox_wrong (P : ℕ → Prop) (n : ℕ) (h : ¬ P n) : ¬ (tickBox P).DMPComplete (0 : ℕ) :=
  fun hc => h ((tickBox_complete_iff P).1 hc n)

/-! ## The card box -/

/-- **The card box**: every tick carries the card's one open step. -/
def cardBox (Pr : API.Problem) (i : Pr.Input) : Arsenal.Rotation.Box.{0} := tickBox (fun _ => Pr.Open i)

/-- **The card box passes exactly when the card's open step holds.** -/
theorem cardBox_complete_iff (Pr : API.Problem) (i : Pr.Input) : (cardBox Pr i).DMPComplete (0 : ℕ) ↔ Pr.Open i :=
  (tickBox_complete_iff _).trans ⟨fun h => h 0, fun h _ => h⟩

/-- **A passing card box gives the card's conclusion.** -/
theorem cardBox_concl (Pr : API.Problem) (i : Pr.Input) (h : (cardBox Pr i).DMPComplete (0 : ℕ)) : Pr.Concl i :=
  Pr.holds i ((cardBox_complete_iff Pr i).1 h)

/-! ## The five boxes -/

/-- **GRH**: the box of a finite zero model passes exactly when the sign holds at every scale. -/
theorem grh_box_iff (i : API.GRH.Input) :
    (cardBox API.GRH.problem i).DMPComplete (0 : ℕ) ↔ Unified.ScaleSign i.Z.t :=
  cardBox_complete_iff API.GRH.problem i

/-- **GRH from Mathlib's statement**: for a model of zeta's zeros with nonnegative weights, the box passes under the
Riemann hypothesis (an `External` slot). -/
theorem grh_box_of_RH (hExt : API.External "Mathlib: RiemannHypothesis (the statement; open)" Unified.ExtRH)
    (i : API.GRH.Input) (hw : ∀ j, ∃ r : ℝ, 0 ≤ r ∧ i.Z.w j = r) (hz : Unified.StripZeros riemannZeta i.Z.γ) :
    (cardBox API.GRH.problem i).DMPComplete (0 : ℕ) :=
  (cardBox_complete_iff API.GRH.problem i).2 (API.GRH.tie_in hExt i hw hz).1

/-- **P vs NP**: a passing box gives the crossing bound, every refutation of size at least `e^{θ b}`. -/
theorem np_box_concl (i : API.NP.Input) (h : (cardBox API.NP.problem i).DMPComplete (0 : ℕ)) :
    ∀ P, i.Refutes P → Real.exp (i.θ * i.b) ≤ P.card :=
  cardBox_concl API.NP.problem i h

/-- **BSD**: the box of a curve passes exactly when BSD holds for it. -/
theorem bsd_box_iff (i : API.BSD.Input) :
    (cardBox API.BSD.problem i).DMPComplete (0 : ℕ) ↔ Arsenal.BSD.BSDStatement i.W :=
  cardBox_complete_iff API.BSD.problem i

/-- **Hodge**: the box passes exactly when the card's open step holds for the input. -/
theorem hodge_box_iff (i : API.Hodge.Input) :
    (cardBox API.Hodge.problem i).DMPComplete (0 : ℕ) ↔ API.Hodge.problem.Open i :=
  cardBox_complete_iff API.Hodge.problem i

/-- **Hodge for divisors**: in codimension one the box passes (Lefschetz (1,1), with its named inputs). -/
theorem hodge_box_divisor (D : API.Hodge.DivisorInput) : (cardBox API.Hodge.problem D.toInput).DMPComplete (0 : ℕ) :=
  (cardBox_complete_iff API.Hodge.problem D.toInput).2 D.holds

/-- **GU**: the box whose ticks carry charge quantisation passes, proved. -/
theorem gu_box : (tickBox (fun _ => API.ChargeQuantisation)).DMPComplete (0 : ℕ) :=
  (tickBox_complete_iff _).2 fun _ => API.chargeQuantisation

end ProofPhase.ETM

end
