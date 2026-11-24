/-
The rotation round: the one box, its one command, and the marker test of DMP-completeness (2026-11-24).
Released under Apache 2.0.

Note: `docs/unified/ROTATION-API.md`.
-/

import ProofPhase.API
import Arsenal.Rotation

/-!
# The rotation API: one box, one command, one test

**The box (`Box δ`).** A running system `S : RunSys δ` (`ETM/RunSys.lean`: `step`, the gate factor `fac`, `mass`, the
ledger law `pays`) with one command, the step at the one shared gate (the universal tick), a **gate margin** `θ` with
`e^δ θ < 1` (a cost above the floor), and the **marker** `mark x` the box produces at each state: `inside` or `r136a1`
(DMP's marker for "outside", in place of an unproved step). There is no outside input: the outside is read through the same
gate by the half-turn (`Gate`, `complete_halfTurn`), whose flux law is the same on both sides.

**The test.** The gate's own verdict at `x` is `inside` when `fac x ≤ θ` and `r136a1` otherwise (`gate`). The marker is
**correct** at `x` when it agrees with the gate (`Correct`); never with an outside oracle. `DMPComplete x` says every step
from `x` gives the correct marker. A wrong marker at some tick means not DMP-complete.

**The theorems.**
1. *One-box certificate* (`onebox_certificate`): correct at the start and one step at the shared gate preserves
   correctness, hence correct at every tick (induction). *Scale version* (`scale_certificate`, `onebox_everywhere`): if
   every scale's box is reconstructed from the one box through its gate (`SharedGate`, carried as the named hypothesis
   `OpenStep "III.64 ..."`, never proved here), a box certified at one scale is correct at every scale. Without III.64 the
   step fails in the only way it can: a wrong marker at some scale refutes the sharing (`not_shared_of_wrong`).
2. *Universality and its price*: the ETM (`ETM/Machine.lean`) is a box (`etmBox`, balance marker); whether it is
   DMP-complete from a description is exactly whether the description runs forever (`etmBox_complete_iff`), so
   `DMPComplete` is not decidable for all content (`etmBox_complete_undecidable`, from `etm_balance_undecidable`). On
   the contraction class (cost above the floor) the same test settles: from the explicit tick
   `balanceBound M ε q` on, every marker is correct (`settles_of_contracting`), so `DMPComplete` is the finite check of
   the ticks below the bound (`complete_iff_bounded`).

**Vacuity checks.** A box whose marker is its own gate verdict is always DMP-complete (`selfMarked_complete`): the class
has content only once the marker is fixed by the system, not read off the gate afterwards. A box with a wrong marker
exists (`exists_not_complete`). Sharing the gate alone is free: every box's gate verdict is read through its trace into
the terminal object (`gate_through_trace`); the content of III.64 is that the marker travels with the gate.

**The core lives in IM.** The marker, the two-sided gate and the generic box with its test are IM's
(`Arsenal/Rotation.lean`, the arsenal of `StevenHrovat/im`). A box here is IM's box with a running system's ledger under
it: `toArsenal` forgets the mass, the definitions agree with IM's by `rfl` (`toArsenal_gate`, `toArsenal_correct`,
`toArsenal_dmpComplete`), and the one-box certificate, its exact form, the half-turn and the pull-back along a
reconstruction are IM's theorems, applied here. What stays here is what needs the ledger: the margin as a cost above the
floor, the balance marker, the contraction class, the universal machine.

The instances (Yang-Mills, Navier-Stokes, the half-turn of the plaquette layer) are in `ETM/RotationInstances.lean`.
No axioms beyond the standard ones; the open statement III.64 is a hypothesis, never an axiom.
-/

open Finset Nat.Partrec Nat.Partrec.Code

noncomputable section

namespace ProofPhase.ETM

universe u v w

/-! ## 1. The marker, the box, the gate, the test -/

-- The marker a step produces, `inside` or `r136a1`, is IM's (`Arsenal.Rotation.Marker`).
open Arsenal.Rotation (Marker)

/-- **The box.** A running system with one command (the step at the one shared gate), a gate margin `θ` that is a cost
above the floor (`e^δ θ < 1`), and the marker the box produces at each state. -/
structure Box (δ : ℝ) where
  /-- The running system: its step is the one command, its factor the gate factor. -/
  S : RunSys.{u} δ
  /-- The gate margin. -/
  θ : ℝ
  /-- The margin is a cost above the floor. -/
  margin : Real.exp δ * θ < 1
  /-- The marker the box produces at each state. -/
  mark : S.X → Marker

namespace Box

variable {δ : ℝ}

/-- **IM's box under this box**: the states, the one command, the gate factor, the margin and the marker; the mass and
the ledger law are forgotten. -/
def toArsenal (B : Box.{u} δ) : Arsenal.Rotation.Box.{u} := ⟨B.S.X, B.S.step, B.S.fac, B.θ, B.mark⟩

/-- **The gate's own verdict**: `inside` when the gate factor is within the margin, `r136a1` otherwise. -/
def gate (B : Box.{u} δ) (x : B.S.X) : Marker := if B.S.fac x ≤ B.θ then .inside else .r136a1

/-- **The marker is correct** at `x`: it agrees with the gate's own factor (no outside oracle). -/
def Correct (B : Box.{u} δ) (x : B.S.X) : Prop := B.mark x = B.gate x

/-- **DMP-complete from `x`**: every step from `x` gives the correct marker. -/
def DMPComplete (B : Box.{u} δ) (x : B.S.X) : Prop := ∀ n, B.Correct (B.S.step^[n] x)

/-- **The test settles from `x`**: from some tick on, every marker is correct. -/
def Settles (B : Box.{u} δ) (x : B.S.X) : Prop := ∃ N, ∀ n ≥ N, B.Correct (B.S.step^[n] x)

/-- The gate is IM's gate. -/
theorem toArsenal_gate (B : Box.{u} δ) (x : B.S.X) : B.toArsenal.gate x = B.gate x := rfl

/-- Correctness is IM's correctness. -/
theorem toArsenal_correct (B : Box.{u} δ) (x : B.S.X) : B.toArsenal.Correct x ↔ B.Correct x := Iff.rfl

/-- DMP-completeness is IM's DMP-completeness. -/
theorem toArsenal_dmpComplete (B : Box.{u} δ) (x : B.S.X) : B.toArsenal.DMPComplete x ↔ B.DMPComplete x := Iff.rfl

theorem gate_eq_inside_iff (B : Box.{u} δ) (x : B.S.X) : B.gate x = .inside ↔ B.S.fac x ≤ B.θ :=
  B.toArsenal.gate_eq_inside_iff x

theorem gate_eq_r136a1_iff (B : Box.{u} δ) (x : B.S.X) : B.gate x = .r136a1 ↔ B.θ < B.S.fac x :=
  B.toArsenal.gate_eq_r136a1_iff x

/-- DMP-completeness is carried along the run. -/
theorem DMPComplete.step {B : Box.{u} δ} {x : B.S.X} (h : B.DMPComplete x) : B.DMPComplete (B.S.step x) :=
  fun n => by
    have := h (n + 1)
    rwa [Function.iterate_succ_apply] at this

theorem DMPComplete.settles {B : Box.{u} δ} {x : B.S.X} (h : B.DMPComplete x) : B.Settles x := ⟨0, fun n _ => h n⟩

/-! ## 2. The one-box certificate -/

/-- **The one-box certificate.** If the marker is correct at the start, and one step at the gate shared by every tick
preserves correctness, then the marker is correct at every tick. -/
theorem onebox_certificate (B : Box.{u} δ) {x₀ : B.S.X} (h0 : B.Correct x₀)
    (hstep : ∀ x, B.Correct x → B.Correct (B.S.step x)) : B.DMPComplete x₀ :=
  B.toArsenal.onebox_certificate h0 hstep

/-- **The certificate is exact along the run**: DMP-complete from `x₀` exactly when the start is correct and each step
of the run carries correctness to the next. -/
theorem dmpComplete_iff_orbit (B : Box.{u} δ) (x₀ : B.S.X) : B.DMPComplete x₀ ↔
    B.Correct x₀ ∧ ∀ n, B.Correct (B.S.step^[n] x₀) → B.Correct (B.S.step^[n + 1] x₀) :=
  B.toArsenal.dmpComplete_iff_orbit x₀

/-! ## 3. The half-turn: the outside is read through the same gate -/

-- The two-sided gate (the reading from inside, the reading after the half-turn, and the flux law, the same on both
-- sides) and the half-turn theorem `Gate.halfTurn` are IM's (`Arsenal.Rotation.Box.Gate`).
open Arsenal.Rotation.Box (Gate)

/-- The test with the gate read through a reading `r` instead of the factor. -/
def CompleteVia (B : Box.{u} δ) (r : B.S.X → ℝ) (x : B.S.X) : Prop :=
  ∀ n, B.mark (B.S.step^[n] x) = if r (B.S.step^[n] x) ≤ B.θ then .inside else .r136a1

/-- **No outside input**: for a two-sided gate whose inside reading is the gate factor, the test read after the half-turn
is the test. -/
theorem complete_halfTurn (B : Box.{u} δ) (g : Gate B.S.X ℝ) (hin : ∀ x, g.inner x = B.S.fac x) (x : B.S.X) :
    B.CompleteVia g.outer x ↔ B.DMPComplete x :=
  B.toArsenal.complete_halfTurn g hin x

/-! ## 4. The scale version: III.64 as a named hypothesis -/

/-- **The gate is shared across scales** (the content of the paper's one assumption III.64): every scale's box has the same
margin and is reconstructed from the one box through its gate, by a morphism of running systems (step, gate factor and
mass preserved) that sends the scale's start to the one box's start and carries the marker. -/
def SharedGate (B : Box.{u} δ) (x₀ : B.S.X) {ι : Type w} (C : ι → Box.{v} δ) (x : ∀ j, (C j).S.X) : Prop :=
  ∀ j, (C j).θ = B.θ ∧
    ∃ φ : RunSys.Hom (C j).S B.S, φ.toFun (x j) = x₀ ∧ ∀ y, B.mark (φ.toFun y) = (C j).mark y

/-- A morphism of running systems is a reconstruction of IM's boxes (it keeps the step and the gate factor). -/
def homArsenal {B : Box.{u} δ} {C : Box.{v} δ} (φ : RunSys.Hom C.S B.S) :
    Arsenal.Rotation.Box.Hom C.toArsenal B.toArsenal :=
  ⟨φ.toFun, φ.step_comm, φ.fac_eq⟩

/-- Along a reconstruction map, correctness is read on the one box. -/
theorem correct_hom {B : Box.{u} δ} {C : Box.{v} δ} (φ : RunSys.Hom C.S B.S) (hθ : C.θ = B.θ)
    (hmk : ∀ y, B.mark (φ.toFun y) = C.mark y) (y : C.S.X) : C.Correct y ↔ B.Correct (φ.toFun y) :=
  Arsenal.Rotation.Box.correct_hom (homArsenal φ) hθ hmk y

/-- DMP-completeness pulls back along a reconstruction map. -/
theorem dmpComplete_hom {B : Box.{u} δ} {C : Box.{v} δ} (φ : RunSys.Hom C.S B.S) (hθ : C.θ = B.θ)
    (hmk : ∀ y, B.mark (φ.toFun y) = C.mark y) {y : C.S.X} (h : B.DMPComplete (φ.toFun y)) : C.DMPComplete y :=
  Arsenal.Rotation.Box.dmpComplete_hom (homArsenal φ) hθ hmk h

/-- **The scale certificate.** A box certified on the one box is correct at every scale, provided the gate is shared
across scales. The sharing is the paper's one assumption III.64, carried as a named hypothesis and not proved. -/
theorem scale_certificate (B : Box.{u} δ) {x₀ : B.S.X} {ι : Type w} (C : ι → Box.{v} δ) (x : ∀ j, (C j).S.X)
    (hB : B.DMPComplete x₀)
    (hX64 : ProofPhase.API.OpenStep
      "III.64: the one box is a running, DMP-complete system; every tick at every scale is reconstructed from its gate"
      (SharedGate B x₀ C x)) :
    ∀ j, (C j).DMPComplete (x j) := fun j => by
  obtain ⟨hθ, φ, hx, hmk⟩ := hX64 j
  exact dmpComplete_hom φ hθ hmk (by rw [hx]; exact hB)

/-- **One box, every scale**: the one-box certificate (start correct, the shared step preserves correctness) and III.64
give the correct marker at every tick of every scale. -/
theorem onebox_everywhere (B : Box.{u} δ) {x₀ : B.S.X} (h0 : B.Correct x₀)
    (hstep : ∀ x, B.Correct x → B.Correct (B.S.step x)) {ι : Type w} (C : ι → Box.{v} δ) (x : ∀ j, (C j).S.X)
    (hX64 : ProofPhase.API.OpenStep
      "III.64: the one box is a running, DMP-complete system; every tick at every scale is reconstructed from its gate"
      (SharedGate B x₀ C x)) :
    ∀ j, (C j).DMPComplete (x j) :=
  scale_certificate B C x (B.onebox_certificate h0 hstep) hX64

/-- **Falsifiability of the sharing**: a certified one box and a scale with a wrong marker refute III.64 for that family. -/
theorem not_shared_of_wrong (B : Box.{u} δ) {x₀ : B.S.X} {ι : Type w} (C : ι → Box.{v} δ) (x : ∀ j, (C j).S.X)
    (hB : B.DMPComplete x₀) (j : ι) (hj : ¬ (C j).DMPComplete (x j)) : ¬ SharedGate B x₀ C x :=
  fun h => hj (scale_certificate B C x hB h j)

/-- The sharing is satisfiable: the one box shares its gate with itself, at every scale. -/
theorem sharedGate_self (B : Box.{u} δ) (x₀ : B.S.X) (ι : Type w) :
    SharedGate B x₀ (fun _ : ι => B) (fun _ => x₀) :=
  fun _ => ⟨rfl, RunSys.Hom.id B.S, rfl, fun _ => rfl⟩

/-! ## 5. Vacuity checks -/

/-- **The self-marked box**: a running system marked by its own gate verdict. -/
def selfMarked (S : RunSys.{u} δ) (θ : ℝ) (hθ : Real.exp δ * θ < 1) : Box.{u} δ :=
  ⟨S, θ, hθ, fun x => if S.fac x ≤ θ then .inside else .r136a1⟩

/-- **A marker read off the gate afterwards is always right**: the class has content only once the marker is fixed by
the system. -/
theorem selfMarked_complete (S : RunSys.{u} δ) (θ : ℝ) (hθ : Real.exp δ * θ < 1) (x : S.X) :
    (selfMarked S θ hθ).DMPComplete x := fun _ => rfl

/-- **A wrong marker exists**: the one-point system (factor `0`, margin `0`, gate `inside`) marked `r136a1` is not
DMP-complete. -/
theorem exists_not_complete : ∃ (B : Box.{u} δ) (x : B.S.X), ¬ B.DMPComplete x := by
  refine ⟨⟨RunSys.point.{u} δ, 0, by rw [mul_zero]; exact one_pos, fun _ => .r136a1⟩, PUnit.unit, fun h => ?_⟩
  have h0 : Marker.r136a1 = if (0 : ℝ) ≤ 0 then Marker.inside else Marker.r136a1 := h 0
  simp only [le_refl, ↓reduceIte] at h0
  exact Marker.noConfusion h0

/-- **Sharing the gate alone is free**: every box's gate verdict is the verdict read on its image in the terminal object
(`RunSys.univ`), through the trace. What III.64 adds is that the marker travels with the gate. -/
theorem gate_through_trace (B : Box.{u} δ) (x : B.S.X) :
    B.gate x = if (RunSys.univ.{u} δ).fac ((B.S.trace : RunSys.Hom B.S (RunSys.univ.{u} δ)).toFun x) ≤ B.θ
      then .inside else .r136a1 := by
  unfold gate
  rw [(B.S.trace : RunSys.Hom B.S (RunSys.univ.{u} δ)).fac_eq]

/-! ## 6. The balance marker; the contraction class settles the test -/

/-- **The balance marker**: the box reports `inside` once its run is within `ε` of balance (mass at most `ε`), `r136a1`
before. -/
def ofBalance (S : RunSys.{u} δ) (θ : ℝ) (hθ : Real.exp δ * θ < 1) (ε : ℝ) : Box.{u} δ :=
  ⟨S, θ, hθ, fun x => if S.mass x ≤ ε then .inside else .r136a1⟩

/-- On the contraction class, with the margin of the class, the gate reads `inside` at every state. -/
theorem gate_inside_of_contracting (S : RunSys.{u} δ) {θ : ℝ} (hS : S.Contracting θ) (ε : ℝ) (x : S.X) :
    (ofBalance S θ hS.2 ε).gate x = .inside :=
  ((ofBalance S θ hS.2 ε).gate_eq_inside_iff x).2 (hS.1 x)

/-- **On the contraction class the test settles, by the explicit bound**: from tick `balanceBound M ε q` on (any rational
`q` with `e^δ θ ≤ q < 1`, start mass at most `M`), every balance marker is correct. -/
theorem settles_of_contracting (S : RunSys.{u} δ) {θ : ℝ} (hS : S.Contracting θ) (x : S.X) {M ε q : ℚ}
    (hq : Real.exp δ * θ ≤ q) (hq1 : q < 1) (hM : S.mass x ≤ M) (hε : 0 < ε) :
    ∀ n ≥ balanceBound M ε q, (ofBalance S θ hS.2 ε).Correct (S.step^[n] x) := by
  intro n hn
  have hb := S.reaches_of_contracting hS x hq hq1 hM hε n hn
  unfold Correct
  rw [gate_inside_of_contracting S hS]
  show (if S.mass (S.step^[n] x) ≤ (ε : ℝ) then Marker.inside else Marker.r136a1) = Marker.inside
  exact ite_eq_left_iff.2 fun h => absurd hb h

/-- **On the contraction class `DMPComplete` is a finite check**: it holds exactly when the markers below the explicit
bound are correct. -/
theorem complete_iff_bounded (S : RunSys.{u} δ) {θ : ℝ} (hS : S.Contracting θ) (x : S.X) {M ε q : ℚ}
    (hq : Real.exp δ * θ ≤ q) (hq1 : q < 1) (hM : S.mass x ≤ M) (hε : 0 < ε) :
    (ofBalance S θ hS.2 ε).DMPComplete x ↔
      ∀ n < balanceBound M ε q, (ofBalance S θ hS.2 ε).Correct (S.step^[n] x) := by
  refine ⟨fun h n _ => h n, fun h n => ?_⟩
  rcases lt_or_ge n (balanceBound M ε q) with hn | hn
  · exact h n hn
  · exact settles_of_contracting S hS x hq hq1 hM hε n hn

/-- On the contraction class the test settles from every state. -/
theorem settles_of_contracting' (S : RunSys.{u} δ) {θ : ℝ} (hS : S.Contracting θ) (x : S.X) {ε : ℚ} (hε : 0 < ε) :
    (ofBalance S θ hS.2 ε).Settles x := by
  obtain ⟨q, hq, hq1⟩ := exists_rat_btwn hS.2
  obtain ⟨M, hM⟩ := exists_rat_gt (S.mass x)
  exact ⟨_, settles_of_contracting S hS x hq.le (by exact_mod_cast hq1) hM.le hε⟩

end Box

/-! ## 7. The universal machine is a box; the price of universality -/

open Box

/-- **The ETM as a box**: margin `1/2` (a cost above the floor `0`), balance marker at `ε = 1/2`. The ETM is lossless
(factor `1`), so its gate reads `r136a1` at every state: it sits outside the contraction class. -/
def etmBox : Box.{0} 0 := ofBalance etm (1 / 2) (by rw [Real.exp_zero, one_mul]; norm_num) (1 / 2)

theorem etmBox_gate (s : EState) : etmBox.gate s = .r136a1 :=
  ite_eq_right_iff.2 fun h => absurd (show (1 : ℝ) ≤ 1 / 2 from h) (by norm_num)

/-- At every state the ETM's marker is correct exactly while the content has not balanced. -/
theorem etmBox_correct_iff (s : EState) : etmBox.Correct s ↔ ¬ etm.mass s ≤ 1 / 2 := by
  unfold Correct
  rw [etmBox_gate]
  show (if etm.mass s ≤ 1 / 2 then Marker.inside else Marker.r136a1) = Marker.r136a1 ↔ _
  by_cases h : etm.mass s ≤ 1 / 2
  · simp only [h, ↓reduceIte, not_true_eq_false, iff_false]
    exact fun e => Marker.noConfusion e
  · simp only [h, ↓reduceIte, not_false_eq_true]

/-- **The ETM is DMP-complete from a description exactly when the description runs forever.** -/
theorem etmBox_complete_iff (c : Code) (n : ℕ) : etmBox.DMPComplete (start c n) ↔ ¬ (eval c n).Dom := by
  rw [← etm_runs c n (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)]
  exact ⟨fun h ⟨k, hk⟩ => (etmBox_correct_iff _).1 (h k) hk,
    fun h k => (etmBox_correct_iff _).2 fun hk => h ⟨k, hk⟩⟩

/-- **`DMPComplete` is not decidable for all content**: no computable predicate decides it for the ETM (from
`etm_balance_undecidable`). The box's step and marker are primitive recursive (`estep_primrec`, `halted_primrec`); the
test is not computable. -/
theorem etmBox_complete_undecidable (n : ℕ) : ¬ ComputablePred fun c : Code => etmBox.DMPComplete (start c n) :=
  fun h => etm_balance_undecidable n (ε := 1 / 2) (by norm_num) (by norm_num)
    (ComputablePred.of_eq h.not fun c => by
      rw [etmBox_complete_iff, not_not, etm_runs c n (by norm_num) (by norm_num)])

/-- **On the ETM the test settles exactly when the description runs forever** (balance, once reached, is kept). -/
theorem etmBox_settles_iff (c : Code) (n : ℕ) : etmBox.Settles (start c n) ↔ ¬ (eval c n).Dom := by
  refine ⟨fun ⟨N, hN⟩ hd => ?_, fun h => ((etmBox_complete_iff c n).2 h).settles⟩
  obtain ⟨k, hk⟩ := (etm_runs c n (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).2 hd
  obtain ⟨x, hx⟩ := (etm_balanced_iff c n k (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).1 hk
  have hb : etm.Balanced (1 / 2) (start c n) (max N k) :=
    (etm_balanced_iff c n _ (by norm_num) (by norm_num)).2 ⟨x, evaln_mono (le_max_right N k) hx⟩
  exact (etmBox_correct_iff _).1 (hN _ (le_max_left N k)) hb

/-- **Settling is not decidable for all content either.** -/
theorem etmBox_settles_undecidable (n : ℕ) : ¬ ComputablePred fun c : Code => etmBox.Settles (start c n) :=
  fun h => etm_balance_undecidable n (ε := 1 / 2) (by norm_num) (by norm_num)
    (ComputablePred.of_eq h.not fun c => by
      rw [etmBox_settles_iff, not_not, etm_runs c n (by norm_num) (by norm_num)])

/-- **The edge of the test.** Cost above the floor: the balance-marker test settles from the explicit tick
`balanceBound M ε q` on, so `DMPComplete` is a finite check. The lossless universal machine: `DMPComplete` and settling
are both undecidable over its descriptions. -/
theorem rotation_edge :
    (∀ (δ : ℝ) (S : RunSys.{u} δ) (θ : ℝ) (hS : S.Contracting θ) (x : S.X) (M ε q : ℚ),
      Real.exp δ * θ ≤ q → q < 1 → S.mass x ≤ M → 0 < ε →
        ∀ n ≥ balanceBound M ε q, (ofBalance S θ hS.2 ε).Correct (S.step^[n] x)) ∧
    (∀ (c : Code) (n : ℕ), etmBox.DMPComplete (start c n) ↔ ¬ (eval c n).Dom) ∧
    (∀ n, ¬ ComputablePred fun c : Code => etmBox.DMPComplete (start c n)) ∧
    (∀ n, ¬ ComputablePred fun c : Code => etmBox.Settles (start c n)) :=
  ⟨fun _ S _ hS x _ _ _ hq hq1 hM hε => settles_of_contracting S hS x hq hq1 hM hε, etmBox_complete_iff,
    etmBox_complete_undecidable, etmBox_settles_undecidable⟩

end ProofPhase.ETM
