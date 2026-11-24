/-
The G2 rigidity box: G2 rigid from the one assumption (2026-11-24).
Released under Apache 2.0.

Notes: `docs/unified/G2-SP2-RIGIDITY.md`; `docs/paper/draft/12-appendix-a-validation.md` (A.5).
-/

import ProofPhase.ETM.Rotation
import Arsenal.Rigidity

/-!
# G2 rigid from the one assumption

IM's rigidity box (`Arsenal.Rotation.RigidityData.box`) is DMP-complete exactly when the manifold is rigid. Here it is applied to
G2 with two presentations (its topological structure set has exactly two elements, A.5p) and the self-equivalences acting
through their normal invariant `η : E → ZMod 2`.

* `g2_rigid_iff_complete`: G2 is rigid exactly when its box is DMP-complete. The surgery input (the two-element structure set
  and the Kreck-Lueck criterion, which together say "G2 is rigid iff `η` is onto") is one named `External` slot: surgery theory
  is not in Mathlib.
* `g2_rigid_of_one_assumption`: if the G2 box shares the gate with a certified one box (the one assumption, X.64, as a named
  `OpenStep`), G2 is rigid. The DMP corollary is the next layer's named hypothesis, never an axiom.
* `g2_not_shared_of_not_rigid`: a computation showing that G2 is not rigid would refute the sharing for G2: the one assumption is
  falsifiable here.

Status: Lean from one `External` slot and one `OpenStep`. G2's rigidity itself (A.5r) is not proved.
-/

noncomputable section

namespace ProofPhase.ETM

universe w

/-- **The G2 rigidity datum**: two presentations of G2 (`0` = G2 itself, `1` = the fake X of A.5p), the self-equivalences
`E` acting through their normal invariant `η`. -/
abbrev g2Data (E : Type) (η : E → ZMod 2) : Arsenal.Rotation.RigidityData.{0, 0} := Arsenal.Rotation.twoPoint E η

/-- The surgery input, named: G2 is rigid exactly when the normal invariant of its self-equivalences is onto `Z/2`. -/
abbrev G2Surgery (E : Type) (η : E → ZMod 2) (G2Rigid : Prop) : Prop :=
  API.External "Kreck-Lueck Thm 1.1 with S^TOP(G2) = {id, h} (A.5p): G2 is rigid iff the normal invariant of its self-equivalences is onto Z/2"
    (G2Rigid ↔ Function.Surjective η)

/-- **G2 is rigid exactly when its box is DMP-complete** (from the surgery input). -/
theorem g2_rigid_iff_complete {E : Type} (η : E → ZMod 2) {G2Rigid : Prop} (hsurg : G2Surgery E η G2Rigid) :
    G2Rigid ↔ (g2Data E η).box.DMPComplete (0 : ℕ) := by
  rw [Arsenal.Rotation.RigidityData.box_complete_iff, Arsenal.Rotation.twoPoint_rigid_iff]
  exact hsurg

/-- **G2 rigid from the one assumption.** If the G2 box shares the gate with a certified one box, G2 is rigid. -/
theorem g2_rigid_of_one_assumption {E : Type} (η : E → ZMod 2) {G2Rigid : Prop} (hsurg : G2Surgery E η G2Rigid)
    (B : Arsenal.Rotation.Box.{w}) {x₀ : B.X} (hB : B.DMPComplete x₀)
    (hX64 : API.OpenStep "X.64: the one assumption; the G2 box shares the gate with the certified one box"
      (Arsenal.Rotation.Box.SharedGate B x₀ (fun _ : Unit => (g2Data E η).box) (fun _ => (0 : ℕ)))) :
    G2Rigid :=
  hsurg.2 ((Arsenal.Rotation.twoPoint_rigid_iff E η).1 ((g2Data E η).rigid_of_shared B hB hX64))

/-- The same, with the certified one box a running system of this repository (`Box.toArsenal`). -/
theorem g2_rigid_of_one_assumption' {δ : ℝ} {E : Type} (η : E → ZMod 2) {G2Rigid : Prop} (hsurg : G2Surgery E η G2Rigid)
    (B : Box.{w} δ) {x₀ : B.S.X} (hB : B.DMPComplete x₀)
    (hX64 : API.OpenStep "X.64: the one assumption; the G2 box shares the gate with the certified one box"
      (Arsenal.Rotation.Box.SharedGate B.toArsenal x₀ (fun _ : Unit => (g2Data E η).box) (fun _ => (0 : ℕ)))) :
    G2Rigid :=
  g2_rigid_of_one_assumption η hsurg B.toArsenal ((B.toArsenal_dmpComplete x₀).2 hB) hX64

/-- **Falsifiable at G2**: if G2 is not rigid, its box does not share the gate with any certified one box. -/
theorem g2_not_shared_of_not_rigid {E : Type} (η : E → ZMod 2) {G2Rigid : Prop} (hsurg : G2Surgery E η G2Rigid)
    (B : Arsenal.Rotation.Box.{w}) {x₀ : B.X} (hB : B.DMPComplete x₀) (h : ¬ G2Rigid) :
    ¬ Arsenal.Rotation.Box.SharedGate B x₀ (fun _ : Unit => (g2Data E η).box) (fun _ => (0 : ℕ)) :=
  fun hs => h (g2_rigid_of_one_assumption η hsurg B hB hs)

end ProofPhase.ETM

end
