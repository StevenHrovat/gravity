/-
Proof phase, generalisation phase 1: the old SU(2), `d = 4` counting and one-box statements re-derived from the generic
`d` versions (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`.
-/

import ProofPhase.General.Torus
import ProofPhase.General.SU2Instance
import ProofPhase.OneBox2.Anchor
import ProofPhase.Torus.Local
import ProofPhase.Quantum.BlockedRoute

/-!
# The `d = 4`, SU(2) statements as corollaries of the generic ones

Each theorem here has **the same type** as the old theorem named in its docstring (checked by the `example` below it,
which states the old name's type through the new proof), and is proved in one line from the generic version at `d := 4`.
Nothing in the old files is edited.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.LinkDist

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

/-! ## Counting -/

/-- `ProofPhase.OneBox2.card_near_le` from `card_near_le` at `d = 4`. -/
theorem card_near_le_four {N : ℕ} [NeZero N] :
    (univ.filter (fun u : FinLatticeSites 4 N => siteDist u 0 ≤ 1)).card ≤ 81 := by
  have h := card_near_le (d := 4) (N := N)
  norm_num at h
  exact h

/-- `ProofPhase.Torus.card_le_of_siteDist` from `card_le_of_siteDist` at `d = 4`. -/
theorem card_le_of_siteDist_four {N : ℕ} [NeZero N] {A : Finset (LatticeLink 4 N)} {r : ℕ}
    (h : ∀ e ∈ A, ∀ e' ∈ A, siteDist e.site e'.site ≤ r) : A.card ≤ 4 * (2 * r + 1) ^ 4 :=
  card_le_of_siteDist (d := 4) h

/-- The constant of the `d`-dimensional tail at `d = 4` is `24`. -/
theorem factorial_four : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]

/-- `ProofPhase.RouteA.poly_exp_le` from `poly_exp_le` at `d = 4`. -/
theorem poly_exp_le_four {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    (1 + x) ^ 4 * Real.exp (-(2 * a * x)) ≤ 24 / a ^ 4 * Real.exp a * Real.exp (-(a * x)) := by
  have h := poly_exp_le 4 ha hx
  rw [factorial_four] at h
  exact h

/-- `ProofPhase.Quantum.poly4_exp_bound` from `poly_exp_bound` at `d = 4`. -/
theorem poly4_exp_bound_four {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → (1 + x) ^ 4 * Real.exp (-(r * x)) ≤ C :=
  poly_exp_bound 4 hr


/-! ## Boxes on the torus -/

section Torus

variable {M : ℕ} [NeZero M]

/-- The generic box block at `d = 4` is the old one. -/
theorem boxBlock_four (Λ₀ : Finset (FinLatticeSites 4 M)) (t : FinLatticeSites 4 M) :
    boxBlock Λ₀ t = ProofPhase.OneBox.boxBlock Λ₀ t := by
  ext x; simp [boxBlock, ProofPhase.OneBox.boxBlock]

/-- `ProofPhase.OneBox.card_boxBlock` from `card_boxBlock` at `d = 4`. -/
theorem card_boxBlock_four (Λ₀ : Finset (FinLatticeSites 4 M)) (t : FinLatticeSites 4 M) :
    (ProofPhase.OneBox.boxBlock Λ₀ t).card ≤ 4 * Λ₀.card := by
  rw [← boxBlock_four]
  exact card_boxBlock Λ₀ t

end Torus

section Law

variable {M : ℕ → ℕ} [∀ j, NeZero (M j)]

/-- The old `OneBoxLaw` is the generic one at `SU2`, `d = 4`. -/
theorem oneBoxLaw_iff {ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))} {lam : ℝ} :
    ProofPhase.OneBox.OneBoxLaw ρ lam ↔ OneBoxLaw ρ lam := by
  unfold ProofPhase.OneBox.OneBoxLaw OneBoxLaw
  refine exists_congr fun γ => exists_congr fun D₀ => exists_congr fun nmax => and_congr Iff.rfl (and_congr Iff.rfl
    (exists_congr fun k₀ => forall_congr' fun k => forall_congr' fun _ => forall_congr' fun j => ?_))
  refine exists_congr fun Λ₀ => exists_congr fun κ => exists_congr fun P => ?_
  simp only [boxBlock_four]
  rfl

/-- The old `LawGapBddW` is the generic one at `SU2`, `d = 4`, cost `geodSU2`. -/
theorem lawGapBddW_iff {ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))} {lam : ℝ} :
    ProofPhase.V4.LawGapBddW ρ lam ↔ LawGapBddW ProofPhase.Certified.geodSU2 ρ lam := Iff.rfl

/-- `ProofPhase.OneBox.lawGapBddW_of_oneBoxLaw` from the generic `lawGapBddW_of_oneBoxLaw` at `SU2`, `d = 4`. -/
theorem lawGapBddW_of_oneBoxLaw_su2 {ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))} {lam : ℝ}
    (hlam : 0 ≤ lam) (hρ : ∀ k j, IsProbabilityMeasure (ρ k j)) (h : ProofPhase.OneBox.OneBoxLaw ρ lam) :
    ProofPhase.V4.LawGapBddW ρ lam :=
  lawGapBddW_iff.2 (lawGapBddW_of_oneBoxLaw hlam hρ (oneBoxLaw_iff.1 h))

end Law

/-! ## Same-type checks

`@old = @new := rfl` typechecks exactly when the two statements are definitionally the same proposition (proof
irrelevance does the rest). -/

example : @ProofPhase.OneBox2.card_near_le = @card_near_le_four := rfl
example : @ProofPhase.Torus.card_le_of_siteDist = @card_le_of_siteDist_four := rfl
example : @ProofPhase.RouteA.poly_exp_le = @poly_exp_le_four := rfl
example : @ProofPhase.Quantum.poly4_exp_bound = @poly4_exp_bound_four := rfl
example : @ProofPhase.OneBox.card_boxBlock = @card_boxBlock_four := rfl
example : @ProofPhase.OneBox.lawGapBddW_of_oneBoxLaw = @lawGapBddW_of_oneBoxLaw_su2 := rfl

end ProofPhase.General
