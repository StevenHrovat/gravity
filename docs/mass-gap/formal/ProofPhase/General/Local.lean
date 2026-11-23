/-
Proof phase, generalisation phase 1: sets of bounded physical extent have at most `d (2⌊R/a_k⌋ + 1)^d` links
(2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`.
-/

import ProofPhase.General.Filter
import ProofPhase.General.Counting
import ProofPhase.Torus.Local

/-!
# Physical extent and the link count, in dimension `d`

`ProofPhase.Torus.card_le_of_physExtent` (a family of physical extent `≤ R` has at most `4 (2⌊R/a_k⌋ + 1)⁴` fine
links at level `k`) in dimension `d`, from the counting layer, with the `d = 4` statements re-derived. This is the
counting step behind `ObsTransferPhys` (`Torus/Local`) and the constants `K_R = 4 (2r + 1)⁴` of `OneBox/Fine`,
`OneBox2/Cube` and `V3/CondMass`.
-/

open MeasureTheory Finset OneScale.LinkDist

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

section Geometry

variable {d N : ℕ} [NeZero N]

/-- Physical extent `≤ R` at level `k` bounds the lattice diameter by `⌊R/a_k⌋`. -/
theorem siteDist_le_floor {T : Tuning} {k : ℕ} {A : Finset (LatticeLink d N)} {R : ℝ} (h : PhysExtent T k A R) :
    ∀ e ∈ A, ∀ e' ∈ A, siteDist e.site e'.site ≤ ⌊R / T.a k⌋₊ := by
  intro e he e' he'
  apply Nat.le_floor
  rw [le_div_iff₀ (T.a_pos k)]
  have := h e he e' he'
  unfold linkDist at this
  rw [mul_comm] at this
  exact this

/-- **A family of physical extent `≤ R` has at most `d (2⌊R/a_k⌋ + 1)^d` fine links at level `k`.** -/
theorem card_le_of_physExtent {T : Tuning} {k : ℕ} {A : Finset (LatticeLink d N)} {R : ℝ}
    (h : PhysExtent T k A R) : A.card ≤ d * (2 * ⌊R / T.a k⌋₊ + 1) ^ d :=
  card_le_of_siteDist (siteDist_le_floor h)

end Geometry

/-! ## The `d = 4` instances -/

section Instance

variable {N : ℕ} [NeZero N]

/-- `ProofPhase.Torus.siteDist_le_floor` at `d = 4`. -/
theorem siteDist_le_floor_four {T : Tuning} {k : ℕ} {A : Finset (LatticeLink 4 N)} {R : ℝ}
    (h : ProofPhase.PhysExtent T k A R) : ∀ e ∈ A, ∀ e' ∈ A, siteDist e.site e'.site ≤ ⌊R / T.a k⌋₊ :=
  siteDist_le_floor h

/-- `ProofPhase.Torus.card_le_of_physExtent` at `d = 4`. -/
theorem card_le_of_physExtent_four {T : Tuning} {k : ℕ} {A : Finset (LatticeLink 4 N)} {R : ℝ}
    (h : ProofPhase.PhysExtent T k A R) : A.card ≤ 4 * (2 * ⌊R / T.a k⌋₊ + 1) ^ 4 :=
  card_le_of_physExtent h

example : @ProofPhase.Torus.siteDist_le_floor = @siteDist_le_floor_four := rfl
example : @ProofPhase.Torus.card_le_of_physExtent = @card_le_of_physExtent_four := rfl

end Instance

end ProofPhase.General
