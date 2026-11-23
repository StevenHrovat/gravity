/-
Proof phase, generalisation phase 1b: the ported generic theorems at SU(N) (2026-11-24). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 1b.
-/

import ProofPhase.General.Cube
import ProofPhase.General.Recursion
import ProofPhase.General.SUNSubst

/-!
# The ported one-box chain and recursion lemma at SU(N)

`SUN N` is an instance of the gauge-group package (`SUN.lean`) and is Hausdorff (a subtype of the matrices), so the
generic theorems of phase 1b apply to it for every `N` and every dimension `d`. Four examples, each a one-line
corollary of the generic theorem: the decay from the one-box criterion, the SU(N) strong-coupling anchor with the
explicit window `anchorG d · tanh(N β_k) ≤ g < 1`, the cube decay from the wall-cut criterion, and the recursion lemma
with the SU(N) cost distance `geodSUN` (non-negative and `≤ π`).
-/

open MeasureTheory

noncomputable section

namespace ProofPhase.General

/-- `fineDecayInv_of_fineOneBox` for SU(N), any `N`, any `d`. -/
theorem fineDecayInv_of_fineOneBox_SUN (N d : ℕ) [NeZero d] {T : Tuning} (h : FineOneBox (SUN N) N d T) :
    FineDecayInv (SUN N) N d T :=
  fineDecayInv_of_fineOneBox (SUN N) N d h

/-- **The strong-coupling anchor for SU(N)**: along a tuning with one lattice step per cell and bare couplings with
`0 ≤ β_k` and `anchorG d · tanh(N β_k) ≤ g < 1`, the Wilson one-box criterion with the actual box law holds. -/
theorem wilsonOneBox_strong_SUN (N d : ℕ) [NeZero d] (T : Tuning) (hℓ : ∀ k, T.ℓ k = 1) {g : ℝ} (hg : g < 1)
    (hβ : ∀ k, 0 ≤ T.β k ∧ anchorG d * Real.tanh ((N : ℝ) * T.β k) ≤ g) : WilsonOneBox (SUN N) N d T :=
  wilsonOneBox_strong (SUN N) N d T hℓ hg hβ

/-- `cubeDecay_of_wallCutOneBox` for SU(N), any `N`, any `d`. -/
theorem cubeDecay_of_wallCutOneBox_SUN (N d : ℕ) [NeZero d] {T : Tuning} (h : WallCutOneBox (SUN N) N d T) :
    CubeDecay (SUN N) N d T :=
  cubeDecay_of_wallCutOneBox (SUN N) N d h

/-- The recursion lemma for SU(N), with the cost distance `geodSUN` (`0 ≤ geodSUN ≤ π`). -/
theorem blockGapBddW_of_levelDprimeWOn_SUN (N d : ℕ) [NeZero d] {M : ℕ → ℕ} [∀ j, NeZero (M j)] {T : Tuning}
    (B₁ : BlockingFamily (SUN N) d T)
    (B₂ : ∀ _k j : ℕ, GaugeConnection (SUN N) d (coarseSide j) → GaugeConnection (SUN N) d (M j))
    (hB₂ : ∀ k j : ℕ, Measurable (B₂ k j)) {s lam₂ : ℝ} (hs : 0 < s) (hlam₂ : 0 < lam₂)
    (hD : LevelDprimeWOn (geodSUN N) (fun k j => (blockedLaw N T B₁ k j).map (B₂ k j)) lam₂)
    (hX : StageTwoW (geodSUN N) (blockedLaw N T B₁) B₂ s) :
    ∃ lam : ℝ, 0 < lam ∧ BlockGapBddW N (geodSUN N) T B₁ lam :=
  blockGapBddW_of_levelDprimeWOn N (geodSUN N) (fun a b => geodSUN_nonneg a b) (fun a b => geodSUN_le_pi a b)
    B₁ B₂ hB₂ hs hlam₂ hD hX

end ProofPhase.General
