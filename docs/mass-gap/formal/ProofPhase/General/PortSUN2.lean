/-
Proof phase, generalisation phase 1c: the ported slab layer and routes at SU(N) (2026-11-24).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 1c.
-/

import ProofPhase.General.CondInputs
import ProofPhase.General.SUNSubst

/-!
# The ported slab layer and routes at SU(N)

The generic theorems of phase 1c apply to `SUN N` for every `N` and `d`. Examples: the blocked route gives the gap for
slab observables of bounded physical extent in both orders of limits; the level route and the W₁ route do the same, the
latter with the cost distance `geodSUN` (non-negative and `≤ π`); the reflection positivity of every limit point.
-/

open Filter Topology

noncomputable section

namespace ProofPhase.General

/-- **Reflection positivity of every continuum limit point, for SU(N)**, any `N`, any `d`. -/
theorem limitRP_SUN (N d : ℕ) [NeZero d] (T : Tuning) : LimitRP (SUN N) N d T := limitRP (SUN N) N d T

/-- **The blocked route gives torus decay and the gap in both orders of limits, for SU(N).** -/
theorem bothOrdersLoc_of_blockedRoute_SUN (N d : ℕ) [NeZero d] {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0))
    (B : BlockingFamily (SUN N) d T) {lam : ℝ} (hlam : 0 < lam) {Vk : ∀ j, ℕ → CoarsePot (SUN N) d j}
    {Vinf : ∀ j, CoarsePot (SUN N) d j} (h1 : H1Local N T B lam Vk Vinf) (h2 : LimitDprime lam Vinf)
    (h3 : ObsTransferPhys N T B) :
    TorusDecayLoc (SUN N) N d T.toV ∧ MassGapLoc (SUN N) N d T ∧ MassGapMFLoc (SUN N) N d T.toV :=
  bothOrdersLoc_of_blockedRoute (SUN N) N d ha B hlam h1 h2 h3

/-- **The level route gives the gap in both orders of limits, for SU(N).** -/
theorem bothOrdersLoc_of_levelRoute_SUN (N d : ℕ) [NeZero d] {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0))
    (h : LevelTorusRoute (SUN N) N d T) :
    TorusDecayLoc (SUN N) N d T.toV ∧ MassGapLoc (SUN N) N d T ∧ MassGapMFLoc (SUN N) N d T.toV :=
  bothOrdersLoc_of_levelRoute (SUN N) N d ha h

/-- **The W₁ route with the SU(N) cost distance gives the gap in both orders of limits.** -/
theorem bothOrdersLoc_of_levelRouteW_SUN (N d : ℕ) [NeZero d] {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0))
    (h : LevelTorusRouteW (SUN N) N d (geodSUN N) T) :
    TorusDecayLoc (SUN N) N d T.toV ∧ MassGapLoc (SUN N) N d T ∧ MassGapMFLoc (SUN N) N d T.toV :=
  bothOrdersLoc_of_levelRouteW (SUN N) N d (geodSUN N) (fun a b => geodSUN_nonneg a b)
    (fun a b => geodSUN_le_pi a b) ha h

end ProofPhase.General
