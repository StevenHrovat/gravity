/-
The hand-over rate for every SU(N) sector, unconditionally (2026-11-24).
Released under Apache 2.0.

Paper: `docs/paper/draft/03-part-III-yang-mills.md`, III.3 (the hand-over), and the introduction's list of results.
-/

import ProofPhase.General.SUNTwistInstances
import ProofPhase.Crossover.HandOver

/-!
# The hand-over for the SU(N) package, with no stated hypothesis

`log_one_add_sqrt_two_le_max` (`Crossover/HandOver.lean`) is abstract in two numbers `0 < Z_tw < Z`. For the SU(N) twisted
Wilson partition functions both conditions are theorems: `sunZtw_pos` (every N, every sector) and `sunZtw_lt` (every N >= 2, every
nontrivial sector, `β ≠ 0`, even time extent). So the per-box hand-over rate `log(1 + √2)` holds for them with no hypothesis
beyond those. For SU(2), the `Flip` partition functions of `su2_handover` are the `k = 1` case of this package up to the
identification `SUNTwistInstances.lean` names. No axioms beyond the standard ones.
-/

open ProofPhase.Flip ProofPhase.Crossover

namespace ProofPhase.General

variable (N : ℕ) [NeZero N] (L : ℕ) [NeZero L]

/-- **The hand-over rate for every SU(N) sector**: the twist free energy or the electric free energy of the SU(N) Wilson box is at
least `log(1 + √2)`, for every `β ≠ 0`, every even time extent and every nontrivial sector `k`. -/
theorem sun_handover [Fact (1 < N)] {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L)
    {T : ℕ} [NeZero T] (hT : Even T) {k : ZMod N} (hk : k ≠ 0) :
    Real.log (1 + √2) ≤
      max (twistF (sunZ N L β P T) (sunZtw N L β P c T k)) (elecF (sunZ N L β P T) (sunZtw N L β P c T k)) :=
  log_one_add_sqrt_two_le_max (sunZtw_pos N L β P c T k) (sunZtw_lt N L hβ P c hT hk)

end ProofPhase.General
