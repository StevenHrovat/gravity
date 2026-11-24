/-
Attempt r3-dmp (round 3, attempt 5), 2026-11-21. Released under Apache 2.0.

# T38 on the Yang–Mills side: a blocked layer inherits reflection positivity when it is "gated from above"

Note: `docs/mass-gap/weak-coupling/attempts/r3-dmp/NOTE.md`, section 6 (the inventory).

DMP's T38 ("Every information layer has its own Duality") is enforced in the recipe by well-formedness: a line whose Duality is not
minted must be laid over a line that gates it (`Recipe.lineOk`, third clause). Under the hosting of NOTE §1 the Duality of a layer is
reflection positivity (RP) of that layer's measure: the two halves are the two half-spaces of a reflection, and "minted" is RP.

What this file proves (finite configuration spaces, no Yang–Mills specifics): **the "gated from above" form transfers for free.**
If the fine layer is RP for a class of positive-half observables, and the blocking kernel factorises across the reflection plane with
the reflected kernel on the negative half (a coarse variable on the positive side is drawn from the fine positive half only), then
every coarse observable `G` of the positive-side coarse variables satisfies the coarse RP inequality, provided its lift
`ω ↦ Σ_v K₊(ω, v) G(v)` is a positive-half observable of the fine layer. Coarse variables that straddle the plane are not covered:
for them the coarse layer needs a Duality of its own (a separate RP proof), as T38 says.
-/

import Mathlib

namespace Attempts.R3.DmpHost

/-- **Gated reflection positivity.** `w` is the fine weight, `θ` the reflection, `𝓕` the positive-half observables for which the fine
    layer is reflection positive. `Kp ω v` is the kernel drawing the positive-side coarse variable `v` from the fine configuration `ω`
    (depending on its positive half only, which is what `hlift` asks of the lifted observable); the negative-side coarse variable is
    drawn from `θ ω` by the same kernel. Then the coarse reflection-positivity form of `G` is non-negative. -/
theorem gated_rp {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] (w : Ω → ℝ) (θ : Ω → Ω) (𝓕 : Set (Ω → ℝ))
    (hRP : ∀ F ∈ 𝓕, 0 ≤ ∑ ω, w ω * (F ω * F (θ ω))) (Kp : Ω → Ξ → ℝ) (G : Ξ → ℝ)
    (hlift : (fun ω => ∑ v, Kp ω v * G v) ∈ 𝓕) :
    0 ≤ ∑ ω, w ω * ∑ v, ∑ v', Kp ω v * Kp (θ ω) v' * (G v * G v') := by
  refine le_of_le_of_eq (hRP _ hlift) (Finset.sum_congr rfl fun ω _ => ?_)
  congr 1
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun v' _ => ?_
  ring

end Attempts.R3.DmpHost
