/-
Proof phase, M1 tools (m1-tools): a scale-invariant lower bound for the transverse action of Z2 flux (2026-11-22).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/MILESTONE-1.md`, section 1.
-/

import Mathlib

/-!
# The cost of carrying flux through `n` plaquettes

If a closed loop has holonomy at distance `θ` from the identity (bi-invariant angle; `θ = π` for the flip `-1`,
`θ = π/2` for an act), the non-abelian Stokes formula writes it as a product of conjugated plaquette holonomies, and the
triangle inequality for the bi-invariant distance gives `Σ α_p ≥ θ` for the plaquette angles of any surface it bounds
(paper, `MILESTONE-1.md` 1). The Wilson action of those plaquettes is then at least `(2/π²) θ²/n`:

* `one_sub_cos_ge`: `2/π² · x² ≤ 1 - cos x` on `[0, π]` (Jordan's inequality for the half angle);
* `transverse_lower_bound`: angles in `[0, π]` with sum `≥ θ ≥ 0` have `Σ (1 - cos α_i) ≥ (2/π²) θ² / n`.

With `n ~ T²` plaquettes across a vortex of thickness `T`, the action per `T × T` patch of sheet is bounded below
independently of `T` (scale invariance); the uniform abelian tube attains `n (1 - cos(θ/n)) ≈ θ²/(2n)`, so the
constant is sharp up to the factor `4/π²`.

**Claim level.** Proved (standard axioms). The group-theoretic step (Stokes plus the triangle inequality) is on paper.
-/

namespace ProofPhase.M1

open Real

/-- `1 - cos x ≥ (2/π²) x²` on `[0, π]`. -/
theorem one_sub_cos_ge {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ π) : 2 / π ^ 2 * x ^ 2 ≤ 1 - cos x := by
  have hpi : 0 < π := pi_pos
  have hc : cos x = 1 - 2 * sin (x / 2) ^ 2 := by
    rw [← cos_two_mul_eq_one_sub]; ring_nf
  have hs : 2 / π * (x / 2) ≤ sin (x / 2) := mul_le_sin (by linarith) (by linarith)
  have hs0 : 0 ≤ 2 / π * (x / 2) := by positivity
  have hsq : (2 / π * (x / 2)) ^ 2 ≤ sin (x / 2) ^ 2 := pow_le_pow_left₀ hs0 hs 2
  rw [hc]
  have : 2 / π ^ 2 * x ^ 2 = 2 * (2 / π * (x / 2)) ^ 2 := by field_simp
  rw [this]
  linarith

/-- **Transverse lower bound.** -/
theorem transverse_lower_bound {n : ℕ} (hn : 0 < n) (α : Fin n → ℝ) (h0 : ∀ i, 0 ≤ α i) (h1 : ∀ i, α i ≤ π)
    {θ : ℝ} (hθ : 0 ≤ θ) (hsum : θ ≤ ∑ i, α i) :
    2 / π ^ 2 * θ ^ 2 / n ≤ ∑ i, (1 - cos (α i)) := by
  have hpi : 0 < π := pi_pos
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hcs : (∑ i, α i) ^ 2 ≤ (n : ℝ) * ∑ i, α i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := α)
    simpa using this
  have hθ2 : θ ^ 2 ≤ (∑ i, α i) ^ 2 := pow_le_pow_left₀ hθ hsum 2
  have hterm : ∑ i, 2 / π ^ 2 * α i ^ 2 ≤ ∑ i, (1 - cos (α i)) :=
    Finset.sum_le_sum fun i _ => one_sub_cos_ge (h0 i) (h1 i)
  rw [← Finset.mul_sum] at hterm
  have hk : 0 < 2 / π ^ 2 := by positivity
  calc 2 / π ^ 2 * θ ^ 2 / n ≤ 2 / π ^ 2 * ((n : ℝ) * ∑ i, α i ^ 2) / n := by
        gcongr; exact hθ2.trans hcs
    _ = 2 / π ^ 2 * ∑ i, α i ^ 2 := by field_simp
    _ ≤ ∑ i, (1 - cos (α i)) := hterm

end ProofPhase.M1
