/-
Proof phase, M1 tools (m1-tools): the two elementary steps of the off-centre dilution lemma R1 (2026-11-22).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/OFFCENTRE.md`.
-/

import Mathlib

/-!
# Off-centre dilution: common parts cancel, segments are few

Balaban's bond average (0.4) of a coarse bond `c` at a coarse site `y` is a weighted mean, over the end point `x` of a
shortest path `Γ` in the block `B(y)` and its continuation (segment and return path), of loop logarithms. In the
linearised form, the perturbation of the loop is the sum of a part inside `B(y)` (along `Γ`) and a part along the
straight segment. The law of `(x, Γ)` is the same for every coarse bond at `y`, so the `Γ`-part is common:

* `wavg_common_cancel`: two weighted means with the same weights and the same common part differ by at most the
  weighted mean of the remainders (`‖Σ wᵢ (Xᵢ + Rᵢ) − Σ wᵢ (Xᵢ + R'ᵢ)‖ ≤ Σ wᵢ (‖Rᵢ‖ + ‖R'ᵢ‖)`);
* `sum_abs_sum_le_mult`: if every bond lies on at most `t` of the segments, then the segments' total of
  `|Σ_{b ∈ seg} a_b|` is at most `t Σ_b |a_b|` (each bond on at most `L` segments of a coarse bond, weight `L^{-d}`,
  so the segment part of a coarse bond is at most `L^{1-d} Σ_b |a_b|`).

**Claim level.** Both proved (standard axioms). The identification with (0.4) is on paper (`OFFCENTRE.md` 1).
-/

open Finset

namespace ProofPhase.M1

/-- **The common part cancels.** -/
theorem wavg_common_cancel {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (X R R' : ι → E) :
    ‖∑ i, w i • (X i + R i) - ∑ i, w i • (X i + R' i)‖ ≤ ∑ i, w i * (‖R i‖ + ‖R' i‖) := by
  rw [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hw i)]
  refine mul_le_mul_of_nonneg_left ?_ (hw i)
  calc ‖X i + R i - (X i + R' i)‖ = ‖R i - R' i‖ := by congr 1; abel
    _ ≤ ‖R i‖ + ‖R' i‖ := norm_sub_le _ _

/-- **Few segments per bond.** -/
theorem sum_abs_sum_le_mult {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (S : ι → Finset κ) (a : κ → ℝ)
    {t : ℕ} (ht : ∀ b, (univ.filter (fun i => b ∈ S i)).card ≤ t) :
    ∑ i, |∑ b ∈ S i, a b| ≤ t * ∑ b, |a b| := by
  calc ∑ i, |∑ b ∈ S i, a b| ≤ ∑ i, ∑ b ∈ S i, |a b| := sum_le_sum fun i _ => abs_sum_le_sum_abs _ _
    _ = ∑ b, ((univ.filter (fun i => b ∈ S i)).card : ℝ) * |a b| := by
        rw [sum_comm' (t' := univ) (s' := fun b => univ.filter (fun i => b ∈ S i))]
        · simp [sum_const, nsmul_eq_mul]
        · intro i b; simp
    _ ≤ ∑ b, (t : ℝ) * |a b| :=
        sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (by exact_mod_cast ht b) (abs_nonneg _)
    _ = t * ∑ b, |a b| := by rw [mul_sum]

end ProofPhase.M1
