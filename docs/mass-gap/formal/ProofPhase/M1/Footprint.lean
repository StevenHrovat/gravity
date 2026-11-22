/-
Proof phase, M1 tools (m1-tools): the footprint-weighted lifetime of a shrinking large-field region (2026-11-22).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/R2-REPAIR.md`, section 2.
-/

import Mathlib

/-!
# A region whose footprint shrinks geometrically costs a bounded multiple of its birth size

By Lemma F of `P2-PRIME.md`, the physical support of a connected region with `n_s` sites at its birth scale meets at
most `N_k ≤ 3^d (2 n_s L^{-k} + 1)` cubes `k` steps later. Balaban's entropy induction charges `O(M^d R^{d+1})` per cube
per step, so the total charge of a region over a life of `n` steps is controlled by `Σ_{k<n} N_k`:

* `footprint_sum_le`: if `N k ≤ A q^k + B` with `A ≥ 0`, `0 ≤ q < 1`, then `Σ_{k<n} N k ≤ A/(1 - q) + n B`.

With `A = 2·3^d n_s`, `q = 1/L`, `B = 3^d`: the birth size times a constant, plus `3^d` per step of life.

**Claim level.** Proved (standard axioms).
-/

open Finset

namespace ProofPhase.M1

/-- **Footprint-weighted lifetime.** -/
theorem footprint_sum_le {A B q : ℝ} (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ → ℝ)
    (h : ∀ k, N k ≤ A * q ^ k + B) (n : ℕ) : ∑ k ∈ range n, N k ≤ A / (1 - q) + n * B := by
  have hq : 0 < 1 - q := by linarith
  have hgeom : ∑ k ∈ range n, q ^ k ≤ 1 / (1 - q) := by
    rw [geom_sum_eq (by linarith : q ≠ 1)]
    have e : (q ^ n - 1) / (q - 1) = (1 - q ^ n) / (1 - q) := by
      rw [show q ^ n - 1 = -(1 - q ^ n) by ring, show q - 1 = -(1 - q) by ring, neg_div_neg_eq]
    rw [e]
    apply div_le_div_of_nonneg_right _ hq.le
    linarith [pow_nonneg hq0 n]
  calc ∑ k ∈ range n, N k ≤ ∑ k ∈ range n, (A * q ^ k + B) := sum_le_sum fun k _ => h k
    _ = A * ∑ k ∈ range n, q ^ k + n * B := by
        rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
    _ ≤ A * (1 / (1 - q)) + n * B := by gcongr
    _ = A / (1 - q) + n * B := by ring

end ProofPhase.M1
