/-
Proof phase, crossover workstream (c9a-crossover): renormalized Doeblin, a density floor set in physical units at the
hand-over scale (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/RDOEBLIN.md`.
-/

import ProofPhase.Mixing.Chain

/-!
# A floor uniform in the lattice spacing gives a physical rate along a chain, and not the `2d`-neighbour sum

Kernels are the stochastic matrices of `Mixing/Doeblin.lean`; `kpow K n` is the `n`-fold homogeneous chain (`Chain.lean`).

* **`rdoeblin_family`** (S): a family of blocked transfer kernels `K a` indexed by the lattice spacing `a`, each with a density
  floor `ε ν_a` where `ε` does **not** depend on `a`, contracts by `(1 − ε)^n` over `n` boxes, for every `a`.
* **`one_sub_pow_eq_exp`** (S): `(1 − ε)^n = exp(−m · (n ℓ))` with `m = −log(1 − ε)/ℓ`, for `ε < 1`, `ℓ > 0`.
* **`rdoeblin_physical_decay`** (S): hence for every `a`, two inputs of the chain have outputs at total-variation distance at
  most `exp(−m D)` at physical distance `D = n ℓ`, with the same `m > 0` for all `a`.
* **`floor_column_requirement`** (S): `k (1 − e^{−C}) < 1 ↔ C < log(k/(k − 1))`, for `k ≥ 2` (`log(8/7) ≈ 0.134` for `2d = 8`).
* **`floor_disagreement_requirement`** (S): `1 − e^{−C} < p ↔ C < −log(1 − p)`, for `0 < p < 1` (the disagreement-percolation
  form, with `p` a site-percolation threshold of the box graph).

**Claim level.** Lean, abstract. That the blocked kernels at the hand-over scale have an `a`-independent floor is the M1 input
discussed in RDOEBLIN.md 1 (paper, with a named gap: a lower bound on the blocked density).
-/

open Finset Real

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Crossover

open ProofPhase.Mixing

section Family

variable {ι : Type*} {X : ι → Type*} [∀ a, Fintype (X a)] [∀ a, DecidableEq (X a)]

/-- **Renormalized Doeblin** (S): an `a`-independent floor gives an `a`-independent contraction along the chain. -/
theorem rdoeblin_family (K : ∀ a, X a → X a → ℝ) (hK : ∀ a, IsStoch (K a)) (ν : ∀ a, X a → ℝ)
    (hν : ∀ a, ∑ y, ν a y = 1) {ε : ℝ} (hε : ∀ a x y, ε * ν a y ≤ K a x y) (a : ι) (n : ℕ) :
    Contracts (kpow (K a) n) ((1 - ε) ^ n) :=
  contracts_kpow_of_doeblin (hK a) (hν a) (hε a) n

/-- **The chain contraction as a rate per physical length** (S). -/
theorem one_sub_pow_eq_exp {ε ℓ : ℝ} (h1 : ε < 1) (hℓ : 0 < ℓ) (n : ℕ) :
    (1 - ε) ^ n = Real.exp (-(-Real.log (1 - ε) / ℓ) * (n * ℓ)) := by
  have hpos : 0 < 1 - ε := by linarith
  rw [← Real.exp_log (pow_pos hpos n), Real.log_pow]
  congr 1
  field_simp

/-- **Physical decay, uniform in the spacing** (S): at physical distance `D = n ℓ`, influence `≤ exp(−m D)`. -/
theorem rdoeblin_physical_decay (K : ∀ a, X a → X a → ℝ) (hK : ∀ a, IsStoch (K a)) (ν : ∀ a, X a → ℝ)
    (hν : ∀ a, ∑ y, ν a y = 1) {ε ℓ : ℝ} (h1 : ε < 1) (hℓ : 0 < ℓ) (hε : ∀ a x y, ε * ν a y ≤ K a x y)
    (a : ι) {p q : X a → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1)
    (n : ℕ) :
    tv (pushv p (kpow (K a) n)) (pushv q (kpow (K a) n)) ≤
      Real.exp (-(-Real.log (1 - ε) / ℓ) * (n * ℓ)) := by
  rw [← one_sub_pow_eq_exp h1 hℓ n]
  exact tv_pushv_kpow_le_pow (hK a) (contracts_of_doeblin (hK a) (hν a) (hε a)) hp hq hp1 hq1 n

end Family

/-- **Column-sum requirement on the floor exponent** (S): `k (1 − e^{−C}) < 1 ↔ C < log(k/(k − 1))`, `k ≥ 2`. -/
theorem floor_column_requirement {k : ℕ} (hk : 2 ≤ k) (C : ℝ) :
    (k : ℝ) * (1 - Real.exp (-C)) < 1 ↔ C < Real.log (k / (k - 1)) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hkpos : (0 : ℝ) < k := by linarith
  rw [column_sum_lt_one_iff (by omega : 1 ≤ k)]
  have e : 1 - 1 / (k : ℝ) = ((k : ℝ) - 1) / k := by field_simp
  rw [e]
  have hpos : (0 : ℝ) < ((k : ℝ) - 1) / k := div_pos (by linarith) hkpos
  have e2 : Real.log ((k : ℝ) / (k - 1)) = -Real.log (((k : ℝ) - 1) / k) := by
    rw [← Real.log_inv, inv_div]
  rw [e2, ← Real.log_lt_iff_lt_exp hpos]
  constructor <;> intro h <;> linarith

/-- **Disagreement-percolation requirement on the floor exponent** (S): `1 − e^{−C} < p ↔ C < −log(1 − p)`. -/
theorem floor_disagreement_requirement {p : ℝ} (hp1 : p < 1) (C : ℝ) :
    1 - Real.exp (-C) < p ↔ C < -Real.log (1 - p) := by
  have hpos : 0 < 1 - p := by linarith
  constructor
  · intro h
    have h' : 1 - p < Real.exp (-C) := by linarith
    have := (Real.log_lt_iff_lt_exp hpos).2 h'
    linarith
  · intro h
    have h' : Real.log (1 - p) < -C := by linarith
    have := (Real.log_lt_iff_lt_exp hpos).1 h'
    linarith

end ProofPhase.Crossover
