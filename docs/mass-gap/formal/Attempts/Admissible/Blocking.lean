/-
Attempt round 2026-11-21, route (c) "admissible". Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/admissible/NOTE.md`, section 3 (admissibility does not survive
blocking) and section 6 (U(1): no monopoles).
-/

import Mathlib

/-!
# Admissibility is a cutoff-scale constraint: the blocking bound, and admissible U(1) has no monopoles

**1. Blocking.** A *defect* on a group is a function `δ ≥ 0` with `δ (g h) ≤ δ g + δ h` and `δ (g h g⁻¹) = δ h`
(`Defect`). For the unitary group of any C*-ring (`n × n` unitary matrices with the operator norm), `δ U = ‖1 − U‖` is a
defect (`unitaryDefect`); Luescher's admissibility condition is `δ (U_p) < ε` for every plaquette.

* `lasso_2x2`: in any group, the holonomy around a 2 × 2 square of plaquettes is a product of the four plaquette
  holonomies, conjugated by paths from the corner (the lattice non-abelian Stokes identity, one blocking step `L = 2`).
* `defect_coarse_le`: hence the coarse plaquette (links = products of two fine links, decimation blocking) has defect at
  most the sum of the four fine defects. Admissibility at `ε` on the fine lattice gives admissibility at `4ε` after one
  step and `4^k ε` after `k` steps: the bound is lost after `≈ log₄(2/ε)` steps.
* `u1_constant_field`: the bound is attained: in U(1) a constant field strength `θ` per plaquette (defect `≤ |θ|`, so
  admissible for small `θ`) gives an `m`-fold product `e^{i m θ}`; with `θ = π/m` the big loop is `−1`, the maximal
  defect. Admissibility at any `ε` constrains no loop of side `≳ √(π/ε)`.

**2. Admissible U(1) has no monopoles.** The DeGrand–Toussaint monopole number of a cube is `(1/2π) Σ_faces ± θ̄_p ∈ ℤ`,
with `θ̄_p ∈ (−π, π]` the plaquette angle. If every `|θ̄_p| < π/3` (Luescher-admissible with `ε < π/3`), the sum of six
terms has modulus `< 2π`, so the monopole number is `0` (`no_monopole`). This holds at every `β`, including `β = 0`.
-/

noncomputable section

namespace Attempts.Admissible

/-! ## Defects -/

/-- A defect on a group: nonnegative, subadditive, conjugation invariant. -/
structure Defect (G : Type*) [Group G] where
  δ : G → ℝ
  nonneg : ∀ g, 0 ≤ δ g
  mul_le : ∀ g h, δ (g * h) ≤ δ g + δ h
  conj : ∀ g h, δ (g * h * g⁻¹) = δ h

/-- **Lattice Stokes identity for a 2 × 2 square** (any group). Sites `(i, j)`, `0 ≤ i, j ≤ 2`; horizontal links
    `h i j : (i, j) → (i+1, j)`, vertical links `v i j : (i, j) → (i, j+1)`; plaquette at `(i, j)`:
    `P i j = h i j · v (i+1) j · (h i (j+1))⁻¹ · (v i j)⁻¹` (the framework's `U_{l₀} U_{l₁} U_{l₂}⁻¹ U_{l₃}⁻¹`).
    The coarse plaquette with links `h₀₀h₁₀`, `v₂₀v₂₁`, `h₀₂h₁₂`... equals
    `(h₀₀ P₁₀ h₀₀⁻¹) · ((h₀₀v₁₀) P₁₁ (h₀₀v₁₀)⁻¹) · P₀₀ · (v₀₀ P₀₁ v₀₀⁻¹)`. -/
theorem lasso_2x2 {G : Type*} [Group G] (h00 h10 h01 h11 h02 h12 v00 v10 v20 v01 v11 v21 : G) :
    (h00 * h10) * (v20 * v21) * (h02 * h12)⁻¹ * (v00 * v01)⁻¹ =
      (h00 * (h10 * v20 * h11⁻¹ * v10⁻¹) * h00⁻¹) *
      ((h00 * v10) * (h11 * v21 * h12⁻¹ * v11⁻¹) * (h00 * v10)⁻¹) *
      (h00 * v10 * h01⁻¹ * v00⁻¹) *
      (v00 * (h01 * v11 * h02⁻¹ * v01⁻¹) * v00⁻¹) := by
  group

/-- **One blocking step multiplies the admissibility bound by at most 4.** The coarse plaquette's defect is at most the
    sum of the defects of the four fine plaquettes it contains. -/
theorem defect_coarse_le {G : Type*} [Group G] (D : Defect G)
    (h00 h10 h01 h11 h02 h12 v00 v10 v20 v01 v11 v21 : G) :
    D.δ ((h00 * h10) * (v20 * v21) * (h02 * h12)⁻¹ * (v00 * v01)⁻¹) ≤
      D.δ (h00 * v10 * h01⁻¹ * v00⁻¹) + D.δ (h10 * v20 * h11⁻¹ * v10⁻¹) +
      D.δ (h11 * v21 * h12⁻¹ * v11⁻¹) + D.δ (h01 * v11 * h02⁻¹ * v01⁻¹) := by
  rw [lasso_2x2]
  refine (D.mul_le _ _).trans ?_
  have e1 := D.mul_le ((h00 * (h10 * v20 * h11⁻¹ * v10⁻¹) * h00⁻¹) *
      ((h00 * v10) * (h11 * v21 * h12⁻¹ * v11⁻¹) * (h00 * v10)⁻¹)) (h00 * v10 * h01⁻¹ * v00⁻¹)
  have e2 := D.mul_le (h00 * (h10 * v20 * h11⁻¹ * v10⁻¹) * h00⁻¹)
      ((h00 * v10) * (h11 * v21 * h12⁻¹ * v11⁻¹) * (h00 * v10)⁻¹)
  rw [D.conj, D.conj] at e2
  rw [D.conj]
  linarith

/-- If all four fine plaquettes are `ε`-admissible, the coarse plaquette is `4ε`-admissible. -/
theorem admissible_coarse {G : Type*} [Group G] (D : Defect G) {ε : ℝ}
    (h00 h10 h01 h11 h02 h12 v00 v10 v20 v01 v11 v21 : G)
    (a : D.δ (h00 * v10 * h01⁻¹ * v00⁻¹) ≤ ε) (b : D.δ (h10 * v20 * h11⁻¹ * v10⁻¹) ≤ ε)
    (c : D.δ (h11 * v21 * h12⁻¹ * v11⁻¹) ≤ ε) (e : D.δ (h01 * v11 * h02⁻¹ * v01⁻¹) ≤ ε) :
    D.δ ((h00 * h10) * (v20 * v21) * (h02 * h12)⁻¹ * (v00 * v01)⁻¹) ≤ 4 * ε := by
  have := defect_coarse_le D h00 h10 h01 h11 h02 h12 v00 v10 v20 v01 v11 v21
  linarith

/-! ## The unitary defect `‖1 − U‖` -/

section Unitary

variable {E : Type*} [NormedRing E] [StarRing E] [CStarRing E] [Nontrivial E]

omit [Nontrivial E] in
theorem norm_mul_unitary_right (A : E) (U : unitary E) : ‖A * (U : E)‖ = ‖A‖ := by
  rw [← norm_star, star_mul, ← Unitary.coe_star, CStarRing.norm_coe_unitary_mul, norm_star]

/-- `δ U = ‖1 − U‖` on the unitary group of a C*-ring (e.g. `n × n` unitary matrices, operator norm). -/
def unitaryDefect : Defect (unitary E) where
  δ U := ‖(1 : E) - (U : E)‖
  nonneg _ := norm_nonneg _
  mul_le U V := by
    have : (1 : E) - ((U * V : unitary E) : E) = (1 - (U : E)) + (U : E) * (1 - (V : E)) := by
      simp only [Submonoid.coe_mul]; noncomm_ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [CStarRing.norm_coe_unitary_mul]
  conj g U := by
    have : (1 : E) - ((g * U * g⁻¹ : unitary E) : E) = (g : E) * (1 - (U : E)) * ((g⁻¹ : unitary E) : E) := by
      have hg : (g : E) * ((g⁻¹ : unitary E) : E) = 1 := by
        rw [← Submonoid.coe_mul, mul_inv_cancel]; simp
      simp only [Submonoid.coe_mul]
      rw [mul_sub, sub_mul, mul_one, hg]
    rw [this, norm_mul_unitary_right, CStarRing.norm_coe_unitary_mul]

end Unitary

/-! ## Sharpness in U(1) -/

/-- A constant U(1) field strength `θ` per plaquette: each plaquette has defect `|1 − e^{iθ}| ≤ |θ|`, while the product of
    `m` of them is `e^{i m θ}`; for `θ = π/m` it is `−1` (maximal defect `2`). -/
theorem u1_constant_field (m : ℕ) (hm : 0 < m) :
    ‖(1 : ℂ) - Complex.exp (Complex.I * (Real.pi / m))‖ ≤ Real.pi / m ∧
      Complex.exp (Complex.I * (Real.pi / m)) ^ m = -1 := by
  constructor
  · have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := Real.pi / m)
    rw [norm_sub_rev]
    have hpos : 0 ≤ Real.pi / m := div_nonneg Real.pi_pos.le (Nat.cast_nonneg _)
    simpa [Complex.ofReal_div, abs_of_nonneg hpos] using h
  · rw [← Complex.exp_nat_mul]
    have : (m : ℂ) * (Complex.I * (Real.pi / m)) = Real.pi * Complex.I := by
      have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      field_simp
    rw [this, Complex.exp_pi_mul_I]

/-! ## Admissible U(1): no monopoles -/

/-- **No monopoles in admissible U(1).** Six oriented face angles `t i` of a cube, each with `|t i| < π/3`, whose sum is
    `2π m` with `m ∈ ℤ` (the monopole number), have `m = 0`. -/
theorem no_monopole (t : Fin 6 → ℝ) (ht : ∀ i, |t i| < Real.pi / 3) (m : ℤ)
    (hm : ∑ i, t i = 2 * Real.pi * m) : m = 0 := by
  have hsum : |∑ i, t i| < 2 * Real.pi := by
    calc |∑ i, t i| ≤ ∑ i, |t i| := Finset.abs_sum_le_sum_abs _ _
      _ < ∑ _i : Fin 6, Real.pi / 3 := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => ht i
      _ = 2 * Real.pi := by simp; ring
  rw [hm, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hsum
  have : |(m : ℝ)| < 1 := by
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    nlinarith
  have : |m| < 1 := by exact_mod_cast this
  have := abs_lt.mp this
  omega

end Attempts.Admissible
