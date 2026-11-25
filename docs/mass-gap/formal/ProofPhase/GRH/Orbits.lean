/-
GRH attempt, closed-orbit route, step d: the finite models. Remnants (fixed points of iterates) are counted by closed
orbits; a positive form on which the dynamics acts by similitude forces the line; a duality without positivity only
forces mirror pairs (2026-11-23). Released under Apache 2.0.

Note: `docs/rh-guide/grh/ORBITS.md`.
-/

import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.NumberTheory.Divisors

/-!
# Closed orbits, traces and positivity, in finite form

**1. Remnants are counted by closed orbits** (`card_fixed_pow_eq_sum`). For a map `f` on a finite set, the fixed points
of the `n`-th iterate are exactly the points on closed orbits whose length divides `n`:
`#Fix(f^n) = ∑_{d ∣ n} #{x : exact period d}`. This is the finite shape of the explicit formula's prime side, where a
closed orbit of length `log p` contributes at every multiple `k log p`. Each primitive orbit of length `d` contributes
`d` points: its length, as in the trace formula's `l(γ)`.

**2. Positivity on cohomology forces the line.**
* `similitude_eigenvalue` (Frobenius form): if `⟪F x, F y⟫ = q ⟪x, y⟫` for a positive definite inner product, every
  eigenvalue `α` of `F` has `|α|^2 = q`. This is Weil's mechanism over a finite field: Rosati positivity together with
  `F V = q`.
* `skew_shift_re_half` (flow form, Deninger): if `⟪Θ x, y⟫ + ⟪x, Θ y⟫ = ⟪x, y⟫`, i.e. `Θ - 1/2` is skew-adjoint for a
  positive definite form (the flow acts by similitude with factor `e^t`), every eigenvalue `ρ` of `Θ` has
  `Re ρ = 1/2`.

**3. A duality without positivity gives only the mirror** (`krein_mirror`). On `ℂ²` with the indefinite Hermitian
form `B(x, y) = conj x₀ y₁ + conj x₁ y₀`, the operator `Θ = diag(ρ, 1 - conj ρ)` satisfies the same identity
`B(Θx, y) + B(x, Θy) = B(x, y)` for **every** `ρ`. Its eigenvalues are the mirror pair `ρ, 1 - conj ρ`, for example
`3/4` and `1/4`, off the line. The duality (Poincare / Serre, the functional equation) pairs `ρ` with `1 - conj ρ`;
only positivity of the form puts `ρ` on `Re = 1/2`.
-/

open Function Finset

open scoped InnerProductSpace

noncomputable section

namespace ProofPhase.GRH

/-! ### 1. Fixed points of iterates and closed orbits -/

/-- **Remnants are counted by closed orbits.** For `f` on a finite type and `n ≠ 0`, the fixed points of `f^[n]` split
by exact period, over the divisors of `n`. -/
theorem card_fixed_pow_eq_sum {X : Type*} [Fintype X] [DecidableEq X] (f : X → X) {n : ℕ} (hn : n ≠ 0) :
    (univ.filter fun x => f^[n] x = x).card =
      ∑ d ∈ n.divisors, (univ.filter fun x => minimalPeriod f x = d).card := by
  classical
  have hmaps : ∀ x ∈ univ.filter (fun x => f^[n] x = x), minimalPeriod f x ∈ n.divisors := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    have : IsPeriodicPt f n x := hx
    exact Nat.mem_divisors.mpr ⟨isPeriodicPt_iff_minimalPeriod_dvd.mp this, hn⟩
  rw [card_eq_sum_card_fiberwise hmaps]
  refine sum_congr rfl fun d hd => ?_
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    have hdvd : minimalPeriod f x ∣ n := h ▸ (Nat.mem_divisors.mp hd).1
    exact (isPeriodicPt_iff_minimalPeriod_dvd.mpr hdvd : IsPeriodicPt f n x)

/-! ### 2. Positivity on cohomology forces the line -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Frobenius form.** A similitude with multiplier `q` of a positive definite inner product has all its eigenvalues
on the circle `|α|^2 = q`. -/
theorem similitude_eigenvalue {F : E → E} {q : ℝ} (hF : ∀ x y, ⟪F x, F y⟫_ℂ = (q : ℂ) * ⟪x, y⟫_ℂ)
    {α : ℂ} {x : E} (hx : x ≠ 0) (hev : F x = α • x) : ‖α‖ ^ 2 = q := by
  have h := hF x x
  rw [hev, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K] at h
  have hn : (‖x‖ : ℂ) ^ 2 ≠ 0 := by
    have : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    exact pow_ne_zero 2 (by exact_mod_cast this)
  have h' : (starRingEnd ℂ) α * α * (‖x‖ : ℂ) ^ 2 = (q : ℂ) * (‖x‖ : ℂ) ^ 2 := by
    rw [mul_assoc]; exact h
  have h2 : (starRingEnd ℂ) α * α = (q : ℂ) := mul_right_cancel₀ hn h'
  rw [mul_comm, Complex.mul_conj', ← Complex.ofReal_pow] at h2
  exact_mod_cast h2

/-- **Flow form (Deninger's mechanism).** If `Θ - 1/2` is skew-adjoint for a positive definite inner product, every
eigenvalue of `Θ` has real part `1/2`. -/
theorem skew_shift_re_half {Θ : E → E} (hΘ : ∀ x y, ⟪Θ x, y⟫_ℂ + ⟪x, Θ y⟫_ℂ = ⟪x, y⟫_ℂ)
    {ρ : ℂ} {x : E} (hx : x ≠ 0) (hev : Θ x = ρ • x) : ρ.re = 1 / 2 := by
  have h := hΘ x x
  rw [hev, inner_smul_left, inner_smul_right, ← add_mul] at h
  have hn : ⟪x, x⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hx
  have h1 : (starRingEnd ℂ) ρ + ρ = 1 := by
    have := mul_right_cancel₀ hn (h.trans (one_mul _).symm)
    exact this
  have := congrArg Complex.re h1
  simp only [Complex.add_re, Complex.conj_re, Complex.one_re] at this
  linarith

/-! ### 3. Duality without positivity: only mirror pairs -/

/-- The indefinite Hermitian form `B(x, y) = conj x₀ y₁ + conj x₁ y₀` on `ℂ²` (a duality pairing). -/
def kreinForm (x y : Fin 2 → ℂ) : ℂ := (starRingEnd ℂ) (x 0) * y 1 + (starRingEnd ℂ) (x 1) * y 0

/-- `Θ = diag(ρ, 1 - conj ρ)`. -/
def mirrorOp (ρ : ℂ) (x : Fin 2 → ℂ) : Fin 2 → ℂ := ![ρ * x 0, (1 - (starRingEnd ℂ) ρ) * x 1]

/-- The form is Hermitian. -/
theorem kreinForm_hermitian (x y : Fin 2 → ℂ) : kreinForm y x = (starRingEnd ℂ) (kreinForm x y) := by
  simp only [kreinForm, map_add, map_mul, Complex.conj_conj]
  ring

/-- The form is indefinite: it takes the value `2` and the value `-2`. -/
theorem kreinForm_indefinite : kreinForm ![1, 1] ![1, 1] = 2 ∧ kreinForm ![1, -1] ![1, -1] = -2 := by
  constructor <;> simp [kreinForm] <;> norm_num

/-- **Duality without positivity gives only the mirror.** For every `ρ`, `Θ = diag(ρ, 1 - conj ρ)` satisfies
`B(Θx, y) + B(x, Θy) = B(x, y)`, and has the eigenvectors `e₀` (eigenvalue `ρ`) and `e₁` (eigenvalue `1 - conj ρ`).
With `ρ = 3/4` both eigenvalues are off the line `Re = 1/2`. -/
theorem krein_mirror (ρ : ℂ) :
    (∀ x y, kreinForm (mirrorOp ρ x) y + kreinForm x (mirrorOp ρ y) = kreinForm x y) ∧
      mirrorOp ρ ![1, 0] = ρ • ![1, 0] ∧
      mirrorOp ρ ![0, 1] = (1 - (starRingEnd ℂ) ρ) • ![0, 1] := by
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · simp only [kreinForm, mirrorOp, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul,
      map_sub, map_one, Complex.conj_conj]
    ring
  · ext i; fin_cases i <;> simp [mirrorOp]
  · ext i; fin_cases i <;> simp [mirrorOp]

/-- The concrete off-line case: `ρ = 3/4` satisfies the duality identity and has real part `3/4 ≠ 1/2`. -/
theorem krein_off_line :
    (∀ x y, kreinForm (mirrorOp (3 / 4) x) y + kreinForm x (mirrorOp (3 / 4) y) = kreinForm x y) ∧
      mirrorOp (3 / 4) ![1, 0] = (3 / 4 : ℂ) • ![1, 0] ∧ (3 / 4 : ℂ).re ≠ 1 / 2 := by
  refine ⟨(krein_mirror _).1, (krein_mirror _).2.1, ?_⟩
  norm_num

end ProofPhase.GRH
