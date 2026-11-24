/-
Proof phase, crossover workstream (c9a-crossover): a composite Higgs-type field (HTF) on the collars, what conditioning on it
gives, and the superadditivity of the carried flux's free energy (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/HTF.md`.
-/

import Mathlib

/-!
# A gauge-covariant frame carries no gauge-invariant information; the flux free energy is superadditive up to the excess act

**1. Frame independence** (finite analogue of the compact-group statement, HTF.md 2). A group `G` acts on configurations `Ω`
with an invariant weight `w` (the gauge group and the Wilson weight); `F : Ω → X` is equivariant (a composite HTF frame, e.g.
the normalised lowest eigenvector of the collar's covariant Laplacian) and `G` acts transitively on `X`; `O : Ω → Y` is
invariant (any gauge-invariant observable).
* **`weight_fiber_eq`** (S): the weight of `{F = x, O = y}` does not depend on `x`.
* **`weight_fiber_mul_card`** (S): `#X · weight(F = x, O = y) = weight(O = y)`. With `O` constant: `#X · weight(F = x)` is the
  total weight; so the conditional law of every invariant observable given the frame equals its unconditional law.

**2. Superadditivity of the carried flux's free energy** (HTF.md 4). For a nonnegative transfer spectrum `x` (flux sector),
`Z₁(n) = Σ xᵢⁿ` is submultiplicative (**`sum_pow_add_le`**, S). For any `Z₀` with `lⁿ ≤ Z₀(n)` (the neutral sector, `l` its
top eigenvalue) and submultiplicative positive `Z₁`, the flux free energy `F(n) = log Z₀(n) − log Z₁(n)` satisfies
* **`flux_superadd`** (S): `F(a + b) ≥ F(a) + F(b) − c(a) − c(b)`, `c(n) = log(Z₀(n)/lⁿ)` (the neutral excess act);
* **`flux_superadd_iter`** (S): if `c ≤ C` on the multiples of `L`, then `F(kL) ≥ k (F(L) − 2C)` for `k ≥ 1`.

**Claim level.** Lean, abstract. The identification with SU(2) (transfer matrix of the spatial torus, `Z₀, Z₁` the electric
sector traces, `l` the vacuum eigenvalue) is the standard one of `Attempts/R4/LayerSector.lean` and is not re-derived here; the
transfer spectrum there is not finite, and the finite statement is the model of it (HTF.md 4).
-/

open Finset

namespace ProofPhase.Crossover

section Frame

variable {G Ω X Y : Type*} [Group G] [MulAction G Ω] [MulAction G X] [Fintype Ω] [DecidableEq X] [DecidableEq Y]

/-- **The weight of a frame fibre does not depend on the frame value** (S). -/
theorem weight_fiber_eq (w : Ω → ℝ) (hw : ∀ (g : G) ω, w (g • ω) = w ω) (F : Ω → X)
    (hF : ∀ (g : G) ω, F (g • ω) = g • F ω) (O : Ω → Y) (hO : ∀ (g : G) ω, O (g • ω) = O ω)
    [MulAction.IsPretransitive G X] (x x' : X) (y : Y) :
    ∑ ω ∈ univ.filter (fun ω => F ω = x ∧ O ω = y), w ω =
      ∑ ω ∈ univ.filter (fun ω => F ω = x' ∧ O ω = y), w ω := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x x'
  refine Finset.sum_equiv (MulAction.toPerm g) ?_ ?_
  · intro ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, MulAction.toPerm_apply, hF, hO]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h1, hg], h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rw [← hg] at h1
      exact (smul_left_cancel_iff g).1 h1
  · intro ω _
    simp only [MulAction.toPerm_apply, hw]

/-- **Independence of invariant observables from the frame** (S): `#X · weight(F = x, O = y) = weight(O = y)`. -/
theorem weight_fiber_mul_card [Fintype X] (w : Ω → ℝ) (hw : ∀ (g : G) ω, w (g • ω) = w ω) (F : Ω → X)
    (hF : ∀ (g : G) ω, F (g • ω) = g • F ω) (O : Ω → Y) (hO : ∀ (g : G) ω, O (g • ω) = O ω)
    [MulAction.IsPretransitive G X] (x : X) (y : Y) :
    (Fintype.card X : ℝ) * ∑ ω ∈ univ.filter (fun ω => F ω = x ∧ O ω = y), w ω =
      ∑ ω ∈ univ.filter (fun ω => O ω = y), w ω := by
  have hsplit : ∑ ω ∈ univ.filter (fun ω => O ω = y), w ω =
      ∑ x' : X, ∑ ω ∈ univ.filter (fun ω => F ω = x' ∧ O ω = y), w ω := by
    rw [← Finset.sum_fiberwise (univ.filter fun ω => O ω = y) F w]
    refine Finset.sum_congr rfl fun x' _ => ?_
    congr 1
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hsplit, Finset.sum_congr rfl fun x' _ => (weight_fiber_eq w hw F hF O hO x x' y).symm, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

end Frame

section Superadd

/-- **Power sums of a nonnegative spectrum are submultiplicative** (S). -/
theorem sum_pow_add_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) (a b : ℕ) :
    ∑ i ∈ s, x i ^ (a + b) ≤ (∑ i ∈ s, x i ^ a) * (∑ i ∈ s, x i ^ b) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [pow_add]
  exact Finset.single_le_sum (f := fun j => x i ^ a * x j ^ b)
    (fun j hj => mul_nonneg (pow_nonneg (hx i hi) _) (pow_nonneg (hx j hj) _)) hi

/-- **Superadditivity of the flux free energy up to the neutral excess act** (S). -/
theorem flux_superadd {Z₀ Z₁ : ℕ → ℝ} {l : ℝ} (hl : 0 < l) (h1 : ∀ n, 0 < Z₁ n) (h0 : ∀ n, l ^ n ≤ Z₀ n)
    (hsub : ∀ a b, Z₁ (a + b) ≤ Z₁ a * Z₁ b) (a b : ℕ) :
    (Real.log (Z₀ a) - Real.log (Z₁ a)) + (Real.log (Z₀ b) - Real.log (Z₁ b))
      - Real.log (Z₀ a / l ^ a) - Real.log (Z₀ b / l ^ b)
      ≤ Real.log (Z₀ (a + b)) - Real.log (Z₁ (a + b)) := by
  have hZ0 : ∀ n, 0 < Z₀ n := fun n => (pow_pos hl n).trans_le (h0 n)
  have e1 : Real.log (Z₁ (a + b)) ≤ Real.log (Z₁ a) + Real.log (Z₁ b) := by
    rw [← Real.log_mul (h1 a).ne' (h1 b).ne']
    exact Real.log_le_log (h1 _) (hsub a b)
  have e0 : Real.log (l ^ (a + b)) ≤ Real.log (Z₀ (a + b)) := Real.log_le_log (pow_pos hl _) (h0 _)
  rw [pow_add, Real.log_mul (pow_pos hl a).ne' (pow_pos hl b).ne'] at e0
  rw [Real.log_div (hZ0 a).ne' (pow_pos hl a).ne', Real.log_div (hZ0 b).ne' (pow_pos hl b).ne']
  linarith

/-- **Iterated: the per-box flux rate multiplies along a chain, less twice the excess act** (S). -/
theorem flux_superadd_iter {Z₀ Z₁ : ℕ → ℝ} {l : ℝ} (hl : 0 < l) (h1 : ∀ n, 0 < Z₁ n) (h0 : ∀ n, l ^ n ≤ Z₀ n)
    (hsub : ∀ a b, Z₁ (a + b) ≤ Z₁ a * Z₁ b) (L : ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ k, Real.log (Z₀ (k * L) / l ^ (k * L)) ≤ C) {k : ℕ} (hk : 1 ≤ k) :
    k * ((Real.log (Z₀ L) - Real.log (Z₁ L)) - 2 * C) ≤ Real.log (Z₀ (k * L)) - Real.log (Z₁ (k * L)) := by
  induction k, hk using Nat.le_induction with
  | base => simp only [Nat.cast_one, one_mul, one_mul]; linarith
  | succ k hk ih =>
    have hs := flux_superadd hl h1 h0 hsub (k * L) L
    have hcL : Real.log (Z₀ L / l ^ L) ≤ C := by simpa using hC 1
    have hck := hC k
    rw [show (k + 1) * L = k * L + L by ring]
    push_cast
    nlinarith

end Superadd

end ProofPhase.Crossover
