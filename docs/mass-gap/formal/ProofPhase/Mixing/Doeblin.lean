/-
Uniformity along the chain, part 1: Doeblin's bound and the box bound (2026-11-23). Released under Apache 2.0.

Paper: `docs/pnp/CHAIN.md`.
-/

import ProofPhase.Mixing.Classical

/-!
# Doeblin's bound: a floor under the kernel bounds its contraction coefficient

Setting: a Markov kernel from `X` to a finite set `Y` is a stochastic matrix `K : X → Y → ℝ` (`IsStoch`). Its
*contraction coefficient* (Dobrushin's coefficient of the kernel) is the largest total-variation distance between two
rows, `eta K = sup_{x, x'} tv (K x) (K x')`. We state bounds as `Contracts K η` (every pair of rows is at distance at most
`η`), and `etaCoef_le_iff` shows that this is the same as `etaCoef K ≤ η`.

* `contracts_of_doeblin`: if `K x y ≥ ε ν y` for all `x y`, with `ν` a probability vector, then `Contracts K (1 - ε)`.
* `doeblin_sharp`: the bound `1 - ε` cannot be improved from the floor alone (a two-point example attains it).
* `box_bound`: abstract box law as a kernel from outsides to box configurations. If its density relative to a reference
  probability vector is at least `e^{-C}` for every outside, then `eta ≤ 1 - e^{-C}` for every outside.

`X` (the outsides) may be any type; only `Y` (the box configurations) is finite. No measurability is needed. The
standard Borel case (a kernel with a floor `K(x, .) ≥ ε ν`) is the same statement for measures; it is not formalised here.

No axioms beyond the standard ones; nothing is assumed.
-/

open Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Mixing

section Kernels

variable {X Y : Type*} [Fintype Y] [DecidableEq Y]

/-- A Markov kernel from `X` to the finite set `Y`: every row is a probability vector. -/
structure IsStoch (K : X → Y → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ K x y
  sum_one : ∀ x, ∑ y, K x y = 1

/-- `K` has contraction coefficient at most `η`: any two rows are at total-variation distance at most `η`. -/
def Contracts (K : X → Y → ℝ) (η : ℝ) : Prop := ∀ x x', tv (K x) (K x') ≤ η

/-- The contraction coefficient (Dobrushin's coefficient) of a kernel: the largest distance between two rows. -/
def etaCoef (K : X → Y → ℝ) : ℝ := ⨆ p : X × X, tv (K p.1) (K p.2)

theorem etaCoef_le_iff [Finite X] [Nonempty X] {K : X → Y → ℝ} {η : ℝ} : etaCoef K ≤ η ↔ Contracts K η := by
  have hfin : (Set.range fun p : X × X => tv (K p.1) (K p.2)).Finite := Set.finite_range _
  unfold etaCoef Contracts
  rw [ciSup_le_iff hfin.bddAbove]
  exact ⟨fun h x x' => h (x, x'), fun h p => h p.1 p.2⟩

/-- Two probability vectors are at total-variation distance at most `1`. -/
theorem tv_le_one {a b : Y → ℝ} (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s) (ha1 : ∑ s, a s = 1)
    (hb1 : ∑ s, b s = 1) : tv a b ≤ 1 := by
  unfold tv
  have h : ∑ s, |a s - b s| ≤ ∑ s, (a s + b s) :=
    Finset.sum_le_sum fun s _ => abs_sub_le_iff.2 ⟨by linarith [hb s], by linarith [ha s]⟩
  rw [Finset.sum_add_distrib, ha1, hb1] at h
  linarith

theorem IsStoch.contracts_one {K : X → Y → ℝ} (hK : IsStoch K) : Contracts K 1 := fun x x' =>
  tv_le_one (hK.nonneg x) (hK.nonneg x') (hK.sum_one x) (hK.sum_one x')

/-- **Doeblin's bound.** If every row of `K` is at least `ε ν` pointwise, with `ν` a probability vector, then any two
rows overlap in mass at least `ε`, so their total-variation distance is at most `1 - ε`. -/
theorem contracts_of_doeblin {K : X → Y → ℝ} (hK : IsStoch K) {ν : Y → ℝ} (hν : ∑ y, ν y = 1) {ε : ℝ}
    (hε : ∀ x y, ε * ν y ≤ K x y) : Contracts K (1 - ε) := by
  intro x x'
  rw [← dlt_eq_tv (hK.sum_one x) (hK.sum_one x')]
  unfold dlt
  have h0 : ε = ∑ y, ε * ν y := by rw [← Finset.mul_sum, hν, mul_one]
  have h : ∑ y, ε * ν y ≤ ∑ y, minv (K x) (K x') y :=
    Finset.sum_le_sum fun y _ => le_min (hε x y) (hε x' y)
  linarith

/-- The same in terms of the coefficient `etaCoef`. -/
theorem etaCoef_le_of_doeblin [Finite X] [Nonempty X] {K : X → Y → ℝ} (hK : IsStoch K) {ν : Y → ℝ}
    (hν : ∑ y, ν y = 1) {ε : ℝ} (hε : ∀ x y, ε * ν y ≤ K x y) : etaCoef K ≤ 1 - ε :=
  etaCoef_le_iff.2 (contracts_of_doeblin hK hν hε)

/-- **The bound `1 - ε` is sharp.** For every `ε ∈ [0, 1]` there is a kernel on two points with floor `ε ν`
(`ν` uniform) whose two rows are at distance exactly `1 - ε`. So a floor alone gives nothing better. -/
theorem doeblin_sharp {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    ∃ K : Bool → Bool → ℝ, IsStoch K ∧ (∀ x y, ε * (1 / 2) ≤ K x y) ∧ tv (K true) (K false) = 1 - ε := by
  refine ⟨fun x y => ε / 2 + (1 - ε) * (if x = y then 1 else 0), ⟨fun x y => ?_, fun x => ?_⟩, fun x y => ?_, ?_⟩
  · split_ifs <;> nlinarith
  · cases x <;> simp <;> ring
  · beta_reduce
    split_ifs <;> nlinarith
  · simp only [tv, Fintype.sum_bool]
    simp only [Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    ring

end Kernels

section Box

variable {O B : Type*} [Fintype B] [DecidableEq B]

/-- **The box bound.** The law of the box configuration given the outside `o` is `law o`, with density `f o b` relative
to a reference probability vector `ρ` on the box configurations: `law o b = f o b * ρ b`. If `f o b ≥ e^{-C}` for every
outside `o` and configuration `b`, then the box law is a Markov kernel from outsides to box configurations with
contraction coefficient at most `1 - e^{-C}`, for every pair of outsides. -/
theorem box_bound {ρ : B → ℝ} (hρ0 : ∀ b, 0 ≤ ρ b) (hρ1 : ∑ b, ρ b = 1) {C : ℝ} {f law : O → B → ℝ}
    (hlaw : ∀ o b, law o b = f o b * ρ b) (hf : ∀ o b, Real.exp (-C) ≤ f o b)
    (hnorm : ∀ o, ∑ b, law o b = 1) : IsStoch law ∧ Contracts law (1 - Real.exp (-C)) := by
  have hfloor : ∀ o b, Real.exp (-C) * ρ b ≤ law o b := fun o b => by
    rw [hlaw]; exact mul_le_mul_of_nonneg_right (hf o b) (hρ0 b)
  have hst : IsStoch law :=
    ⟨fun o b => (mul_nonneg (Real.exp_pos _).le (hρ0 b)).trans (hfloor o b), hnorm⟩
  exact ⟨hst, contracts_of_doeblin hst hρ1 hfloor⟩

end Box

end ProofPhase.Mixing
