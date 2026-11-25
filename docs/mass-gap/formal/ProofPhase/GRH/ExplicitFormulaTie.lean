/-
The explicit formula, layer (c): the ledger's named hypothesis `ExplicitFormula` (`TieIn.lean`) from the contour shift,
for smoothed cells (2026-11-23). Released under Apache 2.0.

Paper: `docs/unified/EXPLICIT-FORMULA.md`, section 4.
-/

import ProofPhase.GRH.ExplicitFormula
import ProofPhase.GRH.TieIn

/-!
# "Toy = not-toy" for smoothed cells: `ExplicitFormula` from the contour shift

`TieIn.lean` names the explicit formula on the grid as a hypothesis, `ExplicitFormula T t γ σ`: the Toeplitz form of the
prime-side moments `t` on the cells `s` with coefficients `c` equals Weil's zero pairing of the test function `T s c`.
Here it is derived, for **smoothed cells**, from Weil's explicit formula (`ExplicitFormula.lean`), so from the single
named classical input `ContourShift`.

**Smoothed cells.** A cell profile with transform `Φ` (on the critical line), cells at the lags `j ε`. The test function of
the coefficients `c` is `F(z) = Φ(z) ∑ⱼ cⱼ e^{i z j ε}` (`smoothedTest`, the transform of `∑ⱼ cⱼ φ(x - j ε)`). The kernel of
the lag `m` is a test function `k_m` in log scale whose transform on the critical line is
`Φ(z) conj Φ(conj z) e^{i z m ε}` (`KernelSpec`; for `k_m(x) = (φ ⋆ φ~)(x - m ε)` this is the convolution theorem). The
**prime-side moment** of the lag `m` is the right side of the explicit formula for `k_m` (`efMoment`): poles, primes
`Λ(n) n^{-1/2}`, real place.

* **`explicitFormula_of_residueShift`**: the contour shift for every kernel gives `ExplicitFormula (smoothedTest Φ ε)
  (efMoment c k) γ σ`, for any family `γ` closed under `γ ↦ conj γ`. Bilinearity, with the zero sums absolutely
  convergent.
* **`explicitFormula_of_contourShift`**: the same for the nontrivial zeros of `ζ` with multiplicity.
* **`zeta_tie_in_contourShift`**: with `ExtRH` (the external RH, `TieIn.lean`), `ScaleSign` of the prime-side moments
  and nonnegative Weil pairing. The named inputs are `ExtRH` and `ContourShift` (plus the regularity of the kernels,
  `EFTest`, `KernelSpec`, and the symmetry `σ` of the zero family, audit items 8 and 9 of `GRH-TIE-IN.md`).

This does not prove RH or GRH; the sign comes from the external hypothesis through the easy direction.

Standard axioms only.
-/

open Complex Finset ComplexConjugate

noncomputable section

namespace ProofPhase.GRH.EF

open ProofPhase.GRH ProofPhase.Unified

/-- **Smoothed cells**: the test function of the coefficients `c` on the cells `s`, `F(z) = Φ(z) ∑ⱼ cⱼ e^{i z j ε}`. -/
def smoothedTest (Φ : ℂ → ℂ) (ε : ℝ) : Finset ℕ → (ℕ → ℂ) → ℂ → ℂ := fun s c z => Φ z * gridTest ε s c z

/-- The kernel transform of the lag `m`: `K_m(z) = Φ(z) conj Φ(conj z) e^{i z m ε}`. -/
def kernelHat (Φ : ℂ → ℂ) (ε : ℝ) (m : ℤ) (z : ℂ) : ℂ :=
  Φ z * conj (Φ (conj z)) * Complex.exp (I * z * (((m : ℝ) * ε : ℝ) : ℂ))

/-- **The kernels** `k_m` have the transforms `K_m` on the critical line. -/
def KernelSpec (Φ : ℂ → ℂ) (ε : ℝ) (k : ℤ → ℝ → ℂ) : Prop :=
  ∀ m z, laplace (k m) (1 / 2 + I * z) = kernelHat Φ ε m z

/-- **The prime-side moment of the lag `m`**: the right side of the explicit formula for the kernel `k_m`. -/
def efMoment (c : ℝ) (k : ℤ → ℝ → ℂ) (m : ℤ) : ℂ := efRHS c (k m)

/-- The pairing of the smoothed test function is the double sum of the kernel transforms. -/
theorem smoothed_pairing (Φ : ℂ → ℂ) (ε : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) (z : ℂ) :
    smoothedTest Φ ε s c z * conj (smoothedTest Φ ε s c (conj z)) =
      ∑ j ∈ s, ∑ l ∈ s, conj (c j) * c l * kernelHat Φ ε ((l : ℤ) - j) z := by
  simp only [smoothedTest, gridTest, map_mul, map_sum]
  rw [mul_mul_mul_comm, Finset.sum_mul_sum, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hexp : conj (Complex.exp (I * conj z * (((j : ℝ) * ε : ℝ) : ℂ))) =
      Complex.exp (-(I * z * (((j : ℝ) * ε : ℝ) : ℂ))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
    ring
  have hmul : Complex.exp (I * z * (((l : ℝ) * ε : ℝ) : ℂ)) * Complex.exp (-(I * z * (((j : ℝ) * ε : ℝ) : ℂ))) =
      Complex.exp (I * z * ((((((l : ℤ) - j : ℤ) : ℝ)) * ε : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp, kernelHat, ← hmul]
  ring

/-- **The explicit formula on the grid, from the contour shift** (any family of points closed under conjugation). -/
theorem explicitFormula_of_residueShift {c : ℝ} (hc : 1 < c) {Φ : ℂ → ℂ} {ε : ℝ} {k : ℤ → ℝ → ℂ}
    (hT : ∀ m, EFTest c (k m) ∧ EFTest c (refl (k m))) (hK : KernelSpec Φ ε k)
    {ι : Type} {γ : ι → ℂ} {σ : ι → ι} (hσ : ∀ i, γ (σ i) = conj (γ i))
    (hR : ∀ m, ResidueShift c (k m) (fun i => 1 / 2 + I * γ i)) :
    ExplicitFormula (smoothedTest Φ ε) (efMoment c k) γ σ := by
  -- each moment is the zero sum of its kernel transform
  have hEF : ∀ m, Summable (fun i => kernelHat Φ ε m (γ i)) ∧ ∑' i, kernelHat Φ ε m (γ i) = efMoment c k m := by
    intro m
    have h := explicit_formula hc (hT m).1 (hT m).2 (hR m)
    simp only [hK m] at h
    exact h
  intro s cs
  have hsum : ∀ j l, Summable fun i => conj (cs j) * cs l * kernelHat Φ ε ((l : ℤ) - j) (γ i) :=
    fun j l => (hEF _).1.mul_left _
  calc toepForm (efMoment c k) s cs
      = ∑ j ∈ s, ∑ l ∈ s, ∑' i, conj (cs j) * cs l * kernelHat Φ ε ((l : ℤ) - j) (γ i) := by
        unfold toepForm
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        rw [tsum_mul_left, (hEF _).2]
    _ = ∑' i, ∑ j ∈ s, ∑ l ∈ s, conj (cs j) * cs l * kernelHat Φ ε ((l : ℤ) - j) (γ i) := by
        rw [Summable.tsum_finsetSum fun j _ => summable_sum fun l _ => hsum j l]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Summable.tsum_finsetSum fun l _ => hsum j l]
    _ = weilSum γ σ (smoothedTest Φ ε s cs) := by
        unfold weilSum weilTerm
        refine tsum_congr fun i => ?_
        rw [hσ i, smoothed_pairing]

/-- **The ledger's named hypothesis, discharged for smoothed cells by the contour shift.** For an enumeration `γ` of the
nontrivial zeros of `ζ` with multiplicity, closed under conjugation by `σ`: `ExplicitFormula` of `TieIn.lean` holds for
the smoothed test functions and the prime-side moments `efMoment`. -/
theorem explicitFormula_of_contourShift {c : ℝ} (hc : 1 < c) {Φ : ℂ → ℂ} {ε : ℝ} {k : ℤ → ℝ → ℂ}
    (hT : ∀ m, EFTest c (k m) ∧ EFTest c (refl (k m))) (hK : KernelSpec Φ ε k) (hCS : ∀ m, ContourShift c (k m))
    {ι : Type} {γ : ι → ℂ} {σ : ι → ι} (hσ : ∀ i, γ (σ i) = conj (γ i)) (hZ : NontrivialZeroFamily γ) :
    ExplicitFormula (smoothedTest Φ ε) (efMoment c k) γ σ :=
  explicitFormula_of_residueShift hc hT hK hσ fun m => hCS m ι γ hZ

/-- A nontrivial zero family is a family of strip zeros in the sense of `TieIn.lean`. -/
theorem stripZeros_of_family {ι : Type} {γ : ι → ℂ} (hZ : NontrivialZeroFamily γ) : StripZeros riemannZeta γ :=
  hZ.1

/-- **Zeta column, smoothed cells.** The external RH (`ExtRH`) and the contour shift give `ScaleSign` of the prime-side
moments `efMoment` (poles, `Λ(n) n^{-1/2}`, real place, for the kernels of the smoothed cells) and nonnegative Weil
pairing. The explicit formula is no longer a hypothesis of the tie: it is reduced to `ContourShift`. -/
theorem zeta_tie_in_contourShift (hExt : ExtRH) {c : ℝ} (hc : 1 < c) {Φ : ℂ → ℂ} {ε : ℝ} {k : ℤ → ℝ → ℂ}
    (hT : ∀ m, EFTest c (k m) ∧ EFTest c (refl (k m))) (hK : KernelSpec Φ ε k) (hCS : ∀ m, ContourShift c (k m))
    {ι : Type} {γ : ι → ℂ} {σ : ι → ι} (hσ : ∀ i, γ (σ i) = conj (γ i)) (hZ : NontrivialZeroFamily γ) :
    ScaleSign (efMoment c k) ∧ ∀ F, 0 ≤ (weilSum γ σ F).re :=
  zeta_tie_in hExt hσ (stripZeros_of_family hZ) (explicitFormula_of_contourShift hc hT hK hCS hσ hZ)

end ProofPhase.GRH.EF
