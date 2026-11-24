/-
The contour shift: an enumeration of the nontrivial zeros with multiplicity exists, and the explicit formula for it
(2026-11-24). Released under Apache 2.0.

Paper: `docs/unified/CONTOUR-SHIFT.md`, section 7.
-/

import ProofPhase.GRH.ContourShiftTie

/-!
# A concrete enumeration of the nontrivial zeros, and the explicit formula for it

`explicit_formula_of_smooth` quantifies over every `γ` with `EF.NontrivialZeroFamily γ`. This file shows the hypothesis
is not vacuous:

* `zetaZeroIndex`: the pairs `(z, k)` with `z` a zero of `ζ` in the open strip and `k < ord_z ζ`;
* `zetaZeroOrdinate`: `γ(z, k) = -i (z - 1/2)`, so that `1/2 + iγ = z`;
* **`nontrivialZeroFamily_zetaZeroOrdinate`**: this is a `NontrivialZeroFamily` (each zero occurs exactly `ord_z ζ`
  times; the order is finite because `ζ` is not identically zero near any point of the strip, `analyticOrderAt_xiF`);
* **`exists_nontrivialZeroFamily`**: such a family exists;
* **`explicit_formula_zetaZeros`**: the explicit formula for this enumeration, with nothing assumed about `γ`.

Standard axioms only.
-/

open Complex
open scoped ContDiff

noncomputable section

namespace ProofPhase.GRH.CSTie

open ProofPhase.GRH ProofPhase.GRH.EF

/-- The index set: zeros `z` of `ζ` in the open strip, each with `k < ord_z ζ` copies. -/
def zetaZeroIndex : Type :=
  {p : ℂ × ℕ // (0 < p.1.re ∧ p.1.re < 1 ∧ riemannZeta p.1 = 0) ∧ (p.2 : ℕ∞) < analyticOrderAt riemannZeta p.1}

/-- The ordinate `γ = -i (z - 1/2)`, so that `1/2 + iγ = z`. -/
def zetaZeroOrdinate (i : zetaZeroIndex) : ℂ := -I * (i.1.1 - 1 / 2)

theorem half_add_zetaZeroOrdinate (i : zetaZeroIndex) : 1 / 2 + I * zetaZeroOrdinate i = i.1.1 := by
  unfold zetaZeroOrdinate
  rw [← mul_assoc, show I * -I = 1 by rw [mul_neg, I_mul_I, neg_neg], one_mul]
  ring

/-- **The enumeration is a `NontrivialZeroFamily`.** -/
theorem nontrivialZeroFamily_zetaZeroOrdinate : NontrivialZeroFamily zetaZeroOrdinate := by
  refine ⟨fun i => by rw [half_add_zetaZeroOrdinate]; exact i.2.1, fun z h1 h2 => ?_⟩
  simp_rw [half_add_zetaZeroOrdinate]
  -- the order at `z` is finite
  have htop : analyticOrderAt riemannZeta z ≠ ⊤ := by
    rw [← CS.analyticOrderAt_xiF h1 h2]; exact CS.analyticOrderAt_xiF_ne_top z
  set N := (analyticOrderAt riemannZeta z).toNat with hN
  have hord : analyticOrderAt riemannZeta z = (N : ℕ∞) := (ENat.natCast_toNat htop).symm
  set S := {i : zetaZeroIndex | i.1.1 = z} with hS
  by_cases hz : riemannZeta z = 0
  · -- `S` is in bijection with `{k | k < N}` by `i ↦ i.1.2`
    have hinj : Set.InjOn (fun i : zetaZeroIndex => i.1.2) S := by
      intro i hi j hj hij
      exact Subtype.ext (Prod.ext (hi.trans hj.symm) hij)
    have himg : (fun i : zetaZeroIndex => i.1.2) '' S = ((Finset.range N : Finset ℕ) : Set ℕ) := by
      ext k
      simp only [Set.mem_image, Finset.coe_range, Set.mem_Iio]
      constructor
      · rintro ⟨i, hi, rfl⟩
        have := i.2.2
        rw [show i.1.1 = z from hi, hord] at this
        exact_mod_cast this
      · intro hk
        refine ⟨⟨(z, k), ⟨h1, h2, hz⟩, ?_⟩, rfl, rfl⟩
        simp only
        rw [hord]
        exact_mod_cast hk
    rw [← hinj.encard_image, himg, Set.encard_coe_eq_coe_finsetCard, Finset.card_range, hord]
  · -- no zero at `z`: the fibre is empty and the order is `0`
    have hS0 : S = ∅ := by
      ext i
      simp only [hS, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hz (h ▸ i.2.1.2.2)
    have hz1 : z ≠ 1 := fun h => by rw [h] at h2; simp at h2
    have han : AnalyticAt ℂ riemannZeta z := by
      have hd : DifferentiableOn ℂ riemannZeta {t : ℂ | t ≠ 1} := fun t ht =>
        (differentiableAt_riemannZeta ht).differentiableWithinAt
      exact hd.analyticAt (isOpen_ne.mem_nhds hz1)
    rw [hS0, Set.encard_empty, han.analyticOrderAt_eq_zero.2 hz]

/-- **An enumeration of the nontrivial zeros with multiplicity exists.** -/
theorem exists_nontrivialZeroFamily : ∃ (ι : Type) (γ : ι → ℂ), NontrivialZeroFamily γ :=
  ⟨zetaZeroIndex, zetaZeroOrdinate, nontrivialZeroFamily_zetaZeroOrdinate⟩

/-- **The explicit formula for the concrete enumeration of the nontrivial zeros**, with nothing assumed about `γ`: for
`c > 1` and `g` smooth with compact support, `∑_{(z, k)} ∫ g(x) e^{iγx} dx` (`γ = -i(z - 1/2)`, each zero `z` counted
`ord_z ζ` times) converges absolutely and equals the right side of Weil's explicit formula. -/
theorem explicit_formula_zetaZeros {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hgs : HasCompactSupport g) :
    Summable (fun i : zetaZeroIndex => ∫ x : ℝ, g x * Complex.exp (I * zetaZeroOrdinate i * x)) ∧
      ∑' i : zetaZeroIndex, ∫ x : ℝ, g x * Complex.exp (I * zetaZeroOrdinate i * x) = efRHS c g :=
  explicit_formula_of_smooth hc hg hgs nontrivialZeroFamily_zetaZeroOrdinate

end ProofPhase.GRH.CSTie
