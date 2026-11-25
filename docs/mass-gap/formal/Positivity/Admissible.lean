/-
The admissible Wilson measure is reflection positive (positivity project, 2026-11-21). Released under Apache 2.0.

# Admissible Wilson measure

Luescher's admissibility condition asks every plaquette's shortfall `‖1 − U_p‖` to stay below a bound `ε`; for a unitary
`n × n` matrix `‖1 − U‖² = 2n − 2 Re tr U`, so the condition is `n − Re tr U_p ≤ ε` (with `ε` rescaled). The admissible Wilson
weight is `∏_p exp (β Re tr U_p) · 1[n − Re tr U_p ≤ ε]`. The project owner reads this as the Yang-Mills counterpart of the
DMP existence rule ("only DMP-complete systems exist"): the admissible configurations are the ones that exist.

Scope: this file proves only that the *site-reflection* positivity of `Positivity.General` applies to this weight, for every
real `β` and every `ε ≥ 0` (indeed every real `ε`), for SU(2), U(n) and SU(n). It says nothing about the owner's physical
reading, about the continuum limit, or about link-reflection positivity (see the end of `Positivity.General`).
-/

import Positivity.General
import AreaLaw.ConcreteSUn

open MeasureTheory Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace Positivity

open AreaLaw.Concrete AreaLaw.ConcreteSUn

/-- The admissible plaquette weight `x ↦ exp (β x) · 1[n − x ≤ ε]` (`x = Re tr U_p`; `n − x` is the shortfall). -/
def admissibleWeight (n : ℕ) (β ε : ℝ) (x : ℝ) : ℝ :=
  Real.exp (β * x) * (if (n : ℝ) - x ≤ ε then 1 else 0)

theorem plaqWeight_admissible (n : ℕ) (β ε : ℝ) : PlaqWeight n (admissibleWeight n β ε) where
  meas := by
    unfold admissibleWeight
    exact (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      (Measurable.ite (measurableSet_le (measurable_const.sub measurable_id) measurable_const) measurable_const
        measurable_const)
  nonneg := fun x _ => by
    unfold admissibleWeight
    split_ifs <;> simp [(Real.exp_pos _).le]
  bdd := ⟨Real.exp (|β| * n), fun x hx => by
    unfold admissibleWeight
    have h1 : Real.exp (β * x) ≤ Real.exp (|β| * n) := by
      refine Real.exp_le_exp.mpr ?_
      calc β * x ≤ |β * x| := le_abs_self _
        _ = |β| * |x| := abs_mul _ _
        _ ≤ |β| * n := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    split_ifs
    · rw [mul_one, abs_of_pos (Real.exp_pos _)]; exact h1
    · simp [(Real.exp_pos _).le]⟩

variable {d N : ℕ} [NeZero d] [NeZero N]

section General

variable {G : Type*} [Group G] {n : ℕ} [HasGaugeTrace G n]
  [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [HasHaarProbability G] [(haarG G).IsInvInvariant]

/-- **Reflection positivity of the admissible Wilson measure (site reflection).** The weight is
    `∏_p exp (β Re tr U_p) · 1[n − Re tr U_p ≤ ε]`: the Wilson weight restricted to configurations whose every plaquette
    has shortfall at most `ε` (Luescher admissibility; the owner's reading: DMP-admissible configurations). For every real
    `β` and `ε` and every bounded measurable `F` of the closed positive half, `∫ F · (F ∘ Θ) · weight ≥ 0`. -/
theorem admissible_rp (hN : Even N) (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ) (β ε : ℝ)
    {F : GaugeConnection G d N → ℝ} (hF : LinkDep F (posHalfLinks d N)) (mF : Measurable F)
    (bF : ∃ M, ∀ U, |F U| ≤ M) :
    0 ≤ ∫ U, F U * F (thetaConn U) *
        ∏ p ∈ (univ : Finset (LatticePlaquette d N)), admissibleWeight n β ε (xp n p U)
      ∂(productHaar G d N) :=
  rp_plaquette_weight hN hc hU (plaqWeight_admissible n β ε) hF mF bF

end General

/-- **Admissible SU(2) lattice gauge theory is reflection positive** (site reflection, any `β`, any `ε`). -/
theorem admissible_rp_SU2 (hN : Even N) (β ε : ℝ) {F : GaugeConnection SU2 d N → ℝ}
    (hF : LinkDep F (posHalfLinks d N)) (mF : Measurable F) (bF : ∃ M, ∀ U, |F U| ≤ M) :
    0 ≤ ∫ U, F U * F (thetaConn U) *
        ∏ p ∈ (univ : Finset (LatticePlaquette d N)), admissibleWeight 2 β ε (xp 2 p U)
      ∂(productHaar SU2 d N) :=
  admissible_rp hN continuous_subtype_val (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) β ε hF mF bF

/-- **Admissible U(n) lattice gauge theory is reflection positive** (site reflection, any `β`, any `ε`). -/
theorem admissible_rp_Un (n : ℕ) (hN : Even N) (β ε : ℝ) {F : GaugeConnection (Un n) d N → ℝ}
    (hF : LinkDep F (posHalfLinks d N)) (mF : Measurable F) (bF : ∃ M, ∀ U, |F U| ≤ M) :
    0 ≤ ∫ U, F U * F (thetaConn U) *
        ∏ p ∈ (univ : Finset (LatticePlaquette d N)), admissibleWeight n β ε (xp n p U)
      ∂(productHaar (Un n) d N) :=
  admissible_rp hN continuous_subtype_val (fun g => g.2) β ε hF mF bF

instance (n : ℕ) : (haarG (SUn n)).IsInvInvariant := by
  show (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (SUn n))).IsInvInvariant
  have := isProbabilityMeasure_haarMeasure_top (G := SUn n)
  exact isInvInvariant_of_compact _

/-- **Admissible SU(n) lattice gauge theory is reflection positive** (site reflection, any `β`, any `ε`). -/
theorem admissible_rp_SUn (n : ℕ) (hN : Even N) (β ε : ℝ) {F : GaugeConnection (SUn n) d N → ℝ}
    (hF : LinkDep F (posHalfLinks d N)) (mF : Measurable F) (bF : ∃ M, ∀ U, |F U| ≤ M) :
    0 ≤ ∫ U, F U * F (thetaConn U) *
        ∏ p ∈ (univ : Finset (LatticePlaquette d N)), admissibleWeight n β ε (xp n p U)
      ∂(productHaar (SUn n) d N) :=
  admissible_rp hN (continuous_rep_SUn n) (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) β ε hF mF bF

end Positivity
