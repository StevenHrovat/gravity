/-
Reflection positivity for SU(2) and U(n) (positivity project, 2026-11-21). Released under Apache 2.0.

# Haar measure on a compact group is inversion invariant; the concrete reflection-positivity theorems

Mathlib proves inversion invariance of Haar measure only for commutative groups. For a compact group we show it here:
the normalised Haar measure `μ` is right invariant (the right translate of `μ` is a left-invariant probability measure,
hence equal to `μ` by uniqueness), so `μ.inv` is a left-invariant probability measure, hence `μ.inv = μ`
(`isInvInvariant_of_compact`). Then `wilson_rp` applies to SU(2) and U(n) (`wilson_rp_SU2`, `wilson_rp_Un`).
-/

import Positivity.Wilson

open MeasureTheory Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace Positivity

open AreaLaw.Concrete

section Compact

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- A Haar probability measure on a compact group is right invariant. -/
theorem isMulRightInvariant_of_compact (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    μ.IsMulRightInvariant := by
  constructor
  intro g
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace (Measure.map (· * g) μ) μ
  have hc : Measure.haarScalarFactor (Measure.map (· * g) μ) μ = 1 := by
    have := congrArg (fun m : Measure G => m Set.univ) h
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
      Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ] at this
    rw [ENNReal.smul_def, smul_eq_mul, mul_one] at this
    exact ENNReal.coe_eq_one.mp this.symm
  rw [h, hc, one_smul]

/-- **Haar measure on a compact group is inversion invariant.** -/
theorem isInvInvariant_of_compact (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] : μ.IsInvInvariant := by
  have := isMulRightInvariant_of_compact μ
  constructor
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace μ.inv μ
  have hc : Measure.haarScalarFactor μ.inv μ = 1 := by
    have := congrArg (fun m : Measure G => m Set.univ) h
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, Measure.inv_apply, Set.inv_univ] at this
    rw [ENNReal.smul_def, smul_eq_mul, mul_one] at this
    exact ENNReal.coe_eq_one.mp this.symm
  rw [h, hc, one_smul]

end Compact

instance : (haarG SU2).IsInvInvariant := by
  show (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts SU2)).IsInvInvariant
  have := isProbabilityMeasure_haarMeasure_top (G := SU2)
  exact isInvInvariant_of_compact _

instance (n : ℕ) : (haarG (Un n)).IsInvInvariant := by
  show (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (Un n))).IsInvInvariant
  have := isProbabilityMeasure_haarMeasure_top (G := Un n)
  exact isInvInvariant_of_compact _

variable {d N : ℕ} [NeZero d] [NeZero N]

/-- **Reflection positivity of SU(2) lattice gauge theory** (Wilson action, site reflection `t ↦ −t` on the periodic
    lattice (ℤ/Nℤ)^d, `N` even, any real `β`): for every bounded measurable `F` depending only on the links of the closed
    positive half `0 ≤ t ≤ N/2`, `∫ F · (F ∘ Θ) · ∏_p exp(β Re tr U_p) d(productHaar) ≥ 0`. -/
theorem wilson_rp_SU2 (hN : Even N) (β : ℝ) {F : GaugeConnection SU2 d N → ℝ} (hF : LinkDep F (posHalfLinks d N))
    (mF : Measurable F) (bF : ∃ M, ∀ U, |F U| ≤ M) :
    0 ≤ ∫ U, F U * F (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 2 p U)
      ∂(productHaar SU2 d N) :=
  wilson_rp hN continuous_subtype_val (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) β hF mF bF

/-- **Reflection positivity of U(n) lattice gauge theory** (Wilson action, site reflection). -/
theorem wilson_rp_Un (n : ℕ) (hN : Even N) (β : ℝ) {F : GaugeConnection (Un n) d N → ℝ}
    (hF : LinkDep F (posHalfLinks d N)) (mF : Measurable F) (bF : ∃ M, ∀ U, |F U| ≤ M) :
    0 ≤ ∫ U, F U * F (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U)
      ∂(productHaar (Un n) d N) :=
  wilson_rp hN continuous_subtype_val (fun g => g.2) β hF mF bF

/-- Gram positivity for SU(2). -/
theorem wilson_rp_gram_SU2 (hN : Even N) (β : ℝ) {ι : Type*} (s : Finset ι) (Fs : ι → GaugeConnection SU2 d N → ℝ)
    (hFs : ∀ i ∈ s, LinkDep (Fs i) (posHalfLinks d N) ∧ Measurable (Fs i) ∧ ∃ M, ∀ U, |Fs i U| ≤ M) (z : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, z i * z j *
      ∫ U, Fs i U * Fs j (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 2 p U)
        ∂(productHaar SU2 d N) :=
  wilson_rp_gram hN continuous_subtype_val (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) β s Fs hFs z

/-- Gram positivity for U(n). -/
theorem wilson_rp_gram_Un (n : ℕ) (hN : Even N) (β : ℝ) {ι : Type*} (s : Finset ι)
    (Fs : ι → GaugeConnection (Un n) d N → ℝ)
    (hFs : ∀ i ∈ s, LinkDep (Fs i) (posHalfLinks d N) ∧ Measurable (Fs i) ∧ ∃ M, ∀ U, |Fs i U| ≤ M) (z : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, z i * z j *
      ∫ U, Fs i U * Fs j (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U)
        ∂(productHaar (Un n) d N) :=
  wilson_rp_gram hN continuous_subtype_val (fun g => g.2) β s Fs hFs z

end Positivity
