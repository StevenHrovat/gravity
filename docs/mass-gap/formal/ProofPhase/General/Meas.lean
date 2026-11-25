/-
Proof phase, generalisation phase 2: measurability of the projection onto SU(N) (2026-11-23).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 2.
-/

import ProofPhase.General.Projection
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable

open scoped MatrixOrder Matrix ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

noncomputable section

namespace ProofPhase.General

variable {N : ℕ}

theorem measurable_sqrtGram :
    Measurable (fun A : Matrix (Fin N) (Fin N) ℂ => CFC.sqrt (Aᴴ * A)) :=
  CFC.measurable_sqrt.comp (by fun_prop)


/-- Matrix inversion is measurable (`P⁻¹ = (det P)⁻¹ adj P`). -/
theorem measurable_matrix_inv : Measurable (fun P : Matrix (Fin N) (Fin N) ℂ => P⁻¹) := by
  have e : (fun P : Matrix (Fin N) (Fin N) ℂ => P⁻¹) = fun P => (P.det)⁻¹ • P.adjugate := by
    funext P
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [e]
  have h1 : Measurable (fun P : Matrix (Fin N) (Fin N) ℂ => (P.det)⁻¹) :=
    (continuous_id.matrix_det.measurable).inv
  have h2 : Continuous (fun P : Matrix (Fin N) (Fin N) ℂ => P.adjugate) := continuous_id.matrix_adjugate
  exact (continuous_smul.measurable).comp (h1.prodMk h2.measurable)

theorem measurable_polarFactor : Measurable (polarFactor (N := N)) := by
  unfold polarFactor
  have h1 : Measurable (fun A : Matrix (Fin N) (Fin N) ℂ => (CFC.sqrt (Aᴴ * A))⁻¹) :=
    measurable_matrix_inv.comp measurable_sqrtGram
  exact (continuous_fst.matrix_mul continuous_snd).measurable.comp (measurable_id.prodMk h1)

theorem measurable_phaseFix : Measurable (phaseFix N) := by
  unfold phaseFix
  have h1 : Measurable (fun U : Matrix (Fin N) (Fin N) ℂ => Complex.arg U.det) :=
    Complex.measurable_arg.comp continuous_id.matrix_det.measurable
  have h2 : Measurable (fun U : Matrix (Fin N) (Fin N) ℂ =>
      Complex.exp (((-(Complex.arg U.det) / N : ℝ) : ℂ) * Complex.I)) := by
    have : Measurable (fun U : Matrix (Fin N) (Fin N) ℂ => (-(Complex.arg U.det) / N : ℝ)) :=
      (h1.neg).div_const _
    exact Complex.continuous_exp.measurable.comp ((Complex.measurable_ofReal.comp this).mul_const _)
  exact (continuous_smul.measurable).comp (h2.prodMk measurable_id)

theorem measurable_projVal : Measurable (projVal N) := measurable_phaseFix.comp measurable_polarFactor

/-- **The projection onto SU(N) is measurable.** -/
theorem measurable_projSUN : Measurable (projSUN N) := by
  classical
  have hclosed : IsClosed (Matrix.specialUnitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) :=
    (isCompact_SUN N).isClosed
  have hset : MeasurableSet {A : Matrix (Fin N) (Fin N) ℂ |
      projVal N A ∈ Matrix.specialUnitaryGroup (Fin N) ℂ} :=
    (by exact measurable_projVal hclosed.measurableSet)
  have hf : Measurable (fun A : Matrix (Fin N) (Fin N) ℂ =>
      if projVal N A ∈ Matrix.specialUnitaryGroup (Fin N) ℂ
        then projVal N A else 1) :=
    Measurable.ite hset measurable_projVal measurable_const
  have hmem : ∀ A : Matrix (Fin N) (Fin N) ℂ,
      (if projVal N A ∈ Matrix.specialUnitaryGroup (Fin N) ℂ
        then projVal N A else 1) ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
    intro A
    split_ifs with h
    · exact h
    · exact (1 : SUN N).2
  have e : projSUN N = fun A => ⟨_, hmem A⟩ := by
    funext A
    apply Subtype.ext
    unfold projSUN
    split_ifs <;> rfl
  rw [e]
  exact hf.subtype_mk
end ProofPhase.General
