/-
Proof phase, generalisation phase 2: the projection of matrices onto SU(N) by polar decomposition (2026-11-23).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 2.
-/

import ProofPhase.General.SUN
import Mathlib.Analysis.Matrix.Order

/-!
# The projection onto SU(N)

For SU(2) the repository uses the explicit `A ↦ A / √|det A|` (`RouteA.projSU2`). For SU(N) there is no such formula;
the projection is built from the polar decomposition and a determinant root:

* `polarFactor A = A (A* A)^{-1/2}` (the unitary factor of `A`, defined when `A` is invertible; `(A* A)^{1/2}` is the
  continuous-functional-calculus square root `CFC.sqrt`);
* `phaseFix U = e^{-i arg(det U) / N} U` (multiplying a unitary matrix by this phase turns its determinant of modulus
  one into `1`);
* `projSUN N A` is the result if it lies in `SU(N)`, and `1` otherwise ("constant elsewhere").

The one property the package uses is `proj_rep`: `projSUN N` is the identity on `SU(N)` (`projSUN_coe`). In addition:

* on every invertible matrix the candidate lies in `SU(N)` (`projVal_mem_of_det_ne_zero`), so `projSUN N A = projVal N A`
  there (`projSUN_val_of_det_ne_zero`) and the "constant elsewhere" clause only concerns singular matrices;
* the map is measurable (`ProofPhase.General.measurable_projSUN`, in `Meas.lean`).

Continuity near `SU(N)` is not stated: it follows from the same continuity of `CFC.sqrt` on positive matrices that
the measurability proof uses, but no generic file needs it.
-/

open scoped MatrixOrder Matrix Classical ComplexOrder

open MeasureTheory Finset

noncomputable section

namespace ProofPhase.General

section Polar

variable {N : ℕ}

/-- The unitary factor of the polar decomposition `A = U P`: `U = A (A* A)^{-1/2}`. -/
def polarFactor (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  A * (CFC.sqrt (Aᴴ * A))⁻¹

/-- Multiplication by the phase `e^{-i arg(det U)/N}`: the `N`-th root of the inverse phase of the determinant. -/
def phaseFix (N : ℕ) (U : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Complex.exp (((-(Complex.arg U.det) / N : ℝ) : ℂ) * Complex.I) • U

/-- The candidate projection: polar factor, then the phase correction. -/
def projVal (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ := phaseFix N (polarFactor A)

/-- **The projection onto SU(N)**: `projVal N A` where that lies in `SU(N)`, and the identity `1` elsewhere. -/
def projSUN (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : SUN N :=
  if h : projVal N A ∈ Matrix.specialUnitaryGroup (Fin N) ℂ then ⟨projVal N A, h⟩ else 1

theorem polarFactor_of_unitary {g : Matrix (Fin N) (Fin N) ℂ} (hg : g ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    polarFactor g = g := by
  have h1 : gᴴ * g = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hg
    rwa [Matrix.star_eq_conjTranspose] at this
  simp [polarFactor, h1, CFC.sqrt_one]

theorem phaseFix_of_det_one {g : Matrix (Fin N) (Fin N) ℂ} (hg : g.det = 1) : phaseFix N g = g := by
  simp [phaseFix, hg]

/-- **The projection fixes SU(N).** -/
theorem projVal_of_mem (g : SUN N) : projVal N (g : Matrix (Fin N) (Fin N) ℂ) = g := by
  have hu : (g : Matrix (Fin N) (Fin N) ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ := g.2.1
  have hd : (g : Matrix (Fin N) (Fin N) ℂ).det = 1 := g.2.2
  rw [projVal, polarFactor_of_unitary hu]
  exact phaseFix_of_det_one hd

/-- **`projSUN` is a left inverse of the inclusion `SU(N) ⊆ M_N(ℂ)`** (the field `proj_rep` of `GaugeSubst`). -/
theorem projSUN_coe (g : SUN N) : projSUN N (g : Matrix (Fin N) (Fin N) ℂ) = g := by
  have hm : projVal N (g : Matrix (Fin N) (Fin N) ℂ) ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
    rw [projVal_of_mem]; exact g.2
  unfold projSUN
  split_ifs
  exact Subtype.ext (projVal_of_mem g)

end Polar

/-! ## The set where the projection is defined: the invertible matrices -/

section Defined

variable {N : ℕ}

theorem sqrt_gram_mul_self (A : Matrix (Fin N) (Fin N) ℂ) :
    CFC.sqrt (Aᴴ * A) * CFC.sqrt (Aᴴ * A) = Aᴴ * A :=
  CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.2 (Matrix.posSemidef_conjTranspose_mul_self A))

theorem sqrt_gram_hermitian (A : Matrix (Fin N) (Fin N) ℂ) : (CFC.sqrt (Aᴴ * A))ᴴ = CFC.sqrt (Aᴴ * A) :=
  (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg (Aᴴ * A))).isHermitian

theorem det_sqrt_gram_ne_zero {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) : (CFC.sqrt (Aᴴ * A)).det ≠ 0 := by
  intro h
  have hS : (Aᴴ * A).det = 0 := by rw [← sqrt_gram_mul_self A, Matrix.det_mul, h, zero_mul]
  rw [Matrix.det_mul, Matrix.det_conjTranspose] at hS
  rcases mul_eq_zero.1 hS with h1 | h1
  · exact hA (by simpa using h1)
  · exact hA h1

/-- **The polar factor of an invertible matrix is unitary.** -/
theorem polarFactor_mem_unitary {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) :
    polarFactor A ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  set P := CFC.sqrt (Aᴴ * A) with hP
  have hdet : IsUnit P.det := isUnit_iff_ne_zero.2 (det_sqrt_gram_ne_zero hA)
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hdet
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  show (A * P⁻¹)ᴴ * (A * P⁻¹) = 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hP, sqrt_gram_hermitian, ← hP]
  calc P⁻¹ * Aᴴ * (A * P⁻¹) = P⁻¹ * (Aᴴ * A) * P⁻¹ := by simp only [Matrix.mul_assoc]
    _ = P⁻¹ * (P * P) * P⁻¹ := by rw [hP, sqrt_gram_mul_self]
    _ = (P⁻¹ * P) * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]

/-- **On invertible matrices the candidate lies in SU(N)**, so `projSUN N A = projVal N A` there: the "constant
elsewhere" clause of `projSUN` only concerns singular matrices. -/
theorem projVal_mem_of_det_ne_zero {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) [NeZero N] :
    projVal N A ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
  set U := polarFactor A with hU
  have hUu : U ∈ Matrix.unitaryGroup (Fin N) ℂ := polarFactor_mem_unitary hA
  set u := U.det with hu
  have hun : ‖u‖ = 1 := by
    have h1 : u * star u = 1 := (Matrix.det_of_mem_unitary hUu).2
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h1
    have h2 : ‖u‖ ^ 2 = 1 := by exact_mod_cast h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg u) two_ne_zero).1 h2
  set c : ℂ := Complex.exp (((-(Complex.arg u) / N : ℝ) : ℂ) * Complex.I) with hc
  have hcn : ‖c‖ = 1 := by rw [hc]; exact Complex.norm_exp_ofReal_mul_I _
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    show (c • U)ᴴ * (c • U) = 1
    have hU1 : Uᴴ * U = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.1 hUu
      rwa [Matrix.star_eq_conjTranspose] at this
    rw [Matrix.conjTranspose_smul, smul_mul_smul, hU1]
    have : star c * c = 1 := by
      rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hcn]; simp
    rw [this, one_smul]
  · show (c • U).det = 1
    rw [Matrix.det_smul, Fintype.card_fin, ← hu, hc, ← Complex.exp_nat_mul]
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
    have : (N : ℂ) * (((-(Complex.arg u) / N : ℝ) : ℂ) * Complex.I) = -(Complex.arg u : ℂ) * Complex.I := by
      push_cast; field_simp
    rw [this]
    have h3 : u = Complex.exp ((Complex.arg u : ℂ) * Complex.I) := by
      have := (Complex.norm_mul_exp_arg_mul_I u).symm
      rw [hun] at this
      simpa using this
    calc Complex.exp (-(Complex.arg u : ℂ) * Complex.I) * u
        = Complex.exp (-(Complex.arg u : ℂ) * Complex.I) * Complex.exp ((Complex.arg u : ℂ) * Complex.I) :=
          congrArg _ h3
      _ = 1 := by rw [← Complex.exp_add]; ring_nf; simp

/-- On invertible matrices `projSUN` is the polar projection with phase correction. -/
theorem projSUN_val_of_det_ne_zero [NeZero N] {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) :
    ((projSUN N A : SUN N) : Matrix (Fin N) (Fin N) ℂ) = projVal N A := by
  simp [projSUN, projVal_mem_of_det_ne_zero hA]
end Defined

end ProofPhase.General
