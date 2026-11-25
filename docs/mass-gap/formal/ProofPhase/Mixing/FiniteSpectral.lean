/-
P vs NP dictionary, item 2 of "Missing": the spectral theorem for the heat bath on a finite system
(2026-11-23). Released under Apache 2.0.

Paper: `docs/pnp/ITEMS.md`.
-/

import ProofPhase.Mixing.Classical
import ProofPhase.Mixing.Link

/-!
# The spectral theorem for the heat bath on a finite system

`Link.lean` takes the spectral representation `hrep` of the random-scan operator, and its support in `[0, 1]`, as
hypotheses. For a finite site set and a finite single-site space (positive weights) this file **proves** both, so that
the spectral gap statement has no spectral hypothesis.

**Steps.**
* `exists_spectral_measure`: a real symmetric matrix `B` with `0 ≤ ⟨v, B v⟩ ≤ ⟨v, v⟩` and a vector `h` give a finite
  measure `ρ`, a finite sum of point masses at the eigenvalues, carried by `[0, 1]`, with `∫ λ^k dρ = ⟨h, B^k h⟩`.
  Built from Mathlib's finite-dimensional spectral theorem (`Matrix.IsHermitian.spectral_theorem`); the identity
  `⟨h, B^k h⟩ = Σ_j λ_j^k c_j²` is `quad_pow_eq`.
* The heat-bath update at one site is `K x`, the conditional expectation given the other spins. Conjugated by the
  square roots of the weights, `Bx = D^{1/2} K x D^{-1/2}` is a **symmetric idempotent matrix** (`Bx_symm`, `Bx_idem`,
  from reversibility and `K_mul_K`), so `0 ≤ ⟨v, Bx v⟩ ≤ ⟨v, v⟩` (`quad_proj`). The random-scan operator is the average
  `Bm` of the `Bx`, so it is a symmetric positive contraction (`Bm_quad`).
* `heatBath_integral_iterate`: the sampler's law after `k` steps acts on test functions as the `k`-th power of the
  matrix `R = D^{-1/2} Bm D^{1/2}`; `timeCorr_eq`: the time correlation `C_F(k)` of `Link.lean` is `⟨h, B^k h⟩` with
  `h = √μ · (F - μ F)`.

**Main results.**
* `timeCorr_spectral`: for every function `F` there is a finite measure `ρ` on `[0, 1]` (a finite sum of point masses)
  with `acorr ρ k = timeCorr F k` for all `k`. This is `hrep` together with `h0`, `h1` of `spectral_gap_of_column`.
* `spectral_gap_dobrushin`: with the classical Dobrushin column condition `Σ_x dob μ x z ≤ α < 1` only: the spectral
  measure of any `F` for the random-scan heat bath has no mass above `1 - (1 - α)/n`. No coupling and no spectral
  hypothesis; `Classical.lean` supplies the coupling.

Nothing is assumed beyond positive weights of a finite system. Standard axioms only.
-/

open MeasureTheory Matrix Finset ProofPhase.OneBox

open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Mixing

/-! ### The spectral measure of a symmetric matrix -/

section Abstract

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The orthogonal matrix of eigenvectors of a real symmetric matrix (Mathlib's finite-dimensional spectral theorem). -/
def eigU {B : Matrix Ω Ω ℝ} (hB : B.IsHermitian) : Matrix Ω Ω ℝ := hB.eigenvectorUnitary

theorem eigU_transpose_mul {B : Matrix Ω Ω ℝ} (hB : B.IsHermitian) : (eigU hB)ᵀ * eigU hB = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.mp hB.eigenvectorUnitary.2
  rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this

theorem eigU_mul_transpose {B : Matrix Ω Ω ℝ} (hB : B.IsHermitian) : eigU hB * (eigU hB)ᵀ = 1 := by
  have := Matrix.mem_unitaryGroup_iff.mp hB.eigenvectorUnitary.2
  rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this

theorem eig_spectral {B : Matrix Ω Ω ℝ} (hB : B.IsHermitian) :
    B = eigU hB * diagonal hB.eigenvalues * (eigU hB)ᵀ := by
  have := hB.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at this
  simpa [eigU, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this

/-- **The spectral expansion of the quadratic forms of the powers**: `⟨h, B^k h⟩ = Σ_j λ_j^k c_j²`, with `λ_j` the
eigenvalues and `c = Uᵀ h` the coordinates of `h` in the eigenbasis. -/
theorem quad_pow_eq (B : Matrix Ω Ω ℝ) (hB : B.IsHermitian) (k : ℕ) (h : Ω → ℝ) :
    h ⬝ᵥ ((B ^ k) *ᵥ h) = ∑ j, hB.eigenvalues j ^ k * ((eigU hB)ᵀ *ᵥ h) j ^ 2 := by
  set U : Matrix Ω Ω ℝ := eigU hB with hU
  have h1 : Uᵀ * U = 1 := eigU_transpose_mul hB
  have h2 : U * Uᵀ = 1 := eigU_mul_transpose hB
  have hspec : B = U * diagonal hB.eigenvalues * Uᵀ := eig_spectral hB
  have conj : ∀ X Y : Matrix Ω Ω ℝ, (U * X * Uᵀ) * (U * Y * Uᵀ) = U * (X * Y) * Uᵀ := fun X Y => by
    calc (U * X * Uᵀ) * (U * Y * Uᵀ) = U * X * (Uᵀ * U) * Y * Uᵀ := by noncomm_ring
      _ = U * (X * Y) * Uᵀ := by rw [h1]; noncomm_ring
  have hpow : ∀ k : ℕ, B ^ k = U * diagonal (fun j => hB.eigenvalues j ^ k) * Uᵀ := by
    intro k
    induction k with
    | zero => simp [h2]
    | succ k ih =>
      calc B ^ (k + 1) = B ^ k * B := pow_succ B k
        _ = (U * diagonal (fun j => hB.eigenvalues j ^ k) * Uᵀ) * (U * diagonal hB.eigenvalues * Uᵀ) := by
            rw [ih]; exact congrArg _ hspec
        _ = U * diagonal (fun j => hB.eigenvalues j ^ (k + 1)) * Uᵀ := by
            rw [conj, Matrix.diagonal_mul_diagonal]
            congr 3
  rw [hpow k, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have hv : h ᵥ* U = Uᵀ *ᵥ h := by simpa using Matrix.vecMul_transpose Uᵀ h
  rw [hv]
  unfold dotProduct
  exact Finset.sum_congr rfl fun j _ => by rw [Matrix.mulVec_diagonal]; ring

/-- **Finite spectral measure.** A real symmetric matrix `B` with `0 ≤ ⟨v, B v⟩ ≤ ⟨v, v⟩` for all `v` and a vector `h`:
there is a finite measure `ρ` on `ℝ`, a finite sum of point masses at the eigenvalues, carried by `[0, 1]`, whose moments
are the quadratic forms of the powers: `∫ λ^k dρ = ⟨h, B^k h⟩`. -/
theorem exists_spectral_measure (B : Matrix Ω Ω ℝ) (hB : B.IsHermitian)
    (hq0 : ∀ v : Ω → ℝ, 0 ≤ v ⬝ᵥ (B *ᵥ v)) (hq1 : ∀ v : Ω → ℝ, v ⬝ᵥ (B *ᵥ v) ≤ v ⬝ᵥ v) (h : Ω → ℝ) :
    ∃ ρ : Measure ℝ, IsFiniteMeasure ρ ∧ (∀ᵐ l ∂ρ, 0 ≤ l) ∧ (∀ᵐ l ∂ρ, l ≤ 1) ∧
      ∀ k : ℕ, ∫ l, l ^ k ∂ρ = h ⬝ᵥ ((B ^ k) *ᵥ h) := by
  have h1 : (eigU hB)ᵀ * eigU hB = 1 := eigU_transpose_mul hB
  have hsum : ∀ (j : Ω) (k : ℕ), ∑ i, hB.eigenvalues i ^ k * ((Pi.single j (1 : ℝ) : Ω → ℝ) i) ^ 2 =
      hB.eigenvalues j ^ k := by
    intro j k
    simp [Pi.single_apply]
  have hbd : ∀ j, 0 ≤ hB.eigenvalues j ∧ hB.eigenvalues j ≤ 1 := by
    intro j
    set v : Ω → ℝ := eigU hB *ᵥ (Pi.single j (1 : ℝ) : Ω → ℝ) with hv
    have hw : (eigU hB)ᵀ *ᵥ v = (Pi.single j (1 : ℝ) : Ω → ℝ) := by
      rw [hv, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    have e1 := quad_pow_eq B hB 1 v
    have e0 := quad_pow_eq B hB 0 v
    rw [hw, hsum] at e1 e0
    simp only [pow_one, pow_zero, Matrix.one_mulVec] at e1 e0
    exact ⟨e1 ▸ hq0 v, by have := hq1 v; rw [e1, e0] at this; exact this⟩
  set ρ : Measure ℝ := ∑ j, ENNReal.ofReal (((eigU hB)ᵀ *ᵥ h) j ^ 2) • Measure.dirac (hB.eigenvalues j) with hρ
  have hfin : IsFiniteMeasure ρ := ⟨by
    simp only [hρ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
      mul_one]
    exact ENNReal.sum_lt_top.mpr fun j _ => ENNReal.ofReal_lt_top⟩
  have hae : ∀ P : Set ℝ, MeasurableSet P → (∀ j, hB.eigenvalues j ∈ P) → ∀ᵐ l ∂ρ, l ∈ P := by
    intro P hP hj
    rw [ae_iff]
    show ρ Pᶜ = 0
    simp only [hρ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      Measure.dirac_apply' _ hP.compl, smul_eq_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Set.indicator_of_notMem (by simpa using hj j)]
    simp
  refine ⟨ρ, hfin, hae (Set.Ici 0) measurableSet_Ici fun j => (hbd j).1,
    hae (Set.Iic 1) measurableSet_Iic fun j => (hbd j).2, ?_⟩
  intro k
  rw [quad_pow_eq B hB k h, hρ, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
    ring
  · intro j _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem dot_self_nonneg' (g : Ω → ℝ) : 0 ≤ g ⬝ᵥ g := Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- **A symmetric idempotent matrix (an orthogonal projection) has quadratic form between `0` and the norm.** -/
theorem quad_proj {B : Matrix Ω Ω ℝ} (hs : Bᵀ = B) (hi : B * B = B) (v : Ω → ℝ) :
    0 ≤ v ⬝ᵥ (B *ᵥ v) ∧ v ⬝ᵥ (B *ᵥ v) ≤ v ⬝ᵥ v := by
  set g := B *ᵥ v with hg
  have hBg : B *ᵥ g = g := by rw [hg, Matrix.mulVec_mulVec, hi]
  have hvm : g ᵥ* B = B *ᵥ g := by
    have := Matrix.vecMul_transpose B g
    rwa [hs] at this
  have h1 : g ⬝ᵥ g = g ⬝ᵥ v := by
    calc g ⬝ᵥ g = g ⬝ᵥ (B *ᵥ v) := rfl
      _ = (g ᵥ* B) ⬝ᵥ v := Matrix.dotProduct_mulVec _ _ _
      _ = g ⬝ᵥ v := by rw [hvm, hBg]
  have h2 : 0 ≤ (v - g) ⬝ᵥ (v - g) := dot_self_nonneg' _
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm g v] at h2
  have h3 : v ⬝ᵥ g = g ⬝ᵥ g := by rw [dotProduct_comm v g, h1]
  have h4 := dot_self_nonneg' g
  constructor
  · rw [h3]; exact h4
  · linarith

theorem quad_sum {κ : Type*} (s : Finset κ) (A : κ → Matrix Ω Ω ℝ) (v : Ω → ℝ) :
    v ⬝ᵥ ((∑ x ∈ s, A x) *ᵥ v) = ∑ x ∈ s, v ⬝ᵥ (A x *ᵥ v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec, dotProduct_add, ih]

end Abstract

/-! ### The heat bath on a finite system as a symmetric matrix -/

section HeatBathMatrix

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [DiscreteMeasurableSpace S] {μ : Measure (ι → S)}

theorem Agree.trans {x : ι} {σ τ ρ : ι → S} (h : Agree x σ τ) (h' : Agree x τ ρ) : Agree x σ ρ :=
  fun z hz => (h z hz).trans (h' z hz)

/-- The heat bath at one site is idempotent (a conditional expectation). -/
theorem K_mul_K (hpos : ∀ σ : ι → S, 0 < pw μ σ) (x : ι) (σ ρ : ι → S) :
    ∑ τ, K μ x σ τ * K μ x τ ρ = K μ x σ ρ := by
  by_cases hσρ : Agree x σ ρ
  · have hterm : ∀ τ, K μ x σ τ * K μ x τ ρ =
        if Agree x σ τ then (pw μ τ / Zs μ x σ) * (pw μ ρ / Zs μ x σ) else 0 := fun τ => by
      by_cases hτ : Agree x σ τ
      · have hτρ : Agree x τ ρ := hτ.symm.trans hσρ
        simp only [K, hτ, hτρ, ↓reduceIte, Zs_congr hτ]
      · simp [K, hτ]
    simp_rw [hterm]
    rw [sum_agree x σ (fun τ => (pw μ τ / Zs μ x σ) * (pw μ ρ / Zs μ x σ))]
    have hZ : ∑ s, pw μ (Function.update σ x s) / Zs μ x σ * (pw μ ρ / Zs μ x σ) = pw μ ρ / Zs μ x σ := by
      rw [← Finset.sum_mul, ← Finset.sum_div]
      have : ∑ s, pw μ (Function.update σ x s) = Zs μ x σ := rfl
      rw [this, div_self (Zs_pos hpos x σ).ne', one_mul]
    rw [hZ]
    simp [K, hσρ]
  · have hterm : ∀ τ, K μ x σ τ * K μ x τ ρ = 0 := fun τ => by
      by_cases hτ : Agree x σ τ
      · have : ¬ Agree x τ ρ := fun h => hσρ (hτ.trans h)
        simp [K, this]
      · simp [K, hτ]
    rw [Finset.sum_eq_zero fun τ _ => hterm τ]
    simp [K, hσρ]

variable (μ)

/-- `√(μ {σ})`, the square root of the weight. -/
def sq (σ : ι → S) : ℝ := Real.sqrt (pw μ σ)

/-- The heat bath at `x`, conjugated by the square roots of the weights: a symmetric orthogonal projection. -/
def Bx (x : ι) : Matrix (ι → S) (ι → S) ℝ := fun σ τ => sq μ σ * K μ x σ τ / sq μ τ

/-- The random-scan heat-bath operator, conjugated: the average of the projections `Bx`. -/
def Bm : Matrix (ι → S) (ι → S) ℝ := ((Fintype.card ι : ℝ)⁻¹) • ∑ x, Bx μ x

/-- The random-scan heat-bath matrix `R σ τ = (1/n) Σ_x K x σ τ`. -/
def Rm : Matrix (ι → S) (ι → S) ℝ := fun σ τ => (Fintype.card ι : ℝ)⁻¹ * ∑ x, K μ x σ τ

variable {μ}

theorem sq_pos (hpos : ∀ σ : ι → S, 0 < pw μ σ) (σ : ι → S) : 0 < sq μ σ := Real.sqrt_pos.mpr (hpos σ)

theorem sq_mul_self (hpos : ∀ σ : ι → S, 0 < pw μ σ) (σ : ι → S) : sq μ σ * sq μ σ = pw μ σ :=
  Real.mul_self_sqrt (hpos σ).le

theorem Bx_symm (hpos : ∀ σ : ι → S, 0 < pw μ σ) (x : ι) : (Bx μ x)ᵀ = Bx μ x := by
  ext σ τ
  simp only [Matrix.transpose_apply, Bx]
  have h := rev hpos x τ σ
  have hσ := sq_mul_self hpos σ
  have hτ := sq_mul_self hpos τ
  rw [div_eq_div_iff (sq_pos hpos σ).ne' (sq_pos hpos τ).ne']
  rw [← hσ, ← hτ] at h
  linear_combination h

theorem Bx_idem (hpos : ∀ σ : ι → S, 0 < pw μ σ) (x : ι) : Bx μ x * Bx μ x = Bx μ x := by
  ext σ ρ
  simp only [Matrix.mul_apply, Bx]
  have hterm : ∀ τ, sq μ σ * K μ x σ τ / sq μ τ * (sq μ τ * K μ x τ ρ / sq μ ρ) =
      sq μ σ / sq μ ρ * (K μ x σ τ * K μ x τ ρ) := fun τ => by
    have := (sq_pos hpos τ).ne'
    field_simp
  simp_rw [hterm]
  rw [← Finset.mul_sum, K_mul_K hpos]
  have := (sq_pos hpos ρ).ne'
  field_simp

theorem Bm_symm (hpos : ∀ σ : ι → S, 0 < pw μ σ) : (Bm μ)ᵀ = Bm μ := by
  unfold Bm
  rw [Matrix.transpose_smul, Matrix.transpose_sum]
  simp_rw [Bx_symm hpos]

theorem Bm_apply (σ τ : ι → S) : Bm μ σ τ = sq μ σ * Rm μ σ τ / sq μ τ := by
  simp only [Bm, Rm, Matrix.smul_apply, Matrix.sum_apply, Bx, smul_eq_mul]
  have hx : ∀ x, sq μ σ * K μ x σ τ / sq μ τ = sq μ σ / sq μ τ * K μ x σ τ := fun x => by ring
  simp only [hx, ← Finset.mul_sum]
  ring


theorem Bm_isHermitian (hpos : ∀ σ : ι → S, 0 < pw μ σ) : (Bm μ).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact Bm_symm hpos

/-- **The averaged heat bath is a positive contraction**: `0 ≤ ⟨v, B v⟩ ≤ ⟨v, v⟩` (an average of orthogonal projections). -/
theorem Bm_quad (hpos : ∀ σ : ι → S, 0 < pw μ σ) [Nonempty ι] (v : (ι → S) → ℝ) :
    0 ≤ v ⬝ᵥ (Bm μ *ᵥ v) ∧ v ⬝ᵥ (Bm μ *ᵥ v) ≤ v ⬝ᵥ v := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hq : v ⬝ᵥ (Bm μ *ᵥ v) = (Fintype.card ι : ℝ)⁻¹ * ∑ x, v ⬝ᵥ (Bx μ x *ᵥ v) := by
    unfold Bm
    rw [Matrix.smul_mulVec, dotProduct_smul, quad_sum, smul_eq_mul]
  rw [hq]
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hn.le)
      (Finset.sum_nonneg fun x _ => (quad_proj (Bx_symm hpos x) (Bx_idem hpos x) v).1)
  · calc (Fintype.card ι : ℝ)⁻¹ * ∑ x, v ⬝ᵥ (Bx μ x *ᵥ v)
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _x : ι, v ⬝ᵥ v :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun x _ => (quad_proj (Bx_symm hpos x) (Bx_idem hpos x) v).2)
            (inv_nonneg.mpr hn.le)
      _ = v ⬝ᵥ v := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]

/-! #### The operator `R` and its powers -/

theorem Bm_mulVec (hpos : ∀ σ : ι → S, 0 < pw μ σ) (f : (ι → S) → ℝ) :
    (fun σ => sq μ σ * (Rm μ *ᵥ f) σ) = Bm μ *ᵥ (fun σ => sq μ σ * f σ) := by
  funext σ
  simp only [Matrix.mulVec, dotProduct, Bm_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have := (sq_pos hpos τ).ne'
  field_simp

theorem Bm_pow_mulVec (hpos : ∀ σ : ι → S, 0 < pw μ σ) (k : ℕ) (f : (ι → S) → ℝ) :
    (fun σ => sq μ σ * ((Rm μ ^ k) *ᵥ f) σ) = (Bm μ ^ k) *ᵥ (fun σ => sq μ σ * f σ) := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Bm_mulVec hpos, ih]

theorem Rm_row (hpos : ∀ σ : ι → S, 0 < pw μ σ) [Nonempty ι] (σ : ι → S) : ∑ τ, Rm μ σ τ = 1 := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  simp only [Rm]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [sum_K hpos]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ hn.ne'

theorem Rm_const (hpos : ∀ σ : ι → S, 0 < pw μ σ) [Nonempty ι] (c : ℝ) :
    Rm μ *ᵥ (fun _ => c) = fun _ => c := by
  funext σ
  simp only [Matrix.mulVec, dotProduct]
  rw [← Finset.sum_mul, Rm_row hpos, one_mul]

theorem Rm_pow_const (hpos : ∀ σ : ι → S, 0 < pw μ σ) [Nonempty ι] (k : ℕ) (c : ℝ) :
    (Rm μ ^ k) *ᵥ (fun _ => c) = fun _ => c := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Rm_const hpos]

theorem pw_Rm (hpos : ∀ σ : ι → S, 0 < pw μ σ) [Nonempty ι] (τ : ι → S) :
    ∑ σ, pw μ σ * Rm μ σ τ = pw μ τ := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  calc ∑ σ, pw μ σ * Rm μ σ τ = ∑ σ, ∑ x, (Fintype.card ι : ℝ)⁻¹ * (pw μ σ * K μ x σ τ) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        simp only [Rm]
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ = ∑ x, ∑ σ, (Fintype.card ι : ℝ)⁻¹ * (pw μ σ * K μ x σ τ) := Finset.sum_comm
    _ = ∑ _x : ι, (Fintype.card ι : ℝ)⁻¹ * pw μ τ :=
        Finset.sum_congr rfl fun x _ => by rw [← Finset.mul_sum, sum_pK hpos]
    _ = pw μ τ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]

theorem pw_mulVec (hpos : ∀ σ : ι → S, 0 < pw μ σ) [Nonempty ι] (f : (ι → S) → ℝ) :
    ∑ σ, pw μ σ * (Rm μ *ᵥ f) σ = ∑ τ, pw μ τ * f τ := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  calc ∑ σ, pw μ σ * (Rm μ σ τ * f τ) = (∑ σ, pw μ σ * Rm μ σ τ) * f τ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun σ _ => by ring
    _ = pw μ τ * f τ := by rw [pw_Rm hpos τ]

theorem pw_Rm_pow (hpos : ∀ σ : ι → S, 0 < pw μ σ) [Nonempty ι] (k : ℕ) (f : (ι → S) → ℝ) :
    ∑ σ, pw μ σ * ((Rm μ ^ k) *ᵥ f) σ = ∑ σ, pw μ σ * f σ := by
  induction k generalizing f with
  | zero => simp
  | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, ih, pw_mulVec hpos]

/-! #### From the sampler's law to the matrix `R` -/

end HeatBathMatrix

section Sampler

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [DiscreteMeasurableSpace S] {μ : Measure (ι → S)}

namespace SiteDynamics

variable (D : SiteDynamics μ)

theorem isProbabilityMeasure_rsStep [Nonempty ι] (ν : Measure (ι → S)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (D.rsStep ν) := by
  constructor
  rw [rsStep, avg_apply]
  have : ∀ x, ν.bind (D.P x) Set.univ = 1 := fun x => by
    have := isProbabilityMeasure_bind (π := ν) (D.P x)
    exact measure_univ
  simp_rw [this]
  exact card_inv_mul_card _

theorem rsStep_real [Nonempty ι] (ν : Measure (ι → S)) [IsProbabilityMeasure ν] (s : Set (ι → S)) :
    (D.rsStep ν).real s = (Fintype.card ι : ℝ)⁻¹ * ∑ x, (ν.bind (D.P x)).real s := by
  have hp : ∀ x, IsProbabilityMeasure (ν.bind (D.P x)) := fun x => isProbabilityMeasure_bind (D.P x)
  rw [measureReal_def, rsStep, avg_apply, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun x _ => measure_ne_top _ _)]
  rfl

end SiteDynamics

theorem heatBath_P_real [IsFiniteMeasure μ] (hpos : ∀ σ : ι → S, 0 < pw μ σ) (x : ι) (σ τ : ι → S) :
    ((heatBath hpos).P x σ).real {τ} = K μ x σ τ := by
  show (hbKernel μ x σ).real {τ} = _
  rw [hbKernel_apply, measureReal_def, wm_singleton, ENNReal.toReal_ofReal (K_nonneg hpos x σ τ)]

/-- **The law of one random-scan heat-bath step**, from the law `ν`, is `ν R`. -/
theorem heatBath_rsStep_real [IsProbabilityMeasure μ] [Nonempty ι] (hpos : ∀ σ : ι → S, 0 < pw μ σ)
    (ν : Measure (ι → S)) [IsProbabilityMeasure ν] (τ : ι → S) :
    ((heatBath hpos).rsStep ν).real {τ} = ∑ σ, ν.real {σ} * Rm μ σ τ := by
  rw [SiteDynamics.rsStep_real]
  have h1 : ∀ x, (ν.bind ((heatBath hpos).P x)).real {τ} = ∑ σ, ν.real {σ} * K μ x σ τ := fun x => by
    rw [bind_real _ (MeasurableSet.of_discrete), integral_fintype Integrable.of_finite]
    exact Finset.sum_congr rfl fun σ _ => by rw [heatBath_P_real hpos, smul_eq_mul]
  simp_rw [h1]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Rm]
  rw [← Finset.mul_sum]
  ring

/-- **One step, as an operator on test functions**: `∫ F d(ν R) = ∫ (R F) dν`. -/
theorem heatBath_integral_rsStep [IsProbabilityMeasure μ] [Nonempty ι] (hpos : ∀ σ : ι → S, 0 < pw μ σ)
    (ν : Measure (ι → S)) [IsProbabilityMeasure ν] (F : (ι → S) → ℝ) :
    ∫ τ, F τ ∂((heatBath hpos).rsStep ν) = ∫ σ, (Rm μ *ᵥ F) σ ∂ν := by
  have := (heatBath hpos).isProbabilityMeasure_rsStep ν
  rw [integral_fintype Integrable.of_finite, integral_fintype Integrable.of_finite]
  simp_rw [heatBath_rsStep_real hpos ν, smul_eq_mul, Finset.sum_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => by ring

theorem heatBath_integral_iterate [IsProbabilityMeasure μ] [Nonempty ι] (hpos : ∀ σ : ι → S, 0 < pw μ σ)
    (ν : Measure (ι → S)) [IsProbabilityMeasure ν] (k : ℕ) (F : (ι → S) → ℝ) :
    ∫ τ, F τ ∂((heatBath hpos).rsStep^[k] ν) = ∫ σ, ((Rm μ ^ k) *ᵥ F) σ ∂ν := by
  induction k generalizing F with
  | zero => simp
  | succ k ih =>
    have hP : ∀ j : ℕ, IsProbabilityMeasure ((heatBath hpos).rsStep^[j] ν) := by
      intro j
      induction j with
      | zero => simp only [Function.iterate_zero, id_eq]; infer_instance
      | succ j ihj =>
        rw [Function.iterate_succ_apply']
        exact (heatBath hpos).isProbabilityMeasure_rsStep _
    have := hP k
    rw [Function.iterate_succ_apply', heatBath_integral_rsStep hpos _ F, ih, Matrix.mulVec_mulVec, ← pow_succ]

theorem sum_pw [IsProbabilityMeasure μ] : ∑ σ : ι → S, pw μ σ = 1 := by
  simp

theorem rsPow_eq [IsProbabilityMeasure μ] [Nonempty ι] (hpos : ∀ σ : ι → S, 0 < pw μ σ) (F : (ι → S) → ℝ)
    (k : ℕ) (σ : ι → S) : (heatBath hpos).rsPow F k σ = ((Rm μ ^ k) *ᵥ F) σ := by
  unfold SiteDynamics.rsPow
  rw [heatBath_integral_iterate hpos (Measure.dirac σ) k F, integral_dirac]

/-- **The time correlation of the heat bath as a quadratic form of a symmetric matrix**:
`C_F(k) = ⟨h, B^k h⟩` with `h = √μ · (F - μ F)`. -/
theorem timeCorr_eq [IsProbabilityMeasure μ] [Nonempty ι] (hpos : ∀ σ : ι → S, 0 < pw μ σ)
    (F : (ι → S) → ℝ) (k : ℕ) :
    (heatBath hpos).timeCorr F k =
      (fun σ => sq μ σ * (F σ - ∑ τ, pw μ τ * F τ)) ⬝ᵥ
        ((Bm μ ^ k) *ᵥ (fun σ => sq μ σ * (F σ - ∑ τ, pw μ τ * F τ))) := by
  set c : ℝ := ∑ τ, pw μ τ * F τ with hc
  have hcμ : ∫ τ, F τ ∂μ = c := by
    rw [integral_fintype Integrable.of_finite]
    exact Finset.sum_congr rfl fun τ _ => by rw [smul_eq_mul]
  set G : (ι → S) → ℝ := (Rm μ ^ k) *ᵥ F with hG
  have hg : (Rm μ ^ k) *ᵥ (fun σ => F σ - c) = fun σ => G σ - c := by
    have : (fun σ => F σ - c) = F - fun _ => c := rfl
    rw [this, Matrix.mulVec_sub, Rm_pow_const hpos k c]
    rfl
  have hB := Bm_pow_mulVec hpos k (fun σ => F σ - c)
  rw [hg] at hB
  rw [← hB]
  have hdiff : ∑ σ, pw μ σ * (G σ - c) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, sum_pw, hG, pw_Rm_pow hpos k F, ← hc]
    ring
  unfold SiteDynamics.timeCorr
  rw [integral_fintype Integrable.of_finite]
  simp only [dotProduct, smul_eq_mul]
  have e1 : ∀ σ, μ.real {σ} * (F σ * ((heatBath hpos).rsPow F k σ - ∫ τ, F τ ∂μ)) =
      pw μ σ * (F σ * (G σ - c)) := fun σ => by
    rw [rsPow_eq hpos, hcμ]
  simp_rw [e1]
  have e2 : ∀ σ, sq μ σ * (F σ - c) * (sq μ σ * (G σ - c)) = pw μ σ * ((F σ - c) * (G σ - c)) := fun σ => by
    rw [← sq_mul_self hpos σ]; ring
  simp_rw [e2]
  have e3 : ∀ σ, pw μ σ * ((F σ - c) * (G σ - c)) =
      pw μ σ * (F σ * (G σ - c)) - c * (pw μ σ * (G σ - c)) := fun σ => by ring
  simp_rw [e3]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hdiff, mul_zero, sub_zero]

/-- **The spectral measure of the heat bath, no hypothesis.** For every function `F` on configurations there is a
finite measure `ρ` on `[0, 1]`, a finite sum of point masses at the eigenvalues of the (conjugated) random-scan
heat-bath matrix, whose moments are the time correlations: `∫ λ^k dρ = C_F(k)` for all `k`. -/
theorem timeCorr_spectral [IsProbabilityMeasure μ] [Nonempty ι] (hpos : ∀ σ : ι → S, 0 < pw μ σ)
    (F : (ι → S) → ℝ) :
    ∃ ρ : Measure ℝ, IsFiniteMeasure ρ ∧ (∀ᵐ l ∂ρ, 0 ≤ l) ∧ (∀ᵐ l ∂ρ, l ≤ 1) ∧
      ∀ k : ℕ, acorr ρ k = (heatBath hpos).timeCorr F k := by
  obtain ⟨ρ, h1, h2, h3, h4⟩ := exists_spectral_measure (Bm μ) (Bm_isHermitian hpos)
    (fun v => (Bm_quad hpos v).1) (fun v => (Bm_quad hpos v).2)
    (fun σ => sq μ σ * (F σ - ∑ τ, pw μ τ * F τ))
  exact ⟨ρ, h1, h2, h3, fun k => by rw [timeCorr_eq hpos F k]; exact h4 k⟩

/-- **Influence below 1 gives a spectral gap, with no spectral hypothesis.** Finite system, positive weights, the
classical Dobrushin column condition `Σ_x dob μ x z ≤ α < 1`, any function `F`: the spectral measure of the random-scan
heat bath for `F` exists (a finite sum of point masses on `[0, 1]`) and has no mass above `1 - (1 - α)/n`: the spectral
gap is at least `(1 - α)/n` per single-site step. -/
theorem spectral_gap_dobrushin [IsProbabilityMeasure μ] [Nonempty ι] (hpos : ∀ σ : ι → S, 0 < pw μ σ) {α : ℝ}
    (hα0 : 0 < α) (hcol : ∀ z, ∑ x, dob μ x z ≤ α) (F : (ι → S) → ℝ) :
    ∃ ρ : Measure ℝ, IsFiniteMeasure ρ ∧ (∀ᵐ l ∂ρ, 0 ≤ l) ∧ (∀ᵐ l ∂ρ, l ≤ 1) ∧
      (∀ k : ℕ, acorr ρ k = (heatBath hpos).timeCorr F k) ∧
      ρ (Set.Ioi (1 - (1 - α) / Fintype.card ι)) = 0 := by
  obtain ⟨ρ, h1, h2, h3, h4⟩ := timeCorr_spectral hpos F
  have := h1
  refine ⟨ρ, h1, h2, h3, h4, ?_⟩
  have hFM : ∀ σ, |F σ| ≤ ∑ τ, |F τ| := fun σ =>
    Finset.single_le_sum (f := fun τ => |F τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)
  exact (heatBath hpos).spectral_gap_of_column hα0 hcol (Measurable.of_discrete) hFM ρ h2 h3 h4

end Sampler

end ProofPhase.Mixing
