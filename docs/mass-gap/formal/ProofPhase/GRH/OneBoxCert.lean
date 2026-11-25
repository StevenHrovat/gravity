/-
GRH one-box certificate: the abstract step from a certified finite part and a tail bound to positivity
(2026-11-23). Released under Apache 2.0.

Note: `docs/unified/GRH-ONEBOX-CERT.md`; numbers from `docs/unified/grh_onebox_cert.py`.
-/

import ProofPhase.Unified.Transport
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positivity from a certified finite part plus a tail bound

The computer-assisted certificate (`docs/unified/GRH-ONEBOX-CERT.md`) shows that Weil's form `W` for zeta is
positive on `L²(-a, a)` for one support `a`.  It splits `f = u + g` with `u` in a finite-dimensional space `S` (the
polynomials of degree `< N`) and `g ⊥ S`, and needs three inputs:

* **finite part** (`hfin`): `c ‖u‖² + ρ(u)² / (μ - c) ≤ W u u` on `S`; this is what the Cholesky factorisation in ball
  arithmetic certifies (`fin_of_ldl` turns a factorisation `L D Lᵀ` with `D ≥ 0` into exactly this inequality);
* **cross term** (`hcross`): `|W u g| ≤ ρ(u) ‖g‖`, with `ρ(u) = ‖Q_N H u‖` (the residual of `u` off `S`);
* **tail** (`htail`): `μ ‖g‖² ≤ W g g` on `S⊥`.

`schur_scalar` is the scalar core (one AM-GM step), `onebox_positive` the statement on an inner product space,
`onebox_sign` the strict sign in the form of the transport theorem's part (c) (`sign_transport`): the uncoupled value
`W u u + W g g` is the margin, the cross term `2 W u g` the uncertainty.  `OneBoxEnclosures` names the numerical
enclosures; `onebox_cert_13_20`, `onebox_cert_3_5`, `onebox_cert_69_100` are the three certified runs with their
exact values.

What Lean does **not** do here: it does not define Weil's form or compute any of the enclosures.  The Gram matrix, the
residual bound and the tail constant `μ` are computed in interval arithmetic by the script and enter as hypotheses.
-/

namespace ProofPhase.GRH

open Finset Matrix

/-! ### 1. The scalar core -/

/-- **Schur step, scalars.** With the finite-part bound `c nu² + r²/(μ - c) ≤ Wu`, the tail bound `μ ng² ≤ Wg` and the
cross bound `|B| ≤ r ng`, the coupled value `Wu + 2B + Wg` is at least `c (nu² + ng²)`. -/
theorem schur_scalar {Wu Wg B nu ng r μ c : ℝ} (hμc : c < μ) (hfin : c * nu ^ 2 + r ^ 2 / (μ - c) ≤ Wu)
    (htail : μ * ng ^ 2 ≤ Wg) (hcross : |B| ≤ r * ng) : c * (nu ^ 2 + ng ^ 2) ≤ Wu + 2 * B + Wg := by
  have hpos : 0 < μ - c := sub_pos.2 hμc
  have hamgm : 2 * r * ng ≤ r ^ 2 / (μ - c) + (μ - c) * ng ^ 2 := by
    rw [div_add' _ _ _ hpos.ne', le_div_iff₀ hpos]
    nlinarith [sq_nonneg (r - (μ - c) * ng)]
  have hB := (abs_le.1 hcross).1
  nlinarith

/-- **The strict sign as transport part (c).** Margin `m = c (nu² + ng²) + 2 r ng ≤ Wu + Wg`, uncertainty
`e = 2 r ng ≥ |2B|`; when `c (nu² + ng²) > 0` the uncertainty is below the margin and `sign_transport` gives
`0 < Wu + 2B + Wg`. -/
theorem schur_sign {Wu Wg B nu ng r μ c : ℝ} (hμc : c < μ) (hfin : c * nu ^ 2 + r ^ 2 / (μ - c) ≤ Wu)
    (htail : μ * ng ^ 2 ≤ Wg) (hcross : |B| ≤ r * ng) (hmargin : 0 < c * (nu ^ 2 + ng ^ 2)) :
    0 < Wu + 2 * B + Wg := by
  have hpos : 0 < μ - c := sub_pos.2 hμc
  have hamgm : 2 * r * ng ≤ r ^ 2 / (μ - c) + (μ - c) * ng ^ 2 := by
    rw [div_add' _ _ _ hpos.ne', le_div_iff₀ hpos]
    nlinarith [sq_nonneg (r - (μ - c) * ng)]
  have hm : ∀ _ : ℕ, c * (nu ^ 2 + ng ^ 2) + 2 * r * ng ≤ Wu + Wg := fun _ => by nlinarith
  have he : ∀ _ : ℕ, |(Wu + 2 * B + Wg) - (Wu + Wg)| ≤ 2 * r * ng := fun _ => by
    rw [show (Wu + 2 * B + Wg) - (Wu + Wg) = 2 * B by ring, abs_mul, abs_two]
    linarith
  have hlt : ∀ _ : ℕ, 2 * r * ng < c * (nu ^ 2 + ng ^ 2) + 2 * r * ng := fun _ => by linarith
  have := ProofPhase.Unified.sign_transport (M := fun _ => Wu + Wg) (N := fun _ => Wu + 2 * B + Wg)
    (m := fun _ => c * (nu ^ 2 + ng ^ 2) + 2 * r * ng) (e := fun _ => 2 * r * ng) hm he hlt 0
  linarith [this.1, this.2]

/-! ### 2. On an inner product space -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **One-box positivity, abstract form.** `W` is a symmetric bilinear form on an inner product space `E` (in the
application: the form domain of Weil's form inside `L²(-a, a)`), `S` a subspace with an orthogonal projection (the
polynomials of degree `< N`).  The three certified inputs give `W f f ≥ c ‖f‖²` for every `f`. -/
theorem onebox_positive (S : Submodule ℝ E) [S.HasOrthogonalProjection] (W : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, W x y = W y x) {c μ : ℝ} (hμc : c < μ) (ρ : E → ℝ)
    (hfin : ∀ u ∈ S, c * ‖u‖ ^ 2 + ρ u ^ 2 / (μ - c) ≤ W u u)
    (hcross : ∀ u ∈ S, ∀ g ∈ Sᗮ, |W u g| ≤ ρ u * ‖g‖)
    (htail : ∀ g ∈ Sᗮ, μ * ‖g‖ ^ 2 ≤ W g g) (f : E) : c * ‖f‖ ^ 2 ≤ W f f := by
  obtain ⟨u, hu, g, hg, rfl⟩ := S.exists_add_mem_mem_orthogonal f
  have horth : (inner ℝ u g : ℝ) = 0 := Submodule.inner_right_of_mem_orthogonal hu hg
  have hnorm : ‖u + g‖ ^ 2 = ‖u‖ ^ 2 + ‖g‖ ^ 2 := by
    rw [sq, sq, sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u g horth]
  have hexp : W (u + g) (u + g) = W u u + 2 * W u g + W g g := by
    simp only [map_add, LinearMap.add_apply]
    rw [hsymm g u]
    ring
  rw [hnorm, hexp]
  exact schur_scalar hμc (hfin u hu) (htail g hg) (hcross u hu g hg)

/-- **Strict sign.** Under the same inputs with `c > 0`, `W f f > 0` for every `f ≠ 0`. -/
theorem onebox_sign (S : Submodule ℝ E) [S.HasOrthogonalProjection] (W : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, W x y = W y x) {c μ : ℝ} (hc : 0 < c) (hμc : c < μ) (ρ : E → ℝ)
    (hfin : ∀ u ∈ S, c * ‖u‖ ^ 2 + ρ u ^ 2 / (μ - c) ≤ W u u)
    (hcross : ∀ u ∈ S, ∀ g ∈ Sᗮ, |W u g| ≤ ρ u * ‖g‖)
    (htail : ∀ g ∈ Sᗮ, μ * ‖g‖ ^ 2 ≤ W g g) {f : E} (hf : f ≠ 0) : 0 < W f f := by
  have h := onebox_positive S W hsymm hμc ρ hfin hcross htail f
  have : 0 < ‖f‖ ^ 2 := by positivity
  nlinarith

/-! ### 3. The finite part from a factorisation -/

/-- **LDLᵀ gives a nonnegative form.** If `A = L D Lᵀ` with `D` diagonal and nonnegative, then `xᵀ A x ≥ 0`. -/
theorem ldl_nonneg {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ ((L * diagonal d * Lᵀ) *ᵥ x) := by
  have h0 : (0 : Fin n → ℝ) ≤ d := fun i => hd i
  have hP := (Matrix.PosSemidef.diagonal h0).mul_mul_conjTranspose_same L
  rw [conjTranspose_eq_transpose_of_trivial] at hP
  simpa using hP.dotProduct_mulVec_nonneg x

/-- **Finite part from the certificate.** `b` is an orthonormal basis of `S` (Legendre polynomials), `G` the Gram
matrix of `W` in it, `R` a matrix with `ρ(∑ xᵢ bᵢ)² ≤ xᵀ R x` (the residual Gram), and the certified matrix
`G - c I - R/(μ - c)` factors as `L D Lᵀ` with `D ≥ 0` (ball-arithmetic Cholesky).  Then the finite-part input
`hfin` of `onebox_positive` holds on the span of `b`. -/
theorem fin_of_ldl {n : ℕ} (b : Fin n → E) (hb : Orthonormal ℝ b) (W : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (G R L : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) {c μ : ℝ} (hμc : c < μ)
    (hG : ∀ i j, G i j = W (b i) (b j)) (ρ : E → ℝ)
    (hρ : ∀ x : Fin n → ℝ, ρ (∑ i, x i • b i) ^ 2 ≤ x ⬝ᵥ (R *ᵥ x))
    (hfac : G - c • (1 : Matrix (Fin n) (Fin n) ℝ) - (μ - c)⁻¹ • R = L * diagonal d * Lᵀ)
    (x : Fin n → ℝ) :
    c * ‖∑ i, x i • b i‖ ^ 2 + ρ (∑ i, x i • b i) ^ 2 / (μ - c) ≤ W (∑ i, x i • b i) (∑ i, x i • b i) := by
  have hpos : 0 < μ - c := sub_pos.2 hμc
  have hW : W (∑ i, x i • b i) (∑ i, x i • b i) = x ⬝ᵥ (G *ᵥ x) := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, dotProduct, mulVec,
      hG, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hn : ‖∑ i, x i • b i‖ ^ 2 = x ⬝ᵥ x := by
    rw [← real_inner_self_eq_norm_sq, hb.inner_sum x x Finset.univ]
    simp [dotProduct]
  have h0 := ldl_nonneg L d hd x
  rw [← hfac] at h0
  simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h0
  have hr := hρ x
  rw [hW, hn]
  have : ρ (∑ i, x i • b i) ^ 2 / (μ - c) ≤ (μ - c)⁻¹ * (x ⬝ᵥ (R *ᵥ x)) := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hr (inv_nonneg.2 hpos.le)
  linarith

/-! ### 4. The numbers, as named hypotheses -/

/-- **The enclosures of one certificate run, as named hypotheses.** `S` = polynomials of degree `< 100` on `[-a, a]`;
`c` the certified margin, `μ` the certified lower bound of `W` on `S⊥`.  In the application `E` is the form domain of
Weil's form in `L²(-a, a)` and `W` Weil's form (polarised).  The three inequality fields are what
`docs/unified/grh_onebox_cert.py` certifies: `fin` by the ball-arithmetic Cholesky of the final matrix (`fin_of_ldl`),
`cross` by the coupling block plus the exact Legendre-tail Gram of the singular part of `H u` (`ρ u = ‖Q_N H u‖`), `tail`
by the frequency-side bound. -/
structure OneBoxEnclosures (S : Submodule ℝ E) (W : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (ρ : E → ℝ) (c μ : ℝ) : Prop where
  symm : ∀ x y, W x y = W y x
  fin : ∀ u ∈ S, c * ‖u‖ ^ 2 + ρ u ^ 2 / (μ - c) ≤ W u u
  cross : ∀ u ∈ S, ∀ g ∈ Sᗮ, |W u g| ≤ ρ u * ‖g‖
  tail : ∀ g ∈ Sᗮ, μ * ‖g‖ ^ 2 ≤ W g g

/-- **The certificate at `a = 13/20`** (log `grh_onebox_cert-a0.65.log`): with `c = 3.398 · 10⁻¹¹` and
`μ = 0.6367` (certified `μ ≥ 0.636772…`), `W f f ≥ 3.398 · 10⁻¹¹ ‖f‖²` for every `f`. -/
theorem onebox_cert_13_20 (S : Submodule ℝ E) [S.HasOrthogonalProjection] (W : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (ρ : E → ℝ)
    (h : OneBoxEnclosures S W ρ (3398 / 10 ^ 14) (6367 / 10000)) (f : E) :
    (3398 / 10 ^ 14 : ℝ) * ‖f‖ ^ 2 ≤ W f f :=
  onebox_positive S W h.symm (by norm_num) ρ h.fin h.cross h.tail f

/-- **The certificate at `a = 3/5`** (log `grh_onebox_cert-a0.60.log`): `c = 1.5 · 10⁻⁹`, `μ = 0.7151`
(certified `μ ≥ 0.715195…`). -/
theorem onebox_cert_3_5 (S : Submodule ℝ E) [S.HasOrthogonalProjection] (W : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (ρ : E → ℝ)
    (h : OneBoxEnclosures S W ρ (15 / 10 ^ 10) (7151 / 10000)) (f : E) :
    (15 / 10 ^ 10 : ℝ) * ‖f‖ ^ 2 ≤ W f f :=
  onebox_positive S W h.symm (by norm_num) ρ h.fin h.cross h.tail f

/-- **The certificate at `a = 69/100`** (log `grh_onebox_cert-a0.69.log`): `c = 6.417 · 10⁻¹³`, `μ = 0.5751`
(certified `μ ≥ 0.575148…`). -/
theorem onebox_cert_69_100 (S : Submodule ℝ E) [S.HasOrthogonalProjection] (W : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (ρ : E → ℝ)
    (h : OneBoxEnclosures S W ρ (6417 / 10 ^ 16) (5751 / 10000)) (f : E) :
    (6417 / 10 ^ 16 : ℝ) * ‖f‖ ^ 2 ≤ W f f :=
  onebox_positive S W h.symm (by norm_num) ρ h.fin h.cross h.tail f

end ProofPhase.GRH
