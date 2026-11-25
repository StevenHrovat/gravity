/-
The blowup blueprint, Poincare and SU(N): the symmetric part (2026-11-23).
Released under Apache 2.0.

Note: `docs/unified/BLOWUP.md`, section 7. Nothing new about Poincare or geometrization is claimed or proved here.
-/

import Mathlib

/-!
# SU(2) is the 3-sphere; every SU(N) shrinks homothetically to extinction at time `1/N`

**1. SU(2) is the unit sphere of `ℂ²` (= `ℝ⁴`).**
* `su2Mat`: `(α, β) ↦ !![α, β; -conj β, conj α]`.
* `su2Mat_mem`: for `|α|² + |β|² = 1` the matrix lies in `Matrix.specialUnitaryGroup (Fin 2) ℂ`.
* `su2_form`: every element of SU(2) has this form, with `|α|² + |β|² = 1`.
* `sphereEquivSU2`: the bijection between `{(α, β) : |α|² + |β|² = 1}` (the 3-sphere) and SU(2), as sets. That it is a
  homeomorphism (indeed a diffeomorphism) is classical and not formalised here.

**2. Homothetic Ricci flow of an Einstein metric (the scalar ODE).** For `Ric(g₀) = λ g₀`, the metric `g(t) = φ(t) g₀`
solves `∂g/∂t = −2 Ric(g)` iff `φ' = −2λ` (Ricci is scale invariant). So
* `shrink_hasDerivAt`, `shrink_unique`: `φ(t) = 1 − 2λ t` is the solution with `φ(0) = 1`, and the only one;
* `shrink_pos`, `shrink_extinct`: `φ > 0` before `T = 1/(2λ)` and `φ(T) = 0`: extinction at `T`;
* `einstein_hasDerivAt`: the Einstein constant of `g(t)`, `λ(t) = λ/(1 − 2λ t)`, satisfies `λ' = 2 λ²`. With
  `R = n λ(t)` this is `R' = (2/n) R²`, the equality case of `∂R/∂t ≥ ΔR + (2/n) R²`;
* `einstein_unbounded`: `λ(t) → ∞` as `t → T⁻` (the curvature blows up only at the final point).

**3. The SU(N) constants** (`<X, Y> = −tr(XY)` on `su(N)`; the Einstein constant `N/2` is classical, checked numerically in
`blowup_sun_check.py`): `sun_extinction` (`T = 1/N`).

**4. The conformal instability window** (Cao-He's criterion, external): `sun_window` (for `N ≥ 3`,
`n/(n−1) · λ < N − 1/N < 2λ` with `n = N² − 1`, `λ = N/2`) and `su2_window_edge` (for `N = 2` the lower end is attained:
`3/2 = 3/2`, Obata's equality, the round sphere).

No axioms beyond the standard ones; no unproved steps.
-/

open Matrix Complex Filter Topology

noncomputable section

namespace ProofPhase.Unified

/-! ### 1. SU(2) is the 3-sphere -/

/-- The quaternion matrix of `(α, β)`. -/
def su2Mat (α β : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![α, β; -(starRingEnd ℂ) β, (starRingEnd ℂ) α]

theorem su2Mat_det (α β : ℂ) : (su2Mat α β).det = (normSq α + normSq β : ℝ) := by
  rw [su2Mat, Matrix.det_fin_two_of]
  push_cast
  rw [← mul_conj, ← mul_conj]
  ring

/-- For `|α|² + |β|² = 1`, `su2Mat α β` is special unitary. -/
theorem su2Mat_mem {α β : ℂ} (h : normSq α + normSq β = 1) :
    su2Mat α β ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, by rw [su2Mat_det, h]; simp⟩
  rw [Matrix.mem_unitaryGroup_iff]
  have h' : α * (starRingEnd ℂ) α + β * (starRingEnd ℂ) β = 1 := by
    rw [mul_conj, mul_conj, ← ofReal_add, h, ofReal_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2Mat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;>
    first | linear_combination h' | linear_combination -h' | ring

/-- **Every element of SU(2) is a quaternion matrix**: `U = su2Mat (U 0 0) (U 0 1)`, with `|U 0 0|² + |U 0 1|² = 1`. -/
theorem su2_form {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    U = su2Mat (U 0 0) (U 0 1) ∧ normSq (U 0 0) + normSq (U 0 1) = 1 := by
  rw [Matrix.mem_specialUnitaryGroup_iff] at hU
  obtain ⟨hu, hdet⟩ := hU
  have hsU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hu
  have hadj : U * adjugate U = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
  have hstar : star U = adjugate U := by
    calc star U = star U * (U * adjugate U) := by rw [hadj, Matrix.mul_one]
      _ = adjugate U := by rw [← Matrix.mul_assoc, hsU, Matrix.one_mul]
  have e11 : U 1 1 = (starRingEnd ℂ) (U 0 0) := by
    have := congrFun (congrFun hstar 0) 0
    simp [Matrix.star_apply, Matrix.adjugate_fin_two] at this
    exact this.symm
  have e10 : U 1 0 = -(starRingEnd ℂ) (U 0 1) := by
    have := congrFun (congrFun hstar 1) 0
    simp [Matrix.star_apply, Matrix.adjugate_fin_two] at this
    rw [this, neg_neg]
  have hform : U = su2Mat (U 0 0) (U 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [su2Mat, e11, e10]
  refine ⟨hform, ?_⟩
  have hd := su2Mat_det (U 0 0) (U 0 1)
  rw [← hform, hdet] at hd
  exact_mod_cast hd.symm

/-- The 3-sphere as the unit sphere of `ℂ²`: `|α|² + |β|² = 1` (four real coordinates, sum of squares 1). -/
def Sphere3 : Type := {p : ℂ × ℂ // normSq p.1 + normSq p.2 = 1}

/-- **SU(2) is the 3-sphere** (as sets): the quaternion matrix is a bijection from the unit sphere of `ℂ²` onto SU(2). -/
def sphereEquivSU2 : Sphere3 ≃ Matrix.specialUnitaryGroup (Fin 2) ℂ where
  toFun p := ⟨su2Mat p.1.1 p.1.2, su2Mat_mem p.2⟩
  invFun U := ⟨(U.1 0 0, U.1 0 1), (su2_form U.2).2⟩
  left_inv p := by
    obtain ⟨⟨α, β⟩, _⟩ := p
    rfl
  right_inv U := by
    apply Subtype.ext
    exact (su2_form U.2).1.symm

/-! ### 2. Homothetic Ricci flow of an Einstein metric -/

/-- The homothety factor `φ(t) = 1 − 2λ t`. -/
def shrink (lam t : ℝ) : ℝ := 1 - 2 * lam * t

theorem shrink_hasDerivAt (lam t : ℝ) : HasDerivAt (shrink lam) (-(2 * lam)) t := by
  have h1 : HasDerivAt (fun x : ℝ => 2 * lam * x) (2 * lam) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * lam)
  exact h1.const_sub 1

/-- The factor is the only solution of `φ' = −2λ`, `φ(0) = 1`. -/
theorem shrink_unique {lam : ℝ} {ψ : ℝ → ℝ} (hψ : ∀ t, HasDerivAt ψ (-(2 * lam)) t) (h0 : ψ 0 = 1) :
    ψ = shrink lam := by
  have hd : ∀ t, HasDerivAt (fun t => ψ t - shrink lam t) 0 t := fun t => by
    have := (hψ t).sub (shrink_hasDerivAt lam t)
    rw [sub_self] at this
    exact this
  have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv)
  funext t
  have := hc t 0
  simp only [h0, shrink, mul_zero, sub_zero, sub_self] at this
  show ψ t = 1 - 2 * lam * t
  linarith

theorem shrink_pos {lam t : ℝ} (hlam : 0 < lam) (ht : t < 1 / (2 * lam)) : 0 < shrink lam t := by
  have : 2 * lam * t < 1 := by
    rw [lt_div_iff₀ (by linarith)] at ht; linarith
  simp only [shrink]; linarith

theorem shrink_extinct {lam : ℝ} (hlam : 0 < lam) : shrink lam (1 / (2 * lam)) = 0 := by
  simp only [shrink]; field_simp; ring

/-- The Einstein constant of `φ(t) g₀`: `λ(t) = λ/φ(t)`. -/
def einsteinAt (lam t : ℝ) : ℝ := lam / shrink lam t

/-- **The curvature ODE, equality case**: `λ(t)' = 2 λ(t)²` before extinction. -/
theorem einstein_hasDerivAt {lam t : ℝ} (hlam : 0 < lam) (ht : t < 1 / (2 * lam)) :
    HasDerivAt (einsteinAt lam) (2 * einsteinAt lam t ^ 2) t := by
  have hp := shrink_pos hlam ht
  have hd := (hasDerivAt_const t lam).div (shrink_hasDerivAt lam t) hp.ne'
  convert hd using 1
  · funext x; rfl
  · show 2 * (lam / shrink lam t) ^ 2 = _
    field_simp
    ring

/-- **Curvature blows up only at the final point**: `λ(t) → ∞` as `t → (1/(2λ))⁻`. -/
theorem einstein_unbounded {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (einsteinAt lam) (𝓝[<] (1 / (2 * lam))) atTop := by
  have hφ : Tendsto (shrink lam) (𝓝[<] (1 / (2 * lam))) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : Continuous (shrink lam) := by unfold shrink; fun_prop
      have := (hc.tendsto (1 / (2 * lam))).mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 / (2 * lam))))
      rwa [shrink_extinct hlam] at this
    · filter_upwards [self_mem_nhdsWithin] with t ht using shrink_pos hlam ht
  exact (tendsto_inv_nhdsGT_zero.comp hφ).const_mul_atTop hlam |>.congr fun t => by
    simp [einsteinAt, div_eq_mul_inv]

/-! ### 3. The SU(N) constants -/

/-- **Extinction of SU(N)** in the normalisation `<X, Y> = −tr(XY)`: Einstein constant `N/2` gives `T = 1/N`, and the
factor is `1 − N t`. -/
theorem sun_extinction {N : ℝ} (hN : 0 < N) :
    1 / (2 * (N / 2)) = 1 / N ∧ (∀ t, shrink (N / 2) t = 1 - N * t) ∧ shrink (N / 2) (1 / N) = 0 := by
  refine ⟨by ring_nf, fun t => by simp only [shrink]; ring, ?_⟩
  have := shrink_extinct (lam := N / 2) (by linarith)
  rwa [show 1 / (2 * (N / 2)) = 1 / N by ring_nf] at this

/-! ### 4. The conformal instability window -/

/-- **Every SU(N), `N ≥ 3`, lies strictly inside the window** `n/(n−1) · λ < μ₁ < 2λ` (`n = N² − 1`, `λ = N/2`,
`μ₁ = N − 1/N`, the Casimir of the fundamental representation). -/
theorem sun_window {N : ℝ} (hN : 3 ≤ N) :
    (N ^ 2 - 1) / (N ^ 2 - 2) * (N / 2) < N - 1 / N ∧ N - 1 / N < 2 * (N / 2) := by
  have hN0 : 0 < N := by linarith
  have h2 : 0 < N ^ 2 - 2 := by nlinarith
  constructor
  · have key : (N ^ 2 - 1) / (N ^ 2 - 2) * (N / 2) = N * (N ^ 2 - 1) / (2 * (N ^ 2 - 2)) := by
      field_simp
    have key2 : N - 1 / N = (N ^ 2 - 1) / N := by field_simp
    rw [key, key2, div_lt_div_iff₀ (by linarith) hN0]
    have hA : (0 : ℝ) < N ^ 2 - 1 := by nlinarith
    have hB : (0 : ℝ) < N ^ 2 - 4 := by nlinarith
    nlinarith [mul_pos hA hB]
  · have : 0 < 1 / N := by positivity
    linarith

/-- **SU(2) sits on the lower edge**: `n/(n−1) · λ = μ₁ = 3/2`, Obata's equality case, the round 3-sphere. -/
theorem su2_window_edge : ((2 : ℝ) ^ 2 - 1) / (2 ^ 2 - 2) * (2 / 2) = 2 - 1 / 2 := by norm_num

end ProofPhase.Unified
