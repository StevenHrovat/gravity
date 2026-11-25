/-
The one-scale reduction, abstract layer (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/PROOF-NOTE.md`, §4.1 (Theorem A, Steps 1 to 4).
-/

import OneScale.Comparison

/-!
# Theorem A: decay of covariances from a block Dobrushin condition (H variant)

* `BlockSpec.cov_le_weighted`: the core estimate with an abstract weight `w`:
  `|Cov(f, g)| ≤ L_g / (c₋(1 - γE)) · ∑_j (∑_{a ∈ B_j ∩ A} δ_a(f)) (∑_{y ∈ B_j} w(y))`.
  Proof as in the note: iterate the averaged operator `P` (Step 1, `oscBound_avg`), telescope the covariance with the
  block covariance identity (Step 3, Lemma 2.6), keep the remainder `‖f‖ θ^t ∑ w` and let `t → ∞` (Step 2).
* `BlockSpec.theoremA_H`: **Theorem A (H)** with a distance on the index set:
  `|Cov(f, g)| ≤ b/(c₋(1 - ρ_λ)) · c₊ ∑_{a ∈ A} δ_a(f) · L_g · e^{-λ(R - D₀)}`, where `ρ_λ = γ e^{λ D₁} < 1`,
  `R ≤ dist(A, S_g)`, `D₀` bounds block diameters, `D₁` the distance from a block to the outside indices that influence
  it, `b` the block size, `c₋ ≤ c ≤ c₊` the coverage, and `L_g` the single-coordinate oscillation of `g`.
  No constant depends on the number of indices or blocks.

Standard background: Dobrushin's uniqueness theorem and covariance estimate (Dobrushin 1970), Foellmer's comparison
(Foellmer 1982), the block version of Dobrushin–Shlosman (1985). The proof here (telescoping over all blocks, no frozen
set) and its formalisation are ours; see the proof note, correction C1.
-/

open MeasureTheory Finset Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace OneScale

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S]

/-- `sup_σ |h(σ) - μ(h)| ≤ ∑_x δ_x(h)` (Lemma 2.3, last claim). -/
theorem abs_sub_integral_le {μ : Measure (ι → S)} [IsProbabilityMeasure μ] {h : (ι → S) → ℝ} (hh : BM h)
    {v : ι → ℝ} (hv : OscBound h v) (σ : ι → S) : |h σ - ∫ τ, h τ ∂μ| ≤ ∑ x, v x := by
  rw [show h σ = ∫ _τ, h σ ∂μ by simp, ← integral_sub (integrable_const _) (hh.integrable μ)]
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun τ => h σ - h τ) (C := ∑ x, v x)
    (Eventually.of_forall fun τ => by
      rw [Real.norm_eq_abs]
      exact hv.abs_sub_le univ (fun i hi => absurd (mem_univ i) hi))
  simpa [Real.norm_eq_abs] using this

namespace BlockSpec

variable {J : Type*} [Fintype J] {μ : Measure (ι → S)} (P : BlockSpec μ J)

/-- `P^t g`. -/
def iter (g : (ι → S) → ℝ) (t : ℕ) : (ι → S) → ℝ := (P.avg)^[t] g

theorem iter_zero (g : (ι → S) → ℝ) : P.iter g 0 = g := rfl

theorem iter_succ (g : (ι → S) → ℝ) (t : ℕ) : P.iter g (t + 1) = P.avg (P.iter g t) :=
  Function.iterate_succ_apply' _ _ _

theorem bm_iter {g : (ι → S) → ℝ} (hg : BM g) (t : ℕ) : BM (P.iter g t) := by
  induction t with
  | zero => exact hg
  | succ t ih => rw [iter_succ]; exact P.bm_avg' ih

/-- One telescoping step: `μ(f (h - P h)) = M⁻¹ ∑_j μ((f - P_j f)(h - P_j h))`. -/
theorem integral_mul_sub_avg' [IsFiniteMeasure μ] [Nonempty J] {f h : (ι → S) → ℝ} (hf : BM f) (hh : BM h) :
    ∫ σ, f σ * (h σ - P.avg h σ) ∂μ =
      (Fintype.card J : ℝ)⁻¹ * ∑ j, ∫ σ, (f σ - blockAvg (P.block j) (P.spec j) f σ) *
        (h σ - blockAvg (P.block j) (P.spec j) h σ) ∂μ := by
  have hM : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have e : ∀ σ, f σ * (h σ - P.avg h σ) =
      (Fintype.card J : ℝ)⁻¹ * ∑ j, f σ * (h σ - blockAvg (P.block j) (P.spec j) h σ) := by
    intro σ
    unfold avg
    rw [← mul_sum, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
    field_simp
  simp_rw [e]
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => (hf.mul (hh.sub (P.bm_avg j hh))).integrable μ)]
  congr 1
  exact sum_congr rfl fun j _ => P.integral_mul_sub_avg j hf hh

/-- The telescoped covariance: `μ(f g) = ∑_{s < t} μ(f (P^s g - P^{s+1} g)) + μ(f P^t g)`. -/
theorem integral_mul_telescope [IsFiniteMeasure μ] {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) (t : ℕ) :
    ∫ σ, f σ * g σ ∂μ = ∑ s ∈ range t, ∫ σ, f σ * (P.iter g s σ - P.iter g (s + 1) σ) ∂μ +
      ∫ σ, f σ * P.iter g t σ ∂μ := by
  induction t with
  | zero => simp [iter_zero]
  | succ t ih =>
    rw [ih, sum_range_succ, add_assoc]
    congr 1
    have h1 := (hf.mul (P.bm_iter hg t)).integrable μ
    have h2 := (hf.mul (P.bm_iter hg (t + 1))).integrable μ
    rw [← integral_add ((hf.mul ((P.bm_iter hg t).sub (P.bm_iter hg (t + 1)))).integrable μ) h2]
    refine integral_congr_ae (Eventually.of_forall fun σ => ?_)
    simp only; ring

theorem integral_iter [IsFiniteMeasure μ] [Nonempty J] {g : (ι → S) → ℝ} (hg : BM g) (t : ℕ) :
    ∫ σ, P.iter g t σ ∂μ = ∫ σ, g σ ∂μ := by
  induction t with
  | zero => rfl
  | succ t ih => rw [iter_succ, P.integral_avg (P.bm_iter hg t), ih]

/-- **Theorem A, Steps 2 to 4, from oscillation bounds of the iterates.** If `δ_x(P^t g) ≤ θ^t L w(x)` for all `t`
with `0 ≤ θ < 1` and `D = (1 - θ) M`, then
`|μ(f g) - μ(f) μ(g)| ≤ L / D · ∑_j (∑_{a ∈ B_j ∩ A} δ_a(f)) (∑_{y ∈ B_j} w(y))`. -/
theorem cov_le_of_iter_osc [IsProbabilityMeasure μ] [Nonempty J] {θ D : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hD0 : 0 < D) (hθD : D = (1 - θ) * (Fintype.card J : ℝ)) {w : ι → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A : Finset ι} (hfA : DepOn f A) {vf : ι → ℝ}
    (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hosc : ∀ t, OscBound (P.iter g t) (fun x => θ ^ t * Lg * w x)) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * ∫ σ, g σ ∂μ| ≤
      Lg / D * ∑ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y := by
  obtain ⟨σ₀⟩ := nonempty_of_isProbabilityMeasure μ
  set M : ℝ := (Fintype.card J : ℝ)
  have hM0 : 0 < M := by simp only [M]; exact_mod_cast Fintype.card_pos
  -- bounds on `f`
  obtain ⟨Cf, hCf⟩ := hf.bdd
  have hCf0 : 0 ≤ Cf := (abs_nonneg _).trans (hCf σ₀)
  have hvf0 : ∀ a, 0 ≤ vf a := fun a => hvf.nonneg σ₀ a
  set of : J → ℝ := fun j => ∑ a ∈ P.block j ∩ A, vf a
  set W : J → ℝ := fun j => ∑ y ∈ P.block j, w y
  have hof0 : ∀ j, 0 ≤ of j := fun j => sum_nonneg fun a _ => hvf0 a
  have hW0 : ∀ j, 0 ≤ W j := fun j => sum_nonneg fun y _ => hw0 y
  set X : ℝ := Lg * ∑ j, of j * W j
  have hX0 : 0 ≤ X := mul_nonneg hLg (sum_nonneg fun j _ => mul_nonneg (hof0 j) (hW0 j))
  -- Step 3: one telescoping term
  have hterm : ∀ s, |∫ σ, f σ * (P.iter g s σ - P.iter g (s + 1) σ) ∂μ| ≤ M⁻¹ * (θ ^ s * X) := by
    intro s
    have hs := P.bm_iter hg s
    rw [iter_succ, P.integral_mul_sub_avg' hf hs, abs_mul, abs_of_pos (inv_pos.2 hM0)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hM0.le)
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hX : θ ^ s * X = ∑ j, of j * (θ ^ s * Lg * W j) := by
      simp only [X, mul_sum]
      exact sum_congr rfl fun j _ => by ring
    rw [hX]
    refine sum_le_sum fun j _ => ?_
    have hpt : ∀ σ, ‖(f σ - blockAvg (P.block j) (P.spec j) f σ) *
        (P.iter g s σ - blockAvg (P.block j) (P.spec j) (P.iter g s) σ)‖ ≤ of j * (θ ^ s * Lg * W j) := by
      intro σ
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul (abs_sub_blockAvg_le_inter hf hvf hfA σ) ?_ (abs_nonneg _) (hof0 j)
      have := abs_sub_blockAvg_le (B := P.block j) (q := P.spec j) hs (hosc s) σ
      simpa [W, mul_sum, mul_assoc] using this
    have := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hpt)
    simpa [Real.norm_eq_abs] using this
  -- the geometric sum
  have hgeom : ∀ t, ∑ s ∈ range t, θ ^ s ≤ M / D := by
    intro t
    rw [le_div_iff₀ hD0]
    have h1 := mul_neg_geom_sum θ t
    rw [hθD, ← mul_assoc, mul_comm (∑ s ∈ range t, θ ^ s) (1 - θ), h1]
    nlinarith [pow_nonneg hθ0 t]
  -- Step 2: the remainder
  set K : ℝ := Cf * (Lg * ∑ x, w x)
  have hrem : ∀ t, |∫ σ, f σ * P.iter g t σ ∂μ - (∫ σ, f σ ∂μ) * ∫ σ, g σ ∂μ| ≤ θ ^ t * K := by
    intro t
    have ht := P.bm_iter hg t
    rw [← P.integral_iter hg t, ← integral_mul_const,
      ← integral_sub ((hf.mul ht).integrable μ) ((hf.mul (BM.const _)).integrable μ)]
    have hpt : ∀ σ, ‖f σ * P.iter g t σ - f σ * ∫ τ, P.iter g t τ ∂μ‖ ≤ θ ^ t * K := by
      intro σ
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
      have h2 := abs_sub_integral_le (μ := μ) ht (hosc t) σ
      have h3 : ∑ x, θ ^ t * Lg * w x = θ ^ t * (Lg * ∑ x, w x) := by
        rw [mul_sum, mul_sum]; exact sum_congr rfl fun x _ => by ring
      rw [h3] at h2
      calc |f σ| * |P.iter g t σ - ∫ τ, P.iter g t τ ∂μ| ≤ Cf * (θ ^ t * (Lg * ∑ x, w x)) :=
            mul_le_mul (hCf σ) h2 (abs_nonneg _) hCf0
        _ = θ ^ t * K := by simp only [K]; ring
    have := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hpt)
    simpa [Real.norm_eq_abs] using this
  -- assembling, for every `t`
  have hall : ∀ t, |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * ∫ σ, g σ ∂μ| ≤ X / D + θ ^ t * K := by
    intro t
    rw [P.integral_mul_telescope hf hg t, add_sub_assoc]
    refine (abs_add_le _ _).trans (add_le_add ?_ (hrem t))
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ s ∈ range t, |∫ σ, f σ * (P.iter g s σ - P.iter g (s + 1) σ) ∂μ|
        ≤ ∑ s ∈ range t, M⁻¹ * (θ ^ s * X) := sum_le_sum fun s _ => hterm s
      _ = M⁻¹ * (X * ∑ s ∈ range t, θ ^ s) := by
          rw [mul_sum, mul_sum]; exact sum_congr rfl fun s _ => by ring
      _ ≤ M⁻¹ * (X * (M / D)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hgeom t) hX0) (inv_nonneg.2 hM0.le)
      _ = X / D := by field_simp
  have hlim : Tendsto (fun t : ℕ => X / D + θ ^ t * K) atTop (𝓝 (X / D + 0 * K)) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const K)
  rw [zero_mul, add_zero] at hlim
  have := ge_of_tendsto' hlim hall
  calc _ ≤ X / D := this
    _ = Lg / D * ∑ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y := by
        simp only [X, of, W]; ring


/-- **Theorem A, core estimate with an abstract weight.** Under GDS with constant `γ`, coverage at least `c₋ ≥ 1`, a
weight `w ≥ 0` that grows at most by the factor `E` across influential block boundaries, `γ E < 1`, and
`δ_x(g) ≤ L_g w(x)`:
`|μ(f g) - μ(f) μ(g)| ≤ L_g / (c₋(1 - γ E)) · ∑_j (∑_{a ∈ B_j ∩ A} δ_a(f)) (∑_{y ∈ B_j} w(y))`. -/
theorem cov_le_weighted [IsProbabilityMeasure μ] [Nonempty ι] (k : J → ι → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBound (P.block j) (P.spec j) z (k j z))
    {γ : ℝ} (hγ : 0 ≤ γ) (hgds : GDS P.block k γ) {cmin : ℕ} (hc1 : 1 ≤ cmin)
    (hcov : ∀ x, cmin ≤ coverage P.block x)
    {w : ι → ℝ} (hw0 : ∀ x, 0 ≤ w x) {E : ℝ} (hE : 0 ≤ E)
    (hwk : ∀ j x y, x ∉ P.block j → y ∈ P.block j → k j x ≠ 0 → w y ≤ E * w x) (hρ : γ * E < 1)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A : Finset ι} (hfA : DepOn f A) {vf : ι → ℝ}
    (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : OscBound g (fun x => Lg * w x)) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * ∫ σ, g σ ∂μ| ≤
      Lg / (cmin * (1 - γ * E)) * ∑ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y := by
  obtain ⟨σ₀⟩ := nonempty_of_isProbabilityMeasure μ
  obtain ⟨x₀⟩ := (inferInstance : Nonempty ι)
  set M : ℝ := (Fintype.card J : ℝ)
  have hMc : cmin ≤ Fintype.card J := (hcov x₀).trans (P.coverage_le_card x₀)
  have hJ : Nonempty J := Fintype.card_pos_iff.1 (by omega)
  have hM0 : 0 < M := by simp only [M]; exact_mod_cast (by omega : 0 < Fintype.card J)
  have hcm : (1 : ℝ) ≤ cmin := by exact_mod_cast hc1
  have hcM : (cmin : ℝ) ≤ M := by simp only [M]; exact_mod_cast hMc
  have hγE0 : 0 ≤ γ * E := mul_nonneg hγ hE
  have hgap : 0 < 1 - γ * E := by linarith
  set θ : ℝ := 1 - cmin * (1 - γ * E) / M with hθ
  have hθ1 : θ < 1 := by
    have : 0 < cmin * (1 - γ * E) / M := div_pos (mul_pos (by linarith) hgap) hM0
    linarith
  have hθ0 : 0 ≤ θ := by
    have : cmin * (1 - γ * E) / M ≤ 1 := by
      rw [div_le_one hM0]
      nlinarith
    linarith
  -- Step 1: oscillation bounds for the iterates
  have hosc : ∀ t, OscBound (P.iter g t) (fun x => θ ^ t * Lg * w x) := by
    intro t
    induction t with
    | zero => simpa [iter_zero] using hvg
    | succ t ih =>
      rw [iter_succ]
      have h := P.oscBound_avg k hk hgds hcov hc1 hw0 hE hwk hρ.le (Nn := θ ^ t * Lg)
        (mul_nonneg (pow_nonneg hθ0 t) hLg) (P.bm_iter hg t) (by simpa [mul_assoc] using ih)
      refine h.mono fun x => le_of_eq ?_
      rw [pow_succ]; ring
  have hD0 : 0 < (cmin : ℝ) * (1 - γ * E) := mul_pos (by linarith) hgap
  exact P.cov_le_of_iter_osc hθ0 hθ1 hD0 (by simp only [θ, M]; field_simp; ring) hw0 hf hg hfA hvf hLg hosc

end BlockSpec

/-! ## The exponential weight `w(x) = e^{-λ dist(x, S_g)}` -/

/-- `w(x) = max_{s ∈ T} e^{-λ dist(x, s)}` (`0` if `T` is empty). -/
def expWeight (dist : ι → ι → ℝ) (lam : ℝ) (T : Finset ι) (x : ι) : ℝ :=
  NNReal.toReal (T.sup fun s => Real.toNNReal (Real.exp (-(lam * dist x s))))

theorem expWeight_nonneg (dist : ι → ι → ℝ) (lam : ℝ) (T : Finset ι) (x : ι) : 0 ≤ expWeight dist lam T x :=
  NNReal.coe_nonneg _

theorem le_expWeight (dist : ι → ι → ℝ) (lam : ℝ) {T : Finset ι} {s : ι} (hs : s ∈ T) (x : ι) :
    Real.exp (-(lam * dist x s)) ≤ expWeight dist lam T x := by
  have := Finset.le_sup (f := fun s => Real.toNNReal (Real.exp (-(lam * dist x s)))) hs
  calc Real.exp (-(lam * dist x s)) = ((Real.toNNReal (Real.exp (-(lam * dist x s))) : NNReal) : ℝ) :=
        (Real.coe_toNNReal _ (Real.exp_pos _).le).symm
    _ ≤ _ := by unfold expWeight; exact NNReal.coe_le_coe.2 this

theorem expWeight_le (dist : ι → ι → ℝ) (lam : ℝ) (T : Finset ι) (x : ι) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ s ∈ T, Real.exp (-(lam * dist x s)) ≤ C) : expWeight dist lam T x ≤ C := by
  have : (T.sup fun s => Real.toNNReal (Real.exp (-(lam * dist x s)))) ≤ C.toNNReal :=
    Finset.sup_le fun s hs => Real.toNNReal_le_toNNReal (h s hs)
  calc expWeight dist lam T x ≤ ((C.toNNReal : NNReal) : ℝ) := by unfold expWeight; exact NNReal.coe_le_coe.2 this
    _ = C := Real.coe_toNNReal _ hC

theorem one_le_expWeight (dist : ι → ι → ℝ) (hd0 : ∀ x, dist x x = 0) (lam : ℝ) {T : Finset ι} {x : ι}
    (hx : x ∈ T) : 1 ≤ expWeight dist lam T x := by
  have := le_expWeight dist lam hx x
  rwa [hd0, mul_zero, neg_zero, Real.exp_zero] at this

/-- `w(y) ≤ e^{λ dist(x, y)} w(x)` (triangle inequality). -/
theorem expWeight_le_mul (dist : ι → ι → ℝ) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z) {lam : ℝ}
    (hlam : 0 ≤ lam) (T : Finset ι) (x y : ι) :
    expWeight dist lam T y ≤ Real.exp (lam * dist x y) * expWeight dist lam T x := by
  refine expWeight_le dist lam T y (mul_nonneg (Real.exp_pos _).le (expWeight_nonneg _ _ _ _)) fun s hs => ?_
  calc Real.exp (-(lam * dist y s)) ≤ Real.exp (lam * dist x y) * Real.exp (-(lam * dist x s)) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have := mul_le_mul_of_nonneg_left (htri x y s) hlam
        linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_expWeight dist lam hs x) (Real.exp_pos _).le

/-- If `dist(a, y) ≤ D₀` and `R ≤ dist(a, s)` for all `s ∈ T`, then `w(y) ≤ e^{-λ(R - D₀)}`. -/
theorem expWeight_le_of_dist (dist : ι → ι → ℝ) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z) {lam : ℝ}
    (hlam : 0 ≤ lam) {T : Finset ι} {a y : ι} {R D₀ : ℝ} (hR : ∀ s ∈ T, R ≤ dist a s) (hay : dist a y ≤ D₀) :
    expWeight dist lam T y ≤ Real.exp (-(lam * (R - D₀))) := by
  refine expWeight_le dist lam T y (Real.exp_pos _).le fun s hs => Real.exp_le_exp.2 ?_
  have h1 := htri a y s
  have h2 := hR s hs
  have : R - D₀ ≤ dist y s := by linarith
  have := mul_le_mul_of_nonneg_left this hlam
  linarith

namespace BlockSpec

variable {J : Type*} [Fintype J] {μ : Measure (ι → S)} (P : BlockSpec μ J)

/-- `∑_j ∑_{a ∈ B_j ∩ A} v a = ∑_{a ∈ A} c(a) v a`. -/
theorem sum_sum_inter (A : Finset ι) (v : ι → ℝ) :
    ∑ j, ∑ a ∈ P.block j ∩ A, v a = ∑ a ∈ A, (coverage P.block a : ℝ) * v a := by
  have e : ∀ j, ∑ a ∈ P.block j ∩ A, v a = ∑ a ∈ A, if a ∈ P.block j then v a else 0 := by
    intro j
    rw [inter_comm, ← filter_mem_eq_inter, sum_filter]
  simp_rw [e]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  rfl

/-- **Theorem A (H variant)** (`PROOF-NOTE.md` §4.1). Let `μ` be a probability measure on a finite product with a block
specification `P` (blocks `B_j`, DLR), influence bounds `k_j(z)`, and GDS with `0 ≤ γ`, coverage
`1 ≤ c₋ ≤ c(x) ≤ c₊`, block sizes `≤ b`. Let `dist` satisfy `dist x x = 0` and the triangle inequality, with block
diameters `≤ D₀` and `dist(x, y) ≤ D₁` whenever `k_j(x) ≠ 0`, `y ∈ B_j`. Let `λ ≥ 0` with `ρ_λ = γ e^{λ D₁} < 1`.
If `f` depends only on `A` with `δ_a(f) ≤ v_a`, and `g` depends only on `S_g` with `δ_x(g) ≤ L_g`, and
`R ≤ dist(a, s)` for `a ∈ A`, `s ∈ S_g`, then
`|μ(f g) - μ(f) μ(g)| ≤ b/(c₋(1 - ρ_λ)) · (c₊ ∑_{a ∈ A} v_a) · L_g · e^{-λ(R - D₀)}`.
No constant depends on the number of indices or blocks. -/
theorem theoremA_H [IsProbabilityMeasure μ] [Nonempty ι] (k : J → ι → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBound (P.block j) (P.spec j) z (k j z))
    {γ : ℝ} (hγ : 0 ≤ γ) (hgds : GDS P.block k γ) {cmin cmax b : ℕ} (hc1 : 1 ≤ cmin)
    (hcov : ∀ x, cmin ≤ coverage P.block x) (hcmax : ∀ x, coverage P.block x ≤ cmax)
    (hb : ∀ j, (P.block j).card ≤ b)
    (dist : ι → ι → ℝ) (hd0 : ∀ x, dist x x = 0) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    {D₀ D₁ : ℝ} (hD₀ : ∀ j, ∀ x ∈ P.block j, ∀ y ∈ P.block j, dist x y ≤ D₀)
    (hD₁ : ∀ j x y, x ∉ P.block j → y ∈ P.block j → k j x ≠ 0 → dist x y ≤ D₁)
    {lam : ℝ} (hlam : 0 ≤ lam) (hρ : γ * Real.exp (lam * D₁) < 1)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A Sg : Finset ι} (hfA : DepOn f A) (hgS : DepOn g Sg)
    {vf : ι → ℝ} (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : OscBound g (fun _ => Lg))
    {R : ℝ} (hR : ∀ a ∈ A, ∀ s ∈ Sg, R ≤ dist a s) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * ∫ σ, g σ ∂μ| ≤
      b / (cmin * (1 - γ * Real.exp (lam * D₁))) * (cmax * ∑ a ∈ A, vf a) * Lg *
        Real.exp (-(lam * (R - D₀))) := by
  obtain ⟨σ₀⟩ := nonempty_of_isProbabilityMeasure μ
  set w := expWeight dist lam Sg
  set E := Real.exp (lam * D₁)
  set e := Real.exp (-(lam * (R - D₀)))
  have hw0 : ∀ x, 0 ≤ w x := expWeight_nonneg dist lam Sg
  have hwk : ∀ j x y, x ∉ P.block j → y ∈ P.block j → k j x ≠ 0 → w y ≤ E * w x := by
    intro j x y hx hy hkx
    refine (expWeight_le_mul dist htri hlam Sg x y).trans (mul_le_mul_of_nonneg_right ?_ (hw0 x))
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hD₁ j x y hx hy hkx) hlam)
  have hvg' : OscBound g (fun x => Lg * w x) := by
    intro σ x s
    by_cases hx : x ∈ Sg
    · calc |g σ - g (Function.update σ x s)| ≤ Lg := hvg σ x s
        _ = Lg * 1 := (mul_one _).symm
        _ ≤ Lg * w x := mul_le_mul_of_nonneg_left (one_le_expWeight dist hd0 lam hx) hLg
    · rw [hgS.update_eq hx σ s, sub_self, abs_zero]
      exact mul_nonneg hLg (hw0 x)
  have hcore := P.cov_le_weighted k hk hγ hgds hc1 hcov hw0 (Real.exp_pos _).le hwk hρ hf hg hfA hvf hLg hvg'
  refine hcore.trans ?_
  have hvf0 : ∀ a, 0 ≤ vf a := fun a => hvf.nonneg σ₀ a
  have hgap : 0 < 1 - γ * E := by linarith
  have hpre : 0 ≤ Lg / (cmin * (1 - γ * E)) :=
    div_nonneg hLg (mul_nonneg (Nat.cast_nonneg _) hgap.le)
  -- each block: `(∑_{B ∩ A} v) · W_j ≤ (∑_{B ∩ A} v) · b e`
  have hblock : ∀ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y ≤
      (∑ a ∈ P.block j ∩ A, vf a) * (b * e) := by
    intro j
    by_cases hj : (P.block j ∩ A).Nonempty
    · obtain ⟨a, ha⟩ := hj
      refine mul_le_mul_of_nonneg_left ?_ (sum_nonneg fun a _ => hvf0 a)
      have hwy : ∀ y ∈ P.block j, w y ≤ e := fun y hy =>
        expWeight_le_of_dist dist htri hlam (hR a (mem_inter.1 ha).2)
          (hD₀ j a (mem_inter.1 ha).1 y hy)
      calc ∑ y ∈ P.block j, w y ≤ ∑ _y ∈ P.block j, e := sum_le_sum hwy
        _ = (P.block j).card * e := by rw [sum_const, nsmul_eq_mul]
        _ ≤ b * e := mul_le_mul_of_nonneg_right (by exact_mod_cast hb j) (Real.exp_pos _).le
    · rw [not_nonempty_iff_eq_empty.1 hj, sum_empty, zero_mul, zero_mul]
  have hsum : ∑ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y ≤
      (cmax * ∑ a ∈ A, vf a) * (b * e) := by
    refine (sum_le_sum fun j _ => hblock j).trans ?_
    rw [← sum_mul, P.sum_sum_inter A vf]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
    rw [mul_sum]
    exact sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (by exact_mod_cast hcmax a) (hvf0 a)
  calc Lg / (cmin * (1 - γ * E)) * ∑ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y
      ≤ Lg / (cmin * (1 - γ * E)) * ((cmax * ∑ a ∈ A, vf a) * (b * e)) := mul_le_mul_of_nonneg_left hsum hpre
    _ = b / (cmin * (1 - γ * E)) * (cmax * ∑ a ∈ A, vf a) * Lg * e := by ring

end BlockSpec

end OneScale
