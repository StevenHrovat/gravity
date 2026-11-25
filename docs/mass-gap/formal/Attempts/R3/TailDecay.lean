/-
Round 3, attempt 1 (torus robustness): Theorem A with a weighted block Dobrushin condition (2026-11-21).
Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/r3-robust/NOTE.md`, section 4 (quasi-local effective actions).
-/

import OneScale.Decay

/-!
# Theorem A for infinite-range influences (a weighted GDS)

`OneScale.BlockSpec.theoremA_H` needs **finite range**: an influence coefficient `k_j(x)` may be nonzero only for `x`
within `D₁` of the block `B_j`, and the condition is `γ e^{λ D₁} < 1`. Blocked effective actions are not exactly finite
range (polymer tails), so here the range condition and GDS are merged into one **weighted** condition, the block form of
the weighted Dobrushin condition (Dobrushin 1970; Gross 1979, Dobrushin–Pechersky 1983 for exponential weights):

  `GDSw P.block k e γ`:  `∑_{j : x ∉ B_j} k_j(x) e_j(x) ≤ γ c(x)` for every `x`,

where `e_j(x) ≥ 0` bounds how much the weight `w` can grow from `x` into the block `B_j`. With the exponential weight
`w = e^{-λ dist(·, S_g)}` one takes `e_j(x) = e^{λ E_j(x)}`, `E_j(x) ≥ dist(x, y)` for `y ∈ B_j`.

* `oscBound_avg_w`: Step 1 (contraction) under `GDSw`, `γ ≤ 1`.
* `cov_le_weighted_w`: the core covariance estimate under `GDSw`, `γ < 1`.
* **`theoremA_w`**: `|Cov(f, g)| ≤ b/(c₋(1 - γ)) · (c₊ ∑_{a ∈ A} δ_a(f)) · L_g · e^{-λ(R - D₀)}` under
  `∑_{j : x ∉ B_j} k_j(x) e^{λ E_j(x)} ≤ γ c(x)`, `γ < 1`. No finite-range assumption; nothing depends on the number of
  indices or blocks.

The finite-range Theorem A is the special case `e_j(x) = e^{λ D₁}` on the coefficients that do not vanish. The proofs
follow `OneScale.BlockSpec.oscBound_avg`, `cov_le_weighted` and `theoremA_H` line by line; only the bookkeeping of the
weight changes. Standard (weighted Dobrushin uniqueness); formalised here.
-/

open MeasureTheory Finset Filter Topology OneScale

set_option linter.unusedSectionVars false

noncomputable section

namespace Attempts.R3

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] {J : Type*} [Fintype J]

/-- **Weighted GDS.** `∑_{j : x ∉ B_j} k_j(x) e_j(x) ≤ γ c(x)` for every `x`. -/
def GDSw (block : J → Finset ι) (k e : J → ι → ℝ) (γ : ℝ) : Prop :=
  ∀ x, ∑ j ∈ univ.filter (fun j => x ∉ block j), k j x * e j x ≤ γ * coverage block x

variable {μ : Measure (ι → S)} (P : BlockSpec μ J)

/-- **Step 1 under the weighted condition.** If `δ_x(h) ≤ N w(x)`, `w(y) ≤ e_j(x) w(x)` for `x ∉ B_j ∋ y`, and
`GDSw` holds with `γ ≤ 1`, then `δ_x(P h) ≤ (1 - c₋(1 - γ)/M) N w(x)`. -/
theorem oscBound_avg_w (k : J → ι → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBound (P.block j) (P.spec j) z (k j z))
    (e : J → ι → ℝ) {γ : ℝ} (hgds : GDSw P.block k e γ) {cmin : ℕ} (hcov : ∀ x, cmin ≤ coverage P.block x)
    (hc1 : 1 ≤ cmin) {w : ι → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    (hwk : ∀ j x y, x ∉ P.block j → y ∈ P.block j → w y ≤ e j x * w x) (hγ1 : γ ≤ 1)
    {Nn : ℝ} (hN : 0 ≤ Nn) {h : (ι → S) → ℝ} (hh : BM h) (hv : OscBound h (fun x => Nn * w x)) :
    OscBound (P.avg h) (fun x => (1 - cmin * (1 - γ) / Fintype.card J) * (Nn * w x)) := by
  intro σ x s
  set σ' := Function.update σ x s
  set M : ℝ := (Fintype.card J : ℝ)
  have hM : (1 : ℝ) ≤ M := by
    have := (hc1.trans (hcov x)).trans (P.coverage_le_card x)
    simp only [M]
    exact_mod_cast this
  have hM0 : 0 < M := by linarith
  set t : J → ℝ := fun j =>
    |blockAvg (P.block j) (P.spec j) h σ - blockAvg (P.block j) (P.spec j) h σ'|
  have ht_in : ∀ j, x ∈ P.block j → t j = 0 := by
    intro j hj
    simp only [t, σ', blockAvg_update_mem (P.spec_congr j) h hj σ s, sub_self, abs_zero]
  have ht_out : ∀ j, x ∉ P.block j → t j ≤ Nn * w x + k j x * (Nn * (e j x * w x)) := by
    intro j hj
    have hm : ∀ y ∈ P.block j, Nn * w y ≤ Nn * (e j x * w x) := fun y hy =>
      mul_le_mul_of_nonneg_left (hwk j x y hj hy) hN
    exact osc_blockAvg_of_not_mem hj (hk j x hj) hh hv hm σ s
  have hNw : 0 ≤ Nn * w x := mul_nonneg hN (hw0 x)
  have hsum : ∑ j, t j ≤ (M - coverage P.block x) * (Nn * w x) + Nn * w x * (γ * coverage P.block x) := by
    rw [← sum_filter_add_sum_filter_not univ (fun j => x ∈ P.block j)]
    rw [sum_eq_zero (fun j hj => ht_in j (mem_filter.1 hj).2), zero_add]
    calc ∑ j ∈ univ.filter (fun j => x ∉ P.block j), t j
        ≤ ∑ j ∈ univ.filter (fun j => x ∉ P.block j), (Nn * w x + k j x * (Nn * (e j x * w x))) :=
          sum_le_sum fun j hj => ht_out j (mem_filter.1 hj).2
      _ = (M - coverage P.block x) * (Nn * w x) +
          Nn * w x * ∑ j ∈ univ.filter (fun j => x ∉ P.block j), k j x * e j x := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul, P.card_not_mem x, mul_sum]
          congr 1
          refine sum_congr rfl fun j _ => ?_
          ring
      _ ≤ _ := by
          gcongr
          exact hgds x
  have hdiff : P.avg h σ - P.avg h σ' =
      M⁻¹ * ∑ j, (blockAvg (P.block j) (P.spec j) h σ - blockAvg (P.block j) (P.spec j) h σ') := by
    unfold BlockSpec.avg; rw [sum_sub_distrib]; ring
  have hcx : (cmin : ℝ) ≤ coverage P.block x := by exact_mod_cast hcov x
  rw [hdiff, abs_mul, abs_of_pos (inv_pos.2 hM0)]
  calc M⁻¹ * |∑ j, (blockAvg (P.block j) (P.spec j) h σ - blockAvg (P.block j) (P.spec j) h σ')|
      ≤ M⁻¹ * ∑ j, t j := mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (inv_nonneg.2 hM0.le)
    _ ≤ M⁻¹ * ((M - coverage P.block x) * (Nn * w x) + Nn * w x * (γ * coverage P.block x)) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hM0.le)
    _ = M⁻¹ * ((M - coverage P.block x * (1 - γ)) * (Nn * w x)) := by ring
    _ ≤ M⁻¹ * ((M - cmin * (1 - γ)) * (Nn * w x)) := by
        gcongr
    _ = (1 - cmin * (1 - γ) / M) * (Nn * w x) := by
        field_simp

/-- **The core estimate under the weighted condition.** As `OneScale.BlockSpec.cov_le_weighted`, with `GDSw` and
`γ < 1` in place of GDS and `γ E < 1`. -/
theorem cov_le_weighted_w [IsProbabilityMeasure μ] [Nonempty ι] (k : J → ι → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBound (P.block j) (P.spec j) z (k j z))
    (e : J → ι → ℝ) {γ : ℝ} (hγ : 0 ≤ γ) (hgds : GDSw P.block k e γ) {cmin : ℕ} (hc1 : 1 ≤ cmin)
    (hcov : ∀ x, cmin ≤ coverage P.block x) {w : ι → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    (hwk : ∀ j x y, x ∉ P.block j → y ∈ P.block j → w y ≤ e j x * w x) (hρ : γ < 1)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A : Finset ι} (hfA : DepOn f A) {vf : ι → ℝ}
    (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : OscBound g (fun x => Lg * w x)) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * ∫ σ, g σ ∂μ| ≤
      Lg / (cmin * (1 - γ)) * ∑ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty ι)
  set M : ℝ := (Fintype.card J : ℝ)
  have hMc : cmin ≤ Fintype.card J := (hcov x₀).trans (P.coverage_le_card x₀)
  have hJ : Nonempty J := Fintype.card_pos_iff.1 (by omega)
  have hM0 : 0 < M := by simp only [M]; exact_mod_cast (by omega : 0 < Fintype.card J)
  have hcm : (1 : ℝ) ≤ cmin := by exact_mod_cast hc1
  have hcM : (cmin : ℝ) ≤ M := by simp only [M]; exact_mod_cast hMc
  have hgap : 0 < 1 - γ := by linarith
  set θ : ℝ := 1 - cmin * (1 - γ) / M with hθ
  have hθ1 : θ < 1 := by
    have : 0 < cmin * (1 - γ) / M := div_pos (mul_pos (by linarith) hgap) hM0
    linarith
  have hθ0 : 0 ≤ θ := by
    have : cmin * (1 - γ) / M ≤ 1 := by
      rw [div_le_one hM0]
      nlinarith
    linarith
  have hosc : ∀ t, OscBound (P.iter g t) (fun x => θ ^ t * Lg * w x) := by
    intro t
    induction t with
    | zero => simpa [BlockSpec.iter_zero] using hvg
    | succ t ih =>
      rw [BlockSpec.iter_succ]
      have h := oscBound_avg_w P k hk e hgds hcov hc1 hw0 hwk hρ.le (Nn := θ ^ t * Lg)
        (mul_nonneg (pow_nonneg hθ0 t) hLg) (P.bm_iter hg t) (by simpa [mul_assoc] using ih)
      refine h.mono fun x => le_of_eq ?_
      rw [pow_succ]; ring
  have hD0 : 0 < (cmin : ℝ) * (1 - γ) := mul_pos (by linarith) hgap
  exact P.cov_le_of_iter_osc hθ0 hθ1 hD0 (by simp only [θ, M]; field_simp; ring) hw0 hf hg hfA hvf hLg hosc

/-- **Theorem A with a weighted Dobrushin condition (no finite range).** Let `E_j(x)` bound `dist(x, y)` for
`x ∉ B_j ∋ y`, `λ ≥ 0`, and `∑_{j : x ∉ B_j} k_j(x) e^{λ E_j(x)} ≤ γ c(x)` with `0 ≤ γ < 1`. Then, with block sizes
`≤ b`, coverage `1 ≤ c₋ ≤ c ≤ c₊`, block diameters `≤ D₀`, `f` depending on `A` (`δ_a(f) ≤ v_a`), `g` depending on `S_g`
(`δ_x(g) ≤ L_g`) and `R ≤ dist(a, s)` on `A × S_g`:
`|μ(f g) - μ(f) μ(g)| ≤ b/(c₋(1 - γ)) · (c₊ ∑_{a ∈ A} v_a) · L_g · e^{-λ(R - D₀)}`. -/
theorem theoremA_w [IsProbabilityMeasure μ] [Nonempty ι] (k : J → ι → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBound (P.block j) (P.spec j) z (k j z))
    {cmin cmax b : ℕ} (hc1 : 1 ≤ cmin)
    (hcov : ∀ x, cmin ≤ coverage P.block x) (hcmax : ∀ x, coverage P.block x ≤ cmax)
    (hb : ∀ j, (P.block j).card ≤ b)
    (dist : ι → ι → ℝ) (hd0 : ∀ x, dist x x = 0) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    {D₀ : ℝ} (hD₀ : ∀ j, ∀ x ∈ P.block j, ∀ y ∈ P.block j, dist x y ≤ D₀)
    (E : J → ι → ℝ) (hE : ∀ j x y, x ∉ P.block j → y ∈ P.block j → dist x y ≤ E j x)
    {lam : ℝ} (hlam : 0 ≤ lam) {γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hgds : GDSw P.block k (fun j x => Real.exp (lam * E j x)) γ)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A Sg : Finset ι} (hfA : DepOn f A) (hgS : DepOn g Sg)
    {vf : ι → ℝ} (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : OscBound g (fun _ => Lg))
    {R : ℝ} (hR : ∀ a ∈ A, ∀ s ∈ Sg, R ≤ dist a s) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * ∫ σ, g σ ∂μ| ≤
      b / (cmin * (1 - γ)) * (cmax * ∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * (R - D₀))) := by
  obtain ⟨σ₀⟩ := nonempty_of_isProbabilityMeasure μ
  set w := expWeight dist lam Sg
  set e := Real.exp (-(lam * (R - D₀)))
  have hw0 : ∀ x, 0 ≤ w x := expWeight_nonneg dist lam Sg
  have hwk : ∀ j x y, x ∉ P.block j → y ∈ P.block j → w y ≤ Real.exp (lam * E j x) * w x := by
    intro j x y hx hy
    refine (expWeight_le_mul dist htri hlam Sg x y).trans (mul_le_mul_of_nonneg_right ?_ (hw0 x))
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hE j x y hx hy) hlam)
  have hvg' : OscBound g (fun x => Lg * w x) := by
    intro σ x s
    by_cases hx : x ∈ Sg
    · calc |g σ - g (Function.update σ x s)| ≤ Lg := hvg σ x s
        _ = Lg * 1 := (mul_one _).symm
        _ ≤ Lg * w x := mul_le_mul_of_nonneg_left (one_le_expWeight dist hd0 lam hx) hLg
    · rw [hgS.update_eq hx σ s, sub_self, abs_zero]
      exact mul_nonneg hLg (hw0 x)
  have hcore := cov_le_weighted_w P k hk (fun j x => Real.exp (lam * E j x)) hγ hgds hc1 hcov hw0 hwk hγ1
    hf hg hfA hvf hLg hvg'
  refine hcore.trans ?_
  have hvf0 : ∀ a, 0 ≤ vf a := fun a => hvf.nonneg σ₀ a
  have hgap : 0 < 1 - γ := by linarith
  have hpre : 0 ≤ Lg / (cmin * (1 - γ)) :=
    div_nonneg hLg (mul_nonneg (Nat.cast_nonneg _) hgap.le)
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
  calc Lg / (cmin * (1 - γ)) * ∑ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y
      ≤ Lg / (cmin * (1 - γ)) * ((cmax * ∑ a ∈ A, vf a) * (b * e)) := mul_le_mul_of_nonneg_left hsum hpre
    _ = b / (cmin * (1 - γ)) * (cmax * ∑ a ∈ A, vf a) * Lg * e := by ring

end Attempts.R3
