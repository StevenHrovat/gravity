/-
Positive-definite exponential kernels and reflection positivity (positivity project, 2026-11-21). Released under
Apache 2.0.

# The kernel `exp (β ∑ⱼ gⱼ(a) gⱼ(b))` is positive definite

For bounded measurable `gⱼ` (finitely many) and `β ≥ 0`, and every bounded measurable `H`,

  `∫∫ H(a) H(b) exp (β ∑ⱼ gⱼ(a) gⱼ(b)) dν(a) dν(b) ≥ 0`.

Proof: for each power `m`, `∫∫ H(a) H(b) (∑ⱼ gⱼ(a) gⱼ(b))^m ≥ 0` by induction on `m` (the step distributes one factor
`∑ⱼ gⱼ(a) gⱼ(b)` and applies the induction hypothesis to `H gⱼ`); the partial sums of the exponential series are
nonnegative combinations of these, and they converge to the exponential with a uniform bound (dominated convergence).

This is the analytic core of reflection positivity for the reflection through a plane between time slices (link
reflection): after splitting the crossing links, the crossing plaquettes carry `exp (β ⟨P, Θ P⟩)` with the real Frobenius
inner product `⟨·, ·⟩`. We also give the version over a fixed factor `C` (`pd_exp_fiber`) and on product measures over a
finite index set with a reflection (`config_rp_kernel`).
-/

import Positivity.Product

open MeasureTheory Filter Topology Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace Positivity

theorem IsBdd.sum {α ι : Type*} (s : Finset ι) {f : ι → α → ℝ} (hf : ∀ i, IsBdd (f i)) :
    IsBdd (fun x => ∑ i ∈ s, f i x) := by
  choose M hM using hf
  exact ⟨∑ i ∈ s, M i, fun x => (norm_sum_le _ _).trans (sum_le_sum fun i _ => hM i x)⟩

section Kernel

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] {J : Type*} [Fintype J]

/-- **Powers of a finite-rank kernel are positive definite.** -/
theorem pd_pow {g : J → X → ℝ} (mg : ∀ j, Measurable (g j)) (bg : ∀ j, IsBdd (g j)) (m : ℕ) :
    ∀ H : X → ℝ, Measurable H → IsBdd H →
      0 ≤ ∫ z, H z.1 * H z.2 * (∑ j, g j z.1 * g j z.2) ^ m ∂(ν.prod ν) := by
  have ms : Measurable (fun z : X × X => ∑ j, g j z.1 * g j z.2) :=
    Finset.measurable_sum _ (fun j _ => ((mg j).comp measurable_fst).mul ((mg j).comp measurable_snd))
  have bs : IsBdd (fun z : X × X => ∑ j, g j z.1 * g j z.2) :=
    IsBdd.sum _ (fun j => ((bg j).comp Prod.fst).mul ((bg j).comp Prod.snd))
  induction m with
  | zero =>
    intro H _ _
    simp only [pow_zero, mul_one]
    rw [integral_prod_mul (fun a => H a) (fun b => H b)]
    exact mul_self_nonneg _
  | succ m ih =>
    intro H mH bH
    have hexp : ∀ z : X × X, H z.1 * H z.2 * (∑ j, g j z.1 * g j z.2) ^ (m + 1) =
        ∑ j, (H z.1 * g j z.1) * (H z.2 * g j z.2) * (∑ j, g j z.1 * g j z.2) ^ m := by
      intro z
      rw [pow_succ, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [hexp]
    rw [integral_finsetSum _ (fun j _ => IsBdd.integrable
      ((((bH.comp Prod.fst).mul ((bg j).comp Prod.fst)).mul ((bH.comp Prod.snd).mul ((bg j).comp Prod.snd))).mul
        (by obtain ⟨K, hK⟩ := bs; exact ⟨K ^ m, fun z => by
          rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hK z) m⟩))
      ((((mH.comp measurable_fst).mul ((mg j).comp measurable_fst)).mul
        ((mH.comp measurable_snd).mul ((mg j).comp measurable_snd))).mul (ms.pow_const m)).aestronglyMeasurable)]
    exact Finset.sum_nonneg fun j _ => ih (fun z => H z * g j z) (mH.mul (mg j)) (bH.mul (bg j))

/-- **The exponential kernel `exp (β ∑ⱼ gⱼ(a) gⱼ(b))`, `β ≥ 0`, is positive definite.** -/
theorem pd_exp {g : J → X → ℝ} (mg : ∀ j, Measurable (g j)) (bg : ∀ j, IsBdd (g j)) {β : ℝ} (hβ : 0 ≤ β)
    {H : X → ℝ} (mH : Measurable H) (bH : IsBdd H) :
    0 ≤ ∫ z, H z.1 * H z.2 * Real.exp (β * ∑ j, g j z.1 * g j z.2) ∂(ν.prod ν) := by
  set s : X × X → ℝ := fun z => ∑ j, g j z.1 * g j z.2 with hs
  have ms : Measurable s :=
    Finset.measurable_sum _ (fun j _ => ((mg j).comp measurable_fst).mul ((mg j).comp measurable_snd))
  obtain ⟨Ms, hMs⟩ : IsBdd s := IsBdd.sum _ (fun j => ((bg j).comp Prod.fst).mul ((bg j).comp Prod.snd))
  obtain ⟨MH, hMH⟩ := bH
  have mHH : Measurable (fun z : X × X => H z.1 * H z.2) := (mH.comp measurable_fst).mul (mH.comp measurable_snd)
  let T : ℕ → X × X → ℝ := fun M z => H z.1 * H z.2 * ∑ m ∈ range M, (β * s z) ^ m / (m.factorial : ℝ)
  have hTeq : ∀ M z, T M z = ∑ m ∈ range M, (β ^ m / (m.factorial : ℝ)) * (H z.1 * H z.2 * s z ^ m) := by
    intro M z
    simp only [T, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [mul_pow]; ring
  have hT : ∀ M, 0 ≤ ∫ z, T M z ∂(ν.prod ν) := by
    intro M
    simp_rw [hTeq]
    have hint : ∀ m, Integrable (fun z : X × X => H z.1 * H z.2 * s z ^ m) (ν.prod ν) := fun m =>
      IsBdd.integrable ⟨MH * MH * Ms ^ m, fun z => by
        rw [norm_mul, norm_mul, norm_pow]
        exact mul_le_mul (mul_le_mul (hMH z.1) (hMH z.2) (norm_nonneg _) ((norm_nonneg _).trans (hMH z.1)))
          (pow_le_pow_left₀ (norm_nonneg _) (hMs z) m) (by positivity)
          (mul_nonneg ((norm_nonneg _).trans (hMH z.1)) ((norm_nonneg _).trans (hMH z.1)))⟩
        (mHH.mul (ms.pow_const m)).aestronglyMeasurable
    rw [integral_finsetSum _ (fun m _ => (hint m).const_mul _)]
    refine Finset.sum_nonneg fun m _ => ?_
    rw [integral_const_mul]
    exact mul_nonneg (div_nonneg (pow_nonneg hβ m) (Nat.cast_nonneg _)) (pd_pow ν mg bg m H mH ⟨MH, hMH⟩)
  have hMH0 : ∀ x, 0 ≤ MH := fun x => (norm_nonneg _).trans (hMH x)
  have hlim : Tendsto (fun M => ∫ z, T M z ∂(ν.prod ν)) atTop
      (𝓝 (∫ z, H z.1 * H z.2 * Real.exp (β * s z) ∂(ν.prod ν))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => MH * MH * Real.exp (|β| * Ms))
      (fun M => ?_) (integrable_const _) (fun M => ae_of_all _ fun z => ?_) (ae_of_all _ fun z => ?_)
    · exact (mHH.mul (Finset.measurable_sum _ fun m _ =>
        ((ms.const_mul β).pow_const m).div_const _)).aestronglyMeasurable
    · simp only [T]
      rw [norm_mul, norm_mul]
      have h1 : ‖∑ m ∈ range M, (β * s z) ^ m / (m.factorial : ℝ)‖ ≤ Real.exp (|β| * Ms) := by
        calc ‖∑ m ∈ range M, (β * s z) ^ m / (m.factorial : ℝ)‖
            ≤ ∑ m ∈ range M, ‖(β * s z) ^ m / (m.factorial : ℝ)‖ := norm_sum_le _ _
          _ = ∑ m ∈ range M, |β * s z| ^ m / (m.factorial : ℝ) := by
              refine Finset.sum_congr rfl fun m _ => ?_
              rw [Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
          _ ≤ Real.exp |β * s z| := Real.sum_le_exp_of_nonneg (abs_nonneg _) M
          _ ≤ Real.exp (|β| * Ms) := by
              refine Real.exp_le_exp.mpr ?_
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hMs z) (abs_nonneg _)
      exact mul_le_mul (mul_le_mul (hMH _) (hMH _) (norm_nonneg _) (hMH0 z.1)) h1 (norm_nonneg _)
        (mul_nonneg (hMH0 z.1) (hMH0 z.1))
    · have h := (NormedSpace.expSeries_div_hasSum_exp (β * s z)).tendsto_sum_nat
      rw [← Real.exp_eq_exp_ℝ] at h
      exact h.const_mul (H z.1 * H z.2)
  exact ge_of_tendsto' hlim hT

/-- **Positive-definite kernel over a fixed factor.** On `C × (X × X)` with `ν_C ⊗ ν ⊗ ν`, for bounded measurable
    `h, gⱼ : X × C → ℝ`, `v ≥ 0` and `β ≥ 0`:
    `∫ h(a, c) h(b, c) v(c) exp (β ∑ⱼ gⱼ(a, c) gⱼ(b, c)) ≥ 0`. -/
theorem pd_exp_fiber {C : Type*} [MeasurableSpace C] (νC : Measure C) [IsFiniteMeasure νC] {h : X × C → ℝ}
    {v : C → ℝ} {g : J → X × C → ℝ} (mh : Measurable h) (mv : Measurable v) (mg : ∀ j, Measurable (g j))
    (bh : IsBdd h) (bv : IsBdd v) (bg : ∀ j, IsBdd (g j)) (hv : ∀ c, 0 ≤ v c) {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ ∫ z, h (z.2.1, z.1) * h (z.2.2, z.1) * v z.1 *
      Real.exp (β * ∑ j, g j (z.2.1, z.1) * g j (z.2.2, z.1)) ∂(νC.prod (ν.prod ν)) := by
  have m1 : Measurable (fun z : C × (X × X) => (z.2.1, z.1)) := measurable_snd.fst.prodMk measurable_fst
  have m2 : Measurable (fun z : C × (X × X) => (z.2.2, z.1)) := measurable_snd.snd.prodMk measurable_fst
  obtain ⟨Ms, hMs⟩ : IsBdd (fun z : C × (X × X) => ∑ j, g j (z.2.1, z.1) * g j (z.2.2, z.1)) :=
    IsBdd.sum _ (fun j => ((bg j).comp _).mul ((bg j).comp _))
  have hint : Integrable (fun z : C × (X × X) => h (z.2.1, z.1) * h (z.2.2, z.1) * v z.1 *
      Real.exp (β * ∑ j, g j (z.2.1, z.1) * g j (z.2.2, z.1))) (νC.prod (ν.prod ν)) := by
    refine IsBdd.integrable ((((bh.comp _).mul (bh.comp _)).mul (bv.comp _)).mul
      ⟨Real.exp (|β| * Ms), fun z => ?_⟩) ?_
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.mpr ((le_abs_self _).trans ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hMs z) (abs_nonneg _)
    · exact ((((mh.comp m1).mul (mh.comp m2)).mul (mv.comp measurable_fst)).mul
        (Real.measurable_exp.comp ((Finset.measurable_sum _ fun j _ =>
          ((mg j).comp m1).mul ((mg j).comp m2)).const_mul β))).aestronglyMeasurable
  rw [integral_prod _ hint]
  refine integral_nonneg fun c => ?_
  have hc : Measurable (fun a : X => (a, c)) := measurable_id.prodMk measurable_const
  have heq : (fun ab : X × X => h (ab.1, c) * h (ab.2, c) * v c *
      Real.exp (β * ∑ j, g j (ab.1, c) * g j (ab.2, c))) =
      fun ab => v c * ((fun a => h (a, c)) ab.1 * (fun a => h (a, c)) ab.2 *
        Real.exp (β * ∑ j, (fun j a => g j (a, c)) j ab.1 * (fun j a => g j (a, c)) j ab.2)) := by
    funext ab; ring
  simp only []
  rw [heq, integral_const_mul]
  exact mul_nonneg (hv c) (pd_exp ν (g := fun j a => g j (a, c)) (fun j => (mg j).comp hc)
    (fun j => (bg j).comp _) hβ (mh.comp hc) (bh.comp _))

end Kernel

section Config

variable {ι C X G : Type*} [Fintype ι] [Fintype C] [Fintype X] [MeasurableSpace G] [Nonempty G]
  (ν : Measure G) [IsProbabilityMeasure ν] {e : C ⊕ (X ⊕ X) ≃ ι} {σ : X → G → G} {Θ : (ι → G) → (ι → G)}
  {J : Type*} [Fintype J]

/-- **Reflection positivity with a positive-definite exponential kernel on `ι → G`.** For bounded measurable `F` and `gⱼ`
    depending only on fixed and positive coordinates, `B ≥ 0` depending only on fixed coordinates, and `β ≥ 0`:
    `∫ F · (F ∘ Θ) · B · exp (β ∑ⱼ gⱼ · (gⱼ ∘ Θ)) ≥ 0`. -/
theorem config_rp_kernel (hσ : ∀ x, MeasurePreserving (σ x) ν ν) (hΘ : IsReflection e σ Θ)
    {F B : (ι → G) → ℝ} (hF : DepPos e F) (hB : DepFix e B) (mF : Measurable F) (mB : Measurable B)
    (bF : IsBdd F) (bB : IsBdd B) (hB0 : ∀ U, 0 ≤ B U) {g : J → (ι → G) → ℝ} (hg : ∀ j, DepPos e (g j))
    (mg : ∀ j, Measurable (g j)) (bg : ∀ j, IsBdd (g j)) {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ ∫ U, F U * F (Θ U) * B U * Real.exp (β * ∑ j, g j U * g j (Θ U)) ∂(Measure.pi fun _ : ι => ν) := by
  have hsplit := measurePreserving_split ν e σ hσ
  let K : (C → G) × ((X → G) × (X → G)) → ℝ := fun z =>
    posPart e F (z.2.1, z.1) * posPart e F (z.2.2, z.1) * fixPart e B z.1 *
      Real.exp (β * ∑ j, posPart e (g j) (z.2.1, z.1) * posPart e (g j) (z.2.2, z.1))
  have m1 : Measurable (fun z : (C → G) × ((X → G) × (X → G)) => (z.2.1, z.1)) :=
    measurable_snd.fst.prodMk measurable_fst
  have m2 : Measurable (fun z : (C → G) × ((X → G) × (X → G)) => (z.2.2, z.1)) :=
    measurable_snd.snd.prodMk measurable_fst
  have hK : Measurable K :=
    ((((measurable_posPart mF).comp m1).mul ((measurable_posPart mF).comp m2)).mul
      ((measurable_fixPart mB).comp measurable_fst)).mul
      (Real.measurable_exp.comp ((Finset.measurable_sum _ fun j _ =>
        ((measurable_posPart (mg j)).comp m1).mul ((measurable_posPart (mg j)).comp m2)).const_mul β))
  have hpt : ∀ U, F U * F (Θ U) * B U * Real.exp (β * ∑ j, g j U * g j (Θ U)) = K (split e σ U) := by
    intro U
    have hFU : F U = posPart e F ((split e σ U).2.1, (split e σ U).1) := hF.eq_posPart U
    have hFΘ := hF.eq_posPart_theta σ Θ hΘ.fix hΘ.pos U
    have hBU := hB.eq_fixPart σ U
    have hgU : ∀ j, g j U = posPart e (g j) ((split e σ U).2.1, (split e σ U).1) := fun j => (hg j).eq_posPart U
    have hgΘ : ∀ j, g j (Θ U) = posPart e (g j) ((split e σ U).2.2, (split e σ U).1) :=
      fun j => (hg j).eq_posPart_theta σ Θ hΘ.fix hΘ.pos U
    simp only [K]
    rw [hFΘ, hFU, hBU]
    congr 3
    exact Finset.sum_congr rfl fun j _ => by rw [hgΘ j, hgU j]
  rw [show (fun U => F U * F (Θ U) * B U * Real.exp (β * ∑ j, g j U * g j (Θ U))) =
    fun U => K (split e σ U) from funext hpt]
  rw [integral_comp_of_measurePreserving hsplit hK.aestronglyMeasurable]
  exact pd_exp_fiber _ _ (measurable_posPart mF) (measurable_fixPart mB)
    (fun j => measurable_posPart (mg j)) (bF.comp _) (bB.comp _) (fun j => (bg j).comp _) (fun c => hB0 _) hβ

end Config

end Positivity
