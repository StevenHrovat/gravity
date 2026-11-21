/-
Reflection positivity, the abstract lemma (positivity project, 2026-11-21). Released under Apache 2.0.

Reflection positivity of lattice gauge theories is due to Osterwalder and Seiler (Ann. Phys. 110 (1978) 440); see also
Glimm–Jaffe, *Quantum Physics*, ch. 6 and 10. This file is an independent formalisation of the measure-theoretic core.

# The abstract reflection-positivity lemma

A configuration space split as `X × C × X` (positive half, fixed plane, negative half) carries the product measure
`ν ⊗ ν_C ⊗ ν`; the reflection `θ (a, c, b) = (b, c, a)` swaps the two halves. For a weight of the form
`w(a, c) · w(b, c) · v(c)` with `v ≥ 0` and every bounded measurable `F` depending only on `(a, c)`,

  `∫ F(a, c) · F(b, c) · w(a, c) w(b, c) v(c) = ∫ (∫ F(a, c) w(a, c) dν(a))² v(c) dν_C(c) ≥ 0`

(Fubini). The sign of `w` plays no role. We prove the real and the complex version (with conjugation) and, for any family
of functions closed under linear combinations on which a "reflected" form `∫ F · (G ∘ θ) · W` is positive and symmetric,
the Gram-matrix positivity and the Cauchy–Schwarz inequality (`gram_of_rp`, `cs_of_rp`).

## Main results

- `reflection_formula`: the Fubini identity on `C × (X × X)` for two different functions.
- `rp_core`, `rp_core_complex`: positivity on `C × (X × X)`.
- `rp_abstract`, `rp_abstract_complex`: positivity on `X × C × X` with the swap reflection and weight `w w v`.
- `rp_abstract_cs`: `|∫ F · (G ∘ θ) dμ_w|² ≤ (∫ F · (F ∘ θ) dμ_w) (∫ G · (G ∘ θ) dμ_w)` on `X × C × X`.
- `gram_of_rp`, `cs_of_rp`: Gram positivity and Cauchy–Schwarz from positivity, symmetry and integrability.
-/

import Mathlib

open MeasureTheory ComplexConjugate
open scoped ComplexOrder

noncomputable section

namespace Positivity

/-! ## Bounded functions -/

/-- A function with a uniform bound on its norm. -/
def IsBdd {α E : Type*} [Norm E] (f : α → E) : Prop := ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M

namespace IsBdd

variable {α β E : Type*}

theorem comp [Norm E] {f : α → E} (hf : IsBdd f) (g : β → α) : IsBdd (fun x => f (g x)) := by
  obtain ⟨M, hM⟩ := hf; exact ⟨M, fun x => hM (g x)⟩

theorem mul [NonUnitalSeminormedRing E] {f g : α → E} (hf : IsBdd f) (hg : IsBdd g) :
    IsBdd (fun x => f x * g x) := by
  obtain ⟨M, hM⟩ := hf; obtain ⟨K, hK⟩ := hg
  exact ⟨M * K, fun x => (norm_mul_le _ _).trans
    (mul_le_mul (hM x) (hK x) (norm_nonneg _) ((norm_nonneg _).trans (hM x)))⟩

theorem add [SeminormedAddGroup E] {f g : α → E} (hf : IsBdd f) (hg : IsBdd g) : IsBdd (fun x => f x + g x) := by
  obtain ⟨M, hM⟩ := hf; obtain ⟨K, hK⟩ := hg
  exact ⟨M + K, fun x => (norm_add_le _ _).trans (add_le_add (hM x) (hK x))⟩

theorem const_mul (c : ℝ) {f : α → ℝ} (hf : IsBdd f) : IsBdd (fun x => c * f x) := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨‖c‖ * M, fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)⟩

theorem const [Norm E] (c : E) : IsBdd (fun _ : α => c) := ⟨‖c‖, fun _ => le_rfl⟩

theorem integrable [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α} [IsFiniteMeasure μ] {f : α → E}
    (hf : IsBdd f) (hm : AEStronglyMeasurable f μ) : Integrable f μ := by
  obtain ⟨M, hM⟩ := hf
  exact Integrable.of_bound hm M (ae_of_all _ hM)

theorem prod {ι : Type*} (s : Finset ι) {f : ι → α → ℝ} (hf : ∀ i, IsBdd (f i)) :
    IsBdd (fun x => ∏ i ∈ s, f i x) := by
  choose M hM using hf
  refine ⟨∏ i ∈ s, M i, fun x => ?_⟩
  rw [Real.norm_eq_abs, Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => by simpa [Real.norm_eq_abs] using hM i x)

theorem of_abs {f : α → ℝ} (h : ∃ M, ∀ x, |f x| ≤ M) : IsBdd f := by
  obtain ⟨M, hM⟩ := h; exact ⟨M, fun x => by simpa [Real.norm_eq_abs] using hM x⟩

end IsBdd

/-- Transport of an integral along a measure-preserving map. -/
theorem integral_comp_of_measurePreserving {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} {ν : Measure β} {f : α → β}
    (hf : MeasurePreserving f μ ν) {g : β → E} (hg : AEStronglyMeasurable g ν) :
    ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν := by
  rw [← hf.map_eq] at hg ⊢
  exact (integral_map hf.measurable.aemeasurable hg).symm

/-! ## The core identity on `C × (X × X)` -/

section Core

variable {X C : Type*} [MeasurableSpace X] [MeasurableSpace C] (ν : Measure X) (νC : Measure C)
  [IsFiniteMeasure ν] [IsFiniteMeasure νC]

/-- **The reflection formula** (Fubini). For bounded measurable `h₁ h₂ : X × C → 𝕜` and `v : C → 𝕜`,
    `∫ h₁(a, c) h₂(b, c) v(c) d(ν_C ⊗ ν ⊗ ν) = ∫ (∫ h₁(a, c) dν(a)) (∫ h₂(b, c) dν(b)) v(c) dν_C(c)`. -/
theorem reflection_formula {𝕜 : Type*} [RCLike 𝕜] {h₁ h₂ : X × C → 𝕜} {v : C → 𝕜}
    (m₁ : Measurable h₁) (m₂ : Measurable h₂) (mv : Measurable v)
    (b₁ : IsBdd h₁) (b₂ : IsBdd h₂) (bv : IsBdd v) :
    ∫ z, h₁ (z.2.1, z.1) * h₂ (z.2.2, z.1) * v z.1 ∂(νC.prod (ν.prod ν)) =
      ∫ c, (∫ a, h₁ (a, c) ∂ν) * (∫ b, h₂ (b, c) ∂ν) * v c ∂νC := by
  have hint : Integrable (fun z : C × (X × X) => h₁ (z.2.1, z.1) * h₂ (z.2.2, z.1) * v z.1)
      (νC.prod (ν.prod ν)) := by
    refine IsBdd.integrable (((b₁.comp _).mul (b₂.comp _)).mul (bv.comp _)) ?_
    exact (((m₁.comp (measurable_snd.fst.prodMk measurable_fst)).mul
      (m₂.comp (measurable_snd.snd.prodMk measurable_fst))).mul (mv.comp measurable_fst)).aestronglyMeasurable
  rw [integral_prod _ hint]
  refine integral_congr_ae (ae_of_all _ fun c => ?_)
  simp only []
  rw [integral_mul_const]
  congr 1
  exact integral_prod_mul (fun a => h₁ (a, c)) (fun b => h₂ (b, c))

/-- **Reflection positivity on `C × (X × X)`**, real version. -/
theorem rp_core {h : X × C → ℝ} {v : C → ℝ} (hm : Measurable h) (mv : Measurable v) (hb : IsBdd h)
    (bv : IsBdd v) (hv : ∀ c, 0 ≤ v c) :
    0 ≤ ∫ z, h (z.2.1, z.1) * h (z.2.2, z.1) * v z.1 ∂(νC.prod (ν.prod ν)) := by
  rw [reflection_formula ν νC hm hm mv hb hb bv]
  exact integral_nonneg fun c => mul_nonneg (mul_self_nonneg _) (hv c)

/-- **Reflection positivity on `C × (X × X)`**, complex version: `∫ h(a, c) conj(h(b, c)) v(c) ≥ 0` (a nonnegative real
    number). -/
theorem rp_core_complex {h : X × C → ℂ} {v : C → ℝ} (hm : Measurable h) (mv : Measurable v) (hb : IsBdd h)
    (bv : IsBdd v) (hv : ∀ c, 0 ≤ v c) :
    0 ≤ ∫ z, h (z.2.1, z.1) * conj (h (z.2.2, z.1)) * (v z.1 : ℂ) ∂(νC.prod (ν.prod ν)) := by
  have hb' : IsBdd (fun z => conj (h z)) := by
    obtain ⟨M, hM⟩ := hb; exact ⟨M, fun z => by simpa using hM z⟩
  have bv' : IsBdd (fun c => (v c : ℂ)) := by
    obtain ⟨M, hM⟩ := bv; exact ⟨M, fun c => by simpa using hM c⟩
  rw [reflection_formula ν νC (h₂ := fun z => conj (h z)) (v := fun c => (v c : ℂ)) hm
    (Complex.continuous_conj.measurable.comp hm) (Complex.measurable_ofReal.comp mv) hb hb' bv']
  simp_rw [integral_conj]
  have hpt : ∀ c, (∫ a, h (a, c) ∂ν) * conj (∫ a, h (a, c) ∂ν) * (v c : ℂ) =
      ((Complex.normSq (∫ a, h (a, c) ∂ν) * v c : ℝ) : ℂ) := by
    intro c; rw [Complex.mul_conj]; push_cast; ring
  simp_rw [hpt, integral_complex_ofReal]
  exact Complex.zero_le_real.mpr (integral_nonneg fun c => mul_nonneg (Complex.normSq_nonneg _) (hv c))

/-! ## The form `X × C × X` -/

/-- The rearrangement `(a, c, b) ↦ (c, a, b)`. -/
def rearrange (z : X × (C × X)) : C × (X × X) := (z.2.1, (z.1, z.2.2))

theorem measurePreserving_rearrange :
    MeasurePreserving (rearrange (X := X) (C := C)) (ν.prod (νC.prod ν)) (νC.prod (ν.prod ν)) := by
  have h1 := MeasurePreserving.symm _ (measurePreserving_prodAssoc ν νC ν)
  have h2 := (Measure.measurePreserving_swap (μ := ν) (ν := νC)).prod (MeasurePreserving.id ν)
  have h3 := measurePreserving_prodAssoc νC ν ν
  have h := h3.comp (h2.comp h1)
  convert h using 1
  funext z; rfl

/-- The reflection of `X × C × X`: swap the two halves. -/
def swapHalves (z : X × (C × X)) : X × (C × X) := (z.2.2, (z.2.1, z.1))

/-- A function of the positive half and the fixed plane, seen on `X × C × X`. -/
def onPos {E : Type*} (F : X × C → E) (z : X × (C × X)) : E := F (z.1, z.2.1)

/-- The reflection-symmetric weight `w(a, c) w(b, c) v(c)`. -/
def rpWeight {𝕜 : Type*} [Mul 𝕜] (w : X × C → 𝕜) (v : C → 𝕜) (z : X × (C × X)) : 𝕜 :=
  w (z.1, z.2.1) * w (z.2.2, z.2.1) * v z.2.1

/-- The integral `∫ F · (G ∘ θ) · w w v` on `X × C × X` as an integral on `C × (X × X)`. -/
theorem integral_onPos_eq {𝕜 : Type*} [RCLike 𝕜] (F G w : X × C → 𝕜) (v : C → 𝕜)
    (mF : Measurable F) (mG : Measurable G) (mw : Measurable w) (mv : Measurable v) :
    ∫ z, onPos F z * onPos G (swapHalves z) * rpWeight w v z ∂(ν.prod (νC.prod ν)) =
      ∫ y, (fun p : X × C => F p * w p) (y.2.1, y.1) * (fun p : X × C => G p * w p) (y.2.2, y.1) * v y.1
        ∂(νC.prod (ν.prod ν)) := by
  rw [← integral_comp_of_measurePreserving (measurePreserving_rearrange ν νC)]
  · refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [onPos, swapHalves, rpWeight, rearrange]; ring
  · exact ((((mF.mul mw).comp (measurable_snd.fst.prodMk measurable_fst)).mul
      ((mG.mul mw).comp (measurable_snd.snd.prodMk measurable_fst))).mul
      (mv.comp measurable_fst)).aestronglyMeasurable

/-- **Abstract reflection positivity (site reflection), real version.** On `X × C × X` with the product measure
    `ν ⊗ ν_C ⊗ ν`, the swap `θ (a, c, b) = (b, c, a)` and the weight `w(a, c) w(b, c) v(c)` (`v ≥ 0`), every bounded
    measurable `F` of `(a, c)` satisfies `∫ F · (F ∘ θ) · w w v ≥ 0`. -/
theorem rp_abstract {F w : X × C → ℝ} {v : C → ℝ} (mF : Measurable F) (mw : Measurable w) (mv : Measurable v)
    (bF : IsBdd F) (bw : IsBdd w) (bv : IsBdd v) (hv : ∀ c, 0 ≤ v c) :
    0 ≤ ∫ z, onPos F z * onPos F (swapHalves z) * rpWeight w v z ∂(ν.prod (νC.prod ν)) := by
  rw [integral_onPos_eq ν νC F F w v mF mF mw mv]
  exact rp_core ν νC (mF.mul mw) mv (bF.mul bw) bv hv

/-- **Abstract reflection positivity, complex version:** `∫ F · conj (F ∘ θ) · w w v ≥ 0` for real weights `w`, `v ≥ 0`. -/
theorem rp_abstract_complex {F : X × C → ℂ} {w : X × C → ℝ} {v : C → ℝ} (mF : Measurable F) (mw : Measurable w)
    (mv : Measurable v) (bF : IsBdd F) (bw : IsBdd w) (bv : IsBdd v) (hv : ∀ c, 0 ≤ v c) :
    0 ≤ ∫ z, onPos F z * conj (onPos F (swapHalves z)) * ((rpWeight w v z : ℝ) : ℂ) ∂(ν.prod (νC.prod ν)) := by
  have mw' : Measurable (fun p => (w p : ℂ)) := Complex.measurable_ofReal.comp mw
  have bw' : IsBdd (fun p => (w p : ℂ)) := by
    obtain ⟨M, hM⟩ := bw; exact ⟨M, fun c => by simpa using hM c⟩
  have hmK : Measurable (fun p => F p * (w p : ℂ)) := mF.mul mw'
  have hmeas : Measurable (fun y : C × (X × X) => (fun p => F p * (w p : ℂ)) (y.2.1, y.1) *
        conj ((fun p => F p * (w p : ℂ)) (y.2.2, y.1)) * ((v y.1 : ℝ) : ℂ)) :=
    ((hmK.comp (measurable_snd.fst.prodMk measurable_fst)).mul
        ((Complex.continuous_conj.measurable.comp hmK).comp (measurable_snd.snd.prodMk measurable_fst))).mul
        ((Complex.measurable_ofReal.comp mv).comp measurable_fst)
  have htr := integral_comp_of_measurePreserving (measurePreserving_rearrange ν νC) hmeas.aestronglyMeasurable
  have key : ∫ z, onPos F z * conj (onPos F (swapHalves z)) * ((rpWeight w v z : ℝ) : ℂ) ∂(ν.prod (νC.prod ν)) =
      ∫ y, (fun p => F p * (w p : ℂ)) (y.2.1, y.1) *
        conj ((fun p => F p * (w p : ℂ)) (y.2.2, y.1)) * ((v y.1 : ℝ) : ℂ) ∂(νC.prod (ν.prod ν)) := by
    rw [← htr]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [onPos, swapHalves, rpWeight, rearrange, map_mul, Complex.conj_ofReal]; push_cast; ring
  rw [key]
  exact rp_core_complex ν νC hmK mv (bF.mul bw') bv hv

end Core

/-! ## Gram positivity and Cauchy–Schwarz from reflection positivity -/

section Form

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (θ : Ω → Ω) (W : Ω → ℝ) (Adm : (Ω → ℝ) → Prop)

/-- **Gram positivity.** If a class `Adm` of functions is closed under linear combinations, the reflected integrals
    `∫ F · (G ∘ θ) · W` exist, and `∫ F · (F ∘ θ) · W ≥ 0` on `Adm`, then for `F₁, …, F_k ∈ Adm` the matrix
    `[∫ Fᵢ · (Fⱼ ∘ θ) · W]` is positive semi-definite. -/
theorem gram_of_rp (h0 : Adm 0) (hadd : ∀ F G, Adm F → Adm G → Adm (F + G))
    (hsmul : ∀ (t : ℝ) F, Adm F → Adm (t • F))
    (hint : ∀ F G, Adm F → Adm G → Integrable (fun ω => F ω * G (θ ω) * W ω) μ)
    (hpos : ∀ F, Adm F → 0 ≤ ∫ ω, F ω * F (θ ω) * W ω ∂μ)
    {ι : Type*} (s : Finset ι) (Fs : ι → Ω → ℝ) (hFs : ∀ i ∈ s, Adm (Fs i)) (z : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, z i * z j * ∫ ω, Fs i ω * Fs j (θ ω) * W ω ∂μ := by
  set F : Ω → ℝ := ∑ i ∈ s, z i • Fs i with hFdef
  have hF : Adm F := Finset.sum_induction _ Adm hadd h0 (fun i hi => hsmul _ _ (hFs i hi))
  have hexp : ∀ ω, F ω * F (θ ω) * W ω = ∑ i ∈ s, ∑ j ∈ s, z i * z j * (Fs i ω * Fs j (θ ω) * W ω) := by
    intro ω
    simp only [hFdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h := hpos F hF
  simp_rw [hexp] at h
  rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _
    (fun j hj => (hint _ _ (hFs i hi) (hFs j hj)).const_mul _))] at h
  refine h.trans_eq (Finset.sum_congr rfl fun i hi => ?_)
  rw [integral_finsetSum _ (fun j hj => (hint _ _ (hFs i hi) (hFs j hj)).const_mul _)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- A real quadratic polynomial that is nonnegative everywhere has nonpositive discriminant. -/
theorem sq_le_mul_of_quadratic_nonneg {a b c : ℝ} (h : ∀ t : ℝ, 0 ≤ c * (t * t) + 2 * b * t + a) :
    b ^ 2 ≤ a * c := by
  have := discrim_le_zero h
  unfold discrim at this
  nlinarith

/-- **Cauchy–Schwarz for the reflected form.** Under the hypotheses of `gram_of_rp` and symmetry,
    `|∫ F · (G ∘ θ) · W|² ≤ (∫ F · (F ∘ θ) · W) (∫ G · (G ∘ θ) · W)`. -/
theorem cs_of_rp (h0 : Adm 0) (hadd : ∀ F G, Adm F → Adm G → Adm (F + G))
    (hsmul : ∀ (t : ℝ) F, Adm F → Adm (t • F))
    (hint : ∀ F G, Adm F → Adm G → Integrable (fun ω => F ω * G (θ ω) * W ω) μ)
    (hpos : ∀ F, Adm F → 0 ≤ ∫ ω, F ω * F (θ ω) * W ω ∂μ)
    (hsymm : ∀ F G, Adm F → Adm G → ∫ ω, F ω * G (θ ω) * W ω ∂μ = ∫ ω, G ω * F (θ ω) * W ω ∂μ)
    {F G : Ω → ℝ} (hF : Adm F) (hG : Adm G) :
    |∫ ω, F ω * G (θ ω) * W ω ∂μ| ^ 2 ≤ (∫ ω, F ω * F (θ ω) * W ω ∂μ) * ∫ ω, G ω * G (θ ω) * W ω ∂μ := by
  rw [sq_abs]
  refine sq_le_mul_of_quadratic_nonneg fun t => ?_
  have h := gram_of_rp θ W Adm h0 hadd hsmul hint hpos (μ := μ) (Finset.univ : Finset (Fin 2)) ![F, G]
    (by intro i _; fin_cases i <;> simpa) ![1, t]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [hsymm G F hG hF] at h
  nlinarith [h]

end Form

/-- **Abstract Cauchy–Schwarz for reflection positivity** on `X × C × X`:
    `|∫ F · (G ∘ θ) · w w v|² ≤ (∫ F · (F ∘ θ) · w w v) (∫ G · (G ∘ θ) · w w v)`. -/
theorem rp_abstract_cs {X C : Type*} [MeasurableSpace X] [MeasurableSpace C] (ν : Measure X) (νC : Measure C)
    [IsFiniteMeasure ν] [IsFiniteMeasure νC] {F G w : X × C → ℝ} {v : C → ℝ}
    (mF : Measurable F) (mG : Measurable G) (mw : Measurable w) (mv : Measurable v)
    (bF : IsBdd F) (bG : IsBdd G) (bw : IsBdd w) (bv : IsBdd v) (hv : ∀ c, 0 ≤ v c) :
    |∫ z, onPos F z * onPos G (swapHalves z) * rpWeight w v z ∂(ν.prod (νC.prod ν))| ^ 2 ≤
      (∫ z, onPos F z * onPos F (swapHalves z) * rpWeight w v z ∂(ν.prod (νC.prod ν))) *
        ∫ z, onPos G z * onPos G (swapHalves z) * rpWeight w v z ∂(ν.prod (νC.prod ν)) := by
  let Adm : (X × (C × X) → ℝ) → Prop := fun Φ => ∃ H : X × C → ℝ, Measurable H ∧ IsBdd H ∧ Φ = onPos H
  have hAdm : ∀ H : X × C → ℝ, Measurable H → IsBdd H → Adm (onPos H) := fun H m b => ⟨H, m, b, rfl⟩
  refine cs_of_rp swapHalves (rpWeight w v) Adm (μ := ν.prod (νC.prod ν)) ?_ ?_ ?_ ?_ ?_ ?_ (hAdm F mF bF)
    (hAdm G mG bG)
  · exact ⟨0, measurable_const, IsBdd.const 0, rfl⟩
  · rintro _ _ ⟨H, mH, bH, rfl⟩ ⟨K, mK, bK, rfl⟩
    exact ⟨H + K, mH.add mK, bH.add bK, rfl⟩
  · rintro t _ ⟨H, mH, bH, rfl⟩
    exact ⟨t • H, mH.const_smul t, bH.const_mul t, rfl⟩
  · rintro _ _ ⟨H, mH, bH, rfl⟩ ⟨K, mK, bK, rfl⟩
    refine IsBdd.integrable (((bH.comp _).mul (bK.comp _)).mul ((((bw.comp _).mul (bw.comp _)).mul (bv.comp _)))) ?_
    exact (((mH.comp (measurable_fst.prodMk measurable_snd.fst)).mul
      (mK.comp (measurable_snd.snd.prodMk measurable_snd.fst))).mul
      (((mw.comp (measurable_fst.prodMk measurable_snd.fst)).mul
        (mw.comp (measurable_snd.snd.prodMk measurable_snd.fst))).mul
        (mv.comp measurable_snd.fst))).aestronglyMeasurable
  · rintro _ ⟨H, mH, bH, rfl⟩
    exact rp_abstract ν νC mH mw mv bH bw bv hv
  · rintro _ _ ⟨H, mH, bH, rfl⟩ ⟨K, mK, bK, rfl⟩
    rw [integral_onPos_eq ν νC H K w v mH mK mw mv, integral_onPos_eq ν νC K H w v mK mH mw mv,
      reflection_formula ν νC (h₁ := fun p => H p * w p) (h₂ := fun p => K p * w p) (mH.mul mw) (mK.mul mw) mv
        (bH.mul bw) (bK.mul bw) bv,
      reflection_formula ν νC (h₁ := fun p => K p * w p) (h₂ := fun p => H p * w p) (mK.mul mw) (mH.mul mw) mv
        (bK.mul bw) (bH.mul bw) bv]
    refine integral_congr_ae (ae_of_all _ fun c => ?_)
    simp only; ring

end Positivity
