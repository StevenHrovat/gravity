/-
Reflection positivity for product measures over a finite index set (positivity project, 2026-11-21). Released under
Apache 2.0.

# Reflection positivity on `ι → G` with the product measure

The configuration space of a lattice gauge theory is `ι → G` (one group element per link) with the product measure
`⊗_ι ν`. A reflection splits the index set into fixed coordinates `C`, positive coordinates `X`, and their mirror images
(again indexed by `X`); this is an equivalence `e : C ⊕ (X ⊕ X) ≃ ι`. A reflection `Θ` of configurations keeps the fixed
coordinates and sends the positive coordinate `x` to `σ x (U (mirror of x))`, where each `σ x` preserves `ν` (identity or
inversion in the gauge case).

We prove that `U ↦ (U|_C, U|_X, σ (U|_mirror))` carries `⊗_ι ν` to `(⊗_C ν) ⊗ (⊗_X ν) ⊗ (⊗_X ν)`
(`measurePreserving_split`), and deduce from the abstract identity of `Positivity.Abstract`: for bounded measurable `F, G`
depending only on fixed and positive coordinates and `B` depending only on fixed coordinates,

  `∫ F · (G ∘ Θ) · B = ∫ (∫ F) (∫ G) B`  (`integral_split_formula`),

hence reflection positivity (`config_rp`, for `B ≥ 0`), symmetry (`config_symm`), Gram positivity and Cauchy–Schwarz.
-/

import Positivity.Abstract

open MeasureTheory

set_option linter.unusedSectionVars false

noncomputable section

namespace Positivity

/-- Reindexing a product measure of identical factors along an equivalence preserves it. -/
theorem measurePreserving_reindex {ι ι' G : Type*} [Fintype ι] [Fintype ι'] [MeasurableSpace G] (ν : Measure G)
    [SigmaFinite ν] (f : ι' ≃ ι) :
    MeasurePreserving (fun (U : ι → G) (i : ι') => U (f i)) (Measure.pi fun _ : ι => ν)
      (Measure.pi fun _ : ι' => ν) := by
  have h := MeasurePreserving.symm _ (measurePreserving_piCongrLeft (fun _ : ι => ν) f)
  convert h using 1
  funext U i; rfl

section Config

variable {ι C X G : Type*} [Fintype ι] [Fintype C] [Fintype X] [MeasurableSpace G]
  (ν : Measure G) [IsProbabilityMeasure ν] (e : C ⊕ (X ⊕ X) ≃ ι)

/-- `F` depends only on the fixed and the positive coordinates. -/
def DepPos {α : Type*} (F : (ι → G) → α) : Prop :=
  ∀ U V : ι → G, (∀ c, U (e (.inl c)) = V (e (.inl c))) → (∀ x, U (e (.inr (.inl x))) = V (e (.inr (.inl x)))) →
    F U = F V

/-- `B` depends only on the fixed coordinates. -/
def DepFix {α : Type*} (B : (ι → G) → α) : Prop :=
  ∀ U V : ι → G, (∀ c, U (e (.inl c)) = V (e (.inl c))) → B U = B V

/-- Split a configuration into its fixed part, its positive part, and its (twisted) negative part. -/
def split (σ : X → G → G) (U : ι → G) : (C → G) × ((X → G) × (X → G)) :=
  (fun c => U (e (.inl c)), (fun x => U (e (.inr (.inl x))), fun x => σ x (U (e (.inr (.inr x))))))

/-- Glue the three parts back into a configuration (without twist). -/
def glue (z : (C → G) × ((X → G) × (X → G))) : ι → G :=
  fun i => Sum.elim z.1 (Sum.elim z.2.1 z.2.2) (e.symm i)

omit [Fintype ι] [Fintype C] [Fintype X] [MeasurableSpace G] in
theorem glue_inl (z : (C → G) × ((X → G) × (X → G))) (c : C) : glue e z (e (.inl c)) = z.1 c := by
  simp [glue]

omit [Fintype ι] [Fintype C] [Fintype X] [MeasurableSpace G] in
theorem glue_inrl (z : (C → G) × ((X → G) × (X → G))) (x : X) : glue e z (e (.inr (.inl x))) = z.2.1 x := by
  simp [glue]

omit [Fintype ι] [Fintype C] [Fintype X] in
theorem measurable_glue : Measurable (glue (G := G) e) := by
  refine measurable_pi_iff.mpr fun i => ?_
  rcases h : e.symm i with c | x | x
  · simp only [glue, h, Sum.elim_inl]; exact (measurable_pi_apply c).comp measurable_fst
  · simp only [glue, h, Sum.elim_inl, Sum.elim_inr]; exact (measurable_pi_apply x).comp measurable_snd.fst
  · simp only [glue, h, Sum.elim_inr]; exact (measurable_pi_apply x).comp measurable_snd.snd

/-- **The splitting map is measure preserving.** -/
theorem measurePreserving_split (σ : X → G → G) (hσ : ∀ x, MeasurePreserving (σ x) ν ν) :
    MeasurePreserving (split e σ) (Measure.pi fun _ : ι => ν)
      ((Measure.pi fun _ : C => ν).prod ((Measure.pi fun _ : X => ν).prod (Measure.pi fun _ : X => ν))) := by
  have h0 := measurePreserving_reindex ν e
  have h1 := measurePreserving_sumPiEquivProdPi (X := fun _ : C ⊕ (X ⊕ X) => G) (fun _ => ν)
  have h2 := (MeasurePreserving.id (Measure.pi fun _ : C => ν)).prod
    (measurePreserving_sumPiEquivProdPi (X := fun _ : X ⊕ X => G) (fun _ => ν))
  have h3 := (MeasurePreserving.id (Measure.pi fun _ : C => ν)).prod
    ((MeasurePreserving.id (Measure.pi fun _ : X => ν)).prod (measurePreserving_pi (fun _ => ν) (fun _ => ν) hσ))
  have h := h3.comp (h2.comp (h1.comp h0))
  convert h using 1
  funext U; rfl

variable [Nonempty G]

/-- The function of (positive part, fixed part) that a `DepPos` function induces. -/
def posPart (F : (ι → G) → ℝ) (p : (X → G) × (C → G)) : ℝ := F (glue e (p.2, (p.1, p.1)))

/-- The function of the fixed part that a `DepFix` function induces. -/
def fixPart (B : (ι → G) → ℝ) (c : C → G) : ℝ :=
  B (glue e (c, ((fun _ => Classical.arbitrary G), (fun _ => Classical.arbitrary G))))

/-- Hypotheses on the reflection `Θ`: it fixes the fixed coordinates and maps the positive coordinate `x` to the twisted
    value at its mirror. -/
structure IsReflection (σ : X → G → G) (Θ : (ι → G) → (ι → G)) : Prop where
  fix : ∀ U c, Θ U (e (.inl c)) = U (e (.inl c))
  pos : ∀ U x, Θ U (e (.inr (.inl x))) = σ x (U (e (.inr (.inr x))))

variable {e}

omit [Fintype ι] [Fintype C] [Fintype X] [MeasurableSpace G] [Nonempty G] in
theorem DepPos.mul {F F' : (ι → G) → ℝ} (hF : DepPos e F) (hF' : DepPos e F') :
    DepPos e (fun U => F U * F' U) := fun U V h0 h1 => by
  show F U * F' U = F V * F' V
  rw [hF U V h0 h1, hF' U V h0 h1]


theorem DepPos.eq_posPart {F : (ι → G) → ℝ} (hF : DepPos e F) (U : ι → G) :
    F U = posPart e F ((split e (fun _ => id) U).2.1, (split e (fun _ => id) U).1) := by
  refine hF _ _ (fun c => ?_) (fun x => ?_)
  · rw [glue_inl]; rfl
  · rw [glue_inrl]; rfl

theorem DepPos.eq_posPart_theta {F : (ι → G) → ℝ} (hF : DepPos e F) (σ : X → G → G) (Θ : (ι → G) → (ι → G))
    (hΘ0 : ∀ U c, Θ U (e (.inl c)) = U (e (.inl c)))
    (hΘ1 : ∀ U x, Θ U (e (.inr (.inl x))) = σ x (U (e (.inr (.inr x))))) (U : ι → G) :
    F (Θ U) = posPart e F ((split e σ U).2.2, (split e σ U).1) := by
  refine hF _ _ (fun c => ?_) (fun x => ?_)
  · rw [glue_inl, hΘ0]; rfl
  · rw [glue_inrl, hΘ1]; rfl

theorem DepFix.eq_fixPart {B : (ι → G) → ℝ} (hB : DepFix e B) (σ : X → G → G) (U : ι → G) :
    B U = fixPart e B (split e σ U).1 := by
  refine hB _ _ (fun c => ?_)
  rw [glue_inl]; rfl

omit [IsProbabilityMeasure ν] [Fintype ι] [Fintype C] [Fintype X] in
theorem measurable_posPart {F : (ι → G) → ℝ} (mF : Measurable F) : Measurable (posPart e F) :=
  mF.comp ((measurable_glue e).comp (measurable_snd.prodMk (measurable_fst.prodMk measurable_fst)))

omit [IsProbabilityMeasure ν] [Fintype ι] [Fintype C] [Fintype X] in
theorem measurable_fixPart {B : (ι → G) → ℝ} (mB : Measurable B) : Measurable (fixPart e B) :=
  mB.comp ((measurable_glue e).comp (measurable_id.prodMk measurable_const))

variable {σ : X → G → G} {Θ : (ι → G) → (ι → G)}

omit [IsProbabilityMeasure ν] in
/-- `F ∘ Θ` is measurable for measurable `F` of the fixed and positive coordinates. -/
theorem measurable_comp_reflection (hσ : ∀ x, MeasurePreserving (σ x) ν ν) (hΘ : IsReflection e σ Θ)
    {F : (ι → G) → ℝ} (hF : DepPos e F) (mF : Measurable F) : Measurable (fun U => F (Θ U)) := by
  have hs : Measurable (split e σ) := by
    refine Measurable.prodMk (measurable_pi_iff.mpr fun c => measurable_pi_apply _)
      (Measurable.prodMk (measurable_pi_iff.mpr fun x => measurable_pi_apply _)
        (measurable_pi_iff.mpr fun x => (hσ x).measurable.comp (measurable_pi_apply _)))
  have : (fun U => F (Θ U)) = fun U => posPart e F ((split e σ U).2.2, (split e σ U).1) :=
    funext (hF.eq_posPart_theta σ Θ hΘ.fix hΘ.pos)
  rw [this]
  exact (measurable_posPart mF).comp (hs.snd.snd.prodMk hs.fst)

/-- **The reflection formula on `ι → G`.** -/
theorem integral_split_formula (hσ : ∀ x, MeasurePreserving (σ x) ν ν) (hΘ : IsReflection e σ Θ)
    {F F' B : (ι → G) → ℝ} (hF : DepPos e F) (hF' : DepPos e F') (hB : DepFix e B)
    (mF : Measurable F) (mF' : Measurable F') (mB : Measurable B) (bF : IsBdd F) (bF' : IsBdd F') (bB : IsBdd B) :
    ∫ U, F U * F' (Θ U) * B U ∂(Measure.pi fun _ : ι => ν) =
      ∫ c, (∫ a, posPart e F (a, c) ∂(Measure.pi fun _ : X => ν)) *
        (∫ b, posPart e F' (b, c) ∂(Measure.pi fun _ : X => ν)) * fixPart e B c ∂(Measure.pi fun _ : C => ν) := by
  have hsplit := measurePreserving_split ν e σ hσ
  have hK : Measurable (fun z : (C → G) × ((X → G) × (X → G)) =>
      posPart e F (z.2.1, z.1) * posPart e F' (z.2.2, z.1) * fixPart e B z.1) :=
    (((measurable_posPart mF).comp (measurable_snd.fst.prodMk measurable_fst)).mul
      ((measurable_posPart mF').comp (measurable_snd.snd.prodMk measurable_fst))).mul
      ((measurable_fixPart mB).comp measurable_fst)
  have hpt : ∀ U, F U * F' (Θ U) * B U =
      posPart e F ((split e σ U).2.1, (split e σ U).1) * posPart e F' ((split e σ U).2.2, (split e σ U).1) *
        fixPart e B (split e σ U).1 := by
    intro U
    rw [hF.eq_posPart U, hF'.eq_posPart_theta σ Θ hΘ.fix hΘ.pos U, hB.eq_fixPart σ U]
    rfl
  simp_rw [hpt]
  rw [integral_comp_of_measurePreserving hsplit hK.aestronglyMeasurable]
  have bP : ∀ {H : (ι → G) → ℝ}, IsBdd H → IsBdd (posPart e H) := fun h => h.comp _
  exact reflection_formula _ _ (measurable_posPart mF) (measurable_posPart mF') (measurable_fixPart mB)
    (bP bF) (bP bF') (bB.comp _)

/-- **Reflection positivity on `ι → G`.** -/
theorem config_rp (hσ : ∀ x, MeasurePreserving (σ x) ν ν) (hΘ : IsReflection e σ Θ)
    {F B : (ι → G) → ℝ} (hF : DepPos e F) (hB : DepFix e B) (mF : Measurable F) (mB : Measurable B)
    (bF : IsBdd F) (bB : IsBdd B) (hB0 : ∀ U, 0 ≤ B U) :
    0 ≤ ∫ U, F U * F (Θ U) * B U ∂(Measure.pi fun _ : ι => ν) := by
  rw [integral_split_formula ν hσ hΘ hF hF hB mF mF mB bF bF bB]
  exact integral_nonneg fun c => mul_nonneg (mul_self_nonneg _) (hB0 _)

/-- **Symmetry of the reflected form on `ι → G`.** -/
theorem config_symm (hσ : ∀ x, MeasurePreserving (σ x) ν ν) (hΘ : IsReflection e σ Θ)
    {F F' B : (ι → G) → ℝ} (hF : DepPos e F) (hF' : DepPos e F') (hB : DepFix e B)
    (mF : Measurable F) (mF' : Measurable F') (mB : Measurable B) (bF : IsBdd F) (bF' : IsBdd F') (bB : IsBdd B) :
    ∫ U, F U * F' (Θ U) * B U ∂(Measure.pi fun _ : ι => ν) =
      ∫ U, F' U * F (Θ U) * B U ∂(Measure.pi fun _ : ι => ν) := by
  rw [integral_split_formula ν hσ hΘ hF hF' hB mF mF' mB bF bF' bB,
    integral_split_formula ν hσ hΘ hF' hF hB mF' mF mB bF' bF bB]
  refine integral_congr_ae (ae_of_all _ fun c => ?_)
  simp only []; ring

/-- Integrability of the reflected integrand. -/
theorem config_integrable (hσ : ∀ x, MeasurePreserving (σ x) ν ν) (hΘ : IsReflection e σ Θ)
    {F F' B : (ι → G) → ℝ} (hF' : DepPos e F') (mF : Measurable F) (mF' : Measurable F') (mB : Measurable B)
    (bF : IsBdd F) (bF' : IsBdd F') (bB : IsBdd B) :
    Integrable (fun U => F U * F' (Θ U) * B U) (Measure.pi fun _ : ι => ν) :=
  IsBdd.integrable ((bF.mul (bF'.comp Θ)).mul bB)
    ((mF.mul (measurable_comp_reflection ν hσ hΘ hF' mF')).mul mB).aestronglyMeasurable

end Config

end Positivity
