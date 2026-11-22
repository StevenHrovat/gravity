/-
Proof phase, cycle 8, workstream d (c8d-strict): the strict reflection bound `Z_tw < Z` (2026-11-22). Released under
Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c8d-strict/NOTE.md`.
-/

import ProofPhase.Flip.Bound

/-!
# `Z_tw < Z`: the strict reflection bound

**Setting.** As in `ProofPhase.Flip.Bound`: the time chain `ℤ/Tℤ × (spatial graph)` (`T` even), a chain weight
`W = ∏_t V(a_t) K(a_t, b_t, a_{t+1})`, a slice twist `g` (linkwise, measure preserving, involutive, `V`-invariant), the
twisted weight; `A`, `B` the half-chain and fixed-slice weights of `cweight_factor`, `σ = flip0 g` the twist of slice
`0`. `Bound` proved `Z_tw ≤ Z` and `2(Z − Z_tw) = ⟨A∘σ − A, A∘σ − A⟩` for the reflection form
`⟨F, F'⟩ = ∫ F · (F'∘Θ) · B`.

**1. Strict bound from one boundary moment (`cZtw_lt_cZ_of_moment`).** Every chain weight with `K > 0`, every slice
twist, every even `T`: if some bounded measurable function `η` of the two fixed slices `a₀`, `a_{T/2}` has
`∫ (A∘σ − A) · η(a₀, a_{T/2}) · B ≠ 0`, then `Z_tw < Z` (Cauchy–Schwarz for the reflection form). This is the
non-degeneracy "the half-chain state `ψ(a₀, a_{T/2}) = ∫ A d(open half)` is not `σ`-invariant on a set of positive
measure", stated as a moment.

**2. Strict bound from one transfer step (`cZtw_lt_cZ_of_step`).** With the one-step transfer operator
`(𝒦 f)(a) = ∫ K(a, b, c) V(c) f(c) db dc` and `⟨f, h⟩_V = ∫ f h V` on one slice: if `⟨φ, 𝒦 χ⟩_V ≠ 0` for some bounded
measurable `φ` that is odd under the twist (`OddUnder`) and some bounded measurable `χ`, then `Z_tw < Z` **for every
even `T`**. The hypothesis does not involve `T`. Ingredients: the half-chain identity
`∫ A · φ(a₀) χ(a_{T/2}) · B = ⟨φ, 𝒦^{T/2} χ⟩_V` (`half_chain`, by integrating out one step at a time,
`integral_step`); the symmetry `⟨f, 𝒦 h⟩_V = ⟨𝒦 f, h⟩_V` (`vip_kop`, from `K(c, b⁻¹, a) = K(a, b, c)`); the descent
"if `𝒦^{j+2}` kills the odd sector, so does `𝒦^{j+1}`" (`stepVanish_descend`, `‖𝒦^{j+1} φ‖² = ⟨φ, 𝒦^{j+2} 𝒦^j φ⟩`).
Only the symmetry of the transfer matrix is used, not its positivity, so the coupling may have either sign.

**3. SU(2) (`su2_Ztw_lt_Z`, `su2_Ze1_pos`, `su2_flipProb_lt_half`).** For the SU(2) Wilson action, every `β ≠ 0`, every
`L ≥ 1`, every even `T`, every spatial background twist `P`, every plane position `c`: `Z_tw < Z`, so
`Z − Z_tw = 2 Z_{e=1} > 0` and `0 ≤ p < ½`. The step hypothesis is discharged with `φ = χ = Re tr P / V`, `P` the
Polyakov line through the origin along the first spatial axis (odd under the twist): after the gauge change that absorbs
the temporal links (`gaugeSub`) the step integral factorises over links, and Schur's lemma
`∫ e^{β Re tr v} Re tr(v M) dv = λ(β) Re tr M` (`schur_SU2`) integrates the line link by link (`lineInt`), giving
`⟨φ, 𝒦 φ⟩_V = λ(β)^L κ ∫ (Re tr P)²` (`su2_vip_polyRatio`) with `κ > 0`, `∫ (Re tr P)² > 0` (Haar measure charges open
sets) and `λ(β) = Re ∫ e^{β Re tr v} v₀₀ dv ≠ 0` for `β ≠ 0` (`schurC_ne_zero`: `β λ(β) = ½ ∫ (e^{βt} − 1) βt > 0`,
`t = Re tr v`).

**Claim discipline.** Substantive and sharp in `β`: at `β = 0` the weight is constant and `Z_tw = Z` exactly, so
`β ≠ 0` is necessary; the theorem holds for all other real `β`, all `L`, all even `T`. It is a strict inequality at each
fixed finite lattice, with no control of its size: it gives no lower bound on `Z − Z_tw` uniform in the volume, no bound
on the flux free energy, and so no confinement or mass-gap content (`p < ½` strictly, but `p` may still tend to `½` or
to `0`). Items 1 and 2 are model-blind (any chain weight, any compact group); the SU(2) input of item 3 is Schur's lemma
for the defining representation (`schurN_01`, `schurN_10`, `schurN_11`), the reality of SU(2) traces and the sign of
`λ(β)`. As in `Bound`, the bridge from this chain to `ProofPhase.RouteB.twistZ` on `(ℤ/Nℤ)⁴` is not formalised.
-/

open MeasureTheory Finset Positivity AreaLaw.Concrete ProofPhase.RouteB Filter

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Flip

/-! ## Product measures: resampling a set of coordinates, marginals -/

section Resample

variable {G : Type*} [MeasurableSpace G] (μ : Measure G) [IsProbabilityMeasure μ]

/-- Mixing two independent configurations (the coordinates in `p` from the second) preserves the product measure. -/
theorem measurePreserving_mix {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving (fun q : (ι → G) × (ι → G) => fun i => if p i then q.2 i else q.1 i)
      ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : ι => μ)) (Measure.pi fun _ : ι => μ) := by
  have h1 := MeasurePreserving.symm _
    (measurePreserving_arrowProdEquivProdArrow G G ι (fun _ => μ) (fun _ => μ))
  have h2 := measurePreserving_pi (fun _ : ι => μ.prod μ) (fun _ : ι => μ)
    (f := fun i => if p i then (Prod.snd : G × G → G) else Prod.fst) (fun i => by
      by_cases h : p i
      · simp only [h, ↓reduceIte]; exact measurePreserving_snd
      · simp only [h, ↓reduceIte]; exact measurePreserving_fst)
  convert h2.comp h1 using 1
  funext q i
  by_cases h : p i
  · simp only [Function.comp, h, ↓reduceIte]; rfl
  · simp only [Function.comp, h, ↓reduceIte]; rfl


/-- **Resampling**: integrating over a configuration equals integrating over a configuration whose `p`-coordinates
are replaced by those of an independent copy. -/
theorem integral_mix {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] {Φ : (ι → G) → ℝ}
    (hΦ : Integrable Φ (Measure.pi fun _ : ι => μ)) :
    ∫ U, Φ U ∂(Measure.pi fun _ : ι => μ) =
      ∫ U, ∫ U', Φ (fun i => if p i then U' i else U i) ∂(Measure.pi fun _ : ι => μ)
        ∂(Measure.pi fun _ : ι => μ) := by
  have hmp := measurePreserving_mix μ p
  rw [← integral_comp_of_measurePreserving hmp hΦ.aestronglyMeasurable]
  exact integral_prod _ ((hmp.integrable_comp hΦ.aestronglyMeasurable).2 hΦ)

/-- Restriction to the coordinates in the image of an injective map is measure preserving (marginal). -/
theorem measurePreserving_restrictInj {ι J : Type*} [Fintype ι] [Fintype J] (f : J → ι)
    (hf : Function.Injective f) :
    MeasurePreserving (fun (U : ι → G) (j : J) => U (f j)) (Measure.pi fun _ : ι => μ)
      (Measure.pi fun _ : J => μ) := by
  have h1 := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (fun i => i ∈ Set.range f)
  have h2 := measurePreserving_fst.comp h1
  have h3 := @measurePreserving_reindex (Set.range f) J G (Subtype.fintype _) _ _ μ _ (Equiv.ofInjective f hf)
  convert h3.comp h2 using 1
  funext U j; rfl

end Resample

/-! ## The chain: boundary observables, the strict bound from one non-vanishing moment -/

section ChainStrict

variable {G : Type*} [Group G] [MeasurableSpace G] {E S : Type*} [Fintype E] [Fintype S] {T : ℕ} [NeZero T]

/-- The second fixed slice `t = T/2`. -/
def halfT (T : ℕ) : ZMod T := ((T / 2 : ℕ) : ZMod T)

theorem val_halfT : (halfT T).val = T / 2 :=
  ZMod.val_cast_of_lt (Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne T)) (by norm_num))

theorem neg_halfT (hT : Even T) : -halfT T = halfT T := neg_eq_self_of_val_half hT _ val_halfT

theorem halfT_ne_zero (hT : Even T) : halfT T ≠ 0 := by
  intro h
  have h1 := congrArg ZMod.val h
  rw [val_halfT, ZMod.val_zero] at h1
  have := two_le_of_even hT
  omega

/-- **A boundary observable of the half chain**: a function `η` of the two fixed slices `a₀`, `a_{T/2}`. -/
def bdry (η : (E → G) × (E → G) → ℝ) (U : CCfg G E S T) : ℝ := η (sp U 0, sp U (halfT T))

theorem bdry_ctheta (hT : Even T) (η : (E → G) × (E → G) → ℝ) (U : CCfg G E S T) :
    bdry η (ctheta U) = bdry η U := by
  unfold bdry
  rw [sp_ctheta, sp_ctheta, neg_zero, neg_halfT hT]

theorem bdry_depPos (hT : Even T) (η : (E → G) × (E → G) → ℝ) :
    DepPos (csplit (E := E) (S := S) hT) (bdry (G := G) (T := T) η) := by
  intro U V h0 _
  unfold bdry
  have e : ∀ t : ZMod T, (t.val = 0 ∨ t.val = T / 2) → sp U t = sp V t := fun t ht => by
    funext e; exact h0 ⟨(t, Sum.inl e), ht⟩
  rw [e 0 (Or.inl ZMod.val_zero), e (halfT T) (Or.inr val_halfT)]

theorem measurable_bdry {η : (E → G) × (E → G) → ℝ} (mη : Measurable η) :
    Measurable (bdry (G := G) (S := S) (T := T) η) :=
  mη.comp ((measurable_sp 0).prodMk (measurable_sp _))

theorem bdry_flip0 (hT : Even T) (g : E → G → G) (η : (E → G) × (E → G) → ℝ) (U : CCfg G E S T) :
    bdry η (flip0 g U) = η (sliceMap g (sp U 0), sp U (halfT T)) := by
  unfold bdry
  rw [sp_flip0_zero, sp_flip0_ne g U (halfT_ne_zero hT)]

variable [HasHaarProbability G] [MeasurableInv G] [(haarG G).IsInvInvariant]
variable (w : ChainWeight G E S) (g : E → G → G)

/-- The reflection twists are measure preserving (identity on spatial links, inversion on temporal ones). -/
theorem measurePreserving_ctwist (x : CPosL E S T) : MeasurePreserving (ctwist (G := G) x.1) (haarG G) (haarG G) := by
  rcases x with ⟨⟨t, e | s⟩, hx⟩
  · exact MeasurePreserving.id _
  · exact Measure.measurePreserving_inv _

/-- **The strict reflection bound from one boundary moment (general chain).** For every chain weight with `K > 0`,
every slice twist and every even `T`: if some bounded measurable function `η` of the two fixed slices sees the twist,
`∫ (A∘σ − A) · η(a₀, a_{T/2}) · B ≠ 0`, then `Z_tw < Z`. (Cauchy–Schwarz for the reflection form: the moment is
`⟨A∘σ − A, η⟩`, and `‖A∘σ − A‖² = 2(Z − Z_tw)`.) Equivalently: the half-chain state `ψ` (the integral of `A` over the
open half at fixed boundary slices) is not `σ`-invariant on a set of positive measure. -/
theorem cZtw_lt_cZ_of_moment (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c)
    (hg : ∀ e, MeasurePreserving (g e) (haarG G) (haarG G)) (hinv : ∀ e, Function.Involutive (g e))
    (hV : ∀ a, w.V (sliceMap g a) = w.V a) {η : (E → G) × (E → G) → ℝ} (mη : Measurable η) (bη : IsBdd η)
    (hη : ∫ U, (cA w (flip0 g U) - cA w U) * bdry η U * cB w U ∂(cHaar G E S T) ≠ 0) :
    cZtw (T := T) w g < cZ (T := T) w := by
  have : Nonempty G := ⟨1⟩
  have mg : ∀ e, Measurable (g e) := fun e => (hg e).measurable
  set F : CCfg G E S T → ℝ := fun U => cA w (flip0 g U) - cA w U with hFdef
  have hFd : CDep F CHalf := fun U V hUV => by
    simp only [hFdef]
    rw [cA_dep w hT U V hUV, cA_dep w hT _ _ (flip0_agree hUV)]
  have bF : IsBdd F := by
    obtain ⟨M, hM⟩ := cA_isBdd (T := T) w
    exact ⟨M + M, fun U => (norm_sub_le _ _).trans (add_le_add (hM _) (hM _))⟩
  have mF : Measurable F := ((measurable_cA w).comp (measurable_flip0 mg)).sub (measurable_cA w)
  have hΘ := isReflection_ctheta (G := G) (E := E) (S := S) hT
  let Adm : (CCfg G E S T → ℝ) → Prop := fun Φ => DepPos (csplit hT) Φ ∧ Measurable Φ ∧ IsBdd Φ
  have hAF : Adm F := ⟨depPos_of_cdep hT hFd, mF, bF⟩
  have hAH : Adm (bdry η) := ⟨bdry_depPos hT η, measurable_bdry mη, bη.comp _⟩
  have hcs := cs_of_rp ctheta (cB w) Adm (μ := cHaar G E S T)
    ⟨fun _ _ _ _ => rfl, measurable_zero, IsBdd.const 0⟩
    (fun F1 F2 hF hG => ⟨fun U V h0 h1 => by simp only [Pi.add_apply]; rw [hF.1 U V h0 h1, hG.1 U V h0 h1],
      hF.2.1.add hG.2.1, hF.2.2.add hG.2.2⟩)
    (fun t F1 hF => ⟨fun U V h0 h1 => by simp only [Pi.smul_apply]; rw [hF.1 U V h0 h1], hF.2.1.const_smul t,
      hF.2.2.const_mul t⟩)
    (fun F1 F2 hF hG => config_integrable (haarG G) measurePreserving_ctwist hΘ hG.1 hF.2.1 hG.2.1
      (measurable_cB w) hF.2.2 hG.2.2 (cB_isBdd w))
    (fun F1 hF => config_rp (haarG G) measurePreserving_ctwist hΘ hF.1 (cB_depFix w hT) hF.2.1 (measurable_cB w)
      hF.2.2 (cB_isBdd w) (cB_nonneg w))
    (fun F1 F2 hF hG => config_symm (haarG G) measurePreserving_ctwist hΘ hF.1 hG.1 (cB_depFix w hT) hF.2.1 hG.2.1
      (measurable_cB w) hF.2.2 hG.2.2 (cB_isBdd w))
    hAF hAH
  have hFF : 0 ≤ ∫ U, F U * F (ctheta U) * cB w U ∂(cHaar G E S T) :=
    config_rp (haarG G) measurePreserving_ctwist hΘ hAF.1 (cB_depFix w hT) mF (measurable_cB w) bF (cB_isBdd w)
      (cB_nonneg w)
  have hFH : ∫ U, F U * bdry η (ctheta U) * cB w U ∂(cHaar G E S T) =
      ∫ U, (cA w (flip0 g U) - cA w U) * bdry η U * cB w U ∂(cHaar G E S T) := by
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    simp only [bdry_ctheta hT, hFdef]
  rw [hFH] at hcs
  have hpos : 0 < ∫ U, F U * F (ctheta U) * cB w U ∂(cHaar G E S T) := by
    rcases hFF.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at hcs
      exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hcs (sq_nonneg _)))
        (abs_ne_zero.2 hη)
    · exact h0
  have h2 := cZ_sub_cZtw_eq w g hT hK hg hinv hV
  have h3 : ∫ U, F U * F (ctheta U) * cB w U ∂(cHaar G E S T) = 2 * (cZ (T := T) w - cZtw (T := T) w g) := h2.symm
  linarith

end ChainStrict

/-! ## The one-step transfer operator on one slice -/

section Kernel

variable {G : Type*} [Group G] [MeasurableSpace G] [HasHaarProbability G] {E S : Type*} [Fintype E] [Fintype S]
variable (w : ChainWeight G E S)

/-- Haar measure on the configurations of a finite set of links. -/
abbrev sliceHaar (G E : Type*) [MeasurableSpace G] [HasHaarProbability G] [Fintype E] : Measure (E → G) :=
  Measure.pi fun _ : E => haarG G

/-- **The one-step transfer operator** `(𝒦 f)(a) = ∫ K(a, b, c) V(c) f(c) db dc`. -/
def kop (f : (E → G) → ℝ) (a : E → G) : ℝ :=
  ∫ q, w.K a q.1 q.2 * w.V q.2 * f q.2 ∂((sliceHaar G S).prod (sliceHaar G E))

/-- **The slice inner product** `⟨f, h⟩_V = ∫ f h V`. -/
def vip (f h : (E → G) → ℝ) : ℝ := ∫ a, f a * h a * w.V a ∂(sliceHaar G E)

/-- Bounded and measurable. -/
def BM {α : Type*} [MeasurableSpace α] (f : α → ℝ) : Prop := Measurable f ∧ IsBdd f

theorem measurable_kop {f : (E → G) → ℝ} (mf : Measurable f) : Measurable (kop w f) := by
  have hm : Measurable fun z : (E → G) × ((S → G) × (E → G)) => w.K z.1 z.2.1 z.2.2 * w.V z.2.2 * f z.2.2 :=
    ((w.measK.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd))).mul
      (w.measV.comp measurable_snd.snd)).mul (mf.comp measurable_snd.snd)
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := (sliceHaar G S).prod (sliceHaar G E))).measurable

theorem isBdd_kop {f : (E → G) → ℝ} (bf : IsBdd f) : IsBdd (kop w f) := by
  obtain ⟨MV, hMV⟩ := w.V_bdd
  obtain ⟨MK, hMK⟩ := w.K_bdd
  obtain ⟨Mf, hMf⟩ := bf
  refine ⟨MK * MV * Mf, fun a => ?_⟩
  unfold kop
  refine (norm_integral_le_of_norm_le_const (C := MK * MV * Mf) (Eventually.of_forall fun q => ?_)).trans (by simp)
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (w.K_nonneg _ _ _), Real.norm_of_nonneg (w.V_nonneg _)]
  have hK0 := w.K_nonneg a q.1 q.2
  have hV0 := w.V_nonneg q.2
  exact mul_le_mul (mul_le_mul (hMK _ _ _) (hMV _) hV0 (hK0.trans (hMK _ _ _))) (hMf _) (norm_nonneg _)
    (mul_nonneg (hK0.trans (hMK _ _ _)) (hV0.trans (hMV _)))

theorem bm_kop {f : (E → G) → ℝ} (hf : BM f) : BM (kop w f) := ⟨measurable_kop w hf.1, isBdd_kop w hf.2⟩

theorem bm_kop_iter {f : (E → G) → ℝ} (hf : BM f) (j : ℕ) : BM ((kop w)^[j] f) := by
  induction j with
  | zero => exact hf
  | succ j ih => rw [Function.iterate_succ_apply']; exact bm_kop w ih

variable [MeasurableInv G] [(haarG G).IsInvInvariant]

/-- The reflection `(a, b, c) ↦ (c, b⁻¹, a)` of one time step preserves the measure. -/
theorem measurePreserving_kswap :
    MeasurePreserving (fun z : (E → G) × ((S → G) × (E → G)) => (z.2.2, ((fun s => (z.2.1 s)⁻¹), z.1)))
      ((sliceHaar G E).prod ((sliceHaar G S).prod (sliceHaar G E)))
      ((sliceHaar G E).prod ((sliceHaar G S).prod (sliceHaar G E))) := by
  have hinv : MeasurePreserving (fun b : S → G => fun s => (b s)⁻¹) (sliceHaar G S) (sliceHaar G S) :=
    measurePreserving_pi (fun _ => haarG G) (fun _ => haarG G) (fun _ => Measure.measurePreserving_inv _)
  have h0 := (MeasurePreserving.id (sliceHaar G E)).prod (hinv.prod (MeasurePreserving.id (sliceHaar G E)))
  have h1 := MeasurePreserving.symm _ (measurePreserving_prodAssoc (sliceHaar G E) (sliceHaar G S) (sliceHaar G E))
  have h2 := Measure.measurePreserving_swap (μ := (sliceHaar G E).prod (sliceHaar G S)) (ν := sliceHaar G E)
  have h3 := (MeasurePreserving.id (sliceHaar G E)).prod
    (Measure.measurePreserving_swap (μ := sliceHaar G E) (ν := sliceHaar G S))
  convert h3.comp (h2.comp (h1.comp h0)) using 1
  funext z; rfl

/-- **The transfer operator is symmetric** for `⟨·, ·⟩_V` (reflection symmetry `K(c, b⁻¹, a) = K(a, b, c)`). -/
theorem vip_kop {f h : (E → G) → ℝ} (hf : BM f) (hh : BM h) : vip w f (kop w h) = vip w (kop w f) h := by
  obtain ⟨MV, hMV⟩ := w.V_bdd
  obtain ⟨MK, hMK⟩ := w.K_bdd
  have bV : IsBdd w.V := ⟨MV, fun a => by rw [Real.norm_of_nonneg (w.V_nonneg a)]; exact hMV a⟩
  have bK : IsBdd fun z : (E → G) × ((S → G) × (E → G)) => w.K z.1 z.2.1 z.2.2 :=
    ⟨MK, fun z => by rw [Real.norm_of_nonneg (w.K_nonneg _ _ _)]; exact hMK _ _ _⟩
  have mK : Measurable fun z : (E → G) × ((S → G) × (E → G)) => w.K z.1 z.2.1 z.2.2 :=
    w.measK.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd))
  set μ3 := (sliceHaar G E).prod ((sliceHaar G S).prod (sliceHaar G E))
  set Ψ : (E → G) × ((S → G) × (E → G)) → ℝ :=
    fun z => f z.1 * w.V z.1 * (w.K z.1 z.2.1 z.2.2 * w.V z.2.2 * h z.2.2) with hΨ
  set Ψ' : (E → G) × ((S → G) × (E → G)) → ℝ :=
    fun z => h z.1 * w.V z.1 * (w.K z.1 z.2.1 z.2.2 * w.V z.2.2 * f z.2.2) with hΨ'
  have iΨ : Integrable Ψ μ3 :=
    IsBdd.integrable (((hf.2.comp _).mul (bV.comp _)).mul ((bK.mul (bV.comp _)).mul (hh.2.comp _)))
      (((hf.1.comp measurable_fst).mul (w.measV.comp measurable_fst)).mul
        ((mK.mul (w.measV.comp measurable_snd.snd)).mul (hh.1.comp measurable_snd.snd))).aestronglyMeasurable
  have iΨ' : Integrable Ψ' μ3 :=
    IsBdd.integrable (((hh.2.comp _).mul (bV.comp _)).mul ((bK.mul (bV.comp _)).mul (hf.2.comp _)))
      (((hh.1.comp measurable_fst).mul (w.measV.comp measurable_fst)).mul
        ((mK.mul (w.measV.comp measurable_snd.snd)).mul (hf.1.comp measurable_snd.snd))).aestronglyMeasurable
  have e1 : vip w f (kop w h) = ∫ z, Ψ z ∂μ3 := by
    rw [integral_prod _ iΨ]
    unfold vip kop
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    simp only [hΨ]
    rw [integral_const_mul]; ring
  have e2 : vip w (kop w f) h = ∫ z, Ψ' z ∂μ3 := by
    rw [integral_prod _ iΨ']
    unfold vip kop
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    simp only [hΨ']
    rw [integral_const_mul]; ring
  rw [e1, e2, ← integral_comp_of_measurePreserving measurePreserving_kswap iΨ'.aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [hΨ, hΨ']
  rw [w.K_symm]; ring

theorem vip_kop_iter {f h : (E → G) → ℝ} (hf : BM f) (hh : BM h) (j : ℕ) :
    vip w f ((kop w)^[j] h) = vip w ((kop w)^[j] f) h := by
  induction j generalizing h with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply' (kop w) j f, Function.iterate_succ_apply (kop w) j h, ih (bm_kop w hh),
      vip_kop w (bm_kop_iter w hf j) hh]

theorem vip_eq_zero_of_self {ψ : (E → G) → ℝ} (hψ : BM ψ) (h0 : vip w ψ ψ = 0) (χ : (E → G) → ℝ) :
    vip w ψ χ = 0 := by
  obtain ⟨MV, hMV⟩ := w.V_bdd
  have bV : IsBdd w.V := ⟨MV, fun a => by rw [Real.norm_of_nonneg (w.V_nonneg a)]; exact hMV a⟩
  have hnn : 0 ≤ᵐ[sliceHaar G E] fun a => ψ a * ψ a * w.V a :=
    ae_of_all _ fun a => mul_nonneg (mul_self_nonneg _) (w.V_nonneg _)
  have hi : Integrable (fun a => ψ a * ψ a * w.V a) (sliceHaar G E) :=
    IsBdd.integrable ((hψ.2.mul hψ.2).mul bV) ((hψ.1.mul hψ.1).mul w.measV).aestronglyMeasurable
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hi).1 h0
  unfold vip
  refine integral_eq_zero_of_ae (hz.mono fun a ha => ?_)
  simp only [Pi.zero_apply] at ha ⊢
  rcases mul_eq_zero.1 ha with h | h
  · rw [mul_self_eq_zero.1 h]; ring
  · rw [h]; ring

/-- `φ` is odd under the slice twist. -/
def OddUnder (g : E → G → G) (φ : (E → G) → ℝ) : Prop := ∀ a, φ (sliceMap g a) = -φ a

/-- `j` transfer steps never connect a twist-odd observable to anything. -/
def StepVanish (g : E → G → G) (j : ℕ) : Prop :=
  ∀ φ χ : (E → G) → ℝ, BM φ → BM χ → OddUnder g φ → vip w φ ((kop w)^[j] χ) = 0

/-- **Descent** (self-adjointness): if `j + 2` steps annihilate the odd sector, so do `j + 1`. -/
theorem stepVanish_descend (g : E → G → G) (j : ℕ) (h : StepVanish w g (j + 2)) : StepVanish w g (j + 1) := by
  intro φ χ hφ hχ hodd
  have hψ := bm_kop_iter w hφ (j + 1)
  have h0 : vip w ((kop w)^[j + 1] φ) ((kop w)^[j + 1] φ) = 0 := by
    rw [← vip_kop_iter w hφ hψ (j + 1), ← Function.iterate_add_apply,
      show j + 1 + (j + 1) = (j + 2) + j by ring, Function.iterate_add_apply]
    exact h φ _ hφ (bm_kop_iter w hφ j) hodd
  rw [vip_kop_iter w hφ hχ]
  exact vip_eq_zero_of_self w hψ h0 χ

theorem stepVanish_one (g : E → G → G) {n : ℕ} (hn : 1 ≤ n) (h : StepVanish w g n) : StepVanish w g 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction k with
  | zero => exact h
  | succ k ih => exact ih (stepVanish_descend w g k h)

end Kernel

/-! ## The half chain is `n` transfer steps -/

section HalfChain

variable {G : Type*} [Group G] [MeasurableSpace G] [HasHaarProbability G] {E S : Type*} [Fintype E] [Fintype S]
  {T : ℕ} [NeZero T]
variable (w : ChainWeight G E S)

theorem measurePreserving_sp (t : ZMod T) :
    MeasurePreserving (fun U : CCfg G E S T => sp U t) (cHaar G E S T) (sliceHaar G E) := by
  unfold cHaar
  exact measurePreserving_restrictInj (haarG G) (fun e : E => ((t, Sum.inl e) : CLink E S T))
    (fun e e' h => by simpa using h)

theorem measurePreserving_tmsp (t t' : ZMod T) :
    MeasurePreserving (fun U : CCfg G E S T => (tm U t, sp U t')) (cHaar G E S T)
      ((sliceHaar G S).prod (sliceHaar G E)) := by
  have h1 := measurePreserving_restrictInj (haarG G) (ι := CLink E S T)
    (Sum.elim (fun s : S => ((t, Sum.inr s) : CLink E S T)) (fun e : E => ((t', Sum.inl e) : CLink E S T)))
    (by rintro (s | e) (s' | e') h <;> simp_all)
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : S ⊕ E => G) (fun _ => haarG G)
  unfold cHaar
  convert h2.comp h1 using 1
  funext U; rfl

/-- The links resampled in one transfer step from slice `t`: temporal links of `t`, spatial links of `t + 1`. -/
def stepP (t : ZMod T) : CLink E S T → Prop
  | (s, .inl _) => s = t + 1
  | (s, .inr _) => s = t

/-- `U` with the step links of `t` taken from `U'`. -/
def stepMix (t : ZMod T) (U U' : CCfg G E S T) : CCfg G E S T := fun l => if stepP t l then U' l else U l

theorem sp_stepMix_ne {t s : ZMod T} (h : s ≠ t + 1) (U U' : CCfg G E S T) : sp (stepMix t U U') s = sp U s := by
  funext e; simp [sp, stepMix, stepP, h]

theorem sp_stepMix_eq (t : ZMod T) (U U' : CCfg G E S T) : sp (stepMix t U U') (t + 1) = sp U' (t + 1) := by
  funext e; simp [sp, stepMix, stepP]

theorem tm_stepMix_ne {t s : ZMod T} (h : s ≠ t) (U U' : CCfg G E S T) : tm (stepMix t U U') s = tm U s := by
  funext e; simp [tm, stepMix, stepP, h]

theorem tm_stepMix_eq (t : ZMod T) (U U' : CCfg G E S T) : tm (stepMix t U U') t = tm U' t := by
  funext e; simp [tm, stepMix, stepP]

/-- **Integrating out one transfer step**: the temporal links of slice `t` and the spatial links of slice `t + 1`
are independent of everything a function `Ψ` of the other links sees. -/
theorem integral_step (t : ZMod T) (ht : t ≠ t + 1) {Ψ : CCfg G E S T → ℝ} (hΨ : BM Ψ)
    (hmix : ∀ U U', Ψ (stepMix t U U') = Ψ U) {F : (E → G) × ((S → G) × (E → G)) → ℝ} (hF : BM F) :
    ∫ U, Ψ U * F (sp U t, (tm U t, sp U (t + 1))) ∂(cHaar G E S T) =
      ∫ U, Ψ U * ∫ q, F (sp U t, q) ∂((sliceHaar G S).prod (sliceHaar G E)) ∂(cHaar G E S T) := by
  have mI : Measurable fun U : CCfg G E S T => Ψ U * F (sp U t, (tm U t, sp U (t + 1))) :=
    hΨ.1.mul (hF.1.comp ((measurable_sp t).prodMk ((measurable_tm t).prodMk (measurable_sp (t + 1)))))
  have iI : Integrable (fun U : CCfg G E S T => Ψ U * F (sp U t, (tm U t, sp U (t + 1)))) (cHaar G E S T) :=
    IsBdd.integrable (hΨ.2.mul (hF.2.comp _)) mI.aestronglyMeasurable
  have hm : ∫ U, Ψ U * F (sp U t, (tm U t, sp U (t + 1))) ∂(cHaar G E S T) =
      ∫ U, ∫ U', (fun V : CCfg G E S T => Ψ V * F (sp V t, (tm V t, sp V (t + 1))))
        (fun l => if stepP t l then U' l else U l) ∂(cHaar G E S T) ∂(cHaar G E S T) :=
    integral_mix (haarG G) (stepP t) iI
  rw [hm]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  have e : ∀ U' : CCfg G E S T, (fun l => if stepP t l then U' l else U l) = stepMix t U U' := fun _ => rfl
  simp only [e, hmix, sp_stepMix_ne ht, tm_stepMix_eq, sp_stepMix_eq]
  rw [integral_const_mul]
  congr 1
  exact integral_comp_of_measurePreserving (measurePreserving_tmsp t (t + 1)) (g := fun q => F (sp U t, q))
    (hF.1.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable

theorem natCast_ne {a b : ℕ} (ha : a < T) (hb : b < T) (h : a ≠ b) : (a : ZMod T) ≠ (b : ZMod T) := by
  intro e
  have := congrArg ZMod.val e
  rw [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at this
  exact h this

/-- The weight of the first `m` steps of the half chain (slices `1, …, m−1` and steps `0, …, m−1`). -/
def cAm (m : ℕ) (U : CCfg G E S T) : ℝ :=
  (∏ k ∈ Ico 1 m, w.V (sp U (k : ZMod T))) *
    ∏ k ∈ range m, w.K (sp U (k : ZMod T)) (tm U (k : ZMod T)) (sp U ((k : ZMod T) + 1))

theorem bm_cAm (m : ℕ) : BM (cAm (T := T) w m) := by
  obtain ⟨MV, hMV⟩ := w.V_bdd
  obtain ⟨MK, hMK⟩ := w.K_bdd
  refine ⟨(Finset.measurable_prod _ fun k _ => w.measV.comp (measurable_sp _)).mul
    (Finset.measurable_prod _ fun k _ =>
      w.measK.comp ((measurable_sp _).prodMk ((measurable_tm _).prodMk (measurable_sp _)))), ?_⟩
  refine IsBdd.mul (IsBdd.prod _ fun k => ⟨MV, fun U => ?_⟩) (IsBdd.prod _ fun k => ⟨MK, fun U => ?_⟩)
  · rw [Real.norm_eq_abs, abs_of_nonneg (w.V_nonneg _)]; exact hMV _
  · rw [Real.norm_eq_abs, abs_of_nonneg (w.K_nonneg _ _ _)]; exact hMK _ _ _

theorem cAm_stepMix {m : ℕ} (hm : m + 1 < T) (U U' : CCfg G E S T) :
    cAm w m (stepMix (m : ZMod T) U U') = cAm w m U := by
  have h1 : ((m : ZMod T) + 1) = ((m + 1 : ℕ) : ZMod T) := by push_cast; ring
  unfold cAm
  congr 1
  · refine prod_congr rfl fun k hk => ?_
    have hk' := (mem_Ico.1 hk).2
    rw [sp_stepMix_ne (by rw [h1]; exact natCast_ne (by omega) hm (by omega))]
  · refine prod_congr rfl fun k hk => ?_
    have hk' := mem_range.1 hk
    have hk1 : ((k : ZMod T) + 1) = ((k + 1 : ℕ) : ZMod T) := by push_cast; ring
    rw [sp_stepMix_ne (by rw [h1]; exact natCast_ne (by omega) hm (by omega)),
      tm_stepMix_ne (natCast_ne (by omega) (by omega) (by omega)),
      sp_stepMix_ne (by rw [h1, hk1]; exact natCast_ne (by omega) hm (by omega))]

/-- **The half chain as iterated transfer steps** (induction over the steps). -/
theorem chain_aux (hT : Even T) {Φ0 : (E → G) → ℝ} (hΦ : BM Φ0) (m : ℕ) (hm : 1 ≤ m) (hmT : m ≤ T / 2) :
    ∀ χ, BM χ → ∫ U, cAm w m U * Φ0 (sp U 0) * (χ (sp U (m : ZMod T)) * w.V (sp U (m : ZMod T)))
        ∂(cHaar G E S T) = ∫ a, Φ0 a * (kop w)^[m] χ a ∂(sliceHaar G E) := by
  have hT2 := two_le_of_even hT
  obtain ⟨MV, hMV⟩ := w.V_bdd
  have bV : IsBdd w.V := ⟨MV, fun a => by rw [Real.norm_of_nonneg (w.V_nonneg a)]; exact hMV a⟩
  obtain ⟨MK, hMK⟩ := w.K_bdd
  have bK : IsBdd fun z : (E → G) × ((S → G) × (E → G)) => w.K z.1 z.2.1 z.2.2 :=
    ⟨MK, fun z => by rw [Real.norm_of_nonneg (w.K_nonneg _ _ _)]; exact hMK _ _ _⟩
  have mK : Measurable fun z : (E → G) × ((S → G) × (E → G)) => w.K z.1 z.2.1 z.2.2 :=
    w.measK.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd))
  -- the step integrand
  have hFb : ∀ χ : (E → G) → ℝ, BM χ →
      BM fun z : (E → G) × ((S → G) × (E → G)) => w.K z.1 z.2.1 z.2.2 * w.V z.2.2 * χ z.2.2 := fun χ hχ =>
    ⟨(mK.mul (w.measV.comp measurable_snd.snd)).mul (hχ.1.comp measurable_snd.snd),
      (bK.mul (bV.comp _)).mul (hχ.2.comp _)⟩
  induction m, hm using Nat.le_induction with
  | base =>
    intro χ hχ
    have h01 : (0 : ZMod T) ≠ 0 + 1 := by rw [zero_add]; exact (one_ne_zero_of_even hT).symm
    have e : ∀ U : CCfg G E S T, cAm w 1 U * Φ0 (sp U 0) * (χ (sp U ((1 : ℕ) : ZMod T)) *
        w.V (sp U ((1 : ℕ) : ZMod T))) = Φ0 (sp U 0) *
        (fun z : (E → G) × ((S → G) × (E → G)) => w.K z.1 z.2.1 z.2.2 * w.V z.2.2 * χ z.2.2)
          (sp U 0, (tm U 0, sp U (0 + 1))) := by
      intro U
      simp only [cAm, Ico_self, prod_empty, range_one, prod_singleton, Nat.cast_zero, Nat.cast_one, zero_add]
      ring
    refine (integral_congr_ae (ae_of_all _ e)).trans ((integral_step 0 h01 (Ψ := fun U => Φ0 (sp U 0))
      ⟨hΦ.1.comp (measurable_sp 0), hΦ.2.comp _⟩ (fun U U' => congrArg Φ0 (sp_stepMix_ne h01 U U'))

      (hFb χ hχ)).trans ?_)
    exact integral_comp_of_measurePreserving (measurePreserving_sp 0) (g := fun a => Φ0 a * kop w χ a)
      (hΦ.1.mul (measurable_kop w hχ.1)).aestronglyMeasurable
  | succ m hm1 ih =>
    intro χ hχ
    have hmT' : m + 1 < T := by omega
    have hne : ((m : ZMod T)) ≠ (m : ZMod T) + 1 := by
      intro h
      have h1 : ((m : ZMod T) + 1) = ((m + 1 : ℕ) : ZMod T) := by push_cast; ring
      rw [h1] at h
      exact natCast_ne (by omega) hmT' (by omega) h
    have h0 : (0 : ZMod T) ≠ (m : ZMod T) + 1 := by
      have h1 : ((m : ZMod T) + 1) = ((m + 1 : ℕ) : ZMod T) := by push_cast; ring
      rw [h1, ← Nat.cast_zero]
      exact natCast_ne (by omega) hmT' (by omega)
    have e : ∀ U : CCfg G E S T, cAm w (m + 1) U * Φ0 (sp U 0) * (χ (sp U ((m + 1 : ℕ) : ZMod T)) *
        w.V (sp U ((m + 1 : ℕ) : ZMod T))) = (cAm w m U * Φ0 (sp U 0) * w.V (sp U (m : ZMod T))) *
        (fun z : (E → G) × ((S → G) × (E → G)) => w.K z.1 z.2.1 z.2.2 * w.V z.2.2 * χ z.2.2)
          (sp U (m : ZMod T), (tm U (m : ZMod T), sp U ((m : ZMod T) + 1))) := by
      intro U
      simp only [cAm]
      rw [prod_Ico_succ_top hm1, prod_range_succ, Nat.cast_succ]
      ring
    refine (integral_congr_ae (ae_of_all _ e)).trans ?_
    have hΨ : BM fun U : CCfg G E S T => cAm w m U * Φ0 (sp U 0) * w.V (sp U (m : ZMod T)) :=
      ⟨((bm_cAm w m).1.mul (hΦ.1.comp (measurable_sp 0))).mul (w.measV.comp (measurable_sp _)),
        ((bm_cAm w m).2.mul (hΦ.2.comp _)).mul (bV.comp _)⟩
    refine (integral_step (m : ZMod T) hne hΨ (fun U U' => by
      rw [cAm_stepMix w hmT', sp_stepMix_ne h0, sp_stepMix_ne hne]) (hFb χ hχ)).trans ?_
    have e2 : ∀ U : CCfg G E S T, cAm w m U * Φ0 (sp U 0) * w.V (sp U (m : ZMod T)) *
        ∫ q, (fun z : (E → G) × ((S → G) × (E → G)) => w.K z.1 z.2.1 z.2.2 * w.V z.2.2 * χ z.2.2)
          (sp U (m : ZMod T), q) ∂((sliceHaar G S).prod (sliceHaar G E)) =
        cAm w m U * Φ0 (sp U 0) * (kop w χ (sp U (m : ZMod T)) * w.V (sp U (m : ZMod T))) := by
      intro U; unfold kop; ring
    refine (integral_congr_ae (ae_of_all _ e2)).trans ?_
    rw [ih (by omega) (kop w χ) (bm_kop w hχ), Function.iterate_succ_apply]

theorem tLow_eq : tLow T = (range (T / 2)).image (fun k : ℕ => (k : ZMod T)) := by
  ext t
  simp only [tLow, mem_filter, mem_univ, true_and, mem_image, mem_range]
  constructor
  · intro h; exact ⟨t.val, h, ZMod.natCast_zmod_val t⟩
  · rintro ⟨k, hk, rfl⟩
    rw [ZMod.val_cast_of_lt (by omega)]; exact hk

theorem tPos_eq : tPos T = (Ico 1 (T / 2)).image (fun k : ℕ => (k : ZMod T)) := by
  ext t
  simp only [tPos, mem_filter, mem_univ, true_and, mem_image, mem_Ico]
  constructor
  · intro h; exact ⟨t.val, ⟨h.1, h.2⟩, ZMod.natCast_zmod_val t⟩
  · rintro ⟨k, hk, rfl⟩
    rw [ZMod.val_cast_of_lt (by omega)]; exact ⟨hk.1, hk.2⟩

theorem tFix_eq : tFix T = {0, halfT T} := by
  ext t
  simp only [tFix, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · rintro (h | h)
    · exact Or.inl ((ZMod.val_eq_zero t).1 h)
    · right
      rw [← ZMod.natCast_zmod_val t, h]; rfl
  · rintro (rfl | rfl)
    · exact Or.inl ZMod.val_zero
    · exact Or.inr val_halfT

theorem cA_eq_cAm (hT : Even T) (U : CCfg G E S T) : cA w U = cAm w (T / 2) U := by
  have hT2 := two_le_of_even hT
  have hinj : ∀ s : Finset ℕ, (∀ k ∈ s, k < T) → Set.InjOn (fun k : ℕ => (k : ZMod T)) s := fun s hs x hx y hy h =>
    by_contra fun hne => natCast_ne (hs x hx) (hs y hy) hne h
  unfold cA cAm
  rw [tPos_eq, tLow_eq, prod_image (hinj _ fun k hk => by have := (mem_Ico.1 hk).2; omega),
    prod_image (hinj _ fun k hk => by have := mem_range.1 hk; omega)]

theorem cB_eq (hT : Even T) (U : CCfg G E S T) : cB w U = w.V (sp U 0) * w.V (sp U (halfT T)) := by
  unfold cB
  rw [tFix_eq, prod_pair (halfT_ne_zero hT).symm]

/-- **The half-chain identity**: for boundary observables `φ(a₀) χ(a_{T/2})`,
`∫ A · φ(a₀) χ(a_{T/2}) · B = ⟨φ, 𝒦^{T/2} χ⟩_V`. -/
theorem half_chain (hT : Even T) {φ χ : (E → G) → ℝ} (hφ : BM φ) (hχ : BM χ) :
    ∫ U, cA w U * bdry (fun p => φ p.1 * χ p.2) U * cB w U ∂(cHaar G E S T) = vip w φ ((kop w)^[T / 2] χ) := by
  have hT2 := two_le_of_even hT
  obtain ⟨MV, hMV⟩ := w.V_bdd
  have bV : IsBdd w.V := ⟨MV, fun a => by rw [Real.norm_of_nonneg (w.V_nonneg a)]; exact hMV a⟩
  have e : ∀ U : CCfg G E S T, cA w U * bdry (fun p => φ p.1 * χ p.2) U * cB w U =
      cAm w (T / 2) U * (fun a => φ a * w.V a) (sp U 0) *
        (χ (sp U ((T / 2 : ℕ) : ZMod T)) * w.V (sp U ((T / 2 : ℕ) : ZMod T))) := by
    intro U
    rw [cA_eq_cAm w hT, cB_eq w hT]
    simp only [bdry, halfT]
    ring
  refine (integral_congr_ae (ae_of_all _ e)).trans
    ((chain_aux w hT (Φ0 := fun a => φ a * w.V a) ⟨hφ.1.mul w.measV, hφ.2.mul bV⟩ (T / 2) (by omega) le_rfl χ
      hχ).trans ?_)
  unfold vip

  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  simp only []; ring

end HalfChain

/-! ## The strict bound from one transfer step (general chain, every even `T`) -/

section Step

variable {G : Type*} [Group G] [MeasurableSpace G] [HasHaarProbability G] [MeasurableInv G]
  [(haarG G).IsInvInvariant] {E S : Type*} [Fintype E] [Fintype S] {T : ℕ} [NeZero T]
variable (w : ChainWeight G E S) (g : E → G → G)

/-- The boundary moment of a product observable `φ(a₀) χ(a_{T/2})` with `φ` odd is `−2 ⟨φ, 𝒦^{T/2} χ⟩_V`. -/
theorem moment_odd (hT : Even T) (hg : ∀ e, MeasurePreserving (g e) (haarG G) (haarG G))
    (hinv : ∀ e, Function.Involutive (g e)) (hV : ∀ a, w.V (sliceMap g a) = w.V a) {φ χ : (E → G) → ℝ}
    (hφ : BM φ) (hχ : BM χ) (hodd : OddUnder g φ) :
    ∫ U, (cA w (flip0 g U) - cA w U) * bdry (fun p => φ p.1 * χ p.2) U * cB w U ∂(cHaar G E S T) =
      -2 * vip w φ ((kop w)^[T / 2] χ) := by
  have mg : ∀ e, Measurable (g e) := fun e => (hg e).measurable
  have hmp := measurePreserving_flip0 (S := S) (T := T) hg
  set Φ : CCfg G E S T → ℝ := fun U => bdry (fun p => φ p.1 * χ p.2) U * cB w U with hΦdef
  have mΦ : Measurable Φ :=
    (measurable_bdry ((hφ.1.comp measurable_fst).mul (hχ.1.comp measurable_snd))).mul (measurable_cB w)
  have bΦ : IsBdd Φ := (((hφ.2.comp _).mul (hχ.2.comp _)).comp _).mul (cB_isBdd w)
  have hΦσ : ∀ U, Φ (flip0 g U) = -Φ U := by
    intro U
    simp only [hΦdef]
    rw [bdry_flip0 hT, cB_flip0 w g hT hV, hodd]
    simp only [bdry]; ring
  have mA := measurable_cA (T := T) w
  have bA := cA_isBdd (T := T) w
  have i1 : Integrable (fun U => cA w (flip0 g U) * Φ U) (cHaar G E S T) :=
    IsBdd.integrable ((bA.comp _).mul bΦ) ((mA.comp (measurable_flip0 mg)).mul mΦ).aestronglyMeasurable
  have i2 : Integrable (fun U => cA w U * Φ U) (cHaar G E S T) :=
    IsBdd.integrable (bA.mul bΦ) (mA.mul mΦ).aestronglyMeasurable
  have e1 : ∫ U, cA w (flip0 g U) * Φ U ∂(cHaar G E S T) = -∫ U, cA w U * Φ U ∂(cHaar G E S T) := by
    have h := integral_comp_of_measurePreserving hmp (g := fun U => cA w U * Φ (flip0 g U))
      (mA.mul (mΦ.comp (measurable_flip0 mg))).aestronglyMeasurable
    simp only [flip0_flip0 hinv] at h
    rw [h, ← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    simp only []; rw [hΦσ]; ring
  have e0 : ∀ U, (cA w (flip0 g U) - cA w U) * bdry (fun p => φ p.1 * χ p.2) U * cB w U =
      cA w (flip0 g U) * Φ U - cA w U * Φ U := fun U => by simp only [hΦdef]; ring
  simp_rw [e0]
  rw [integral_sub i1 i2, e1]
  have h := half_chain w hT hφ hχ
  have e3 : ∫ U, cA w U * Φ U ∂(cHaar G E S T) =
      ∫ U, cA w U * bdry (fun p => φ p.1 * χ p.2) U * cB w U ∂(cHaar G E S T) :=
    integral_congr_ae (ae_of_all _ fun U => by simp only [hΦdef]; ring)
  rw [e3, h]; ring

/-- **The strict reflection bound from one transfer step (general chain, every even `T`).** For every chain weight
with `K > 0`, every slice twist (measure preserving, involutive, `V`-invariant) and every even time extent: if the
one-step transfer operator `𝒦` connects some twist-odd bounded observable `φ` to some bounded `χ`,
`⟨φ, 𝒦 χ⟩_V ≠ 0`, then `Z_tw < Z`. The hypothesis does not involve `T`. Proof: `Z_tw = Z` would make every boundary
moment vanish (`cZtw_lt_cZ_of_moment`), i.e. `𝒦^{T/2}` would annihilate the odd sector (`half_chain`, `moment_odd`),
and by self-adjointness of `𝒦` so would `𝒦` itself (`stepVanish_one`). -/
theorem cZtw_lt_cZ_of_step (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c)
    (hg : ∀ e, MeasurePreserving (g e) (haarG G) (haarG G)) (hinv : ∀ e, Function.Involutive (g e))
    (hV : ∀ a, w.V (sliceMap g a) = w.V a) {φ χ : (E → G) → ℝ} (hφ : BM φ) (hχ : BM χ) (hodd : OddUnder g φ)
    (hne : vip w φ (kop w χ) ≠ 0) : cZtw (T := T) w g < cZ (T := T) w := by
  by_contra hlt
  have hS : StepVanish w g (T / 2) := by
    intro φ' χ' hφ' hχ' hodd'
    by_contra hne'
    apply hlt
    refine cZtw_lt_cZ_of_moment w g hT hK hg hinv hV (η := fun p => φ' p.1 * χ' p.2)
      ((hφ'.1.comp measurable_fst).mul (hχ'.1.comp measurable_snd)) ((hφ'.2.comp _).mul (hχ'.2.comp _)) ?_
    rw [moment_odd w g hT hg hinv hV hφ' hχ' hodd']
    exact mul_ne_zero (by norm_num) hne'
  have h1 := stepVanish_one w g (n := T / 2) (by have := two_le_of_even hT; omega) hS
  exact hne (h1 φ χ hφ hχ hodd)

end Step

/-! ## Compact spaces, single-coordinate resampling -/

section Compact

/-- Continuous functions on a compact space are bounded. -/
theorem isBdd_of_continuous {X F : Type*} [TopologicalSpace X] [CompactSpace X] [NormedAddCommGroup F] {f : X → F}
    (hf : Continuous f) : IsBdd f := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, fun x => hC x (Set.mem_univ x)⟩

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasure μ]

theorem integrable_of_continuous {F : Type*} [NormedAddCommGroup F] [SecondCountableTopology F] {f : X → F}
    (hf : Continuous f) : Integrable f μ :=
  IsBdd.integrable (isBdd_of_continuous hf) hf.aestronglyMeasurable

/-- A continuous nonnegative function that is positive somewhere has positive integral (open sets have positive
measure). -/
theorem integral_pos_of_continuous [μ.IsOpenPosMeasure] {f : X → ℝ} (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x)
    {x0 : X} (hx0 : 0 < f x0) : 0 < ∫ x, f x ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun x => h0 x) (integrable_of_continuous hf)]
  exact lt_of_lt_of_le ((isOpen_lt continuous_const hf).measure_pos μ ⟨x0, hx0⟩)
    (measure_mono fun x hx => Function.mem_support.2 (ne_of_gt hx))

end Compact

section Update

variable {G : Type*} [MeasurableSpace G] (μ : Measure G) [IsProbabilityMeasure μ]

/-- **Resampling one coordinate.** -/
theorem integral_update {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι) {Φ : (ι → G) → ℝ} (mΦ : Measurable Φ)
    (bΦ : IsBdd Φ) :
    ∫ U, Φ U ∂(Measure.pi fun _ : ι => μ) =
      ∫ U, ∫ v, Φ (Function.update U i0 v) ∂μ ∂(Measure.pi fun _ : ι => μ) := by
  rw [integral_mix μ (· = i0) (IsBdd.integrable bΦ mΦ.aestronglyMeasurable)]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  have e : ∀ U' : ι → G, (fun i => if i = i0 then U' i else U i) = Function.update U i0 (U' i0) := by
    intro U'; funext i
    by_cases h : i = i0
    · subst h; simp
    · simp [h]
  simp only [e]
  exact integral_comp_of_measurePreserving (measurePreserving_eval (fun _ : ι => μ) i0)
    (g := fun v => Φ (Function.update U i0 v)) (mΦ.comp (measurable_update U)).aestronglyMeasurable

end Update

/-! ## SU(2): the Schur lemma for the plaquette factor -/

section SchurSU2

instance instOpenPosHaarSU2 : (haarG SU2).IsOpenPosMeasure := by
  show (Measure.haarMeasure ⊤).IsOpenPosMeasure; infer_instance

theorem continuous_tr2 : Continuous (gaugeReTr SU2 2) := continuous_gaugeReTr continuous_subtype_val

theorem tr2_one : gaugeReTr SU2 2 1 = 2 := by simp [gaugeReTr, gaugeTrace]

/-- The plaquette factor `e^{β Re tr u}`. -/
def bw (β : ℝ) (u : SU2) : ℝ := Real.exp (β * gaugeReTr SU2 2 u)

theorem continuous_bw (β : ℝ) : Continuous (bw β) := Real.continuous_exp.comp (continuous_const.mul continuous_tr2)

theorem bw_pos (β : ℝ) (u : SU2) : 0 < bw β u := Real.exp_pos _

theorem bw_conj (β : ℝ) (h v : SU2) : bw β (h * v * h⁻¹) = bw β v := by unfold bw; rw [gaugeReTr_conj]

theorem continuous_entry (i j : Fin 2) : Continuous fun v : SU2 => (v : Matrix (Fin 2) (Fin 2) ℂ) i j :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

theorem continuous_bwEntry (β : ℝ) (i j : Fin 2) :
    Continuous fun v : SU2 => (bw β v : ℂ) * (v : Matrix (Fin 2) (Fin 2) ℂ) i j :=
  (Complex.continuous_ofReal.comp (continuous_bw β)).mul (continuous_entry i j)

/-- The entries of the matrix `∫ e^{β Re tr v} v dv`. -/
def schurN (β : ℝ) (i j : Fin 2) : ℂ := ∫ v, (bw β v : ℂ) * (v : Matrix (Fin 2) (Fin 2) ℂ) i j ∂(haarG SU2)

theorem schurN_conj (β : ℝ) (h : SU2) (i j : Fin 2) :
    ∫ v, (bw β v : ℂ) * ((h * v * h⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) i j ∂(haarG SU2) = schurN β i j := by
  have hmp : MeasurePreserving (fun v : SU2 => h * v * h⁻¹) (haarG SU2) (haarG SU2) :=
    (measurePreserving_mul_right (haarG SU2) h⁻¹).comp (measurePreserving_mul_left (haarG SU2) h)
  have := integral_comp_of_measurePreserving hmp
    (g := fun v : SU2 => (bw β v : ℂ) * (v : Matrix (Fin 2) (Fin 2) ℂ) i j)
    (continuous_bwEntry β i j).aestronglyMeasurable
  unfold schurN
  refine Eq.trans ?_ this
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [bw_conj]

/-- `diag(i, −i) ∈ SU(2)`. -/
def suD : SU2 := ⟨!![Complex.I, 0; 0, -Complex.I], Matrix.mem_specialUnitaryGroup_iff.2
  ⟨Matrix.mem_unitaryGroup_iff.2 (by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two]),
   by simp [Matrix.det_fin_two]⟩⟩

/-- `[[0, 1], [−1, 0]] ∈ SU(2)`. -/
def suJ : SU2 := ⟨!![0, 1; -1, 0], Matrix.mem_specialUnitaryGroup_iff.2
  ⟨Matrix.mem_unitaryGroup_iff.2 (by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two]),
   by simp [Matrix.det_fin_two]⟩⟩

theorem suD_conj_01 (v : SU2) :
    ((suD * v * suD⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = -(v : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by
  show ((suD : Matrix (Fin 2) (Fin 2) ℂ) * v * star (suD : Matrix (Fin 2) (Fin 2) ℂ)) 0 1 = _
  simp [suD, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.vecMul, dotProduct]
  ring_nf; simp [Complex.I_sq]

theorem suD_conj_10 (v : SU2) :
    ((suD * v * suD⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = -(v : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
  show ((suD : Matrix (Fin 2) (Fin 2) ℂ) * v * star (suD : Matrix (Fin 2) (Fin 2) ℂ)) 1 0 = _
  simp [suD, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.vecMul, dotProduct]
  ring_nf; simp [Complex.I_sq]

theorem suJ_conj_00 (v : SU2) :
    ((suJ * v * suJ⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = (v : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
  show ((suJ : Matrix (Fin 2) (Fin 2) ℂ) * v * star (suJ : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 = _
  simp [suJ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.vecMul, dotProduct]

theorem schurN_01 (β : ℝ) : schurN β 0 1 = 0 := by
  have h := schurN_conj β suD 0 1
  simp_rw [suD_conj_01, mul_neg, integral_neg] at h
  change -schurN β 0 1 = schurN β 0 1 at h
  linear_combination (-1 / 2 : ℂ) * h

theorem schurN_10 (β : ℝ) : schurN β 1 0 = 0 := by
  have h := schurN_conj β suD 1 0
  simp_rw [suD_conj_10, mul_neg, integral_neg] at h
  change -schurN β 1 0 = schurN β 1 0 at h
  linear_combination (-1 / 2 : ℂ) * h

theorem schurN_11 (β : ℝ) : schurN β 1 1 = schurN β 0 0 := by
  have h := schurN_conj β suJ 0 0
  simp_rw [suJ_conj_00] at h
  exact h

/-- In SU(2) the lower-right entry is the conjugate of the upper-left one. -/
theorem su2_entry11 (M : SU2) :
    (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = star ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
  have h := Matrix.mem_specialUnitaryGroup_iff.1 M.2
  have hu : (M : Matrix (Fin 2) (Fin 2) ℂ) * star (M : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 h.1
  have hinv : (M : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = star (M : Matrix (Fin 2) (Fin 2) ℂ) := Matrix.inv_eq_right_inv hu
  have hadj : (M : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = Matrix.adjugate (M : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Matrix.inv_def, h.2, Ring.inverse_one, one_smul]
  have := congrFun (congrFun (hinv.symm.trans hadj) 0) 0
  rw [Matrix.adjugate_fin_two] at this
  simpa [Matrix.star_apply] using this.symm

/-- The trace of an SU(2) matrix is real. -/
theorem su2_trace_im (M : SU2) : (Matrix.trace (M : Matrix (Fin 2) (Fin 2) ℂ)).im = 0 := by
  rw [Matrix.trace_fin_two, su2_entry11]
  simp

theorem integral_bw_tr_mul (β : ℝ) (M : SU2) :
    ∫ v, bw β v * gaugeReTr SU2 2 (v * M) ∂(haarG SU2) =
      (schurN β 0 0 * Matrix.trace (M : Matrix (Fin 2) (Fin 2) ℂ)).re := by
  set m := (M : Matrix (Fin 2) (Fin 2) ℂ) with hm
  let t : Fin 2 → Fin 2 → SU2 → ℂ := fun i j v => (bw β v : ℂ) * (v : Matrix (Fin 2) (Fin 2) ℂ) i j * m j i
  have ct : ∀ i j, Continuous (t i j) := fun i j => (continuous_bwEntry β i j).mul continuous_const
  have it : ∀ i j, Integrable (t i j) (haarG SU2) := fun i j => integrable_of_continuous (ct i j)
  have e : ∀ v : SU2, bw β v * gaugeReTr SU2 2 (v * M) =
      Complex.reCLM (t 0 0 v + t 0 1 v + (t 1 0 v + t 1 1 v)) := by
    intro v
    show bw β v * (Matrix.trace ((v : Matrix (Fin 2) (Fin 2) ℂ) * m)).re = _
    rw [Complex.reCLM_apply, Matrix.trace_fin_two]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, t]
    rw [← Complex.re_ofReal_mul]
    congr 1; ring
  simp_rw [e]
  have i01 : Integrable (fun v => t 0 0 v + t 0 1 v) (haarG SU2) := (it 0 0).add (it 0 1)
  have i23 : Integrable (fun v => t 1 0 v + t 1 1 v) (haarG SU2) := (it 1 0).add (it 1 1)
  have iall : Integrable (fun v => t 0 0 v + t 0 1 v + (t 1 0 v + t 1 1 v)) (haarG SU2) := i01.add i23
  rw [ContinuousLinearMap.integral_comp_comm Complex.reCLM iall, integral_add i01 i23, integral_add (it 0 0) (it 0 1),
    integral_add (it 1 0) (it 1 1)]
  have hi : ∀ i j, ∫ v, t i j v ∂(haarG SU2) = schurN β i j * m j i := fun i j => integral_mul_const _ _
  rw [hi, hi, hi, hi, schurN_01, schurN_10, schurN_11, Complex.reCLM_apply, Matrix.trace_fin_two]
  congr 1; ring

/-- **The Schur constant** `λ(β) = Re ∫ e^{β Re tr v} v₀₀ dv = ½ ∫ e^{β Re tr v} Re tr v dv`. -/
def schurC (β : ℝ) : ℝ := (schurN β 0 0).re

/-- **Schur's lemma for the plaquette factor**: `∫ e^{β Re tr v} Re tr(v M) dv = λ(β) Re tr M` on SU(2). -/
theorem schur_SU2 (β : ℝ) (M : SU2) :
    ∫ v, bw β v * gaugeReTr SU2 2 (v * M) ∂(haarG SU2) = schurC β * gaugeReTr SU2 2 M := by
  rw [integral_bw_tr_mul, Complex.mul_re, su2_trace_im, mul_zero, sub_zero]
  rfl

theorem integral_tr2_eq_zero : ∫ v, gaugeReTr SU2 2 v ∂(haarG SU2) = 0 := by
  have h := integral_comp_of_measurePreserving (measurePreserving_mul_left (haarG SU2) negOneSU2)
    (g := gaugeReTr SU2 2) continuous_tr2.aestronglyMeasurable
  simp only [gaugeReTr_mul_central (G := SU2) (n := 2) (z := negOneSU2) rfl, integral_neg] at h
  linarith

theorem exp_lt_one_of_neg' {x : ℝ} (hx : x < 0) : Real.exp x < 1 := by
  have := Real.exp_lt_exp.2 hx
  rwa [Real.exp_zero] at this

theorem expsub_mul_nonneg (x : ℝ) : 0 ≤ (Real.exp x - 1) * x := by
  rcases le_or_gt 0 x with hx | hx
  · exact mul_nonneg (by linarith [Real.add_one_le_exp x]) hx
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith [exp_lt_one_of_neg' hx]) hx.le

theorem expsub_mul_pos {x : ℝ} (hx : x ≠ 0) : 0 < (Real.exp x - 1) * x := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · exact mul_pos_of_neg_of_neg (by linarith [exp_lt_one_of_neg' hx]) hx
  · exact mul_pos (by linarith [Real.add_one_le_exp x]) hx

/-- **`λ(β) ≠ 0` for `β ≠ 0`** (`β λ(β) > 0`). -/
theorem schurC_ne_zero {β : ℝ} (hβ : β ≠ 0) : schurC β ≠ 0 := by
  have h1 : ∫ v, bw β v * gaugeReTr SU2 2 v ∂(haarG SU2) = 2 * schurC β := by
    have := integral_bw_tr_mul β 1
    simp only [mul_one, OneMemClass.coe_one, Matrix.trace_one, Fintype.card_fin] at this
    rw [this, schurC]
    simp [Complex.mul_re]; ring
  have hc : Continuous fun v : SU2 => (Real.exp (β * gaugeReTr SU2 2 v) - 1) * (β * gaugeReTr SU2 2 v) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_tr2)).sub continuous_const).mul
      (continuous_const.mul continuous_tr2)
  have h2 := integral_pos_of_continuous (μ := haarG SU2) hc (fun v => expsub_mul_nonneg _) (x0 := 1)
    (expsub_mul_pos (by rw [tr2_one]; exact mul_ne_zero hβ two_ne_zero))
  have h3 : ∫ v, (Real.exp (β * gaugeReTr SU2 2 v) - 1) * (β * gaugeReTr SU2 2 v) ∂(haarG SU2) =
      β * ∫ v, bw β v * gaugeReTr SU2 2 v ∂(haarG SU2) - β * ∫ v, gaugeReTr SU2 2 v ∂(haarG SU2) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (f := fun v => β * (bw β v * gaugeReTr SU2 2 v))
      (g := fun v => β * gaugeReTr SU2 2 v)
      (integrable_of_continuous ((continuous_const.mul ((continuous_bw β).mul continuous_tr2))))
      (integrable_of_continuous (continuous_const.mul continuous_tr2))]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [bw]; ring
  rw [h3, integral_tr2_eq_zero, h1] at h2
  intro h0
  rw [h0] at h2
  simp at h2

end SchurSU2

/-! ## SU(2): integrating a Wilson line against independent plaquette factors -/

section LineInt

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **Line integral.** Integrating out the links of a (duplicate-free) list `ls` against independent plaquette
factors `e^{β Re tr u_e}` turns `Re tr(X · ∏ u_e a_e)` into `λ(β)^{|ls|} Re tr(X · ∏ a_e)`. -/
theorem lineInt (β : ℝ) (a : E → SU2) (ls : List E) :
    ∀ (s : Finset E) (X : SU2), ls.Nodup → (∀ e ∈ ls, e ∈ s) →
      ∫ u, (∏ e ∈ s, bw β (u e)) * gaugeReTr SU2 2 (X * (ls.map fun e => u e * a e).prod) ∂(sliceHaar SU2 E) =
        schurC β ^ ls.length * (∫ u, ∏ e ∈ s \ ls.toFinset, bw β (u e) ∂(sliceHaar SU2 E)) *
          gaugeReTr SU2 2 (X * (ls.map a).prod) := by
  induction ls with
  | nil =>
    intro s X _ _
    simp only [List.map_nil, List.prod_nil, mul_one, List.length_nil, pow_zero, one_mul, List.toFinset_nil,
      Finset.sdiff_empty]
    exact integral_mul_const _ _
  | cons e ls ih =>
    intro s X hnd hs
    obtain ⟨he_ls, hnd'⟩ := List.nodup_cons.1 hnd
    have hes : e ∈ s := hs e List.mem_cons_self
    have hs' : ∀ e' ∈ ls, e' ∈ s.erase e := fun e' he' =>
      Finset.mem_erase.2 ⟨fun h : e' = e => he_ls (h ▸ he'), hs e' (List.mem_cons_of_mem _ he')⟩
    have hcont : Continuous fun u : E → SU2 =>
        (∏ e' ∈ s, bw β (u e')) * gaugeReTr SU2 2 (X * ((e :: ls).map fun e' => u e' * a e').prod) :=
      (continuous_finsetProd _ fun e' _ => (continuous_bw β).comp (continuous_apply e')).mul
        (continuous_tr2.comp (continuous_const.mul
          (continuous_list_prod _ fun e' _ => (continuous_apply e').mul continuous_const)))
    rw [integral_update (haarG SU2) e hcont.measurable (isBdd_of_continuous hcont)]
    set Q : (E → SU2) → SU2 := fun u => (ls.map fun e' => u e' * a e').prod with hQ
    set R : (E → SU2) → ℝ := fun u => ∏ e' ∈ s.erase e, bw β (u e') with hR
    have pt : ∀ (u : E → SU2) (v : SU2),
        (∏ e' ∈ s, bw β (Function.update u e v e')) *
          gaugeReTr SU2 2 (X * ((e :: ls).map fun e' => Function.update u e v e' * a e').prod) =
        R u * (bw β v * gaugeReTr SU2 2 (v * (a e * Q u * X))) := by
      intro u v
      rw [← Finset.mul_prod_erase s _ hes, Function.update_self]
      have hpr : ∏ e' ∈ s.erase e, bw β (Function.update u e v e') = R u :=
        prod_congr rfl fun e' he' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase he')]
      have hls : (ls.map fun e' => Function.update u e v e' * a e') = ls.map fun e' => u e' * a e' :=
        List.map_congr_left fun e' he' => by
          rw [Function.update_of_ne (fun h : e' = e => he_ls (h ▸ he'))]
      rw [hpr, List.map_cons, List.prod_cons, hls, Function.update_self]
      have hc : X * (v * a e * Q u) = X * (v * (a e * Q u * X)) * X⁻¹ := by group
      rw [hc, gaugeReTr_conj]
      ring
    have inner : ∀ u : E → SU2,
        ∫ v, (∏ e' ∈ s, bw β (Function.update u e v e')) *
          gaugeReTr SU2 2 (X * ((e :: ls).map fun e' => Function.update u e v e' * a e').prod) ∂(haarG SU2) =
        schurC β * (R u * gaugeReTr SU2 2 ((X * a e) * Q u)) := by
      intro u
      simp_rw [pt u]
      rw [integral_const_mul, schur_SU2]
      have hc : X * a e * Q u = X * (a e * Q u * X) * X⁻¹ := by group
      rw [hc, gaugeReTr_conj]
      ring
    simp_rw [inner]
    rw [integral_const_mul, ih (s.erase e) (X * a e) hnd' hs']
    have hset : s.erase e \ ls.toFinset = s \ (e :: ls).toFinset := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_erase, List.mem_toFinset, List.mem_cons]
      tauto
    rw [hset, List.length_cons, pow_succ, List.map_cons, List.prod_cons, mul_assoc X]
    ring

end LineInt

/-! ## SU(2) Wilson chain: the Polyakov line connects the odd sector in one step -/

section WilsonSU2

variable (L : ℕ) [NeZero L]

/-- The SU(2) Wilson chain weight on `ℤ/Tℤ × (ℤ/Lℤ)³` (coupling `β`, spatial twist `P`). -/
abbrev su2W (β : ℝ) (P : Finset (LatticePlaquette 3 L)) :
    ChainWeight SU2 (LatticeLink 3 L) (FinLatticeSites 3 L) :=
  wilsonChain (G := SU2) (n := 2) L continuous_subtype_val (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) β P

/-- The links of the Wilson line through the origin along the first spatial axis. -/
def lineLinks : List (LatticeLink 3 L) := (List.range L).map fun k => ⟨lineSite L 0 k, 0⟩

/-- **The Polyakov line** `Re tr P(a)` through the origin, winding once around the first spatial axis. -/
def polyObs (a : GaugeConnection SU2 3 L) : ℝ := gaugeReTr SU2 2 (polyLine L a 0)

theorem polyLine_eq (a : GaugeConnection SU2 3 L) : polyLine L a 0 = ((lineLinks L).map a).prod := by
  unfold polyLine lineLinks; rw [List.map_map]; rfl

theorem lineLinks_nodup : (lineLinks L).Nodup := by
  refine List.Nodup.map_on (fun x hx y hy h => ?_) List.nodup_range
  have h1 := congrArg (fun l : LatticeLink 3 L => l.site 0) h
  simp only [lineSite, Function.update_self] at h1
  have := congrArg ZMod.val h1
  rwa [ZMod.val_cast_of_lt (List.mem_range.1 hx), ZMod.val_cast_of_lt (List.mem_range.1 hy)] at this

theorem line_target (y : FinLatticeSites 3 L) (k : ℕ) :
    (⟨lineSite L y k, 0⟩ : LatticeLink 3 L).target = lineSite L y (k + 1) := by
  funext i
  by_cases hi : i = 0
  · subst hi; simp [LatticeLink.target, siteShift, lineSite]
  · simp [LatticeLink.target, siteShift, lineSite, hi]

theorem lineSite_L (y : FinLatticeSites 3 L) : lineSite L y L = lineSite L y 0 := by simp [lineSite]

theorem prod_telescope {H : Type*} [Group H] (B X : ℕ → H) (n : ℕ) :
    ((List.range n).map fun k => (B k)⁻¹ * X k * B (k + 1)).prod = (B 0)⁻¹ * ((List.range n).map X).prod * B n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.prod_append, List.prod_append, ih]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    group

theorem continuous_polyObs : Continuous (polyObs L) := by
  unfold polyObs polyLine
  exact continuous_tr2.comp (continuous_list_prod _ fun k _ => continuous_apply _)

/-- The gauge change that absorbs the temporal links of one step. -/
def gaugeSub (a : GaugeConnection SU2 3 L) (b : FinLatticeSites 3 L → SU2) (u : GaugeConnection SU2 3 L) :
    GaugeConnection SU2 3 L :=
  fun e => (b e.site)⁻¹ * u e * (a e * b e.target)

theorem measurePreserving_gaugeSub (a : GaugeConnection SU2 3 L) (b : FinLatticeSites 3 L → SU2) :
    MeasurePreserving (gaugeSub L a b) (sliceHaar SU2 (LatticeLink 3 L)) (sliceHaar SU2 (LatticeLink 3 L)) :=
  measurePreserving_pi (fun _ => haarG SU2) (fun _ => haarG SU2) (fun e =>
    (measurePreserving_mul_right (haarG SU2) (a e * b e.target)).comp
      (measurePreserving_mul_left (haarG SU2) (b e.site)⁻¹))

theorem stepK_gaugeSub (β : ℝ) (a : GaugeConnection SU2 3 L) (b : FinLatticeSites 3 L → SU2)
    (u : GaugeConnection SU2 3 L) : stepK L 2 β a b (gaugeSub L a b u) = ∏ e, bw β (u e) := by
  unfold stepK
  refine prod_congr rfl fun e _ => ?_
  unfold bw tempHol gaugeSub
  congr 3
  group

theorem polyObs_gaugeSub (a : GaugeConnection SU2 3 L) (b : FinLatticeSites 3 L → SU2)
    (u : GaugeConnection SU2 3 L) :
    polyObs L (gaugeSub L a b u) = gaugeReTr SU2 2 (1 * ((lineLinks L).map fun e => u e * a e).prod) := by
  unfold polyObs
  rw [polyLine_eq, one_mul]
  have e1 : (lineLinks L).map (gaugeSub L a b u) = (List.range L).map fun k =>
      (b (lineSite L 0 k))⁻¹ * (u ⟨lineSite L 0 k, 0⟩ * a ⟨lineSite L 0 k, 0⟩) * b (lineSite L 0 (k + 1)) := by
    unfold lineLinks
    rw [List.map_map]
    refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp, gaugeSub, line_target]
    group
  rw [e1, prod_telescope, lineSite_L]
  have e2 : ((List.range L).map fun k => u ⟨lineSite L 0 k, 0⟩ * a ⟨lineSite L 0 k, 0⟩) =
      (lineLinks L).map fun e => u e * a e := by
    unfold lineLinks; rw [List.map_map]; rfl
  rw [e2]
  have := gaugeReTr_conj (G := SU2) (n := 2) (b (lineSite L 0 0))⁻¹ (((lineLinks L).map fun e => u e * a e).prod)
  rwa [inv_inv] at this

theorem continuous_stepK (β : ℝ) :
    Continuous fun z : GaugeConnection SU2 3 L × (FinLatticeSites 3 L → SU2) × GaugeConnection SU2 3 L =>
      stepK L 2 β z.1 z.2.1 z.2.2 := by
  unfold stepK tempHol
  refine continuous_finsetProd _ fun e _ => Real.continuous_exp.comp (continuous_const.mul
    (continuous_tr2.comp ?_))
  fun_prop

/-- The product of the plaquette factors off the line. -/
def lineConst (β : ℝ) : ℝ :=
  ∫ u, ∏ e ∈ univ \ (lineLinks L).toFinset, bw β (u e) ∂(sliceHaar SU2 (LatticeLink 3 L))

theorem lineConst_pos (β : ℝ) : 0 < lineConst L β :=
  integral_pos_of_continuous (continuous_finsetProd _ fun e _ => (continuous_bw β).comp (continuous_apply e))
    (fun _ => (prod_pos fun _ _ => bw_pos β _).le) (x0 := 1) (prod_pos fun _ _ => bw_pos β _)

/-- **One transfer step of the Polyakov line**: `∫ K(a, b, c) Re tr P(c) dc = λ(β)^L κ Re tr P(a)` for every `a`, `b`. -/
theorem stepK_polyObs (β : ℝ) (a : GaugeConnection SU2 3 L) (b : FinLatticeSites 3 L → SU2) :
    ∫ c, stepK L 2 β a b c * polyObs L c ∂(sliceHaar SU2 (LatticeLink 3 L)) =
      schurC β ^ L * lineConst L β * polyObs L a := by
  have hc : Continuous fun c => stepK L 2 β a b c * polyObs L c :=
    ((continuous_stepK L β).comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))).mul
      (continuous_polyObs L)
  refine (integral_comp_of_measurePreserving (measurePreserving_gaugeSub L a b)
    (g := fun c => stepK L 2 β a b c * polyObs L c) hc.aestronglyMeasurable).symm.trans ?_
  simp only [stepK_gaugeSub, polyObs_gaugeSub]
  rw [lineInt β a (lineLinks L) univ 1 (lineLinks_nodup L) (fun e _ => mem_univ e)]
  unfold lineConst polyObs
  rw [polyLine_eq, one_mul, lineLinks, List.length_map, List.length_range]

/-- The odd observable `Re tr P / V` (the slice weight divided out). -/
def polyRatio (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (a : GaugeConnection SU2 3 L) : ℝ :=
  polyObs L a / sliceV L 2 β P a

theorem sliceV_pos (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (a : GaugeConnection SU2 3 L) :
    0 < sliceV L 2 β P a := prod_pos fun _ _ => Real.exp_pos _

theorem continuous_sliceV (β : ℝ) (P : Finset (LatticePlaquette 3 L)) : Continuous (sliceV (G := SU2) L 2 β P) := by
  unfold sliceV xp
  refine continuous_finsetProd _ fun p _ => Real.continuous_exp.comp (continuous_const.mul
    (continuous_tr2.comp ?_))
  show Continuous fun U : GaugeConnection SU2 3 L => U (p.boundaryLinks 0) * U (p.boundaryLinks 1) *
    (U (p.boundaryLinks 2))⁻¹ * (U (p.boundaryLinks 3))⁻¹
  fun_prop

theorem continuous_polyRatio (β : ℝ) (P : Finset (LatticePlaquette 3 L)) : Continuous (polyRatio L β P) :=
  (continuous_polyObs L).div (continuous_sliceV L β P) fun a => (sliceV_pos L β P a).ne'

theorem bm_polyRatio (β : ℝ) (P : Finset (LatticePlaquette 3 L)) : BM (polyRatio L β P) :=
  ⟨(continuous_polyRatio L β P).measurable, isBdd_of_continuous (continuous_polyRatio L β P)⟩

theorem oddUnder_polyRatio (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) :
    OddUnder (flipG L negOneSU2 c) (polyRatio L β P) := by
  intro a
  unfold polyRatio polyObs
  rw [sliceMap_flipG, polyLine_flip L negOneSU2_central, gaugeReTr_mul_central (G := SU2) (n := 2) (z := negOneSU2) rfl,
    sliceV_flip L negOneSU2_central]
  ring

theorem kop_polyRatio (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (a : GaugeConnection SU2 3 L) :
    kop (su2W L β P) (polyRatio L β P) a = schurC β ^ L * lineConst L β * polyObs L a := by
  unfold kop
  have e : ∀ q : (FinLatticeSites 3 L → SU2) × GaugeConnection SU2 3 L,
      (su2W L β P).K a q.1 q.2 * (su2W L β P).V q.2 * polyRatio L β P q.2 =
        stepK L 2 β a q.1 q.2 * polyObs L q.2 := by
    intro q
    show stepK L 2 β a q.1 q.2 * sliceV L 2 β P q.2 * (polyObs L q.2 / sliceV L 2 β P q.2) = _
    field_simp [(sliceV_pos L β P q.2).ne']
    try ring
  simp_rw [e]
  have hc : Continuous fun q : (FinLatticeSites 3 L → SU2) × GaugeConnection SU2 3 L =>
      stepK L 2 β a q.1 q.2 * polyObs L q.2 :=
    ((continuous_stepK L β).comp (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))).mul
      ((continuous_polyObs L).comp continuous_snd)
  rw [integral_prod _ (integrable_of_continuous hc)]
  simp only [stepK_polyObs]
  simp

/-- **The one-step non-degeneracy for SU(2)**, every `β ≠ 0`, every `L ≥ 1`, every spatial twist `P`:
`⟨Re tr P / V, 𝒦 (Re tr P / V)⟩_V = λ(β)^L κ ∫ (Re tr P)² ≠ 0`. -/
theorem su2_vip_polyRatio {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L)) :
    vip (su2W L β P) (polyRatio L β P) (kop (su2W L β P) (polyRatio L β P)) ≠ 0 := by
  have e : vip (su2W L β P) (polyRatio L β P) (kop (su2W L β P) (polyRatio L β P)) =
      schurC β ^ L * lineConst L β * ∫ a, polyObs L a ^ 2 ∂(sliceHaar SU2 (LatticeLink 3 L)) := by
    unfold vip
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    show polyRatio L β P a * kop (su2W L β P) (polyRatio L β P) a * sliceV L 2 β P a =
      schurC β ^ L * lineConst L β * polyObs L a ^ 2
    rw [kop_polyRatio]
    unfold polyRatio
    field_simp [(sliceV_pos L β P a).ne']
    try ring

  rw [e]
  have hsq : 0 < ∫ a, polyObs L a ^ 2 ∂(sliceHaar SU2 (LatticeLink 3 L)) := by
    refine integral_pos_of_continuous ((continuous_polyObs L).pow 2) (fun a => sq_nonneg _) (x0 := 1) ?_
    have h1 : polyObs L 1 = 2 := by
      unfold polyObs polyLine
      simp [tr2_one]
    rw [h1]; norm_num
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (schurC_ne_zero hβ)) (lineConst_pos L β).ne') hsq.ne'

end WilsonSU2

/-! ## The SU(2) headline -/

/-- **The strict reflection bound for SU(2): `Z_tw < Z`** for every `β ≠ 0`, every `L ≥ 1`, every even `T`, every
spatial background twist `P`, every plane position `c`. -/
theorem su2_Ztw_lt_Z (L : ℕ) [NeZero L] {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L)
    {T : ℕ} [NeZero T] (hT : Even T) : su2Ztw L β P c T < su2Z L β P T := by
  refine cZtw_lt_cZ_of_step (su2W L β P) (flipG L negOneSU2 c) hT (fun a b c => stepK_pos L β a b c)
    (fun e => ?_) (fun e => ?_) (fun a => ?_) (bm_polyRatio L β P) (bm_polyRatio L β P)
    (oddUnder_polyRatio L β P c) (su2_vip_polyRatio L hβ P)
  · unfold flipG; split_ifs
    · exact measurePreserving_mul_left (haarG SU2) negOneSU2
    · exact MeasurePreserving.id _
  · unfold flipG; split_ifs
    · intro x; simp only [← mul_assoc, negOneSU2_mul_self, one_mul]
    · exact fun x => rfl
  · show sliceV L 2 β P (sliceMap (flipG L negOneSU2 c) a) = sliceV L 2 β P a
    rw [sliceMap_flipG, sliceV_flip L negOneSU2_central]

/-- **The electric-flux partition function is strictly positive**: `Z − Z_tw = 2 Z_{e=1} > 0` (SU(2), `β ≠ 0`). -/
theorem su2_Ze1_pos (L : ℕ) [NeZero L] {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L)
    {T : ℕ} [NeZero T] (hT : Even T) : 0 < su2Z L β P T - su2Ztw L β P c T :=
  sub_pos.2 (su2_Ztw_lt_Z L hβ P c hT)

/-- **`0 ≤ p < ½`** on the real SU(2) Wilson measure for every `β ≠ 0` (every `L`, `P`, `c`; `T` even). -/
theorem su2_flipProb_lt_half (L : ℕ) [NeZero L] {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L))
    (c : ZMod L) {T : ℕ} [NeZero T] (hT : Even T) :
    0 ≤ su2FlipProb L β P c T ∧ su2FlipProb L β P c T < 1 / 2 := by
  have h1 := su2_Ztw_lt_Z L hβ P c hT
  have h0 := su2Ztw_nonneg L β P c T
  unfold su2FlipProb
  have hpos : 0 < su2Ztw L β P c T + su2Z L β P T := by linarith
  refine ⟨div_nonneg h0 hpos.le, ?_⟩
  rw [div_lt_iff₀ hpos]; linarith

end ProofPhase.Flip
