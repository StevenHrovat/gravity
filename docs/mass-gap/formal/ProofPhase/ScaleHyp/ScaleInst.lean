/-
Proof phase, ScaleHyp kit, module 5: `ScaleHyp` for a scale kernel given by explicit box densities (2026-11-23).
Released under Apache 2.0.

Pack: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/PACK-SCALEHYP.md`, section 4 (`UVTVScaleInst`) and section 7.
Note: `docs/mass-gap/weak-coupling/proof-phase/scalehyp/NOTE.md`.
-/

import ProofPhase.ScaleHyp.BoxLaw
import ProofPhase.ScaleHyp.Counting
import ProofPhase.M1.UVTVInfluence

/-!
# `ScaleHyp` from box densities

`BoxDensities`: one scale's two laws `μ = F Λ₀`, `μ' = F' Λ₀'` (the scale-`j` kernel given a pattern pair, in the two
copies), the blocks `B b`, the good blocks, and per block the block references `Λ b`, `Λ' b` along which `Λ₀`, `Λ₀'`
split (`IsSplit`, pitfall 3). On good blocks the two copies have the same block reference (`UV-TV.md` 39.4: "the
same in both copies on good and composite blocks, where the coarse data agree").

* `BoxDensities.Q`: the block couplings. On a good block, the maximal coupling of the two conditional densities
  (module 2), glued to the two boundary configurations. On a source block, the independent (product) coupling of the
  two box laws (`UV-TV.md` 38.5 (3): "source blocks take the product kernel").
* `BoxDensities.spec`: the `CouplingSpec` (all of (S) and (C) proved), given supports `Ω₀`, `Ω₀'` that are measurable,
  of full measure and kept by the box laws (for instance `Ω₀ = Ω₀' = univ`).
* `BoxDensities.Q_differOn_le`: on a good block, if the conditional densities satisfy the density-ratio bound
  `e^{-δ} ρ_σ ≤ ρ'_{σ'}` with `δ = Σ_{z ∉ B, σ_z ≠ σ'_z} c b z`, then the block coupling leaves some site of the block
  disagreeing with probability at most `δ`. This is `hunion`.
* `BoxDensities.scaleHyp`: **`ScaleHyp μ μ' β`**, through `ScaleHyp.ofBlockBounds`, with the named hypotheses:
  * `hratio`, **the density-ratio constants** (Balaban; paper): H3's analyticity bound for good boxes, Lemma C's
    collar decay for composite boxes (`UV-TV.md` 29.2-29.5);
  * `hsmall` and `hcount`: smallness and counting (module 4 proves `hcount` on the torus).
* `BoxDensities.scaleHyp_torus`: the same on the torus `(ZMod N)^d` with the translates of the side-`ℓ` box, the
  lattice distance, `γ = ε (2R + 1)^d ℓ_K e^{λ (R + d ℓ)}` with `ℓ_K = |K|`; the only analytic inputs are `hratio`, the
  bound `c ≤ ε` and the range `R` of `c`.

What is not here (paper, by design): the identification of the real scale-`j` kernel with `F Λ₀` and its box
conditional densities (`UV-TV.md` 29.1, 33.4), and the constants in `hratio`.
-/

open MeasureTheory ProbabilityTheory Function ProofPhase.OneBox ProofPhase.M1.UVTV

open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.ScaleHypKit

variable {ι S β : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] [Fintype β] [DecidableEq β]

/-- **One scale's box densities** in the two copies. -/
structure BoxDensities (ι S β : Type*) [Fintype ι] [DecidableEq ι] [MeasurableSpace S] [Fintype β] where
  Λ₀ : Measure (ι → S)
  Λ₀' : Measure (ι → S)
  F : (ι → S) → ℝ≥0∞
  F' : (ι → S) → ℝ≥0∞
  B : β → Finset ι
  Λ : β → Measure (ι → S)
  Λ' : β → Measure (ι → S)
  good : Finset β
  sfinite₀ : SFinite Λ₀
  sfinite₀' : SFinite Λ₀'
  prob : ∀ b, IsProbabilityMeasure (Λ b)
  prob' : ∀ b, IsProbabilityMeasure (Λ' b)
  hF : Measurable F
  hF' : Measurable F'
  F_one : ∫⁻ σ, F σ ∂Λ₀ = 1
  F'_one : ∫⁻ σ, F' σ ∂Λ₀' = 1
  split : ∀ b, IsSplit (Λ b) Λ₀ (B b)
  split' : ∀ b, IsSplit (Λ' b) Λ₀' (B b)
  same : ∀ b ∈ good, Λ' b = Λ b

namespace BoxDensities

variable (D : BoxDensities ι S β)

instance : SFinite D.Λ₀ := D.sfinite₀
instance : SFinite D.Λ₀' := D.sfinite₀'
instance (b : β) : IsProbabilityMeasure (D.Λ b) := D.prob b
instance (b : β) : IsProbabilityMeasure (D.Λ' b) := D.prob' b

/-- The first law, `μ = F Λ₀`. -/
def μ : Measure (ι → S) := D.Λ₀.withDensity D.F

/-- The second law, `μ' = F' Λ₀'`. -/
def μ' : Measure (ι → S) := D.Λ₀'.withDensity D.F'

/-- The box laws of the first copy. -/
def q (b : β) : Kernel (ι → S) (ι → S) := boxLaw (D.Λ b) D.F (D.B b)

/-- The box laws of the second copy. -/
def q' (b : β) : Kernel (ι → S) (ι → S) := boxLaw (D.Λ' b) D.F' (D.B b)

instance (b : β) : IsMarkovKernel (D.q b) := isMarkovKernel_boxLaw D.hF
instance (b : β) : IsMarkovKernel (D.q' b) := isMarkovKernel_boxLaw D.hF'

/-- The first copy's conditional density on block `b`, as a function of the pair. -/
def ρ (b : β) (p : (ι → S) × (ι → S)) : (ι → S) → ℝ≥0∞ := condDens (D.Λ b) D.F (D.B b) p.1

/-- The second copy's conditional density on block `b` (against the first copy's block reference, which is the
second copy's on good blocks). -/
def ρ' (b : β) (p : (ι → S) × (ι → S)) : (ι → S) → ℝ≥0∞ := condDens (D.Λ b) D.F' (D.B b) p.2

/-- The gluing of a pair of block samples to a pair of boundary configurations. -/
def pairGlue (B : Finset ι) (p q : (ι → S) × (ι → S)) : (ι → S) × (ι → S) := (glue B q.1 p.1, glue B q.2 p.2)

theorem measurable_pairGlue (B : Finset ι) : Measurable (uncurry (pairGlue (S := S) B)) :=
  ((measurable_glue B).comp ((measurable_fst.comp measurable_snd).prodMk (measurable_fst.comp measurable_fst))).prodMk
    ((measurable_glue B).comp ((measurable_snd.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst)))

theorem measurable_pairGlue_left (B : Finset ι) (p : (ι → S) × (ι → S)) : Measurable (pairGlue B p) :=
  (measurable_pairGlue B).comp measurable_prodMk_left

theorem measurable_ρ (b : β) : Measurable (uncurry (D.ρ b)) :=
  (measurable_condDens D.hF).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

theorem measurable_ρ' (b : β) : Measurable (uncurry (D.ρ' b)) :=
  (measurable_condDens D.hF').comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

theorem measurable_ρ_apply (b : β) (p : (ι → S) × (ι → S)) : Measurable (D.ρ b p) :=
  (D.measurable_ρ b).comp measurable_prodMk_left

theorem measurable_ρ'_apply (b : β) (p : (ι → S) × (ι → S)) : Measurable (D.ρ' b p) :=
  (D.measurable_ρ' b).comp measurable_prodMk_left

theorem lintegral_ρ (b : β) (p : (ι → S) × (ι → S)) : ∫⁻ η, D.ρ b p η ∂(D.Λ b) = 1 :=
  lintegral_condDens D.hF p.1

theorem lintegral_ρ' (b : β) (p : (ι → S) × (ι → S)) : ∫⁻ η, D.ρ' b p η ∂(D.Λ b) = 1 :=
  lintegral_condDens D.hF' p.2

/-! ### The block couplings -/

/-- The maximal block coupling (good blocks). -/
def goodQ (b : β) : Kernel ((ι → S) × (ι → S)) ((ι → S) × (ι → S)) :=
  mapParam (maxCouplingKernel (D.Λ b) (D.ρ b) (D.ρ' b)) (pairGlue (D.B b))

/-- The product block coupling (source blocks). -/
def srcQ (b : β) : Kernel ((ι → S) × (ι → S)) ((ι → S) × (ι → S)) :=
  (D.q b).comap Prod.fst measurable_fst ×ₖ (D.q' b).comap Prod.snd measurable_snd

/-- **The block couplings**: maximal on good blocks, product on source blocks. -/
def Q (b : β) : Kernel ((ι → S) × (ι → S)) ((ι → S) × (ι → S)) := if b ∈ D.good then D.goodQ b else D.srcQ b

instance (b : β) : IsMarkovKernel (maxCouplingKernel (D.Λ b) (D.ρ b) (D.ρ' b)) :=
  isMarkovKernel_maxCouplingKernel (D.measurable_ρ b) (D.measurable_ρ' b) (D.lintegral_ρ b) (D.lintegral_ρ' b)

instance (b : β) : IsMarkovKernel (D.goodQ b) := isMarkovKernel_mapParam _ (measurable_pairGlue _)

instance (b : β) : IsMarkovKernel (D.srcQ b) := by
  unfold srcQ; infer_instance

instance (b : β) : IsMarkovKernel (D.Q b) := by
  unfold Q; split_ifs <;> infer_instance

theorem goodQ_apply (b : β) (p : (ι → S) × (ι → S)) :
    D.goodQ b p = (maxCoupling (D.Λ b) (D.ρ b p) (D.ρ' b p)).map (pairGlue (D.B b) p) := by
  rw [goodQ, mapParam_apply _ (measurable_pairGlue _),
    maxCouplingKernel_apply (D.measurable_ρ b) (D.measurable_ρ' b) (D.lintegral_ρ b) (D.lintegral_ρ' b)]

theorem srcQ_apply (b : β) (σ σ' : ι → S) : D.srcQ b (σ, σ') = (D.q b σ).prod (D.q' b σ') := by
  rw [srcQ, Kernel.prod_apply, Kernel.comap_apply, Kernel.comap_apply]

theorem Q_fst (b : β) (σ σ' : ι → S) : (D.Q b (σ, σ')).map Prod.fst = D.q b σ := by
  unfold Q
  split_ifs with hb
  · rw [goodQ_apply, Measure.map_map measurable_fst (measurable_pairGlue_left _ _)]
    have hc : (Prod.fst ∘ pairGlue (D.B b) (σ, σ')) = (fun η => glue (D.B b) η σ) ∘ Prod.fst := rfl
    rw [hc, ← Measure.map_map (measurable_glue_left _ σ) measurable_fst,
      maxCoupling_map_fst (D.measurable_ρ_apply b _)
        (D.measurable_ρ'_apply b _) (D.lintegral_ρ b _) (D.lintegral_ρ' b _), q,
      boxLaw_apply D.hF]
    rfl
  · rw [srcQ_apply, Measure.map_fst_prod, measure_univ, one_smul]

theorem Q_snd (b : β) (σ σ' : ι → S) : (D.Q b (σ, σ')).map Prod.snd = D.q' b σ' := by
  unfold Q
  split_ifs with hb
  · rw [goodQ_apply, Measure.map_map measurable_snd (measurable_pairGlue_left _ _)]
    have hc : (Prod.snd ∘ pairGlue (D.B b) (σ, σ')) = (fun η => glue (D.B b) η σ') ∘ Prod.snd := rfl
    rw [hc, ← Measure.map_map (measurable_glue_left _ σ') measurable_snd,
      maxCoupling_map_snd (D.measurable_ρ_apply b _)
        (D.measurable_ρ'_apply b _) (D.lintegral_ρ b _) (D.lintegral_ρ' b _), q',
      boxLaw_apply D.hF', D.same b hb]
    rfl
  · rw [srcQ_apply, Measure.map_snd_prod, measure_univ, one_smul]

/-! ### The coupling specification -/

/-- **The `CouplingSpec` of the box densities**, for supports that are measurable, of full measure and kept by the box
laws. -/
def spec [MeasurableEq S] (Ω₀ Ω₀' : Set (ι → S)) (meas₀ : MeasurableSet Ω₀) (meas₀' : MeasurableSet Ω₀')
    (full₀ : D.μ Ω₀ᶜ = 0) (full₀' : D.μ' Ω₀'ᶜ = 0) (inv₀ : ∀ b, ∀ σ ∈ Ω₀, D.q b σ Ω₀ᶜ = 0)
    (inv₀' : ∀ b, ∀ σ ∈ Ω₀', D.q' b σ Ω₀'ᶜ = 0) : CouplingSpec D.μ D.μ' β where
  Ω₀ := Ω₀
  Ω₀' := Ω₀'
  meas₀ := meas₀
  meas₀' := meas₀'
  full₀ := full₀
  full₀' := full₀'
  B := D.B
  q := D.q
  q' := D.q'
  q_local := fun _ σ _ _ hx => boxLaw_local D.hF σ hx
  q'_local := fun _ σ _ _ hx => boxLaw_local D.hF' σ hx
  q_dlr := fun b => boxLaw_dlr D.hF D.F_one (D.split b)
  q'_dlr := fun b => boxLaw_dlr D.hF' D.F'_one (D.split' b)
  q_supp := inv₀
  q'_supp := inv₀'
  Q := D.Q
  Q_markov := fun _ => inferInstance
  Q_fst := fun b σ _ σ' _ => D.Q_fst b σ σ'
  Q_snd := fun b σ _ σ' _ => D.Q_snd b σ σ'

/-- The boundary disagreement weight `δ = Σ_{z ∉ B, σ_z ≠ σ'_z} c b z`. -/
def delta (c : β → ι → ℝ) (b : β) (σ σ' : ι → S) : ℝ :=
  ∑ z ∈ (D.B b)ᶜ, (disagree z).indicator (fun _ => c b z) (σ, σ')

theorem delta_nonneg {c : β → ι → ℝ} (hc : ∀ b z, 0 ≤ c b z) (b : β) (σ σ' : ι → S) : 0 ≤ D.delta c b σ σ' :=
  Finset.sum_nonneg fun z _ => Set.indicator_nonneg (fun _ _ => hc b z) _

/-- **The block coupling bound from the density ratio** (`hunion` for one good block and one boundary pair). -/
theorem Q_differOn_le [MeasurableEq S] {c : β → ι → ℝ} (hc : ∀ b z, 0 ≤ c b z) {b : β} (hb : b ∈ D.good)
    {σ σ' : ι → S}
    (hr : ∀ᵐ η ∂(D.Λ b), ENNReal.ofReal (Real.exp (-D.delta c b σ σ')) * D.ρ b (σ, σ') η ≤ D.ρ' b (σ, σ') η) :
    (D.Q b (σ, σ')).real (differOn (D.B b)) ≤ D.delta c b σ σ' := by
  have hG := measurable_pairGlue_left (D.B b) (σ, σ')
  have hD : MeasurableSet (pairGlue (D.B b) (σ, σ') ⁻¹' differOn (D.B b)) := hG (measurableSet_differOn _)
  have hdiag : ∀ a, (a, a) ∉ pairGlue (D.B b) (σ, σ') ⁻¹' differOn (D.B b) := by
    intro a ha
    simp only [Set.mem_preimage, differOn, Set.mem_iUnion, disagree, Set.mem_ofPred_eq, pairGlue] at ha
    obtain ⟨y, hy, hne⟩ := ha
    exact hne (by rw [glue_of_mem hy, glue_of_mem hy])
  simp only [Q, hb, ite_true]
  rw [measureReal_def, goodQ_apply, Measure.map_apply hG (measurableSet_differOn _), ← measureReal_def]
  exact maxCoupling_real_le_of_ratio (D.measurable_ρ_apply b _) (D.measurable_ρ'_apply b _) (D.lintegral_ρ b _) (D.lintegral_ρ' b _) hD hdiag
    (D.delta_nonneg hc b σ σ') hr

/-! ### `ScaleHyp` -/

/-- **`ScaleHyp` from box densities.** The named hypotheses are the density-ratio bound `hratio` (Balaban: H3 for good
boxes, Lemma C for composite boxes), smallness `hsmall` and counting `hcount`; everything else is proved. -/
def scaleHyp [MeasurableEq S] (Ω₀ Ω₀' : Set (ι → S)) (meas₀ : MeasurableSet Ω₀) (meas₀' : MeasurableSet Ω₀')
    (full₀ : D.μ Ω₀ᶜ = 0) (full₀' : D.μ' Ω₀'ᶜ = 0) (inv₀ : ∀ b, ∀ σ ∈ Ω₀, D.q b σ Ω₀ᶜ = 0)
    (inv₀' : ∀ b, ∀ σ ∈ Ω₀', D.q' b σ Ω₀'ᶜ = 0)
    (dist : ι → ι → ℝ) (dist_self : ∀ x, dist x x = 0) (dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z)
    (c w : β → ι → ℝ) (hc : ∀ b z, 0 ≤ c b z) (lam : ℝ) (hlam : 0 ≤ lam)
    (ε M cmin : ℝ) (hε : 0 ≤ ε) (hM : 0 ≤ M) (hεM : ε * M < 1) (hcmin : 0 < cmin)
    (hcmin_le : ∀ x, cmin ≤ coverage D.B x)
    (hratio : ∀ b ∈ D.good, ∀ σ ∈ Ω₀, ∀ σ' ∈ Ω₀', ∀ᵐ η ∂(D.Λ b),
      ENNReal.ofReal (Real.exp (-D.delta c b σ σ')) * condDens (D.Λ b) D.F (D.B b) σ η ≤
        condDens (D.Λ b) D.F' (D.B b) σ' η)
    (hsmall : ∀ b z, c b z ≤ ε * w b z)
    (hcount : ∀ z, ∑ b ∈ D.good.filter (fun b => z ∉ D.B b), ∑ y ∈ D.B b, w b z * Real.exp (lam * dist z y) ≤
      M * coverage D.B z) :
    ScaleHyp D.μ D.μ' β :=
  ScaleHyp.ofBlockBounds (D.spec Ω₀ Ω₀' meas₀ meas₀' full₀ full₀' inv₀ inv₀') dist dist_self dist_triangle D.good
    c w hc lam hlam ε M cmin hε hM hεM hcmin hcmin_le
    (fun b hb σ hσ σ' hσ' => D.Q_differOn_le hc hb (hratio b hb σ hσ σ' hσ'))
    hsmall hcount

theorem scaleHyp_γ [MeasurableEq S] (Ω₀ Ω₀' : Set (ι → S)) (meas₀ : MeasurableSet Ω₀)
    (meas₀' : MeasurableSet Ω₀') (full₀ : D.μ Ω₀ᶜ = 0) (full₀' : D.μ' Ω₀'ᶜ = 0)
    (inv₀ : ∀ b, ∀ σ ∈ Ω₀, D.q b σ Ω₀ᶜ = 0) (inv₀' : ∀ b, ∀ σ ∈ Ω₀', D.q' b σ Ω₀'ᶜ = 0)
    (dist : ι → ι → ℝ) (dist_self : ∀ x, dist x x = 0) (dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z)
    (c w : β → ι → ℝ) (hc : ∀ b z, 0 ≤ c b z) (lam : ℝ) (hlam : 0 ≤ lam)
    (ε M cmin : ℝ) (hε : 0 ≤ ε) (hM : 0 ≤ M) (hεM : ε * M < 1) (hcmin : 0 < cmin)
    (hcmin_le : ∀ x, cmin ≤ coverage D.B x) (hratio) (hsmall : ∀ b z, c b z ≤ ε * w b z) (hcount) :
    (D.scaleHyp Ω₀ Ω₀' meas₀ meas₀' full₀ full₀' inv₀ inv₀' dist dist_self dist_triangle c w hc lam hlam ε M cmin hε
      hM hεM hcmin hcmin_le hratio hsmall hcount).γ = ε * M := rfl

/-! ### The torus -/

/-- **`ScaleHyp` on the torus**, for the translates of the side-`ℓ` box and the lattice distance. The analytic inputs
are the density-ratio bound `hratio`, the size `c ≤ ε` and the range `R` of `c` (it vanishes for outside sites farther
than `R` from the box). -/
def scaleHyp_torus [MeasurableEq S] {d N : ℕ} [NeZero N] (D : BoxDensities (Torus d N) S (Torus d N)) (ℓ R : ℕ)
    (hℓ : 0 < ℓ) (hB : D.B = boxes ℓ)
    (Ω₀ Ω₀' : Set (Torus d N → S)) (meas₀ : MeasurableSet Ω₀) (meas₀' : MeasurableSet Ω₀')
    (full₀ : D.μ Ω₀ᶜ = 0) (full₀' : D.μ' Ω₀'ᶜ = 0) (inv₀ : ∀ b, ∀ σ ∈ Ω₀, D.q b σ Ω₀ᶜ = 0)
    (inv₀' : ∀ b, ∀ σ ∈ Ω₀', D.q' b σ Ω₀'ᶜ = 0)
    (c : Torus d N → Torus d N → ℝ) (hc : ∀ b z, 0 ≤ c b z) (lam : ℝ) (hlam : 0 ≤ lam) (ε : ℝ) (hε : 0 ≤ ε)
    (hcε : ∀ b z, c b z ≤ ε) (hcR : ∀ b z, (∀ y ∈ boxes ℓ b, (R : ℝ) < tdist z y) → c b z = 0)
    (hεM : ε * ((2 * R + 1 : ℝ) ^ d * (offsets d N ℓ).card * Real.exp (lam * (R + d * ℓ))) < 1)
    (hratio : ∀ b ∈ D.good, ∀ σ ∈ Ω₀, ∀ σ' ∈ Ω₀', ∀ᵐ η ∂(D.Λ b),
      ENNReal.ofReal (Real.exp (-D.delta c b σ σ')) * condDens (D.Λ b) D.F (D.B b) σ η ≤
        condDens (D.Λ b) D.F' (D.B b) σ' η) :
    ScaleHyp D.μ D.μ' (Torus d N) :=
  D.scaleHyp Ω₀ Ω₀' meas₀ meas₀' full₀ full₀' inv₀ inv₀' tdist tdist_self tdist_triangle c (nearW ℓ R) hc lam hlam
    ε ((2 * R + 1 : ℝ) ^ d * (offsets d N ℓ).card * Real.exp (lam * (R + d * ℓ))) (offsets d N ℓ).card hε
    (by positivity) hεM (by exact_mod_cast (offsets_nonempty hℓ).card_pos)
    (fun x => by rw [hB, coverage_boxes])
    hratio
    (fun b z => by
      unfold nearW
      split_ifs with h
      · simpa using hcε b z
      · push Not at h
        rw [hcR b z h, mul_zero])
    (fun z => by rw [hB]; exact torus_hcount ℓ R D.good hlam z)

/-! ### Non-vacuity: product references -/

/-- Box densities with product references `Λ₀ = Λ₀' = Λ b = Λ' b = Measure.pi ν` (all splitting hypotheses proved by
`isSplit_pi`). -/
def ofProduct (ν : ι → Measure S) [∀ i, IsProbabilityMeasure (ν i)] (F F' : (ι → S) → ℝ≥0∞) (B : β → Finset ι)
    (good : Finset β) (hF : Measurable F) (hF' : Measurable F') (hF1 : ∫⁻ σ, F σ ∂Measure.pi ν = 1)
    (hF1' : ∫⁻ σ, F' σ ∂Measure.pi ν = 1) : BoxDensities ι S β where
  Λ₀ := Measure.pi ν
  Λ₀' := Measure.pi ν
  F := F
  F' := F'
  B := B
  Λ := fun _ => Measure.pi ν
  Λ' := fun _ => Measure.pi ν
  good := good
  sfinite₀ := inferInstance
  sfinite₀' := inferInstance
  prob := fun _ => inferInstance
  prob' := fun _ => inferInstance
  hF := hF
  hF' := hF'
  F_one := hF1
  F'_one := hF1'
  split := fun b => isSplit_pi ν (B b)
  split' := fun b => isSplit_pi ν (B b)
  same := fun _ _ => rfl

/-- **Sanity check of the hypotheses**: for the independent product law on the torus (density `1` against
`Measure.pi ν`), `scaleHyp_torus` applies with `c = 0`, `ε = 0` and `Ω₀ = Ω₀' = univ`, so all of its hypotheses can
be met at once. -/
theorem nonempty_scaleHyp_torus_product [MeasurableEq S] {d N : ℕ} [NeZero N] (ν : Torus d N → Measure S)
    [∀ i, IsProbabilityMeasure (ν i)] (ℓ : ℕ) (hℓ : 0 < ℓ) (good : Finset (Torus d N)) :
    Nonempty (ScaleHyp ((Measure.pi ν).withDensity fun _ => 1) ((Measure.pi ν).withDensity fun _ => 1)
      (Torus d N)) := by
  have h1 : ∫⁻ _σ, (1 : ℝ≥0∞) ∂Measure.pi ν = 1 := by simp
  let D := ofProduct ν (fun _ => 1) (fun _ => 1) (boxes ℓ) good measurable_const measurable_const h1 h1
  exact ⟨D.scaleHyp_torus ℓ 0 hℓ rfl Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ (by simp [D, μ])
    (by simp [D, μ']) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ => 0) (fun _ _ => le_rfl) 0 le_rfl 0
    le_rfl (fun _ _ => le_rfl) (fun _ _ _ => rfl) (by simp)
    (fun b _ σ _ σ' _ => ae_of_all _ fun η => by simp [D, ofProduct, delta, condDens, boxZ])⟩

end BoxDensities

end ProofPhase.ScaleHypKit
