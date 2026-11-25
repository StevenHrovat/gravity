/-
Proof phase, cycle 6, workstream 5 (c6e-bookkeeping): the law of multiplicative noise (2026-11-22).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c6e-bookkeeping/NOTE.md`, section 1.
-/

import ProofPhase.Repair.MulNoise

/-!
# The conditional law of the multiplicative noise has a product density

Generic measure theory (no gauge group yet):

* `map_mul_left_withDensity`: left translation of `h dμ` is `h(b⁻¹ ·) dμ` (`μ` left invariant).
* `map_inv_withDensity`: inversion of `g dμ` is `g(·⁻¹) dμ` (`μ` inversion invariant).
* `map_inv_mul_withDensity`: `z ↦ z⁻¹ b` sends `h dμ` to `h(b ·⁻¹) dμ`.
* `pi_withDensity`: a finite product of bounded densities is the density of the product.

Link bookkeeping for `mulNoise` (`ProofPhase.Repair`):

* `rawNoise`: the noise variable that sits on each link (fixed: `c`, positive: `a`, mirror: `a'`), and
  `rawNoise_law`: for i.i.d. noise it is i.i.d. on the links (`linkSplit` is a bijection).
* `mulNoise_eq`: `mulNoise b η = (l ↦ step (b l) l (rawNoise η l))`, coordinatewise.
* `mulNoise_law`: for an i.i.d. noise of law `h dμ` with `0 ≤ h ≤ C`, the law of `mulNoise b η` is the product
  density `∏_l k_l(b_l, φ_l) dμ^{⊗links}`, `k_l(b, φ) = h(b⁻¹ φ)` (all links but the negative temporal ones) and
  `h(b φ⁻¹)` (negative temporal links: the noise sits on the left, inverted).

No class-function or inversion-symmetry property of `h` is needed (NOTE section 1: this weakens the paper argument of
c5c §3.2, which used both).
-/

open MeasureTheory Finset AreaLaw.Concrete Positivity ProofPhase.Repair

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Book

/-! ## 1. Densities under translation, inversion, products -/

section Generic

variable {G : Type*} [Group G] [MeasurableSpace G]

theorem map_mul_left_withDensity [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] {h : G → ℝ} (b : G) :
    (μ.withDensity (fun z => ENNReal.ofReal (h z))).map (fun z => b * z) =
      μ.withDensity (fun φ => ENNReal.ofReal (h (b⁻¹ * φ))) := by
  ext s hs
  have hm : Measurable (fun z : G => b * z) := measurable_const_mul b
  rw [Measure.map_apply hm hs, withDensity_apply _ (hm hs), withDensity_apply _ hs,
    ← lintegral_indicator (hm hs), ← lintegral_indicator hs]
  have e : ∀ z, ((fun z : G => b * z) ⁻¹' s).indicator (fun z => ENNReal.ofReal (h z)) z =
      (s.indicator (fun φ => ENNReal.ofReal (h (b⁻¹ * φ)))) (b * z) := by
    intro z
    simp [Set.indicator_apply]
  simp_rw [e]
  exact lintegral_mul_left_eq_self (s.indicator (fun φ => ENNReal.ofReal (h (b⁻¹ * φ)))) b

theorem map_inv_withDensity [MeasurableInv G] (μ : Measure G) [μ.IsInvInvariant] {g : G → ℝ} :
    (μ.withDensity (fun z => ENNReal.ofReal (g z))).map (fun z => z⁻¹) =
      μ.withDensity (fun φ => ENNReal.ofReal (g φ⁻¹)) := by
  ext s hs
  have hm : Measurable (fun z : G => z⁻¹) := measurable_inv
  rw [Measure.map_apply hm hs, withDensity_apply _ (hm hs), withDensity_apply _ hs,
    ← lintegral_indicator (hm hs), ← lintegral_indicator hs]
  have e : ∀ z, ((fun z : G => z⁻¹) ⁻¹' s).indicator (fun z => ENNReal.ofReal (g z)) z =
      (s.indicator (fun φ => ENNReal.ofReal (g φ⁻¹))) z⁻¹ := by
    intro z
    simp [Set.indicator_apply]
  simp_rw [e]
  exact lintegral_inv_eq_self (s.indicator (fun φ => ENNReal.ofReal (g φ⁻¹)))

theorem map_inv_mul_withDensity [MeasurableMul G] [MeasurableInv G] (μ : Measure G) [μ.IsMulLeftInvariant]
    [μ.IsInvInvariant] {h : G → ℝ} (b : G) :
    (μ.withDensity (fun z => ENNReal.ofReal (h z))).map (fun z => z⁻¹ * b) =
      μ.withDensity (fun φ => ENNReal.ofReal (h (b * φ⁻¹))) := by
  have e : (fun z : G => z⁻¹ * b) = (fun z => z⁻¹) ∘ (fun z => b⁻¹ * z) := by
    funext z; simp
  have h1 := map_mul_left_withDensity (μ := μ) (h := h) b⁻¹
  have h2 := map_inv_withDensity (μ := μ) (g := fun φ => h (b⁻¹⁻¹ * φ))
  rw [e, ← Measure.map_map measurable_inv (measurable_const_mul b⁻¹), h1, h2]
  simp

end Generic

section PiDensity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- **A finite product of bounded densities is the density of the product measure.** -/
theorem pi_withDensity (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)] {f : ∀ i, X i → ℝ}
    (hf : ∀ i, Measurable (f i)) {C : ℝ} (h0 : ∀ i x, 0 ≤ f i x) (hC : ∀ i x, f i x ≤ C) :
    Measure.pi (fun i => (ν i).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (Measure.pi ν).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  have hbd : ∀ i x, |f i x| ≤ C := fun i x => by rw [abs_of_nonneg (h0 i x)]; exact hC i x
  have hfin : ∀ i, IsFiniteMeasure ((ν i).withDensity (fun x => ENNReal.ofReal (f i x))) := by
    intro i
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ∫⁻ x, ENNReal.ofReal (f i x) ∂(ν i) ≤ ∫⁻ _, ENNReal.ofReal C ∂(ν i) :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hC i x)
      _ < ⊤ := by simp
  haveI : ∀ i, SigmaFinite ((ν i).withDensity (fun x => ENNReal.ofReal (f i x))) := fun i => inferInstance
  refine Measure.pi_eq fun s hs => ?_
  -- the integrand of the box
  set g : ∀ i, X i → ℝ := fun i x => (s i).indicator (f i) x with hg
  have g0 : ∀ i x, 0 ≤ g i x := fun i x => by
    simp only [hg, Set.indicator_apply]; split_ifs
    · exact h0 i x
    · exact le_rfl
  have gm : ∀ i, Measurable (g i) := fun i => (hf i).indicator (hs i)
  have gbd : ∀ i x, |g i x| ≤ C := fun i x => by
    simp only [hg, Set.indicator_apply]; split_ifs
    · exact hbd i x
    · simpa using (abs_nonneg _).trans (hbd i x)
  have hint : ∀ i, Integrable (g i) (ν i) := fun i =>
    Integrable.of_bound (gm i).aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact gbd i x)
  have hprodm : Measurable (fun x : ∀ i, X i => ∏ i, g i (x i)) :=
    Finset.measurable_prod _ fun i _ => (gm i).comp (measurable_pi_apply i)
  have hprod0 : ∀ x : ∀ i, X i, 0 ≤ ∏ i, g i (x i) := fun x => Finset.prod_nonneg fun i _ => g0 i _
  have hprodint : Integrable (fun x : ∀ i, X i => ∏ i, g i (x i)) (Measure.pi ν) := by
    refine Integrable.of_bound hprodm.aestronglyMeasurable (∏ _i : ι, |C|) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hprod0 x)]
    exact Finset.prod_le_prod₀ (fun i _ => g0 i _)
      (fun i _ => ((le_abs_self _).trans (gbd i (x i))).trans (le_abs_self C))
  have hlhs : ((Measure.pi ν).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i)))) (Set.pi Set.univ s) =
      ENNReal.ofReal (∏ i, ∫ x, g i x ∂(ν i)) := by
    rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs),
      ← integral_fintype_prod_eq_prod (fun i x => g i x) (μ := ν),
      ofReal_integral_eq_lintegral_ofReal hprodint (Filter.Eventually.of_forall hprod0)]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hx]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [hg]
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [hg]; rw [Set.indicator_of_notMem hi]),
        ENNReal.ofReal_zero]
  rw [hlhs, ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (g0 i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i),
    ofReal_integral_eq_lintegral_ofReal (hint i) (Filter.Eventually.of_forall (g0 i))]
  refine lintegral_congr fun x => ?_
  simp only [hg, Set.indicator_apply]
  split_ifs <;> simp

end PiDensity

/-! ## 2. The noise variable on each link -/

section Links

variable {d M : ℕ} [NeZero d] [NeZero M] {G : Type*} [Group G]

/-- The noise variable that sits on the link `l`: `c_l` on a fixed link, `a_l` on a positive link, `a'_p` on the mirror
of the positive link `p`. -/
def rawNoise (hM : Even M) (η : (FixLink d M → G) × (PosLink d M → G) × (PosLink d M → G)) :
    LatticeLink d M → G :=
  fun l => Sum.elim η.1 (Sum.elim η.2.1 η.2.2) ((linkSplit hM).symm l)

theorem rawNoise_fixed (hM : Even M) (η : (FixLink d M → G) × (PosLink d M → G) × (PosLink d M → G))
    {l : LatticeLink d M} (h1 : IsFixedLink l) : rawNoise hM η l = η.1 ⟨l, h1⟩ := by
  have : (linkSplit hM).symm l = Sum.inl ⟨l, h1⟩ := (Equiv.symm_apply_eq _).2 rfl
  simp [rawNoise, this]

theorem rawNoise_pos (hM : Even M) (η : (FixLink d M → G) × (PosLink d M → G) × (PosLink d M → G))
    {l : LatticeLink d M} (h2 : IsPosLink l) : rawNoise hM η l = η.2.1 ⟨l, h2⟩ := by
  have : (linkSplit hM).symm l = Sum.inr (Sum.inl ⟨l, h2⟩) := (Equiv.symm_apply_eq _).2 rfl
  simp [rawNoise, this]

theorem rawNoise_neg (hM : Even M) (η : (FixLink d M → G) × (PosLink d M → G) × (PosLink d M → G))
    {l : LatticeLink d M} (h1 : ¬IsFixedLink l) (h2 : ¬IsPosLink l) :
    rawNoise hM η l = η.2.2 ⟨mirrorLink l, link_neg_mirror hM h1 h2⟩ := by
  have : (linkSplit hM).symm l = Sum.inr (Sum.inr ⟨mirrorLink l, link_neg_mirror hM h1 h2⟩) :=
    (Equiv.symm_apply_eq _).2 (mirrorLink_involutive l).symm
  simp [rawNoise, this]

variable [MeasurableSpace G]

theorem measurable_rawNoise (hM : Even M) : Measurable (rawNoise (G := G) (d := d) hM) := by
  refine measurable_pi_iff.2 fun l => ?_
  unfold rawNoise
  generalize (linkSplit hM).symm l = i
  rcases i with i | i | i
  · exact (measurable_pi_apply i).comp measurable_fst
  · exact (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  · exact (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)

/-- **The noise is i.i.d. on the links**: for i.i.d. noise `c, a, a' ~ τ`, the link variables `rawNoise` are i.i.d.
`τ`, because `linkSplit` is a bijection fixed ⊕ positive ⊕ mirror(positive) → links. -/
theorem rawNoise_law (hM : Even M) (τ : Measure G) [IsProbabilityMeasure τ] :
    (((Measure.pi fun _ : FixLink d M => τ).prod
      ((Measure.pi fun _ : PosLink d M => τ).prod (Measure.pi fun _ : PosLink d M => τ)))).map (rawNoise hM) =
      Measure.pi (fun _ : LatticeLink d M => τ) := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (measurable_rawNoise hM) (MeasurableSet.univ_pi hs)]
  have e : rawNoise hM ⁻¹' (Set.pi Set.univ s) =
      (Set.pi Set.univ fun i : FixLink d M => s i.1) ×ˢ
        ((Set.pi Set.univ fun p : PosLink d M => s p.1) ×ˢ
          (Set.pi Set.univ fun p : PosLink d M => s (mirrorLink p.1))) := by
    ext η
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun p => ?_, fun p => ?_⟩
      · have := h i.1; rwa [rawNoise_fixed hM η i.2] at this
      · have := h p.1; rwa [rawNoise_pos hM η p.2] at this
      · have h1 := (link_pos_mirror hM p.2).1
        have h2 := (link_pos_mirror hM p.2).2
        have := h (mirrorLink p.1)
        rw [rawNoise_neg hM η h1 h2] at this
        have e : (⟨mirrorLink (mirrorLink p.1), link_neg_mirror hM h1 h2⟩ : PosLink d M) = p :=
          Subtype.ext (mirrorLink_involutive p.1)
        rwa [e] at this
    · rintro ⟨hf, hp, hq⟩ l
      by_cases h1 : IsFixedLink l
      · rw [rawNoise_fixed hM η h1]; exact hf ⟨l, h1⟩
      by_cases h2 : IsPosLink l
      · rw [rawNoise_pos hM η h2]; exact hp ⟨l, h2⟩
      · rw [rawNoise_neg hM η h1 h2]
        have := hq ⟨mirrorLink l, link_neg_mirror hM h1 h2⟩
        simpa [mirrorLink_involutive l] using this
  rw [e, Measure.prod_prod, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Measure.pi_pi]
  have := Fintype.prod_equiv (linkSplit hM) (fun i => τ (s ((linkSplit hM) i))) (fun l => τ (s l)) (fun i => rfl)
  rw [← this, Fintype.prod_sum_type, Fintype.prod_sum_type]
  rfl

/-! ## 3. `mulNoise` acts coordinatewise on the link variables, and its law has a product density -/

/-- The coordinate map of `mulNoise`: on a negative temporal link the noise sits on the left, inverted. -/
def noiseStep (l : LatticeLink d M) (bl z : G) : G :=
  if ¬IsFixedLink l ∧ ¬IsPosLink l ∧ l.dir = 0 then z⁻¹ * bl else bl * z

theorem mulNoise_eq (hM : Even M) (b : GaugeConnection G d M)
    (η : (FixLink d M → G) × (PosLink d M → G) × (PosLink d M → G)) :
    mulNoise hM b η = fun l => noiseStep l (b l) (rawNoise hM η l) := by
  funext l
  by_cases h1 : IsFixedLink l
  · rw [mulNoise_fixed hM b η h1, rawNoise_fixed hM η h1]
    simp [noiseStep, h1]
  by_cases h2 : IsPosLink l
  · rw [mulNoise_pos hM b η h2, rawNoise_pos hM η h2]
    simp [noiseStep, h2]
  · rw [mulNoise_neg hM b η h1 h2, rawNoise_neg hM η h1 h2]
    by_cases hd : l.dir = 0
    · simp [noiseStep, h1, h2, hd]
    · simp [noiseStep, h1, h2, hd]

variable [MeasurableMul₂ G] [MeasurableInv G]

theorem measurable_noiseStep (l : LatticeLink d M) (bl : G) : Measurable (noiseStep l bl) := by
  unfold noiseStep
  split_ifs
  · exact measurable_inv.mul_const bl
  · exact measurable_const_mul bl

/-- The density of the one-link kernel: `h(b⁻¹ φ)`, and `h(b φ⁻¹)` on negative temporal links. -/
def linkKernel (h : G → ℝ) (l : LatticeLink d M) (bl φ : G) : ℝ :=
  if ¬IsFixedLink l ∧ ¬IsPosLink l ∧ l.dir = 0 then h (bl * φ⁻¹) else h (bl⁻¹ * φ)

theorem measurable_linkKernel {h : G → ℝ} (hh : Measurable h) (l : LatticeLink d M) :
    Measurable (fun q : G × G => linkKernel h l q.1 q.2) := by
  unfold linkKernel
  split_ifs
  · exact hh.comp (measurable_fst.mul measurable_snd.inv)
  · exact hh.comp (measurable_fst.inv.mul measurable_snd)


theorem measurable_linkKernel' {α : Type*} [MeasurableSpace α] {h : G → ℝ} (hh : Measurable h) (l : LatticeLink d M)
    {f g : α → G} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => linkKernel h l (f a) (g a)) := by
  unfold linkKernel
  split_ifs
  · exact hh.comp (hf.mul hg.inv)
  · exact hh.comp (hf.inv.mul hg)
theorem noiseStep_law (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsInvInvariant] {h : G → ℝ}
    (l : LatticeLink d M) (bl : G) :
    (μ.withDensity (fun z => ENNReal.ofReal (h z))).map (noiseStep l bl) =
      μ.withDensity (fun φ => ENNReal.ofReal (linkKernel h l bl φ)) := by
  by_cases hc : ¬IsFixedLink l ∧ ¬IsPosLink l ∧ l.dir = 0
  · have e : noiseStep l bl = fun z => z⁻¹ * bl := by funext z; simp [noiseStep, hc]
    rw [e, map_inv_mul_withDensity]
    simp [linkKernel, hc]
  · have e : noiseStep l bl = fun z => bl * z := by funext z; simp [noiseStep, hc]
    rw [e, map_mul_left_withDensity]
    simp [linkKernel, hc]

/-- **The law of the multiplicative noise given the smeared field `b`**: for i.i.d. noise of law `h dμ`
(`0 ≤ h ≤ C`, `μ` a probability measure invariant under left translation and inversion), the law of
`mulNoise b η` is the product density `∏_l linkKernel h l (b l) (φ l)` with respect to `μ^{⊗ links}`. -/
theorem mulNoise_law (hM : Even M) (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    [μ.IsInvInvariant] {h : G → ℝ} (hh : Measurable h) {C : ℝ} (h0 : ∀ x, 0 ≤ h x) (hC : ∀ x, h x ≤ C)
    [IsProbabilityMeasure (μ.withDensity (fun z => ENNReal.ofReal (h z)))] (b : GaugeConnection G d M) :
    (((Measure.pi fun _ : FixLink d M => μ.withDensity (fun z => ENNReal.ofReal (h z))).prod
      ((Measure.pi fun _ : PosLink d M => μ.withDensity (fun z => ENNReal.ofReal (h z))).prod
        (Measure.pi fun _ : PosLink d M => μ.withDensity (fun z => ENNReal.ofReal (h z)))))).map (mulNoise hM b) =
      (Measure.pi fun _ : LatticeLink d M => μ).withDensity
        (fun φ => ENNReal.ofReal (∏ l, linkKernel h l (b l) (φ l))) := by
  set τ := μ.withDensity (fun z => ENNReal.ofReal (h z)) with hτ
  have hm : Measurable (fun (z : LatticeLink d M → G) (l : LatticeLink d M) => noiseStep l (b l) (z l)) :=
    measurable_pi_iff.2 fun l => (measurable_noiseStep l (b l)).comp (measurable_pi_apply l)
  have e : mulNoise hM b = (fun (z : LatticeLink d M → G) (l : LatticeLink d M) => noiseStep l (b l) (z l)) ∘
      rawNoise hM := by
    funext η; exact mulNoise_eq hM b η
  rw [e, ← Measure.map_map hm (measurable_rawNoise hM), rawNoise_law hM τ]
  haveI : ∀ l : LatticeLink d M, IsProbabilityMeasure (τ.map (noiseStep l (b l))) := fun l =>
    (Measure.isProbabilityMeasure_map_iff (measurable_noiseStep l (b l)).aemeasurable).2 inferInstance
  rw [Measure.pi_map_pi (μ := fun _ : LatticeLink d M => τ) (f := fun l => noiseStep l (b l))
    (fun l => (measurable_noiseStep l (b l)).aemeasurable)]
  have hker : ∀ l : LatticeLink d M, τ.map (noiseStep l (b l)) =
      μ.withDensity (fun φ => ENNReal.ofReal (linkKernel h l (b l) φ)) := fun l => noiseStep_law μ l (b l)
  simp_rw [hker]
  have hk0 : ∀ (l : LatticeLink d M) φ, 0 ≤ linkKernel h l (b l) φ := fun l φ => by
    unfold linkKernel; split_ifs <;> exact h0 _
  have hkC : ∀ (l : LatticeLink d M) φ, linkKernel h l (b l) φ ≤ C := fun l φ => by
    unfold linkKernel; split_ifs <;> exact hC _
  have hkm : ∀ l : LatticeLink d M, Measurable (fun φ => linkKernel h l (b l) φ) := fun l =>
    (measurable_linkKernel hh l).comp (measurable_const.prodMk measurable_id)
  exact pi_withDensity (fun _ : LatticeLink d M => μ) hkm hk0 hkC

end Links

end ProofPhase.Book
