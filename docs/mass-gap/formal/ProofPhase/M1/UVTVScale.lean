/-
Proof phase, M1 tools (m1-tools), Lean phase, module 1: one scale of Lemma UV-TV (2026-11-23).
Released under Apache 2.0.

Paper: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/UV-TV.md`, sections 28, 30.2, 33.1, 34.1, 38.5, 39.3-39.4.
-/

import ProofPhase.OneBox.CouplingDS

/-!
# One scale of Lemma UV-TV: the disagreement radius

The generic coupling theorem (`ProofPhase.OneBox.CouplingDS`) turns influence bounds on good blocks into a coupling.
This module instantiates it the way `UV-TV.md` 30.2 uses it at one scale.

* `ScaleHyp`: one scale's data. A `CouplingSpec` (the block specifications and block couplings of the scale-`j` kernel
  given one pattern pair), a distance on the sites, the good blocks, and the **unweighted** influence matrix `k b y z`
  of a good block: the probability that the block coupling leaves site `y ∈ B b` disagreeing is at most the sum of
  `k b y z` over the disagreeing outside sites `z`. This is the form in which H3 (good boxes) and Lemma C (composite
  boxes) are proved (`UV-TV.md` 10.2, 19, 29). They enter here as the named hypothesis `influence`, with the column
  condition `column` (`UV-TV.md` 22.3).
* `ScaleHyp.weights`: for **every** centre `x`, the weights `v_x(y) = exp(-λ d(y, x))` are admissible, with the same
  influence numbers `K b z = Σ_{y ∈ B b} k b y z exp(λ d(z, y))`. This is Corollary 34.1 ("one coupling for all sites").
* `ScaleHyp.exists_coupling_pointwise`: one coupling `π` with, for every site `x`,
  `π(Y_x ≠ Y'_x) ≤ Σ_{b source} Σ_{y ∈ B b} exp(-λ d(y, x)) / ((1 - γ) c_min) + ε`.
* `ScaleHyp.exists_coupling_target`: if every source site is at distance `≥ a` from a target set `T`, then
  `Σ_{x ∈ T} π(Y_x ≠ Y'_x) ≤ |T| (n_src exp(-λ a)/((1 - γ) c_min) + ε)`.
* `scale_front`: **the truncation events as a case split** (`UV-TV.md` 33.1). The scale-`j` laws are mixtures over a
  finite set of pattern pairs `p` (coupled first by H1). On the truncation set `E` nothing is assumed; off `E` each
  pattern pair has its `ScaleHyp` and its sources at distance `≥ a` from `T`. Then the mixtures have a coupling `Π` with
  `Π(Y ≠ Y' somewhere on T) ≤ w(E) + Σ_{p ∉ E} w_p |T| (n_src,p exp(-λ_p a)/((1 - γ_p) c_min,p) + ε)`.
* `scale_front_integral`: the same bound for `|∫ F dμ - ∫ F dμ'|`, `F` bounded measurable and depending only on `T`.

**Site bundling** (`UV-TV.md` 38.5, 39.3): `S` is one per-site space and the blocks `B b` are sets of whole sites,
exactly as in `CouplingSpec`. The block couplings `Q b` are fields of `CouplingSpec`, i.e. measurable kernels: their
construction (39.4) is the instantiation's obligation, not proved here.
-/

open MeasureTheory ProbabilityTheory Finset ProofPhase.OneBox ProofPhase.OneBox.CouplingSpec

open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.M1.UVTV

variable {ι S β : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] [Fintype β] [DecidableEq β]

/-! ### One scale's hypotheses -/

/-- **One scale of UV-TV** (`UV-TV.md` 28.3, 30.2). The coupling data `C` of the scale-`j` kernel given a pattern pair,
a distance `dist` (triangle inequality, `dist x x = 0`), the good blocks, the decay rate `lam ≥ 0`, and the constants
`γ < 1`, `c_min > 0` of the column condition.

* `influence` (**H3 / Lemma C**, named hypothesis): on a good block, for in-support boundary pairs, the block coupling
  leaves `y ∈ B b` disagreeing with probability at most `Σ_{z ∉ B b, σ_z ≠ σ'_z} k b y z`.
* `column` (**the column condition (K)**, `UV-TV.md` 22.3): `Σ_{b good, z ∉ B b} Σ_{y ∈ B b} k b y z e^{λ d(z, y)} ≤
  γ c(z)`. -/
structure ScaleHyp (μ μ' : Measure (ι → S)) (β : Type*) [Fintype β] [DecidableEq β] where
  C : CouplingSpec μ μ' β
  dist : ι → ι → ℝ
  dist_self : ∀ x, dist x x = 0
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z
  good : Finset β
  k : β → ι → ι → ℝ
  k_nonneg : ∀ b y z, 0 ≤ k b y z
  lam : ℝ
  lam_nonneg : 0 ≤ lam
  γ : ℝ
  cmin : ℝ
  γ_nonneg : 0 ≤ γ
  γ_lt_one : γ < 1
  cmin_pos : 0 < cmin
  cmin_le : ∀ x, cmin ≤ coverage C.B x
  influence : ∀ b ∈ good, ∀ σ ∈ C.Ω₀, ∀ σ' ∈ C.Ω₀', ∀ y ∈ C.B b,
    (C.Q b (σ, σ')).real (disagree y) ≤ ∑ z ∈ (C.B b)ᶜ, (disagree z).indicator (fun _ => k b y z) (σ, σ')
  column : ∀ z, ∑ b ∈ good.filter (fun b => z ∉ C.B b), ∑ y ∈ C.B b, k b y z * Real.exp (lam * dist z y) ≤
    γ * coverage C.B z

namespace ScaleHyp

variable {μ μ' : Measure (ι → S)} (H : ScaleHyp μ μ' β)

/-- The weights centred at `x`: `v_x(y) = exp(-λ d(y, x))`. -/
def v (x : ι) (y : ι) : ℝ := Real.exp (-(H.lam * H.dist y x))

/-- The influence numbers of the weighted form: `K b z = Σ_{y ∈ B b} k b y z exp(λ d(z, y))`, the same for every
centre. -/
def K (b : β) (z : ι) : ℝ := ∑ y ∈ H.C.B b, H.k b y z * Real.exp (H.lam * H.dist z y)

theorem v_nonneg (x y : ι) : 0 ≤ H.v x y := (Real.exp_pos _).le

theorem v_self (x : ι) : H.v x x = 1 := by simp [v, H.dist_self]

/-- `v_x(y) ≤ e^{λ d(z, y)} v_x(z)`, by the triangle inequality `d(z, x) ≤ d(z, y) + d(y, x)`. -/
theorem v_le (x y z : ι) : H.v x y ≤ Real.exp (H.lam * H.dist z y) * H.v x z := by
  simp only [v, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := H.dist_triangle z y x
  nlinarith [H.lam_nonneg]

/-- The indicator with a constant value, written as a product. -/
theorem indicator_eq_mul (s : Set ((ι → S) × (ι → S))) (c : ℝ) (p : (ι → S) × (ι → S)) :
    s.indicator (fun _ => c) p = s.indicator (fun _ => (1 : ℝ)) p * c := by
  by_cases h : p ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

/-- **The weighted influence bound (I) for every centre**, from the unweighted one. -/
theorem weighted_influence (x : ι) : ∀ b ∈ H.good, ∀ σ ∈ H.C.Ω₀, ∀ σ' ∈ H.C.Ω₀',
    ∑ y ∈ H.C.B b, H.v x y * (H.C.Q b (σ, σ')).real (disagree y) ≤
      ∑ z ∈ (H.C.B b)ᶜ, (disagree z).indicator (fun _ => H.K b z * H.v x z) (σ, σ') := by
  intro b hb σ hσ σ' hσ'
  set ind : ι → ℝ := fun z => (disagree z).indicator (fun _ => (1 : ℝ)) (σ, σ') with hind
  have hind0 : ∀ z, 0 ≤ ind z := fun z => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  calc ∑ y ∈ H.C.B b, H.v x y * (H.C.Q b (σ, σ')).real (disagree y)
      ≤ ∑ y ∈ H.C.B b, H.v x y * ∑ z ∈ (H.C.B b)ᶜ, ind z * H.k b y z := by
        refine Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_left ?_ (H.v_nonneg x y)
        refine (H.influence b hb σ hσ σ' hσ' y hy).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun z _ => indicator_eq_mul _ _ _
    _ = ∑ z ∈ (H.C.B b)ᶜ, ind z * ∑ y ∈ H.C.B b, H.v x y * H.k b y z := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => by ring
    _ ≤ ∑ z ∈ (H.C.B b)ᶜ, ind z * (H.K b z * H.v x z) := by
        refine Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (hind0 z)
        simp only [K, Finset.sum_mul]
        refine Finset.sum_le_sum fun y _ => ?_
        calc H.v x y * H.k b y z ≤ (Real.exp (H.lam * H.dist z y) * H.v x z) * H.k b y z :=
              mul_le_mul_of_nonneg_right (H.v_le x y z) (H.k_nonneg b y z)
          _ = H.k b y z * Real.exp (H.lam * H.dist z y) * H.v x z := by ring
    _ = ∑ z ∈ (H.C.B b)ᶜ, (disagree z).indicator (fun _ => H.K b z * H.v x z) (σ, σ') :=
        Finset.sum_congr rfl fun z _ => (indicator_eq_mul _ _ _).symm

/-- **Corollary 34.1 in Lean: admissible weights for every centre**, with one good set and one `K`. -/
def weights (x : ι) : H.C.DSWeights where
  good := H.good
  v := H.v x
  K := H.K
  γ := H.γ
  cmin := H.cmin
  v_nonneg := H.v_nonneg x
  γ_nonneg := H.γ_nonneg
  γ_lt_one := H.γ_lt_one
  cmin_pos := H.cmin_pos
  cmin_le := H.cmin_le
  influence := H.weighted_influence x
  column := H.column

/-- The source kernel at `x`: `Σ_{b source} Σ_{y ∈ B b} exp(-λ d(y, x))`. -/
def srcKernel (x : ι) : ℝ := srcWeight H.good H.C.B (H.v x)

/-- The number of source sites, counted with multiplicity: `Σ_{b source} |B b|`. -/
def nSrc : ℕ := ∑ b ∈ univ \ H.good, (H.C.B b).card

theorem one_sub_mul_cmin_pos : 0 < (1 - H.γ) * H.cmin :=
  mul_pos (by linarith [H.γ_lt_one]) H.cmin_pos

/-- A single disagreement probability is bounded by `Φ` with the weights centred at that site. -/
theorem real_disagree_le_phi (x : ι) (π : Measure ((ι → S) × (ι → S))) :
    π.real (disagree x) ≤ phi (H.v x) π := by
  have hle := Finset.single_le_sum (f := fun y => H.v x y * π.real (disagree y))
    (fun y _ => mul_nonneg (H.v_nonneg x y) measureReal_nonneg) (Finset.mem_univ x)
  simpa [phi, H.v_self] using hle

/-- **One coupling, pointwise bounds at every site** (`UV-TV.md` 30.2, step 1). -/
theorem exists_coupling_pointwise [MeasurableEq S] [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [Nonempty β]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ π, H.C.IsSuppCoupling π ∧ ∀ x, π.real (disagree x) ≤ H.srcKernel x / ((1 - H.γ) * H.cmin) + ε := by
  obtain ⟨n, hs, hn⟩ := H.C.exists_iter_forall_le H.weights hε
  exact ⟨H.C.iter n, hs, fun x => (H.real_disagree_le_phi x _).trans (hn x)⟩

/-- If every source site is at distance `≥ a` from `x`, the source kernel at `x` is at most `n_src e^{-λ a}`. -/
theorem srcKernel_le {a : ℝ} {x : ι} (hsep : ∀ b ∉ H.good, ∀ y ∈ H.C.B b, a ≤ H.dist y x) :
    H.srcKernel x ≤ H.nSrc * Real.exp (-(H.lam * a)) := by
  simp only [srcKernel, srcWeight, nSrc, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun b hb => ?_
  have hb' : b ∉ H.good := (Finset.mem_sdiff.mp hb).2
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun y hy => ?_
  exact Real.exp_le_exp.mpr (by nlinarith [H.lam_nonneg, hsep b hb' y hy])

/-- **The disagreement radius at one scale** (`UV-TV.md` 30.2). If every source site is at distance `≥ a` from the
target `T`, one coupling has `Σ_{x ∈ T} π(Y_x ≠ Y'_x) ≤ |T| (n_src e^{-λ a}/((1 - γ) c_min) + ε)`. -/
theorem exists_coupling_target [MeasurableEq S] [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [Nonempty β]
    (T : Finset ι) {a : ℝ} (hsep : ∀ b ∉ H.good, ∀ y ∈ H.C.B b, ∀ x ∈ T, a ≤ H.dist y x) {ε : ℝ} (hε : 0 < ε) :
    ∃ π, H.C.IsSuppCoupling π ∧
      ∑ x ∈ T, π.real (disagree x) ≤
        T.card * (H.nSrc * Real.exp (-(H.lam * a)) / ((1 - H.γ) * H.cmin) + ε) := by
  obtain ⟨π, hs, hx⟩ := H.exists_coupling_pointwise hε
  refine ⟨π, hs, ?_⟩
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun x hxT => (hx x).trans ?_
  gcongr
  · exact H.one_sub_mul_cmin_pos.le
  · exact H.srcKernel_le fun b hb y hy => hsep b hb y hy x hxT

end ScaleHyp

/-! ### Mixtures over pattern pairs, with the truncation events as a case split -/

section Mixture

variable {X : Type*} [MeasurableSpace X] {P : Type*} [Fintype P] [DecidableEq P]

/-- The marginals of a finite mixture of couplings are the mixtures of the marginals. -/
theorem map_sum_smul {Y : Type*} [MeasurableSpace Y] (w : P → ℝ≥0∞) (π : P → Measure (X × X)) {f : X × X → Y}
    (hf : Measurable f) : (∑ p, w p • π p).map f = ∑ p, w p • (π p).map f := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.finsetSum_apply, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Measure.smul_apply, Measure.smul_apply, Measure.map_apply hf hs]

/-- `(Σ_p w_p • π_p)(s)` in real numbers, for weights `≤ 1` and probability measures. -/
theorem real_sum_smul (w : P → ℝ≥0∞) (hw : ∀ p, w p ≤ 1) (π : P → Measure (X × X))
    [∀ p, IsProbabilityMeasure (π p)] (s : Set (X × X)) :
    (∑ p, w p • π p).real s = ∑ p, (w p).toReal * (π p).real s := by
  rw [measureReal_def, Measure.finsetSum_apply, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, measureReal_def]
  · intro p _
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ((hw p).trans_lt ENNReal.one_lt_top).ne (measure_ne_top _ _)

theorem isProbabilityMeasure_sum_smul (w : P → ℝ≥0∞) (hw : ∑ p, w p = 1) (π : P → Measure (X × X))
    [∀ p, IsProbabilityMeasure (π p)] : IsProbabilityMeasure (∑ p, w p • π p) := by
  constructor
  rw [Measure.finsetSum_apply]
  simp [hw]

/-- **The case split** (`UV-TV.md` 33.1). For a finite mixture of couplings `Π = Σ_p w_p π_p` and any event `bad`,
`Π(bad) ≤ w(E) + Σ_{p ∉ E} w_p π_p(bad)`. -/
theorem real_mixture_le (w : P → ℝ≥0∞) (hw : ∀ p, w p ≤ 1) (π : P → Measure (X × X))
    [∀ p, IsProbabilityMeasure (π p)] (E : Finset P) (bad : Set (X × X)) :
    (∑ p, w p • π p).real bad ≤
      ∑ p ∈ E, (w p).toReal + ∑ p ∈ univ \ E, (w p).toReal * (π p).real bad := by
  rw [real_sum_smul w hw π bad, ← Finset.sum_sdiff (Finset.subset_univ E), add_comm]
  gcongr with p hp
  calc (w p).toReal * (π p).real bad ≤ (w p).toReal * 1 :=
        mul_le_mul_of_nonneg_left measureReal_le_one ENNReal.toReal_nonneg
    _ = (w p).toReal := mul_one _

end Mixture

/-! ### One scale with patterns and truncation -/

section Front

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The event "the two copies differ somewhere on `T`". -/
def differOn (T : Finset ι) : Set ((ι → S) × (ι → S)) := ⋃ x ∈ T, disagree x

theorem real_differOn_le (π : Measure ((ι → S) × (ι → S))) [IsFiniteMeasure π] (T : Finset ι) :
    π.real (differOn T) ≤ ∑ x ∈ T, π.real (disagree (S := S) x) :=
  measureReal_biUnion_finset_le T _

theorem measurableSet_differOn [MeasurableEq S] (T : Finset ι) : MeasurableSet (differOn (S := S) T) :=
  Finset.measurableSet_biUnion T fun x _ => measurableSet_disagree x

/-- The per-pattern bound of `scale_front`. -/
def frontBound {μ μ' : Measure (ι → S)} {β : Type*} [Fintype β] [DecidableEq β] (H : ScaleHyp μ μ' β)
    (T : Finset ι) (a ε : ℝ) : ℝ :=
  T.card * (H.nSrc * Real.exp (-(H.lam * a)) / ((1 - H.γ) * H.cmin) + ε)

/-- **One scale of UV-TV, with patterns and truncation** (`UV-TV.md` 30.2 with 33.1).

The scale-`j` laws are the mixtures `Σ_p w_p μ_p` and `Σ_p w_p μ'_p` over a finite set of pattern pairs `p` (the
weights `w` are the law of the H1 pattern coupling). `E` is the truncation set: nothing is assumed there. Off `E`, the
pattern pair has its one-scale hypotheses `H p` (blocks `β p` may depend on `p`: good boxes, composite boxes, sources),
and every source site is at distance `≥ a` from the target `T`. Then the mixtures have a coupling `Π` with
`Π(the copies differ on T) ≤ w(E) + Σ_{p ∉ E} w_p |T| (n_src,p e^{-λ_p a}/((1 - γ_p) c_min,p) + ε)`. -/
theorem scale_front [MeasurableEq S] (w : P → ℝ≥0∞) (hw : ∑ p, w p = 1) (μ μ' : P → Measure (ι → S))
    [∀ p, IsProbabilityMeasure (μ p)] [∀ p, IsProbabilityMeasure (μ' p)]
    (β : P → Type*) [∀ p, Fintype (β p)] [∀ p, DecidableEq (β p)] [∀ p, Nonempty (β p)]
    (E : Finset P) (H : ∀ p, p ∉ E → ScaleHyp (μ p) (μ' p) (β p))
    (T : Finset ι) {a : ℝ}
    (hsep : ∀ p (hp : p ∉ E), ∀ b ∉ (H p hp).good, ∀ y ∈ (H p hp).C.B b, ∀ x ∈ T, a ≤ (H p hp).dist y x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ πm : Measure ((ι → S) × (ι → S)), IsProbabilityMeasure πm ∧
      πm.map Prod.fst = ∑ p, w p • μ p ∧ πm.map Prod.snd = ∑ p, w p • μ' p ∧
      πm.real (differOn T) ≤
        ∑ p ∈ E, (w p).toReal +
          ∑ p ∈ univ \ E, (w p).toReal * (if hp : p ∈ E then 0 else frontBound (H p hp) T a ε) := by
  classical
  have hw1 : ∀ p, w p ≤ 1 := fun p => by
    rw [← hw]; exact Finset.single_le_sum (fun q _ => zero_le) (Finset.mem_univ p)
  -- the coupling for each pattern pair
  have hex : ∀ p (hp : p ∉ E), ∃ π, (H p hp).C.IsSuppCoupling π ∧
      ∑ x ∈ T, π.real (disagree x) ≤ frontBound (H p hp) T a ε :=
    fun p hp => (H p hp).exists_coupling_target T (hsep p hp) hε
  let π : P → Measure ((ι → S) × (ι → S)) := fun p =>
    if hp : p ∈ E then (μ p).prod (μ' p) else Classical.choose (hex p hp)
  have hπ : ∀ p, IsProbabilityMeasure (π p) ∧ (π p).map Prod.fst = μ p ∧ (π p).map Prod.snd = μ' p := by
    intro p
    by_cases hp : p ∈ E
    · simp only [π, hp, dite_true]
      refine ⟨inferInstance, ?_, ?_⟩
      · rw [← Measure.fst, Measure.fst_prod]
      · rw [← Measure.snd, Measure.snd_prod]
    · simp only [π, hp, dite_false]
      have hs := (Classical.choose_spec (hex p hp)).1
      exact ⟨hs.isProbabilityMeasure, hs.fst, hs.snd⟩
  have : ∀ p, IsProbabilityMeasure (π p) := fun p => (hπ p).1
  refine ⟨∑ p, w p • π p, isProbabilityMeasure_sum_smul w hw π, ?_, ?_, ?_⟩
  · rw [map_sum_smul w π measurable_fst]
    exact Finset.sum_congr rfl fun p _ => by rw [(hπ p).2.1]
  · rw [map_sum_smul w π measurable_snd]
    exact Finset.sum_congr rfl fun p _ => by rw [(hπ p).2.2]
  · refine (real_mixture_le w hw1 π E (differOn T)).trans ?_
    gcongr with p hp
    have hpE : p ∉ E := (Finset.mem_sdiff.mp hp).2
    simp only [hpE, dite_false]
    refine (real_differOn_le (π p) T).trans ?_
    simp only [π, hpE, dite_false]
    exact (Classical.choose_spec (hex p hpE)).2

/-- `|F(σ) - F(σ')| ≤ 2M` on the event "differ on `T`", and `0` off it, for `F` depending only on `T`. -/
theorem abs_integral_sub_le_differOn [MeasurableEq S] {μ μ' : Measure (ι → S)} {π : Measure ((ι → S) × (ι → S))}
    [IsProbabilityMeasure π] (hfst : π.map Prod.fst = μ) (hsnd : π.map Prod.snd = μ') (T : Finset ι)
    {F : (ι → S) → ℝ} (hF : Measurable F) {M : ℝ} (hFM : ∀ σ, |F σ| ≤ M)
    (hdep : ∀ σ σ' : ι → S, (∀ x ∈ T, σ x = σ' x) → F σ = F σ') :
    |∫ σ, F σ ∂μ - ∫ σ, F σ ∂μ'| ≤ 2 * M * π.real (differOn T) := by
  obtain ⟨p₀, -⟩ := nonempty_of_measure_ne_zero (μ := π) (s := Set.univ) (by simp)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hFM p₀.1)
  have hint : ∀ g : (ι → S) × (ι → S) → ι → S, Measurable g → Integrable (fun p => F (g p)) π :=
    fun g hg => Integrable.of_bound (C := M) (hF.comp hg).aestronglyMeasurable
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hFM _)
  rw [← hfst, ← hsnd, integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable hF.aestronglyMeasurable,
    ← integral_sub (hint _ measurable_fst) (hint _ measurable_snd)]
  have hpt : ∀ p : (ι → S) × (ι → S), |F p.1 - F p.2| ≤ (differOn T).indicator (fun _ => 2 * M) p := by
    intro p
    by_cases hall : ∀ x ∈ T, p.1 x = p.2 x
    · rw [hdep _ _ hall, sub_self, abs_zero]
      exact Set.indicator_nonneg (fun _ _ => by linarith) _
    · have hp : p ∈ differOn T := by
        push Not at hall
        obtain ⟨x, hxT, hx⟩ := hall
        exact Set.mem_biUnion hxT hx
      rw [Set.indicator_of_mem hp]
      have h1 := abs_le.mp (hFM p.1)
      have h2 := abs_le.mp (hFM p.2)
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  calc |∫ p, (F p.1 - F p.2) ∂π|
      ≤ ∫ p, |F p.1 - F p.2| ∂π := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := π) (fun p => F p.1 - F p.2)
    _ ≤ ∫ p, (differOn T).indicator (fun _ => 2 * M) p ∂π :=
        integral_mono ((hint _ measurable_fst).sub (hint _ measurable_snd)).abs
          ((integrable_const _).indicator (measurableSet_differOn T)) hpt
    _ = 2 * M * π.real (differOn T) := by
        rw [integral_indicator_const _ (measurableSet_differOn T), smul_eq_mul, mul_comm]

/-- **One scale, for observables** (`UV-TV.md` 30.2 with 33.1 and 28.1): for `F` bounded measurable and depending
only on `T`, `|∫ F d(Σ w μ) - ∫ F d(Σ w μ')| ≤ 2M (w(E) + Σ_{p ∉ E} w_p |T| (n_src,p e^{-λ_p a}/((1 - γ_p) c_min,p)
+ ε))`. -/
theorem scale_front_integral [MeasurableEq S] (w : P → ℝ≥0∞) (hw : ∑ p, w p = 1) (μ μ' : P → Measure (ι → S))
    [∀ p, IsProbabilityMeasure (μ p)] [∀ p, IsProbabilityMeasure (μ' p)]
    (β : P → Type*) [∀ p, Fintype (β p)] [∀ p, DecidableEq (β p)] [∀ p, Nonempty (β p)]
    (E : Finset P) (H : ∀ p, p ∉ E → ScaleHyp (μ p) (μ' p) (β p))
    (T : Finset ι) {a : ℝ}
    (hsep : ∀ p (hp : p ∉ E), ∀ b ∉ (H p hp).good, ∀ y ∈ (H p hp).C.B b, ∀ x ∈ T, a ≤ (H p hp).dist y x)
    {ε : ℝ} (hε : 0 < ε)
    {F : (ι → S) → ℝ} (hF : Measurable F) {M : ℝ} (hFM : ∀ σ, |F σ| ≤ M)
    (hdep : ∀ σ σ' : ι → S, (∀ x ∈ T, σ x = σ' x) → F σ = F σ') :
    |∫ σ, F σ ∂(∑ p, w p • μ p) - ∫ σ, F σ ∂(∑ p, w p • μ' p)| ≤
      2 * M * (∑ p ∈ E, (w p).toReal +
        ∑ p ∈ univ \ E, (w p).toReal * (if hp : p ∈ E then 0 else frontBound (H p hp) T a ε)) := by
  obtain ⟨πm, hπm, hfst, hsnd, hb⟩ := scale_front w hw μ μ' β E H T hsep hε
  obtain ⟨σ₀, -⟩ := nonempty_of_measure_ne_zero (μ := πm) (s := Set.univ) (by simp)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hFM σ₀.1)
  exact (abs_integral_sub_le_differOn hfst hsnd T hF hFM hdep).trans
    (mul_le_mul_of_nonneg_left hb (by linarith))

end Front

end ProofPhase.M1.UVTV
