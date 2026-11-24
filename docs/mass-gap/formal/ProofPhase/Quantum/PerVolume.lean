/-
Proof phase (round 5), workstream 3 (the quantum half): the per-volume gap theorem in one Lean theorem (2026-11-22).
Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/r3-wp/NOTE.md` (sections 1.2 and 1.4);
`docs/mass-gap/weak-coupling/proof-phase/ws3-quantum/NOTE.md` (this workstream).
-/

import ProofPhase.Quantum.LemmaT
import ProofPhase.Existence.Bridge
import Attempts.R3.WpNoise
import Attempts.R3.Robust

/-!
# The per-volume gap theorem: one noisy blocking step + D′ for every limit point at L₁

This file joins the three round-3 islands (review finding 2) for the per-volume route, **on the real objects**:
the SU(2) Wilson measures of a tuning (`ProofPhase.Existence.VTuning`, bare coupling `β_{k,j}` allowed to depend on the
volume), one noisy blocking step (`Attempts.R3.Wp`: compactness, the noise lemma), Lemma T(a) and the expectation bound
(`ProofPhase.Quantum.LemmaT`), and Dobrushin's theorem with weights for the limit (`Attempts.R3.decay_of_flatW`).

**The noisy blocking (`NoisyBlocking`).** In every volume `j`: a compact metric space `X j` of noisy block variables
(e.g. SU(2) links at an intermediate scale `L_p ≤ L₁`) with a reference probability measure, a compact metric space
`Y j` of *predictions*, a measurable prediction map of the fine SU(2) field at every level, a continuous noise kernel
`K_j(x, y) ≥ m_j > 0` (a density in `x`, normalised), and a measurable blocking `Ψ_j : X j → GaugeConnection SU2 4
(coarseSide j)` onto the SU(2) link variables at scale `L₁`. The noisy law at level `k` is `ρ_{k,j} · ref` with
`ρ_{k,j}(x) = ∫ K_j(x, pred(U)) dμ_{k,j}(U)` (`noisyLaw`, a probability measure: `isProbabilityMeasure_noisyLaw`), and
the **L₁ block law** is its image under `Ψ_j` (`l1Law`).

**The hypothesis (H2-all, `LimitDprimeAll`, open: the crossover).** Every mesh limit point `ν` of the prediction laws
(weak limit of a subsequence `k → ∞`, at fixed volume) gives an L₁ law that is the Gibbs measure, w.r.t. product Haar
measure on the coarse SU(2) links, of a potential satisfying D′_λ with one `γ < 1` (`linkDist` weights), the same `γ`, `λ`
for all volumes and all limit points.

**The theorem (`perVolumeGap`, substantive).** Then for every volume `j` and all block observables `f`, `g` of the L₁
variables (bounded measurable, depending on `A`, `S_g` at coarse distance `≥ R`), **every mesh limit point** of the
level-`k` covariance `Cov_{l1Law k j}(f, g)` satisfies `|h| ≤ (1 − γ)⁻¹ (∑_{a ∈ A} v_f(a)) L_g e^{-λR}`.
Order: mesh first (`k → ∞` at fixed `j`), then the volume (the constant does not depend on `j`), then the observable.
Proof: a mesh limit point is the limit along a subsequence; Prokhorov gives a further subsequence along which the
prediction laws converge weakly; the noise lemma (`Attempts.R3.Wp.noise_uniform`) makes the noisy densities converge in
relative sup norm, Lemma T(a) carries this through `Ψ_j`, and the expectation bound of `LemmaT` makes every bounded
measurable expectation converge; H2-all identifies the limit as a D′ Gibbs measure, and `decay_of_flatW` bounds its
covariance.
* `perVolumeGap_eventually`: the same as "eventually in `k`, up to any `ε > 0`" (the per-volume gap statement:
  `k₀` depends on the volume, the observables and `ε`).
* `exists_blockLimit` (**substantive, no open hypothesis**): one subsequence of levels along which, **in every volume at
  once**, the prediction laws converge and every bounded measurable expectation of the L₁ block law converges
  (Tychonoff + Prokhorov on `∏_j P(Y_j)`, the noise lemma, Lemma T). The block-level continuum limit at scale `L₁`
  exists in every volume, subsequentially; `blockLimit_gap` adds H2-all.

**What this is not.** (1) It does not give `SlabDecay` or `TorusDecay`: `k₀` depends on the volume (order mesh first),
and the observables are noisy L₁ block observables, not fine slab observables. (2) No Yang–Mills input beyond the
measures: the theorem holds for any family of laws with a noisy blocking; the photon passes because H2-all fails for it
(gapless limit), pure noise satisfies everything (it has a gap). (3) H2-all is the crossover itself (open).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Quantum

/-! ## Noisy laws (abstract) -/

section Mixture

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace Y] [MetricSpace Y] [CompactSpace Y] [BorelSpace Y]

/-- The noisy block density `ρ_ν(x) = ∫ K(x, y) dν(y)`. -/
def mixDens (K : X × Y → ℝ) (ν : ProbabilityMeasure Y) (x : X) : ℝ := ∫ y, K (x, y) ∂(ν : Measure Y)

/-- The noisy block law `ρ_ν · ref`. -/
def noisyLaw (ref : Measure X) (K : X × Y → ℝ) (ν : ProbabilityMeasure Y) : Measure X :=
  ref.withDensity fun x => ENNReal.ofReal (mixDens K ν x)

theorem mixDens_ge {K : X × Y → ℝ} (hK : Continuous K) {m : ℝ} (hKm : ∀ p, m ≤ K p) (ν : ProbabilityMeasure Y)
    (x : X) : m ≤ mixDens K ν x :=
  Attempts.R3.Wp.le_integral_of_forall_le _ (Attempts.R3.Wp.integrable_section _ hK x) fun y => hKm (x, y)

theorem exists_bound_kernel {K : X × Y → ℝ} (hK : Continuous K) : ∃ C, ∀ p, |K p| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := X × Y)).exists_bound_of_continuousOn hK.continuousOn
  exact ⟨C, fun p => by simpa [Real.norm_eq_abs] using hC p (Set.mem_univ _)⟩

theorem continuous_mixDens {K : X × Y → ℝ} (hK : Continuous K) (ν : ProbabilityMeasure Y) :
    Continuous (mixDens K ν) := by
  obtain ⟨C, hC⟩ := exists_bound_kernel hK
  refine continuous_of_dominated (bound := fun _ => C) (fun x => ?_) (fun x => ?_) (integrable_const C) ?_
  · exact (Attempts.R3.Wp.continuous_section hK x).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC (x, y)
  · exact Eventually.of_forall fun y => hK.comp (Continuous.prodMk continuous_id continuous_const)

theorem mixDens_le {K : X × Y → ℝ} (hK : Continuous K) {C : ℝ} (hC : ∀ p, |K p| ≤ C) (ν : ProbabilityMeasure Y)
    (x : X) : |mixDens K ν x| ≤ C := by
  unfold mixDens
  have := norm_integral_le_of_norm_le_const (μ := (ν : Measure Y)) (f := fun y => K (x, y)) (C := C)
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC (x, y))
  simpa [Real.norm_eq_abs] using this

/-- The noisy law of a normalised kernel is a probability measure (Fubini). -/
theorem isProbabilityMeasure_noisyLaw (ref : Measure X) [IsProbabilityMeasure ref] {K : X × Y → ℝ}
    (hK : Continuous K) {m : ℝ} (hm : 0 < m) (hKm : ∀ p, m ≤ K p) (hnorm : ∀ y, ∫ x, K (x, y) ∂ref = 1)
    (ν : ProbabilityMeasure Y) : IsProbabilityMeasure (noisyLaw ref K ν) := by
  obtain ⟨C, hC⟩ := exists_bound_kernel hK
  constructor
  unfold noisyLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : Integrable (mixDens K ν) ref :=
    Integrable.of_bound (continuous_mixDens hK ν).aestronglyMeasurable C
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact mixDens_le hK hC ν x)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun x => hm.le.trans (mixDens_ge hK hKm ν x))]
  have hKint : Integrable (Function.uncurry fun x y => K (x, y)) (ref.prod (ν : Measure Y)) :=
    Integrable.of_bound hK.aestronglyMeasurable C (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact hC p)
  unfold mixDens
  rw [integral_integral_swap hKint]
  simp [hnorm]

theorem isFiniteMeasure_noisyLaw (ref : Measure X) [IsFiniteMeasure ref] {K : X × Y → ℝ} (hK : Continuous K)
    (ν : ProbabilityMeasure Y) : IsFiniteMeasure (noisyLaw ref K ν) := by
  obtain ⟨C, hC⟩ := exists_bound_kernel hK
  exact isFiniteMeasure_withDensity_ofReal
    (Integrable.of_bound (continuous_mixDens hK ν).aestronglyMeasurable C
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact mixDens_le hK hC ν x)).hasFiniteIntegral

/-- **Noise lemma + Lemma T ⇒ convergence of every bounded measurable expectation of the blocked noisy laws.** If the
log-densities converge uniformly, then for every further measurable blocking `Ψ` and every bounded measurable `F`,
`∫ F d(Ψ_* noisyLaw(ν_n)) → ∫ F d(Ψ_* noisyLaw(ν_∞))`. -/
theorem tendsto_integral_blocked (ref : Measure X) [IsFiniteMeasure ref] {K : X × Y → ℝ} (hK : Continuous K)
    {m : ℝ} (hm : 0 < m) (hKm : ∀ p, m ≤ K p) (ν : ℕ → ProbabilityMeasure Y) (νinf : ProbabilityMeasure Y)
    (hu : TendstoUniformly (fun n x => Real.log (mixDens K (ν n) x)) (fun x => Real.log (mixDens K νinf x)) atTop)
    {Z : Type*} [MeasurableSpace Z] {Ψ : X → Z} (hΨ : Measurable Ψ) {F : Z → ℝ} (hF : Measurable F) {M : ℝ}
    (hM : ∀ z, |F z| ≤ M) :
    Tendsto (fun n => ∫ z, F z ∂((noisyLaw ref K (ν n)).map Ψ)) atTop
      (𝓝 (∫ z, F z ∂((noisyLaw ref K νinf).map Ψ))) := by
  have := isFiniteMeasure_noisyLaw ref hK νinf
  set A := ∫ z, |F z| ∂((noisyLaw ref K νinf).map Ψ)
  have hA : 0 ≤ A := integral_nonneg fun z => abs_nonneg _
  have hpos : ∀ (μ : ProbabilityMeasure Y) x, 0 < mixDens K μ x := fun μ x => hm.trans_le (mixDens_ge hK hKm μ x)
  -- closeness for every `ε > 0`, eventually
  have hclose : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      |∫ z, F z ∂((noisyLaw ref K (ν n)).map Ψ) - ∫ z, F z ∂((noisyLaw ref K νinf).map Ψ)| ≤
        (Real.exp ε - 1) * A := by
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.1 hu ε hε] with n hn
    have hrc : RelClose ε (noisyLaw ref K νinf) (noisyLaw ref K (ν n)) :=
      relClose_withDensity_log ref (hpos νinf) (hpos (ν n)) fun x => by
        have := hn x; rw [Real.dist_eq] at this; exact this.le
    exact abs_integral_sub_le_of_relClose (hrc.map hΨ) hF hM
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set ε := min 1 (δ / (4 * (A + 1))) with hεdef
  have hε : 0 < ε := lt_min one_pos (by positivity)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hclose ε hε)
  refine ⟨n₀, fun n hn => ?_⟩
  rw [Real.dist_eq]
  have h1 := hn₀ n hn
  have hexp : Real.exp ε - 1 ≤ 2 * ε := by
    have := Real.abs_exp_sub_one_le (x := ε) (by rw [abs_of_pos hε]; exact min_le_left _ _)
    rw [abs_of_pos hε] at this
    exact (le_abs_self _).trans this
  have hεA : 2 * ε * A < δ := by
    have h2 : ε ≤ δ / (4 * (A + 1)) := min_le_right _ _
    have h3 : 2 * ε * A ≤ 2 * (δ / (4 * (A + 1))) * A := by gcongr
    have h4 : 2 * (δ / (4 * (A + 1))) * A < δ := by
      rw [show 2 * (δ / (4 * (A + 1))) * A = δ * (A / (2 * (A + 1))) by field_simp; ring]
      have : A / (2 * (A + 1)) < 1 := by rw [div_lt_one (by positivity)]; linarith
      nlinarith
    linarith
  have hexpA : (Real.exp ε - 1) * A ≤ 2 * ε * A := mul_le_mul_of_nonneg_right hexp hA
  linarith

end Mixture

/-! ## Covariances -/

/-- The covariance of `f, g` under `μ`. -/
def cov {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (f g : Z → ℝ) : ℝ :=
  ∫ z, f z * g z ∂μ - (∫ z, f z ∂μ) * ∫ z, g z ∂μ

/-! ## The noisy blocking of the SU(2) Wilson family -/

open ProofPhase.Existence

theorem ym_isProb (V : VTuning) (k j : ℕ) : IsProbabilityMeasure (V.ym k j) :=
  isProbabilityMeasure_gaugeMeasure (d := 4) (N := V.T.side k j) continuous_subtype_val
    (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) (posWeight_wilson 2 (V.βv k j))

/-- **A noisy blocking of the SU(2) Wilson family `V` down to `L₁`, volume by volume** (see the module docstring). -/
structure NoisyBlocking (V : VTuning) (X Y : ℕ → Type*) [∀ j, MetricSpace (X j)] [∀ j, MeasurableSpace (X j)]
    [∀ j, MetricSpace (Y j)] [∀ j, MeasurableSpace (Y j)] where
  ref : ∀ j, Measure (X j)
  ref_prob : ∀ j, IsProbabilityMeasure (ref j)
  K : ∀ j, X j × Y j → ℝ
  K_cont : ∀ j, Continuous (K j)
  K_low : ∀ j, ∃ m : ℝ, 0 < m ∧ ∀ p, m ≤ K j p
  K_norm : ∀ j y, ∫ x, K j (x, y) ∂(ref j) = 1
  pred : ∀ k j, GaugeConnection SU2 4 (V.T.side k j) → Y j
  pred_meas : ∀ k j, Measurable (pred k j)
  Ψ : ∀ j, X j → GaugeConnection SU2 4 (coarseSide j)
  Ψ_meas : ∀ j, Measurable (Ψ j)

namespace NoisyBlocking

variable {V : VTuning} {X Y : ℕ → Type*} [∀ j, MetricSpace (X j)] [∀ j, CompactSpace (X j)]
  [∀ j, MeasurableSpace (X j)] [∀ j, BorelSpace (X j)] [∀ j, MetricSpace (Y j)] [∀ j, CompactSpace (Y j)]
  [∀ j, MeasurableSpace (Y j)] [∀ j, BorelSpace (Y j)] (NB : NoisyBlocking V X Y)

/-- The law of the prediction at level `k`, volume `j`: the image of the SU(2) Wilson measure. -/
def predLaw (k j : ℕ) : ProbabilityMeasure (Y j) :=
  ⟨(V.ym k j).map (NB.pred k j), by
    have := ym_isProb V k j; exact (Measure.isProbabilityMeasure_map_iff (NB.pred_meas k j).aemeasurable).2 this⟩

/-- The L₁ block law of the limit theory with prediction law `ν`. -/
def l1LawOf (j : ℕ) (ν : ProbabilityMeasure (Y j)) : Measure (GaugeConnection SU2 4 (coarseSide j)) :=
  (noisyLaw (NB.ref j) (NB.K j) ν).map (NB.Ψ j)

/-- **The L₁ block law at level `k`, volume `j`** (one noisy step, then the blocking `Ψ_j`). -/
def l1Law (k j : ℕ) : Measure (GaugeConnection SU2 4 (coarseSide j)) := NB.l1LawOf j (NB.predLaw k j)

theorem isProb_l1LawOf (j : ℕ) (ν : ProbabilityMeasure (Y j)) : IsProbabilityMeasure (NB.l1LawOf j ν) := by
  obtain ⟨m, hm, hKm⟩ := NB.K_low j
  have := NB.ref_prob j
  have := isProbabilityMeasure_noisyLaw (NB.ref j) (NB.K_cont j) hm hKm (NB.K_norm j) ν
  unfold l1LawOf; infer_instance

/-- `ν` is a **mesh limit point** of the prediction laws in volume `j`. -/
def IsMeshLimit (j : ℕ) (ν : ProbabilityMeasure (Y j)) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => NB.predLaw (φ n) j) atTop (𝓝 ν)

/-- **H2-all (open; the crossover at L₁, per-volume form).** Every mesh limit point gives an L₁ law that is the Gibbs
measure (w.r.t. product Haar on the coarse SU(2) links) of a potential satisfying D′_λ with the same `γ` in every
volume. -/
def LimitDprimeAll (lam γ : ℝ) : Prop :=
  ∀ (j : ℕ) (ν : ProbabilityMeasure (Y j)), NB.IsMeshLimit j ν →
    ∃ Vinf : CoarsePot j, Attempts.R3.Potential (fun A => A) Vinf ∧
      ∃ Sb : LatticeLink 4 (coarseSide j) → LatticeLink 4 (coarseSide j) → ℝ,
        Attempts.R3.PairOsc (fun A => A) Vinf Sb ∧ Attempts.R3.FlatCriterionW linkDist lam Sb γ ∧
        NB.l1LawOf j ν = Attempts.R3.gibbsMeasure (haarG SU2) Vinf

variable [∀ j, TopologicalSpace.SeparableSpace (Y j)]

/-- Along a weakly convergent subsequence of prediction laws, the noisy log-densities converge uniformly. -/
theorem uniform_of_tendsto (j : ℕ) {ν : ℕ → ProbabilityMeasure (Y j)} {νinf : ProbabilityMeasure (Y j)}
    (h : Tendsto ν atTop (𝓝 νinf)) :
    TendstoUniformly (fun n x => Real.log (mixDens (NB.K j) (ν n) x))
      (fun x => Real.log (mixDens (NB.K j) νinf x)) atTop := by
  obtain ⟨m, hm, hKm⟩ := NB.K_low j
  have hconst : TendstoUniformly (fun _ : ℕ => NB.K j) (NB.K j) atTop :=
    Metric.tendstoUniformly_iff.2 fun ε hε => Eventually.of_forall fun _ x => by simpa using hε
  exact Attempts.R3.Wp.noise_uniform (fun _ => NB.K j) (NB.K j) (fun _ => NB.K_cont j) (NB.K_cont j) hconst hm
    (fun _ => hKm) hKm ν νinf h

/-- Along a weakly convergent subsequence of prediction laws, every bounded measurable expectation of the L₁ block
law converges to that of the limit theory. -/
theorem tendsto_integral_l1 (j : ℕ) {φ : ℕ → ℕ} {νinf : ProbabilityMeasure (Y j)}
    (h : Tendsto (fun n => NB.predLaw (φ n) j) atTop (𝓝 νinf)) {F : GaugeConnection SU2 4 (coarseSide j) → ℝ}
    (hF : Measurable F) {M : ℝ} (hM : ∀ z, |F z| ≤ M) :
    Tendsto (fun n => ∫ z, F z ∂(NB.l1Law (φ n) j)) atTop (𝓝 (∫ z, F z ∂(NB.l1LawOf j νinf))) := by
  obtain ⟨m, hm, hKm⟩ := NB.K_low j
  have := NB.ref_prob j
  exact tendsto_integral_blocked (NB.ref j) (NB.K_cont j) hm hKm _ νinf (NB.uniform_of_tendsto j h)
    (NB.Ψ_meas j) hF hM

theorem tendsto_cov_l1 (j : ℕ) {φ : ℕ → ℕ} {νinf : ProbabilityMeasure (Y j)}
    (h : Tendsto (fun n => NB.predLaw (φ n) j) atTop (𝓝 νinf)) {f g : GaugeConnection SU2 4 (coarseSide j) → ℝ}
    (hf : BM f) (hg : BM g) :
    Tendsto (fun n => cov (NB.l1Law (φ n) j) f g) atTop (𝓝 (cov (NB.l1LawOf j νinf) f g)) := by
  obtain ⟨Mf, hMf⟩ := hf.bdd
  obtain ⟨Mg, hMg⟩ := hg.bdd
  have hfg : ∀ z, |f z * g z| ≤ Mf * Mg := fun z => by
    rw [abs_mul]; exact mul_le_mul (hMf z) (hMg z) (abs_nonneg _) ((abs_nonneg _).trans (hMf z))
  exact (NB.tendsto_integral_l1 j h (hf.meas.mul hg.meas) hfg).sub
    ((NB.tendsto_integral_l1 j h hf.meas hMf).mul (NB.tendsto_integral_l1 j h hg.meas hMg))

/-- **The per-volume gap theorem (order mesh → volume → observable).** Under H2-all, in every volume `j`, every mesh
limit point of the level-`k` L₁ block covariance of `f`, `g` (bounded measurable, depending on `A`, `S_g`, at coarse
distance `≥ R`) is at most `(1 − γ)⁻¹ (∑_{a ∈ A} v_f(a)) L_g e^{-λR}`: the constant does not depend on the volume. -/
theorem perVolumeGap {lam γ : ℝ} (hlam : 0 ≤ lam) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hH2 : NB.LimitDprimeAll lam γ)
    (j : ℕ) {f g : GaugeConnection SU2 4 (coarseSide j) → ℝ} {A Sg : Finset (LatticeLink 4 (coarseSide j))}
    {vf : LatticeLink 4 (coarseSide j) → ℝ} {Lg R : ℝ} (hf : BM f) (hg : BM g) (hfA : DepOn f A)
    (hgS : DepOn g Sg) (hvf : OscBound f vf) (hLg : 0 ≤ Lg) (hvg : OscBound g (fun _ => Lg))
    (hR : ∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) {h : ℝ} (hh : IsLimitPoint (fun k => cov (NB.l1Law k j) f g) h) :
    |h| ≤ (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)) := by
  obtain ⟨φ, hφ, hlim⟩ := hh
  obtain ⟨νinf, -, ψ, hψ, hν⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (ProbabilityMeasure (Y j)))).tendsto_subseq
      (fun n => Set.mem_univ (NB.predLaw (φ n) j))
  have hν' : Tendsto (fun n => NB.predLaw ((φ ∘ ψ) n) j) atTop (𝓝 νinf) := hν
  have h1 := NB.tendsto_cov_l1 j hν' hf hg
  have h2 : Tendsto (fun n => cov (NB.l1Law ((φ ∘ ψ) n) j) f g) atTop (𝓝 h) := hlim.comp hψ.tendsto_atTop
  have hh : h = cov (NB.l1LawOf j νinf) f g := tendsto_nhds_unique h2 h1
  obtain ⟨Vinf, hpot, Sb, hpair, hflat, heq⟩ := hH2 j νinf ⟨φ ∘ ψ, hφ.comp hψ, hν'⟩
  have : Nonempty (LatticeLink 4 (coarseSide j)) := ⟨⟨fun _ => 0, 0⟩⟩
  rw [hh, cov, heq]
  exact Attempts.R3.decay_of_flatW (haarG SU2) hpot hpair linkDist linkDist_self linkDist_triangle hlam hγ0 hγ1
    hflat hf hg hfA hgS hvf hLg hvg hR

theorem abs_cov_le {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ] {f g : Z → ℝ}
    {Mf Mg : ℝ} (hMf : ∀ z, |f z| ≤ Mf) (hMg : ∀ z, |g z| ≤ Mg) : |cov μ f g| ≤ 2 * (Mf * Mg) := by
  have i1 : |∫ z, f z * g z ∂μ| ≤ Mf * Mg := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun z => f z * g z) (C := Mf * Mg)
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hMf z) (hMg z) (abs_nonneg _) ((abs_nonneg _).trans (hMf z)))
    simpa using this
  have i2 : |∫ z, f z ∂μ| ≤ Mf := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := Mf)
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hMf z)
    simpa using this
  have i3 : |∫ z, g z ∂μ| ≤ Mg := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := Mg)
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hMg z)
    simpa using this
  unfold cov
  calc _ ≤ |∫ z, f z * g z ∂μ| + |(∫ z, f z ∂μ) * ∫ z, g z ∂μ| := abs_sub _ _
    _ ≤ Mf * Mg + Mf * Mg := by
        rw [abs_mul]
        exact add_le_add i1 (mul_le_mul i2 i3 (abs_nonneg _) ((abs_nonneg _).trans i2))
    _ = 2 * (Mf * Mg) := by ring

/-- **The per-volume gap theorem, eventually form.** Under H2-all: in every volume, for all block observables as in
`perVolumeGap` and every `ε > 0`, from some level `k₀(j, f, g, ε)` on,
`|Cov_{l1Law k j}(f, g)| ≤ (1 − γ)⁻¹ (∑ v_f) L_g e^{-λR} + ε`. -/
theorem perVolumeGap_eventually {lam γ : ℝ} (hlam : 0 ≤ lam) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hH2 : NB.LimitDprimeAll lam γ) (j : ℕ) {f g : GaugeConnection SU2 4 (coarseSide j) → ℝ}
    {A Sg : Finset (LatticeLink 4 (coarseSide j))} {vf : LatticeLink 4 (coarseSide j) → ℝ} {Lg R : ℝ}
    (hf : BM f) (hg : BM g) (hfA : DepOn f A) (hgS : DepOn g Sg) (hvf : OscBound f vf) (hLg : 0 ≤ Lg)
    (hvg : OscBound g (fun _ => Lg)) (hR : ∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, |cov (NB.l1Law k j) f g| ≤ (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)) + ε := by
  set b := (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R))
  by_contra hne
  rw [not_eventually] at hne
  obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop hne
  obtain ⟨Mf, hMf⟩ := hf.bdd
  obtain ⟨Mg, hMg⟩ := hg.bdd
  have hbd : ∀ n, cov (NB.l1Law (φ n) j) f g ∈ Metric.closedBall (0 : ℝ) (2 * (Mf * Mg)) := fun n => by
    have := NB.isProb_l1LawOf j (NB.predLaw (φ n) j)
    change IsProbabilityMeasure (NB.l1LawOf j (NB.predLaw (φ n) j)) at this
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    exact @abs_cov_le _ _ (NB.l1Law (φ n) j) this _ _ _ _ hMf hMg
  obtain ⟨a, -, ψ, hψ, ha⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hbd
  have hlp : IsLimitPoint (fun k => cov (NB.l1Law k j) f g) a := ⟨φ ∘ ψ, hφ.comp hψ, ha⟩
  have hle := NB.perVolumeGap hlam hγ0 hγ1 hH2 j hf hg hfA hgS hvf hLg hvg hR hlp
  have hge : b + ε ≤ |a| :=
    ge_of_tendsto ha.abs (Eventually.of_forall fun n => (lt_of_not_ge (hP (ψ n))).le)
  linarith

/-- **The block-level mesh limit exists in every volume at once (no open hypothesis).** There is one subsequence of
levels `φ` and limit prediction laws `ν_j` such that, in every volume `j`, the prediction laws converge weakly and every
bounded measurable expectation of the L₁ block law converges to that of the limit theory `l1LawOf j ν_j`. -/
theorem exists_blockLimit :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ νinf : ∀ j, ProbabilityMeasure (Y j), ∀ j,
      Tendsto (fun n => NB.predLaw (φ n) j) atTop (𝓝 (νinf j)) ∧
      ∀ (F : GaugeConnection SU2 4 (coarseSide j) → ℝ), Measurable F → ∀ M, (∀ z, |F z| ≤ M) →
        Tendsto (fun n => ∫ z, F z ∂(NB.l1Law (φ n) j)) atTop (𝓝 (∫ z, F z ∂(NB.l1LawOf j (νinf j)))) := by
  obtain ⟨νinf, -, φ, hφ, hν⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (∀ j, ProbabilityMeasure (Y j)))).tendsto_subseq
      (fun n => Set.mem_univ (fun j => NB.predLaw n j))
  refine ⟨φ, hφ, νinf, fun j => ?_⟩
  have hj : Tendsto (fun n => NB.predLaw (φ n) j) atTop (𝓝 (νinf j)) := (continuous_apply j).tendsto _ |>.comp hν
  exact ⟨hj, fun F hF M hM => NB.tendsto_integral_l1 j hj hF hM⟩

/-- **The block-level continuum limit has the gap at L₁, uniformly in the volume, under H2-all.** Along the subsequence
of `exists_blockLimit`, in every volume, the limit theory's block covariances obey the D′ bound with one constant. -/
theorem blockLimit_gap {lam γ : ℝ} (hlam : 0 ≤ lam) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hH2 : NB.LimitDprimeAll lam γ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ νinf : ∀ j, ProbabilityMeasure (Y j), ∀ j,
      (∀ {f g : GaugeConnection SU2 4 (coarseSide j) → ℝ}, BM f → BM g →
        Tendsto (fun n => cov (NB.l1Law (φ n) j) f g) atTop (𝓝 (cov (NB.l1LawOf j (νinf j)) f g))) ∧
      ∀ {f g : GaugeConnection SU2 4 (coarseSide j) → ℝ} {A Sg : Finset (LatticeLink 4 (coarseSide j))}
        {vf : LatticeLink 4 (coarseSide j) → ℝ} {Lg R : ℝ}, BM f → BM g → DepOn f A → DepOn g Sg →
        OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) → (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
        |cov (NB.l1LawOf j (νinf j)) f g| ≤ (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)) := by
  obtain ⟨φ, hφ, νinf, h⟩ := NB.exists_blockLimit
  refine ⟨φ, hφ, νinf, fun j => ⟨fun hf hg => NB.tendsto_cov_l1 j (h j).1 hf hg, ?_⟩⟩
  intro f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR
  have hc := NB.tendsto_cov_l1 j (h j).1 hf hg
  exact NB.perVolumeGap hlam hγ0 hγ1 hH2 j hf hg hfA hgS hvf hLg hvg hR ⟨φ, hφ, hc⟩

end NoisyBlocking

end ProofPhase.Quantum
