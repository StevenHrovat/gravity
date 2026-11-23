/-
Proof phase, generalisation phase 1: the per-volume gap theorem for noisy blockings of the Wilson family of any gauge
group in any dimension (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`.
-/

import ProofPhase.Quantum.PerVolume
import ProofPhase.General.GaugeGroup
import ProofPhase.General.SU2Instance

/-!
# The per-volume gap theorem, for any gauge group and dimension

The abstract part of `ProofPhase.Quantum.PerVolume` (`mixDens`, `noisyLaw`, `tendsto_integral_blocked`, `cov`,
`abs_cov_le`, ...) is group-free and reused as it is. The Yang-Mills layer (`NoisyBlocking`, its laws, `LimitDprimeAll`,
`perVolumeGap`, `perVolumeGap_eventually`, `exists_blockLimit`, `blockLimit_gap`) is restated for the Wilson family of a
gauge group `G` of the package in dimension `d`, with the volume-dependent coupling of a `VTuning`. The old SU(2),
`d = 4` statements are re-derived at the end with the same types (the old structure is converted field by field).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity

open ProofPhase.Quantum (mixDens noisyLaw isProbabilityMeasure_noisyLaw tendsto_integral_blocked cov)

open scoped Classical

set_option linter.unusedSectionVars false

universe u v

noncomputable section

namespace ProofPhase.General

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [HasHaarProbability G]
  (n : ℕ) [HasGaugeTrace G n] [GaugeGroupBase G] [GaugeRep G n] {d : ℕ} [NeZero d]

/-- The Wilson measure of `G` at level `k`, torus `j`, with the volume-dependent coupling of `V`. -/
abbrev vmLaw (d : ℕ) (V : ProofPhase.Existence.VTuning) (k j : ℕ) : Measure (GaugeConnection G d (V.T.side k j)) :=
  wilsonMeasure G n (V.βv k j) d (V.T.side k j)

theorem vmLaw_isProb (d : ℕ) (V : ProofPhase.Existence.VTuning) (k j : ℕ) :
    IsProbabilityMeasure (vmLaw (G := G) n d V k j) :=
  isProbabilityMeasure_wilsonMeasure (G := G) (n := n) d (V.T.side k j) (V.βv k j)

end Generic

/-- **A noisy blocking of the Wilson family `V` of `G` down to `L₁`, volume by volume.** -/
structure NoisyBlocking (G : Type*) [Group G] [MeasurableSpace G] (d : ℕ) [NeZero d]
    (V : ProofPhase.Existence.VTuning) (X Y : ℕ → Type*) [∀ j, MetricSpace (X j)] [∀ j, MeasurableSpace (X j)]
    [∀ j, MetricSpace (Y j)] [∀ j, MeasurableSpace (Y j)] where
  ref : ∀ j, Measure (X j)
  ref_prob : ∀ j, IsProbabilityMeasure (ref j)
  K : ∀ j, X j × Y j → ℝ
  K_cont : ∀ j, Continuous (K j)
  K_low : ∀ j, ∃ m : ℝ, 0 < m ∧ ∀ p, m ≤ K j p
  K_norm : ∀ j y, ∫ x, K j (x, y) ∂(ref j) = 1
  pred : ∀ k j, GaugeConnection G d (V.T.side k j) → Y j
  pred_meas : ∀ k j, Measurable (pred k j)
  Ψ : ∀ j, X j → GaugeConnection G d (ProofPhase.coarseSide j)
  Ψ_meas : ∀ j, Measurable (Ψ j)

namespace NoisyBlocking

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [HasHaarProbability G]
  (n : ℕ) [HasGaugeTrace G n] [GaugeGroupBase G] [GaugeRep G n] {d : ℕ} [NeZero d]
  {V : ProofPhase.Existence.VTuning} {X Y : ℕ → Type*} [∀ j, MetricSpace (X j)] [∀ j, CompactSpace (X j)]
  [∀ j, MeasurableSpace (X j)] [∀ j, BorelSpace (X j)] [∀ j, MetricSpace (Y j)] [∀ j, CompactSpace (Y j)]
  [∀ j, MeasurableSpace (Y j)] [∀ j, BorelSpace (Y j)] (NB : NoisyBlocking G d V X Y)

/-- The law of the prediction at level `k`, volume `j`: the image of the Wilson measure. -/
def predLaw (k j : ℕ) : ProbabilityMeasure (Y j) :=
  ⟨(vmLaw (G := G) n d V k j).map (NB.pred k j), by
    have := vmLaw_isProb (G := G) n d V k j
    exact (Measure.isProbabilityMeasure_map_iff (NB.pred_meas k j).aemeasurable).2 this⟩

/-- The L₁ block law of the limit theory with prediction law `ν`. -/
def l1LawOf (j : ℕ) (ν : ProbabilityMeasure (Y j)) : Measure (GaugeConnection G d (ProofPhase.coarseSide j)) :=
  (noisyLaw (NB.ref j) (NB.K j) ν).map (NB.Ψ j)

/-- **The L₁ block law at level `k`, volume `j`** (one noisy step, then the blocking `Ψ_j`). -/
def l1Law (k j : ℕ) : Measure (GaugeConnection G d (ProofPhase.coarseSide j)) :=
  NB.l1LawOf j (NB.predLaw n k j)

theorem isProb_l1LawOf (j : ℕ) (ν : ProbabilityMeasure (Y j)) : IsProbabilityMeasure (NB.l1LawOf j ν) := by
  obtain ⟨m, hm, hKm⟩ := NB.K_low j
  have := NB.ref_prob j
  have := isProbabilityMeasure_noisyLaw (NB.ref j) (NB.K_cont j) hm hKm (NB.K_norm j) ν
  unfold l1LawOf; infer_instance

/-- `ν` is a **mesh limit point** of the prediction laws in volume `j`. -/
def IsMeshLimit (j : ℕ) (ν : ProbabilityMeasure (Y j)) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun m => NB.predLaw n (φ m) j) atTop (𝓝 ν)

/-- **H2-all (open; the crossover at L₁, per-volume form).** Every mesh limit point gives an L₁ law that is the Gibbs
measure (w.r.t. product Haar on the coarse links) of a potential satisfying D′_λ with the same `γ` in every volume. -/
def LimitDprimeAll (lam γ : ℝ) : Prop :=
  ∀ (j : ℕ) (ν : ProbabilityMeasure (Y j)), NB.IsMeshLimit n j ν →
    ∃ Vinf : Finset (LatticeLink d (ProofPhase.coarseSide j)) → GaugeConnection G d (ProofPhase.coarseSide j) → ℝ,
      Attempts.R3.Potential (fun A => A) Vinf ∧
      ∃ Sb : LatticeLink d (ProofPhase.coarseSide j) → LatticeLink d (ProofPhase.coarseSide j) → ℝ,
        Attempts.R3.PairOsc (fun A => A) Vinf Sb ∧ Attempts.R3.FlatCriterionW linkDist lam Sb γ ∧
        NB.l1LawOf j ν = Attempts.R3.gibbsMeasure (haarG G) Vinf

variable [∀ j, TopologicalSpace.SeparableSpace (Y j)]

/-- Along a weakly convergent subsequence of prediction laws, the noisy log-densities converge uniformly. -/
theorem uniform_of_tendsto (j : ℕ) {ν : ℕ → ProbabilityMeasure (Y j)} {νinf : ProbabilityMeasure (Y j)}
    (h : Tendsto ν atTop (𝓝 νinf)) :
    TendstoUniformly (fun m x => Real.log (mixDens (NB.K j) (ν m) x))
      (fun x => Real.log (mixDens (NB.K j) νinf x)) atTop := by
  obtain ⟨m, hm, hKm⟩ := NB.K_low j
  have hconst : TendstoUniformly (fun _ : ℕ => NB.K j) (NB.K j) atTop :=
    Metric.tendstoUniformly_iff.2 fun ε hε => Eventually.of_forall fun _ x => by simpa using hε
  exact Attempts.R3.Wp.noise_uniform (fun _ => NB.K j) (NB.K j) (fun _ => NB.K_cont j) (NB.K_cont j) hconst hm
    (fun _ => hKm) hKm ν νinf h

/-- Along a weakly convergent subsequence of prediction laws, every bounded measurable expectation of the L₁ block
law converges to that of the limit theory. -/
theorem tendsto_integral_l1 (j : ℕ) {φ : ℕ → ℕ} {νinf : ProbabilityMeasure (Y j)}
    (h : Tendsto (fun m => NB.predLaw n (φ m) j) atTop (𝓝 νinf))
    {F : GaugeConnection G d (ProofPhase.coarseSide j) → ℝ} (hF : Measurable F) {M : ℝ} (hM : ∀ z, |F z| ≤ M) :
    Tendsto (fun m => ∫ z, F z ∂(NB.l1Law n (φ m) j)) atTop (𝓝 (∫ z, F z ∂(NB.l1LawOf j νinf))) := by
  obtain ⟨m, hm, hKm⟩ := NB.K_low j
  have := NB.ref_prob j
  exact tendsto_integral_blocked (NB.ref j) (NB.K_cont j) hm hKm _ νinf (NB.uniform_of_tendsto j h)
    (NB.Ψ_meas j) hF hM

theorem tendsto_cov_l1 (j : ℕ) {φ : ℕ → ℕ} {νinf : ProbabilityMeasure (Y j)}
    (h : Tendsto (fun m => NB.predLaw n (φ m) j) atTop (𝓝 νinf))
    {f g : GaugeConnection G d (ProofPhase.coarseSide j) → ℝ} (hf : BM f) (hg : BM g) :
    Tendsto (fun m => cov (NB.l1Law n (φ m) j) f g) atTop (𝓝 (cov (NB.l1LawOf j νinf) f g)) := by
  obtain ⟨Mf, hMf⟩ := hf.bdd
  obtain ⟨Mg, hMg⟩ := hg.bdd
  have hfg : ∀ z, |f z * g z| ≤ Mf * Mg := fun z => by
    rw [abs_mul]; exact mul_le_mul (hMf z) (hMg z) (abs_nonneg _) ((abs_nonneg _).trans (hMf z))
  exact (NB.tendsto_integral_l1 n j h (hf.meas.mul hg.meas) hfg).sub
    ((NB.tendsto_integral_l1 n j h hf.meas hMf).mul (NB.tendsto_integral_l1 n j h hg.meas hMg))

/-- **The per-volume gap theorem (order mesh → volume → observable)**, for any `G` of the package and any `d`. Under
H2-all, in every volume `j`, every mesh limit point of the level-`k` L₁ block covariance of `f`, `g` is at most
`(1 − γ)⁻¹ (∑_{a ∈ A} v_f(a)) L_g e^{-λR}`: the constant does not depend on the volume. -/
theorem perVolumeGap {lam γ : ℝ} (hlam : 0 ≤ lam) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hH2 : NB.LimitDprimeAll n lam γ)
    (j : ℕ) {f g : GaugeConnection G d (ProofPhase.coarseSide j) → ℝ}
    {A Sg : Finset (LatticeLink d (ProofPhase.coarseSide j))}
    {vf : LatticeLink d (ProofPhase.coarseSide j) → ℝ} {Lg R : ℝ} (hf : BM f) (hg : BM g) (hfA : DepOn f A)
    (hgS : DepOn g Sg) (hvf : OscBound f vf) (hLg : 0 ≤ Lg) (hvg : OscBound g (fun _ => Lg))
    (hR : ∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) {h : ℝ}
    (hh : IsLimitPoint (fun k => cov (NB.l1Law n k j) f g) h) :
    |h| ≤ (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)) := by
  obtain ⟨φ, hφ, hlim⟩ := hh
  obtain ⟨νinf, -, ψ, hψ, hν⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (ProbabilityMeasure (Y j)))).tendsto_subseq
      (fun m => Set.mem_univ (NB.predLaw n (φ m) j))
  have hν' : Tendsto (fun m => NB.predLaw n ((φ ∘ ψ) m) j) atTop (𝓝 νinf) := hν
  have h1 := NB.tendsto_cov_l1 n j hν' hf hg
  have h2 : Tendsto (fun m => cov (NB.l1Law n ((φ ∘ ψ) m) j) f g) atTop (𝓝 h) := hlim.comp hψ.tendsto_atTop
  have hh : h = cov (NB.l1LawOf j νinf) f g := tendsto_nhds_unique h2 h1
  obtain ⟨Vinf, hpot, Sb, hpair, hflat, heq⟩ := hH2 j νinf ⟨φ ∘ ψ, hφ.comp hψ, hν'⟩
  have : Nonempty (LatticeLink d (ProofPhase.coarseSide j)) :=
    ⟨⟨fun _ => 0, ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩⟩
  rw [hh, cov, heq]
  exact Attempts.R3.decay_of_flatW (haarG G) hpot hpair linkDist linkDist_self linkDist_triangle hlam hγ0 hγ1
    hflat hf hg hfA hgS hvf hLg hvg hR

/-- **The per-volume gap theorem, eventually form.** -/
theorem perVolumeGap_eventually {lam γ : ℝ} (hlam : 0 ≤ lam) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hH2 : NB.LimitDprimeAll n lam γ) (j : ℕ) {f g : GaugeConnection G d (ProofPhase.coarseSide j) → ℝ}
    {A Sg : Finset (LatticeLink d (ProofPhase.coarseSide j))} {vf : LatticeLink d (ProofPhase.coarseSide j) → ℝ}
    {Lg R : ℝ} (hf : BM f) (hg : BM g) (hfA : DepOn f A) (hgS : DepOn g Sg) (hvf : OscBound f vf) (hLg : 0 ≤ Lg)
    (hvg : OscBound g (fun _ => Lg)) (hR : ∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, |cov (NB.l1Law n k j) f g| ≤ (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)) + ε := by
  set b := (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R))
  by_contra hne
  rw [not_eventually] at hne
  obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop hne
  obtain ⟨Mf, hMf⟩ := hf.bdd
  obtain ⟨Mg, hMg⟩ := hg.bdd
  have hbd : ∀ m, cov (NB.l1Law n (φ m) j) f g ∈ Metric.closedBall (0 : ℝ) (2 * (Mf * Mg)) := fun m => by
    have := NB.isProb_l1LawOf j (NB.predLaw n (φ m) j)
    change IsProbabilityMeasure (NB.l1LawOf j (NB.predLaw n (φ m) j)) at this
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    exact @ProofPhase.Quantum.NoisyBlocking.abs_cov_le _ _ (NB.l1Law n (φ m) j) this _ _ _ _ hMf hMg
  obtain ⟨a, -, ψ, hψ, ha⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hbd
  have hlp : IsLimitPoint (fun k => cov (NB.l1Law n k j) f g) a := ⟨φ ∘ ψ, hφ.comp hψ, ha⟩
  have hle := NB.perVolumeGap n hlam hγ0 hγ1 hH2 j hf hg hfA hgS hvf hLg hvg hR hlp
  have hge : b + ε ≤ |a| :=
    ge_of_tendsto ha.abs (Eventually.of_forall fun m => (lt_of_not_ge (hP (ψ m))).le)
  linarith

/-- **The block-level mesh limit exists in every volume at once (no open hypothesis).** -/
theorem exists_blockLimit :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ νinf : ∀ j, ProbabilityMeasure (Y j), ∀ j,
      Tendsto (fun m => NB.predLaw n (φ m) j) atTop (𝓝 (νinf j)) ∧
      ∀ (F : GaugeConnection G d (ProofPhase.coarseSide j) → ℝ), Measurable F → ∀ M, (∀ z, |F z| ≤ M) →
        Tendsto (fun m => ∫ z, F z ∂(NB.l1Law n (φ m) j)) atTop (𝓝 (∫ z, F z ∂(NB.l1LawOf j (νinf j)))) := by
  obtain ⟨νinf, -, φ, hφ, hν⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (∀ j, ProbabilityMeasure (Y j)))).tendsto_subseq
      (fun m => Set.mem_univ (fun j => NB.predLaw n m j))
  refine ⟨φ, hφ, νinf, fun j => ?_⟩
  have hj : Tendsto (fun m => NB.predLaw n (φ m) j) atTop (𝓝 (νinf j)) :=
    (continuous_apply j).tendsto _ |>.comp hν
  exact ⟨hj, fun F hF M hM => NB.tendsto_integral_l1 n j hj hF hM⟩

/-- **The block-level continuum limit has the gap at L₁, uniformly in the volume, under H2-all.** -/
theorem blockLimit_gap {lam γ : ℝ} (hlam : 0 ≤ lam) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hH2 : NB.LimitDprimeAll n lam γ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ νinf : ∀ j, ProbabilityMeasure (Y j), ∀ j,
      (∀ {f g : GaugeConnection G d (ProofPhase.coarseSide j) → ℝ}, BM f → BM g →
        Tendsto (fun m => cov (NB.l1Law n (φ m) j) f g) atTop (𝓝 (cov (NB.l1LawOf j (νinf j)) f g))) ∧
      ∀ {f g : GaugeConnection G d (ProofPhase.coarseSide j) → ℝ}
        {A Sg : Finset (LatticeLink d (ProofPhase.coarseSide j))}
        {vf : LatticeLink d (ProofPhase.coarseSide j) → ℝ} {Lg R : ℝ}, BM f → BM g → DepOn f A → DepOn g Sg →
        OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) → (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
        |cov (NB.l1LawOf j (νinf j)) f g| ≤ (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)) := by
  obtain ⟨φ, hφ, νinf, h⟩ := NB.exists_blockLimit n
  refine ⟨φ, hφ, νinf, fun j => ⟨fun hf hg => NB.tendsto_cov_l1 n j (h j).1 hf hg, ?_⟩⟩
  intro f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR
  have hc := NB.tendsto_cov_l1 n j (h j).1 hf hg
  exact NB.perVolumeGap n hlam hγ0 hγ1 hH2 j hf hg hfA hgS hvf hLg hvg hR ⟨φ, hφ, hc⟩

end NoisyBlocking

/-! ## The SU(2), `d = 4` instances -/

section Instance

open ProofPhase.Quantum (NoisyBlocking)

variable {V : ProofPhase.Existence.VTuning} {X Y : ℕ → Type*} [∀ j, MetricSpace (X j)] [∀ j, CompactSpace (X j)]
  [∀ j, MeasurableSpace (X j)] [∀ j, BorelSpace (X j)] [∀ j, MetricSpace (Y j)] [∀ j, CompactSpace (Y j)]
  [∀ j, MeasurableSpace (Y j)] [∀ j, BorelSpace (Y j)]

/-- The old SU(2), `d = 4` noisy blocking as a generic one (same fields). -/
def NoisyBlocking.ofOld (NB : ProofPhase.Quantum.NoisyBlocking V X Y) : ProofPhase.General.NoisyBlocking SU2 4 V X Y where
  ref := NB.ref
  ref_prob := NB.ref_prob
  K := NB.K
  K_cont := NB.K_cont
  K_low := NB.K_low
  K_norm := NB.K_norm
  pred := NB.pred
  pred_meas := NB.pred_meas
  Ψ := NB.Ψ
  Ψ_meas := NB.Ψ_meas

variable (NB : ProofPhase.Quantum.NoisyBlocking V X Y) [∀ j, TopologicalSpace.SeparableSpace (Y j)]

/-- The old `LimitDprimeAll` is the generic one for the converted blocking. -/
theorem limitDprimeAll_iff (lam γ : ℝ) :
    NB.LimitDprimeAll lam γ ↔ (NoisyBlocking.ofOld NB).LimitDprimeAll 2 lam γ := Iff.rfl

/-- `ProofPhase.Quantum.NoisyBlocking.perVolumeGap` from the generic theorem. -/
theorem perVolumeGap_su2 {lam γ : ℝ} (hlam : 0 ≤ lam) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hH2 : NB.LimitDprimeAll lam γ)
    (j : ℕ) {f g : GaugeConnection SU2 4 (ProofPhase.coarseSide j) → ℝ}
    {A Sg : Finset (LatticeLink 4 (ProofPhase.coarseSide j))}
    {vf : LatticeLink 4 (ProofPhase.coarseSide j) → ℝ} {Lg R : ℝ} (hf : BM f) (hg : BM g) (hfA : DepOn f A)
    (hgS : DepOn g Sg) (hvf : OscBound f vf) (hLg : 0 ≤ Lg) (hvg : OscBound g (fun _ => Lg))
    (hR : ∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) {h : ℝ}
    (hh : IsLimitPoint (fun k => cov (NB.l1Law k j) f g) h) :
    |h| ≤ (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)) :=
  (General.NoisyBlocking.perVolumeGap 2 (NoisyBlocking.ofOld NB) hlam hγ0 hγ1 hH2 j hf hg hfA hgS hvf hLg hvg hR hh)

/-- `ProofPhase.Quantum.NoisyBlocking.perVolumeGap_eventually` from the generic theorem. -/
theorem perVolumeGap_eventually_su2 {lam γ : ℝ} (hlam : 0 ≤ lam) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hH2 : NB.LimitDprimeAll lam γ) (j : ℕ) {f g : GaugeConnection SU2 4 (ProofPhase.coarseSide j) → ℝ}
    {A Sg : Finset (LatticeLink 4 (ProofPhase.coarseSide j))} {vf : LatticeLink 4 (ProofPhase.coarseSide j) → ℝ}
    {Lg R : ℝ} (hf : BM f) (hg : BM g) (hfA : DepOn f A) (hgS : DepOn g Sg) (hvf : OscBound f vf) (hLg : 0 ≤ Lg)
    (hvg : OscBound g (fun _ => Lg)) (hR : ∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, |cov (NB.l1Law k j) f g| ≤ (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)) + ε :=
  General.NoisyBlocking.perVolumeGap_eventually 2 (NoisyBlocking.ofOld NB) hlam hγ0 hγ1 hH2 j hf hg hfA hgS hvf hLg
    hvg hR hε

/-- `ProofPhase.Quantum.NoisyBlocking.exists_blockLimit` from the generic theorem. -/
theorem exists_blockLimit_su2 :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ νinf : ∀ j, ProbabilityMeasure (Y j), ∀ j,
      Tendsto (fun n => NB.predLaw (φ n) j) atTop (𝓝 (νinf j)) ∧
      ∀ (F : GaugeConnection SU2 4 (ProofPhase.coarseSide j) → ℝ), Measurable F → ∀ M, (∀ z, |F z| ≤ M) →
        Tendsto (fun n => ∫ z, F z ∂(NB.l1Law (φ n) j)) atTop (𝓝 (∫ z, F z ∂(NB.l1LawOf j (νinf j)))) :=
  General.NoisyBlocking.exists_blockLimit 2 (NoisyBlocking.ofOld NB)

/-- `ProofPhase.Quantum.NoisyBlocking.blockLimit_gap` from the generic theorem. -/
theorem blockLimit_gap_su2 {lam γ : ℝ} (hlam : 0 ≤ lam) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hH2 : NB.LimitDprimeAll lam γ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ νinf : ∀ j, ProbabilityMeasure (Y j), ∀ j,
      (∀ {f g : GaugeConnection SU2 4 (ProofPhase.coarseSide j) → ℝ}, BM f → BM g →
        Tendsto (fun n => cov (NB.l1Law (φ n) j) f g) atTop (𝓝 (cov (NB.l1LawOf j (νinf j)) f g))) ∧
      ∀ {f g : GaugeConnection SU2 4 (ProofPhase.coarseSide j) → ℝ}
        {A Sg : Finset (LatticeLink 4 (ProofPhase.coarseSide j))}
        {vf : LatticeLink 4 (ProofPhase.coarseSide j) → ℝ} {Lg R : ℝ}, BM f → BM g → DepOn f A → DepOn g Sg →
        OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) → (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
        |cov (NB.l1LawOf j (νinf j)) f g| ≤ (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)) :=
  General.NoisyBlocking.blockLimit_gap 2 (NoisyBlocking.ofOld NB) hlam hγ0 hγ1 hH2

example : @ProofPhase.Quantum.NoisyBlocking.perVolumeGap = @perVolumeGap_su2 := rfl
example : @ProofPhase.Quantum.NoisyBlocking.perVolumeGap_eventually = @perVolumeGap_eventually_su2 := rfl
example : @ProofPhase.Quantum.NoisyBlocking.exists_blockLimit = @exists_blockLimit_su2 := rfl
example : @ProofPhase.Quantum.NoisyBlocking.blockLimit_gap = @blockLimit_gap_su2 := rfl

end Instance

end ProofPhase.General
