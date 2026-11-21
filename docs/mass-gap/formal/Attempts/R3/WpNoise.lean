/-
Attempt round 3 (2026-11-21), attempt 3 (r3-wp): W_p from weak convergence through one noisy blocking step.
Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/r3-wp/NOTE.md` (sections 1 and 2).
-/

import Mathlib

/-!
# The noise lemma: relative sup-norm convergence of noisy block densities from weak convergence

**Setting.** `X` is the space of coarse block configurations of one finite volume (for a lattice gauge theory with a
compact group `G` and `n` coarse links: `X = G^n`, compact). `Y` is the space of the *predictions* of a blocking step
(also compact). A **noisy** blocking step draws the coarse configuration `x` from a kernel density `K(x, y)` around the
prediction `y` (for example `∏_e κ(x_e y_e⁻¹)` with a heat-kernel or Wilson-type noise `κ` on `G`, as in the stochastic
blocking of the OpenAI construction). If `ν` is the law of the prediction, the coarse density is the mixture
`ρ_ν(x) = ∫ K(x, y) dν(y)`.

**Results.**
* `abs_log_sub_log_le`: for `a, b ≥ m > 0`, `|log a − log b| ≤ |a − b| / m` (absolute closeness plus a lower bound
  gives relative closeness).
* `le_integral_of_forall_le`: a mixture of densities bounded below by `m` is bounded below by `m`. This is the
  **large-field lower bound for free**: on every coarse configuration, however large the field, `ρ_ν ≥ min K`.
* **`noise_uniform`**: if the kernels `K_k` are continuous, bounded below by one `m > 0` and converge uniformly to
  `K_∞`, and the prediction laws `ν_k` converge weakly to `ν_∞`, then `log ρ_k → log ρ_∞` **uniformly on all of `X`**.
  This is W_p (relative sup-norm convergence on all configurations) at the scale of the noisy step.
* **`noise_subseq`**: for a single continuous kernel bounded below, every sequence of prediction laws has a subsequence
  along which W_p holds (Prokhorov compactness of probability measures on a compact metric space).
* `eventually_of_subseq`: the subsequence principle. If every subsequence has a further subsequence along which a
  property eventually holds, it eventually holds along the whole sequence. With `noise_subseq` this turns "(H2) for every
  limit point, with one constant" into the per-volume gap statement for the full sequence (note, section 2).
* `prod_kernel_lower`: a product kernel `∏_e κ_e` with every factor `≥ m₀ > 0` is `≥ m₀^n`.

**What this does not say.** Nothing here is quantitative in the volume: the lower bound of a product kernel is
`m₀^n`, exponentially small in the number of coarse links, so the relative error obtained from an absolute one is
amplified by `m₀^{-n}`. That is enough per volume (the order "mesh first, then volume"), not for a volume-uniform rate.
Nothing here gives a gap: it applies verbatim to the free photon (U(1)), whose blocked theory converges and is gapless.
-/

open MeasureTheory Filter Topology Metric

set_option linter.unusedSectionVars false

noncomputable section

namespace Attempts.R3.Wp

/-! ## Elementary bounds -/

/-- **Relative from absolute.** For `a, b ≥ m > 0`: `|log a − log b| ≤ |a − b| / m`. -/
theorem abs_log_sub_log_le {a b m : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / m := by
  have key : ∀ x y : ℝ, m ≤ x → m ≤ y → Real.log y - Real.log x ≤ |x - y| / m := by
    intro x y hx hy
    have hx0 : 0 < x := hm.trans_le hx
    have hy0 : 0 < y := hm.trans_le hy
    have h1 := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [Real.log_div hy0.ne' hx0.ne'] at h1
    have h2 : y / x - 1 = (y - x) / x := by field_simp
    have h3 : (y - x) / x ≤ |x - y| / x := by
      apply div_le_div_of_nonneg_right _ hx0.le
      rw [abs_sub_comm]; exact le_abs_self _
    have h4 : |x - y| / x ≤ |x - y| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hx
    linarith
  rw [abs_le]
  constructor
  · have := key a b ha hb; linarith
  · have := key b a hb ha; rw [abs_sub_comm] at this; linarith

variable {Y : Type*} [MeasurableSpace Y]

/-- **A mixture keeps the lower bound** (the large-field lower bound of a noisy step). -/
theorem le_integral_of_forall_le (ν : Measure Y) [IsProbabilityMeasure ν] {f : Y → ℝ} (hf : Integrable f ν) {m : ℝ}
    (h : ∀ y, m ≤ f y) : m ≤ ∫ y, f y ∂ν := by
  have := integral_mono (integrable_const m) hf h
  simpa using this

/-- Two integrable functions that differ by at most `C` everywhere have integrals (against a probability measure)
that differ by at most `C`. -/
theorem abs_integral_sub_le (μ : Measure Y) [IsProbabilityMeasure μ] {f g : Y → ℝ} (hf : Integrable f μ)
    (hg : Integrable g μ) {C : ℝ} (h : ∀ y, |f y - g y| ≤ C) :
    |∫ y, f y ∂μ - ∫ y, g y ∂μ| ≤ C := by
  rw [← integral_sub hf hg]
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => f y - g y) (C := C)
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using h y)
  simpa [Real.norm_eq_abs] using this

/-- **Product kernels.** If every factor is at least `m₀ ≥ 0`, the product of `n` factors is at least `m₀ ^ n`. -/
theorem prod_kernel_lower {ι : Type*} [Fintype ι] {f : ι → ℝ} {m₀ : ℝ} (hm : 0 ≤ m₀) (h : ∀ i, m₀ ≤ f i) :
    m₀ ^ Fintype.card ι ≤ ∏ i, f i := by
  rw [← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => hm) (fun i _ => h i)

/-! ## The noise lemma -/

variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MetricSpace Y] [CompactSpace Y] [BorelSpace Y]

theorem continuous_section {K : X × Y → ℝ} (hK : Continuous K) (x : X) : Continuous fun y => K (x, y) :=
  hK.comp (Continuous.prodMk continuous_const continuous_id)

theorem integrable_section (μ : Measure Y) [IsFiniteMeasure μ] {K : X × Y → ℝ} (hK : Continuous K) (x : X) :
    Integrable (fun y => K (x, y)) μ :=
  (BoundedContinuousFunction.mkOfCompact ⟨fun y => K (x, y), continuous_section hK x⟩).integrable μ

/-- **The noise lemma.** Continuous kernels `K_k` on `X × Y`, all bounded below by one `m > 0`, converging uniformly to
`K_∞`; prediction laws `ν_k` converging weakly to `ν_∞`. Then the logarithms of the mixtures
`ρ_k(x) = ∫ K_k(x, y) dν_k(y)` converge to `log ρ_∞` **uniformly in `x ∈ X`**: relative sup-norm convergence of the
noisy block densities on all configurations, large fields included. -/
theorem noise_uniform (K : ℕ → X × Y → ℝ) (Kinf : X × Y → ℝ) (hKc : ∀ k, Continuous (K k))
    (hKinf : Continuous Kinf) (hKu : TendstoUniformly K Kinf atTop) {m : ℝ} (hm : 0 < m)
    (hKm : ∀ k p, m ≤ K k p) (hKinfm : ∀ p, m ≤ Kinf p)
    (ν : ℕ → ProbabilityMeasure Y) (νinf : ProbabilityMeasure Y) (hν : Tendsto ν atTop (𝓝 νinf)) :
    TendstoUniformly (fun k x => Real.log (∫ y, K k (x, y) ∂(ν k : Measure Y)))
      (fun x => Real.log (∫ y, Kinf (x, y) ∂(νinf : Measure Y))) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  set η : ℝ := ε * m / 4 with hη_def
  have hη : 0 < η := by positivity
  -- (i) the kernels are uniformly close
  have hKev : ∀ᶠ k in atTop, ∀ p, dist (Kinf p) (K k p) < η :=
    (Metric.tendstoUniformly_iff.1 hKu) η hη
  -- (ii) equicontinuity of the mixtures of `Kinf`, uniformly in the mixing measure
  obtain ⟨δ, hδ, hδK⟩ := Metric.uniformContinuous_iff.1 (CompactSpace.uniformContinuous_of_continuous hKinf) η hη
  have heq : ∀ (μ : Measure Y) [IsProbabilityMeasure μ] (x x' : X), dist x x' < δ →
      |∫ y, Kinf (x, y) ∂μ - ∫ y, Kinf (x', y) ∂μ| ≤ η := by
    intro μ _ x x' hxx'
    apply abs_integral_sub_le μ (integrable_section μ hKinf x) (integrable_section μ hKinf x')
    intro y
    have hd : dist (x, y) (x', y) < δ := by
      rw [Prod.dist_eq, dist_self]
      exact lt_of_le_of_lt (max_le le_rfl dist_nonneg) hxx'
    have := hδK hd
    rw [Real.dist_eq] at this
    exact this.le
  -- (iii) a finite δ-net of `X`
  obtain ⟨T, -, hTfin, hTcov⟩ := finite_cover_balls_of_compact (isCompact_univ (X := X)) hδ
  -- (iv) convergence at the net points
  have hpt : ∀ x : X, Tendsto (fun k => ∫ y, Kinf (x, y) ∂(ν k : Measure Y)) atTop
      (𝓝 (∫ y, Kinf (x, y) ∂(νinf : Measure Y))) := by
    intro x
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hν)
      (BoundedContinuousFunction.mkOfCompact ⟨fun y => Kinf (x, y), continuous_section hKinf x⟩)
  have hnet : ∀ᶠ k in atTop, ∀ t ∈ T,
      dist (∫ y, Kinf (t, y) ∂(ν k : Measure Y)) (∫ y, Kinf (t, y) ∂(νinf : Measure Y)) < η :=
    (Filter.eventually_all_finite hTfin).2 fun t _ => (Metric.tendsto_nhds.1 (hpt t)) η hη
  filter_upwards [hKev, hnet] with k hk1 hk2
  intro x
  -- lower bounds
  have hlo_k : m ≤ ∫ y, K k (x, y) ∂(ν k : Measure Y) :=
    le_integral_of_forall_le _ (integrable_section _ (hKc k) x) fun y => hKm k (x, y)
  have hlo_inf : m ≤ ∫ y, Kinf (x, y) ∂(νinf : Measure Y) :=
    le_integral_of_forall_le _ (integrable_section _ hKinf x) fun y => hKinfm (x, y)
  -- absolute closeness
  have hA : |∫ y, K k (x, y) ∂(ν k : Measure Y) - ∫ y, Kinf (x, y) ∂(ν k : Measure Y)| ≤ η := by
    apply abs_integral_sub_le _ (integrable_section _ (hKc k) x) (integrable_section _ hKinf x)
    intro y
    have := hk1 (x, y)
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this.le
  obtain ⟨t, htT, hxt⟩ : ∃ t ∈ T, x ∈ ball t δ := by
    have := hTcov (Set.mem_univ x)
    simpa using this
  have hxt' : dist x t < δ := mem_ball.1 hxt
  have hB1 := heq (ν k : Measure Y) x t hxt'
  have hB2 := hk2 t htT
  rw [Real.dist_eq] at hB2
  have hB3 := heq (νinf : Measure Y) t x (by rw [dist_comm]; exact hxt')
  have habs : |∫ y, K k (x, y) ∂(ν k : Measure Y) - ∫ y, Kinf (x, y) ∂(νinf : Measure Y)| < 4 * η := by
    have e : ∫ y, K k (x, y) ∂(ν k : Measure Y) - ∫ y, Kinf (x, y) ∂(νinf : Measure Y) =
        (∫ y, K k (x, y) ∂(ν k : Measure Y) - ∫ y, Kinf (x, y) ∂(ν k : Measure Y)) +
        (∫ y, Kinf (x, y) ∂(ν k : Measure Y) - ∫ y, Kinf (t, y) ∂(ν k : Measure Y)) +
        (∫ y, Kinf (t, y) ∂(ν k : Measure Y) - ∫ y, Kinf (t, y) ∂(νinf : Measure Y)) +
        (∫ y, Kinf (t, y) ∂(νinf : Measure Y) - ∫ y, Kinf (x, y) ∂(νinf : Measure Y)) := by ring
    rw [e]
    calc _ ≤ |∫ y, K k (x, y) ∂(ν k : Measure Y) - ∫ y, Kinf (x, y) ∂(ν k : Measure Y)| +
          |∫ y, Kinf (x, y) ∂(ν k : Measure Y) - ∫ y, Kinf (t, y) ∂(ν k : Measure Y)| +
          |∫ y, Kinf (t, y) ∂(ν k : Measure Y) - ∫ y, Kinf (t, y) ∂(νinf : Measure Y)| +
          |∫ y, Kinf (t, y) ∂(νinf : Measure Y) - ∫ y, Kinf (x, y) ∂(νinf : Measure Y)| := by
            have := abs_add_le (∫ y, K k (x, y) ∂(ν k : Measure Y) - ∫ y, Kinf (x, y) ∂(ν k : Measure Y) +
              (∫ y, Kinf (x, y) ∂(ν k : Measure Y) - ∫ y, Kinf (t, y) ∂(ν k : Measure Y)) +
              (∫ y, Kinf (t, y) ∂(ν k : Measure Y) - ∫ y, Kinf (t, y) ∂(νinf : Measure Y)))
              (∫ y, Kinf (t, y) ∂(νinf : Measure Y) - ∫ y, Kinf (x, y) ∂(νinf : Measure Y))
            have := abs_add_le (∫ y, K k (x, y) ∂(ν k : Measure Y) - ∫ y, Kinf (x, y) ∂(ν k : Measure Y) +
              (∫ y, Kinf (x, y) ∂(ν k : Measure Y) - ∫ y, Kinf (t, y) ∂(ν k : Measure Y)))
              (∫ y, Kinf (t, y) ∂(ν k : Measure Y) - ∫ y, Kinf (t, y) ∂(νinf : Measure Y))
            have := abs_add_le (∫ y, K k (x, y) ∂(ν k : Measure Y) - ∫ y, Kinf (x, y) ∂(ν k : Measure Y))
              (∫ y, Kinf (x, y) ∂(ν k : Measure Y) - ∫ y, Kinf (t, y) ∂(ν k : Measure Y))
            linarith
      _ < 4 * η := by linarith
  have hlog := abs_log_sub_log_le hm hlo_inf hlo_k
  rw [Real.dist_eq]
  calc |Real.log (∫ y, Kinf (x, y) ∂(νinf : Measure Y)) - Real.log (∫ y, K k (x, y) ∂(ν k : Measure Y))|
      ≤ |∫ y, Kinf (x, y) ∂(νinf : Measure Y) - ∫ y, K k (x, y) ∂(ν k : Measure Y)| / m := hlog
    _ < 4 * η / m := by
        rw [abs_sub_comm]
        exact div_lt_div_of_pos_right habs hm
    _ = ε := by rw [hη_def]; field_simp

/-- **W_p along a subsequence, for free.** For one continuous kernel bounded below by `m > 0`, every sequence of
prediction laws has a weakly convergent subsequence (Prokhorov), and along it the log-densities of the noisy block
laws converge uniformly on all configurations. -/
theorem noise_subseq [TopologicalSpace.SeparableSpace Y] (K : X × Y → ℝ) (hK : Continuous K) {m : ℝ} (hm : 0 < m)
    (hKm : ∀ p, m ≤ K p) (ν : ℕ → ProbabilityMeasure Y) :
    ∃ νinf : ProbabilityMeasure Y, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun n x => Real.log (∫ y, K (x, y) ∂(ν (φ n) : Measure Y)))
        (fun x => Real.log (∫ y, K (x, y) ∂(νinf : Measure Y))) atTop := by
  obtain ⟨a, -, φ, hφ, h⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (ProbabilityMeasure Y))).tendsto_subseq
      (fun n => Set.mem_univ (ν n))
  refine ⟨a, φ, hφ, ?_⟩
  have hconst : TendstoUniformly (fun _ : ℕ => K) K atTop :=
    Metric.tendstoUniformly_iff.2 fun ε hε => Filter.Eventually.of_forall fun _ x => by simpa using hε
  exact noise_uniform (fun _ => K) K (fun _ => hK) hK hconst hm (fun _ => hKm) hKm (ν ∘ φ) a h

/-! ## The subsequence principle -/

/-- **Subsequence principle.** If every subsequence has a further subsequence along which `P` eventually holds, then
`P` eventually holds. Use: `P k` = "the level-`k` lattice theory in the volume `v` satisfies the decay bound with the
fixed constants `C, m`"; every subsequence has a further one along which the noisy block laws converge (`noise_subseq`),
and if (H2) holds for every limit point with one constant, the reduction gives `P` eventually along it. -/
theorem eventually_of_subseq {P : ℕ → Prop}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ n in atTop, P (φ (ψ n))) :
    ∀ᶠ k in atTop, P k := by
  by_contra hne
  obtain ⟨φ, hφ, hnP⟩ := extraction_of_frequently_atTop (Filter.not_eventually.1 hne)
  obtain ⟨ψ, -, hev⟩ := h φ hφ
  obtain ⟨n, hn⟩ := hev.exists
  exact hnP (ψ n) hn

end Attempts.R3.Wp
