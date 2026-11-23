/-
Proof phase, cycle 9, c9b round 2 (infrared): the pattern-conditioned one-box assembly. Influence bounds are needed only
for in-support pairs (M1's support restriction), so the criterion is stated per pattern and per content pair, not for every
boundary condition (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c9b-adjoint/ROUND2.md`, section 2.
-/

import ProofPhase.OneBox.Fine
import ProofPhase.Adjoint2.CostCoupling

/-!
# The pattern-conditioned assembly

`FineOneBox` (c7c) and `FineOneBoxSplit` (c8a) ask for box influences under **every** boundary condition: Theorem A
contracts oscillations, and an oscillation bound is a statement about all configurations. M1's coupling form
(`couplingDS_bound`) needs the influence hypothesis only for pairs in the supports, and its covariance form
(`UV-TV.md` 33.3) conditions on the content near one observable and compares two **sampled** contents, so nothing leaves the
supports. This file assembles that route at the level of the Wilson measure.

* **Mixtures** (`cov_mixture`, `abs_cov_mixture_le`): for `μ = Σ_p w_p ν_p` (patterns `p`: e.g. which cells are
  ultraviolet-bad), `Cov_μ = Σ_p w_p Cov_{ν_p} + (pattern-index covariance)`. With per-pattern bounds on good patterns:
  `|Cov_μ| ≤ ε + 2 w(bad) + |index term|`.
* **Conditioning on the content near `f`** (`DisintBound`, `abs_cov_le_of_disintBound`): if `ν = η.bind K` with `f`
  determined by the mixing variable (`f = φ(y)` a.s. under `K y`, `|φ| ≤ 1`) and `|K_y g - K_{y'} g| ≤ ε` for `y, y'` in a
  set `Ω` of full `η`-measure, then `|Cov_ν(f, g)| ≤ ε`. **Only pairs inside the support are used**: `Ω` may exclude every
  atypical content.
* **The in-support pair bound from the coupling theorem** (`pair_bound_of_couplingDS`): `couplingDS_integral_bound` for the
  two conditional measures `K y, K y'`, whose influence hypothesis (I) is asked only on their supports; source blocks near
  the conditioned region, composite boxes around bad regions (M1, `UV-TV.md` 16, 33.3).
* **The criterion** (`FineOneBoxPat T`, named, open) and **the assembly** (`fineDecayInv_of_fineOneBoxPat`,
  `yang_mills_assembly_pat`): from some level on, the Wilson measure is a finite pattern mixture; for gauge-invariant `G`
  and bounded `F` at physical distance `D`, the bad patterns weigh `≤ c e^{-mD}`, the pattern-index covariance is
  `≤ c e^{-mD}`, and every good pattern carries a `DisintBound` with `ε = c e^{-mD}`. Then `FineDecayInv`, and the full
  assembly conclusion.

What `FineOneBoxPat` changes is the **form** in which the gap-strength input can be supplied: per pattern, per pair of
sampled contents in a set of full measure, so the influence bounds of the coupling theorem are needed only in the
supports. It is not claimed to follow from `FineDecayInv` (decay controls the conditional averages only in `L¹`, not
uniformly on a full-measure set of content pairs).
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity ProofPhase.Torus ProofPhase.V3 ProofPhase.V4 ProofPhase.RouteA ProofPhase.OneBox

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Adjoint2

/-! ## 1. Covariance of finite mixtures -/

section Mixture

variable {X : Type*} [MeasurableSpace X]

/-- The covariance `∫ f g dμ - ∫ f dμ ∫ g dμ`. -/
def covar (μ : Measure X) (f g : X → ℝ) : ℝ := ∫ x, f x * g x ∂μ - (∫ x, f x ∂μ) * ∫ x, g x ∂μ

theorem abs_integral_le_one {μ : Measure X} [IsProbabilityMeasure μ] {h : X → ℝ} (hh : ∀ x, |h x| ≤ 1) :
    |∫ x, h x ∂μ| ≤ 1 := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := h) (C := 1)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hh x)
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at this
  exact this

theorem abs_covar_le_two {μ : Measure X} [IsProbabilityMeasure μ] {f g : X → ℝ} (hf : ∀ x, |f x| ≤ 1)
    (hg : ∀ x, |g x| ≤ 1) : |covar μ f g| ≤ 2 := by
  have h1 : |∫ x, f x * g x ∂μ| ≤ 1 := abs_integral_le_one fun x => by
    rw [abs_mul]; nlinarith [hf x, hg x, abs_nonneg (f x), abs_nonneg (g x)]
  have h2 := abs_integral_le_one (μ := μ) hf
  have h3 := abs_integral_le_one (μ := μ) hg
  have h4 : |(∫ x, f x ∂μ) * ∫ x, g x ∂μ| ≤ 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg (∫ x, f x ∂μ), abs_nonneg (∫ x, g x ∂μ)]
  unfold covar
  calc |∫ x, f x * g x ∂μ - (∫ x, f x ∂μ) * ∫ x, g x ∂μ|
      ≤ |∫ x, f x * g x ∂μ| + |(∫ x, f x ∂μ) * ∫ x, g x ∂μ| := abs_sub _ _
    _ ≤ 2 := by linarith

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- **Covariance of a finite mixture**: the weighted per-pattern covariances plus the pattern-index covariance. -/
theorem cov_mixture {μ : Measure X} (w : P → ℝ) (ν : P → Measure X) {f g : X → ℝ}
    (hFG : ∫ x, f x * g x ∂μ = ∑ p, w p * ∫ x, f x * g x ∂(ν p))
    (hF : ∫ x, f x ∂μ = ∑ p, w p * ∫ x, f x ∂(ν p)) (hG : ∫ x, g x ∂μ = ∑ p, w p * ∫ x, g x ∂(ν p)) :
    covar μ f g = ∑ p, w p * covar (ν p) f g +
      (∑ p, w p * ((∫ x, f x ∂(ν p)) * ∫ x, g x ∂(ν p)) -
        (∑ p, w p * ∫ x, f x ∂(ν p)) * ∑ p, w p * ∫ x, g x ∂(ν p)) := by
  unfold covar
  rw [hFG, hF, hG]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- **Mixture bound**: good patterns contribute `≤ ε`, bad ones at most `2` each (weighted), plus the index term. -/
theorem abs_covar_mixture_le {μ : Measure X} (w : P → ℝ) (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∑ p, w p = 1)
    (ν : P → Measure X) (hν : ∀ p, IsProbabilityMeasure (ν p)) {f g : X → ℝ} (hf : ∀ x, |f x| ≤ 1)
    (hg : ∀ x, |g x| ≤ 1)
    (hFG : ∫ x, f x * g x ∂μ = ∑ p, w p * ∫ x, f x * g x ∂(ν p))
    (hF : ∫ x, f x ∂μ = ∑ p, w p * ∫ x, f x ∂(ν p)) (hG : ∫ x, g x ∂μ = ∑ p, w p * ∫ x, g x ∂(ν p))
    (good : Finset P) {ε η δ : ℝ} (hε : 0 ≤ ε) (hgood : ∀ p ∈ good, |covar (ν p) f g| ≤ ε)
    (hbad : ∑ p ∈ univ \ good, w p ≤ η)
    (hidx : |∑ p, w p * ((∫ x, f x ∂(ν p)) * ∫ x, g x ∂(ν p)) -
        (∑ p, w p * ∫ x, f x ∂(ν p)) * ∑ p, w p * ∫ x, g x ∂(ν p)| ≤ δ) :
    |covar μ f g| ≤ ε + 2 * η + δ := by
  rw [cov_mixture w ν hFG hF hG]
  have hsum : |∑ p, w p * covar (ν p) f g| ≤ ε + 2 * η := by
    have hb : ∀ p, |w p * covar (ν p) f g| ≤ w p * (if p ∈ good then ε else 2) := by
      intro p
      rw [abs_mul, abs_of_nonneg (hw0 p)]
      refine mul_le_mul_of_nonneg_left ?_ (hw0 p)
      split_ifs with hp
      · exact hgood p hp
      · exact @abs_covar_le_two _ _ _ (hν p) _ _ hf hg
    calc |∑ p, w p * covar (ν p) f g| ≤ ∑ p, |w p * covar (ν p) f g| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p, w p * (if p ∈ good then ε else 2) := Finset.sum_le_sum fun p _ => hb p
      _ = ∑ p ∈ good, w p * ε + ∑ p ∈ univ \ good, w p * 2 := by
          rw [← Finset.sum_sdiff (Finset.subset_univ good), add_comm]
          congr 1
          · exact Finset.sum_congr rfl fun p hp => by rw [ite_eq_left hp]
          · exact Finset.sum_congr rfl fun p hp => by rw [ite_eq_right (Finset.mem_sdiff.mp hp).2]
      _ ≤ ε + 2 * η := by
          have h1 : ∑ p ∈ good, w p * ε ≤ ε := by
            rw [← Finset.sum_mul]
            have : ∑ p ∈ good, w p ≤ 1 :=
              hw1 ▸ Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ good) fun p _ _ => hw0 p
            nlinarith
          have h2 : ∑ p ∈ univ \ good, w p * 2 ≤ 2 * η := by
            rw [← Finset.sum_mul]; linarith
          linarith
  calc |∑ p, w p * covar (ν p) f g + _| ≤ |∑ p, w p * covar (ν p) f g| + |_| := abs_add_le _ _
    _ ≤ ε + 2 * η + δ := by linarith

end Mixture

/-! ## 2. Conditioning on the content near `f`: only in-support pairs -/

section Disint

variable {X : Type*} [MeasurableSpace X]

/-- **Disintegration data with an in-support pair bound.** `ν = η.bind K` over a content variable `y`; `f` is determined
by the content (`f = φ(y)` a.s. under `K y`, `|φ| ≤ 1`); for contents `y, y'` in a set `Ω` of full measure, the
conditional averages of `g` differ by at most `ε`. Nothing is asked outside `Ω`. -/
structure DisintBound (ν : Measure X) (f g : X → ℝ) (ε : ℝ) where
  Y : Type
  mY : MeasurableSpace Y
  η : @Measure Y mY
  probη : @IsProbabilityMeasure Y mY η
  K : @Kernel Y X mY _
  markov : @IsMarkovKernel Y X mY _ K
  bind_eq : η.bind K = ν
  φ : Y → ℝ
  φ_meas : @Measurable Y ℝ mY _ φ
  φ_le : ∀ y, |φ y| ≤ 1
  f_eq : ∀ y, ∀ᵐ x ∂(K y), f x = φ y
  Ω : Set Y
  Ω_meas : @MeasurableSet Y mY Ω
  Ω_full : η Ωᶜ = 0
  pair : ∀ y ∈ Ω, ∀ y' ∈ Ω, |∫ x, g x ∂(K y) - ∫ x, g x ∂(K y')| ≤ ε

/-- **Covariance from in-support pairs** (`UV-TV.md` 33.3): `|Cov_ν(f, g)| ≤ ε` for `|g| ≤ 1`. -/
theorem abs_covar_le_of_disintBound {ν : Measure X} {f g : X → ℝ} {ε : ℝ} (B : DisintBound ν f g ε)
    (hf : Measurable f) (hf1 : ∀ x, |f x| ≤ 1) (hg : Measurable g) (hg1 : ∀ x, |g x| ≤ 1) :
    |covar ν f g| ≤ ε := by
  rcases B with ⟨Y, mY, η, hη, K, hK, rfl, φ, hφm, hφ, hfe, Ω, hΩm, hΩ, hpair⟩
  set h : Y → ℝ := fun y => ∫ x, g x ∂(K y) with hh
  have hfg1 : ∀ x, |f x * g x| ≤ 1 := fun x => by
    rw [abs_mul]; nlinarith [hf1 x, hg1 x, abs_nonneg (f x), abs_nonneg (g x)]
  -- the three integrals through the content
  have eFG : ∫ x, f x * g x ∂(η.bind K) = ∫ y, φ y * h y ∂η := by
    rw [integral_bind_eq η K (F := fun x => f x * g x) (hf.mul hg) hfg1]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show ∫ x, f x * g x ∂(K y) = φ y * ∫ x, g x ∂(K y)
    rw [← integral_const_mul]
    exact integral_congr_ae (by filter_upwards [hfe y] with x hx; rw [hx])
  have eF : ∫ x, f x ∂(η.bind K) = ∫ y, φ y ∂η := by
    rw [integral_bind_eq η K hf hf1]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show ∫ x, f x ∂(K y) = φ y
    rw [integral_congr_ae (hfe y), integral_const]
    simp
  have eG : ∫ x, g x ∂(η.bind K) = ∫ y, h y ∂η := integral_bind_eq η K hg hg1
  have hint_h : Integrable h η := integrable_integral_kernel η K hg hg1
  have hh1 : ∀ y, |h y| ≤ 1 := fun y => abs_integral_kernel_le K hg1 y
  have hint_φ : Integrable φ η := integrable_of_abs_le hφm hφ
  have hint_φh : Integrable (fun y => φ y * h y) η :=
    Integrable.of_bound (C := 1) (hφm.aestronglyMeasurable.mul hint_h.aestronglyMeasurable)
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_mul]; nlinarith [hφ y, hh1 y, abs_nonneg (φ y), abs_nonneg (h y)])
  set c := ∫ y, h y ∂η
  -- `h y` is within `ε` of its mean for `y ∈ Ω`
  have hΩae : ∀ᵐ y ∂η, y ∈ Ω := (measure_eq_zero_iff_ae_notMem.mp hΩ).mono fun y hy => by simpa using hy
  have hdev : ∀ y ∈ Ω, |h y - c| ≤ ε := by
    intro y hy
    have e1 : h y - c = ∫ y', (h y - h y') ∂η := by
      rw [integral_sub (integrable_const _) hint_h, integral_const]; simp [c]
    rw [e1]
    have := norm_integral_le_of_norm_le_const (μ := η) (f := fun y' => h y - h y') (C := ε)
      (hΩae.mono fun y' hy' => by rw [Real.norm_eq_abs]; exact hpair y hy y' hy')
    rw [Real.norm_eq_abs, probReal_univ, mul_one] at this
    exact this
  have ecov : covar (η.bind K) f g = ∫ y, φ y * (h y - c) ∂η := by
    unfold covar
    rw [eFG, eF, eG]
    simp_rw [mul_sub]
    rw [integral_sub hint_φh (hint_φ.mul_const c), integral_mul_const]
  rw [ecov]
  have := norm_integral_le_of_norm_le_const (μ := η) (f := fun y => φ y * (h y - c)) (C := ε)
    (hΩae.mono fun y hy => by
      rw [Real.norm_eq_abs, abs_mul]
      have := hdev y hy
      nlinarith [hφ y, abs_nonneg (φ y), abs_nonneg (h y - c)])
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at this
  exact this

end Disint

/-! ## 3. The in-support pair bound from the coupling theorem -/

section Pair

variable {ι S β : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] [Fintype β] [DecidableEq β]

/-- **The pair bound of `DisintBound` from M1's coupling theorem** (S): for two conditional measures with a
`CouplingSpec` whose influence hypothesis holds **on their supports only**, and `g` (`|g| ≤ 1`) depending on sites where
the weights are `≥ v_min`: `|∫ g dK_y - ∫ g dK_{y'}| ≤ 2 v_min⁻¹ s/((1 - γ) c_min)`. -/
theorem pair_bound_of_couplingDS [MeasurableEq S] {μ μ' : Measure (ι → S)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] [Nonempty β] (C : CouplingSpec μ μ' β) (W : C.DSWeights) (A : Finset ι) {vmin : ℝ}
    (hvmin : 0 < vmin) (hvA : ∀ x ∈ A, vmin ≤ W.v x) {g : (ι → S) → ℝ} (hg : Measurable g) (hg1 : ∀ σ, |g σ| ≤ 1)
    (hdep : ∀ σ σ' : ι → S, (∀ x ∈ A, σ x = σ' x) → g σ = g σ') :
    |∫ σ, g σ ∂μ - ∫ σ, g σ ∂μ'| ≤ 2 * vmin⁻¹ * W.bound := by
  have := couplingDS_integral_bound C W.good W.v W.K W.γ W.cmin W.v_nonneg W.γ_nonneg W.γ_lt_one W.cmin_pos
    W.cmin_le W.influence W.column A hvmin hvA hg hg1 hdep
  simpa [CouplingSpec.DSWeights.bound] using this

end Pair

/-! ## 4. The criterion and the assembly -/

/-- **The pattern-conditioned one-box criterion for the Wilson measure (named, open).** A rate `m > 0`; for every
physical extent `R` a constant `c` and a level `k₀`; for every level `k ≥ k₀` and volume `j`: the Wilson measure is a
finite mixture `Σ_p w_p ν_p` over patterns (tested on bounded measurable functions), and for bounded measurable `F`, `G`
(`G` gauge invariant, `F` of physical extent `≤ R`) at physical distance `≥ D`: a set of good patterns whose complement
weighs `≤ c e^{-mD}`, a pattern-index covariance `≤ c e^{-mD}`, and for every good pattern a `DisintBound` (content near
`F`, in-support pairs only) with `ε = c e^{-mD}`. -/
def FineOneBoxPat (T : Tuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j : ℕ,
    ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P) (w : P → ℝ) (ν : P → Measure (GaugeConnection SU2 4 (T.side k j))),
      (∀ p, 0 ≤ w p) ∧ ∑ p, w p = 1 ∧ (∀ p, IsProbabilityMeasure (ν p)) ∧
      (∀ h : GaugeConnection SU2 4 (T.side k j) → ℝ, Measurable h → (∀ U, |h U| ≤ 1) →
        ∫ U, h U ∂(T.ym k j) = ∑ p, w p * ∫ U, h U ∂(ν p)) ∧
      ∀ (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink 4 (T.side k j))) (D : ℝ),
        Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant G →
        DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * linkDist e e') →
        ∃ good : Finset P, ∑ p ∈ univ \ good, w p ≤ c * Real.exp (-(m * D)) ∧
          |∑ p, w p * ((∫ U, F U ∂(ν p)) * ∫ U, G U ∂(ν p)) -
            (∑ p, w p * ∫ U, F U ∂(ν p)) * ∑ p, w p * ∫ U, G U ∂(ν p)| ≤ c * Real.exp (-(m * D)) ∧
          ∀ p ∈ good, Nonempty (DisintBound (ν p) F G (c * Real.exp (-(m * D))))

/-- **The pattern-conditioned criterion gives decay** (S), with constant `4c`. -/
theorem fineDecayInv_of_fineOneBoxPat {T : Tuning} (h : FineOneBoxPat T) : FineDecayInv T := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, hc, k₀, Hk⟩ := H R
  refine ⟨4 * c, by positivity, k₀, fun k hk j F G A₀ B₀ D mF mG bF bG gG dF dG eA hsep => ?_⟩
  obtain ⟨P, _, _, w, ν, hw0, hw1, hν, hrep, HFG⟩ := Hk k hk j
  obtain ⟨good, hbad, hidx, hgood⟩ := HFG F G A₀ B₀ D mF mG bF bG gG dF dG eA hsep
  set e := c * Real.exp (-(m * D))
  have he : 0 ≤ e := by positivity
  have hfg1 : ∀ U, |F U * G U| ≤ 1 := fun U => by
    rw [abs_mul]; nlinarith [bF U, bG U, abs_nonneg (F U), abs_nonneg (G U)]
  have hg : ∀ p ∈ good, |covar (ν p) F G| ≤ e := fun p hp => by
    obtain ⟨B⟩ := hgood p hp
    exact abs_covar_le_of_disintBound B mF bF mG bG
  have := abs_covar_mixture_le w hw0 hw1 ν hν bF bG (hrep _ (mF.mul mG) hfg1) (hrep _ mF bF) (hrep _ mG bG)
    good he hg hbad hidx
  show |covar (T.ym k j) F G| ≤ 4 * c * Real.exp (-(m * D))
  calc |covar (T.ym k j) F G| ≤ e + 2 * e + e := this
    _ = 4 * c * Real.exp (-(m * D)) := by simp only [e]; ring

/-- **Assembly with the pattern-conditioned criterion** (S): line of constant physics, non-triviality and
`FineOneBoxPat` give torus decay, the gap in both orders of limits, reflection positivity and non-triviality. -/
theorem yang_mills_assembly_pat {T : Tuning} (hL : OnLCP' T) (hN : NonTrivial T) (h : FineOneBoxPat T) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T := by
  have hT := torusDecayLoc_of_fineDecayInv (fineDecayInv_of_fineOneBoxPat h)
  obtain ⟨hVF, hMF⟩ := bothOrdersLoc_of_torusDecayLoc hL.tendsto_a hT
  exact ⟨hT, hVF, hMF, limitRP T, hN⟩

end ProofPhase.Adjoint2
