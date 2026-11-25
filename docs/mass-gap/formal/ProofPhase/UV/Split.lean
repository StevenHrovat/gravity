/-
Proof phase, cycle 3, workstream 1 (c3a-uv): the structure of `ObsTransferPhys`, 2026-11-22. Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c3a-uv/NOTE.md`.
-/

import ProofPhase.Torus.Top
import Mathlib.Probability.ConditionalExpectation

/-!
# Where the content of `ObsTransferPhys` sits: difficulty conservation and the two-stage split

`ObsTransferPhys` (`ProofPhase.Assembly`) asks three things of a blocking `Φ`: (a) a coarse approximant with a level-uniform
oscillation sum, (b) `E[F|Φ] ≈ f ∘ Φ` in `L¹`, (c) the **conditional decoupling** `|E[FG] − E[E[F|Φ] E[G|Φ]]| ≤ c e^{-mD}`.
This file proves the exact identities that locate the content of (c), and the two-stage split that separates an ultraviolet
stage (fine lattice → an intermediate scale `L₀`) from a crossover stage (`L₀ → L₁`).

**Generic (any probability space, any sub-σ-algebras).** `condDefect μ m F G := ∫ F G − ∫ μ[F|m] μ[G|m]` is the quantity
of (c).
* `condDefect_eq` (**difficulty conservation**): `condDefect m F G = Cov(F, G) − Cov(E[F|m], E[G|m])`. The fine covariance
  is split between (c) and the coarse covariance; the blocked route gains only if (c) is small for a reason other than the
  decay of `Cov(F, G)` itself.
* `abs_condDefect_sub_cov_le` (**the noise-limit trap in reverse**, quantitative): `|condDefect m F G − Cov(F, G)| ≤
  ∫ |E[F|m] − E F|`, the information of the block σ-algebra about `F`. A blocking that forgets `F` (decimation in its
  pure-noise limit) makes (c) **equal** to the fine decay: `condDefect_eq_cov_of_indep` (exact, under independence).
* `abs_condDefect_le`: `|condDefect| ≤ |Cov(F,G)| + |Cov(E[F|m], E[G|m])|`; `abs_condDefect_sub_cov_sub_le`: given
  the approximants of (b) within `ε`, `|condDefect − (Cov(F,G) − Cov(f, g))| ≤ 4ε`. Once the coarse side decays, (c) is
  **equivalent** to the decay of the fine covariance (the converse direction is `RouteA.cov_transfer`).
* `condDefect_tower`: for `𝒢 ≤ ℋ`, `condDefect 𝒢 F G = condDefect ℋ F G + condDefect 𝒢 (E[F|ℋ]) (E[G|ℋ])`.
* `abs_condDefect_sub_le`: `condDefect` is 2-Lipschitz in `L¹` on functions bounded by one.
* `twoStage` (**the two-stage split**): stage-1 estimates (b), (c) for `ℋ` with errors `ε₁, δ₁`, and stage-2 estimates
  for the stage-1 approximants with respect to `𝒢 ≤ ℋ` (errors `ε₂, δ₂`) give the estimates for `𝒢` with errors
  `ε₁ + ε₂` and `δ₁ + δ₂ + 4ε₁`.
* `condExp_comp_map`: conditional expectations through a composite map can be computed on the image law:
  `μ[h ∘ B₁ | σ(B₂ ∘ B₁)] = ν[h | σ(B₂)] ∘ B₁` a.e., `ν = B₁ μ`. `condDefect_map`: the same for the defect.

**Yang–Mills instance.** `twoStage_blocked`: for the SU(2) Wilson measure `T.ym k j` and two reflection-respecting
blockings `B₁` (fine → intermediate torus) and `B₂` (intermediate → coarse), the three `ObsTransferPhys` estimates of the
composite blocking `B₁.comp B₂` (in the syntactic form of `ObsTransferPhys`) follow from (UV) the estimates for `B₁` on the
Wilson measure and (X) the estimates for the stage-1 approximants **on the intermediate blocked law** `(T.ym k j).map B₁`.
Stage 2 is therefore a statement about the `L₀`-blocked theory, a lattice theory of fixed resolution `L₁/L₀`. The good
blocking `RouteA.goodBlocking` is an `n_k`-fold iterate of one smeared step, so it is of this composite shape at every level
(`n_k − r` steps to `L₀ = L₁/2^r`, then `r` steps); the re-association of the iterate across the casts of `smearIter` is
elementary and not formalised here.

**Claim level.** Generic measure theory, substantive only as a reduction and as a precise location of the content;
Yang–Mills enters only through the measure and the blockings (`twoStage_blocked`). No estimate of (c) is proved here for
any interacting theory. See the note for the free-field (photon) computation and for where `b₀ > 0` and large fields enter.
-/

open MeasureTheory

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.UV

/-! ## Generic: covariance, conditional decoupling defect -/

section Generic

variable {X : Type*} {mX : MeasurableSpace X} (μ : Measure[mX] X) [IsProbabilityMeasure μ]

/-- The covariance `∫ F G − ∫ F ∫ G`. -/
def cov (F G : X → ℝ) : ℝ := ∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * ∫ x, G x ∂μ

/-- **The conditional decoupling defect** `∫ F G − ∫ E[F|m] E[G|m]` (part (c) of `ObsTransferPhys`; it equals
`E[Cov(F, G | m)]`). -/
def condDefect (m : MeasurableSpace X) (F G : X → ℝ) : ℝ :=
  ∫ x, F x * G x ∂μ - ∫ x, μ[F | m] x * μ[G | m] x ∂μ

/-- `F` is a.e. strongly measurable and a.e. bounded by one. -/
def Bdd1 (F : X → ℝ) : Prop := AEStronglyMeasurable F μ ∧ ∀ᵐ x ∂μ, |F x| ≤ 1

variable {μ}

theorem integrable_of_ae_abs_le {f : X → ℝ} (hf : AEStronglyMeasurable f μ) {C : ℝ} (h : ∀ᵐ x ∂μ, |f x| ≤ C) :
    Integrable f μ :=
  Integrable.of_bound hf C (h.mono fun x hx => by rwa [Real.norm_eq_abs])

theorem Bdd1.integrable {F : X → ℝ} (h : Bdd1 μ F) : Integrable F μ := integrable_of_ae_abs_le h.1 h.2

theorem Bdd1.of_measurable {F : X → ℝ} (hF : Measurable F) (h1 : ∀ x, |F x| ≤ 1) : Bdd1 μ F :=
  ⟨hF.aestronglyMeasurable, ae_of_all _ h1⟩

theorem Bdd1.mul {F G : X → ℝ} (hF : Bdd1 μ F) (hG : Bdd1 μ G) : Bdd1 μ (fun x => F x * G x) :=
  ⟨hF.1.mul hG.1, by
    filter_upwards [hF.2, hG.2] with x h1 h2
    rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) h1).trans h2⟩

theorem Bdd1.condExp {F : X → ℝ} (h : Bdd1 μ F) {m : MeasurableSpace X} (hm : m ≤ mX) : Bdd1 μ (μ[F | m]) := by
  have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  exact ⟨(stronglyMeasurable_condExp.mono hm).aestronglyMeasurable, ae_bdd_abs_condExp_of_ae_bdd_abs h.2⟩

/-- **Difficulty conservation.** The defect of (c) is the fine covariance minus the covariance of the conditional
expectations. -/
theorem condDefect_eq {m : MeasurableSpace X} (hm : m ≤ mX) (F G : X → ℝ) :
    condDefect μ m F G = cov μ F G - cov μ (μ[F | m]) (μ[G | m]) := by
  have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  unfold condDefect cov
  rw [integral_condExp hm, integral_condExp hm]
  ring

/-- `|(c)| ≤ |fine covariance| + |coarse covariance|`. -/
theorem abs_condDefect_le {m : MeasurableSpace X} (hm : m ≤ mX) (F G : X → ℝ) :
    |condDefect μ m F G| ≤ |cov μ F G| + |cov μ (μ[F | m]) (μ[G | m])| := by
  rw [condDefect_eq hm]; exact abs_sub _ _

/-- The coarse covariance is bounded by the information of the block σ-algebra about `F`. -/
theorem abs_cov_condExp_le {m : MeasurableSpace X} (hm : m ≤ mX) {F G : X → ℝ} (hF : Bdd1 μ F) (hG : Bdd1 μ G) :
    |cov μ (μ[F | m]) (μ[G | m])| ≤ ∫ x, |μ[F | m] x - ∫ y, F y ∂μ| ∂μ := by
  have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  have hEF := hF.condExp hm
  have hEG := hG.condExp hm
  set c := ∫ y, F y ∂μ with hc
  have i1 : Integrable (fun x => μ[F | m] x * μ[G | m] x) μ := (hEF.mul hEG).integrable
  have i2 : Integrable (fun x => c * μ[G | m] x) μ := hEG.integrable.const_mul c
  have i3 : Integrable (fun x => |μ[F | m] x - c|) μ := (hEF.integrable.sub (integrable_const c)).abs
  have e : cov μ (μ[F | m]) (μ[G | m]) = ∫ x, (μ[F | m] x * μ[G | m] x - c * μ[G | m] x) ∂μ := by
    unfold cov
    rw [integral_sub i1 i2, integral_const_mul, integral_condExp hm]
  rw [e]
  refine abs_integral_le_integral_abs.trans (integral_mono_ae (i1.sub i2).abs i3 ?_)
  filter_upwards [hEG.2] with x hx
  have e2 : μ[F | m] x * μ[G | m] x - c * μ[G | m] x = (μ[F | m] x - c) * μ[G | m] x := by ring
  rw [e2, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) hx

/-- **The noise-limit trap in reverse (quantitative).** `(c)` differs from the fine covariance by at most the `L¹`
information of the block σ-algebra about `F`. -/
theorem abs_condDefect_sub_cov_le {m : MeasurableSpace X} (hm : m ≤ mX) {F G : X → ℝ} (hF : Bdd1 μ F)
    (hG : Bdd1 μ G) :
    |condDefect μ m F G - cov μ F G| ≤ ∫ x, |μ[F | m] x - ∫ y, F y ∂μ| ∂μ := by
  rw [condDefect_eq hm, sub_sub_cancel_left, abs_neg]
  exact abs_cov_condExp_le hm hF hG

/-- **The noise-limit trap in reverse (exact).** If the block σ-algebra is independent of `F`, the conditional decoupling
defect **is** the fine covariance. -/
theorem condDefect_eq_cov_of_indep {m : MeasurableSpace X} (hm : m ≤ mX) {F G : X → ℝ} (hFm : Measurable[mX] F)
    (hF : Bdd1 μ F) (hG : Bdd1 μ G)
    (hind : ProbabilityTheory.Indep (MeasurableSpace.comap F inferInstance) m μ) :
    condDefect μ m F G = cov μ F G := by
  have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  have hsm : StronglyMeasurable[MeasurableSpace.comap F inferInstance] F :=
    (comap_measurable F).stronglyMeasurable
  have hce := condExp_indep_eq hFm.comap_le hm hsm hind
  have h0 : ∫ x, |μ[F | m] x - ∫ y, F y ∂μ| ∂μ = 0 := by
    rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
    · simp
    · filter_upwards [hce] with x hx
      rw [hx]; simp
  have h1 := abs_condDefect_sub_cov_le hm hF hG
  rw [h0] at h1
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h1)

/-- **Tower law for the defect.** -/
theorem condDefect_tower {𝒢 ℋ : MeasurableSpace X} (h𝒢 : 𝒢 ≤ ℋ) (hℋ : ℋ ≤ mX) (F G : X → ℝ) :
    condDefect μ 𝒢 F G = condDefect μ ℋ F G + condDefect μ 𝒢 (μ[F | ℋ]) (μ[G | ℋ]) := by
  have : IsFiniteMeasure (μ.trim hℋ) := isFiniteMeasure_trim hℋ
  have e : ∫ x, μ[μ[F | ℋ] | 𝒢] x * μ[μ[G | ℋ] | 𝒢] x ∂μ = ∫ x, μ[F | 𝒢] x * μ[G | 𝒢] x ∂μ := by
    apply integral_congr_ae
    filter_upwards [condExp_condExp_of_le (f := F) (μ := μ) h𝒢 hℋ,
      condExp_condExp_of_le (f := G) (μ := μ) h𝒢 hℋ] with x h1 h2
    rw [h1, h2]
  unfold condDefect
  rw [e]; ring

/-- `L¹` contraction of the conditional expectation, for differences. -/
theorem integral_abs_condExp_sub_le {m : MeasurableSpace X} {f g : X → ℝ} (hf : Integrable f μ)
    (hg : Integrable g μ) :
    ∫ x, |μ[f | m] x - μ[g | m] x| ∂μ ≤ ∫ x, |f x - g x| ∂μ := by
  have e : ∫ x, |μ[f | m] x - μ[g | m] x| ∂μ = ∫ x, |μ[f - g | m] x| ∂μ := by
    apply integral_congr_ae
    filter_upwards [condExp_sub hf hg m] with x hx
    rw [hx]; rfl
  rw [e]
  exact integral_abs_condExp_le (f - g)

theorem abs_integral_mul_sub_le {F G F' G' : X → ℝ} (hF : Bdd1 μ F) (hG : Bdd1 μ G) (hF' : Bdd1 μ F')
    (hG' : Bdd1 μ G') :
    |∫ x, F x * G x ∂μ - ∫ x, F' x * G' x ∂μ| ≤ ∫ x, |F x - F' x| ∂μ + ∫ x, |G x - G' x| ∂μ := by
  have i1 : Integrable (fun x => F x * G x) μ := (hF.mul hG).integrable
  have i2 : Integrable (fun x => F' x * G' x) μ := (hF'.mul hG').integrable
  have iF : Integrable (fun x => |F x - F' x|) μ := (hF.integrable.sub hF'.integrable).abs
  have iG : Integrable (fun x => |G x - G' x|) μ := (hG.integrable.sub hG'.integrable).abs
  rw [← integral_sub i1 i2, ← integral_add iF iG]
  refine abs_integral_le_integral_abs.trans (integral_mono_ae (i1.sub i2).abs (iF.add iG) ?_)
  filter_upwards [hG.2, hF'.2] with x hGx hF'x
  have e : F x * G x - F' x * G' x = (F x - F' x) * G x + F' x * (G x - G' x) := by ring
  show |F x * G x - F' x * G' x| ≤ |F x - F' x| + |G x - G' x|
  rw [e]
  calc _ ≤ |(F x - F' x) * G x| + |F' x * (G x - G' x)| := abs_add_le _ _
    _ = |F x - F' x| * |G x| + |F' x| * |G x - G' x| := by rw [abs_mul, abs_mul]
    _ ≤ |F x - F' x| * 1 + 1 * |G x - G' x| := by
        gcongr
    _ = _ := by ring

/-- **The defect is 2-Lipschitz in `L¹`** on functions bounded by one. -/
theorem abs_condDefect_sub_le {m : MeasurableSpace X} (hm : m ≤ mX) {F G F' G' : X → ℝ}
    (hF : Bdd1 μ F) (hG : Bdd1 μ G) (hF' : Bdd1 μ F') (hG' : Bdd1 μ G') :
    |condDefect μ m F G - condDefect μ m F' G'| ≤ 2 * (∫ x, |F x - F' x| ∂μ + ∫ x, |G x - G' x| ∂μ) := by
  have h1 := abs_integral_mul_sub_le hF hG hF' hG'
  have h2 := abs_integral_mul_sub_le (hF.condExp hm) (hG.condExp hm) (hF'.condExp hm) (hG'.condExp hm)
  have h3 := integral_abs_condExp_sub_le (m := m) hF.integrable hF'.integrable
  have h4 := integral_abs_condExp_sub_le (m := m) hG.integrable hG'.integrable
  have e : condDefect μ m F G - condDefect μ m F' G' =
      (∫ x, F x * G x ∂μ - ∫ x, F' x * G' x ∂μ) -
        (∫ x, μ[F | m] x * μ[G | m] x ∂μ - ∫ x, μ[F' | m] x * μ[G' | m] x ∂μ) := by
    unfold condDefect; ring
  rw [e]
  calc _ ≤ |∫ x, F x * G x ∂μ - ∫ x, F' x * G' x ∂μ| +
        |∫ x, μ[F | m] x * μ[G | m] x ∂μ - ∫ x, μ[F' | m] x * μ[G' | m] x ∂μ| := abs_sub _ _
    _ ≤ _ := by linarith

theorem abs_integral_le_one' {F : X → ℝ} (hF : Bdd1 μ F) : |∫ x, F x ∂μ| ≤ 1 := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := 1) (hF.2.mono fun x hx => by
    rwa [Real.norm_eq_abs])
  simpa using this

/-- **Given (b), the defect (c) is the fine covariance minus the coarse covariance of the approximants**, up to `4ε`. So
once the coarse side decays (from `LimitDprime`), (c) holds iff the fine covariance decays: (c) is not weaker than the
conclusion of the route; it is useful only through a mechanism that makes it small directly. -/
theorem abs_condDefect_sub_cov_sub_le {m : MeasurableSpace X} (hm : m ≤ mX) {F G f g : X → ℝ}
    (hF : Bdd1 μ F) (hG : Bdd1 μ G) (hf : Bdd1 μ f) (hg : Bdd1 μ g) {ε : ℝ}
    (hEF : ∫ x, |μ[F | m] x - f x| ∂μ ≤ ε) (hEG : ∫ x, |μ[G | m] x - g x| ∂μ ≤ ε) :
    |condDefect μ m F G - (cov μ F G - cov μ f g)| ≤ 4 * ε := by
  have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  have bEF := hF.condExp hm
  have bEG := hG.condExp hm
  have h1 := abs_integral_mul_sub_le bEF bEG hf hg
  have ha : |∫ x, μ[F | m] x ∂μ - ∫ x, f x ∂μ| ≤ ε := by
    rw [← integral_sub bEF.integrable hf.integrable]
    exact abs_integral_le_integral_abs.trans hEF
  have hb : |∫ x, μ[G | m] x ∂μ - ∫ x, g x ∂μ| ≤ ε := by
    rw [← integral_sub bEG.integrable hg.integrable]
    exact abs_integral_le_integral_abs.trans hEG
  have bb := abs_integral_le_one' bEG
  have bf := abs_integral_le_one' hf
  have hε : 0 ≤ ε := (integral_nonneg fun x => abs_nonneg _).trans hEF
  have hd : |(∫ x, μ[F | m] x ∂μ) * (∫ x, μ[G | m] x ∂μ) - (∫ x, f x ∂μ) * ∫ x, g x ∂μ| ≤ 2 * ε := by
    have e : (∫ x, μ[F | m] x ∂μ) * (∫ x, μ[G | m] x ∂μ) - (∫ x, f x ∂μ) * ∫ x, g x ∂μ =
        (∫ x, μ[F | m] x ∂μ - ∫ x, f x ∂μ) * (∫ x, μ[G | m] x ∂μ) +
          (∫ x, f x ∂μ) * (∫ x, μ[G | m] x ∂μ - ∫ x, g x ∂μ) := by ring
    rw [e]
    calc _ ≤ |(∫ x, μ[F | m] x ∂μ - ∫ x, f x ∂μ) * (∫ x, μ[G | m] x ∂μ)| +
          |(∫ x, f x ∂μ) * (∫ x, μ[G | m] x ∂μ - ∫ x, g x ∂μ)| := abs_add_le _ _
      _ = |∫ x, μ[F | m] x ∂μ - ∫ x, f x ∂μ| * |∫ x, μ[G | m] x ∂μ| +
          |∫ x, f x ∂μ| * |∫ x, μ[G | m] x ∂μ - ∫ x, g x ∂μ| := by rw [abs_mul, abs_mul]
      _ ≤ ε * 1 + 1 * ε := add_le_add (mul_le_mul ha bb (abs_nonneg _) hε) (mul_le_mul bf hb (abs_nonneg _) zero_le_one)
      _ = 2 * ε := by ring
  have e : condDefect μ m F G - (cov μ F G - cov μ f g) =
      -((∫ x, μ[F | m] x * μ[G | m] x ∂μ - ∫ x, f x * g x ∂μ) -
        ((∫ x, μ[F | m] x ∂μ) * (∫ x, μ[G | m] x ∂μ) - (∫ x, f x ∂μ) * ∫ x, g x ∂μ)) := by
    rw [condDefect_eq hm]; unfold cov; ring
  rw [e, abs_neg]
  calc _ ≤ |∫ x, μ[F | m] x * μ[G | m] x ∂μ - ∫ x, f x * g x ∂μ| +
        |(∫ x, μ[F | m] x ∂μ) * (∫ x, μ[G | m] x ∂μ) - (∫ x, f x ∂μ) * ∫ x, g x ∂μ| := abs_sub _ _
    _ ≤ (ε + ε) + 2 * ε := add_le_add (h1.trans (by linarith)) hd
    _ = 4 * ε := by ring

/-- Approximants pass through the tower: `‖E[F|𝒢] − f₂‖₁ ≤ ‖E[F|ℋ] − f₁‖₁ + ‖E[f₁|𝒢] − f₂‖₁`. -/
theorem approx_tower {𝒢 ℋ : MeasurableSpace X} (h𝒢 : 𝒢 ≤ ℋ) (hℋ : ℋ ≤ mX) {F f₁ f₂ : X → ℝ}
    (hF : Bdd1 μ F) (hf₁ : Bdd1 μ f₁) (hf₂ : Bdd1 μ f₂) :
    ∫ x, |μ[F | 𝒢] x - f₂ x| ∂μ ≤ ∫ x, |μ[F | ℋ] x - f₁ x| ∂μ + ∫ x, |μ[f₁ | 𝒢] x - f₂ x| ∂μ := by
  have : IsFiniteMeasure (μ.trim hℋ) := isFiniteMeasure_trim hℋ
  have hEℋ := hF.condExp hℋ
  have i1 : Integrable (fun x => |μ[F | 𝒢] x - μ[f₁ | 𝒢] x|) μ :=
    (integrable_condExp.sub integrable_condExp).abs
  have i2 : Integrable (fun x => |μ[f₁ | 𝒢] x - f₂ x|) μ := (integrable_condExp.sub hf₂.integrable).abs
  have hcontr : ∫ x, |μ[F | 𝒢] x - μ[f₁ | 𝒢] x| ∂μ ≤ ∫ x, |μ[F | ℋ] x - f₁ x| ∂μ := by
    have e : ∫ x, |μ[F | 𝒢] x - μ[f₁ | 𝒢] x| ∂μ = ∫ x, |μ[μ[F | ℋ] | 𝒢] x - μ[f₁ | 𝒢] x| ∂μ := by
      apply integral_congr_ae
      filter_upwards [condExp_condExp_of_le (f := F) (μ := μ) h𝒢 hℋ] with x hx
      rw [hx]
    rw [e]
    exact integral_abs_condExp_sub_le hEℋ.integrable hf₁.integrable
  calc ∫ x, |μ[F | 𝒢] x - f₂ x| ∂μ
      ≤ ∫ x, (|μ[F | 𝒢] x - μ[f₁ | 𝒢] x| + |μ[f₁ | 𝒢] x - f₂ x|) ∂μ := by
        refine integral_mono_ae (integrable_condExp.sub hf₂.integrable).abs (i1.add i2) (ae_of_all _ fun x => ?_)
        have e : μ[F | 𝒢] x - f₂ x = (μ[F | 𝒢] x - μ[f₁ | 𝒢] x) + (μ[f₁ | 𝒢] x - f₂ x) := by ring
        show |μ[F | 𝒢] x - f₂ x| ≤ |μ[F | 𝒢] x - μ[f₁ | 𝒢] x| + |μ[f₁ | 𝒢] x - f₂ x|
        rw [e]; exact abs_add_le _ _
    _ = ∫ x, |μ[F | 𝒢] x - μ[f₁ | 𝒢] x| ∂μ + ∫ x, |μ[f₁ | 𝒢] x - f₂ x| ∂μ := integral_add i1 i2
    _ ≤ _ := by linarith

/-- **The two-stage split.** Stage 1 (`ℋ`, the ultraviolet stage): approximants `f₁, g₁` of `E[F|ℋ], E[G|ℋ]` within `ε₁`,
defect `≤ δ₁`. Stage 2 (`𝒢 ≤ ℋ`, the crossover stage), **for the stage-1 approximants**: approximants `f₂, g₂` of
`E[f₁|𝒢], E[g₁|𝒢]` within `ε₂`, defect `≤ δ₂`. Then for `𝒢`: approximants within `ε₁ + ε₂`, defect
`≤ δ₁ + δ₂ + 4ε₁`. -/
theorem twoStage {𝒢 ℋ : MeasurableSpace X} (h𝒢 : 𝒢 ≤ ℋ) (hℋ : ℋ ≤ mX) {F G f₁ g₁ f₂ g₂ : X → ℝ}
    (hF : Bdd1 μ F) (hG : Bdd1 μ G) (hf₁ : Bdd1 μ f₁) (hg₁ : Bdd1 μ g₁) (hf₂ : Bdd1 μ f₂) (hg₂ : Bdd1 μ g₂)
    {ε₁ ε₂ δ₁ δ₂ : ℝ}
    (hUVf : ∫ x, |μ[F | ℋ] x - f₁ x| ∂μ ≤ ε₁) (hUVg : ∫ x, |μ[G | ℋ] x - g₁ x| ∂μ ≤ ε₁)
    (hUVc : |condDefect μ ℋ F G| ≤ δ₁)
    (hXf : ∫ x, |μ[f₁ | 𝒢] x - f₂ x| ∂μ ≤ ε₂) (hXg : ∫ x, |μ[g₁ | 𝒢] x - g₂ x| ∂μ ≤ ε₂)
    (hXc : |condDefect μ 𝒢 f₁ g₁| ≤ δ₂) :
    ∫ x, |μ[F | 𝒢] x - f₂ x| ∂μ ≤ ε₁ + ε₂ ∧ ∫ x, |μ[G | 𝒢] x - g₂ x| ∂μ ≤ ε₁ + ε₂ ∧
      |condDefect μ 𝒢 F G| ≤ δ₁ + δ₂ + 4 * ε₁ := by
  refine ⟨(approx_tower h𝒢 hℋ hF hf₁ hf₂).trans (by linarith),
    (approx_tower h𝒢 hℋ hG hg₁ hg₂).trans (by linarith), ?_⟩
  have hlip := abs_condDefect_sub_le (h𝒢.trans hℋ) (hF.condExp hℋ) (hG.condExp hℋ) hf₁ hg₁
  rw [condDefect_tower h𝒢 hℋ]
  calc |condDefect μ ℋ F G + condDefect μ 𝒢 (μ[F | ℋ]) (μ[G | ℋ])|
      ≤ |condDefect μ ℋ F G| + |condDefect μ 𝒢 (μ[F | ℋ]) (μ[G | ℋ]) - condDefect μ 𝒢 f₁ g₁| +
          |condDefect μ 𝒢 f₁ g₁| := by
        have := abs_add_le (condDefect μ ℋ F G)
          (condDefect μ 𝒢 (μ[F | ℋ]) (μ[G | ℋ]) - condDefect μ 𝒢 f₁ g₁ + condDefect μ 𝒢 f₁ g₁)
        have h2 := abs_add_le (condDefect μ 𝒢 (μ[F | ℋ]) (μ[G | ℋ]) - condDefect μ 𝒢 f₁ g₁)
          (condDefect μ 𝒢 f₁ g₁)
        simp only [sub_add_cancel] at this h2
        linarith
    _ ≤ δ₁ + 2 * (ε₁ + ε₁) + δ₂ := by linarith
    _ = δ₁ + δ₂ + 4 * ε₁ := by ring

end Generic

/-! ## Conditional expectations through a composite map -/

section Map

variable {X Y Z : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] [mZ : MeasurableSpace Z]
  (μ : Measure X) [IsProbabilityMeasure μ]

theorem comap_comp_le {B₁ : X → Y} {B₂ : Y → Z} (h1 : Measurable B₁) (h2 : Measurable B₂) :
    MeasurableSpace.comap (B₂ ∘ B₁) mZ ≤ MeasurableSpace.comap B₁ mY := by
  rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono h2.comap_le

/-- **Conditional expectations through a composite map are computed on the image law.** -/
theorem condExp_comp_map {B₁ : X → Y} {B₂ : Y → Z} (h1 : Measurable B₁) (h2 : Measurable B₂) {h : Y → ℝ}
    (hh : Integrable h (μ.map B₁)) :
    μ[h ∘ B₁ | MeasurableSpace.comap (B₂ ∘ B₁) mZ] =ᵐ[μ]
      ((μ.map B₁)[h | MeasurableSpace.comap B₂ mZ]) ∘ B₁ := by
  have hm : MeasurableSpace.comap (B₂ ∘ B₁) mZ ≤ mX := (h2.comp h1).comap_le
  have hm2 : MeasurableSpace.comap B₂ mZ ≤ mY := h2.comap_le
  have : IsProbabilityMeasure (μ.map B₁) := (Measure.isProbabilityMeasure_map_iff h1.aemeasurable).2 inferInstance
  have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  have : IsFiniteMeasure ((μ.map B₁).trim hm2) := isFiniteMeasure_trim hm2
  set ν := μ.map B₁
  have hint : Integrable (ν[h | MeasurableSpace.comap B₂ mZ] ∘ B₁) μ := integrable_condExp.comp_measurable h1
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm (hh.comp_measurable h1)
    (fun s _ _ => hint.integrableOn) (fun s hs _ => ?_) ?_).symm
  · obtain ⟨t, ht, rfl⟩ := hs
    have hB : MeasurableSet (B₂ ⁻¹' t) := h2 ht
    have hB' : MeasurableSet[MeasurableSpace.comap B₂ mZ] (B₂ ⁻¹' t) := ⟨t, ht, rfl⟩
    have e1 := setIntegral_map (μ := μ) (g := B₁) hB
      (stronglyMeasurable_condExp.mono hm2).aestronglyMeasurable h1.aemeasurable
      (f := ν[h | MeasurableSpace.comap B₂ mZ])
    have e2 := setIntegral_map (μ := μ) (g := B₁) hB hh.aestronglyMeasurable h1.aemeasurable
    have e3 := setIntegral_condExp hm2 hh hB'
    rw [Set.preimage_comp]
    show ∫ x in B₁ ⁻¹' (B₂ ⁻¹' t), ν[h | MeasurableSpace.comap B₂ mZ] (B₁ x) ∂μ = ∫ x in B₁ ⁻¹' (B₂ ⁻¹' t), h (B₁ x) ∂μ
    rw [← e1, ← e2, e3]
  · have hB1 : Measurable[MeasurableSpace.comap (B₂ ∘ B₁) mZ, MeasurableSpace.comap B₂ mZ] B₁ := by
      rw [measurable_iff_comap_le, MeasurableSpace.comap_comp]
    exact (stronglyMeasurable_condExp.comp_measurable hB1).aestronglyMeasurable

/-- The defect of a pulled-back pair equals the defect on the image law. -/
theorem condDefect_map {B₁ : X → Y} {B₂ : Y → Z} (h1 : Measurable B₁) (h2 : Measurable B₂) {f g : Y → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf1 : ∀ y, |f y| ≤ 1) (hg1 : ∀ y, |g y| ≤ 1) :
    condDefect μ (MeasurableSpace.comap (B₂ ∘ B₁) mZ) (f ∘ B₁) (g ∘ B₁) =
      condDefect (μ.map B₁) (MeasurableSpace.comap B₂ mZ) f g := by
  have : IsProbabilityMeasure (μ.map B₁) := (Measure.isProbabilityMeasure_map_iff h1.aemeasurable).2 inferInstance
  have hm2 : MeasurableSpace.comap B₂ mZ ≤ mY := h2.comap_le
  have bf : Bdd1 (μ.map B₁) f := Bdd1.of_measurable hf hf1
  have bg : Bdd1 (μ.map B₁) g := Bdd1.of_measurable hg hg1
  have cf := condExp_comp_map μ h1 h2 bf.integrable
  have cg := condExp_comp_map μ h1 h2 bg.integrable
  unfold condDefect
  have e1 : ∫ y, f y * g y ∂(μ.map B₁) = ∫ x, (f ∘ B₁) x * (g ∘ B₁) x ∂μ :=
    integral_map h1.aemeasurable (hf.mul hg).aestronglyMeasurable
  have e2 : ∫ y, (μ.map B₁)[f | MeasurableSpace.comap B₂ mZ] y * (μ.map B₁)[g | MeasurableSpace.comap B₂ mZ] y
      ∂(μ.map B₁) = ∫ x, μ[f ∘ B₁ | MeasurableSpace.comap (B₂ ∘ B₁) mZ] x *
        μ[g ∘ B₁ | MeasurableSpace.comap (B₂ ∘ B₁) mZ] x ∂μ := by
    rw [integral_map (μ := μ) (φ := B₁) h1.aemeasurable
      (f := fun y => (μ.map B₁)[f | MeasurableSpace.comap B₂ mZ] y * (μ.map B₁)[g | MeasurableSpace.comap B₂ mZ] y)
      (((stronglyMeasurable_condExp.mono hm2).mul (stronglyMeasurable_condExp.mono hm2)).aestronglyMeasurable)]
    apply integral_congr_ae
    filter_upwards [cf, cg] with x hx1 hx2
    rw [hx1, hx2]; rfl
  rw [e1, e2]

/-- `L¹` distance of a pulled-back approximant, computed on the image law. -/
theorem approx_map {B₁ : X → Y} {B₂ : Y → Z} (h1 : Measurable B₁) (h2 : Measurable B₂) {f : Y → ℝ} {φ : Z → ℝ}
    (hf : Measurable f) (hf1 : ∀ y, |f y| ≤ 1) (hφ : Measurable φ) :
    ∫ x, |μ[f ∘ B₁ | MeasurableSpace.comap (B₂ ∘ B₁) mZ] x - φ (B₂ (B₁ x))| ∂μ =
      ∫ y, |(μ.map B₁)[f | MeasurableSpace.comap B₂ mZ] y - φ (B₂ y)| ∂(μ.map B₁) := by
  have : IsProbabilityMeasure (μ.map B₁) := (Measure.isProbabilityMeasure_map_iff h1.aemeasurable).2 inferInstance
  have hm2 : MeasurableSpace.comap B₂ mZ ≤ mY := h2.comap_le
  have cf := condExp_comp_map μ h1 h2 (Bdd1.of_measurable (μ := μ.map B₁) hf hf1).integrable
  rw [integral_map (μ := μ) (φ := B₁) h1.aemeasurable
    (f := fun y => |(μ.map B₁)[f | MeasurableSpace.comap B₂ mZ] y - φ (B₂ y)|)
    (((stronglyMeasurable_condExp.mono hm2).aestronglyMeasurable.sub (hφ.comp h2).aestronglyMeasurable).norm)]
  apply integral_congr_ae
  filter_upwards [cf] with x hx
  rw [hx]; rfl

end Map

/-! ## The Yang–Mills instance: the composite of two reflection-respecting blockings of the Wilson measure -/

section Blocked

open AreaLaw.Concrete

theorem ymProb (T : Tuning) (k j : ℕ) : IsProbabilityMeasure (T.ym k j) :=
  OneScale.Gauge.isProbabilityMeasure_gaugeMeasure (d := 4) (N := T.side k j) continuous_subtype_val
    (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) (posWeight_wilson 2 (T.β k))

/-- **The two-stage split for the Wilson measure.** `B₁` blocks the fine torus onto an intermediate torus (cells of an
ultraviolet size `L₀`), `B₂` blocks the intermediate torus onto the coarse one (cells `L₁`). Hypotheses: (UV) the estimates
(b), (c) of `ObsTransferPhys` for `B₁` on the SU(2) Wilson measure, with intermediate approximants `f₁, g₁`; (X) the
estimates for `f₁, g₁` and `B₂` **on the intermediate blocked law** `(T.ym k j).map B₁`. Conclusion: the estimates (b),
(c) for the composite `B₁.comp B₂`, in the syntactic form of `ObsTransferPhys`. -/
theorem twoStage_blocked (T : Tuning) (k j : ℕ) {K : ℕ} [NeZero K]
    (B₁ : RPBlocking SU2 4 (T.side k j) K) (B₂ : RPBlocking SU2 4 K (coarseSide j))
    {F G : GaugeConnection SU2 4 (T.side k j) → ℝ} {f₁ g₁ : GaugeConnection SU2 4 K → ℝ}
    {f g : GaugeConnection SU2 4 (coarseSide j) → ℝ}
    (hF : Measurable F) (hG : Measurable G) (hF1 : ∀ U, |F U| ≤ 1) (hG1 : ∀ U, |G U| ≤ 1)
    (hf₁ : Measurable f₁) (hg₁ : Measurable g₁) (hf₁1 : ∀ W, |f₁ W| ≤ 1) (hg₁1 : ∀ W, |g₁ W| ≤ 1)
    (hf : Measurable f) (hg : Measurable g) (hf1 : ∀ V, |f V| ≤ 1) (hg1 : ∀ V, |g V| ≤ 1)
    {ε₁ ε₂ δ₁ δ₂ : ℝ}
    (hUVf : ∫ U, |condExp (MeasurableSpace.comap B₁.B inferInstance) (T.ym k j) F U - f₁ (B₁.B U)| ∂(T.ym k j) ≤ ε₁)
    (hUVg : ∫ U, |condExp (MeasurableSpace.comap B₁.B inferInstance) (T.ym k j) G U - g₁ (B₁.B U)| ∂(T.ym k j) ≤ ε₁)
    (hUVc : |∫ U, F U * G U ∂(T.ym k j) -
        ∫ U, condExp (MeasurableSpace.comap B₁.B inferInstance) (T.ym k j) F U *
          condExp (MeasurableSpace.comap B₁.B inferInstance) (T.ym k j) G U ∂(T.ym k j)| ≤ δ₁)
    (hXf : ∫ W, |condExp (MeasurableSpace.comap B₂.B inferInstance) ((T.ym k j).map B₁.B) f₁ W - f (B₂.B W)|
        ∂((T.ym k j).map B₁.B) ≤ ε₂)
    (hXg : ∫ W, |condExp (MeasurableSpace.comap B₂.B inferInstance) ((T.ym k j).map B₁.B) g₁ W - g (B₂.B W)|
        ∂((T.ym k j).map B₁.B) ≤ ε₂)
    (hXc : |condDefect ((T.ym k j).map B₁.B) (MeasurableSpace.comap B₂.B inferInstance) f₁ g₁| ≤ δ₂) :
    ∫ U, |condExp (MeasurableSpace.comap (B₁.comp B₂).B inferInstance) (T.ym k j) F U - f ((B₁.comp B₂).B U)|
        ∂(T.ym k j) ≤ ε₁ + ε₂ ∧
    ∫ U, |condExp (MeasurableSpace.comap (B₁.comp B₂).B inferInstance) (T.ym k j) G U - g ((B₁.comp B₂).B U)|
        ∂(T.ym k j) ≤ ε₁ + ε₂ ∧
    |∫ U, F U * G U ∂(T.ym k j) -
        ∫ U, condExp (MeasurableSpace.comap (B₁.comp B₂).B inferInstance) (T.ym k j) F U *
          condExp (MeasurableSpace.comap (B₁.comp B₂).B inferInstance) (T.ym k j) G U ∂(T.ym k j)|
      ≤ δ₁ + δ₂ + 4 * ε₁ := by
  have := ymProb T k j
  set μ := T.ym k j
  have h1 := B₁.meas
  have h2 := B₂.meas
  have hcomp : (B₁.comp B₂).B = B₂.B ∘ B₁.B := rfl
  have hℋ : MeasurableSpace.comap B₁.B inferInstance ≤ (inferInstance : MeasurableSpace _) := h1.comap_le
  have h𝒢 := comap_comp_le h1 h2
  rw [hcomp]
  -- stage 2 pulled back to the fine measure
  have bf₁ : Bdd1 μ (f₁ ∘ B₁.B) := Bdd1.of_measurable (hf₁.comp h1) fun _ => hf₁1 _
  have bg₁ : Bdd1 μ (g₁ ∘ B₁.B) := Bdd1.of_measurable (hg₁.comp h1) fun _ => hg₁1 _
  have bf₂ : Bdd1 μ (fun U => f ((B₂.B ∘ B₁.B) U)) := Bdd1.of_measurable (hf.comp (h2.comp h1)) fun _ => hf1 _
  have bg₂ : Bdd1 μ (fun U => g ((B₂.B ∘ B₁.B) U)) := Bdd1.of_measurable (hg.comp (h2.comp h1)) fun _ => hg1 _
  have hXf' : ∫ U, |μ[f₁ ∘ B₁.B | MeasurableSpace.comap (B₂.B ∘ B₁.B) inferInstance] U - f ((B₂.B ∘ B₁.B) U)| ∂μ
      ≤ ε₂ := by
    exact (approx_map μ h1 h2 hf₁ hf₁1 hf).trans_le hXf
  have hXg' : ∫ U, |μ[g₁ ∘ B₁.B | MeasurableSpace.comap (B₂.B ∘ B₁.B) inferInstance] U - g ((B₂.B ∘ B₁.B) U)| ∂μ
      ≤ ε₂ := by
    exact (approx_map μ h1 h2 hg₁ hg₁1 hg).trans_le hXg
  have hXc' : |condDefect μ (MeasurableSpace.comap (B₂.B ∘ B₁.B) inferInstance) (f₁ ∘ B₁.B) (g₁ ∘ B₁.B)| ≤ δ₂ := by
    exact (condDefect_map μ h1 h2 hf₁ hg₁ hf₁1 hg₁1).symm ▸ hXc
  exact twoStage h𝒢 hℋ (Bdd1.of_measurable hF hF1) (Bdd1.of_measurable hG hG1) bf₁ bg₁ bf₂ bg₂ hUVf hUVg hUVc
    hXf' hXg' hXc'

end Blocked

end ProofPhase.UV
