/-
Proof phase, cycle 6, workstream 5 (c6e-bookkeeping): the kernel density of the noisy good blocking (2026-11-22).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c6e-bookkeeping/NOTE.md`, section 1.
-/

import ProofPhase.Book.NoiseLaw
import ProofPhase.Book.SU2Inst
import ProofPhase.Repair.Noisy

/-!
# `KernelDensity` for the noisy good blocking, and the Gibbs representation without a named hypothesis

`Repair.noisy_blockedLaw_gibbs` needs `KernelDensity NB k j`. Here it is proved for every noise law of the form
`τ = h · Haar` with `h` measurable and `0 < m ≤ h ≤ M` (a `NoiseDensity`), for the multiplicative noisy blocking
of **any** reflection-respecting blocking (`mulNoise_kernel`) and so for `goodNoisyFamily`.

* `NoiseDensity`: a density `h` for the single-link noise law (`law = h · Haar`, a probability measure).
* `mulNoise_kernel` (S): `κ(U, φ) = ∏_l linkKernel h l (b_l(U)) (φ_l)` is jointly measurable, lies in `[m^E, M^E]`
  (`E` = number of links of the coarse torus), and is the density of the law of `mulNoise (P.B U) η`.
* `goodNoisy_kernelDensity` (S): `KernelDensity (goodNoisyFamily T w n hn ND.law) k j` for **every** level and volume.
* `goodNoisy_gibbs` (S): the noisy good blocking's blocked law is `gibbsMeasure (haarG SU2) V` for a bounded `CoarsePot`
  `V`, for every level and volume, with no `KernelDensity` hypothesis left.
* The concrete law: `vmf κ` (von Mises–Fisher type), `h = exp(κ Re tr g) / Z`, `Z = ∫ exp(κ Re tr) dHaar`. It is
  continuous (`continuous_vmfDensity`) and strictly positive, with `e^{-2|κ|}/Z ≤ h ≤ e^{2|κ|}/Z`.
  `goodNoisyVMF_gibbs`: the statement for it, every `κ`.

The heat kernel on SU(2) is not in Mathlib or in the project (no Laplace–Beltrami operator or heat semigroup on a
compact Lie group), so the von Mises–Fisher law stands in. For the route nothing else is used: the representation
needs only a density in `[m, M]` with `m > 0`; class-function and inversion-symmetry properties of the heat kernel are
not needed (the density of the noise law on a negative temporal link is `h(b φ⁻¹)` instead of `h(b⁻¹ φ)`).
-/

open MeasureTheory Finset AreaLaw.Concrete Positivity ProofPhase.Repair

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Book

/-- **A density for the single-link noise law**: `τ = h · Haar`, with `0 < m ≤ h ≤ M`, a probability law. -/
structure NoiseDensity where
  h : SU2 → ℝ
  meas : Measurable h
  m : ℝ
  M : ℝ
  m_pos : 0 < m
  lo : ∀ g, m ≤ h g
  hi : ∀ g, h g ≤ M
  norm : ∫⁻ g, ENNReal.ofReal (h g) ∂(haarG SU2) = 1

/-- The noise law `h · Haar`. -/
def NoiseDensity.law (ND : NoiseDensity) : Measure SU2 :=
  (haarG SU2).withDensity (fun g => ENNReal.ofReal (ND.h g))

instance (ND : NoiseDensity) : IsProbabilityMeasure ND.law :=
  ⟨by simp [NoiseDensity.law, withDensity_apply _ MeasurableSet.univ, ND.norm]⟩

theorem NoiseDensity.nonneg (ND : NoiseDensity) (g : SU2) : 0 ≤ ND.h g := ND.m_pos.le.trans (ND.lo g)

/-- **The kernel of the multiplicative noise has a density in `[m^E, M^E]`** (S), for any reflection-respecting
blocking `P`: jointly measurable `κ`, with the law of `mulNoise (P.B U) η` equal to `κ(U, ·) · Haar`. -/
theorem mulNoise_kernel (ND : NoiseDensity) {N M : ℕ} [NeZero N] [NeZero M] (hM : Even M) (P : RPBlocking SU2 4 N M) :
    ∃ (κ : GaugeConnection SU2 4 N → GaugeConnection SU2 4 M → ℝ) (m Mx : ℝ),
      Measurable (Function.uncurry κ) ∧ 0 < m ∧ (∀ U φ, m ≤ κ U φ) ∧ (∀ U φ, κ U φ ≤ Mx) ∧
      ∀ U, (((Measure.pi fun _ : FixLink 4 M => ND.law).prod
        ((Measure.pi fun _ : PosLink 4 M => ND.law).prod (Measure.pi fun _ : PosLink 4 M => ND.law)))).map
          (fun η => mulNoise hM (P.B U) η) =
        (productHaar SU2 4 M).withDensity (fun φ => ENNReal.ofReal (κ U φ)) := by
  have hC : ∀ g, ND.h g ≤ ND.M := ND.hi
  refine ⟨fun U φ => ∏ l, linkKernel ND.h l (P.B U l) (φ l), ND.m ^ (Finset.univ : Finset (LatticeLink 4 M)).card,
    ND.M ^ (Finset.univ : Finset (LatticeLink 4 M)).card, ?_, pow_pos ND.m_pos _, ?_, ?_, ?_⟩
  · show Measurable (fun q : GaugeConnection SU2 4 N × GaugeConnection SU2 4 M =>
      ∏ l, linkKernel ND.h l (P.B q.1 l) (q.2 l))
    refine Finset.measurable_prod _ fun l _ => ?_
    have h1 : Measurable (fun q : GaugeConnection SU2 4 N × GaugeConnection SU2 4 M => (P.B q.1 l, q.2 l)) :=
      ((measurable_pi_apply l).comp (P.meas.comp measurable_fst)).prodMk ((measurable_pi_apply l).comp measurable_snd)
    exact measurable_linkKernel' ND.meas l ((measurable_pi_apply l).comp (P.meas.comp measurable_fst)) ((measurable_pi_apply l).comp measurable_snd)
  · intro U φ
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod₀ (fun _ _ => ND.m_pos.le) fun l _ => ?_
    unfold linkKernel; split_ifs <;> exact ND.lo _
  · intro U φ
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod₀ (fun l _ => ?_) fun l _ => ?_
    · unfold linkKernel; split_ifs <;> exact ND.nonneg _
    · unfold linkKernel; split_ifs <;> exact ND.hi _
  · intro U
    haveI : IsProbabilityMeasure ((haarG SU2).withDensity (fun z => ENNReal.ofReal (ND.h z))) :=
      (inferInstance : IsProbabilityMeasure ND.law)
    exact mulNoise_law hM (haarG SU2) ND.meas ND.nonneg hC (P.B U)

/-- **`KernelDensity` for the noisy good blocking, every level and volume** (S). -/
theorem goodNoisy_kernelDensity (ND : NoiseDensity) (T : Tuning) (w : ℝ) (n : ℕ → ℕ) (hn : ∀ k, T.ℓ k = 2 ^ n k)
    (k j : ℕ) : KernelDensity (goodNoisyFamily T w n hn ND.law) k j := by
  obtain ⟨κ, m, Mx, hκ, hm, hlo, hhi, hlaw⟩ :=
    mulNoise_kernel ND (RouteA.even_coarseSide j) (RouteA.goodBlocking T w n hn k j)
  exact ⟨κ, m, Mx, hκ, hm, hlo, hhi, hlaw⟩

/-- **The Gibbs representation of the noisy good blocking, with no named hypothesis** (S): for every noise density,
level and volume, the blocked law is the Gibbs measure (w.r.t. Haar) of a bounded coarse potential. -/
theorem goodNoisy_gibbs (ND : NoiseDensity) (T : Tuning) (w : ℝ) (n : ℕ → ℕ) (hn : ∀ k, T.ℓ k = 2 ^ n k) (k j : ℕ) :
    ∃ V : CoarsePot j, Attempts.R3.Potential (fun A => A) V ∧
      noisyBlockedLaw (goodNoisyFamily T w n hn ND.law) k j = Attempts.R3.gibbsMeasure (haarG SU2) V :=
  noisy_blockedLaw_gibbs _ k j (goodNoisy_kernelDensity ND T w n hn k j)

/-- The same for all levels and volumes at once. -/
theorem goodNoisy_gibbs_all (ND : NoiseDensity) (T : Tuning) (w : ℝ) (n : ℕ → ℕ) (hn : ∀ k, T.ℓ k = 2 ^ n k) :
    ∀ k j : ℕ, ∃ V : CoarsePot j, Attempts.R3.Potential (fun A => A) V ∧
      noisyBlockedLaw (goodNoisyFamily T w n hn ND.law) k j = Attempts.R3.gibbsMeasure (haarG SU2) V :=
  fun k j => goodNoisy_gibbs ND T w n hn k j

/-! ## The concrete law: von Mises–Fisher type, `h = exp(κ Re tr g) / Z` -/

section VMF

/-- `Re tr` on SU(2) is continuous. -/
theorem continuous_reTr : Continuous (fun g : SU2 => gaugeReTr SU2 2 g) := by
  unfold gaugeReTr gaugeTrace
  exact Complex.continuous_re.comp
    ((Continuous.matrix_trace (continuous_subtype_val)))

theorem abs_reTr_le (g : SU2) : |gaugeReTr SU2 2 g| ≤ 2 := by
  have h : |gaugeReTr SU2 2 g| ≤ ((2 : ℕ) : ℝ) :=
    abs_re_trace_le_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
  exact_mod_cast h

/-- The unnormalised density `exp(κ Re tr g)`. -/
def vmfRaw (κ : ℝ) (g : SU2) : ℝ := Real.exp (κ * gaugeReTr SU2 2 g)

theorem continuous_vmfRaw (κ : ℝ) : Continuous (vmfRaw κ) :=
  Real.continuous_exp.comp (continuous_const.mul continuous_reTr)

theorem integrable_vmfRaw (κ : ℝ) : Integrable (vmfRaw κ) (haarG SU2) :=
  (continuous_vmfRaw κ).integrable_of_hasCompactSupport (μ := haarG SU2) (HasCompactSupport.of_compactSpace _)

theorem vmfRaw_lo (κ : ℝ) (g : SU2) : Real.exp (-(2 * |κ|)) ≤ vmfRaw κ g := by
  unfold vmfRaw
  refine Real.exp_le_exp.2 ?_
  have h1 := abs_reTr_le g
  have h2 : |κ * gaugeReTr SU2 2 g| ≤ |κ| * 2 := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have := neg_abs_le (κ * gaugeReTr SU2 2 g)
  linarith

theorem vmfRaw_hi (κ : ℝ) (g : SU2) : vmfRaw κ g ≤ Real.exp (2 * |κ|) := by
  unfold vmfRaw
  refine Real.exp_le_exp.2 ?_
  have h1 := abs_reTr_le g
  have h2 : |κ * gaugeReTr SU2 2 g| ≤ |κ| * 2 := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have := le_abs_self (κ * gaugeReTr SU2 2 g)
  linarith

/-- The normalisation `Z(κ) = ∫ exp(κ Re tr) dHaar`. -/
def vmfZ (κ : ℝ) : ℝ := ∫ g, vmfRaw κ g ∂(haarG SU2)

theorem vmfZ_lo (κ : ℝ) : Real.exp (-(2 * |κ|)) ≤ vmfZ κ := by
  have := integral_mono (integrable_const (Real.exp (-(2 * |κ|))))
    (integrable_vmfRaw κ) (vmfRaw_lo κ)
  unfold vmfZ
  simpa using this

theorem vmfZ_pos (κ : ℝ) : 0 < vmfZ κ := (Real.exp_pos _).trans_le (vmfZ_lo κ)

/-- **The von Mises–Fisher type noise density on SU(2)**: `h = exp(κ Re tr g)/Z`, in
`[e^{-2|κ|}/Z, e^{2|κ|}/Z]`. -/
def vmf (κ : ℝ) : NoiseDensity where
  h g := vmfRaw κ g / vmfZ κ
  meas := ((continuous_vmfRaw κ).measurable).div_const _
  m := Real.exp (-(2 * |κ|)) / vmfZ κ
  M := Real.exp (2 * |κ|) / vmfZ κ
  m_pos := div_pos (Real.exp_pos _) (vmfZ_pos κ)
  lo g := div_le_div_of_nonneg_right (vmfRaw_lo κ g) (vmfZ_pos κ).le
  hi g := div_le_div_of_nonneg_right (vmfRaw_hi κ g) (vmfZ_pos κ).le
  norm := by
    have hint : Integrable (fun g => vmfRaw κ g / vmfZ κ) (haarG SU2) :=
      (integrable_vmfRaw κ).div_const _
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun g => div_nonneg ((Real.exp_pos _).le) (vmfZ_pos κ).le)]
    rw [integral_div]
    have : ∫ g, vmfRaw κ g ∂(haarG SU2) = vmfZ κ := rfl
    rw [this, div_self (vmfZ_pos κ).ne']
    simp

/-- The von Mises–Fisher density is continuous and strictly positive. -/
theorem continuous_vmfDensity (κ : ℝ) : Continuous (vmf κ).h :=
  (continuous_vmfRaw κ).div_const _

theorem vmfDensity_pos (κ : ℝ) (g : SU2) : 0 < (vmf κ).h g :=
  (vmf κ).m_pos.trans_le ((vmf κ).lo g)

/-- **The noisy good blocking with von Mises–Fisher noise: the Gibbs representation holds in every volume, with no
hypothesis** (S). -/
theorem goodNoisyVMF_gibbs (κ : ℝ) (T : Tuning) (w : ℝ) (n : ℕ → ℕ) (hn : ∀ k, T.ℓ k = 2 ^ n k) (k j : ℕ) :
    ∃ V : CoarsePot j, Attempts.R3.Potential (fun A => A) V ∧
      noisyBlockedLaw (goodNoisyFamily T w n hn (vmf κ).law) k j = Attempts.R3.gibbsMeasure (haarG SU2) V :=
  goodNoisy_gibbs (vmf κ) T w n hn k j

end VMF

end ProofPhase.Book
