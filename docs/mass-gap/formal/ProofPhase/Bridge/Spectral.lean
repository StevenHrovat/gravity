/-
RH-YM bridge, Part 1, module 4: Instance B, the Yang-Mills side. For a positive spectral measure, the exponential
decay rate of the correlation equals the bottom of the support, and the Laplace transform of the correlation is
singular exactly there (2026-11-23). Released under Apache 2.0.

Note: `docs/rh-guide/bridge/BRIDGE.md`.
-/

import ProofPhase.Bridge.Laplace
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Spectral gap = decay rate, and the singularity at the bottom of the spectrum

**Setting.** `ν` is a finite measure on `ℝ` living on `[0, ∞)`: abstractly the spectral measure of a vector `F`
for a self-adjoint `H ≥ 0` (reflection positivity gives the Hilbert space and `H`; OS reconstruction). The correlation
is `corr ν t = ∫ e^{-t E} dν(E)`, which is `⟨F, e^{-tH} F⟩` by the spectral theorem (classical, not formalized here:
Mathlib has no spectral measure of an unbounded self-adjoint operator). It is the Laplace transform of `ν` at real `t`
(`lap_ofReal_eq_corr`).

**Main results.**
* `corr_le_of_gap`, `corr_ge`: the two one-sided bounds.
* `spectral_gap_iff_nat`: `(∃ K, ∀ n : ℕ, corr ν n ≤ K e^{-m n}) ↔ ν (Iio m) = 0`. The left side has exactly the shape
  of the block-level decay hypothesis `hdec` of `ProofPhase.M1.UVTV.RPData.gap_of_RP` (`Q g (τ^n g) ≤ C e^{-m n}`),
  read through the spectral measure of `g` for the transfer operator `T = e^{-H}`. So that hypothesis says precisely
  that the spectral measure of `g` puts no mass below `m`. `spectral_gap_iff` is the continuous-time form.
* `decayRates_eq`: the set of admissible decay rates equals `{m | ν (Iio m) = 0}`, so the best decay rate (its
  supremum) is the bottom of the support.
* `resolvent_singular`: **the Pringsheim-Landau statement on this side.** Let `corrMeasure ν` be the positive measure
  `C(t) dt` on `(0, ∞)`. Its Laplace transform `∫₀^∞ e^{-s t} C(t) dt` (classically `⟨F, (H + s)⁻¹ F⟩`) converges for
  real `s > -l₀` and diverges for `s < -l₀`, where `l₀` is the bottom of the support of `ν`; by `laplace_landau` it
  has no holomorphic extension to any disc about `s = -l₀`. The gap is a singularity of the resolvent, located by
  positivity, exactly as Landau locates the first singularity of a Dirichlet series with non-negative coefficients.

**From Mathlib:** `setIntegral_ge_of_const_le`, `setIntegral_le_integral`, `integral_mono_ae`, `withDensity`,
`lintegral_withDensity_eq_lintegral_mul`, `exp_neg_integrableOn_Ioi`, `StronglyMeasurable.integral_prod_right'`.
The decay/support equivalence and the singularity statement are added here.
-/

open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace ProofPhase.Bridge

variable {ν : Measure ℝ}

/-- The correlation `t ↦ ∫ e^{-t E} dν(E)`. -/
def corr (ν : Measure ℝ) (t : ℝ) : ℝ := ∫ E, Real.exp (-(t * E)) ∂ν

/-- The correlation is the Laplace transform of the spectral measure at real `t`. -/
theorem lap_ofReal_eq_corr (ν : Measure ℝ) (t : ℝ) : lap ν (t : ℂ) = (corr ν t : ℂ) := by
  rw [lap, corr, ← integral_complex_ofReal]
  congr 1; funext E
  push_cast; ring_nf

variable [IsFiniteMeasure ν]

theorem integrable_corr (hν : ∀ᵐ E ∂ν, 0 ≤ E) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun E => Real.exp (-(t * E))) ν := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (hν.mono fun E hE => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
  nlinarith

/-- **Gap gives decay.** No spectral mass below `m` gives `corr ν t ≤ ν(ℝ) e^{-m t}` for `t ≥ 0`. -/
theorem corr_le_of_gap {m : ℝ} (hgap : ν (Iio m) = 0) {t : ℝ} (ht : 0 ≤ t) :
    corr ν t ≤ ν.real univ * Real.exp (-(m * t)) := by
  have hae : ∀ᵐ E ∂ν, m ≤ E := by
    rw [ae_iff]
    convert hgap using 2
    ext E; simp
  have hb : ∀ᵐ E ∂ν, Real.exp (-(t * E)) ≤ Real.exp (-(m * t)) :=
    hae.mono fun E hE => Real.exp_le_exp.mpr (by nlinarith)
  have hint : Integrable (fun E => Real.exp (-(t * E))) ν :=
    (integrable_const (Real.exp (-(m * t)))).mono' (by fun_prop)
      (hb.mono fun E hE => by rwa [Real.norm_of_nonneg (Real.exp_pos _).le])
  calc corr ν t ≤ ∫ _E, Real.exp (-(m * t)) ∂ν := integral_mono_ae hint (integrable_const _) hb
    _ = ν.real univ * Real.exp (-(m * t)) := by rw [integral_const, smul_eq_mul]

/-- **Mass below `m` forces slow decay.** `ν(Iio m) e^{-m t} ≤ corr ν t` for `t ≥ 0`. -/
theorem corr_ge (hν : ∀ᵐ E ∂ν, 0 ≤ E) (m : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ν.real (Iio m) * Real.exp (-(m * t)) ≤ corr ν t := by
  have hint := integrable_corr hν ht
  have h1 := setIntegral_ge_of_const_le (c := Real.exp (-(m * t))) (measurableSet_Iio (a := m))
    (measure_ne_top ν _) (fun E hE => Real.exp_le_exp.mpr (by
      have : E < m := hE
      nlinarith)) hint.integrableOn
  have h2 := setIntegral_le_integral (s := Iio m) hint
    (Eventually.of_forall fun E => (Real.exp_pos (-(t * E))).le)
  rw [smul_eq_mul] at h1
  rw [corr]
  linarith

/-- **Decay gives a gap** (discrete time). -/
theorem gap_of_decay_nat (hν : ∀ᵐ E ∂ν, 0 ≤ E) {m K : ℝ}
    (hdec : ∀ n : ℕ, corr ν n ≤ K * Real.exp (-(m * n))) : ν (Iio m) = 0 := by
  have key : ∀ m' < m, ν (Iio m') = 0 := by
    intro m' hm'
    have hle : ∀ n : ℕ, ν.real (Iio m') ≤ K * Real.exp (-((m - m') * n)) := by
      intro n
      have h1 := corr_ge hν m' (t := n) (Nat.cast_nonneg n)
      have hpos := Real.exp_pos (-(m' * n))
      have : ν.real (Iio m') * Real.exp (-(m' * n))
          ≤ (K * Real.exp (-((m - m') * n))) * Real.exp (-(m' * n)) := by
        calc _ ≤ corr ν n := h1
          _ ≤ K * Real.exp (-(m * n)) := hdec n
          _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      exact le_of_mul_le_mul_right this hpos
    have htend : Tendsto (fun n : ℕ => K * Real.exp (-((m - m') * n))) atTop (𝓝 (K * 0)) := by
      apply Tendsto.const_mul
      have h1 : Tendsto (fun n : ℕ => (m - m') * (n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith)
      exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
    have h0 : ν.real (Iio m') ≤ 0 := by
      have := ge_of_tendsto' htend hle
      simpa using this
    have hz : ν.real (Iio m') = 0 := le_antisymm h0 measureReal_nonneg
    rwa [measureReal_eq_zero_iff (measure_ne_top ν _)] at hz
  have hU : Iio m = ⋃ k : ℕ, Iio (m - 1 / ((k : ℝ) + 1)) := by
    ext E
    simp only [mem_Iio, mem_iUnion]
    constructor
    · intro hE
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hE)
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  rw [hU]
  exact measure_iUnion_null fun k => key _ (by
    have : 0 < 1 / ((k : ℝ) + 1) := by positivity
    linarith)

/-- **Spectral gap ⟺ exponential decay** (discrete time, the shape of `gap_of_RP`'s `hdec`). -/
theorem spectral_gap_iff_nat (hν : ∀ᵐ E ∂ν, 0 ≤ E) (m : ℝ) :
    (∃ K : ℝ, ∀ n : ℕ, corr ν n ≤ K * Real.exp (-(m * n))) ↔ ν (Iio m) = 0 :=
  ⟨fun ⟨_, hK⟩ => gap_of_decay_nat hν hK,
    fun h => ⟨ν.real univ, fun n => corr_le_of_gap h (Nat.cast_nonneg n)⟩⟩

/-- **Spectral gap ⟺ exponential decay** (continuous time). -/
theorem spectral_gap_iff (hν : ∀ᵐ E ∂ν, 0 ≤ E) (m : ℝ) :
    (∃ K : ℝ, ∀ t : ℝ, 0 ≤ t → corr ν t ≤ K * Real.exp (-(m * t))) ↔ ν (Iio m) = 0 :=
  ⟨fun ⟨_, hK⟩ => gap_of_decay_nat hν (fun n => hK n (Nat.cast_nonneg n)),
    fun h => ⟨ν.real univ, fun _ ht => corr_le_of_gap h ht⟩⟩

/-- **Decay rate = bottom of the support.** The admissible exponential decay rates of the correlation are exactly
the `m` with no spectral mass below `m`; so their supremum, the decay rate, is the bottom of the support. -/
theorem decayRates_eq (hν : ∀ᵐ E ∂ν, 0 ≤ E) :
    {m : ℝ | ∃ K : ℝ, ∀ n : ℕ, corr ν n ≤ K * Real.exp (-(m * n))} = {m : ℝ | ν (Iio m) = 0} := by
  ext m; exact spectral_gap_iff_nat hν m

/-! ### The singularity at the bottom of the spectrum -/

/-- The positive measure `C(t) dt` on `(0, ∞)`. -/
def corrMeasure (ν : Measure ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (corr ν t))

omit [IsFiniteMeasure ν] in
theorem measurable_corr [SFinite ν] : Measurable (corr ν) := by
  have hf : StronglyMeasurable (fun p : ℝ × ℝ => Real.exp (-(p.1 * p.2))) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ => Real.exp (-(p.1 * p.2))).stronglyMeasurable
  exact (hf.integral_prod_right' (ν := ν)).measurable

omit [IsFiniteMeasure ν] in
theorem corrMeasure_nonneg : ∀ᵐ t ∂(corrMeasure ν), 0 ≤ t :=
  (withDensity_absolutelyContinuous _ _).ae_le
    ((ae_restrict_mem measurableSet_Ioi).mono fun _ ht => le_of_lt ht)

theorem lintegral_corrMeasure (x : ℝ) :
    ∫⁻ t, ENNReal.ofReal (Real.exp (-(x * t))) ∂(corrMeasure ν)
      = ∫⁻ t in Ioi 0, ENNReal.ofReal (corr ν t) * ENNReal.ofReal (Real.exp (-(x * t))) := by
  rw [corrMeasure, lintegral_withDensity_eq_lintegral_mul _ (measurable_corr.ennreal_ofReal)
    (by fun_prop)]
  rfl

theorem lapConv_corr_of_gap {m : ℝ} (hgap : ν (Iio m) = 0) {x : ℝ} (hx : -m < x) :
    LapConv (corrMeasure ν) x := by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun t => (Real.exp_pos _).le),
    lintegral_corrMeasure]
  have hb : 0 < m + x := by linarith
  have hint : IntegrableOn (fun t : ℝ => ν.real univ * Real.exp (-(m + x) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hb).const_mul _
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi fun t ht => ?_) hint.lintegral_lt_top
  have ht0 : 0 ≤ t := le_of_lt ht
  calc ENNReal.ofReal (corr ν t) * ENNReal.ofReal (Real.exp (-(x * t)))
      ≤ ENNReal.ofReal (ν.real univ * Real.exp (-(m * t))) * ENNReal.ofReal (Real.exp (-(x * t))) := by
        gcongr; exact corr_le_of_gap hgap ht0
    _ = ENNReal.ofReal (ν.real univ * Real.exp (-(m * t)) * Real.exp (-(x * t))) :=
        (ENNReal.ofReal_mul (mul_nonneg measureReal_nonneg (Real.exp_pos _).le)).symm
    _ = ENNReal.ofReal (ν.real univ * Real.exp (-(m + x) * t)) := by
        congr 1; rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem not_lapConv_corr (hν : ∀ᵐ E ∂ν, 0 ≤ E) {m' : ℝ} (hpos : 0 < ν (Iio m')) {x : ℝ} (hx : x + m' ≤ 0) :
    ¬ LapConv (corrMeasure ν) x := by
  intro hconv
  have hlt := hconv.lintegral_lt_top
  rw [lintegral_corrMeasure] at hlt
  have hc : 0 < ν.real (Iio m') := ENNReal.toReal_pos hpos.ne' (measure_ne_top ν _)
  have hge : ∫⁻ _t in Ioi (0 : ℝ), ENNReal.ofReal (ν.real (Iio m'))
      ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (corr ν t) * ENNReal.ofReal (Real.exp (-(x * t))) := by
    refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 ≤ (t : ℝ) := le_of_lt ht
    have h1 := corr_ge hν m' ht0
    have hcorr0 : 0 ≤ corr ν t :=
      (mul_nonneg measureReal_nonneg (Real.exp_pos _).le).trans h1
    rw [← ENNReal.ofReal_mul hcorr0]
    apply ENNReal.ofReal_le_ofReal
    have he : 1 ≤ Real.exp (-(m' * t)) * Real.exp (-(x * t)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]; nlinarith
    calc ν.real (Iio m') ≤ ν.real (Iio m') * (Real.exp (-(m' * t)) * Real.exp (-(x * t))) :=
          le_mul_of_one_le_right measureReal_nonneg he
      _ = (ν.real (Iio m') * Real.exp (-(m' * t))) * Real.exp (-(x * t)) := by ring
      _ ≤ corr ν t * Real.exp (-(x * t)) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  rw [setLIntegral_const, Real.volume_Ioi, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne'] at hge
  exact absurd (lt_of_le_of_lt hge hlt) (lt_irrefl _)

/-- **The gap is a singularity of the resolvent.** `l₀` the bottom of the support of `ν` (no mass below `l₀`, some
mass below every `m > l₀`). Then the Laplace integral of `C(t) dt`, classically `⟨F, (H + s)⁻¹ F⟩`, converges for real
`s > -l₀`, diverges for `s < -l₀`, and admits no holomorphic extension to any disc about `s = -l₀`. -/
theorem resolvent_singular (hν : ∀ᵐ E ∂ν, 0 ≤ E) {l₀ : ℝ} (hgap : ν (Iio l₀) = 0)
    (hbottom : ∀ m > l₀, 0 < ν (Iio m)) :
    (∀ x > -l₀, LapConv (corrMeasure ν) x) ∧ (∀ x < -l₀, ¬ LapConv (corrMeasure ν) x) ∧
    ¬ ∃ (r : ℝ) (g : ℂ → ℂ), 0 < r ∧ DifferentiableOn ℂ g (Metric.ball ((-l₀ : ℝ) : ℂ) r) ∧
      ∀ s ∈ Metric.ball ((-l₀ : ℝ) : ℂ) r, -l₀ < s.re → g s = lap (corrMeasure ν) s := by
  have hconv : ∀ x > -l₀, LapConv (corrMeasure ν) x := fun x hx => lapConv_corr_of_gap hgap (by linarith)
  have hdiv : ∀ x < -l₀, ¬ LapConv (corrMeasure ν) x := fun x hx =>
    not_lapConv_corr hν (hbottom (-x) (by linarith)) (by linarith)
  exact ⟨hconv, hdiv, laplace_landau corrMeasure_nonneg hconv hdiv⟩

end ProofPhase.Bridge
