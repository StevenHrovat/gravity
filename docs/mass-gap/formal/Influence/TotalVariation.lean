import Mathlib

/-!
# Total variation and the chord bound (LGT-NOTE.md, section 1)

Reference text: `docs/mass-gap/dobrushin/LGT-NOTE.md`, section 1 ("A factor of 2 with `lgt`'s existing lemma").

* `Influence.tv` : total variation distance of two measures, defined directly as the supremum of
  `μ.real A - ν.real A` over measurable sets `A` (Mathlib v4.34.0 has no total-variation *distance*
  of two measures, only the variation of a signed measure, which is less convenient here).
* `Influence.chord_bound` : `∫ (g - 1)⁺ dν ≤ (M - 1)(1 - m)/(M - m)` when `∫ g dν = 1`, `m ≤ g ≤ M`.
* `Influence.chord_le_sqrt` : `(M - 1)(1 - m)/(M - m) ≤ (√R - 1)/(√R + 1)` when `0 < m ≤ 1 ≤ M ≤ R m`.
* `Influence.sqrt_ratio_eq_tanh` : `(√R - 1)/(√R + 1) = tanh (log R / 4)`.
* `Influence.tv_le_of_density_bounds`, `Influence.tv_le_tanh_of_density_bounds`,
  `Influence.tv_le_tanh_of_rnDeriv_bounds` : the main lemma of section 1, `TV(μ, ν) ≤ tanh (log R / 4)`
  when the density `dμ/dν` lies in `[m, M]` with `M ≤ R m`.
-/

open MeasureTheory Real
open scoped ENNReal

namespace Influence

variable {α : Type*} [MeasurableSpace α]

/-- Total variation distance of two measures: the supremum over measurable sets `A` of
`μ(A) - ν(A)` (as real numbers). For probability measures this is the usual
`sup_A |μ(A) - ν(A)|`, since `μ(Aᶜ) - ν(Aᶜ) = ν(A) - μ(A)`. -/
noncomputable def tv (μ ν : Measure α) : ℝ :=
  ⨆ (A : Set α) (_ : MeasurableSet A), (μ.real A - ν.real A)

/-- To bound the total variation by `c ≥ 0`, it suffices to bound `μ(A) - ν(A) ≤ c` for every
measurable set `A`. -/
theorem tv_le_of_forall {μ ν : Measure α} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ A, MeasurableSet A → μ.real A - ν.real A ≤ c) : tv μ ν ≤ c :=
  Real.iSup_le (fun A => Real.iSup_le (fun hA => h A hA) hc) hc

/-- Sanity check that `tv` is the honest supremum: every `μ(A) - ν(A)` with `A` measurable is
below it (for `μ` finite). -/
theorem le_tv (μ ν : Measure α) [IsFiniteMeasure μ] {A : Set α} (hA : MeasurableSet A) :
    μ.real A - ν.real A ≤ tv μ ν := by
  have hb : ∀ B : Set α, (⨆ (_ : MeasurableSet B), (μ.real B - ν.real B)) ≤ μ.real Set.univ := by
    intro B
    refine Real.iSup_le (fun _ => ?_) measureReal_nonneg
    have := measureReal_mono (μ := μ) (Set.subset_univ B)
    have := measureReal_nonneg (μ := ν) (s := B)
    linarith
  refine le_trans ?_ (le_ciSup ⟨_, Set.forall_mem_range.2 hb⟩ A)
  rw [ciSup_pos hA]

/-- The total variation of a finite measure against any measure is nonnegative (take `A = ∅`). -/
theorem tv_nonneg (μ ν : Measure α) [IsFiniteMeasure μ] : 0 ≤ tv μ ν := by
  simpa using le_tv μ ν MeasurableSet.empty

/-- Pointwise chord inequality: on `[m, M]` with `m ≤ 1 ≤ M`, `m < M`, the convex function
`x ↦ (x - 1)⁺` lies below its chord, `(x - 1)⁺ ≤ (M - 1)(x - m)/(M - m)`. -/
theorem chord_pointwise {m M x : ℝ} (hm1 : m ≤ 1) (h1M : 1 ≤ M) (hmM : m < M)
    (hx1 : m ≤ x) (hx2 : x ≤ M) :
    max (x - 1) 0 ≤ (M - 1) * (x - m) / (M - m) := by
  rw [le_div_iff₀ (by linarith)]
  rcases le_total x 1 with h | h
  · rw [max_eq_right (by linarith)]; nlinarith
  · rw [max_eq_left (by linarith)]; nlinarith

/-- If `∫ g dν = 1` for a probability measure `ν` and `m ≤ g ≤ M` almost everywhere, then
`m ≤ 1 ≤ M`. -/
theorem bounds_of_integral_eq_one (ν : Measure α) [IsProbabilityMeasure ν] {g : α → ℝ} {m M : ℝ}
    (hg : ∫ x, g x ∂ν = 1) (hm : ∀ᵐ x ∂ν, m ≤ g x) (hM : ∀ᵐ x ∂ν, g x ≤ M) :
    m ≤ 1 ∧ 1 ≤ M := by
  have hint : Integrable g ν := Integrable.of_integral_ne_zero (by rw [hg]; norm_num)
  constructor
  · have := integral_mono_ae (integrable_const m) hint hm
    simpa [hg] using this
  · have := integral_mono_ae hint (integrable_const M) hM
    simpa [hg] using this

/-- **Chord bound** (LGT-NOTE.md §1, first step of the proof of the Lemma).
If `ν` is a probability measure and `g` is a real function with `∫ g dν = 1` and
`m ≤ g ≤ M` `ν`-almost everywhere, then `∫ (g - 1)⁺ dν ≤ (M - 1)(1 - m)/(M - m)`.

The degenerate case `M = m` is included: then `g = 1` a.e. and both sides are `0` (Lean's
`x / 0 = 0`). Integrability of `g` follows from `∫ g dν = 1`; the hypothesis `g ≥ 0` of the note
is not needed. -/
theorem chord_bound (ν : Measure α) [IsProbabilityMeasure ν] {g : α → ℝ} {m M : ℝ}
    (hg : ∫ x, g x ∂ν = 1) (hm : ∀ᵐ x ∂ν, m ≤ g x) (hM : ∀ᵐ x ∂ν, g x ≤ M) :
    ∫ x, max (g x - 1) 0 ∂ν ≤ (M - 1) * (1 - m) / (M - m) := by
  have hint : Integrable g ν := Integrable.of_integral_ne_zero (by rw [hg]; norm_num)
  obtain ⟨hm1, h1M⟩ := bounds_of_integral_eq_one ν hg hm hM
  rcases eq_or_lt_of_le (hm1.trans h1M) with heq | hlt
  · have h0 : ∫ x, max (g x - 1) 0 ∂ν = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hM] with x hx
      simp only [Pi.zero_apply]
      rw [max_eq_right (by linarith)]
    rw [h0, ← heq, sub_self, div_zero]
  · calc ∫ x, max (g x - 1) 0 ∂ν ≤ ∫ x, (M - 1) * (g x - m) / (M - m) ∂ν := by
          refine integral_mono_ae (Integrable.pos_part (f := fun x => g x - 1)
            (hint.sub (integrable_const 1))) ?_ ?_
          · exact ((hint.sub (integrable_const m)).const_mul (M - 1)).div_const (M - m)
          · filter_upwards [hm, hM] with x h1 h2 using chord_pointwise hm1 h1M hlt h1 h2
      _ = (M - 1) * (1 - m) / (M - m) := by
          rw [integral_div, integral_const_mul, integral_sub hint (integrable_const _)]
          simp [hg]

/-- If `0 < m ≤ 1 ≤ M ≤ R m` then `R ≥ 1`. -/
theorem one_le_of_bounds {m M R : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (h1M : 1 ≤ M)
    (hMR : M ≤ R * m) : 1 ≤ R := by
  by_contra h
  push Not at h
  nlinarith

/-- **Algebraic step** (LGT-NOTE.md §1, second step of the proof of the Lemma).
If `0 < m ≤ 1 ≤ M ≤ R m`, then `(M - 1)(1 - m)/(M - m) ≤ (√R - 1)/(√R + 1)`.
(The left side is increasing in `M`, and at `M = R m` the gap is `(√R m - 1)² ≥ 0` up to a positive
factor.) -/
theorem chord_le_sqrt {m M R : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (h1M : 1 ≤ M)
    (hMR : M ≤ R * m) :
    (M - 1) * (1 - m) / (M - m) ≤ (√R - 1) / (√R + 1) := by
  have hR : 1 ≤ R := one_le_of_bounds hm0 hm1 h1M hMR
  set s := √R with hs
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 hR
  have hss : s ^ 2 = R := Real.sq_sqrt (by linarith)
  have hrhs : 0 ≤ (s - 1) / (s + 1) := div_nonneg (by linarith) (by linarith)
  rcases eq_or_lt_of_le (hm1.trans h1M) with heq | hlt
  · rw [heq, sub_self, div_zero]; exact hrhs
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have key : (s ^ 2 * m - 1) * ((s - 1) * (M - m) - (M - 1) * (1 - m) * (s + 1)) =
        (s ^ 2 * m - M) * ((1 - m) * (s - 1)) + (M - 1) * ((s + 1) * (s * m - 1) ^ 2) := by ring
    have hP1 : 0 ≤ (s ^ 2 * m - M) * ((1 - m) * (s - 1)) :=
      mul_nonneg (by rw [hss]; linarith) (mul_nonneg (by linarith) (by linarith))
    have hP2 : 0 ≤ (M - 1) * ((s + 1) * (s * m - 1) ^ 2) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) (sq_nonneg _))
    rcases eq_or_lt_of_le (show 0 ≤ s ^ 2 * m - 1 by rw [hss]; linarith) with h0 | hpos
    · have hM1 : M = 1 := le_antisymm (by rw [hss] at h0; linarith) h1M
      subst hM1
      nlinarith
    · have := (mul_nonneg_iff_of_pos_left hpos).1 (key ▸ add_nonneg hP1 hP2)
      linarith

/-- `tanh x = (e^{2x} - 1)/(e^{2x} + 1)`. -/
theorem tanh_eq_exp (x : ℝ) : tanh x = (exp (2 * x) - 1) / (exp (2 * x) + 1) := by
  rw [tanh_eq_sinh_div_cosh, sinh_eq, cosh_eq]
  have h1 : exp (2 * x) = exp x * exp x := by rw [← exp_add]; ring_nf
  rw [h1, exp_neg]
  have := exp_pos x
  field_simp

/-- `(√R - 1)/(√R + 1) = tanh (log R / 4)` for `R > 0` (LGT-NOTE.md §1, statement of the Lemma). -/
theorem sqrt_ratio_eq_tanh {R : ℝ} (hR : 0 < R) : (√R - 1) / (√R + 1) = tanh (log R / 4) := by
  rw [tanh_eq_exp]
  have : exp (2 * (log R / 4)) = √R := by
    rw [sqrt_eq_rpow, rpow_def_of_pos hR]; ring_nf
  rw [this]

/-- **Main lemma, density form** (LGT-NOTE.md §1, the Lemma).
Let `μ, ν` be probability measures with `μ = ν.withDensity g` for a measurable real `g`, and
suppose `m ≤ g ≤ M` `ν`-a.e. with `0 < m` and `M ≤ R m`. Then
`TV(μ, ν) ≤ (√R - 1)/(√R + 1)`.

Proof: `μ(A) - ν(A) = ∫_A (g - 1) dν ≤ ∫ (g - 1)⁺ dν`, then `chord_bound` and `chord_le_sqrt`.
(`R ≥ 1` follows from the hypotheses, see `one_le_of_bounds`.) -/
theorem tv_le_of_density_bounds (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {g : α → ℝ} (hg : Measurable g)
    (hμ : μ = ν.withDensity (fun x => ENNReal.ofReal (g x)))
    {m M R : ℝ} (hm0 : 0 < m) (hm : ∀ᵐ x ∂ν, m ≤ g x) (hM : ∀ᵐ x ∂ν, g x ≤ M)
    (hMR : M ≤ R * m) :
    tv μ ν ≤ (√R - 1) / (√R + 1) := by
  have hg0 : ∀ᵐ x ∂ν, 0 ≤ g x := by filter_upwards [hm] with x hx using hm0.le.trans hx
  have hint : Integrable g ν := by
    refine Integrable.of_bound hg.aestronglyMeasurable M ?_
    filter_upwards [hm, hM] with x h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]; exact h2
  have hset : ∀ A, MeasurableSet A → μ.real A = ∫ x in A, g x ∂ν := by
    intro A hA
    rw [measureReal_def, hμ, withDensity_apply _ hA,
      ← ofReal_integral_eq_lintegral_ofReal hint.integrableOn (ae_restrict_of_ae hg0),
      ENNReal.toReal_ofReal (setIntegral_nonneg_of_ae_restrict (ae_restrict_of_ae hg0))]
  have hone : ∫ x, g x ∂ν = 1 := by
    have := hset Set.univ MeasurableSet.univ
    rw [Measure.restrict_univ, probReal_univ] at this
    exact this.symm
  obtain ⟨hm1, h1M⟩ := bounds_of_integral_eq_one ν hone hm hM
  have hpos_int : Integrable (fun x => max (g x - 1) 0) ν :=
    Integrable.pos_part (f := fun x => g x - 1) (hint.sub (integrable_const 1))
  have htv : tv μ ν ≤ ∫ x, max (g x - 1) 0 ∂ν := by
    refine tv_le_of_forall (integral_nonneg fun x => le_max_right _ _) fun A hA => ?_
    have hνA : ν.real A = ∫ x in A, (1 : ℝ) ∂ν := by simp
    rw [hset A hA, hνA, ← integral_sub hint.integrableOn (integrable_const 1).integrableOn]
    calc ∫ x in A, (g x - 1) ∂ν ≤ ∫ x in A, max (g x - 1) 0 ∂ν :=
          setIntegral_mono (hint.sub (integrable_const 1)).integrableOn hpos_int.integrableOn
            (fun x => le_max_left _ _)
      _ ≤ ∫ x, max (g x - 1) 0 ∂ν :=
          setIntegral_le_integral hpos_int (Filter.Eventually.of_forall fun x => le_max_right _ _)
  exact htv.trans ((chord_bound ν hone hm hM).trans (chord_le_sqrt hm0 hm1 h1M hMR))

/-- **Main lemma, `tanh` form** (LGT-NOTE.md §1, the Lemma).
Same hypotheses as `tv_le_of_density_bounds`; conclusion `TV(μ, ν) ≤ tanh (log R / 4)`. -/
theorem tv_le_tanh_of_density_bounds (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {g : α → ℝ} (hg : Measurable g)
    (hμ : μ = ν.withDensity (fun x => ENNReal.ofReal (g x)))
    {m M R : ℝ} (hm0 : 0 < m) (hm : ∀ᵐ x ∂ν, m ≤ g x) (hM : ∀ᵐ x ∂ν, g x ≤ M)
    (hMR : M ≤ R * m) :
    tv μ ν ≤ tanh (log R / 4) := by
  have hg0 : ∀ᵐ x ∂ν, 0 ≤ g x := by filter_upwards [hm] with x hx using hm0.le.trans hx
  have hint : Integrable g ν := by
    refine Integrable.of_bound hg.aestronglyMeasurable M ?_
    filter_upwards [hm, hM] with x h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]; exact h2
  have hone : ∫ x, g x ∂ν = 1 := by
    have h : μ Set.univ = ν.withDensity (fun x => ENNReal.ofReal (g x)) Set.univ := by rw [← hμ]
    rw [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint hg0] at h
    have h' := congrArg ENNReal.toReal h
    rwa [ENNReal.toReal_one, ENNReal.toReal_ofReal (integral_nonneg_of_ae hg0), eq_comm] at h'
  obtain ⟨hm1, h1M⟩ := bounds_of_integral_eq_one ν hone hm hM
  rw [← sqrt_ratio_eq_tanh (by linarith [one_le_of_bounds hm0 hm1 h1M hMR])]
  exact tv_le_of_density_bounds μ ν hg hμ hm0 hm hM hMR

/-- **Main lemma, Radon–Nikodym form** (LGT-NOTE.md §1, the Lemma as stated there).
If `μ ≪ ν` are probability measures and the density `g = dμ/dν` (`μ.rnDeriv ν`, as a real
function) satisfies `m ≤ g ≤ M` `ν`-a.e. with `0 < m`, `M ≤ R m`, then
`TV(μ, ν) ≤ tanh (log R / 4) = (√R - 1)/(√R + 1)`. -/
theorem tv_le_tanh_of_rnDeriv_bounds (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hac : μ ≪ ν) {m M R : ℝ} (hm0 : 0 < m)
    (hm : ∀ᵐ x ∂ν, m ≤ (μ.rnDeriv ν x).toReal) (hM : ∀ᵐ x ∂ν, (μ.rnDeriv ν x).toReal ≤ M)
    (hMR : M ≤ R * m) :
    tv μ ν ≤ tanh (log R / 4) := by
  refine tv_le_tanh_of_density_bounds μ ν (Measure.measurable_rnDeriv μ ν).ennreal_toReal ?_
    hm0 hm hM hMR
  calc μ = ν.withDensity (μ.rnDeriv ν) := (Measure.withDensity_rnDeriv_eq μ ν hac).symm
    _ = _ := by
      refine withDensity_congr_ae ?_
      filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
      exact (ENNReal.ofReal_toReal hx.ne).symm

end Influence
