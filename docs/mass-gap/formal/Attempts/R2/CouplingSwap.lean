/-
Round 2, attempt B: the reflection-positive coupling (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/r2-coupling/NOTE.md`, sections 1 and 3.
-/

import Mathlib

/-!
# The swap identity for couplings, abstractly

The replica-swap argument of the lead route (Theorem R) needs four things: a coupling of the measure with itself whose
pair marginal is the product (independent replicas), a measure-preserving involution `S` of an extended space
(auxiliary variables, e.g. split labels, plus the two replicas), an `S`-invariant "screening" event `E`, and observables
`f`, `g` that `S` exchanges between the replicas (`f`) or leaves alone (`g`) on `E`. Then

  `|Cov_μ(f, g)| ≤ 2 ‖f‖ ‖g‖ ν(Eᶜ)`        (`swap_cov_bound`).

Nothing about agreement of the two replicas is assumed: only measure preservation of `S` on `E`. This is the abstract
core of the soft swap (NOTE §3), in which `E` is "no chain of active split labels joins the supports".

The second result (`cross_transfer`) is the reason why independence cannot be replaced by a correlated coupling for
free: in **any** coupling `ν` with first marginal `μ`, the cross term `E_ν[f(U') g(U)]` equals `E_μ[f g]` up to
`2 ‖f‖ ‖g‖ ν(f(U') ≠ f(U))`. A coupling that agrees on the support of `f` with high probability carries the full
covariance of `μ` in its cross term (NOTE §1, Lemma A).
-/

open MeasureTheory

noncomputable section

namespace Attempts.R2

/-! ## Helpers -/

section Helpers

variable {X : Type*} [MeasurableSpace X]

/-- A probability space is nonempty. -/
theorem nonempty_of_prob (ν : Measure X) [IsProbabilityMeasure ν] : Nonempty X := by
  by_contra h
  rw [not_nonempty_iff] at h
  have h1 := measure_univ (μ := ν)
  rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
  exact zero_ne_one h1

/-- Transport of an integral along a measure-preserving map (measurable integrand). -/
theorem integral_comp_mp {ν : Measure X} {S : X → X} (hS : MeasurePreserving S ν ν) {H : X → ℝ}
    (hH : Measurable H) : ∫ x, H (S x) ∂ν = ∫ x, H x ∂ν := by
  have h := integral_map (μ := ν) hS.measurable.aemeasurable (f := H) hH.aestronglyMeasurable
  rw [hS.map_eq] at h
  exact h.symm

/-- **An integrand that changes sign under a measure-preserving map, on an invariant event, integrates to zero
    there.** -/
theorem setIntegral_eq_zero_of_antisymm {ν : Measure X} {S : X → X} (hS : MeasurePreserving S ν ν)
    {E : Set X} (hSE : S ⁻¹' E = E) {H : X → ℝ} (hH : Measurable H) (hE : MeasurableSet E)
    (hanti : ∀ x ∈ E, H (S x) = -H x) :
    ∫ x in E, H x ∂ν = 0 := by
  have hind : ∀ x, E.indicator H (S x) = E.indicator (fun y => -H y) x := by
    intro x
    by_cases hx : x ∈ E
    · have hSx : S x ∈ E := by
        have : x ∈ S ⁻¹' E := by rw [hSE]; exact hx
        exact this
      rw [Set.indicator_of_mem hSx, Set.indicator_of_mem hx, hanti x hx]
    · have hSx : S x ∉ E := by
        intro h
        apply hx
        have : x ∈ S ⁻¹' E := h
        rwa [hSE] at this
      rw [Set.indicator_of_notMem hSx, Set.indicator_of_notMem hx]
  have h1 : ∫ x, E.indicator H (S x) ∂ν = ∫ x, E.indicator H x ∂ν :=
    integral_comp_mp hS (hH.indicator hE)
  simp_rw [hind] at h1
  rw [integral_indicator hE, integral_indicator hE, integral_neg] at h1
  linarith

/-- A bounded measurable function is integrable for a finite measure. -/
theorem integrable_of_abs_le {ν : Measure X} [IsFiniteMeasure ν] {H : X → ℝ} (hH : Measurable H) {C : ℝ}
    (hC : ∀ x, |H x| ≤ C) : Integrable H ν :=
  Integrable.of_bound hH.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

/-- `|∫_s H| ≤ C ν(s)` for `|H| ≤ C`. -/
theorem abs_setIntegral_le {ν : Measure X} [IsFiniteMeasure ν] {H : X → ℝ} {C : ℝ} (hC : ∀ x, |H x| ≤ C)
    (s : Set X) : |∫ x in s, H x ∂ν| ≤ C * ν.real s := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := ν) (s := s) (f := H) (measure_lt_top ν s)
    (fun x _ => by rw [Real.norm_eq_abs]; exact hC x)
  rwa [Real.norm_eq_abs] at h

end Helpers

/-! ## The swap identity -/

section Swap

variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]

/-- For independent replicas, `E[(f(U) - f(U')) (g(U) - g(U'))] = 2 Cov(f, g)`. -/
theorem replica_identity (μ : Measure Ω) [IsProbabilityMeasure μ] {f g : Ω → ℝ} (hf : Measurable f)
    (hg : Measurable g) {Mf Mg : ℝ} (hfM : ∀ u, |f u| ≤ Mf) (hgM : ∀ u, |g u| ≤ Mg) :
    ∫ p, (f p.1 - f p.2) * (g p.1 - g p.2) ∂(μ.prod μ) =
      2 * (∫ u, f u * g u ∂μ - (∫ u, f u ∂μ) * ∫ u, g u ∂μ) := by
  have := nonempty_of_prob μ
  have hMf : 0 ≤ Mf := (abs_nonneg _).trans (hfM (Classical.arbitrary _))
  have hMg : 0 ≤ Mg := (abs_nonneg _).trans (hgM (Classical.arbitrary _))
  have bfg : ∀ u, |f u * g u| ≤ Mf * Mg := fun u => by
    rw [abs_mul]; exact mul_le_mul (hfM u) (hgM u) (abs_nonneg _) hMf
  have mfst : ∀ {F : Ω → ℝ}, Measurable F → Measurable (fun p : Ω × Ω => F p.1) := fun h => h.comp measurable_fst
  have msnd : ∀ {F : Ω → ℝ}, Measurable F → Measurable (fun p : Ω × Ω => F p.2) := fun h => h.comp measurable_snd
  have i1 : Integrable (fun p : Ω × Ω => f p.1 * g p.1) (μ.prod μ) :=
    integrable_of_abs_le (mfst (hf.mul hg)) (fun p => bfg p.1)
  have i2 : Integrable (fun p : Ω × Ω => f p.2 * g p.2) (μ.prod μ) :=
    integrable_of_abs_le (msnd (hf.mul hg)) (fun p => bfg p.2)
  have i3 : Integrable (fun p : Ω × Ω => f p.1 * g p.2) (μ.prod μ) :=
    integrable_of_abs_le ((mfst hf).mul (msnd hg)) (fun p => by
      rw [abs_mul]; exact mul_le_mul (hfM _) (hgM _) (abs_nonneg _) hMf)
  have i4 : Integrable (fun p : Ω × Ω => f p.2 * g p.1) (μ.prod μ) :=
    integrable_of_abs_le ((msnd hf).mul (mfst hg)) (fun p => by
      rw [abs_mul]; exact mul_le_mul (hfM _) (hgM _) (abs_nonneg _) hMf)
  have hexp : (fun p : Ω × Ω => (f p.1 - f p.2) * (g p.1 - g p.2)) =
      fun p => ((f p.1 * g p.1 + f p.2 * g p.2) - f p.1 * g p.2) - f p.2 * g p.1 := by
    funext p; ring
  have j12 : Integrable (fun p : Ω × Ω => f p.1 * g p.1 + f p.2 * g p.2) (μ.prod μ) := i1.add i2
  have j123 : Integrable (fun p : Ω × Ω => f p.1 * g p.1 + f p.2 * g p.2 - f p.1 * g p.2) (μ.prod μ) :=
    j12.sub i3
  rw [hexp, integral_sub j123 i4, integral_sub j12 i3, integral_add i1 i2]
  have e1 : ∫ p, f p.1 * g p.1 ∂(μ.prod μ) = ∫ u, f u * g u ∂μ := by
    have := integral_prod_mul (μ := μ) (ν := μ) (fun u => f u * g u) (fun _ => (1 : ℝ))
    simpa using this
  have e2 : ∫ p, f p.2 * g p.2 ∂(μ.prod μ) = ∫ u, f u * g u ∂μ := by
    have := integral_prod_mul (μ := μ) (ν := μ) (fun _ => (1 : ℝ)) (fun u => f u * g u)
    simpa using this
  have e3 : ∫ p, f p.1 * g p.2 ∂(μ.prod μ) = (∫ u, f u ∂μ) * ∫ u, g u ∂μ :=
    integral_prod_mul (μ := μ) (ν := μ) f g
  have e4 : ∫ p, f p.2 * g p.1 ∂(μ.prod μ) = (∫ u, f u ∂μ) * ∫ u, g u ∂μ := by
    have := integral_prod_mul (μ := μ) (ν := μ) g f
    rw [mul_comm (∫ u, g u ∂μ)] at this
    rw [← this]
    congr 1; funext p; ring
  rw [e1, e2, e3, e4]; ring

/-- **The swap bound.** `ν` lives on `T × (Ω × Ω)` (auxiliary labels and two replicas) and its replica marginal is
    `μ ⊗ μ`. `S` is a `ν`-preserving map, `E` an `S`-invariant event, and on `E` the map `S` exchanges the values of
    `f` between the replicas and leaves the values of `g` in place. Then `|Cov_μ(f, g)| ≤ 2 Mf Mg ν(Eᶜ)`. -/
theorem swap_cov_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure (T × (Ω × Ω)))
    [IsProbabilityMeasure ν] (hmarg : ν.map Prod.snd = μ.prod μ)
    {S : T × (Ω × Ω) → T × (Ω × Ω)} (hS : MeasurePreserving S ν ν)
    {E : Set (T × (Ω × Ω))} (hE : MeasurableSet E) (hSE : S ⁻¹' E = E)
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) {Mf Mg : ℝ}
    (hfM : ∀ u, |f u| ≤ Mf) (hgM : ∀ u, |g u| ≤ Mg)
    (hfS : ∀ x ∈ E, f (S x).2.1 = f x.2.2 ∧ f (S x).2.2 = f x.2.1)
    (hgS : ∀ x ∈ E, g (S x).2.1 = g x.2.1 ∧ g (S x).2.2 = g x.2.2) :
    |∫ u, f u * g u ∂μ - (∫ u, f u ∂μ) * ∫ u, g u ∂μ| ≤ 2 * Mf * Mg * ν.real Eᶜ := by
  have := nonempty_of_prob μ
  have hMf : 0 ≤ Mf := (abs_nonneg _).trans (hfM (Classical.arbitrary _))
  have hMg : 0 ≤ Mg := (abs_nonneg _).trans (hgM (Classical.arbitrary _))
  set H : T × (Ω × Ω) → ℝ := fun x => (f x.2.1 - f x.2.2) * (g x.2.1 - g x.2.2) with hHdef
  have mH : Measurable H :=
    ((hf.comp (measurable_fst.comp measurable_snd)).sub (hf.comp (measurable_snd.comp measurable_snd))).mul
      ((hg.comp (measurable_fst.comp measurable_snd)).sub (hg.comp (measurable_snd.comp measurable_snd)))
  have bH : ∀ x, |H x| ≤ 4 * Mf * Mg := by
    intro x
    simp only [hHdef]
    rw [abs_mul]
    have h1 : |f x.2.1 - f x.2.2| ≤ 2 * Mf :=
      (abs_sub _ _).trans (by linarith [hfM x.2.1, hfM x.2.2])
    have h2 : |g x.2.1 - g x.2.2| ≤ 2 * Mg :=
      (abs_sub _ _).trans (by linarith [hgM x.2.1, hgM x.2.2])
    nlinarith [abs_nonneg (f x.2.1 - f x.2.2), abs_nonneg (g x.2.1 - g x.2.2)]
  have iH : Integrable H ν := integrable_of_abs_le mH bH
  -- the total integral is twice the covariance
  have htot : ∫ x, H x ∂ν = 2 * (∫ u, f u * g u ∂μ - (∫ u, f u ∂μ) * ∫ u, g u ∂μ) := by
    have mK : Measurable (fun p : Ω × Ω => (f p.1 - f p.2) * (g p.1 - g p.2)) :=
      ((hf.comp measurable_fst).sub (hf.comp measurable_snd)).mul ((hg.comp measurable_fst).sub (hg.comp measurable_snd))
    have hm := integral_map (μ := ν) measurable_snd.aemeasurable
      (f := fun p : Ω × Ω => (f p.1 - f p.2) * (g p.1 - g p.2)) mK.aestronglyMeasurable
    rw [hmarg] at hm
    rw [replica_identity μ hf hg hfM hgM] at hm
    rw [← hm]
  -- the part on `E` vanishes
  have hanti : ∀ x ∈ E, H (S x) = -H x := by
    intro x hx
    simp only [hHdef]
    rw [(hfS x hx).1, (hfS x hx).2, (hgS x hx).1, (hgS x hx).2]
    ring
  have hzero := setIntegral_eq_zero_of_antisymm hS hSE mH hE hanti
  have hsplit := integral_add_compl hE iH
  rw [hzero, zero_add] at hsplit
  have hbound := abs_setIntegral_le (ν := ν) bH Eᶜ
  rw [hsplit, htot] at hbound
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hbound
  linarith

end Swap

/-! ## Lemma A: agreement transfers the covariance into the cross term -/

section Cross

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Agreement transfers covariance.** For any coupling `ν` of `μ` with itself (only the first marginal is used),
    `|E_ν[f(U') g(U)] - E_μ[f g]| ≤ 2 Mf Mg ν(f(U') ≠ f(U))`. -/
theorem cross_transfer (μ : Measure Ω) (ν : Measure (Ω × Ω)) [IsProbabilityMeasure ν]
    (h1 : ν.map Prod.fst = μ) {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) {Mf Mg : ℝ}
    (hfM : ∀ u, |f u| ≤ Mf) (hgM : ∀ u, |g u| ≤ Mg) :
    |∫ x, f x.2 * g x.1 ∂ν - ∫ u, f u * g u ∂μ| ≤ 2 * Mf * Mg * ν.real {x | f x.2 ≠ f x.1} := by
  have : Nonempty (Ω × Ω) := nonempty_of_prob ν
  have : Nonempty Ω := ⟨(Classical.arbitrary (Ω × Ω)).1⟩
  have hMf : 0 ≤ Mf := (abs_nonneg _).trans (hfM (Classical.arbitrary _))
  have hMg : 0 ≤ Mg := (abs_nonneg _).trans (hgM (Classical.arbitrary _))
  have hμ : ∫ u, f u * g u ∂μ = ∫ x, f x.1 * g x.1 ∂ν := by
    have hm := integral_map (μ := ν) measurable_fst.aemeasurable (f := fun u => f u * g u)
      (hf.mul hg).aestronglyMeasurable
    rw [h1] at hm
    exact hm
  set D : Set (Ω × Ω) := {x | f x.2 ≠ f x.1} with hDdef
  have mD : MeasurableSet D :=
    (measurableSet_eq_fun (hf.comp measurable_snd) (hf.comp measurable_fst)).compl
  set Δ : Ω × Ω → ℝ := fun x => (f x.2 - f x.1) * g x.1 with hΔ
  have mΔ : Measurable Δ := ((hf.comp measurable_snd).sub (hf.comp measurable_fst)).mul (hg.comp measurable_fst)
  have bΔ : ∀ x, |Δ x| ≤ 2 * Mf * Mg := by
    intro x
    simp only [hΔ]
    rw [abs_mul]
    have h1 : |f x.2 - f x.1| ≤ 2 * Mf := (abs_sub _ _).trans (by linarith [hfM x.2, hfM x.1])
    nlinarith [abs_nonneg (f x.2 - f x.1), abs_nonneg (g x.1), hgM x.1]
  have iΔ : Integrable Δ ν := integrable_of_abs_le mΔ bΔ
  have hdiff : ∫ x, f x.2 * g x.1 ∂ν - ∫ x, f x.1 * g x.1 ∂ν = ∫ x, Δ x ∂ν := by
    have hb : ∀ x : Ω × Ω, |f x.2 * g x.1| ≤ Mf * Mg := fun x => by
      rw [abs_mul]; exact mul_le_mul (hfM _) (hgM _) (abs_nonneg _) hMf
    have hb' : ∀ x : Ω × Ω, |f x.1 * g x.1| ≤ Mf * Mg := fun x => by
      rw [abs_mul]; exact mul_le_mul (hfM _) (hgM _) (abs_nonneg _) hMf
    have ia : Integrable (fun x : Ω × Ω => f x.2 * g x.1) ν :=
      integrable_of_abs_le ((hf.comp measurable_snd).mul (hg.comp measurable_fst)) hb
    have ib : Integrable (fun x : Ω × Ω => f x.1 * g x.1) ν :=
      integrable_of_abs_le ((hf.comp measurable_fst).mul (hg.comp measurable_fst)) hb'
    rw [← integral_sub ia ib]
    congr 1; funext x; simp only [hΔ]; ring
  have hoff : ∫ x in Dᶜ, Δ x ∂ν = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    have hx' : f x.2 = f x.1 := by simpa [hDdef] using hx
    simp only [hΔ, hx', sub_self, zero_mul]
  have hsplit := integral_add_compl mD iΔ
  rw [hoff, add_zero] at hsplit
  rw [hμ, hdiff, ← hsplit]
  exact abs_setIntegral_le bΔ D

end Cross

end Attempts.R2
