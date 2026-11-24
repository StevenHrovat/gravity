/-
Proof phase, ScaleHyp kit, module 1: the maximal coupling of two densities, and total variation from a density ratio
(2026-11-23). Released under Apache 2.0.

Pack: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/PACK-SCALEHYP.md`, items (a) and (c).
Note: `docs/mass-gap/weak-coupling/proof-phase/scalehyp/NOTE.md`.
-/

import Mathlib

/-!
# The maximal coupling of two densities

Two probability measures `ρ Λ`, `ρ' Λ` with densities against a common measure `Λ` (`UV-TV.md` 38.5 (3), 39.4).

* `overlap Λ ρ ρ' = ∫ ρ ∧ ρ' dΛ`, and `excess ρ ρ' = ρ - ρ ∧ ρ'`.
* `maxCoupling Λ ρ ρ'`: the push-forward of `(ρ ∧ ρ') Λ` to the diagonal, plus
  `(ρ - ρ ∧ ρ') Λ ⊗ (ρ' - ρ ∧ ρ') Λ / (1 - ∫ ρ ∧ ρ')`. The formula needs no case split: when the overlap is `1`, the
  product part is the zero measure and `⊤ • 0 = 0`.
* `maxCoupling_map_fst`, `maxCoupling_map_snd`: the marginals are `ρ Λ` and `ρ' Λ`.
* `maxCoupling_apply_le`: every measurable set that misses the diagonal has mass at most `1 - ∫ ρ ∧ ρ'`, the total
  variation distance. This is the bound the block coupling hypothesis `hunion` of `ScaleHyp.ofBlockBounds` needs.
* `le_overlap_of_ratio`, `maxCoupling_real_le_of_ratio` (item (c)): if `e^{-δ} ρ ≤ ρ'` almost everywhere, with
  `δ ≥ 0`, then the overlap is at least `e^{-δ}` and the coupling misses the diagonal with probability at most
  `1 - e^{-δ} ≤ δ`. Only the lower half of the two-sided ratio bound is used, and the constant is `1 - e^{-δ}` rather
  than the pack's `e^{δ} - 1`.
-/

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.ScaleHypKit

variable {α : Type*} [MeasurableSpace α]

/-- The overlap `∫ ρ ∧ ρ' dΛ`. -/
def overlap (Λ : Measure α) (ρ ρ' : α → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ a, min (ρ a) (ρ' a) ∂Λ

/-- The excess `ρ - ρ ∧ ρ'`. -/
def excess (ρ ρ' : α → ℝ≥0∞) (a : α) : ℝ≥0∞ := ρ a - min (ρ a) (ρ' a)

/-- **The maximal coupling** of `ρ Λ` and `ρ' Λ`. -/
def maxCoupling (Λ : Measure α) (ρ ρ' : α → ℝ≥0∞) : Measure (α × α) :=
  (Λ.withDensity fun a => min (ρ a) (ρ' a)).map (fun a => (a, a)) +
    (1 - overlap Λ ρ ρ')⁻¹ • ((Λ.withDensity (excess ρ ρ')).prod (Λ.withDensity (excess ρ' ρ)))

variable {Λ : Measure α} {ρ ρ' : α → ℝ≥0∞}

theorem measurable_diag : Measurable fun a : α => (a, a) := measurable_id.prodMk measurable_id

theorem measurable_excess (hρ : Measurable ρ) (hρ' : Measurable ρ') : Measurable (excess ρ ρ') :=
  hρ.sub (hρ.min hρ')

theorem overlap_comm : overlap Λ ρ' ρ = overlap Λ ρ ρ' := by simp only [overlap, min_comm]

theorem overlap_le (h1 : ∫⁻ a, ρ a ∂Λ = 1) : overlap Λ ρ ρ' ≤ 1 :=
  h1 ▸ lintegral_mono fun _ => min_le_left _ _

theorem one_sub_overlap_ne_top : 1 - overlap Λ ρ ρ' ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self

theorem lintegral_excess (hρ : Measurable ρ) (hρ' : Measurable ρ') (h1 : ∫⁻ a, ρ a ∂Λ = 1) :
    ∫⁻ a, excess ρ ρ' a ∂Λ = 1 - overlap Λ ρ ρ' := by
  have hfin : ∫⁻ a, min (ρ a) (ρ' a) ∂Λ ≠ ∞ := ((overlap_le h1).trans_lt ENNReal.one_lt_top).ne
  have h := lintegral_sub (hρ.min hρ') hfin (ae_of_all _ fun a => min_le_left (ρ a) (ρ' a))
  rw [h1] at h
  exact h

theorem lintegral_excess' (hρ : Measurable ρ) (hρ' : Measurable ρ') (h1' : ∫⁻ a, ρ' a ∂Λ = 1) :
    ∫⁻ a, excess ρ' ρ a ∂Λ = 1 - overlap Λ ρ ρ' := by
  rw [lintegral_excess hρ' hρ h1', overlap_comm]

theorem withDensity_excess_univ (hρ : Measurable ρ) (hρ' : Measurable ρ') (h1 : ∫⁻ a, ρ a ∂Λ = 1) :
    Λ.withDensity (excess ρ ρ') univ = 1 - overlap Λ ρ ρ' := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_excess hρ hρ' h1]

theorem withDensity_excess_univ' (hρ : Measurable ρ) (hρ' : Measurable ρ') (h1' : ∫⁻ a, ρ' a ∂Λ = 1) :
    Λ.withDensity (excess ρ' ρ) univ = 1 - overlap Λ ρ ρ' := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_excess' hρ hρ' h1']

/-- `t⁻¹ • t • W = W` when `W` has total mass `t < ∞` (also for `t = 0`, where `W = 0`). -/
theorem inv_smul_smul_of_univ {β : Type*} [MeasurableSpace β] (W : Measure β) {t : ℝ≥0∞} (ht : W univ = t)
    (htop : t ≠ ∞) : t⁻¹ • t • W = W := by
  rcases eq_or_ne t 0 with h0 | h0
  · subst h0
    rw [Measure.measure_univ_eq_zero.mp ht]
    simp
  · rw [smul_smul, ENNReal.inv_mul_cancel h0 htop, one_smul]

theorem min_add_excess (ρ ρ' : α → ℝ≥0∞) : (fun a => min (ρ a) (ρ' a)) + excess ρ ρ' = ρ := by
  funext a
  simp only [Pi.add_apply, excess]
  exact add_tsub_cancel_of_le (min_le_left _ _)

theorem min_add_excess' (ρ ρ' : α → ℝ≥0∞) : (fun a => min (ρ a) (ρ' a)) + excess ρ' ρ = ρ' := by
  funext a
  simp only [Pi.add_apply, excess, min_comm (ρ' a)]
  exact add_tsub_cancel_of_le (min_le_right _ _)

section Marginals

variable [SFinite Λ]

/-- **The first marginal** of the maximal coupling is `ρ Λ`. -/
theorem maxCoupling_map_fst (hρ : Measurable ρ) (hρ' : Measurable ρ') (h1 : ∫⁻ a, ρ a ∂Λ = 1)
    (h1' : ∫⁻ a, ρ' a ∂Λ = 1) : (maxCoupling Λ ρ ρ').map Prod.fst = Λ.withDensity ρ := by
  rw [maxCoupling, Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_map measurable_fst measurable_diag,
    Measure.map_fst_prod, withDensity_excess_univ' hρ hρ' h1',
    inv_smul_smul_of_univ _ (withDensity_excess_univ hρ hρ' h1) one_sub_overlap_ne_top]
  have hid : (Prod.fst ∘ fun a : α => (a, a)) = id := rfl
  rw [hid, Measure.map_id, ← withDensity_add_left (hρ.min hρ'), min_add_excess]
  exact measurable_fst.aemeasurable

/-- **The second marginal** of the maximal coupling is `ρ' Λ`. -/
theorem maxCoupling_map_snd (hρ : Measurable ρ) (hρ' : Measurable ρ') (h1 : ∫⁻ a, ρ a ∂Λ = 1)
    (h1' : ∫⁻ a, ρ' a ∂Λ = 1) : (maxCoupling Λ ρ ρ').map Prod.snd = Λ.withDensity ρ' := by
  rw [maxCoupling, Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_map measurable_snd measurable_diag,
    Measure.map_snd_prod, withDensity_excess_univ hρ hρ' h1,
    inv_smul_smul_of_univ _ (withDensity_excess_univ' hρ hρ' h1') one_sub_overlap_ne_top]
  have hid : (Prod.snd ∘ fun a : α => (a, a)) = id := rfl
  rw [hid, Measure.map_id, ← withDensity_add_left (hρ.min hρ'), min_add_excess']
  exact measurable_snd.aemeasurable

theorem isProbabilityMeasure_maxCoupling (hρ : Measurable ρ) (hρ' : Measurable ρ') (h1 : ∫⁻ a, ρ a ∂Λ = 1)
    (h1' : ∫⁻ a, ρ' a ∂Λ = 1) : IsProbabilityMeasure (maxCoupling Λ ρ ρ') := by
  constructor
  have h := congrArg (fun m : Measure α => m univ) (maxCoupling_map_fst hρ hρ' h1 h1')
  simp only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, h1] at h
  exact h

/-- **The coupling misses the diagonal with probability at most `1 - ∫ ρ ∧ ρ'`**: every measurable set `D` that
contains no diagonal point has mass at most the total variation distance. -/
theorem maxCoupling_apply_le (hρ : Measurable ρ) (hρ' : Measurable ρ') (h1 : ∫⁻ a, ρ a ∂Λ = 1)
    (h1' : ∫⁻ a, ρ' a ∂Λ = 1) {D : Set (α × α)} (hD : MeasurableSet D) (hdiag : ∀ a, (a, a) ∉ D) :
    maxCoupling Λ ρ ρ' D ≤ 1 - overlap Λ ρ ρ' := by
  have hpre : (fun a : α => (a, a)) ⁻¹' D = ∅ := eq_empty_of_forall_notMem fun a ha => hdiag a ha
  rw [maxCoupling, Measure.add_apply, Measure.map_apply measurable_diag hD, hpre, measure_empty, zero_add,
    Measure.smul_apply, smul_eq_mul]
  set t := 1 - overlap Λ ρ ρ' with ht
  set P := (Λ.withDensity (excess ρ ρ')).prod (Λ.withDensity (excess ρ' ρ)) with hP
  have hprod : P D ≤ t * t := by
    calc P D ≤ P univ := measure_mono (subset_univ _)
      _ = t * t := by
        rw [hP, ← univ_prod_univ, Measure.prod_prod, withDensity_excess_univ hρ hρ' h1,
          withDensity_excess_univ' hρ hρ' h1']
  rcases eq_or_ne t 0 with h0 | h0
  · have hPD : P D = 0 := by rw [h0, mul_zero] at hprod; exact le_antisymm hprod zero_le
    rw [hPD, mul_zero]
    exact zero_le
  · calc t⁻¹ * P D ≤ t⁻¹ * (t * t) := by gcongr
      _ = t := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 one_sub_overlap_ne_top, one_mul]

end Marginals

/-! ### Total variation from a density ratio (item (c)) -/

/-- **The overlap from a lower density ratio**: if `c ρ ≤ ρ'` almost everywhere with `c ≤ 1`, then `c ≤ ∫ ρ ∧ ρ'`. -/
theorem le_overlap_of_ratio (hρ : Measurable ρ) (h1 : ∫⁻ a, ρ a ∂Λ = 1) {c : ℝ≥0∞} (hc : c ≤ 1)
    (hr : ∀ᵐ a ∂Λ, c * ρ a ≤ ρ' a) : c ≤ overlap Λ ρ ρ' := by
  calc c = ∫⁻ a, c * ρ a ∂Λ := by rw [lintegral_const_mul _ hρ, h1, mul_one]
    _ ≤ overlap Λ ρ ρ' :=
      lintegral_mono_ae (hr.mono fun a ha => le_min (mul_le_of_le_one_left zero_le hc) ha)

/-- **Total variation from a density ratio**: if `e^{-δ} ρ ≤ ρ'` almost everywhere (`δ ≥ 0`), the maximal coupling
gives every measurable set that misses the diagonal real mass at most `δ` (in fact at most `1 - e^{-δ}`). -/
theorem maxCoupling_real_le_of_ratio [SFinite Λ] (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (h1 : ∫⁻ a, ρ a ∂Λ = 1) (h1' : ∫⁻ a, ρ' a ∂Λ = 1) {D : Set (α × α)} (hD : MeasurableSet D)
    (hdiag : ∀ a, (a, a) ∉ D) {δ : ℝ} (hδ : 0 ≤ δ)
    (hr : ∀ᵐ a ∂Λ, ENNReal.ofReal (Real.exp (-δ)) * ρ a ≤ ρ' a) :
    (maxCoupling Λ ρ ρ').real D ≤ δ := by
  have hexp : Real.exp (-δ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hc : ENNReal.ofReal (Real.exp (-δ)) ≤ 1 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hexp
  have h := (maxCoupling_apply_le hρ hρ' h1 h1' hD hdiag).trans
    (tsub_le_tsub_left (le_overlap_of_ratio hρ h1 hc hr) 1)
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le] at h
  calc (maxCoupling Λ ρ ρ').real D ≤ 1 - Real.exp (-δ) := by
        rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal (by linarith) h
    _ ≤ δ := by linarith [Real.add_one_le_exp (-δ)]

end ProofPhase.ScaleHypKit
