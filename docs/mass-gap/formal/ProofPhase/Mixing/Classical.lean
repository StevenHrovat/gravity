/-
P vs NP dictionary, items 1 of "Missing": the coupling of the heat bath from classical Dobrushin coefficients
(2026-11-23). Released under Apache 2.0.

Paper: `docs/pnp/ITEMS.md`.
-/

import ProofPhase.Mixing.Glauber

/-!
# Fast mixing from the classical Dobrushin condition (finite systems)

`Glauber.lean` assumes, as part of the structure `SiteDynamics`, measurable coupling kernels `Q` whose disagreement
probability is bounded by an influence matrix (the *coupling form* of Dobrushin's condition). For finite site set and
finite single-site space this file **builds** those couplings from the classical objects, so that the mixing theorems
have only the classical condition as hypothesis.

**Setting.** `ι` finite (sites), `S` finite with the discrete measurable structure, `μ` a probability measure on
configurations `ι → S` with positive weights `μ {σ} ≠ 0` (the Gibbs measure of a system with positive weights).

* `heatBath μ`: the heat-bath (Gibbs sampler) update at `x`, resampling the spin at `x` from its conditional law given
  the other spins (`cl`), as a Markov kernel; it changes only the spin at `x` and leaves `μ` invariant (reversibility).
* `dob μ x z`: **Dobrushin's coefficient**, the largest total-variation distance between the conditional laws at `x`
  of two configurations that differ only at `z`.
* `maxCoup a b`: the **maximal coupling** of two probability vectors on `S`, with explicit formula; its two marginals
  are `a` and `b` and it puts mass at most `tv a b` off the diagonal.
* `heatBath μ hpos`: a `SiteDynamics μ` whose coupling kernel at `x` couples the conditional laws at `x` of the two
  configurations by their maximal coupling. The coupling inequality of the structure,
  `Q x p (disagree x) ≤ Σ_z A x z [p.1 z ≠ p.2 z]` with `A = dob μ`, follows from the triangle inequality for the
  total variation distance along the hybrid configurations (`condTV_le_sum`).

**Main results.** `tv_sweep_dobrushin`, `tv_rs_dobrushin`, `mixing_sweep_dobrushin`, `mixing_rs_dobrushin`,
`integral_sweep_dobrushin`, `integral_rs_dobrushin`: the statements of `Glauber.lean` with hypothesis only
`Σ_z dob μ x z ≤ α` for all `x` (rows, systematic scan) or `Σ_x dob μ x z ≤ α` for all `z` (columns, random scan).

No axioms beyond the standard ones; nothing is assumed.
-/

open MeasureTheory ProbabilityTheory Finset ProofPhase.OneBox

open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Mixing

/-! ### Finite measures from weights -/

section Weighted

variable {T : Type*} [Fintype T] [MeasurableSpace T] [DiscreteMeasurableSpace T]

/-- The measure on a finite discrete space with weight `f t` at the point `t` (negative weights count as `0`). -/
def wm (f : T → ℝ) : Measure T := ∑ t, ENNReal.ofReal (f t) • Measure.dirac t

theorem wm_apply (f : T → ℝ) (s : Set T) :
    wm f s = ∑ t, s.indicator (fun t => ENNReal.ofReal (f t)) t := by
  have hs : MeasurableSet s := MeasurableSet.of_discrete
  simp only [wm, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, Measure.dirac_apply' _ hs,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : t ∈ s <;> simp [Set.indicator, h]

theorem wm_univ (f : T → ℝ) (hf : ∀ t, 0 ≤ f t) : wm f Set.univ = ENNReal.ofReal (∑ t, f t) := by
  rw [wm_apply, ENNReal.ofReal_sum_of_nonneg fun t _ => hf t]
  simp

theorem wm_real (f : T → ℝ) (hf : ∀ t, 0 ≤ f t) (s : Set T) : (wm f).real s = ∑ t, s.indicator f t := by
  rw [measureReal_def, wm_apply, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : t ∈ s <;> simp [Set.indicator, h, ENNReal.toReal_ofReal (hf t)]
  · intro t _
    by_cases h : t ∈ s <;> simp [Set.indicator, h]

theorem wm_singleton (f : T → ℝ) (t : T) : wm f {t} = ENNReal.ofReal (f t) := by
  rw [wm_apply, Finset.sum_eq_single t]
  · exact Set.indicator_of_mem (Set.mem_singleton t) _
  · intro u _ hu
    exact Set.indicator_of_notMem (by simpa using hu) _
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem isProbabilityMeasure_wm (f : T → ℝ) (hf : ∀ t, 0 ≤ f t) (h1 : ∑ t, f t = 1) :
    IsProbabilityMeasure (wm f) :=
  ⟨by rw [wm_univ f hf, h1]; simp⟩

variable {U : Type*} [Fintype U] [MeasurableSpace U] [DiscreteMeasurableSpace U]

theorem map_fst_wm (G : T × U → ℝ) (hG : ∀ q, 0 ≤ G q) :
    (wm G).map Prod.fst = wm (fun a => ∑ b, G (a, b)) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs, wm_apply, wm_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a ∈ s
  · simp only [Set.indicator, Set.mem_preimage, h, ↓reduceIte]
    rw [ENNReal.ofReal_sum_of_nonneg fun b _ => hG (a, b)]
  · simp [Set.indicator, h]

theorem map_snd_wm (G : T × U → ℝ) (hG : ∀ q, 0 ≤ G q) :
    (wm G).map Prod.snd = wm (fun b => ∑ a, G (a, b)) := by
  ext s hs
  rw [Measure.map_apply measurable_snd hs, wm_apply, wm_apply, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : b ∈ s
  · simp only [Set.indicator, Set.mem_preimage, h, ↓reduceIte]
    rw [ENNReal.ofReal_sum_of_nonneg fun a _ => hG (a, b)]
  · simp [Set.indicator, h]

end Weighted

/-! ### Total variation and the maximal coupling -/

section Coupling

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Total variation distance of two vectors on a finite set, `½ Σ |a - b|`. -/
def tv (a b : S → ℝ) : ℝ := (∑ s, |a s - b s|) / 2

theorem tv_nonneg (a b : S → ℝ) : 0 ≤ tv a b :=
  div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

theorem tv_self (a : S → ℝ) : tv a a = 0 := by simp [tv]

theorem tv_triangle (a b c : S → ℝ) : tv a c ≤ tv a b + tv b c := by
  have h : ∑ s, |a s - c s| ≤ ∑ s, |a s - b s| + ∑ s, |b s - c s| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun s _ => abs_sub_le (a s) (b s) (c s)
  unfold tv
  linarith

/-- The pointwise minimum of two vectors. -/
def minv (a b : S → ℝ) : S → ℝ := fun s => min (a s) (b s)

/-- The mass missing from the overlap, `1 - Σ min`. -/
def dlt (a b : S → ℝ) : ℝ := 1 - ∑ u, minv a b u

/-- **The maximal coupling** of two probability vectors `a`, `b`: the overlap `min (a s) (b s)` on the diagonal, and the
two residuals `a - min`, `b - min` coupled independently (normalised) off it. -/
def maxCoup (a b : S → ℝ) (s t : S) : ℝ :=
  (if s = t then minv a b s else 0) + (a s - minv a b s) * (b t - minv a b t) / dlt a b

variable {a b : S → ℝ}

theorem minv_nonneg (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s) (s : S) : 0 ≤ minv a b s :=
  le_min (ha s) (hb s)

theorem minv_le_left {s : S} : minv a b s ≤ a s := min_le_left _ _

theorem minv_le_right {s : S} : minv a b s ≤ b s := min_le_right _ _

theorem sum_res_left (ha1 : ∑ s, a s = 1) : ∑ s, (a s - minv a b s) = dlt a b := by
  rw [Finset.sum_sub_distrib, ha1]; rfl

theorem sum_res_right (hb1 : ∑ s, b s = 1) : ∑ s, (b s - minv a b s) = dlt a b := by
  rw [Finset.sum_sub_distrib, hb1]; rfl

theorem dlt_nonneg (ha1 : ∑ s, a s = 1) : 0 ≤ dlt a b := by
  rw [← sum_res_left ha1]
  exact Finset.sum_nonneg fun s _ => sub_nonneg.2 minv_le_left

theorem res_le_dlt (ha1 : ∑ s, a s = 1) (s : S) : a s - minv a b s ≤ dlt a b := by
  rw [← sum_res_left ha1]
  exact Finset.single_le_sum (f := fun s => a s - minv a b s) (fun s _ => sub_nonneg.2 minv_le_left)
    (Finset.mem_univ s)

theorem res_mul_div (ha1 : ∑ s, a s = 1) (s : S) :
    (a s - minv a b s) * dlt a b / dlt a b = a s - minv a b s := by
  by_cases hδ : dlt a b = 0
  · have h1 := res_le_dlt (b := b) ha1 s
    have h2 : 0 ≤ a s - minv a b s := sub_nonneg.2 minv_le_left
    have : a s - minv a b s = 0 := le_antisymm (hδ ▸ h1) h2
    rw [hδ, this]; simp
  · exact mul_div_cancel_right₀ _ hδ

theorem dlt_comm : dlt b a = dlt a b := by
  unfold dlt minv; simp only [min_comm]

theorem minv_comm (t : S) : minv b a t = minv a b t := by
  unfold minv; exact min_comm _ _

theorem maxCoup_nonneg (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s) (ha1 : ∑ s, a s = 1) (s t : S) :
    0 ≤ maxCoup a b s t := by
  unfold maxCoup
  have h1 : 0 ≤ (if s = t then minv a b s else 0) := by
    split_ifs
    · exact minv_nonneg ha hb s
    · exact le_rfl
  have h2 : 0 ≤ (a s - minv a b s) * (b t - minv a b t) / dlt a b :=
    div_nonneg (mul_nonneg (sub_nonneg.2 minv_le_left) (sub_nonneg.2 minv_le_right)) (dlt_nonneg ha1)
  linarith

/-- The first marginal of the maximal coupling is `a`. -/
theorem maxCoup_sum_right (ha1 : ∑ s, a s = 1) (hb1 : ∑ s, b s = 1) (s : S) :
    ∑ t, maxCoup a b s t = a s := by
  unfold maxCoup
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ↓reduceIte]
  rw [← Finset.sum_div,
    ← Finset.mul_sum, sum_res_right hb1, res_mul_div ha1 s]
  ring

/-- The second marginal of the maximal coupling is `b`. -/
theorem maxCoup_sum_left (ha1 : ∑ s, a s = 1) (hb1 : ∑ s, b s = 1) (t : S) :
    ∑ s, maxCoup a b s t = b t := by
  unfold maxCoup
  have h2 : ∑ s, (a s - minv a b s) * (b t - minv a b t) / dlt a b = b t - minv a b t := by
    have := res_mul_div (a := b) (b := a) hb1 t
    rw [dlt_comm, minv_comm] at this
    rw [← Finset.sum_div, ← Finset.sum_mul, sum_res_left ha1, mul_comm]
    exact this
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte]
  rw [h2]
  ring

/-- The maximal coupling puts at most `dlt a b` mass off the diagonal. -/
theorem maxCoup_offdiag_le (ha1 : ∑ s, a s = 1) (hb1 : ∑ s, b s = 1) :
    ∑ s, ∑ t, (if s = t then 0 else maxCoup a b s t) ≤ dlt a b := by
  have hterm : ∀ s t, (if s = t then 0 else maxCoup a b s t) ≤
      (a s - minv a b s) * (b t - minv a b t) / dlt a b := fun s t => by
    by_cases h : s = t
    · simp only [h, ↓reduceIte]
      exact div_nonneg (mul_nonneg (sub_nonneg.2 minv_le_left) (sub_nonneg.2 minv_le_right)) (dlt_nonneg ha1)
    · simp only [h, ↓reduceIte]
      unfold maxCoup
      simp only [h, ↓reduceIte, zero_add, le_refl]
  calc ∑ s, ∑ t, (if s = t then 0 else maxCoup a b s t)
      ≤ ∑ s, ∑ t, (a s - minv a b s) * (b t - minv a b t) / dlt a b :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => hterm s t
    _ = (∑ s, (a s - minv a b s)) * (∑ t, (b t - minv a b t)) / dlt a b := by
        rw [Finset.sum_mul_sum, Finset.sum_div]
        exact Finset.sum_congr rfl fun s _ => by rw [Finset.sum_div]
    _ = dlt a b * dlt a b / dlt a b := by rw [sum_res_left ha1, sum_res_right hb1]
    _ ≤ dlt a b := by
        by_cases hδ : dlt a b = 0
        · simp [hδ]
        · exact (mul_div_cancel_right₀ _ hδ).le

theorem min_eq_half (x y : ℝ) : min x y = (x + y - |x - y|) / 2 := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.2 h)]; ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]; ring

theorem dlt_eq_tv (ha1 : ∑ s, a s = 1) (hb1 : ∑ s, b s = 1) : dlt a b = tv a b := by
  unfold dlt tv minv
  simp_rw [min_eq_half]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, ha1, hb1]
  ring

end Coupling

/-! ### The heat bath on a finite system -/

section HeatBath

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [DiscreteMeasurableSpace S] (μ : Measure (ι → S))

/-- The weight `μ {σ}` of a configuration, as a real number. -/
abbrev pw (σ : ι → S) : ℝ := μ.real {σ}

/-- Two configurations agree off the site `x`. -/
def Agree (x : ι) (σ ξ : ι → S) : Prop := ∀ z, z ≠ x → σ z = ξ z

instance (x : ι) (σ ξ : ι → S) : Decidable (Agree x σ ξ) := by unfold Agree; infer_instance

/-- The normalisation of the conditional law at `x` given the spins off `x`. -/
def Zs (x : ι) (σ : ι → S) : ℝ := ∑ s, pw μ (Function.update σ x s)

/-- The conditional law of the spin at `x` given the spins off `x` (read from `σ`). -/
def cl (x : ι) (σ : ι → S) (s : S) : ℝ := pw μ (Function.update σ x s) / Zs μ x σ

/-- The heat-bath transition matrix at `x`: from `σ`, resample the spin at `x` from its conditional law. -/
def K (x : ι) (σ ξ : ι → S) : ℝ := if Agree x σ ξ then pw μ ξ / Zs μ x σ else 0

variable {μ}

theorem Agree.symm {x : ι} {σ ξ : ι → S} (h : Agree x σ ξ) : Agree x ξ σ := fun z hz => (h z hz).symm

theorem agree_update (x : ι) (σ : ι → S) (s : S) : Agree x σ (Function.update σ x s) := fun z hz => by
  rw [Function.update_of_ne hz]

theorem update_eq_of_agree {x : ι} {σ ξ : ι → S} (h : Agree x σ ξ) : Function.update σ x (ξ x) = ξ := by
  funext y
  by_cases hy : y = x
  · subst hy; simp
  · rw [Function.update_of_ne hy, h y hy]

theorem update_congr_of_agree {x : ι} {σ ξ : ι → S} (h : Agree x σ ξ) (s : S) :
    Function.update σ x s = Function.update ξ x s := by
  funext y
  by_cases hy : y = x
  · subst hy; simp
  · rw [Function.update_of_ne hy, Function.update_of_ne hy, h y hy]

theorem Zs_congr {x : ι} {σ ξ : ι → S} (h : Agree x σ ξ) : Zs μ x σ = Zs μ x ξ := by
  unfold Zs
  exact Finset.sum_congr rfl fun s _ => by rw [update_congr_of_agree h]

/-- **Summing over the configurations that agree with `σ` off `x`** is summing over the value at `x`. -/
theorem sum_agree (x : ι) (σ : ι → S) (g : (ι → S) → ℝ) :
    ∑ ξ, (if Agree x σ ξ then g ξ else 0) = ∑ s, g (Function.update σ x s) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun s _ => Function.update σ x s) ?_ ?_ ?_ ?_
  · intro s _
    simp [agree_update]
  · intro s _ t _ hst
    have := congrFun hst x
    simpa using this
  · intro ξ hξ
    have h : Agree x σ ξ := by simpa using hξ
    exact ⟨ξ x, Finset.mem_univ _, update_eq_of_agree h⟩
  · intro s _
    rfl

variable (hpos : ∀ σ : ι → S, 0 < pw μ σ)
include hpos

theorem Zs_pos (x : ι) (σ : ι → S) : 0 < Zs μ x σ :=
  Finset.sum_pos (fun _ _ => hpos _) ⟨σ x, Finset.mem_univ _⟩

theorem cl_nonneg (x : ι) (σ : ι → S) (s : S) : 0 ≤ cl μ x σ s :=
  div_nonneg (hpos _).le (Zs_pos hpos x σ).le

theorem sum_cl (x : ι) (σ : ι → S) : ∑ s, cl μ x σ s = 1 := by
  unfold cl
  rw [← Finset.sum_div]
  exact div_self (Zs_pos hpos x σ).ne'

theorem K_nonneg (x : ι) (σ ξ : ι → S) : 0 ≤ K μ x σ ξ := by
  unfold K
  split_ifs
  · exact div_nonneg (hpos _).le (Zs_pos hpos x σ).le
  · exact le_rfl

theorem sum_K (x : ι) (σ : ι → S) : ∑ ξ, K μ x σ ξ = 1 := by
  have h : ∑ ξ, K μ x σ ξ = ∑ s, pw μ (Function.update σ x s) / Zs μ x σ :=
    sum_agree x σ (fun ξ => pw μ ξ / Zs μ x σ)
  rw [h, ← Finset.sum_div]
  exact div_self (Zs_pos hpos x σ).ne'

/-- **Reversibility (detailed balance) of the heat bath.** -/
theorem rev (x : ι) (σ ξ : ι → S) : pw μ σ * K μ x σ ξ = pw μ ξ * K μ x ξ σ := by
  by_cases h : Agree x σ ξ
  · have h' := h.symm
    simp only [K, h, h', ↓reduceIte]
    rw [Zs_congr h]
    ring
  · have h' : ¬ Agree x ξ σ := fun hh => h hh.symm
    simp [K, h, h']

theorem sum_pK (x : ι) (ξ : ι → S) : ∑ σ, pw μ σ * K μ x σ ξ = pw μ ξ := by
  simp_rw [rev hpos x _ ξ]
  rw [← Finset.mul_sum, sum_K hpos, mul_one]

omit hpos

variable (μ) in
/-- The heat-bath update at `x` as a Markov kernel (a finite discrete space: every function is measurable). -/
def hbKernel (x : ι) : Kernel (ι → S) (ι → S) := Kernel.ofFunOfCountable fun σ => wm (K μ x σ)

theorem hbKernel_apply (x : ι) (σ : ι → S) : hbKernel μ x σ = wm (K μ x σ) := rfl

theorem isProbabilityMeasure_hbKernel (hpos : ∀ σ : ι → S, 0 < pw μ σ) (x : ι) (σ : ι → S) :
    IsProbabilityMeasure (hbKernel μ x σ) := by
  rw [hbKernel_apply]
  exact isProbabilityMeasure_wm _ (K_nonneg hpos x σ) (sum_K hpos x σ)

/-- **The heat bath leaves `μ` invariant** (the DLR equation at `x`). -/
theorem bind_hbKernel [IsFiniteMeasure μ] (hpos : ∀ σ : ι → S, 0 < pw μ σ) (x : ι) :
    μ.bind (hbKernel μ x) = μ := by
  refine Measure.ext_of_singleton fun ξ => ?_
  rw [Measure.bind_apply (MeasurableSet.of_discrete) (hbKernel μ x).aemeasurable, lintegral_fintype]
  have hμ : ∀ σ : ι → S, μ {σ} = ENNReal.ofReal (pw μ σ) := fun σ => by
    rw [pw, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have h1 : ∀ σ : ι → S, (hbKernel μ x σ) {ξ} * μ {σ} = ENNReal.ofReal (K μ x σ ξ * pw μ σ) := fun σ => by
    rw [hbKernel_apply, wm_singleton, hμ, ENNReal.ofReal_mul (K_nonneg hpos x σ ξ)]
  simp_rw [h1]
  rw [← ENNReal.ofReal_sum_of_nonneg fun σ _ => mul_nonneg (K_nonneg hpos x σ ξ) (hpos σ).le, hμ]
  congr 1
  simp_rw [mul_comm (K μ x _ ξ)]
  exact sum_pK hpos x ξ

/-! ### Dobrushin's coefficients -/

variable (μ) in
/-- Total variation distance between the conditional laws at `x` given `σ` and given `σ'`. -/
def condTV (x : ι) (σ σ' : ι → S) : ℝ := tv (cl μ x σ) (cl μ x σ')

variable (μ) in
/-- **Dobrushin's coefficient**: the influence of the site `z` on the site `x`, the largest total variation distance
between the conditional laws at `x` of two configurations that differ only at `z`. -/
def dob (x z : ι) : ℝ :=
  ⨆ q : (ι → S) × (ι → S), if (∀ y, y ≠ z → q.1 y = q.2 y) then condTV μ x q.1 q.2 else 0

theorem dob_nonneg (x z : ι) : 0 ≤ dob μ x z :=
  Real.iSup_nonneg fun q => by
    split_ifs
    · exact tv_nonneg _ _
    · exact le_rfl

/-- A pair differing only at `z` is bounded by the coefficient. -/
theorem condTV_le_dob (x z : ι) (σ σ' : ι → S) (h : ∀ y, y ≠ z → σ y = σ' y) : condTV μ x σ σ' ≤ dob μ x z := by
  have hb : BddAbove (Set.range fun q : (ι → S) × (ι → S) =>
      if (∀ y, y ≠ z → q.1 y = q.2 y) then condTV μ x q.1 q.2 else 0) := Finite.bddAbove_range _
  have h1 : (if (∀ y, y ≠ z → σ y = σ' y) then condTV μ x σ σ' else 0) ≤ dob μ x z := le_ciSup hb (σ, σ')
  simp only [eq_true h, ↓reduceIte] at h1
  exact h1

/-- **The triangle inequality along hybrid configurations**: the total variation distance between the conditional laws
of two configurations is at most the sum of the Dobrushin coefficients over the sites where they differ. -/
theorem condTV_le_sum (x : ι) (σ σ' : ι → S) :
    condTV μ x σ σ' ≤ ∑ z, (if σ z ≠ σ' z then dob μ x z else 0) := by
  have key : ∀ D : Finset ι, condTV μ x σ (fun y => if y ∈ D then σ' y else σ y) ≤
      ∑ z ∈ D, (if σ z ≠ σ' z then dob μ x z else 0) := by
    intro D
    induction D using Finset.induction_on with
    | empty => simp [condTV, tv_self]
    | insert a D ha ih =>
      rw [Finset.sum_insert ha]
      have h1 : condTV μ x (fun y => if y ∈ D then σ' y else σ y)
          (fun y => if y ∈ insert a D then σ' y else σ y) ≤ (if σ a ≠ σ' a then dob μ x a else 0) := by
        by_cases hσ : σ a = σ' a
        · have : (fun y => if y ∈ D then σ' y else σ y) = (fun y => if y ∈ insert a D then σ' y else σ y) := by
            funext y
            by_cases hy : y = a
            · subst hy; simp [ha, hσ]
            · simp [hy]
          rw [this]
          simp [condTV, tv_self, hσ]
        · simp only [ne_eq, hσ, not_false_eq_true, ↓reduceIte]
          refine condTV_le_dob x a _ _ fun y hy => ?_
          simp [hy]
      have h2 := tv_triangle (cl μ x σ) (cl μ x fun y => if y ∈ D then σ' y else σ y)
        (cl μ x fun y => if y ∈ insert a D then σ' y else σ y)
      unfold condTV at ih h1 ⊢
      linarith
  have := key Finset.univ
  simpa using this

/-! ### The coupling kernel -/

variable (μ) in
/-- The density of the coupled heat-bath update at `x` from the pair `p`: the two conditional laws coupled maximally. -/
def G (x : ι) (p q : (ι → S) × (ι → S)) : ℝ :=
  if Agree x p.1 q.1 ∧ Agree x p.2 q.2 then maxCoup (cl μ x p.1) (cl μ x p.2) (q.1 x) (q.2 x) else 0

section
variable (hpos : ∀ σ : ι → S, 0 < pw μ σ)
include hpos

theorem G_nonneg (x : ι) (p q : (ι → S) × (ι → S)) : 0 ≤ G μ x p q := by
  unfold G
  split_ifs
  · exact maxCoup_nonneg (cl_nonneg hpos x p.1) (cl_nonneg hpos x p.2) (sum_cl hpos x p.1) _ _
  · exact le_rfl

/-- The first marginal of the coupling density is the heat-bath matrix of the first configuration. -/
theorem G_sum_snd (x : ι) (p : (ι → S) × (ι → S)) (ξ : ι → S) :
    ∑ ξ', G μ x p (ξ, ξ') = K μ x p.1 ξ := by
  by_cases h : Agree x p.1 ξ
  · have e : ∑ ξ', G μ x p (ξ, ξ') = ∑ ξ', (if Agree x p.2 ξ' then
        maxCoup (cl μ x p.1) (cl μ x p.2) (ξ x) (ξ' x) else 0) :=
      Finset.sum_congr rfl fun ξ' _ => by simp [G, h]
    have e2 : ∑ ξ', (if Agree x p.2 ξ' then maxCoup (cl μ x p.1) (cl μ x p.2) (ξ x) (ξ' x) else 0) =
        ∑ t, maxCoup (cl μ x p.1) (cl μ x p.2) (ξ x) t := by
      rw [sum_agree x p.2 (fun ξ' => maxCoup (cl μ x p.1) (cl μ x p.2) (ξ x) (ξ' x))]
      simp
    rw [e, e2, maxCoup_sum_right (sum_cl hpos x p.1) (sum_cl hpos x p.2)]
    simp only [K, h, ↓reduceIte, cl, update_eq_of_agree h]
  · have : ∀ ξ', G μ x p (ξ, ξ') = 0 := fun ξ' => by simp [G, h]
    simp [this, K, h]

/-- The second marginal of the coupling density is the heat-bath matrix of the second configuration. -/
theorem G_sum_fst (x : ι) (p : (ι → S) × (ι → S)) (ξ' : ι → S) :
    ∑ ξ, G μ x p (ξ, ξ') = K μ x p.2 ξ' := by
  by_cases h : Agree x p.2 ξ'
  · have e : ∑ ξ, G μ x p (ξ, ξ') = ∑ ξ, (if Agree x p.1 ξ then
        maxCoup (cl μ x p.1) (cl μ x p.2) (ξ x) (ξ' x) else 0) :=
      Finset.sum_congr rfl fun ξ _ => by simp [G, h]
    have e2 : ∑ ξ, (if Agree x p.1 ξ then maxCoup (cl μ x p.1) (cl μ x p.2) (ξ x) (ξ' x) else 0) =
        ∑ s, maxCoup (cl μ x p.1) (cl μ x p.2) s (ξ' x) := by
      rw [sum_agree x p.1 (fun ξ => maxCoup (cl μ x p.1) (cl μ x p.2) (ξ x) (ξ' x))]
      simp
    rw [e, e2, maxCoup_sum_left (sum_cl hpos x p.1) (sum_cl hpos x p.2)]
    simp only [K, h, ↓reduceIte, cl, update_eq_of_agree h]
  · have : ∀ ξ, G μ x p (ξ, ξ') = 0 := fun ξ => by simp [G, h]
    simp [this, K, h]

theorem sum_G (x : ι) (p : (ι → S) × (ι → S)) : ∑ q, G μ x p q = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [G_sum_snd hpos]
  exact sum_K hpos x p.1

/-- **The off-diagonal mass of the coupling** at the updated site is at most the total variation distance. -/
theorem G_disagree (x : ι) (p : (ι → S) × (ι → S)) :
    (wm (G μ x p)).real (ProofPhase.OneBox.disagree x) ≤ condTV μ x p.1 p.2 := by
  rw [wm_real _ (G_nonneg hpos x p), Fintype.sum_prod_type]
  set f : S → S → ℝ := fun s t => if s = t then 0 else maxCoup (cl μ x p.1) (cl μ x p.2) s t with hf
  have h1 : ∀ ξ ξ' : ι → S, (ProofPhase.OneBox.disagree x).indicator (G μ x p) (ξ, ξ') =
      if Agree x p.1 ξ then (if Agree x p.2 ξ' then f (ξ x) (ξ' x) else 0) else 0 := fun ξ ξ' => by
    by_cases hd : ξ x = ξ' x
    · have : (ξ, ξ') ∉ ProofPhase.OneBox.disagree x := by simp [ProofPhase.OneBox.disagree, hd]
      rw [Set.indicator_of_notMem this]
      simp [hf, hd]
    · have : (ξ, ξ') ∈ ProofPhase.OneBox.disagree x := hd
      rw [Set.indicator_of_mem this]
      by_cases ha : Agree x p.1 ξ <;> by_cases hb : Agree x p.2 ξ' <;> simp [G, hf, ha, hb, hd]
  simp_rw [h1]
  have e : ∑ ξ : ι → S, ∑ ξ' : ι → S, (if Agree x p.1 ξ then (if Agree x p.2 ξ' then f (ξ x) (ξ' x) else 0) else 0) =
      ∑ s, ∑ t, f s t := by
    calc _ = ∑ ξ : ι → S, (if Agree x p.1 ξ then ∑ t, f (ξ x) t else 0) := by
          refine Finset.sum_congr rfl fun ξ _ => ?_
          by_cases hξ : Agree x p.1 ξ
          · simp only [hξ, ↓reduceIte]
            rw [sum_agree x p.2 (fun ξ' => f (ξ x) (ξ' x))]
            simp
          · simp [hξ]
      _ = ∑ s, ∑ t, f s t := by
          rw [sum_agree x p.1 (fun ξ => ∑ t, f (ξ x) t)]
          simp
  rw [e]
  have := maxCoup_offdiag_le (sum_cl hpos x p.1) (sum_cl hpos x p.2)
  rw [dlt_eq_tv (sum_cl hpos x p.1) (sum_cl hpos x p.2)] at this
  exact this

end

variable (μ) in
/-- The coupled heat-bath update at `x` as a kernel on pairs of configurations. -/
def cplKernel (x : ι) : Kernel ((ι → S) × (ι → S)) ((ι → S) × (ι → S)) :=
  Kernel.ofFunOfCountable fun p => wm (G μ x p)

theorem cplKernel_apply (x : ι) (p : (ι → S) × (ι → S)) : cplKernel μ x p = wm (G μ x p) := rfl

/-- **The finite heat bath as a `SiteDynamics`.** Everything that `Glauber.lean` assumes is built here: the update
kernels (changing only the spin at `x`, leaving `μ` invariant), the maximal couplings of the conditional laws, and the
influence matrix `A = dob μ`, Dobrushin's coefficients. Hypothesis: positive weights. -/
def heatBath [IsFiniteMeasure μ] (hpos : ∀ σ : ι → S, 0 < pw μ σ) : SiteDynamics μ where
  P := hbKernel μ
  P_markov x := ⟨isProbabilityMeasure_hbKernel hpos x⟩
  P_local x σ z hz := by
    rw [hbKernel_apply, ae_iff, wm_apply]
    refine Finset.sum_eq_zero fun ξ _ => ?_
    by_cases hξ : ξ ∈ {a : ι → S | ¬ a z = σ z}
    · rw [Set.indicator_of_mem hξ]
      have hna : ¬ Agree x σ ξ := fun h => hξ (h z hz).symm
      have : K μ x σ ξ = 0 := by simp [K, hna]
      simp [this]
    · rw [Set.indicator_of_notMem hξ]
  P_inv x := bind_hbKernel hpos x
  Q := cplKernel μ
  Q_markov x := ⟨fun p => by
    rw [cplKernel_apply]
    exact isProbabilityMeasure_wm _ (G_nonneg hpos x p) (sum_G hpos x p)⟩
  Q_fst x p := by
    rw [cplKernel_apply, map_fst_wm _ (G_nonneg hpos x p), hbKernel_apply]
    congr 1
    funext ξ
    exact G_sum_snd hpos x p ξ
  Q_snd x p := by
    rw [cplKernel_apply, map_snd_wm _ (G_nonneg hpos x p), hbKernel_apply]
    congr 1
    funext ξ
    exact G_sum_fst hpos x p ξ
  A := dob μ
  A_nonneg := dob_nonneg
  influence x p := by
    rw [cplKernel_apply]
    calc (wm (G μ x p)).real (ProofPhase.OneBox.disagree x) ≤ condTV μ x p.1 p.2 := G_disagree hpos x p
      _ ≤ ∑ z, (if p.1 z ≠ p.2 z then dob μ x z else 0) := condTV_le_sum x p.1 p.2
      _ = ∑ z, (ProofPhase.OneBox.disagree z).indicator (fun _ => dob μ x z) p := by
          refine Finset.sum_congr rfl fun z _ => ?_
          by_cases h : p.1 z = p.2 z <;> simp [Set.indicator, ProofPhase.OneBox.disagree, h]

/-! ### Fast mixing with only the classical condition -/

section Mixing

variable [IsProbabilityMeasure μ] (hpos : ∀ σ : ι → S, 0 < pw μ σ)

/-- **Systematic scan, classical Dobrushin condition (rows).** Finite system, positive weights, heat-bath sweeps over
a list containing every site; if `Σ_z dob μ x z ≤ α ≤ 1` for every `x`, then after `t` sweeps from any start `ν`,
`|ν_t(s) - μ(s)| ≤ n α^t`. No coupling is assumed. -/
theorem tv_sweep_dobrushin {order : List ι} (hcover : ∀ x, x ∈ order) {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1)
    (hrow : ∀ x, ∑ z, dob μ x z ≤ α) (ν : Measure (ι → S)) [IsProbabilityMeasure ν] (t : ℕ)
    {s : Set (ι → S)} (hs : MeasurableSet s) :
    |(((heatBath hpos).sweep order)^[t] ν).real s - μ.real s| ≤ Fintype.card ι * α ^ t :=
  (heatBath hpos).tv_sweep_le hcover hα0 hα hrow ν t hs

/-- **Random scan, classical Dobrushin condition (columns).** If `Σ_x dob μ x z ≤ α` for every `z`, then after `k`
single-site heat-bath steps from any start, `|ν_k(s) - μ(s)| ≤ n (1 - (1 - α)/n)^k`. -/
theorem tv_rs_dobrushin [Nonempty ι] {α : ℝ} (hα0 : 0 ≤ α) (hcol : ∀ z, ∑ x, dob μ x z ≤ α)
    (ν : Measure (ι → S)) [IsProbabilityMeasure ν] (k : ℕ) {s : Set (ι → S)} (hs : MeasurableSet s) :
    |((heatBath hpos).rsStep^[k] ν).real s - μ.real s| ≤
      Fintype.card ι * (1 - (1 - α) / Fintype.card ι) ^ k :=
  (heatBath hpos).tv_rs_le hα0 hcol ν k hs

/-- **Mixing time, systematic scan, classical condition.** Row sums at most `α ∈ (0, 1)`: after
`t ≥ log(n/ε)/log(1/α)` sweeps the heat bath is within `ε` of `μ` in total variation, from every start. -/
theorem mixing_sweep_dobrushin [Nonempty ι] {order : List ι} (hcover : ∀ x, x ∈ order) {α : ℝ} (hα0 : 0 < α)
    (hα : α < 1) (hrow : ∀ x, ∑ z, dob μ x z ≤ α) {ε : ℝ} (hε : 0 < ε) {t : ℕ}
    (ht : Real.log (Fintype.card ι / ε) ≤ t * Real.log α⁻¹) (ν : Measure (ι → S)) [IsProbabilityMeasure ν]
    {s : Set (ι → S)} (hs : MeasurableSet s) :
    |(((heatBath hpos).sweep order)^[t] ν).real s - μ.real s| ≤ ε :=
  (heatBath hpos).mixing_sweep hcover hα0 hα hrow hε ht ν hs

/-- **Mixing time, random scan, classical condition.** Column sums at most `α < 1`: after
`k ≥ n log(n/ε)/(1 - α)` single-site heat-bath steps the sampler is within `ε` of `μ`, from every start. -/
theorem mixing_rs_dobrushin [Nonempty ι] {α : ℝ} (hα0 : 0 ≤ α) (hcol : ∀ z, ∑ x, dob μ x z ≤ α) {ε : ℝ}
    (hε : 0 < ε) {k : ℕ} (hk : Fintype.card ι * Real.log (Fintype.card ι / ε) ≤ (1 - α) * k)
    (ν : Measure (ι → S)) [IsProbabilityMeasure ν] {s : Set (ι → S)} (hs : MeasurableSet s) :
    |((heatBath hpos).rsStep^[k] ν).real s - μ.real s| ≤ ε :=
  (heatBath hpos).mixing_rs hα0 hcol hε hk ν hs

/-- Test functions, systematic scan. -/
theorem integral_sweep_dobrushin {order : List ι} (hcover : ∀ x, x ∈ order) {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1)
    (hrow : ∀ x, ∑ z, dob μ x z ≤ α) (ν : Measure (ι → S)) [IsProbabilityMeasure ν] (t : ℕ)
    {F : (ι → S) → ℝ} (hF : Measurable F) {M : ℝ} (hFM : ∀ σ, |F σ| ≤ M) :
    |∫ σ, F σ ∂(((heatBath hpos).sweep order)^[t] ν) - ∫ σ, F σ ∂μ| ≤ 2 * M * (Fintype.card ι * α ^ t) :=
  (heatBath hpos).integral_sweep_le hcover hα0 hα hrow ν t hF hFM

/-- Test functions, random scan. -/
theorem integral_rs_dobrushin [Nonempty ι] {α : ℝ} (hα0 : 0 ≤ α) (hcol : ∀ z, ∑ x, dob μ x z ≤ α)
    (ν : Measure (ι → S)) [IsProbabilityMeasure ν] (k : ℕ) {F : (ι → S) → ℝ} (hF : Measurable F) {M : ℝ}
    (hFM : ∀ σ, |F σ| ≤ M) :
    |∫ σ, F σ ∂((heatBath hpos).rsStep^[k] ν) - ∫ σ, F σ ∂μ| ≤
      2 * M * (Fintype.card ι * (1 - (1 - α) / Fintype.card ι) ^ k) :=
  (heatBath hpos).integral_rs_le hα0 hcol ν k hF hFM

end Mixing

end HeatBath

end ProofPhase.Mixing
