/-
The one-scale reduction, abstract layer (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/PROOF-NOTE.md`, sections 1.4 to 1.7 and 2 (the elementary lemmas).
-/

import Mathlib

/-!
# Blocks, splicing, oscillation bounds, block specifications

The abstract setting of Theorem A (`PROOF-NOTE.md` section 4): a finite index set `ι` (the links), a single-coordinate
space `S` (the gauge group), configurations `ι → S`, a probability measure `μ` on configurations, and a finite family of
blocks `B_j ⊆ ι` with block specifications `q_j^σ`. Nothing here is gauge specific.

* `splice B σ ξ`: the configuration equal to `ξ` on `B` and to `σ` off `B` (the note's `(σ_{Ω∖B}, ξ)`).
* `OscBound h v`: `v x` bounds the single-coordinate oscillation `δ_x(h)` (note §1.5). We work with bounds rather than with
  suprema, so no `BddAbove` side conditions appear; `δ_x(h)` itself is the least such bound.
* `OscBound.abs_sub_le`: Lemma 2.3 (telescoping): `|h σ - h σ'| ≤ ∑_{x ∈ T} v x` if `σ = σ'` off `T`.
* `BM h`: `h` is bounded and measurable.
* `blockAvg B q h σ = ∫ h (splice B σ ξ) d(q σ)(ξ)`: the block average `P_B h` (note §1.4).
* `BlockSpec μ J`: a block family `(B_j)_{j ∈ J}` with specifications that are probability measures, depend on `σ` only
  off `B_j`, give measurable block averages, and satisfy the DLR identity `μ(P_j h) = μ(h)` (Lemma 2.1, here a field;
  `OneScale.Product` proves it for product measures with a factorised density).
* `IsInfluenceBound B q z k`: the dual-form boundary-influence coefficient in homogeneous form (note §1.6): for every
  bounded measurable `F` depending only on `B` with all single-coordinate oscillations on `B` at most `L`,
  `|q^σ(F) - q^{σ'}(F)| ≤ k L` when `σ, σ'` differ only at `z`. The note's `k^H_B(z)` is the least such `k`.
* `coverage`, `GDS`: the coverage `c(x)` and the hypothesis `GDS(ℬ, γ)`: `∑_{j : z ∉ B_j} k_j(z) ≤ γ c(z)`.

The pull-out property (Lemma 2.2), the bound `|h - P_B h| ≤ ∑_{y ∈ B} δ_y(h)` and the block covariance identity
(Lemma 2.6) are proved here.
-/

open MeasureTheory Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace OneScale

variable {ι S : Type*} [DecidableEq ι]

/-! ## Splicing -/

/-- The configuration equal to `ξ` on `B` and to `σ` off `B`. -/
def splice (B : Finset ι) (σ ξ : ι → S) : ι → S := fun i => if i ∈ B then ξ i else σ i

theorem splice_of_mem {B : Finset ι} {i : ι} (h : i ∈ B) (σ ξ : ι → S) : splice B σ ξ i = ξ i := by
  simp [splice, h]

theorem splice_of_not_mem {B : Finset ι} {i : ι} (h : i ∉ B) (σ ξ : ι → S) : splice B σ ξ i = σ i := by
  simp [splice, h]

theorem splice_splice_left (B : Finset ι) (σ ξ ξ' : ι → S) : splice B (splice B σ ξ) ξ' = splice B σ ξ' := by
  funext i; by_cases h : i ∈ B <;> simp [splice, h]

theorem splice_congr_left {B : Finset ι} {σ σ' : ι → S} (h : ∀ i ∉ B, σ i = σ' i) (ξ : ι → S) :
    splice B σ ξ = splice B σ' ξ := by
  funext i; by_cases hi : i ∈ B <;> simp [splice, hi, h]

theorem splice_eq_off (B : Finset ι) (σ ξ : ι → S) : ∀ i ∉ B, splice B σ ξ i = σ i :=
  fun _ hi => splice_of_not_mem hi σ ξ

theorem splice_update_left {B : Finset ι} {x : ι} (hx : x ∉ B) (σ ξ : ι → S) (s : S) :
    splice B (Function.update σ x s) ξ = Function.update (splice B σ ξ) x s := by
  funext i
  by_cases hi : i = x
  · subst hi; simp [splice, hx]
  · by_cases hB : i ∈ B <;> simp [splice, hB, hi]

theorem splice_update_right {B : Finset ι} {y : ι} (hy : y ∈ B) (σ ξ : ι → S) (t : S) :
    splice B σ (Function.update ξ y t) = Function.update (splice B σ ξ) y t := by
  funext i
  by_cases hi : i = y
  · subst hi; simp [splice, hy]
  · by_cases hB : i ∈ B <;> simp [splice, hB, hi]

theorem splice_update_mem {B : Finset ι} {x : ι} (hx : x ∈ B) (σ ξ : ι → S) (s : S) :
    splice B (Function.update σ x s) ξ = splice B σ ξ := by
  funext i
  by_cases hi : i = x
  · subst hi; simp [splice, hx]
  · by_cases hB : i ∈ B <;> simp [splice, hB, hi]

/-! ## Dependence and oscillation bounds -/

/-- `h` depends only on the coordinates in `A`. -/
def DepOn (h : (ι → S) → ℝ) (A : Finset ι) : Prop := ∀ σ σ' : ι → S, (∀ i ∈ A, σ i = σ' i) → h σ = h σ'

/-- `v` bounds the single-coordinate oscillations of `h`: `|h σ - h σ'| ≤ v x` whenever `σ, σ'` differ only at `x`
(the note's `δ_x(h) ≤ v x`, §1.5). -/
def OscBound (h : (ι → S) → ℝ) (v : ι → ℝ) : Prop :=
  ∀ (σ : ι → S) (x : ι) (s : S), |h σ - h (Function.update σ x s)| ≤ v x

theorem OscBound.mono {h : (ι → S) → ℝ} {v v' : ι → ℝ} (hv : OscBound h v) (hle : ∀ x, v x ≤ v' x) :
    OscBound h v' := fun σ x s => (hv σ x s).trans (hle x)

theorem OscBound.nonneg {h : (ι → S) → ℝ} {v : ι → ℝ} (hv : OscBound h v) (σ : ι → S) (x : ι) : 0 ≤ v x :=
  (abs_nonneg _).trans (hv σ x (σ x))

/-- **Lemma 2.3 (telescoping).** If `σ = σ'` off `T`, then `|h σ - h σ'| ≤ ∑_{x ∈ T} v x`. -/
theorem OscBound.abs_sub_le {h : (ι → S) → ℝ} {v : ι → ℝ} (hv : OscBound h v) (T : Finset ι) :
    ∀ {σ σ' : ι → S}, (∀ i ∉ T, σ i = σ' i) → |h σ - h σ'| ≤ ∑ x ∈ T, v x := by
  induction T using Finset.induction_on with
  | empty =>
    intro σ σ' hT
    have : σ = σ' := funext fun i => hT i (Finset.notMem_empty i)
    simp [this]
  | insert a T ha ih =>
    intro σ σ' hT
    set σ'' := Function.update σ a (σ' a)
    have h1 : ∀ i ∉ T, σ'' i = σ' i := by
      intro i hi
      by_cases hia : i = a
      · subst hia; simp [σ'']
      · simp only [σ'', Function.update_of_ne hia]
        exact hT i (by simp [hia, hi])
    rw [Finset.sum_insert ha]
    calc |h σ - h σ'| ≤ |h σ - h σ''| + |h σ'' - h σ'| := _root_.abs_sub_le _ _ _
      _ ≤ v a + ∑ x ∈ T, v x := add_le_add (hv σ a (σ' a)) (ih h1)

/-- For `h` depending only on `A`: changing the coordinates in `B` changes `h` by at most `∑_{a ∈ B ∩ A} v a`. -/
theorem OscBound.abs_sub_splice_le {h : (ι → S) → ℝ} {v : ι → ℝ} (hv : OscBound h v) {A : Finset ι}
    (hA : DepOn h A) (B : Finset ι) (σ ξ : ι → S) : |h σ - h (splice B σ ξ)| ≤ ∑ a ∈ B ∩ A, v a := by
  have heq : h (splice B σ ξ) = h (splice (B ∩ A) σ ξ) := by
    apply hA
    intro i hi
    by_cases hB : i ∈ B
    · simp [splice, hB, hi]
    · simp [splice, hB]
  rw [heq]
  exact hv.abs_sub_le (B ∩ A) (fun i hi => (splice_of_not_mem hi σ ξ).symm)

/-- A function depending only on `A` has zero oscillation off `A`. -/
theorem DepOn.update_eq {h : (ι → S) → ℝ} {A : Finset ι} (hA : DepOn h A) {x : ι} (hx : x ∉ A) (σ : ι → S)
    (s : S) : h (Function.update σ x s) = h σ := by
  apply hA
  intro i hi
  have : i ≠ x := fun h => hx (h ▸ hi)
  simp [Function.update_of_ne this]

/-! ## Bounded measurable functions -/

variable [MeasurableSpace S]

/-- `h` is bounded and measurable. -/
structure BM (h : (ι → S) → ℝ) : Prop where
  meas : Measurable h
  bdd : ∃ C, ∀ σ, |h σ| ≤ C

theorem BM.integrable {h : (ι → S) → ℝ} (hh : BM h) (ν : Measure (ι → S)) [IsFiniteMeasure ν] :
    Integrable h ν := by
  obtain ⟨C, hC⟩ := hh.bdd
  exact Integrable.of_bound hh.meas.aestronglyMeasurable C (Filter.Eventually.of_forall fun σ => by
    rw [Real.norm_eq_abs]; exact hC σ)

theorem BM.const (c : ℝ) : BM (fun _ : ι → S => c) := ⟨measurable_const, ⟨|c|, fun _ => le_rfl⟩⟩

theorem BM.add {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) : BM (fun σ => f σ + g σ) := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨D, hD⟩ := hg.bdd
  exact ⟨hf.meas.add hg.meas, ⟨C + D, fun σ => (abs_add_le _ _).trans (add_le_add (hC σ) (hD σ))⟩⟩

theorem BM.sub {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) : BM (fun σ => f σ - g σ) := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨D, hD⟩ := hg.bdd
  exact ⟨hf.meas.sub hg.meas, ⟨C + D, fun σ => (abs_sub _ _).trans (add_le_add (hC σ) (hD σ))⟩⟩

theorem BM.mul {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) : BM (fun σ => f σ * g σ) := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨D, hD⟩ := hg.bdd
  refine ⟨hf.meas.mul hg.meas, ⟨C * D, fun σ => ?_⟩⟩
  rw [abs_mul]
  exact mul_le_mul (hC σ) (hD σ) (abs_nonneg _) ((abs_nonneg _).trans (hC σ))

theorem BM.const_mul {f : (ι → S) → ℝ} (hf : BM f) (c : ℝ) : BM (fun σ => c * f σ) :=
  (BM.const c).mul hf

theorem BM.sum {J : Type*} (s : Finset J) {f : J → (ι → S) → ℝ} (hf : ∀ j, BM (f j)) :
    BM (fun σ => ∑ j ∈ s, f j σ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BM.const (ι := ι) (S := S) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a).add ih

theorem measurable_splice_right (B : Finset ι) (σ : ι → S) : Measurable (splice B σ) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : i ∈ B
  · simp only [splice, h, ite_true]; exact measurable_pi_apply i
  · simp only [splice, h, ite_false]; exact measurable_const

theorem measurable_splice (B : Finset ι) :
    Measurable (fun p : (ι → S) × (ι → S) => splice B p.1 p.2) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : i ∈ B
  · simp only [splice, h, ite_true]; exact (measurable_pi_apply i).comp measurable_snd
  · simp only [splice, h, ite_false]; exact (measurable_pi_apply i).comp measurable_fst

/-! ## Block averages -/

/-- The block average `P_B h (σ) = ∫ h (σ_{Ω∖B}, ξ) q^σ(dξ)` (note §1.4). Only the `B`-coordinates of `ξ` are used. -/
def blockAvg (B : Finset ι) (q : (ι → S) → Measure (ι → S)) (h : (ι → S) → ℝ) (σ : ι → S) : ℝ :=
  ∫ ξ, h (splice B σ ξ) ∂(q σ)

/-- **Block specification.** A finite family of blocks with specifications `q_j^σ` that are probability measures, depend
on `σ` only off the block, have measurable block averages and satisfy the DLR identity (Lemma 2.1) for `μ`. -/
structure BlockSpec (μ : Measure (ι → S)) (J : Type*) where
  /-- The blocks `B_j`. -/
  block : J → Finset ι
  /-- The specification `q_j^σ`, a measure on configurations of which only the block coordinates are used. -/
  spec : J → (ι → S) → Measure (ι → S)
  isProb : ∀ j σ, IsProbabilityMeasure (spec j σ)
  spec_congr : ∀ j (σ σ' : ι → S), (∀ i ∉ block j, σ i = σ' i) → spec j σ = spec j σ'
  meas_avg : ∀ j (h : (ι → S) → ℝ), BM h → Measurable (blockAvg (block j) (spec j) h)
  dlr : ∀ j (h : (ι → S) → ℝ), BM h → ∫ σ, blockAvg (block j) (spec j) h σ ∂μ = ∫ σ, h σ ∂μ

/-- **Boundary-influence coefficient, homogeneous dual form** (note §1.6). `k` bounds the influence of the outside
coordinate `z` on the specification `q` of the block `B`, tested on bounded measurable functions of the block. -/
def IsInfluenceBound (B : Finset ι) (q : (ι → S) → Measure (ι → S)) (z : ι) (k : ℝ) : Prop :=
  ∀ (σ : ι → S) (s : S) (F : (ι → S) → ℝ) (L : ℝ), BM F → DepOn F B →
    (∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L) →
    |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q (Function.update σ z s))| ≤ k * L

variable {J : Type*} [Fintype J]

/-- The coverage `c(x) = #{j : x ∈ B_j}`. -/
def coverage (block : J → Finset ι) (x : ι) : ℕ := (univ.filter fun j => x ∈ block j).card

/-- **Hypothesis GDS(ℬ, γ)** (note §1.7): `∑_{j : z ∉ B_j} k_j(z) ≤ γ c(z)` for every `z`. (Coefficients of blocks
not adjacent to `z` may be taken to be `0`; only `k_j(z)` for `z` in the shell matters.) -/
def GDS (block : J → Finset ι) (k : J → ι → ℝ) (γ : ℝ) : Prop :=
  ∀ z : ι, ∑ j ∈ univ.filter (fun j => z ∉ block j), k j z ≤ γ * coverage block z

/-! ## Elementary properties of block averages -/

section BlockAvg

variable {B : Finset ι} {q : (ι → S) → Measure (ι → S)}

theorem integrable_comp_splice {h : (ι → S) → ℝ} (hh : BM h) (σ : ι → S) (ν : Measure (ι → S))
    [IsFiniteMeasure ν] : Integrable (fun ξ => h (splice B σ ξ)) ν := by
  obtain ⟨C, hC⟩ := hh.bdd
  exact Integrable.of_bound (hh.meas.comp (measurable_splice_right B σ)).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact hC _)

/-- The block average does not read the block coordinates. -/
theorem blockAvg_splice (hq : ∀ σ σ' : ι → S, (∀ i ∉ B, σ i = σ' i) → q σ = q σ') (h : (ι → S) → ℝ)
    (σ ξ : ι → S) : blockAvg B q h (splice B σ ξ) = blockAvg B q h σ := by
  unfold blockAvg
  rw [hq _ σ (splice_eq_off B σ ξ)]
  simp_rw [splice_splice_left]

theorem blockAvg_update_mem (hq : ∀ σ σ' : ι → S, (∀ i ∉ B, σ i = σ' i) → q σ = q σ') (h : (ι → S) → ℝ)
    {x : ι} (hx : x ∈ B) (σ : ι → S) (s : S) : blockAvg B q h (Function.update σ x s) = blockAvg B q h σ := by
  unfold blockAvg
  rw [hq (Function.update σ x s) σ (fun i hi => by
    have : i ≠ x := fun h => hi (h ▸ hx)
    simp [Function.update_of_ne this])]
  simp_rw [splice_update_mem hx]

/-- `|P_B h| ≤ C` when `|h| ≤ C`. -/
theorem abs_blockAvg_le [∀ σ, IsProbabilityMeasure (q σ)] {h : (ι → S) → ℝ} {C : ℝ} (hC : ∀ σ, |h σ| ≤ C)
    (σ : ι → S) : |blockAvg B q h σ| ≤ C := by
  unfold blockAvg
  have := norm_integral_le_of_norm_le_const (μ := q σ) (f := fun ξ => h (splice B σ ξ)) (C := C)
    (Filter.Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact hC _)
  simpa [Real.norm_eq_abs] using this

/-- **Lemma 2.2 (pull-out).** If `u` does not read the block coordinates, `P_B (u h) = u P_B h`. -/
theorem blockAvg_mul_left {u h : (ι → S) → ℝ} (hu : ∀ σ ξ, u (splice B σ ξ) = u σ) (σ : ι → S) :
    blockAvg B q (fun τ => u τ * h τ) σ = u σ * blockAvg B q h σ := by
  unfold blockAvg
  simp_rw [hu]
  exact integral_const_mul _ _

/-- `|h - P_B h| ≤ ∑_{y ∈ B} δ_y(h)` (from Lemma 2.3). -/
theorem abs_sub_blockAvg_le [∀ σ, IsProbabilityMeasure (q σ)] {h : (ι → S) → ℝ} (hh : BM h) {v : ι → ℝ}
    (hv : OscBound h v) (σ : ι → S) : |h σ - blockAvg B q h σ| ≤ ∑ y ∈ B, v y := by
  unfold blockAvg
  have hint := integrable_comp_splice (B := B) hh σ (q σ)
  rw [show h σ = ∫ _ξ, h σ ∂(q σ) by simp, ← integral_sub (integrable_const _) hint]
  have := norm_integral_le_of_norm_le_const (μ := q σ) (f := fun ξ => h σ - h (splice B σ ξ))
    (C := ∑ y ∈ B, v y) (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs]
      exact hv.abs_sub_le B (fun i hi => (splice_of_not_mem hi σ ξ).symm))
  simpa [Real.norm_eq_abs] using this

/-- For `f` depending only on `A`: `|f - P_B f| ≤ ∑_{a ∈ B ∩ A} δ_a(f)` (the note's `osc_B(f)` bound). -/
theorem abs_sub_blockAvg_le_inter [∀ σ, IsProbabilityMeasure (q σ)] {f : (ι → S) → ℝ} (hf : BM f)
    {v : ι → ℝ} (hv : OscBound f v) {A : Finset ι} (hA : DepOn f A) (σ : ι → S) :
    |f σ - blockAvg B q f σ| ≤ ∑ a ∈ B ∩ A, v a := by
  unfold blockAvg
  have hint := integrable_comp_splice (B := B) hf σ (q σ)
  rw [show f σ = ∫ _ξ, f σ ∂(q σ) by simp, ← integral_sub (integrable_const _) hint]
  have := norm_integral_le_of_norm_le_const (μ := q σ) (f := fun ξ => f σ - f (splice B σ ξ))
    (C := ∑ a ∈ B ∩ A, v a) (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs]
      exact hv.abs_sub_splice_le hA B σ ξ)
  simpa [Real.norm_eq_abs] using this

end BlockAvg

/-! ## Consequences of a block specification -/

namespace BlockSpec

variable {μ : Measure (ι → S)} (P : BlockSpec μ J)

instance (j : J) (σ : ι → S) : IsProbabilityMeasure (P.spec j σ) := P.isProb j σ

theorem bm_avg (j : J) {h : (ι → S) → ℝ} (hh : BM h) : BM (blockAvg (P.block j) (P.spec j) h) := by
  obtain ⟨C, hC⟩ := hh.bdd
  exact ⟨P.meas_avg j h hh, ⟨C, abs_blockAvg_le hC⟩⟩

theorem avg_splice (j : J) (h : (ι → S) → ℝ) (σ ξ : ι → S) :
    blockAvg (P.block j) (P.spec j) h (splice (P.block j) σ ξ) = blockAvg (P.block j) (P.spec j) h σ :=
  blockAvg_splice (P.spec_congr j) h σ ξ

/-- **Lemma 2.6 (block covariance identity).** `μ(f (h - P_B h)) = μ((f - P_B f)(h - P_B h))`. -/
theorem integral_mul_sub_avg [IsFiniteMeasure μ] (j : J) {f h : (ι → S) → ℝ} (hf : BM f) (hh : BM h) :
    ∫ σ, f σ * (h σ - blockAvg (P.block j) (P.spec j) h σ) ∂μ =
      ∫ σ, (f σ - blockAvg (P.block j) (P.spec j) f σ) * (h σ - blockAvg (P.block j) (P.spec j) h σ) ∂μ := by
  set Pf := blockAvg (P.block j) (P.spec j) f
  set Ph := blockAvg (P.block j) (P.spec j) h
  have hPf := P.bm_avg j hf
  have hPh := P.bm_avg j hh
  -- `μ(P f · h) = μ(P (P f · h)) = μ(P f · P h)`
  have key : ∫ σ, Pf σ * h σ ∂μ = ∫ σ, Pf σ * Ph σ ∂μ := by
    rw [← P.dlr j _ (hPf.mul hh)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    exact blockAvg_mul_left (fun σ ξ => P.avg_splice j f σ ξ) σ
  have e1 : ∀ σ, (f σ - Pf σ) * (h σ - Ph σ) = f σ * (h σ - Ph σ) - (Pf σ * h σ - Pf σ * Ph σ) := by
    intro σ; ring
  simp_rw [e1]
  rw [integral_sub ((hf.mul (hh.sub hPh)).integrable μ) ((hPf.mul hh).sub (hPf.mul hPh) |>.integrable μ),
    integral_sub ((hPf.mul hh).integrable μ) ((hPf.mul hPh).integrable μ), key, sub_self, sub_zero]

end BlockSpec

end OneScale
