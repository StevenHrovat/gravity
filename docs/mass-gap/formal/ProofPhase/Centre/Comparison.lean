/-
Proof phase, cycle 7, workstream b (c7b-centre): the comparison of a Z2-times-background model with the Z2 model of the
worst-case couplings (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c7b-centre/NOTE.md`, section 2.
-/

import ProofPhase.Centre.Ginibre

/-!
# The centre comparison theorem

**Setting.** Spins `σ : ι → Bool` (the Z2 block variables, one per block link), a background `v` (the SO(3) remainder of the
blocked field), a Wilson loop of the form `W = σ_C · w(v)` with `|w| ≤ M` (`C` a multiset of links, `w` the SO(3)-dependent
factor). The Wilson measure, seen through its conditional law of `σ` given the background, is a Z2 model with couplings
`J(v)` of any sign.

* `comparison_integral` (**the comparison theorem, measure form**): if `⟨W⟩ = ∫ w(v) ⟨σ_C⟩_{J(v)} dμ(v)` for a probability
  measure `μ` on backgrounds (the *mixture decomposition*) and `|J(v)_k| ≤ J̄_k` for all `v, k`, then
  `|⟨W⟩| ≤ ⟨σ_C⟩_{J̄}` (the Z2 model with the worst-case couplings, even if `J(v)` has frustration signs).
  The decomposition is the named hypothesis of this form; the theorem is Ginibre (`abs_corr_le`) integrated.
* `comparison_finite` (**joint-weight form, decomposition proved**): for finitely many backgrounds `V` and *any* positive
  joint weight `ω v σ`, define `J(v)_A` as the Walsh coefficient of `log ω(v, ·)` (every positive function on `{±1}^ι` is
  `exp` of a multilinear polynomial: `exp_walsh`). If `|J(v)_A| ≤ J̄_A` for all `v` and all `A ⊆ ι`, then
  `|∑_{v,σ} ω σ_C w(v) / ∑_{v,σ} ω| ≤ ⟨σ_C⟩_{J̄}` with `J̄` indexed by all subsets `A ⊆ ι`. No hypothesis on the
  decomposition: it is a theorem for a finite background set. What stays open for SU(2) is (i) the passage to the
  continuous SO(3) background (`comparison_integral` takes the decomposition as a hypothesis there) and (ii) the size of `J̄`.
-/

open Finset Real

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Centre

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Walsh expansion: every positive weight is a Z2 model -/

/-- Interactions indexed by all subsets of sites: `supp A = A`. -/
def allSupp (A : Finset ι) : Multiset ι := A.val

/-- Walsh coefficient of a function on the cube. -/
def walsh (f : (ι → Bool) → ℝ) (A : Finset ι) : ℝ :=
  (∑ σ : ι → Bool, f σ * mono σ A.val) / 2 ^ Fintype.card ι

theorem mono_finset (σ : ι → Bool) (A : Finset ι) : mono σ A.val = ∏ i ∈ A, sgn (σ i) := rfl

theorem sum_mono_all (ρ : ι → Bool) :
    ∑ A : Finset ι, mono ρ A.val = if (∀ i, ρ i = false) then (2 : ℝ) ^ Fintype.card ι else 0 := by
  simp_rw [mono_finset]
  have h : ∑ A : Finset ι, ∏ i ∈ A, sgn (ρ i) = ∏ i, (1 + sgn (ρ i)) := by
    rw [Finset.prod_one_add, Finset.powerset_univ]
  rw [h]
  split_ifs with hall
  · have : ∀ i, 1 + sgn (ρ i) = 2 := fun i => by rw [hall i]; norm_num [sgn]
    simp [this]
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have : ρ i = true := by simpa using hi
    rw [this]; norm_num [sgn]

theorem xor_eq_false_iff (σ τ : ι → Bool) : (∀ i, xor (σ i) (τ i) = false) ↔ σ = τ := by
  constructor
  · intro h; ext i; have := h i; cases hs : σ i <;> cases ht : τ i <;> simp_all
  · rintro rfl i; simp

/-- **Walsh inversion**: `f = ∑_A f̂(A) σ_A`. -/
theorem walsh_inv (f : (ι → Bool) → ℝ) (σ : ι → Bool) :
    f σ = ∑ A : Finset ι, walsh f A * mono σ A.val := by
  have hN : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  unfold walsh
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul]
  rw [eq_div_iff hN.ne']
  rw [Finset.sum_comm]
  have h : ∀ τ : ι → Bool, ∑ A : Finset ι, f τ * mono τ A.val * mono σ A.val =
      f τ * (if σ = τ then (2 : ℝ) ^ Fintype.card ι else 0) := by
    intro τ
    have : ∀ A : Finset ι, f τ * mono τ A.val * mono σ A.val = f τ * mono (fun i => xor (σ i) (τ i)) A.val := by
      intro A; rw [mono_xor]; ring
    simp_rw [this, ← Finset.mul_sum, sum_mono_all]
    simp only [xor_eq_false_iff]
  simp_rw [h]
  simp [Finset.sum_ite_eq, mul_comm]

/-- Every positive weight on the cube is the Boltzmann weight of a Z2 model with couplings the Walsh coefficients of its
logarithm (the `∅` coefficient is the constant). -/
theorem exp_walsh {ω : (ι → Bool) → ℝ} (hω : ∀ σ, 0 < ω σ) (σ : ι → Bool) :
    ω σ = exp (energy allSupp (walsh (fun σ => Real.log (ω σ))) σ) := by
  have h := walsh_inv (fun σ => Real.log (ω σ)) σ
  have : energy allSupp (walsh (fun σ => Real.log (ω σ))) σ = Real.log (ω σ) := by
    rw [h]; rfl
  rw [this, Real.exp_log (hω σ)]

/-! ## The comparison theorem, measure form -/

section Integral

open MeasureTheory

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (supp : κ → Multiset ι)
  {Ω : Type*} [MeasurableSpace Ω]

/-- **The centre comparison theorem (measure form).** If the Wilson loop expectation is the `μ`-mixture
`∫ w(v) ⟨σ_C⟩_{J(v)} dμ(v)` of Z2 correlations (the *mixture decomposition*, taken as hypothesis `hmix`), with
`|w| ≤ 1` and `|J(v)_k| ≤ J̄_k` for all backgrounds `v` and interactions `k` (couplings of any sign), then
`|⟨W⟩| ≤ ⟨σ_C⟩_{J̄}`. -/
theorem comparison_integral (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : Ω → κ → ℝ) (w : Ω → ℝ) (M : ℝ) (hw : ∀ v, |w v| ≤ M) (Jbar : κ → ℝ) (hJ : ∀ v k, |J v k| ≤ Jbar k)
    (C : Multiset ι) (W : ℝ) (hmix : W = ∫ v, w v * corr supp (J v) C ∂μ) :
    |W| ≤ M * corr supp Jbar C := by
  rw [hmix]
  have hb : ∀ v, ‖w v * corr supp (J v) C‖ ≤ M * corr supp Jbar C := by
    intro v
    rw [Real.norm_eq_abs, abs_mul]
    calc |w v| * |corr supp (J v) C| ≤ M * corr supp Jbar C :=
          mul_le_mul (hw v) (abs_corr_le supp (hJ v) C) (abs_nonneg _) ((abs_nonneg _).trans (hw v))
      _ = _ := by ring
  have := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hb)
  simpa using this

end Integral

/-! ## The comparison theorem, finite backgrounds, decomposition proved -/

section Finite

variable {V : Type*} [Fintype V]

/-- The joint-weight expectation `∑_{v,σ} ω(v,σ) σ_C w(v) / ∑_{v,σ} ω(v,σ)` of a Wilson loop `σ_C · w(v)`. -/
def jointExpect (ω : V → (ι → Bool) → ℝ) (w : V → ℝ) (C : Multiset ι) : ℝ :=
  (∑ v, ∑ σ : ι → Bool, ω v σ * (mono σ C * w v)) / ∑ v, ∑ σ : ι → Bool, ω v σ

/-- **The centre comparison theorem, finite backgrounds, decomposition proved.** For *any* positive joint weight `ω`
(the blocked Wilson weight, with the within-block fields integrated out, at each of finitely many backgrounds `v`), with
`J(v)_A` the Walsh coefficients of `log ω(v,·)`: if `|J(v)_A| ≤ J̄_A` for every background and every `A ⊆ ι`, and `|w| ≤ 1`,
then `|jointExpect ω w C| ≤ ⟨σ_C⟩_{J̄}` (the Z2 model with interactions on all subsets `A`, couplings `J̄`). -/
theorem comparison_finite [Nonempty V] (ω : V → (ι → Bool) → ℝ) (hω : ∀ v σ, 0 < ω v σ) (w : V → ℝ) (M : ℝ)
    (hw : ∀ v, |w v| ≤ M) (Jbar : Finset ι → ℝ)
    (hJ : ∀ v A, |walsh (fun σ => Real.log (ω v σ)) A| ≤ Jbar A) (C : Multiset ι) :
    |jointExpect ω w C| ≤ M * corr allSupp Jbar C := by
  set J : V → Finset ι → ℝ := fun v => walsh (fun σ => Real.log (ω v σ)) with hJdef
  have hexp : ∀ v σ, ω v σ = exp (energy allSupp (J v) σ) := fun v σ => exp_walsh (hω v) σ
  have hZ : ∀ v, 0 < Zf allSupp (J v) := fun v => Zf_pos _ _
  have hden : ∑ v, ∑ σ : ι → Bool, ω v σ = ∑ v, Zf allSupp (J v) := by
    refine Finset.sum_congr rfl (fun v _ => ?_)
    unfold Zf; exact Finset.sum_congr rfl (fun σ _ => hexp v σ)
  have hnum : ∑ v, ∑ σ : ι → Bool, ω v σ * (mono σ C * w v) = ∑ v, w v * num allSupp (J v) C := by
    refine Finset.sum_congr rfl (fun v _ => ?_)
    unfold num; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun σ _ => by rw [hexp v σ]; ring)
  have hpos : 0 < ∑ v, Zf allSupp (J v) := Finset.sum_pos (fun v _ => hZ v) Finset.univ_nonempty
  unfold jointExpect
  rw [hden, hnum, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have hb : ∀ v, |w v * num allSupp (J v) C| ≤ M * corr allSupp Jbar C * Zf allSupp (J v) := by
    intro v
    have h1 : |corr allSupp (J v) C| ≤ corr allSupp Jbar C := abs_corr_le allSupp (hJ v) C
    have h2 : |num allSupp (J v) C| ≤ corr allSupp Jbar C * Zf allSupp (J v) := by
      have : num allSupp (J v) C = corr allSupp (J v) C * Zf allSupp (J v) := by
        unfold corr; field_simp [(hZ v).ne']
      rw [this, abs_mul, abs_of_pos (hZ v)]
      exact mul_le_mul_of_nonneg_right h1 (hZ v).le
    rw [abs_mul]
    calc |w v| * |num allSupp (J v) C| ≤ M * (corr allSupp Jbar C * Zf allSupp (J v)) :=
          mul_le_mul (hw v) h2 (abs_nonneg _) ((abs_nonneg _).trans (hw v))
      _ = _ := by ring
  calc |∑ v, w v * num allSupp (J v) C| ≤ ∑ v, |w v * num allSupp (J v) C| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v, M * corr allSupp Jbar C * Zf allSupp (J v) := Finset.sum_le_sum (fun v _ => hb v)
    _ = M * corr allSupp Jbar C * ∑ v, Zf allSupp (J v) := by rw [Finset.mul_sum]

end Finite

end ProofPhase.Centre
