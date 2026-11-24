/-
Round 3, attempt 1: the robustness lemma with a local H2, and the gap from (H1-local) + (D′) (2026-11-21).
Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/r3-robust/NOTE.md`.
-/

import Attempts.R3.FlatFactors
import Attempts.R3.TailDecay
import OneScale.Effective.Physical

/-!
# The gap from local convergence of the effective action and flat factors of the limit

`OneScale.Effective.gap_of_effective(_W)` needs (H1) `EffectiveConvergence` and (H2) `LimitGDS(_W)`, a boundary-uniform
one-box bound for the limit theory. Round 2 (B) proposed the soft-swap criterion S′ (flat local factors) as a torus-type
H2 and asked for a "torus robustness lemma". This file closes the chain without one: the flatness criterion is a
pointwise statement about the local factors, so it already gives Dobrushin's (boundary-uniform) condition for the
single-site specification (`Attempts.R3.influence_site`), and it is an **open** condition in the local sup norm of the
potentials. Two routes:

**Route 1 (finite range, through the existing chain).**
* `LocalConvergence` (**H1-local**): at every site, the summed sup distance of the level-`k` potentials from the limit
  potentials, over the factors at that site, is `≤ ε_k → 0`, uniformly in the volume.
* `LimitFlat` (**D′ for the limit**): pair-oscillation bounds `S_{iz}` of the limit potentials with
  `∑_{i ≠ z} tanh(S_{iz}/2) ≤ γ < 1`, uniformly in the volume.
* `FactorGeometry`: factor diameters `≤ D₁` (coarse units), at most `r` sites share a factor with a given site.
* `effectiveConvergence_of_local`: H1-local ⇒ `EffectiveConvergence` (single-site blocks, `δ_k = tanh(ε_k/2)`).
* `limitGDS_of_flat`: D′ ⇒ `LimitGDS`.
* **`gap_of_localFactors`**: H1-local + D′ + geometry ⇒ exponential decay of block observables in physical units,
  uniform in the lattice spacing (`k ≥ k₀`) and in the volume (`OneScale.Effective.gap_of_effective`).

**Route 2 (quasi-local factors with tails, direct).**
* `LocalConvergenceW`: per-factor sup distances `η_k(x)`, with the weighted pair sums
  `∑_{i ≠ z} (∑_{x ∋ i, z} η_k(x)) e^{λ dist(z, i)} ≤ ε_k → 0` uniformly in the volume.
* `LimitFlatW`: the weighted criterion `∑_{i ≠ z} tanh(S_{iz}/2) e^{λ dist(z, i)} ≤ γ < 1` for the limit.
* `pairOsc_of_close`, `flatW_of_close`: **openness**: the level-`k` theory satisfies the weighted criterion with
  `γ + 2ε_k`; `levelFlat_of_local`: from some `k₀` on, with `(1 + γ)/2`, in every volume.
* `decay_of_flatW`: the weighted criterion gives Theorem A for the single-site specification of one effective theory
  (`Attempts.R3.theoremA_w`), with constants depending only on `γ`.
* **`gap_of_localFactorsW`** and **`gap_of_localFactorsW_fine`**: H1-local (weighted) + D′_λ for the limit ⇒ decay of
  block observables at the physical rate `λ/(2L₁)`, constant `2/(1 - γ)`, uniformly in `k ≥ k₀` and in the volume;
  the same for the fine theory's observables that are functions of the block variables.
* `limit_decay`: the limit theory itself has the decay, uniformly in the volume (no `k`).

No finite-range assumption is needed in route 2; supports may be arbitrary as long as the weighted sums converge.

**Route A (the continuum limit, per volume).** `continuum_decay`: if the level-`k` block laws converge, in each volume,
to the limit theory on bounded measurable functions (what W_p plus the transport lemma T of round 2 give, with no
locality and no uniformity in the volume), and the limit theory satisfies D′_λ, then the level-`k` block covariances
converge to limit covariances that decay at the physical rate `λ/L₁`, uniformly in the volume. This is the gap of the
continuum theory at scale `L₁`; routes 1 and 2 give the stronger statement uniform in the lattice spacing.
-/

open MeasureTheory Finset Filter Topology OneScale OneScale.Effective Influence

set_option linter.unusedSectionVars false

noncomputable section

namespace Attempts.R3

/-! ## Single volume: openness and decay under the weighted criterion -/

section One

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] {X : Type*} [Fintype X]

/-- **Pair oscillations move by at most twice the local sup distance.** If `S` bounds the pair oscillations of `V`
and `|V' x - V x| ≤ η x`, then `S_{iz} + 2 ∑_{x ∋ i, z} η x` bounds those of `V'`. -/
theorem pairOsc_of_close {supp : X → Finset ι} {V V' : X → (ι → S) → ℝ} {Sb : ι → ι → ℝ}
    (hS : PairOsc supp V Sb) {η : X → ℝ} (hη : ∀ x σ, |V' x σ - V x σ| ≤ η x) :
    PairOsc supp V' (fun i z => Sb i z + 2 * ∑ x ∈ pairFactors supp i z, η x) := by
  intro i z hz τ s
  set τ' := Function.update τ z s
  set P := pairFactors supp i z
  have e : ∑ x ∈ P, (V' x τ - V' x τ') =
      ∑ x ∈ P, (V x τ - V x τ') + (∑ x ∈ P, (V' x τ - V x τ) - ∑ x ∈ P, (V' x τ' - V x τ')) := by
    rw [← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun x _ => by ring
  rw [e]
  have h1 := hS i z hz τ s
  have h2 : |∑ x ∈ P, (V' x τ - V x τ)| ≤ ∑ x ∈ P, η x :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => hη x τ)
  have h3 : |∑ x ∈ P, (V' x τ' - V x τ')| ≤ ∑ x ∈ P, η x :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => hη x τ')
  calc |∑ x ∈ P, (V x τ - V x τ') + (∑ x ∈ P, (V' x τ - V x τ) - ∑ x ∈ P, (V' x τ' - V x τ'))|
      ≤ |∑ x ∈ P, (V x τ - V x τ')| + (|∑ x ∈ P, (V' x τ - V x τ)| + |∑ x ∈ P, (V' x τ' - V x τ')|) :=
        (abs_add_le _ _).trans (add_le_add_right (abs_sub _ _) _)
    _ ≤ Sb i z + 2 * ∑ x ∈ P, η x := by linarith

theorem FlatCriterionW.mono {dist : ι → ι → ℝ} {lam : ℝ} {Sb : ι → ι → ℝ} {γ γ' : ℝ}
    (h : FlatCriterionW dist lam Sb γ) (hγ : γ ≤ γ') : FlatCriterionW dist lam Sb γ' :=
  fun z => (h z).trans hγ

/-- **Openness of the weighted criterion.** If the limit pair oscillations satisfy D′_λ with `γ` and the weighted pair
sums of the local sup distances are `≤ ε`, the perturbed pair oscillations satisfy D′_λ with `γ + 2ε`. -/
theorem flatW_of_close {dist : ι → ι → ℝ} {lam γ ε : ℝ} {Sb : ι → ι → ℝ} (hS0 : ∀ i z, 0 ≤ Sb i z)
    (hflat : FlatCriterionW dist lam Sb γ) {supp : X → Finset ι} {η : X → ℝ} (hη0 : ∀ x, 0 ≤ η x)
    (hηsum : ∀ z, ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset ι)),
      (∑ x ∈ pairFactors supp i z, η x) * Real.exp (lam * dist z i) ≤ ε) :
    FlatCriterionW dist lam (fun i z => Sb i z + 2 * ∑ x ∈ pairFactors supp i z, η x) (γ + 2 * ε) := by
  intro z
  set F := univ.filter (fun i => z ∉ ({i} : Finset ι))
  have hterm : ∀ i, Real.tanh ((Sb i z + 2 * ∑ x ∈ pairFactors supp i z, η x) / 2) * Real.exp (lam * dist z i) ≤
      Real.tanh (Sb i z / 2) * Real.exp (lam * dist z i) +
        2 * ((∑ x ∈ pairFactors supp i z, η x) * Real.exp (lam * dist z i)) := by
    intro i
    have hH : 0 ≤ ∑ x ∈ pairFactors supp i z, η x := sum_nonneg fun x _ => hη0 x
    have ht : Real.tanh ((Sb i z + 2 * ∑ x ∈ pairFactors supp i z, η x) / 2) ≤
        Real.tanh (Sb i z / 2) + 2 * ∑ x ∈ pairFactors supp i z, η x := by
      rw [show (Sb i z + 2 * ∑ x ∈ pairFactors supp i z, η x) / 2 =
        Sb i z / 2 + ∑ x ∈ pairFactors supp i z, η x by ring]
      refine (OneScale.SingleLink.tanh_add_le (by linarith [hS0 i z]) hH).trans ?_
      linarith [tanh_le_two_mul hH]
    have he := Real.exp_pos (lam * dist z i)
    nlinarith
  calc ∑ i ∈ F, Real.tanh ((Sb i z + 2 * ∑ x ∈ pairFactors supp i z, η x) / 2) * Real.exp (lam * dist z i)
      ≤ ∑ i ∈ F, (Real.tanh (Sb i z / 2) * Real.exp (lam * dist z i) +
          2 * ((∑ x ∈ pairFactors supp i z, η x) * Real.exp (lam * dist z i))) := sum_le_sum fun i _ => hterm i
    _ = ∑ i ∈ F, Real.tanh (Sb i z / 2) * Real.exp (lam * dist z i) +
          2 * ∑ i ∈ F, (∑ x ∈ pairFactors supp i z, η x) * Real.exp (lam * dist z i) := by
        rw [sum_add_distrib, mul_sum]
    _ ≤ γ + 2 * ε := by linarith [hflat z, hηsum z]

/-- **Decay for one effective theory under the weighted criterion.** If the pair oscillations of `V` satisfy
D′_λ with `0 ≤ γ < 1` for a distance with `dist x x = 0` and the triangle inequality, then for `f` depending on `A`
(`δ_a(f) ≤ v_a`) and `g` depending on `S_g` (`δ_x(g) ≤ L_g`) with `R ≤ dist(a, s)`:
`|Cov(f, g)| ≤ (1 - γ)⁻¹ (∑_{a ∈ A} v_a) L_g e^{-λ R}` under the effective measure, in every volume, for every
boundary-free torus or finite set. -/
theorem decay_of_flatW (ν : Measure S) [IsProbabilityMeasure ν] [Nonempty ι] {supp : X → Finset ι}
    {V : X → (ι → S) → ℝ} (hV : Potential supp V) {Sb : ι → ι → ℝ} (hS : PairOsc supp V Sb)
    (dist : ι → ι → ℝ) (hd0 : ∀ x, dist x x = 0) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    {lam : ℝ} (hlam : 0 ≤ lam) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hflat : FlatCriterionW dist lam Sb γ)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A Sg : Finset ι} (hfA : DepOn f A) (hgS : DepOn g Sg)
    {vf : ι → ℝ} (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : OscBound g (fun _ => Lg))
    {R : ℝ} (hR : ∀ a ∈ A, ∀ s ∈ Sg, R ≤ dist a s) :
    |∫ σ, f σ * g σ ∂(gibbsMeasure ν V) - (∫ σ, f σ ∂(gibbsMeasure ν V)) * ∫ σ, g σ ∂(gibbsMeasure ν V)| ≤
      (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)) := by
  have := isProbabilityMeasure_gibbsMeasure ν hV
  set P := factorSpec ν supp V hV
  have hk : ∀ j z, z ∉ P.block j → IsInfluenceBound (P.block j) (P.spec j) z (Real.tanh (Sb j z / 2)) :=
    fun j z hz => influence_site ν hV hz (hS j z hz)
  have hcov : ∀ x, coverage P.block x = 1 := coverage_singleton
  have h := theoremA_w P (fun j z => Real.tanh (Sb j z / 2)) hk (cmin := 1) (cmax := 1) (b := 1) le_rfl
    (fun x => (hcov x).ge) (fun x => (hcov x).le) (fun j => by simp [P, factorSpec_block])
    dist hd0 htri (D₀ := 0)
    (fun j x hx y hy => by
      simp only [P, factorSpec_block, mem_singleton] at hx hy
      rw [hx, hy, hd0])
    (fun j x => dist x j)
    (fun j x y _ hy => by
      simp only [P, factorSpec_block, mem_singleton] at hy
      rw [hy])
    hlam hγ0 hγ1
    (fun x => by
      rw [hcov x, Nat.cast_one, mul_one]
      exact hflat x)
    hf hg hfA hgS hvf hLg hvg hR
  refine h.trans (le_of_eq ?_)
  simp only [Nat.cast_one, one_mul, sub_zero, one_div]

end One

/-! ## Families of volumes and levels -/

section Families

variable {Vol : Type*} {ι : Vol → Type*} [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)] {S : Type*}
  [MeasurableSpace S] {X : Vol → Type*} [∀ v, Fintype (X v)]

/-! ### Route 1: finite range, through `gap_of_effective` -/

/-- **Finite-range factor geometry** (one volume). A distance on the sites, factor diameters `≤ D₁`, and at most `r`
sites (other than `z`) sharing a factor with any site `z`. -/
structure FactorGeometry {ι' X' : Type*} [Fintype ι'] [DecidableEq ι'] [Fintype X'] (supp : X' → Finset ι')
    (dist : ι' → ι' → ℝ) (D₁ r : ℝ) : Prop where
  dist_self : ∀ x, dist x x = 0
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z
  diam_le : ∀ f, ∀ i ∈ supp f, ∀ j ∈ supp f, dist i j ≤ D₁
  r_nonneg : 0 ≤ r
  count_le : ∀ z, (shellCount (fun i : ι' => ({i} : Finset ι')) (nbhd supp) z : ℝ) ≤ r

/-- The factor geometry gives the uniform geometry of Theorem A for single-site blocks and factor-neighbourhood
shells, with `c₋ = c₊ = b = 1`, `D₀ = 0`. -/
theorem FactorGeometry.uniform {ι' X' : Type*} [Fintype ι'] [DecidableEq ι'] [Fintype X']
    {supp : X' → Finset ι'} {dist : ι' → ι' → ℝ} {D₁ r : ℝ} (G : FactorGeometry supp dist D₁ r) :
    UniformGeometry (fun i : ι' => ({i} : Finset ι')) (nbhd supp) dist 1 1 1 0 D₁ r where
  one_le_cmin := le_rfl
  cmin_le x := (coverage_singleton x).ge
  le_cmax x := (coverage_singleton x).le
  card_le j := by simp
  dist_self := G.dist_self
  dist_triangle := G.dist_triangle
  diam_le j x hx y hy := by
    rw [mem_singleton] at hx hy
    rw [hx, hy, G.dist_self]
  shell_dist_le j x y hx _ hy := by
    rw [mem_singleton] at hy
    rw [hy]
    obtain ⟨f, hf, hxf⟩ := mem_biUnion.1 hx
    exact G.diam_le f x hxf j (mem_filter.1 hf).2
  r_nonneg := G.r_nonneg
  shellCount_le z := by rw [coverage_singleton, Nat.cast_one, mul_one]; exact G.count_le z

/-- **(H1-local).** At every site of every volume, the level-`k` potentials are within `ε_k` of the limit potentials
in summed sup norm over the factors at that site, `ε_k → 0`. -/
def LocalConvergence (supp : ∀ v, X v → Finset (ι v)) (Vk : ∀ v, ℕ → X v → (ι v → S) → ℝ)
    (Vinf : ∀ v, X v → (ι v → S) → ℝ) : Prop :=
  ∃ ε : ℕ → ℝ, (∀ k, 0 ≤ ε k) ∧ Tendsto ε atTop (𝓝 0) ∧
    ∀ v k i σ, ∑ x ∈ factorsAt (supp v) i, |Vk v k x σ - Vinf v x σ| ≤ ε k

/-- **(D′ for the limit).** Pair-oscillation bounds of the limit potentials with `∑_{i ≠ z} tanh(S_{iz}/2) ≤ γ < 1`,
the same `γ` in every volume. -/
def LimitFlat (supp : ∀ v, X v → Finset (ι v)) (Vinf : ∀ v, X v → (ι v → S) → ℝ) : Prop :=
  ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∃ Sb : ∀ v, ι v → ι v → ℝ, (∀ v i z, 0 ≤ Sb v i z) ∧
    ∀ v, PairOsc (supp v) (Vinf v) (Sb v) ∧ FlatCriterion (Sb v) γ

theorem abs_siteLog_sub_le {ι' X' S' : Type*} [Fintype ι'] [DecidableEq ι'] [Fintype X'] {supp : X' → Finset ι'}
    {V V' : X' → (ι' → S') → ℝ} (i : ι') (σ : ι' → S') :
    |siteLog supp V i σ - siteLog supp V' i σ| ≤ ∑ x ∈ factorsAt supp i, |V' x σ - V x σ| := by
  unfold siteLog
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
  rw [abs_sub_comm]

/-- **H1-local gives `EffectiveConvergence`** for the single-site specifications, with `δ_k = tanh(ε_k/2) ≤ ε_k`. The
distance is local (only the factors at one site enter), so it is uniform in the volume. -/
theorem effectiveConvergence_of_local (ν : Measure S) [IsProbabilityMeasure ν] (supp : ∀ v, X v → Finset (ι v))
    (Vk : ∀ v, ℕ → X v → (ι v → S) → ℝ) (Vinf : ∀ v, X v → (ι v → S) → ℝ)
    (hVk : ∀ v k, Potential (supp v) (Vk v k)) (hVinf : ∀ v, Potential (supp v) (Vinf v))
    (hH1 : LocalConvergence supp Vk Vinf) :
    EffectiveConvergence (μ := fun v k => gibbsMeasure ν (Vk v k))
      (fun v k => factorSpec ν (supp v) (Vk v k) (hVk v k)) (fun v i => ({i} : Finset (ι v)))
      (fun v => nbhd (supp v)) (fun v => siteSpec ν (supp v) (Vinf v)) := by
  obtain ⟨ε, hε0, hε, hclose⟩ := hH1
  refine ⟨fun v k => rfl, fun v k j => siteSpec_isLocal ν (hVk v k) j, fun k => Real.tanh (ε k / 2),
    fun k => OneScale.SingleLink.tanh_nonneg (by linarith [hε0 k]), ?_, fun v k j => ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hε
      (fun k => OneScale.SingleLink.tanh_nonneg (by linarith [hε0 k])) (fun k => ?_)
    have := tanh_le_two_mul (x := ε k / 2) (by linarith [hε0 k])
    linarith
  · exact specDist_site ν (hVinf v) (hVk v k) j fun τ => (abs_siteLog_sub_le j τ).trans (hclose v k j τ)

/-- **D′ for the limit gives `LimitGDS`** (single-site blocks, H form, every boundary condition). -/
theorem limitGDS_of_flat (ν : Measure S) [IsProbabilityMeasure ν] (supp : ∀ v, X v → Finset (ι v))
    (Vinf : ∀ v, X v → (ι v → S) → ℝ) (hVinf : ∀ v, Potential (supp v) (Vinf v)) (hH2 : LimitFlat supp Vinf) :
    LimitGDS (fun v i => ({i} : Finset (ι v))) (fun v => siteSpec ν (supp v) (Vinf v)) := by
  obtain ⟨γ, hγ0, hγ1, Sb, hS0, hS⟩ := hH2
  exact ⟨γ, hγ0, hγ1, fun v => ⟨fun i z => Real.tanh (Sb v i z / 2),
    fun i z => OneScale.SingleLink.tanh_nonneg (by linarith [hS0 v i z]),
    fun i z hz => influence_site ν (hVinf v) hz ((hS v).1 i z hz), gds_of_flat (hS v).2⟩⟩

/-- **The gap from H1-local and D′ (route 1, finite range).** Effective measures `Z⁻¹ e^{∑_x V_k(x)}` on the block
variables of every volume, with finite-range factor geometry uniform in the volume, coarse blocks of physical size
`s_k = ⌈L₁/a_k⌉ a_k`, `a_k → 0`. If the level-`k` potentials converge locally to limit potentials (H1-local) and the
limit potentials satisfy D′, then there are `m > 0`, `C ≥ 0`, `k₀` such that for every `k ≥ k₀` and **every volume**,
block observables at physical distance `R` have `|Cov| ≤ C (∑_{x ∈ A} v_x) L_g e^{-m R}`. -/
theorem gap_of_localFactors [∀ v, Nonempty (ι v)] (ν : Measure S) [IsProbabilityMeasure ν]
    (supp : ∀ v, X v → Finset (ι v)) (Vk : ∀ v, ℕ → X v → (ι v → S) → ℝ) (Vinf : ∀ v, X v → (ι v → S) → ℝ)
    (hVk : ∀ v k, Potential (supp v) (Vk v k)) (hVinf : ∀ v, Potential (supp v) (Vinf v))
    (dist : ∀ v, ι v → ι v → ℝ) {D₁ r : ℝ} (hD₁ : 0 < D₁) (G : ∀ v, FactorGeometry (supp v) (dist v) D₁ r)
    {L₁ : ℝ} (hL₁ : 0 < L₁) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (hH1 : LocalConvergence supp Vk Vinf) (hH2 : LimitFlat supp Vinf) :
    ∃ m : ℝ, 0 < m ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ v,
      ∀ (f g : (ι v → S) → ℝ) (A Sg : Finset (ι v)) (vf : ι v → ℝ) (Lg R : ℝ),
        BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) → 0 ≤ R →
        (∀ x ∈ A, ∀ y ∈ Sg, R ≤ blockSize L₁ a k * dist v x y) →
        |∫ σ, f σ * g σ ∂(gibbsMeasure ν (Vk v k)) -
            (∫ σ, f σ ∂(gibbsMeasure ν (Vk v k))) * ∫ σ, g σ ∂(gibbsMeasure ν (Vk v k))| ≤
          C * (∑ x ∈ A, vf x) * Lg * Real.exp (-(m * R)) := by
  have : ∀ v k, IsProbabilityMeasure (gibbsMeasure ν (Vk v k)) := fun v k =>
    isProbabilityMeasure_gibbsMeasure ν (hVk v k)
  obtain ⟨m, hm, C, hC, k₀, h⟩ := gap_of_effective (μ := fun v k => gibbsMeasure ν (Vk v k))
    (fun v k => factorSpec ν (supp v) (Vk v k) (hVk v k)) (fun v i => ({i} : Finset (ι v)))
    (fun v => nbhd (supp v)) (fun v => siteSpec ν (supp v) (Vinf v)) dist hD₁ (fun v => (G v).uniform) hL₁ ha ha0
    ⟨effectiveConvergence_of_local ν supp Vk Vinf hVk hVinf hH1, limitGDS_of_flat ν supp Vinf hVinf hH2⟩
  refine ⟨m, hm, C, hC, k₀, fun k hk v f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR0 hR => ?_⟩
  have := h k hk v f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR0 hR
  rwa [Nat.cast_one, one_mul] at this

/-! ### Route 2: quasi-local factors, direct -/

/-- **(H1-local, weighted).** Per-factor sup distances `η_k(x)` between the level-`k` and the limit potentials, whose
weighted pair sums `∑_{i ≠ z} (∑_{x ∋ i, z} η_k(x)) e^{λ dist(z, i)}` are `≤ ε_k → 0`, uniformly in the volume. -/
def LocalConvergenceW (supp : ∀ v, X v → Finset (ι v)) (dist : ∀ v, ι v → ι v → ℝ) (lam : ℝ)
    (Vk : ∀ v, ℕ → X v → (ι v → S) → ℝ) (Vinf : ∀ v, X v → (ι v → S) → ℝ) : Prop :=
  ∃ η : ∀ v, ℕ → X v → ℝ, (∀ v k x, 0 ≤ η v k x) ∧ (∀ v k x σ, |Vk v k x σ - Vinf v x σ| ≤ η v k x) ∧
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ v k z, ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset (ι v))),
        (∑ x ∈ pairFactors (supp v) i z, η v k x) * Real.exp (lam * dist v z i) ≤ ε k

/-- **(D′_λ for the limit).** Pair-oscillation bounds of the limit potentials with
`∑_{i ≠ z} tanh(S_{iz}/2) e^{λ dist(z, i)} ≤ γ < 1`, the same `γ` in every volume. -/
def LimitFlatW (supp : ∀ v, X v → Finset (ι v)) (dist : ∀ v, ι v → ι v → ℝ) (lam : ℝ)
    (Vinf : ∀ v, X v → (ι v → S) → ℝ) : Prop :=
  ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∃ Sb : ∀ v, ι v → ι v → ℝ, (∀ v i z, 0 ≤ Sb v i z) ∧
    ∀ v, PairOsc (supp v) (Vinf v) (Sb v) ∧ FlatCriterionW (dist v) lam (Sb v) γ

/-- **Openness (the robustness lemma in local form).** Under H1-local (weighted) and D′_λ for the limit with `γ`,
from some `k₀` on the level-`k` theory itself satisfies D′_λ with `(1 + γ)/2`, in every volume. -/
theorem levelFlat_of_local (supp : ∀ v, X v → Finset (ι v)) (dist : ∀ v, ι v → ι v → ℝ) {lam : ℝ}
    (Vk : ∀ v, ℕ → X v → (ι v → S) → ℝ) (Vinf : ∀ v, X v → (ι v → S) → ℝ)
    (hH1 : LocalConvergenceW supp dist lam Vk Vinf) (hH2 : LimitFlatW supp dist lam Vinf) :
    ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ v, ∃ Sb : ι v → ι v → ℝ,
      PairOsc (supp v) (Vk v k) Sb ∧ FlatCriterionW (dist v) lam Sb (effGamma γ) := by
  obtain ⟨η, hη0, hη, ε, hε, hsum⟩ := hH1
  obtain ⟨γ, hγ0, hγ1, Sb, hS0, hS⟩ := hH2
  have he : Tendsto (fun k => 2 * ε k) atTop (𝓝 0) := by simpa using hε.const_mul 2
  obtain ⟨k₀, hk₀⟩ := eventually_le_half hγ1 he
  refine ⟨γ, hγ0, hγ1, k₀, fun k hk v => ⟨_, pairOsc_of_close (hS v).1 (hη v k), ?_⟩⟩
  exact (flatW_of_close (hS0 v) (hS v).2 (hη0 v k) (hsum v k)).mono (hk₀ k hk)

/-- **The gap from H1-local and D′_λ (route 2, quasi-local factors).** As `gap_of_localFactors`, with weighted
hypotheses and no finite-range assumption: for every `k ≥ k₀` and every volume,
`|Cov| ≤ C (∑_{x ∈ A} v_x) L_g e^{-m R}`, `m = λ/(2L₁)`, `C = 2/(1 - γ)`, `R` the physical distance. -/
theorem gap_of_localFactorsW [∀ v, Nonempty (ι v)] (ν : Measure S) [IsProbabilityMeasure ν]
    (supp : ∀ v, X v → Finset (ι v)) (Vk : ∀ v, ℕ → X v → (ι v → S) → ℝ) (Vinf : ∀ v, X v → (ι v → S) → ℝ)
    (hVk : ∀ v k, Potential (supp v) (Vk v k)) (dist : ∀ v, ι v → ι v → ℝ) (hd0 : ∀ v x, dist v x x = 0)
    (htri : ∀ v x y z, dist v x z ≤ dist v x y + dist v y z) {lam : ℝ} (hlam : 0 < lam)
    {L₁ : ℝ} (hL₁ : 0 < L₁) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (hH1 : LocalConvergenceW supp dist lam Vk Vinf) (hH2 : LimitFlatW supp dist lam Vinf) :
    ∃ m : ℝ, 0 < m ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ v,
      ∀ (f g : (ι v → S) → ℝ) (A Sg : Finset (ι v)) (vf : ι v → ℝ) (Lg R : ℝ),
        BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) → 0 ≤ R →
        (∀ x ∈ A, ∀ y ∈ Sg, R ≤ blockSize L₁ a k * dist v x y) →
        |∫ σ, f σ * g σ ∂(gibbsMeasure ν (Vk v k)) -
            (∫ σ, f σ ∂(gibbsMeasure ν (Vk v k))) * ∫ σ, g σ ∂(gibbsMeasure ν (Vk v k))| ≤
          C * (∑ x ∈ A, vf x) * Lg * Real.exp (-(m * R)) := by
  obtain ⟨γ, hγ0, hγ1, k₁, hlev⟩ := levelFlat_of_local supp dist Vk Vinf hH1 hH2
  obtain ⟨k₂, hk₂⟩ := eventually_atTop.1 ((tendsto_order.1 ha0).2 _ hL₁)
  set γ' := effGamma γ
  have hγ'0 : 0 ≤ γ' := (effGamma_pos hγ0).le
  have hγ'1 : γ' < 1 := effGamma_lt_one hγ1
  have hgap : 0 < 1 - γ' := by linarith
  refine ⟨lam / (2 * L₁), div_pos hlam (by linarith), (1 - γ')⁻¹, (inv_pos.2 hgap).le, max k₁ k₂, ?_⟩
  intro k hk v f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR0 hR
  obtain ⟨Sb, hS, hflat⟩ := hlev k (le_of_max_le_left hk) v
  set s := blockSize L₁ a k
  have hs : 0 < s := hL₁.trans_le (le_blockSize ha k)
  have hsL : s ≤ 2 * L₁ := by
    have h1 := blockSize_lt hL₁.le ha k
    have h2 := (hk₂ k (le_of_max_le_right hk)).le
    linarith
  have hR' : ∀ x ∈ A, ∀ y ∈ Sg, R / s ≤ dist v x y := fun x hx y hy =>
    (div_le_iff₀ hs).2 ((hR x hx y hy).trans_eq (mul_comm _ _))
  have key := decay_of_flatW ν (hVk v k) hS (dist v) (hd0 v) (htri v) hlam.le hγ'0 hγ'1 hflat hf hg hfA hgS hvf
    hLg hvg hR'
  obtain ⟨s₀⟩ := nonempty_of_isProbabilityMeasure ν
  have hX : 0 ≤ ∑ x ∈ A, vf x := sum_nonneg fun x _ => hvf.nonneg (fun _ => s₀) x
  refine key.trans ?_
  have hexp : Real.exp (-(lam * (R / s))) ≤ Real.exp (-(lam / (2 * L₁) * R)) := by
    have := exp_phys_le (D₀ := 0) hlam.le hR0 hs hsL
    simpa using this
  exact mul_le_mul_of_nonneg_left hexp (mul_nonneg (mul_nonneg (inv_pos.2 hgap).le hX) hLg)

/-- **The same for the fine theory's block observables.** If the effective measures are the laws of the block
variables under fine lattice measures (`(ν_f v k).map (Φ v k) = gibbsMeasure ν (Vk v k)`: the effective theory is
Gibbsian with the potentials `Vk`), the bound of `gap_of_localFactorsW` holds for `f ∘ Φ`, `g ∘ Φ`. -/
theorem gap_of_localFactorsW_fine [∀ v, Nonempty (ι v)] (ν : Measure S) [IsProbabilityMeasure ν]
    (supp : ∀ v, X v → Finset (ι v)) (Vk : ∀ v, ℕ → X v → (ι v → S) → ℝ) (Vinf : ∀ v, X v → (ι v → S) → ℝ)
    (hVk : ∀ v k, Potential (supp v) (Vk v k)) (dist : ∀ v, ι v → ι v → ℝ) (hd0 : ∀ v x, dist v x x = 0)
    (htri : ∀ v x y z, dist v x z ≤ dist v x y + dist v y z) {lam : ℝ} (hlam : 0 < lam)
    {L₁ : ℝ} (hL₁ : 0 < L₁) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    {Y : Vol → Type*} [∀ v, MeasurableSpace (Y v)] (νf : ∀ v, ℕ → Measure (Y v)) (Φ : ∀ v, ℕ → Y v → ι v → S)
    (hΦ : ∀ v k, Measurable (Φ v k)) (hμ : ∀ v k, (νf v k).map (Φ v k) = gibbsMeasure ν (Vk v k))
    (hH1 : LocalConvergenceW supp dist lam Vk Vinf) (hH2 : LimitFlatW supp dist lam Vinf) :
    ∃ m : ℝ, 0 < m ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ v,
      ∀ (f g : (ι v → S) → ℝ) (A Sg : Finset (ι v)) (vf : ι v → ℝ) (Lg R : ℝ),
        BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) → 0 ≤ R →
        (∀ x ∈ A, ∀ y ∈ Sg, R ≤ blockSize L₁ a k * dist v x y) →
        |∫ U, f (Φ v k U) * g (Φ v k U) ∂(νf v k) -
            (∫ U, f (Φ v k U) ∂(νf v k)) * ∫ U, g (Φ v k U) ∂(νf v k)| ≤
          C * (∑ x ∈ A, vf x) * Lg * Real.exp (-(m * R)) := by
  obtain ⟨m, hm, C, hC, k₀, h⟩ := gap_of_localFactorsW ν supp Vk Vinf hVk dist hd0 htri hlam hL₁ ha ha0 hH1 hH2
  refine ⟨m, hm, C, hC, k₀, fun k hk v f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR0 hR => ?_⟩
  rw [cov_map (νf v k) (hΦ v k) hf hg, hμ v k]
  exact h k hk v f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR0 hR

/-- **The limit theory has the decay, uniformly in the volume** (D′_λ alone; no level, no H1): in coarse units,
`|Cov| ≤ (1 - γ)⁻¹ (∑_{x ∈ A} v_x) L_g e^{-λ R}`. -/
theorem limit_decay [∀ v, Nonempty (ι v)] (ν : Measure S) [IsProbabilityMeasure ν]
    (supp : ∀ v, X v → Finset (ι v)) (Vinf : ∀ v, X v → (ι v → S) → ℝ)
    (hVinf : ∀ v, Potential (supp v) (Vinf v)) (dist : ∀ v, ι v → ι v → ℝ) (hd0 : ∀ v x, dist v x x = 0)
    (htri : ∀ v x y z, dist v x z ≤ dist v x y + dist v y z) {lam : ℝ} (hlam : 0 ≤ lam)
    (hH2 : LimitFlatW supp dist lam Vinf) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v,
      ∀ (f g : (ι v → S) → ℝ) (A Sg : Finset (ι v)) (vf : ι v → ℝ) (Lg R : ℝ),
        BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) →
        (∀ x ∈ A, ∀ y ∈ Sg, R ≤ dist v x y) →
        |∫ σ, f σ * g σ ∂(gibbsMeasure ν (Vinf v)) -
            (∫ σ, f σ ∂(gibbsMeasure ν (Vinf v))) * ∫ σ, g σ ∂(gibbsMeasure ν (Vinf v))| ≤
          C * (∑ x ∈ A, vf x) * Lg * Real.exp (-(lam * R)) := by
  obtain ⟨γ, hγ0, hγ1, Sb, _, hS⟩ := hH2
  refine ⟨(1 - γ)⁻¹, (inv_pos.2 (by linarith)).le, fun v f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR => ?_⟩
  exact decay_of_flatW ν (hVinf v) (hS v).1 (dist v) (hd0 v) (htri v) hlam hγ0 hγ1 (hS v).2 hf hg hfA hgS hvf hLg
    hvg hR

/-- **The gap of the continuum limit, per volume (route A).** Let `μ v k` be the level-`k` block-variable laws (any
measures) that converge, in every volume, to the limit theory on bounded measurable functions (this is what round 2's
W_p with the transport lemma T gives, per volume, without any locality of the level-`k` theory). If the limit theory
is Gibbs for potentials satisfying D′_λ, then in every volume the level-`k` block covariances converge to the limit
covariances, and these decay at the physical rate `λ/L₁` with a constant independent of the volume (blocks of physical
size `L₁`, `R` the physical distance). No robustness lemma and no uniformity in `k` are needed. -/
theorem continuum_decay [∀ v, Nonempty (ι v)] (ν : Measure S) [IsProbabilityMeasure ν]
    (supp : ∀ v, X v → Finset (ι v)) (Vinf : ∀ v, X v → (ι v → S) → ℝ)
    (hVinf : ∀ v, Potential (supp v) (Vinf v)) (dist : ∀ v, ι v → ι v → ℝ) (hd0 : ∀ v x, dist v x x = 0)
    (htri : ∀ v x y z, dist v x z ≤ dist v x y + dist v y z) {lam : ℝ} (hlam : 0 ≤ lam)
    (hH2 : LimitFlatW supp dist lam Vinf) {L₁ : ℝ} (hL₁ : 0 < L₁) (μ : ∀ v, ℕ → Measure (ι v → S))
    (hconv : ∀ v (h : (ι v → S) → ℝ), BM h →
      Tendsto (fun k => ∫ σ, h σ ∂(μ v k)) atTop (𝓝 (∫ σ, h σ ∂(gibbsMeasure ν (Vinf v))))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v,
      ∀ (f g : (ι v → S) → ℝ) (A Sg : Finset (ι v)) (vf : ι v → ℝ) (Lg R : ℝ),
        BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) →
        (∀ x ∈ A, ∀ y ∈ Sg, R ≤ L₁ * dist v x y) →
        Tendsto (fun k => ∫ σ, f σ * g σ ∂(μ v k) - (∫ σ, f σ ∂(μ v k)) * ∫ σ, g σ ∂(μ v k)) atTop
          (𝓝 (∫ σ, f σ * g σ ∂(gibbsMeasure ν (Vinf v)) -
            (∫ σ, f σ ∂(gibbsMeasure ν (Vinf v))) * ∫ σ, g σ ∂(gibbsMeasure ν (Vinf v)))) ∧
        |∫ σ, f σ * g σ ∂(gibbsMeasure ν (Vinf v)) -
            (∫ σ, f σ ∂(gibbsMeasure ν (Vinf v))) * ∫ σ, g σ ∂(gibbsMeasure ν (Vinf v))| ≤
          C * (∑ x ∈ A, vf x) * Lg * Real.exp (-(lam / L₁ * R)) := by
  obtain ⟨C, hC, h⟩ := limit_decay ν supp Vinf hVinf dist hd0 htri hlam hH2
  refine ⟨C, hC, fun v f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR => ⟨?_, ?_⟩⟩
  · exact (hconv v _ (hf.mul hg)).sub ((hconv v f hf).mul (hconv v g hg))
  · have hR' : ∀ x ∈ A, ∀ y ∈ Sg, R / L₁ ≤ dist v x y := fun x hx y hy =>
      (div_le_iff₀ hL₁).2 ((hR x hx y hy).trans_eq (mul_comm _ _))
    have := h v f g A Sg vf Lg (R / L₁) hf hg hfA hgS hvf hLg hvg hR'
    rwa [show lam * (R / L₁) = lam / L₁ * R by ring] at this

end Families

end Attempts.R3
