/-
The one-scale reduction, effective-theory layer: robustness (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/PROOF-NOTE.md`, §1.6 (influence coefficients, H and W forms), §1.7 (GDS);
`docs/mass-gap/weak-coupling/attempts/ROUND-1.md` (why the contraction can only switch on at a physical scale).
-/

import OneScale.Lipschitz

/-!
# Robustness of influence bounds and of GDS under small changes of the specification

Influence bounds and the hypothesis GDS are stable under small perturbations of the block specifications. This is the
glue between the two hypotheses of the effective-theory reduction (`OneScale.Effective.Physical`): if the blocked
specifications `q_k` are close to a limit `q_∞` that satisfies GDS with `γ_∞ < 1`, then `q_k` satisfies GDS with some
`γ < 1`.

**Distances between specifications** (all for one block `B`, uniformly over boundary conditions `σ`; the test functions
are those of the influence coefficients: bounded measurable, depending only on `B`):
* `SpecDist B q q' δ` (H form, uniform): `|q^σ(F) - q'^σ(F)| ≤ δ L` for every `F` with single-coordinate oscillations
  `≤ L` on `B`. This is the dual (Kantorovich) distance for the Hamming metric on block configurations.
* `TVClose B q q' ε`: the total-variation form, `|q^σ(F) - q'^σ(F)| ≤ ε osc(F)`. It implies `SpecDist` with
  `δ = |B| ε` (`specDist_of_tv`).
* `InfluenceDev B q q' z δ` (H form, pairwise): the boundary variations `q^σ - q^{σ^z}` and `q'^σ - q'^{σ^z}` differ by
  at most `δ L` on the same test functions. `SpecDist δ` implies `InfluenceDev (2δ)` (`InfluenceDev.of_specDist`).
* `InfluenceDevW c B q q' z δ` (W form, pairwise): the same with Lipschitz test functions for the cost `c` and the bound
  `δ L c(σ_z, s)`. There is no uniform W analogue of `SpecDist`: a W coefficient measures how fast `q^σ` moves when the
  boundary value moves, so W-closeness is closeness of boundary derivatives (a C¹-type closeness), not of the laws.

**Robustness lemmas.**
* `IsInfluenceBound.of_dev`: `k` for `q` and deviation `δ` give `k + δ` for `q'` (constant 1).
* `IsInfluenceBound.of_specDist`: `k` for `q` and `SpecDist δ` give `k + 2δ` for `q'` (**constant `c = 2`**).
* `IsInfluenceBoundW.of_devW`: W form, `k + δ`.
* `GDS.add`: if the added coefficients satisfy `∑_{j : z ∉ B_j} δ_j(z) ≤ ε c(z)`, then GDS(γ) gives GDS(γ + ε).
* Finite range (`IsLocal`, `shellCoeff`, `influence_shellCoeff`, `gds_shellCoeff`): if `q'_j` depends on the outside
  only through a shell `Sh_j`, and at most `r c(z)` shells contain a site `z` outside their block, then a uniform
  perturbation `η` of the shell coefficients changes GDS(γ) into **GDS(γ + r η)**; with `SpecDist δ`, `η = 2δ`, so
  **GDS(γ) for `q` gives GDS(γ + 2 r δ) for `q'`** (`C = 2r`).

**Standard, new, open.** Stability of Dobrushin-type uniqueness conditions under small perturbations of the
specification is classical: Dobrushin's condition is an open condition on the specification, and Dobrushin–Shlosman's
complete analyticity (1985/87) is an open condition (its equivalent mixing forms are stable under small changes of the
interaction). The lemmas here are the elementary version of that fact for our influence coefficients (H and W, dual
form) and our block hypothesis GDS. New is only the assembly in this framework. Nothing here is open; the open
statements are in `OneScale.Effective.Physical`.
-/

open MeasureTheory Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace OneScale.Effective

variable {ι S : Type*} [DecidableEq ι] [MeasurableSpace S]

/-! ## Distances between block specifications -/

/-- **Uniform dual distance of two block specifications (H form).** For every boundary condition `σ` and every bounded
measurable `F` depending only on `B` with single-coordinate oscillations `≤ L` on `B`:
`|q^σ(F) - q'^σ(F)| ≤ δ L`. (The dual of the Hamming–Wasserstein distance of the block laws.) -/
def SpecDist (B : Finset ι) (q q' : (ι → S) → Measure (ι → S)) (δ : ℝ) : Prop :=
  ∀ (σ : ι → S) (F : (ι → S) → ℝ) (L : ℝ), BM F → DepOn F B →
    (∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L) →
    |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q' σ)| ≤ δ * L

/-- **Total-variation closeness of the block laws.** For every `σ` and every bounded measurable `F` depending only on
`B` with total oscillation `≤ C`: `|q^σ(F) - q'^σ(F)| ≤ ε C`. (For probability measures this says that the block
marginals of `q^σ` and `q'^σ` are at total-variation distance `≤ ε`.) -/
def TVClose (B : Finset ι) (q q' : (ι → S) → Measure (ι → S)) (ε : ℝ) : Prop :=
  ∀ (σ : ι → S) (F : (ι → S) → ℝ) (C : ℝ), BM F → DepOn F B → (∀ ξ ξ', |F ξ - F ξ'| ≤ C) →
    |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q' σ)| ≤ ε * C

/-- **Deviation of the boundary influence (H form, pairwise).** The boundary variations of `q` and `q'` at the outside
coordinate `z` differ by at most `δ L` on the test functions of the influence coefficients:
`|(q'^σ - q'^{σ^z})(F) - (q^σ - q^{σ^z})(F)| ≤ δ L`, where `σ^z` is `σ` with the coordinate `z` changed. -/
def InfluenceDev (B : Finset ι) (q q' : (ι → S) → Measure (ι → S)) (z : ι) (δ : ℝ) : Prop :=
  ∀ (σ : ι → S) (s : S) (F : (ι → S) → ℝ) (L : ℝ), BM F → DepOn F B →
    (∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L) →
    |(∫ ξ, F ξ ∂(q' σ) - ∫ ξ, F ξ ∂(q' (Function.update σ z s))) -
      (∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q (Function.update σ z s)))| ≤ δ * L

/-- **Deviation of the boundary influence (W form, pairwise).** As `InfluenceDev`, with test functions Lipschitz in each
block coordinate for the cost `c` and the bound `δ L c(σ_z, s)`: the boundary derivatives of `q` and `q'` are close. -/
def InfluenceDevW (c : S → S → ℝ) (B : Finset ι) (q q' : (ι → S) → Measure (ι → S)) (z : ι) (δ : ℝ) : Prop :=
  ∀ (σ : ι → S) (s : S) (F : (ι → S) → ℝ) (L : ℝ), BM F → DepOn F B →
    (∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L * c (ξ y) t) →
    |(∫ ξ, F ξ ∂(q' σ) - ∫ ξ, F ξ ∂(q' (Function.update σ z s))) -
      (∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q (Function.update σ z s)))| ≤ δ * L * c (σ z) s

/-! ## One block: robustness of influence bounds -/

/-- **Robustness, H form, pairwise.** If `k` bounds the influence of `z` on `q` and the boundary variations of `q` and
`q'` differ by at most `δ`, then `k + δ` bounds the influence of `z` on `q'`. -/
theorem _root_.OneScale.IsInfluenceBound.of_dev {B : Finset ι} {q q' : (ι → S) → Measure (ι → S)} {z : ι} {k δ : ℝ}
    (hk : IsInfluenceBound B q z k) (hd : InfluenceDev B q q' z δ) : IsInfluenceBound B q' z (k + δ) := by
  intro σ s F L hF hFB hL
  have h1 := hd σ s F L hF hFB hL
  have h2 := hk σ s F L hF hFB hL
  rw [abs_le] at h1 h2 ⊢
  rw [add_mul]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- A uniform distance `δ` gives a boundary-influence deviation `2δ` (triangle inequality at `σ` and at `σ^z`). -/
theorem InfluenceDev.of_specDist {B : Finset ι} {q q' : (ι → S) → Measure (ι → S)} {δ : ℝ}
    (hd : SpecDist B q q' δ) (z : ι) : InfluenceDev B q q' z (2 * δ) := by
  intro σ s F L hF hFB hL
  have h1 := hd σ F L hF hFB hL
  have h2 := hd (Function.update σ z s) F L hF hFB hL
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- **Robustness lemma, H form.** If `k` is an influence bound for `z` on `q` and `SpecDist B q q' δ`, then `k + 2δ` is
an influence bound for `z` on `q'`. The constant is `c = 2`. -/
theorem _root_.OneScale.IsInfluenceBound.of_specDist {B : Finset ι} {q q' : (ι → S) → Measure (ι → S)} {z : ι} {k δ : ℝ}
    (hk : IsInfluenceBound B q z k) (hd : SpecDist B q q' δ) : IsInfluenceBound B q' z (k + 2 * δ) :=
  hk.of_dev (InfluenceDev.of_specDist hd z)

/-- **Total variation controls the dual distance.** If the block laws are `ε`-close in total variation, then
`SpecDist B q q' (|B| ε)`: a function with oscillations `≤ L` in each of the `|B|` block coordinates has total
oscillation `≤ |B| L`. -/
theorem specDist_of_tv {B : Finset ι} {q q' : (ι → S) → Measure (ι → S)} {ε : ℝ} (htv : TVClose B q q' ε) :
    SpecDist B q q' (B.card * ε) := by
  intro σ F L hF hFB hL
  have hv : OscBound F (fun x => if x ∈ B then L else 0) := by
    intro τ x t
    by_cases hx : x ∈ B
    · simp only [hx, ite_true]; exact hL τ x t hx
    · simp only [hx, ite_false]; rw [hFB.update_eq hx τ t, sub_self, abs_zero]
  have hosc : ∀ ξ ξ', |F ξ - F ξ'| ≤ B.card * L := by
    intro ξ ξ'
    have h := hv.abs_sub_splice_le hFB B ξ ξ'
    have he : F (splice B ξ ξ') = F ξ' := hFB _ _ (fun i hi => splice_of_mem hi ξ ξ')
    rw [he, Finset.inter_self, Finset.sum_ite_mem, Finset.inter_self, sum_const, nsmul_eq_mul] at h
    exact h
  calc |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q' σ)| ≤ ε * (B.card * L) := htv σ F _ hF hFB hosc
    _ = B.card * ε * L := by ring

/-- **Robustness lemma, W form, pairwise.** If `k` is a W influence bound for `z` on `q` and the boundary derivatives
of `q` and `q'` differ by at most `δ` (`InfluenceDevW`), then `k + δ` is a W influence bound for `z` on `q'`. -/
theorem _root_.OneScale.IsInfluenceBoundW.of_devW {c : S → S → ℝ} {B : Finset ι}
    {q q' : (ι → S) → Measure (ι → S)} {z : ι} {k δ : ℝ} (hk : IsInfluenceBoundW c B q z k)
    (hd : InfluenceDevW c B q q' z δ) :
    IsInfluenceBoundW c B q' z (k + δ) := by
  intro σ s F L hF hFB hL
  have h1 := hd σ s F L hF hFB hL
  have h2 := hk σ s F L hF hFB hL
  rw [abs_le] at h1 h2 ⊢
  rw [add_mul, add_mul]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ## Finite range -/

/-- The specification `q` depends on the boundary condition only through the coordinates in `Sh` (the shell). -/
def IsLocal (Sh : Finset ι) (q : (ι → S) → Measure (ι → S)) : Prop :=
  ∀ σ σ' : ι → S, (∀ i ∈ Sh, σ i = σ' i) → q σ = q σ'

theorem IsLocal.update_eq {Sh : Finset ι} {q : (ι → S) → Measure (ι → S)} (hq : IsLocal Sh q) {z : ι} (hz : z ∉ Sh)
    (σ : ι → S) (s : S) : q (Function.update σ z s) = q σ :=
  hq _ _ fun _i hi => Function.update_of_ne (ne_of_mem_of_not_mem hi hz) s σ

/-- A coordinate outside the shell has influence `0` (H form). -/
theorem isInfluenceBound_zero_of_local {B Sh : Finset ι} {q : (ι → S) → Measure (ι → S)} (hq : IsLocal Sh q)
    {z : ι} (hz : z ∉ Sh) : IsInfluenceBound B q z 0 := by
  intro σ s F L _ _ _
  rw [hq.update_eq hz σ s, sub_self, abs_zero, zero_mul]

/-- A coordinate outside the shell has influence `0` (W form). -/
theorem isInfluenceBoundW_zero_of_local (c : S → S → ℝ) {B Sh : Finset ι} {q : (ι → S) → Measure (ι → S)}
    (hq : IsLocal Sh q) {z : ι} (hz : z ∉ Sh) : IsInfluenceBoundW c B q z 0 := by
  intro σ s F L _ _ _
  rw [hq.update_eq hz σ s, sub_self, abs_zero, zero_mul, zero_mul]

/-! ## Block families: robustness of GDS -/

variable {J : Type*} [Fintype J]

/-- GDS is monotone in `γ`. -/
theorem _root_.OneScale.GDS.mono {block : J → Finset ι} {k : J → ι → ℝ} {γ γ' : ℝ} (h : GDS block k γ) (hγ : γ ≤ γ') :
    GDS block k γ' :=
  fun z => (h z).trans (mul_le_mul_of_nonneg_right hγ (Nat.cast_nonneg _))

/-- **GDS under added coefficients.** If GDS(γ) holds for `k` and the added coefficients satisfy
`∑_{j : z ∉ B_j} δ_j(z) ≤ ε c(z)`, then GDS(γ + ε) holds for `k + δ`. -/
theorem _root_.OneScale.GDS.add {block : J → Finset ι} {k δ : J → ι → ℝ} {γ ε : ℝ} (h : GDS block k γ)
    (hδ : ∀ z, ∑ j ∈ univ.filter (fun j => z ∉ block j), δ j z ≤ ε * coverage block z) :
    GDS block (fun j z => k j z + δ j z) (γ + ε) := by
  intro z
  rw [sum_add_distrib, add_mul]
  exact add_le_add (h z) (hδ z)

/-- The shell count `#{j : z ∉ B_j, z ∈ Sh_j}`: the number of blocks whose specification `z` can influence. -/
def shellCount (block shell : J → Finset ι) (z : ι) : ℕ :=
  (univ.filter fun j => z ∉ block j ∧ z ∈ shell j).card

/-- The shell coefficients: `κ_j(z) + η` on the shell, `0` off it. -/
def shellCoeff (shell : J → Finset ι) (κ : J → ι → ℝ) (η : ℝ) (j : J) (z : ι) : ℝ :=
  if z ∈ shell j then κ j z + η else 0

theorem shellCoeff_ne_zero {shell : J → Finset ι} {κ : J → ι → ℝ} {η : ℝ} {j : J} {z : ι}
    (h : shellCoeff shell κ η j z ≠ 0) : z ∈ shell j := by
  by_contra hz
  exact h (by simp [shellCoeff, hz])

/-- **Influence bounds for a nearby local specification (H form).** If `κ` are influence bounds for the specifications
`qlim`, the specifications `q` are local with shells `Sh_j`, and `SpecDist (B_j) (qlim_j) (q_j) δ` for every `j`, then
`shellCoeff Sh κ (2δ)` are influence bounds for `q`. -/
theorem influence_shellCoeff {block shell : J → Finset ι} {qlim q : J → (ι → S) → Measure (ι → S)}
    {κ : J → ι → ℝ} (hκ : ∀ j z, z ∉ block j → IsInfluenceBound (block j) (qlim j) z (κ j z))
    (hloc : ∀ j, IsLocal (shell j) (q j)) {δ : ℝ} (hd : ∀ j, SpecDist (block j) (qlim j) (q j) δ) :
    ∀ j z, z ∉ block j → IsInfluenceBound (block j) (q j) z (shellCoeff shell κ (2 * δ) j z) := by
  intro j z hz
  by_cases hs : z ∈ shell j
  · simp only [shellCoeff, hs, ite_true]
    exact (hκ j z hz).of_specDist (hd j)
  · simp only [shellCoeff, hs, ite_false]
    exact isInfluenceBound_zero_of_local (hloc j) hs

/-- **Influence bounds for a nearby local specification (W form).** As `influence_shellCoeff`, with W coefficients and
the boundary-derivative closeness `InfluenceDevW` on the shell: `shellCoeff Sh κ δ` are W influence bounds for `q`. -/
theorem influenceW_shellCoeff (c : S → S → ℝ) {block shell : J → Finset ι}
    {qlim q : J → (ι → S) → Measure (ι → S)} {κ : J → ι → ℝ}
    (hκ : ∀ j z, z ∉ block j → IsInfluenceBoundW c (block j) (qlim j) z (κ j z))
    (hloc : ∀ j, IsLocal (shell j) (q j)) {δ : ℝ}
    (hd : ∀ j z, z ∉ block j → z ∈ shell j → InfluenceDevW c (block j) (qlim j) (q j) z δ) :
    ∀ j z, z ∉ block j → IsInfluenceBoundW c (block j) (q j) z (shellCoeff shell κ δ j z) := by
  intro j z hz
  by_cases hs : z ∈ shell j
  · simp only [shellCoeff, hs, ite_true]
    exact (hκ j z hz).of_devW (hd j z hz hs)
  · simp only [shellCoeff, hs, ite_false]
    exact isInfluenceBoundW_zero_of_local c (hloc j) hs

/-- **Robustness of GDS (finite range).** If GDS(γ) holds for nonnegative coefficients `κ` and every site `z` lies in at
most `r c(z)` shells of blocks not containing it, then GDS(γ + r η) holds for `shellCoeff Sh κ η` (`η ≥ 0`). -/
theorem gds_shellCoeff {block shell : J → Finset ι} {κ : J → ι → ℝ} (hκ0 : ∀ j z, 0 ≤ κ j z) {γ : ℝ}
    (hgds : GDS block κ γ) {r : ℝ} (hr : ∀ z, (shellCount block shell z : ℝ) ≤ r * coverage block z) {η : ℝ}
    (hη : 0 ≤ η) : GDS block (shellCoeff shell κ η) (γ + r * η) := by
  intro z
  set F := univ.filter (fun j => z ∉ block j)
  have e : ∀ j, shellCoeff shell κ η j z =
      (if z ∈ shell j then κ j z else 0) + (if z ∈ shell j then η else 0) := by
    intro j; unfold shellCoeff; split_ifs <;> simp
  rw [sum_congr rfl (fun j _ => e j), sum_add_distrib]
  have h1 : ∑ j ∈ F, (if z ∈ shell j then κ j z else 0) ≤ ∑ j ∈ F, κ j z :=
    sum_le_sum fun j _ => by split_ifs; exacts [le_rfl, hκ0 j z]
  have h2 : ∑ j ∈ F, (if z ∈ shell j then η else 0) = (shellCount block shell z : ℝ) * η := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, filter_filter]
    rfl
  have h3 : (shellCount block shell z : ℝ) * η ≤ r * coverage block z * η :=
    mul_le_mul_of_nonneg_right (hr z) hη
  rw [h2]
  calc ∑ j ∈ F, (if z ∈ shell j then κ j z else 0) + (shellCount block shell z : ℝ) * η
      ≤ γ * coverage block z + r * coverage block z * η := add_le_add (h1.trans (hgds z)) h3
    _ = (γ + r * η) * coverage block z := by ring

end OneScale.Effective
