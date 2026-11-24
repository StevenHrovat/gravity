/-
The one-scale reduction, effective-theory layer: the two open hypotheses and the gap in physical units (2026-11-21).
Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/PROOF-NOTE.md`, §4.1 (Theorem A), §7 (Corollary B);
`docs/mass-gap/weak-coupling/attempts/ROUND-1.md` (the common obstruction); `docs/mass-gap/weak-coupling/SURVEY-LEAN.md`
§4 (the OpenAI construction).
-/

import OneScale.Effective.Reduction
import OneScale.CorollaryB

/-!
# The gap from two hypotheses at one physical scale: (H1) effective convergence and (H2) the one-box bound

**Why this replaces `UniformGDS`.** `OneScale.CorollaryB.UniformGDS` asks for one GDS bound for boxes of physical size
`L₀` at every grid fineness `a_k`, stated for the fine lattice theory. Attempt round 1 (`ROUND-1.md`) found the common
obstruction: below the physical scale where the running coupling is of order one the theory is nearly free, and for the
free field the boundary influence of a box is at least `1` at every box size. The contraction can only switch on at
that physical scale. So we move the contraction to the **blocked effective theory at a fixed physical scale `L₁`** and
split the open problem into two sharper statements:

* **(H1) `EffectiveConvergence` — OPEN.** The block specifications of the effective theory at scale `L₁` converge as
  `a → 0`, uniformly in the boundary condition, in the distance `SpecDist` (H form) or `InfluenceDevW` (W form). This is
  the short-distance (ultraviolet) problem.
* **(H2) `LimitGDS` — OPEN.** The single limiting effective theory satisfies GDS with some `γ_∞ < 1` (the one-box
  bound, a statement about one theory instead of a family).

The **robustness lemma** (`OneScale.Effective.Robust`) glues them: near the limit the blocked theories satisfy GDS with
`γ = (1 + γ_∞)/2 < 1` (`OneScale.Effective.effective_reduction`), so Theorem A gives exponential decay with constants
independent of `a` and of the volume, and in physical units the rate is at least `λ/(2L₁)`.

**Contents.**
* `blockSize L₁ a k = ⌈L₁/a_k⌉ a_k`: the physical size of the blocks at level `k` (`L₁ ≤ s_k < L₁ + a_k`).
* `EffectiveConvergence`, `LimitGDS` (H form) and `EffectiveConvergenceW`, `LimitGDS_W` (W form): the two hypotheses,
  for a family of volumes `v ∈ V` and levels `k ∈ ℕ`, uniform in `v`.
* `effGamma`, `effRate`: the explicit `γ = (1 + γ_∞)/2` and `λ = log(1/γ)/(2 D₁)`, with `γ e^{λ D₁} < 1`.
* **`gap_of_effective`** (H) and **`gap_of_effective_W`** (W): `EffectiveConvergence ∧ LimitGDS` give `m > 0`, `C` and
  `k₀` such that for all `k ≥ k₀` and **all volumes `v`**, block observables at physical distance `R` have covariance
  `≤ C (c₊ ∑ v_a) L_g e^{-m R}`; `m = λ/(2L₁)`.
* `gap_of_effective_fine`: the same for the fine theory's observables that are functions of the block variables.
* `tendsto_physRate`: the physical rate `λ/s_k` at level `k` tends to `λ/L₁`.

**Standard, new, open.** Standard: stability of Dobrushin-type conditions under small perturbations (Dobrushin–Shlosman
complete analyticity is an open condition), Theorem A itself (Dobrushin–Foellmer comparison in block form), and the
idea of controlling a lattice theory through its renormalisation-group effective theory at a fixed physical scale
(Balaban; Gawedzki–Kupiainen; for the O(N) model and for gauge theory in the ultraviolet). New: this assembly in our
framework, with the explicit constants and the volume-uniform statement. Open: (H1) and (H2); nothing here proves them.
"Gap" means the exponential decay rate of covariances of block observables, as in `OneScale.CorollaryB`; the spectral
reading needs Theorem C and reflection positivity of the effective measure (not addressed here).
-/

open MeasureTheory Finset Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace OneScale.Effective

/-! ## Physical block size -/

/-- The physical size of the blocks at level `k`: `s_k = ℓ_k a_k` with `ℓ_k = ⌈L₁/a_k⌉` fine lattice steps
(`OneScale.CorollaryB.side`). Coarse distances are measured in blocks; physical distance = `s_k` × coarse distance. -/
def blockSize (L₁ : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ := (CorollaryB.side L₁ a k : ℝ) * a k

theorem le_blockSize {L₁ : ℝ} {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) (k : ℕ) : L₁ ≤ blockSize L₁ a k := by
  have h : L₁ / a k ≤ (CorollaryB.side L₁ a k : ℝ) := by unfold CorollaryB.side; exact Nat.le_ceil _
  have := mul_le_mul_of_nonneg_right h (ha k).le
  rwa [div_mul_cancel₀ _ (ha k).ne'] at this

theorem blockSize_lt {L₁ : ℝ} (hL₁ : 0 ≤ L₁) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) (k : ℕ) :
    blockSize L₁ a k < L₁ + a k := by
  have h : (CorollaryB.side L₁ a k : ℝ) < L₁ / a k + 1 := by
    unfold CorollaryB.side; exact Nat.ceil_lt_add_one (div_nonneg hL₁ (ha k).le)
  have := mul_lt_mul_of_pos_right h (ha k)
  rwa [add_mul, div_mul_cancel₀ _ (ha k).ne', one_mul] at this

theorem tendsto_blockSize {L₁ : ℝ} (hL₁ : 0 ≤ L₁) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0)) :
    Tendsto (blockSize L₁ a) atTop (𝓝 L₁) := by
  have hhi : Tendsto (fun k => L₁ + a k) atTop (𝓝 L₁) := by simpa using tendsto_const_nhds.add ha0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hhi (le_blockSize ha)
    (fun k => (blockSize_lt hL₁ ha k).le)

/-- **The physical rate at level `k`** is `λ/s_k`; it lies in `(λ/(L₁ + a_k), λ/L₁]` and tends to `λ/L₁`. -/
theorem tendsto_physRate {L₁ : ℝ} (hL₁ : 0 < L₁) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (lam : ℝ) : Tendsto (fun k => lam / blockSize L₁ a k) atTop (𝓝 (lam / L₁)) :=
  tendsto_const_nhds.div (tendsto_blockSize hL₁.le ha ha0) hL₁.ne'

/-! ## The two hypotheses -/

section Hypotheses

variable {V : Type*} {ι : V → Type*} [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)] {S : Type*} [MeasurableSpace S]
  {J : V → Type*} [∀ v, Fintype (J v)]

/-- **Hypothesis (H1), H form: convergence of the blocked effective theory at scale `L₁` — OPEN.**

*Abstract setting.* For each volume `v ∈ V` (a fixed physical volume, cut into cells of physical size `L₁`) the coarse
index set `ι v` is the set of cells, `S` the space of **block variables** (one value per cell), and for each level `k`
(lattice spacing `a_k`) `μ v k` is the **effective measure**: the law of the block variables `Φ_{v,k}(U)` of the fine
configuration `U` under the level-`k` lattice measure. `P v k` is its block specification (blocks `block v j` of cells:
conditional laws of the block variables in a coarse block given those outside). The hypothesis says:
1. the coarse blocks do not depend on `k` (they are blocks of cells of physical size `L₁`);
2. the effective specifications have finite range: they depend on the outside only through the shells `shell v j`;
3. they converge to limit specifications `qlim v j` as `k → ∞`, uniformly in the boundary condition, the block and the
   volume, in the dual distance `SpecDist` (H form): `SpecDist ≤ δ_k → 0`.

*What this means for gauge theory.* The fine theory is lattice Yang–Mills at spacing `a_k` and coupling `β_k`
(asymptotic freedom). The block variables are Balaban-type block averages: averaged link variables of the cells
(parallel transport averaged over the paths of a cell, in a gauge fixed inside each cell, or gauge-covariant smeared
fields), so that `S` is the gauge group or a space of smeared fields. Their law is the renormalisation-group effective
theory after `log₂(L₁/a_k)` blocking steps. (H1) is the **short-distance problem**: control of the RG flow from the
lattice scale `a_k` up to the fixed physical scale `L₁`, where the coupling is small and perturbation theory around the
free field (with large-field estimates) applies. This is the territory of Balaban's ultraviolet stability and of the
OpenAI construction (validated 2026-11-10: a Balaban-style RG map for the marginal terms; smeared correlations converge
along a chosen sequence `a_N → 0` at fixed physical volume; `SURVEY-LEAN.md` §4). Honest differences: (i) the OpenAI
result gives convergence of correlations in the full (periodic) state, while (H1) asks convergence of the conditional
laws **uniformly over all boundary conditions**, which is stronger (large fields on the boundary must be handled);
(ii) exact effective theories are not finite range (Balaban's effective actions have exponentially small nonlocal
tails); item 2 then needs a truncation, or Theorem A with summable tails (`decay_of_dev_H` already handles GDS with
tails; Theorem A in this framework is finite range); (iii) by `ROUND-1.md` the H form of the influence coefficients can
fail where the W form holds, so `EffectiveConvergenceW` is the version to aim for. -/
def EffectiveConvergence {μ : ∀ v, ℕ → Measure (ι v → S)} (P : ∀ v k, BlockSpec (μ v k) (J v))
    (block shell : ∀ v, J v → Finset (ι v)) (qlim : ∀ v, J v → (ι v → S) → Measure (ι v → S)) : Prop :=
  (∀ v k, (P v k).block = block v) ∧
  (∀ v k j, IsLocal (shell v j) ((P v k).spec j)) ∧
  ∃ δ : ℕ → ℝ, (∀ k, 0 ≤ δ k) ∧ Tendsto δ atTop (𝓝 0) ∧
    ∀ v k j, SpecDist (block v j) (qlim v j) ((P v k).spec j) (δ k)

/-- **Hypothesis (H2), H form: the one-box bound for the limit — OPEN.** The limit effective theory `qlim` (at the
physical scale `L₁`) has nonnegative influence bounds satisfying GDS with one `γ_∞ < 1`, in every volume.

This is a statement about **one** theory at **one** scale (where the coupling is of order one), not about a family as
`a → 0`. It is not easier than it looks: GDS is a worst-case statement over boundary conditions, and by `ROUND-1.md`
(lead route) worst-case boundaries cannot be reached from torus estimates without a boundary cost. If the theory has a
gap, GDS for suitable block variables should hold once `L₁` is large compared with the correlation length, so (H2) is a
one-scale reformulation of the gap at the effective level, not a consequence of anything proved here. -/
def LimitGDS (block : ∀ v, J v → Finset (ι v)) (qlim : ∀ v, J v → (ι v → S) → Measure (ι v → S)) : Prop :=
  ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∀ v, ∃ κ : J v → ι v → ℝ, (∀ j z, 0 ≤ κ j z) ∧
    (∀ j z, z ∉ block v j → IsInfluenceBound (block v j) (qlim v j) z (κ j z)) ∧ GDS (block v) κ γ

/-- **Hypothesis (H1), W form — OPEN.** As `EffectiveConvergence`, with closeness of the boundary derivatives
(`InfluenceDevW c ≤ δ_k → 0` for every shell site of every block, uniformly in the volume) in place of `SpecDist`. For
Gibbsian effective specifications this is closeness of the boundary derivatives of the effective Hamiltonians, a
C¹-type convergence of the effective action. This is the form matching the project's open problem (PROOF-NOTE §7). -/
def EffectiveConvergenceW (c : S → S → ℝ) {μ : ∀ v, ℕ → Measure (ι v → S)} (P : ∀ v k, BlockSpec (μ v k) (J v))
    (block shell : ∀ v, J v → Finset (ι v)) (qlim : ∀ v, J v → (ι v → S) → Measure (ι v → S)) : Prop :=
  (∀ v k, (P v k).block = block v) ∧
  (∀ v k j, IsLocal (shell v j) ((P v k).spec j)) ∧
  ∃ δ : ℕ → ℝ, (∀ k, 0 ≤ δ k) ∧ Tendsto δ atTop (𝓝 0) ∧
    ∀ v k j z, z ∉ block v j → z ∈ shell v j → InfluenceDevW c (block v j) (qlim v j) ((P v k).spec j) z (δ k)

/-- **Hypothesis (H2), W form — OPEN.** As `LimitGDS`, with W influence coefficients for the cost `c`. -/
def LimitGDS_W (c : S → S → ℝ) (block : ∀ v, J v → Finset (ι v))
    (qlim : ∀ v, J v → (ι v → S) → Measure (ι v → S)) : Prop :=
  ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∀ v, ∃ κ : J v → ι v → ℝ, (∀ j z, 0 ≤ κ j z) ∧
    (∀ j z, z ∉ block v j → IsInfluenceBoundW c (block v j) (qlim v j) z (κ j z)) ∧ GDS (block v) κ γ

end Hypotheses

/-! ## The explicit constants -/

/-- `γ = (1 + γ_∞)/2`, the GDS constant of the blocked theories near the limit. -/
def effGamma (γlim : ℝ) : ℝ := (1 + γlim) / 2

/-- `λ = log(1/γ)/(2 D₁)` (in coarse units), half the largest rate Theorem A allows. -/
def effRate (γlim D₁ : ℝ) : ℝ := Real.log (1 / effGamma γlim) / (2 * D₁)

theorem effGamma_pos {γlim : ℝ} (hγ0 : 0 ≤ γlim) : 0 < effGamma γlim := by unfold effGamma; linarith

theorem effGamma_lt_one {γlim : ℝ} (hγ1 : γlim < 1) : effGamma γlim < 1 := by unfold effGamma; linarith

theorem effRate_pos {γlim D₁ : ℝ} (hγ0 : 0 ≤ γlim) (hγ1 : γlim < 1) (hD₁ : 0 < D₁) : 0 < effRate γlim D₁ :=
  div_pos (Real.log_pos (one_lt_one_div (effGamma_pos hγ0) (effGamma_lt_one hγ1))) (by linarith)

theorem effRate_cond {γlim D₁ : ℝ} (hγ0 : 0 ≤ γlim) (hγ1 : γlim < 1) (hD₁ : 0 < D₁) :
    effGamma γlim * Real.exp (effRate γlim D₁ * D₁) < 1 := by
  refine CorollaryB.rate_lt_of_lt (effGamma_pos hγ0) hD₁ ?_
  exact div_lt_div_of_pos_left (Real.log_pos (one_lt_one_div (effGamma_pos hγ0) (effGamma_lt_one hγ1))) hD₁
    (by linarith)

/-- From coarse to physical units: `e^{-λ(R/s - D₀)} ≤ e^{λ D₀} e^{-(λ/(2L₁)) R}` for `0 < s ≤ 2L₁`, `R ≥ 0`. -/
theorem exp_phys_le {lam R s L₁ D₀ : ℝ} (hlam : 0 ≤ lam) (hR : 0 ≤ R) (hs : 0 < s) (hsL : s ≤ 2 * L₁) :
    Real.exp (-(lam * (R / s - D₀))) ≤ Real.exp (lam * D₀) * Real.exp (-(lam / (2 * L₁) * R)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h := div_le_div_of_nonneg_left (mul_nonneg hlam hR) hs hsL
  have e1 : lam / (2 * L₁) * R = lam * R / (2 * L₁) := by ring
  have e2 : lam * (R / s - D₀) = lam * R / s - lam * D₀ := by ring
  rw [e2]
  linarith

/-- The common level choice: eventually `γ_∞ + e_k ≤ (1 + γ_∞)/2` and `a_k ≤ L₁`. -/
theorem eventually_level {γlim : ℝ} (hγ1 : γlim < 1) {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) {L₁ : ℝ}
    (hL₁ : 0 < L₁) {a : ℕ → ℝ} (ha0 : Tendsto a atTop (𝓝 0)) :
    ∃ k₀, ∀ k ≥ k₀, γlim + e k ≤ effGamma γlim ∧ a k ≤ L₁ := by
  obtain ⟨k₁, hk₁⟩ := eventually_le_half hγ1 he
  obtain ⟨k₂, hk₂⟩ := eventually_atTop.1 ((tendsto_order.1 ha0).2 _ hL₁)
  exact ⟨max k₁ k₂, fun k hk => ⟨hk₁ k (le_of_max_le_left hk), (hk₂ k (le_of_max_le_right hk)).le⟩⟩

/-! ## The gap in physical units -/

section Gap

variable {V : Type*} {ι : V → Type*} [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)] [∀ v, Nonempty (ι v)]
  {S : Type*} [MeasurableSpace S] {J : V → Type*} [∀ v, Fintype (J v)]

/-- **`gap_of_effective` (H form).** Setting: volumes `v ∈ V`, coarse cells `ι v` with coarse distance `dist v` (in
blocks) and blocks/shells with uniform geometry (`UniformGeometry`, constants independent of `v`), effective measures
`μ v k` with block specifications `P v k` at levels `k` with spacings `a_k → 0`, blocks of physical size
`s_k = ⌈L₁/a_k⌉ a_k`. If (H1) `EffectiveConvergence` and (H2) `LimitGDS` hold, then there are `m > 0`, `C ≥ 0` and `k₀`
such that for every level `k ≥ k₀`, **every volume `v`**, and block observables `f` (depending on `A`, oscillations
`v_a`) and `g` (depending on `S_g`, oscillations `≤ L_g`) at physical distance `≥ R ≥ 0`:
`|μ(fg) - μ(f)μ(g)| ≤ C (c₊ ∑_{a ∈ A} v_a) L_g e^{-m R}`.
Explicitly `m = λ/(2L₁)` and `C = b/(c₋(1 - γ e^{λD₁})) e^{λ D₀}` with `γ = (1 + γ_∞)/2`, `λ = log(1/γ)/(2D₁)`: the
physical decay rate is bounded below uniformly in the lattice spacing and the volume. -/
theorem gap_of_effective {μ : ∀ v, ℕ → Measure (ι v → S)} [∀ v k, IsProbabilityMeasure (μ v k)]
    (P : ∀ v k, BlockSpec (μ v k) (J v)) (block shell : ∀ v, J v → Finset (ι v))
    (qlim : ∀ v, J v → (ι v → S) → Measure (ι v → S)) (dist : ∀ v, ι v → ι v → ℝ) {cmin cmax b : ℕ}
    {D₀ D₁ r : ℝ} (hD₁ : 0 < D₁) (G : ∀ v, UniformGeometry (block v) (shell v) (dist v) cmin cmax b D₀ D₁ r)
    {L₁ : ℝ} (hL₁ : 0 < L₁) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (hyp : EffectiveConvergence P block shell qlim ∧ LimitGDS block qlim) :
    ∃ m : ℝ, 0 < m ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ v,
      ∀ (f g : (ι v → S) → ℝ) (A Sg : Finset (ι v)) (vf : ι v → ℝ) (Lg R : ℝ),
        BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) → 0 ≤ R →
        (∀ x ∈ A, ∀ y ∈ Sg, R ≤ blockSize L₁ a k * dist v x y) →
        |∫ σ, f σ * g σ ∂(μ v k) - (∫ σ, f σ ∂(μ v k)) * ∫ σ, g σ ∂(μ v k)| ≤
          C * (cmax * ∑ x ∈ A, vf x) * Lg * Real.exp (-(m * R)) := by
  obtain ⟨⟨hPb, hloc, δ, hδ0, hδ, hd⟩, γlim, hγ0, hγ1, hlim⟩ := hyp
  set γ := effGamma γlim
  set lam := effRate γlim D₁
  have hlam : 0 < lam := effRate_pos hγ0 hγ1 hD₁
  have hρ : γ * Real.exp (lam * D₁) < 1 := effRate_cond hγ0 hγ1 hD₁
  have hgap : 0 < 1 - γ * Real.exp (lam * D₁) := by linarith
  have he : Tendsto (fun k => r * (2 * δ k)) atTop (𝓝 0) := by simpa using (hδ.const_mul 2).const_mul r
  obtain ⟨k₀, hk₀⟩ := eventually_level hγ1 he hL₁ ha0
  set B0 := b / (cmin * (1 - γ * Real.exp (lam * D₁)))
  have hB0 : 0 ≤ B0 := div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hgap.le)
  refine ⟨lam / (2 * L₁), div_pos hlam (by linarith), B0 * Real.exp (lam * D₀),
    mul_nonneg hB0 (Real.exp_pos _).le, k₀, ?_⟩
  intro k hk v f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR0 hR
  obtain ⟨κ, hκ0, hκ, hgds⟩ := hlim v
  obtain ⟨hγk, hak⟩ := hk₀ k hk
  set s := blockSize L₁ a k
  have hs : 0 < s := hL₁.trans_le (le_blockSize ha k)
  have hsL : s ≤ 2 * L₁ := by have := blockSize_lt hL₁.le ha k; linarith
  have hR' : ∀ x ∈ A, ∀ y ∈ Sg, R / s ≤ dist v x y := fun x hx y hy =>
    (div_le_iff₀ hs).2 ((hR x hx y hy).trans_eq (mul_comm _ _))
  have key := decay_of_specDist (P v k) (hPb v k) (G v) (hloc v k) hκ0 hκ hgds (hδ0 k) (hd v k)
    (effGamma_pos hγ0).le hγk hlam.le hρ hf hg hfA hgS hvf hLg hvg hR'
  obtain ⟨σ₀⟩ := nonempty_of_isProbabilityMeasure (μ v k)
  have hX : 0 ≤ (cmax : ℝ) * ∑ x ∈ A, vf x :=
    mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun x _ => hvf.nonneg σ₀ x)
  refine key.trans ?_
  calc B0 * (cmax * ∑ x ∈ A, vf x) * Lg * Real.exp (-(lam * (R / s - D₀)))
      ≤ B0 * (cmax * ∑ x ∈ A, vf x) * Lg * (Real.exp (lam * D₀) * Real.exp (-(lam / (2 * L₁) * R))) :=
        mul_le_mul_of_nonneg_left (exp_phys_le hlam.le hR0 hs hsL) (mul_nonneg (mul_nonneg hB0 hX) hLg)
    _ = B0 * Real.exp (lam * D₀) * (cmax * ∑ x ∈ A, vf x) * Lg * Real.exp (-(lam / (2 * L₁) * R)) := by ring

/-- **`gap_of_effective_W` (W form).** As `gap_of_effective`, with the W-form hypotheses `EffectiveConvergenceW` and
`LimitGDS_W` for a cost `0 ≤ c ≤ D_c`, and `g` per-coordinate Lipschitz with constant `L_g`; the prefactor gains the
factor `D_c`: `C = b D_c/(c₋(1 - γ e^{λD₁})) e^{λ D₀}`, `m = λ/(2L₁)`. -/
theorem gap_of_effective_W {μ : ∀ v, ℕ → Measure (ι v → S)} [∀ v k, IsProbabilityMeasure (μ v k)]
    (P : ∀ v k, BlockSpec (μ v k) (J v)) {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) {Dc : ℝ}
    (hcD : ∀ a b, c a b ≤ Dc) (block shell : ∀ v, J v → Finset (ι v))
    (qlim : ∀ v, J v → (ι v → S) → Measure (ι v → S)) (dist : ∀ v, ι v → ι v → ℝ) {cmin cmax b : ℕ}
    {D₀ D₁ r : ℝ} (hD₁ : 0 < D₁) (G : ∀ v, UniformGeometry (block v) (shell v) (dist v) cmin cmax b D₀ D₁ r)
    {L₁ : ℝ} (hL₁ : 0 < L₁) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (hyp : EffectiveConvergenceW c P block shell qlim ∧ LimitGDS_W c block qlim) :
    ∃ m : ℝ, 0 < m ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ v,
      ∀ (f g : (ι v → S) → ℝ) (A Sg : Finset (ι v)) (vf : ι v → ℝ) (Lg R : ℝ),
        BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → LipBound c g (fun _ => Lg) → 0 ≤ R →
        (∀ x ∈ A, ∀ y ∈ Sg, R ≤ blockSize L₁ a k * dist v x y) →
        |∫ σ, f σ * g σ ∂(μ v k) - (∫ σ, f σ ∂(μ v k)) * ∫ σ, g σ ∂(μ v k)| ≤
          C * (cmax * ∑ x ∈ A, vf x) * Lg * Real.exp (-(m * R)) := by
  obtain ⟨⟨hPb, hloc, δ, hδ0, hδ, hd⟩, γlim, hγ0, hγ1, hlim⟩ := hyp
  set γ := effGamma γlim
  set lam := effRate γlim D₁
  have hlam : 0 < lam := effRate_pos hγ0 hγ1 hD₁
  have hρ : γ * Real.exp (lam * D₁) < 1 := effRate_cond hγ0 hγ1 hD₁
  have hgap : 0 < 1 - γ * Real.exp (lam * D₁) := by linarith
  have he : Tendsto (fun k => r * δ k) atTop (𝓝 0) := by simpa using hδ.const_mul r
  obtain ⟨k₀, hk₀⟩ := eventually_level hγ1 he hL₁ ha0
  -- `D_c ≥ 0`: with no volume the statement is vacuous; otherwise `S` is inhabited and `0 ≤ c ≤ D_c`
  by_cases hV : Nonempty V
  swap
  · exact ⟨1, one_pos, 0, le_rfl, 0, fun k _ v => (hV ⟨v⟩).elim⟩
  obtain ⟨v₀⟩ := hV
  obtain ⟨σ₀⟩ := nonempty_of_isProbabilityMeasure (μ v₀ 0)
  obtain ⟨x₀⟩ := (inferInstance : Nonempty (ι v₀))
  have hDc : 0 ≤ Dc := (hc0 (σ₀ x₀) (σ₀ x₀)).trans (hcD _ _)
  set B0 := b * Dc / (cmin * (1 - γ * Real.exp (lam * D₁)))
  have hB0 : 0 ≤ B0 :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hDc) (mul_nonneg (Nat.cast_nonneg _) hgap.le)
  refine ⟨lam / (2 * L₁), div_pos hlam (by linarith), B0 * Real.exp (lam * D₀),
    mul_nonneg hB0 (Real.exp_pos _).le, k₀, ?_⟩
  intro k hk v f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR0 hR
  obtain ⟨κ, hκ0, hκ, hgds⟩ := hlim v
  obtain ⟨hγk, hak⟩ := hk₀ k hk
  set s := blockSize L₁ a k
  have hs : 0 < s := hL₁.trans_le (le_blockSize ha k)
  have hsL : s ≤ 2 * L₁ := by have := blockSize_lt hL₁.le ha k; linarith
  have hR' : ∀ x ∈ A, ∀ y ∈ Sg, R / s ≤ dist v x y := fun x hx y hy =>
    (div_le_iff₀ hs).2 ((hR x hx y hy).trans_eq (mul_comm _ _))
  have key := decay_of_devW (P v k) hc0 hcD (hPb v k) (G v) (hloc v k) hκ0 hκ hgds (hδ0 k) (hd v k)
    (effGamma_pos hγ0).le hγk hlam.le hρ hf hg hfA hgS hvf hLg hvg hR'
  obtain ⟨σ₁⟩ := nonempty_of_isProbabilityMeasure (μ v k)
  have hX : 0 ≤ (cmax : ℝ) * ∑ x ∈ A, vf x :=
    mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun x _ => hvf.nonneg σ₁ x)
  refine key.trans ?_
  calc B0 * (cmax * ∑ x ∈ A, vf x) * Lg * Real.exp (-(lam * (R / s - D₀)))
      ≤ B0 * (cmax * ∑ x ∈ A, vf x) * Lg * (Real.exp (lam * D₀) * Real.exp (-(lam / (2 * L₁) * R))) :=
        mul_le_mul_of_nonneg_left (exp_phys_le hlam.le hR0 hs hsL) (mul_nonneg (mul_nonneg hB0 hX) hLg)
    _ = B0 * Real.exp (lam * D₀) * (cmax * ∑ x ∈ A, vf x) * Lg * Real.exp (-(lam / (2 * L₁) * R)) := by ring

/-- **The gap for the fine theory's block observables.** If the effective measures are the laws of the block variables
`Φ v k` under fine lattice measures `ν v k` (`μ v k = (ν v k).map (Φ v k)`), the conclusion of `gap_of_effective`
holds for the fine observables `f ∘ Φ`, `g ∘ Φ`: covariances of functions of the block variables at scale `L₁` decay
at a physical rate bounded below uniformly in the lattice spacing and the volume. -/
theorem gap_of_effective_fine {μ : ∀ v, ℕ → Measure (ι v → S)} [∀ v k, IsProbabilityMeasure (μ v k)]
    (P : ∀ v k, BlockSpec (μ v k) (J v)) (block shell : ∀ v, J v → Finset (ι v))
    (qlim : ∀ v, J v → (ι v → S) → Measure (ι v → S)) (dist : ∀ v, ι v → ι v → ℝ) {cmin cmax b : ℕ}
    {D₀ D₁ r : ℝ} (hD₁ : 0 < D₁) (G : ∀ v, UniformGeometry (block v) (shell v) (dist v) cmin cmax b D₀ D₁ r)
    {L₁ : ℝ} (hL₁ : 0 < L₁) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    {X : V → Type*} [∀ v, MeasurableSpace (X v)] (ν : ∀ v, ℕ → Measure (X v)) (Φ : ∀ v, ℕ → X v → ι v → S)
    (hΦ : ∀ v k, Measurable (Φ v k)) (hμ : ∀ v k, μ v k = (ν v k).map (Φ v k))
    (hyp : EffectiveConvergence P block shell qlim ∧ LimitGDS block qlim) :
    ∃ m : ℝ, 0 < m ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ v,
      ∀ (f g : (ι v → S) → ℝ) (A Sg : Finset (ι v)) (vf : ι v → ℝ) (Lg R : ℝ),
        BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) → 0 ≤ R →
        (∀ x ∈ A, ∀ y ∈ Sg, R ≤ blockSize L₁ a k * dist v x y) →
        |∫ U, f (Φ v k U) * g (Φ v k U) ∂(ν v k) - (∫ U, f (Φ v k U) ∂(ν v k)) * ∫ U, g (Φ v k U) ∂(ν v k)| ≤
          C * (cmax * ∑ x ∈ A, vf x) * Lg * Real.exp (-(m * R)) := by
  obtain ⟨m, hm, C, hC, k₀, h⟩ := gap_of_effective P block shell qlim dist hD₁ G hL₁ ha ha0 hyp
  refine ⟨m, hm, C, hC, k₀, fun k hk v f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR0 hR => ?_⟩
  rw [cov_map (ν v k) (hΦ v k) hf hg, ← hμ v k]
  exact h k hk v f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR0 hR

end Gap

end OneScale.Effective
