/-
The one-scale reduction, effective-theory layer: the reduction theorem (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/PROOF-NOTE.md`, §4.1 (Theorem A, H and W variants);
`docs/mass-gap/weak-coupling/attempts/ROUND-1.md`.
-/

import OneScale.Effective.Robust

/-!
# Effective-theory reduction: GDS for the limit gives uniform decay for the nearby blocked theories

Theorem A (`OneScale.BlockSpec.theoremA_H`, `OneScale.BlockSpec.theoremA_W`) is abstract: it holds for any finite
product space `ι → S` with a block family and block specifications. So it applies verbatim to a **blocked effective
theory**: `ι` the coarse cells (blocks of physical size `L₁`), `S` the space of block variables, `μ` the law of the
block variables, and its block specifications (conditional laws of the block variables in a coarse block given the
outside).

* `UniformGeometry`: the constants Theorem A needs, bundled (coverage `c₋ ≤ c(x) ≤ c₊`, block sizes `≤ b`, a distance
  with block diameters `≤ D₀`, shells within `D₁` of their block, and the shell count `≤ r c(z)`). None depends on the
  number of sites or blocks.
* `decay_of_dev_H` (pairwise form, no locality needed): influence bounds `κ` and GDS(γ_∞) for a specification `q_∞`, and
  boundary-influence deviations `δ_j(z)` of `P` from `q_∞` with `∑_{j : z ∉ B_j} δ_j(z) ≤ ε c(z)`, give Theorem A for
  `P` with `γ = γ_∞ + ε`.
* `decay_of_specDist` (H, uniform distance, finite range): `SpecDist ≤ δ` on every block and `IsLocal` shells give
  Theorem A for `P` with any `γ ≥ γ_∞ + 2 r δ`.
* `decay_of_devW` (W): the same with W coefficients and boundary-derivative closeness `δ` on the shells, any
  `γ ≥ γ_∞ + r δ`.
* `eventually_le_half`: if the perturbation tends to `0`, then eventually `γ_∞ + e_k ≤ (1 + γ_∞)/2 < 1`.
* **`effective_reduction`** (H) and **`effective_reduction_W`** (W): a sequence of block specifications `P_k` on the
  same blocks converging to `q_∞`, with GDS(γ_∞), `γ_∞ < 1`, for `q_∞`: from some `k₀` on, `P_k` satisfies GDS with
  `γ = (1 + γ_∞)/2 < 1`, hence the covariance bound of Theorem A with constants independent of `k` **and of the system
  size** (the constants involve only `γ_∞, c₋, c₊, b, D₀, D₁, λ`; `k₀` depends only on `γ_∞`, `r` and the sequence
  `δ_k`, so it is the same for every system with the same `δ_k`).
* `cov_map`: covariances of functions of the block variables computed under the fine measure equal those under the
  effective measure (its push-forward); so the decay of the effective theory is decay of the fine theory's block
  observables.
-/

open MeasureTheory Finset Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace OneScale.Effective

variable {ι S : Type*} [DecidableEq ι] [MeasurableSpace S] {J : Type*} [Fintype J]

/-- **The geometry constants of Theorem A, bundled.** Coverage between `c₋ ≥ 1` and `c₊`, block sizes `≤ b`, a
distance with `dist x x = 0` and the triangle inequality, block diameters `≤ D₀`, shell sites within `D₁` of every site
of their block, and every site in at most `r c(z)` shells of blocks not containing it. -/
structure UniformGeometry (block shell : J → Finset ι) (dist : ι → ι → ℝ) (cmin cmax b : ℕ) (D₀ D₁ r : ℝ) :
    Prop where
  one_le_cmin : 1 ≤ cmin
  cmin_le : ∀ x, cmin ≤ coverage block x
  le_cmax : ∀ x, coverage block x ≤ cmax
  card_le : ∀ j, (block j).card ≤ b
  dist_self : ∀ x, dist x x = 0
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z
  diam_le : ∀ j, ∀ x ∈ block j, ∀ y ∈ block j, dist x y ≤ D₀
  shell_dist_le : ∀ j x y, x ∈ shell j → x ∉ block j → y ∈ block j → dist x y ≤ D₁
  r_nonneg : 0 ≤ r
  shellCount_le : ∀ z, (shellCount block shell z : ℝ) ≤ r * coverage block z

variable [Fintype ι]

/-! ## One level -/

/-- **Theorem A for a perturbed specification, pairwise form (H).** If `κ` are influence bounds with GDS(γ_∞) for the
specifications `qlim` on the blocks of `P`, and the boundary influences of `P` deviate from those of `qlim` by
`δ_j(z)` with `∑_{j : z ∉ B_j} δ_j(z) ≤ ε c(z)`, then Theorem A holds for `P` with `γ = γ_∞ + ε`. No locality is
needed for GDS; Theorem A's range condition is asked for `κ + δ`. -/
theorem decay_of_dev_H [Nonempty ι] {μ : Measure (ι → S)} [IsProbabilityMeasure μ] (P : BlockSpec μ J)
    {qlim : J → (ι → S) → Measure (ι → S)} {κ δ : J → ι → ℝ}
    (hκ : ∀ j z, z ∉ P.block j → IsInfluenceBound (P.block j) (qlim j) z (κ j z)) {γlim : ℝ}
    (hgds : GDS P.block κ γlim) (hdev : ∀ j z, z ∉ P.block j → InfluenceDev (P.block j) (qlim j) (P.spec j) z (δ j z))
    {ε : ℝ} (hsum : ∀ z, ∑ j ∈ univ.filter (fun j => z ∉ P.block j), δ j z ≤ ε * coverage P.block z)
    (hγ : 0 ≤ γlim + ε) {cmin cmax b : ℕ} (hc1 : 1 ≤ cmin)
    (hcov : ∀ x, cmin ≤ coverage P.block x) (hcmax : ∀ x, coverage P.block x ≤ cmax)
    (hb : ∀ j, (P.block j).card ≤ b)
    (dist : ι → ι → ℝ) (hd0 : ∀ x, dist x x = 0) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    {D₀ D₁ : ℝ} (hD₀ : ∀ j, ∀ x ∈ P.block j, ∀ y ∈ P.block j, dist x y ≤ D₀)
    (hD₁ : ∀ j x y, x ∉ P.block j → y ∈ P.block j → κ j x + δ j x ≠ 0 → dist x y ≤ D₁)
    {lam : ℝ} (hlam : 0 ≤ lam) (hρ : (γlim + ε) * Real.exp (lam * D₁) < 1)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A Sg : Finset ι} (hfA : DepOn f A) (hgS : DepOn g Sg)
    {vf : ι → ℝ} (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : OscBound g (fun _ => Lg))
    {R : ℝ} (hR : ∀ a ∈ A, ∀ s ∈ Sg, R ≤ dist a s) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * ∫ σ, g σ ∂μ| ≤
      b / (cmin * (1 - (γlim + ε) * Real.exp (lam * D₁))) * (cmax * ∑ a ∈ A, vf a) * Lg *
        Real.exp (-(lam * (R - D₀))) :=
  P.theoremA_H (fun j z => κ j z + δ j z) (fun j z hz => (hκ j z hz).of_dev (hdev j z hz)) hγ
    (hgds.add hsum) hc1 hcov hcmax hb dist hd0 htri hD₀ hD₁ hlam hρ hf hg hfA hgS hvf hLg hvg hR

/-- **Theorem A for a nearby local specification (H, uniform distance).** Let `P` be a block specification on the
blocks `block` whose specifications are local with shells `shell`, and `qlim` specifications on the same blocks with
nonnegative influence bounds `κ` satisfying GDS(γ_∞). If `SpecDist (B_j) (qlim_j) (P_j) δ` for every block, then for any
`γ ≥ γ_∞ + r · 2δ` (and `γ e^{λ D₁} < 1`) Theorem A holds for `P`:
`|μ(fg) - μ(f)μ(g)| ≤ b/(c₋(1 - γ e^{λD₁})) · (c₊ ∑_{a ∈ A} v_a) · L_g · e^{-λ(R - D₀)}`. -/
theorem decay_of_specDist [Nonempty ι] {μ : Measure (ι → S)} [IsProbabilityMeasure μ] (P : BlockSpec μ J)
    {block shell : J → Finset ι} (hPb : P.block = block) {dist : ι → ι → ℝ} {cmin cmax b : ℕ} {D₀ D₁ r : ℝ}
    (G : UniformGeometry block shell dist cmin cmax b D₀ D₁ r) (hloc : ∀ j, IsLocal (shell j) (P.spec j))
    {qlim : J → (ι → S) → Measure (ι → S)} {κ : J → ι → ℝ} (hκ0 : ∀ j z, 0 ≤ κ j z)
    (hκ : ∀ j z, z ∉ block j → IsInfluenceBound (block j) (qlim j) z (κ j z)) {γlim : ℝ}
    (hgds : GDS block κ γlim) {δ : ℝ} (hδ0 : 0 ≤ δ) (hd : ∀ j, SpecDist (block j) (qlim j) (P.spec j) δ)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γlim + r * (2 * δ) ≤ γ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hρ : γ * Real.exp (lam * D₁) < 1)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A Sg : Finset ι} (hfA : DepOn f A) (hgS : DepOn g Sg)
    {vf : ι → ℝ} (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : OscBound g (fun _ => Lg))
    {R : ℝ} (hR : ∀ a ∈ A, ∀ s ∈ Sg, R ≤ dist a s) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * ∫ σ, g σ ∂μ| ≤
      b / (cmin * (1 - γ * Real.exp (lam * D₁))) * (cmax * ∑ a ∈ A, vf a) * Lg *
        Real.exp (-(lam * (R - D₀))) := by
  subst hPb
  exact P.theoremA_H (shellCoeff shell κ (2 * δ)) (influence_shellCoeff hκ hloc hd) hγ0
    ((gds_shellCoeff hκ0 hgds G.shellCount_le (by linarith)).mono hγ) G.one_le_cmin G.cmin_le G.le_cmax
    G.card_le dist G.dist_self G.dist_triangle G.diam_le
    (fun j x y hx hy hk => G.shell_dist_le j x y (shellCoeff_ne_zero hk) hx hy) hlam hρ hf hg hfA hgS hvf hLg hvg hR

/-- **Theorem A for a nearby local specification (W).** As `decay_of_specDist`, with W influence bounds `κ` for `qlim`
(cost `0 ≤ c ≤ D_c`), boundary-derivative closeness `InfluenceDevW ≤ δ` on the shells, and `γ ≥ γ_∞ + r δ`; `g` is
per-coordinate Lipschitz with constant `L_g`. The bound is Theorem A (W):
`b D_c/(c₋(1 - γ e^{λD₁})) · (c₊ ∑_{a ∈ A} v_a) · L_g · e^{-λ(R - D₀)}`. -/
theorem decay_of_devW [Nonempty ι] {μ : Measure (ι → S)} [IsProbabilityMeasure μ] (P : BlockSpec μ J)
    {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) {Dc : ℝ} (hcD : ∀ a b, c a b ≤ Dc)
    {block shell : J → Finset ι} (hPb : P.block = block) {dist : ι → ι → ℝ} {cmin cmax b : ℕ} {D₀ D₁ r : ℝ}
    (G : UniformGeometry block shell dist cmin cmax b D₀ D₁ r) (hloc : ∀ j, IsLocal (shell j) (P.spec j))
    {qlim : J → (ι → S) → Measure (ι → S)} {κ : J → ι → ℝ} (hκ0 : ∀ j z, 0 ≤ κ j z)
    (hκ : ∀ j z, z ∉ block j → IsInfluenceBoundW c (block j) (qlim j) z (κ j z)) {γlim : ℝ}
    (hgds : GDS block κ γlim) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hd : ∀ j z, z ∉ block j → z ∈ shell j → InfluenceDevW c (block j) (qlim j) (P.spec j) z δ)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γlim + r * δ ≤ γ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hρ : γ * Real.exp (lam * D₁) < 1)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A Sg : Finset ι} (hfA : DepOn f A) (hgS : DepOn g Sg)
    {vf : ι → ℝ} (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : LipBound c g (fun _ => Lg))
    {R : ℝ} (hR : ∀ a ∈ A, ∀ s ∈ Sg, R ≤ dist a s) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * ∫ σ, g σ ∂μ| ≤
      b * Dc / (cmin * (1 - γ * Real.exp (lam * D₁))) * (cmax * ∑ a ∈ A, vf a) * Lg *
        Real.exp (-(lam * (R - D₀))) := by
  subst hPb
  exact P.theoremA_W hc0 hcD (shellCoeff shell κ δ) (influenceW_shellCoeff c hκ hloc hd) hγ0
    ((gds_shellCoeff hκ0 hgds G.shellCount_le hδ0).mono hγ) G.one_le_cmin G.cmin_le G.le_cmax
    G.card_le dist G.dist_self G.dist_triangle G.diam_le
    (fun j x y hx hy hk => G.shell_dist_le j x y (shellCoeff_ne_zero hk) hx hy) hlam hρ hf hg hfA hgS hvf hLg hvg hR

/-! ## Sequences -/

/-- If the perturbation `e_k` tends to `0` and `γ_∞ < 1`, then eventually `γ_∞ + e_k ≤ (1 + γ_∞)/2`. -/
theorem eventually_le_half {γlim : ℝ} (hγ1 : γlim < 1) {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    ∃ k₀, ∀ k ≥ k₀, γlim + e k ≤ (1 + γlim) / 2 := by
  have hpos : (0 : ℝ) < (1 - γlim) / 2 := by linarith
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 ((tendsto_order.1 he).2 _ hpos)
  exact ⟨k₀, fun k hk => by have := hk₀ k hk; linarith⟩

theorem half_lt_one {γlim : ℝ} (hγ1 : γlim < 1) : (1 + γlim) / 2 < 1 := by linarith

/-- **Effective-theory reduction (H).** Let `P_k` (`k ∈ ℕ`) be block specifications of probability measures `μ_k` on the
same configuration space `ι → S` and the same blocks, local with shells `shell` and with uniform geometry. Let `qlim` be
specifications on these blocks with nonnegative influence bounds `κ` satisfying GDS(γ_∞), `0 ≤ γ_∞ < 1`, and let
`SpecDist (B_j) (qlim_j) (P_k)_j ≤ δ_k → 0`. Then there is `k₀` such that for every `k ≥ k₀`:
1. `P_k` has influence bounds satisfying GDS with `γ = (1 + γ_∞)/2 < 1`;
2. for every `λ ≥ 0` with `γ e^{λ D₁} < 1`, the covariance bound of Theorem A holds for `μ_k` with a constant that does
   not depend on `k` (nor on `ι`, `J`). -/
theorem effective_reduction [Nonempty ι] {μ : ℕ → Measure (ι → S)} [∀ k, IsProbabilityMeasure (μ k)]
    (P : ∀ k, BlockSpec (μ k) J) {block shell : J → Finset ι} (hPb : ∀ k, (P k).block = block)
    {dist : ι → ι → ℝ} {cmin cmax b : ℕ} {D₀ D₁ r : ℝ} (G : UniformGeometry block shell dist cmin cmax b D₀ D₁ r)
    (hloc : ∀ k j, IsLocal (shell j) ((P k).spec j))
    {qlim : J → (ι → S) → Measure (ι → S)} {κ : J → ι → ℝ} (hκ0 : ∀ j z, 0 ≤ κ j z)
    (hκ : ∀ j z, z ∉ block j → IsInfluenceBound (block j) (qlim j) z (κ j z)) {γlim : ℝ}
    (hγ0 : 0 ≤ γlim) (hγ1 : γlim < 1) (hgds : GDS block κ γlim)
    {δ : ℕ → ℝ} (hδ0 : ∀ k, 0 ≤ δ k) (hδ : Tendsto δ atTop (𝓝 0))
    (hd : ∀ k j, SpecDist (block j) (qlim j) ((P k).spec j) (δ k)) :
    ∃ k₀, ∀ k ≥ k₀,
      (∃ κk : J → ι → ℝ, (∀ j z, z ∉ block j → IsInfluenceBound (block j) ((P k).spec j) z (κk j z)) ∧
        GDS block κk ((1 + γlim) / 2)) ∧
      ∀ lam : ℝ, 0 ≤ lam → (1 + γlim) / 2 * Real.exp (lam * D₁) < 1 →
      ∀ (f g : (ι → S) → ℝ) (A Sg : Finset ι) (vf : ι → ℝ) (Lg R : ℝ), BM f → BM g → DepOn f A → DepOn g Sg →
        OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) → (∀ a ∈ A, ∀ s ∈ Sg, R ≤ dist a s) →
        |∫ σ, f σ * g σ ∂(μ k) - (∫ σ, f σ ∂(μ k)) * ∫ σ, g σ ∂(μ k)| ≤
          b / (cmin * (1 - (1 + γlim) / 2 * Real.exp (lam * D₁))) * (cmax * ∑ a ∈ A, vf a) * Lg *
            Real.exp (-(lam * (R - D₀))) := by
  have he : Tendsto (fun k => r * (2 * δ k)) atTop (𝓝 0) := by
    simpa using (hδ.const_mul 2).const_mul r
  obtain ⟨k₀, hk₀⟩ := eventually_le_half hγ1 he
  refine ⟨k₀, fun k hk => ⟨?_, ?_⟩⟩
  · refine ⟨shellCoeff shell κ (2 * δ k), influence_shellCoeff hκ (hloc k) (hd k), ?_⟩
    exact (gds_shellCoeff hκ0 hgds G.shellCount_le (by linarith [hδ0 k])).mono (hk₀ k hk)
  · intro lam hlam hρ f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR
    exact decay_of_specDist (P k) (hPb k) G (hloc k) hκ0 hκ hgds (hδ0 k) (hd k) (by linarith) (hk₀ k hk) hlam hρ
      hf hg hfA hgS hvf hLg hvg hR

/-- **Effective-theory reduction (W).** As `effective_reduction`, with W influence bounds for `qlim` and
boundary-derivative closeness `InfluenceDevW ≤ δ_k → 0` on the shells; `γ = (1 + γ_∞)/2`. -/
theorem effective_reduction_W [Nonempty ι] {μ : ℕ → Measure (ι → S)} [∀ k, IsProbabilityMeasure (μ k)]
    (P : ∀ k, BlockSpec (μ k) J) {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) {Dc : ℝ} (hcD : ∀ a b, c a b ≤ Dc)
    {block shell : J → Finset ι} (hPb : ∀ k, (P k).block = block)
    {dist : ι → ι → ℝ} {cmin cmax b : ℕ} {D₀ D₁ r : ℝ} (G : UniformGeometry block shell dist cmin cmax b D₀ D₁ r)
    (hloc : ∀ k j, IsLocal (shell j) ((P k).spec j))
    {qlim : J → (ι → S) → Measure (ι → S)} {κ : J → ι → ℝ} (hκ0 : ∀ j z, 0 ≤ κ j z)
    (hκ : ∀ j z, z ∉ block j → IsInfluenceBoundW c (block j) (qlim j) z (κ j z)) {γlim : ℝ}
    (hγ0 : 0 ≤ γlim) (hγ1 : γlim < 1) (hgds : GDS block κ γlim)
    {δ : ℕ → ℝ} (hδ0 : ∀ k, 0 ≤ δ k) (hδ : Tendsto δ atTop (𝓝 0))
    (hd : ∀ k j z, z ∉ block j → z ∈ shell j → InfluenceDevW c (block j) (qlim j) ((P k).spec j) z (δ k)) :
    ∃ k₀, ∀ k ≥ k₀,
      (∃ κk : J → ι → ℝ, (∀ j z, z ∉ block j → IsInfluenceBoundW c (block j) ((P k).spec j) z (κk j z)) ∧
        GDS block κk ((1 + γlim) / 2)) ∧
      ∀ lam : ℝ, 0 ≤ lam → (1 + γlim) / 2 * Real.exp (lam * D₁) < 1 →
      ∀ (f g : (ι → S) → ℝ) (A Sg : Finset ι) (vf : ι → ℝ) (Lg R : ℝ), BM f → BM g → DepOn f A → DepOn g Sg →
        OscBound f vf → 0 ≤ Lg → LipBound c g (fun _ => Lg) → (∀ a ∈ A, ∀ s ∈ Sg, R ≤ dist a s) →
        |∫ σ, f σ * g σ ∂(μ k) - (∫ σ, f σ ∂(μ k)) * ∫ σ, g σ ∂(μ k)| ≤
          b * Dc / (cmin * (1 - (1 + γlim) / 2 * Real.exp (lam * D₁))) * (cmax * ∑ a ∈ A, vf a) * Lg *
            Real.exp (-(lam * (R - D₀))) := by
  have he : Tendsto (fun k => r * δ k) atTop (𝓝 0) := by
    simpa using hδ.const_mul r
  obtain ⟨k₀, hk₀⟩ := eventually_le_half hγ1 he
  refine ⟨k₀, fun k hk => ⟨?_, ?_⟩⟩
  · refine ⟨shellCoeff shell κ (δ k), influenceW_shellCoeff c hκ (hloc k) (hd k), ?_⟩
    exact (gds_shellCoeff hκ0 hgds G.shellCount_le (hδ0 k)).mono (hk₀ k hk)
  · intro lam hlam hρ f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR
    exact decay_of_devW (P k) hc0 hcD (hPb k) G (hloc k) hκ0 hκ hgds (hδ0 k) (hd k) (by linarith) (hk₀ k hk)
      hlam hρ hf hg hfA hgS hvf hLg hvg hR

/-! ## Block observables of the fine theory -/

/-- **Covariances of block observables.** If the effective measure is the law of the block variables `Φ` under the fine
measure `ν`, covariances of functions of the block variables are the same under both. -/
theorem cov_map {X : Type*} [MeasurableSpace X] (ν : Measure X) {Φ : X → ι → S} (hΦ : Measurable Φ)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) :
    ∫ x, f (Φ x) * g (Φ x) ∂ν - (∫ x, f (Φ x) ∂ν) * ∫ x, g (Φ x) ∂ν =
      ∫ σ, f σ * g σ ∂(ν.map Φ) - (∫ σ, f σ ∂(ν.map Φ)) * ∫ σ, g σ ∂(ν.map Φ) := by
  rw [integral_map (f := fun σ => f σ * g σ) hΦ.aemeasurable (hf.meas.mul hg.meas).aestronglyMeasurable,
    integral_map hΦ.aemeasurable hf.meas.aestronglyMeasurable,
    integral_map hΦ.aemeasurable hg.meas.aestronglyMeasurable]

end OneScale.Effective
