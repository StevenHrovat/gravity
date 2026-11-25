/-
The one-scale reduction, Corollary B in the Lipschitz (W) form (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/PROOF-NOTE.md`, §1.5-1.6 (`L_x`, `k^W`), §4.1 (Theorem A, W variant),
§7 (Corollary B.1 and the open problem). Side findings: `weak-coupling/attempts/twist/NOTE.md` (S1) and
`weak-coupling/attempts/admissible/NOTE.md` ("Bookkeeping mismatch").
-/

import OneScale.CubeChain
import OneScale.Lipschitz

/-!
# Corollary B with the W-form hypothesis `UniformGDS_W`

**Why this file exists (a correctness fix of the bookkeeping).** `OneScale.CorollaryB.UniformGDS` states the uniform
one-scale hypothesis with the oscillation (H) form of the influence coefficients (`OneScale.IsInfluenceBound`: test
functions with bounded per-link oscillation, bound `k · L` independent of how far the boundary link moves). The proof
note (§7) states the open problem in the Lipschitz/Wasserstein (W) form (§1.6: test functions Lipschitz in each link for
a bi-invariant metric `ρ`, bound `k^W · L · ρ(σ_z, s)`). The H form contains the "central jump" part of a link's
influence and can fail at fixed physical size where the W form holds (twist NOTE, S1). So the H form is a stronger, and
possibly false, hypothesis; **the open hypothesis of the project is the W form, `UniformGDS_W` below.** The H-form
results (`OneScale.CubeChain.corollaryB_of_uniformGDS`) stay valid as conditional statements, but their hypothesis is
not the one of PROOF-NOTE §7.

**Contents.**
* `OneScale.CorollaryB.UniformGDS_W` — **the open hypothesis of the project** (PROOF-NOTE §7, (OS_k) in the W form):
  same thin cubes of side `ℓ_k = ⌈L₀/a_k⌉`, same `γ` at every level, influence coefficients in the W form
  (`OneScale.IsInfluenceBoundW c`, the definition used by `OneScale.BlockSpec.theoremA_W`) for a cost `c` on the gauge
  group. It is stated, not proved.
* The chain, as in `OneScale.CubeChain`, with Theorem A (W) (`OneScale.BlockSpec.theoremA_W`) in place of Theorem A (H):
  `corr_decay_cubes_W`, `gauge_theoremC_cubes_W`, `gauge_decay_finiteVolume_W`, `levelDecay_of_uniformGDS_W` and
  **`corollaryB_of_uniformGDS_W`**, with the same conclusions as `corollaryB_of_uniformGDS` (decay in physical time at
  rate `log(1/γ)/(L₀ + 2a_k)`, `m_k ≥ log(1/γ)/(L₀ + 2a_k)`, `m_k → log(1/γ)/L₀`).
* The comparison H ⇒ W (`OneScale.IsInfluenceBound.toW`, `OneScale.CorollaryB.uniformGDS_W_of_uniformGDS`): it holds
  only for a cost that is separated (`c a b ≥ δ > 0` for `a ≠ b`), with factor `D_c/δ`; see "H against W" below.

**Assumptions on the cost `c : G → G → ℝ`** (the note's bi-invariant metric `ρ`; the proofs use only these):
`0 ≤ c ≤ D_c` (bounded: `D_c` is the diameter), `c a⁻¹ b⁻¹ = c a b` (invariance under inversion, true for every
bi-invariant metric; it is what the reflection `Θ`, which inverts temporal links, needs), and `c a b > 0` for some
`a, b` (the cost is not identically zero; it makes W coefficients nonnegative, which the restriction to the shell uses).
The triangle inequality and bi-invariance under multiplication are not used.

**Regularity of the observables.** The H chain needs `δ_l(F) ≤ v_l` (oscillation). The W chain needs `F` Lipschitz in
each link for the cost: `|F(U) - F(U with U_l := t)| ≤ w_l · c(U_l, t)` (`OneScale.LipBound c F w`), with `w ≥ 0`,
`∑_l w_l ≤ V` and a uniform constant `w_l ≤ L`. The oscillation bound for the `f`-side of Theorem A follows
(`δ_l ≤ D_c w_l`), so the constant is `cubeConstW = D_c · cubeConst(…, D_c V, L)`. Wilson loops in a unitary
representation are of this kind for the metric `‖g - h‖` on the matrices.

**H against W.** The W bound `|Δ| ≤ k^W L c(σ_z, s)` must vanish as `s → σ_z`, linearly in the cost; the H bound
`|Δ| ≤ k^H · osc` does not, and says nothing about how the block expectation depends on the boundary value for small
moves. So H does not imply W with a factor `D_c` in general: from H one only gets `|Δ| ≤ k^H D_c L`, which is
`≤ (k^H D_c/δ) L c(σ_z, s)` exactly when `c(σ_z, s) ≥ δ` for `s ≠ σ_z`. That is `IsInfluenceBound.toW`. For a finite
gauge group with the discrete metric (`δ = D_c = 1`) the two forms coincide (H is the W form for the discrete metric);
for a compact connected group (`U(1)`, `SU(n)`) every metric of the topology has `inf_{a ≠ b} c(a, b) = 0`, so no such
comparison exists, and H ⇒ W is false in general (an H bound allows the block expectation to depend on the boundary
link non-Lipschitz). The converse fails as well (S1: the H coefficient contains the central jump that the W coefficient
does not see). The two hypotheses are therefore genuinely different, and only `UniformGDS_W` is the note's.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete Positivity
open OneScale.LinkDist OneScale.TimeShift OneScale.Gauge OneScale.CorollaryB

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

/-! ## Abstract layer: nonnegativity of W coefficients and the comparison H ⇒ W -/

namespace OneScale

section Abstract

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S]

/-- A W influence coefficient is nonnegative as soon as the cost takes one positive value (test with `F = 0`). -/
theorem IsInfluenceBoundW.nonneg_of_pos {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) {B : Finset ι}
    {q : (ι → S) → Measure (ι → S)} {z : ι} {k : ℝ} (h : IsInfluenceBoundW c B q z k) {a b : S}
    (hab : 0 < c a b) : 0 ≤ k := by
  have h2 := h (fun _ => a) b (fun _ => 0) 1 (BM.const 0) (fun _ _ _ => rfl)
    (fun ξ y t _ => by simpa using hc0 (ξ y) t)
  have h1 : 0 ≤ k * 1 * c a b := (abs_nonneg _).trans h2
  rw [mul_one] at h1
  by_contra hk
  have := mul_neg_of_neg_of_pos (not_le.1 hk) hab
  linarith

/-- **H ⇒ W for a separated cost.** If `δ ≤ c a b` whenever `a ≠ b` (`δ > 0`) and `0 ≤ c ≤ D_c`, an H-form influence
bound `k` of a nonempty block is a W-form influence bound with coefficient `k · (D_c/δ)`. (Without separation there is no
such implication; see the module docstring.) -/
theorem IsInfluenceBound.toW {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) {δ Dc : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a b, a ≠ b → δ ≤ c a b) (hcD : ∀ a b, c a b ≤ Dc) {B : Finset ι} (hB : B.Nonempty)
    {q : (ι → S) → Measure (ι → S)} {z : ι} {k : ℝ} (h : IsInfluenceBound B q z k) :
    IsInfluenceBoundW c B q z (k * (Dc / δ)) := by
  intro σ s F L hF hdep hL
  obtain ⟨y₀, hy₀⟩ := hB
  have hk : 0 ≤ k := OneScale.CubeChain.IsInfluenceBound.nonneg h σ s
  have hDc : 0 ≤ Dc := (hc0 (σ z) s).trans (hcD _ _)
  have hq : 0 ≤ k * (Dc / δ) := mul_nonneg hk (div_nonneg hDc hδ.le)
  -- `L · c(σ_z, s) ≥ 0` (test the Lipschitz hypothesis at a block link)
  have hP : 0 ≤ L * c (σ z) s := (abs_nonneg _).trans (hL (fun _ => σ z) y₀ s hy₀)
  by_cases hs : s = σ z
  · subst hs
    rw [Function.update_eq_self, sub_self, abs_zero]
    have e : k * (Dc / δ) * L * c (σ z) (σ z) = k * (Dc / δ) * (L * c (σ z) (σ z)) := by ring
    rw [e]
    exact mul_nonneg hq hP
  · have hcs : δ ≤ c (σ z) s := hsep _ _ (Ne.symm hs)
    have hL0 : 0 ≤ L := by
      by_contra h'
      have := mul_neg_of_neg_of_pos (not_le.1 h') (hδ.trans_le hcs)
      linarith
    have hosc : ∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L * Dc := fun ξ y t hy =>
      (hL ξ y t hy).trans (mul_le_mul_of_nonneg_left (hcD _ _) hL0)
    have hH := h σ s F (L * Dc) hF hdep hosc
    have e : k * (L * Dc) = k * (Dc / δ) * L * δ := by field_simp
    rw [e] at hH
    exact hH.trans (mul_le_mul_of_nonneg_left hcs (mul_nonneg hq hL0))

end Abstract

end OneScale

/-! ## The open hypothesis in the W form -/

namespace OneScale.CorollaryB

section HypothesisW

variable {d : ℕ}

/-- **Hypothesis (OS_k), W form — THE OPEN HYPOTHESIS OF THE PROJECT** (PROOF-NOTE §7). At every level `k` (torus
`(ℤ/N_kℤ)^d`, weight `φ_k`, e.g. Wilson at `β_k`), there are W-form influence coefficients `κ_x(z)`
(`OneScale.IsInfluenceBoundW c`: test functions Lipschitz in each block link for the cost `c`, bound
`κ_x(z) · L · c(U_z, s)`) for the thin cubes of side `ℓ_k = ⌈L₀/a_k⌉` (one block per site `x`) satisfying GDS with the
same `γ`. Stated, not proved. This replaces the H form `UniformGDS` as the hypothesis the project aims at: the H form
is stronger in general and may be false at fixed physical size where this one holds (module docstring of
`OneScale.CorollaryBW`). -/
def UniformGDS_W {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [HasHaarProbability G] (n : ℕ) [HasGaugeTrace G n] (c : G → G → ℝ)
    (Nk : ℕ → ℕ) [∀ k, NeZero (Nk k)] (φ : ℕ → ℝ → ℝ) (L₀ γ : ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ∃ κ : FinLatticeSites d (Nk k) → LatticeLink d (Nk k) → ℝ,
    (∀ x z, z ∉ thinCube (side L₀ a k) x →
      IsInfluenceBoundW c (thinCube (side L₀ a k) x)
        (gaugeSpec (G := G) n (φ k) (thinCube (side L₀ a k) x)) z (κ x z)) ∧
    GDS (thinCube (side L₀ a k)) κ γ

/-- **H ⇒ W for a separated cost, uniformly.** If `δ ≤ c a b` for `a ≠ b` (`δ > 0`) and `0 ≤ c ≤ D_c`, the H-form
hypothesis `UniformGDS` with `γ` implies `UniformGDS_W c` with `γ · D_c/δ` (for a finite group with the discrete metric:
`δ = D_c = 1`, the same `γ`). For a compact connected gauge group no `δ > 0` exists and there is no such implication
(module docstring). -/
theorem uniformGDS_W_of_uniformGDS [NeZero d] {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [HasHaarProbability G] {n : ℕ}
    [HasGaugeTrace G n] {c : G → G → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) {δ Dc : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a b, a ≠ b → δ ≤ c a b) (hcD : ∀ a b, c a b ≤ Dc) {Nk : ℕ → ℕ} [∀ k, NeZero (Nk k)]
    {φ : ℕ → ℝ → ℝ} {L₀ γ : ℝ} (hL₀ : 0 < L₀) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k)
    (h : UniformGDS (d := d) (G := G) n Nk φ L₀ γ a) :
    UniformGDS_W (d := d) (G := G) n c Nk φ L₀ (γ * (Dc / δ)) a := by
  intro k
  obtain ⟨κ, hκ, hg⟩ := h k
  have hℓ : 1 ≤ side L₀ a k := Nat.ceil_pos.2 (div_pos hL₀ (ha k))
  refine ⟨fun x z => κ x z * (Dc / δ), fun x z hz => ?_, fun z => ?_⟩
  · have hne : (thinCube (d := d) (N := Nk k) (side L₀ a k) x).Nonempty :=
      ⟨⟨x, 0⟩, OneScale.CubeChain.self_mem_thinCube hℓ ⟨x, 0⟩⟩
    exact (hκ x z hz).toW hc0 hδ hsep hcD hne
  · have hDc : 0 ≤ Dc := (hc0 1 1).trans (hcD _ _)
    calc ∑ j ∈ univ.filter (fun j => z ∉ thinCube (side L₀ a k) j), κ j z * (Dc / δ)
        = (∑ j ∈ univ.filter (fun j => z ∉ thinCube (side L₀ a k) j), κ j z) * (Dc / δ) := by rw [sum_mul]
      _ ≤ (γ * coverage (thinCube (side L₀ a k)) z) * (Dc / δ) :=
          mul_le_mul_of_nonneg_right (hg z) (div_nonneg hDc hδ.le)
      _ = γ * (Dc / δ) * coverage (thinCube (side L₀ a k)) z := by ring

end HypothesisW

end OneScale.CorollaryB

/-! ## The chain for the W form -/

namespace OneScale.CubeChain

variable {d N : ℕ} [NeZero d] [NeZero N]

/-- The constant of Theorem A (W) for the thin-cube family: `D_c · cubeConst d ℓ γ λ (D_c V) L`
(independent of `N`). -/
def cubeConstW (d ℓ : ℕ) (γ lam V L Dc : ℝ) : ℝ := Dc * cubeConst d ℓ γ lam (Dc * V) L

theorem cubeConstW_nonneg {d ℓ : ℕ} {γ lam V L Dc : ℝ} (hD : 0 < 1 - γ * Real.exp (lam * ((ℓ : ℝ) + 1)))
    (hV : 0 ≤ V) (hL : 0 ≤ L) (hDc : 0 ≤ Dc) : 0 ≤ cubeConstW d ℓ γ lam V L Dc :=
  mul_nonneg hDc (cubeConst_nonneg hD (mul_nonneg hDc hV) hL)

section GaugeW

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [HasHaarProbability G] {n : ℕ} [HasGaugeTrace G n]

/-- The trimmed W coefficients are W influence bounds (links off the shell do not influence the block). -/
theorem influence_trim_W {c : G → G → ℝ} {φ : ℝ → ℝ} {J : Type*} {block : J → Finset (LatticeLink d N)}
    {κ : J → LatticeLink d N → ℝ}
    (hκ : ∀ j z, z ∉ block j → IsInfluenceBoundW c (block j) (gaugeSpec (G := G) n φ (block j)) z (κ j z)) :
    ∀ j z, z ∉ block j →
      IsInfluenceBoundW c (block j) (gaugeSpec (G := G) n φ (block j)) z (trim block κ j z) := by
  intro j z hz
  unfold trim
  split_ifs with hs
  · exact hκ j z hz
  · intro U s F L _ _ _
    rw [gaugeSpec_update_of_not_shell hz hs U s, sub_self, abs_zero, zero_mul, zero_mul]

/-- The trimmed W coefficients satisfy GDS whenever the original ones do (the cost takes a positive value). -/
theorem gds_trim_W {c : G → G → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) (hcpos : ∃ a b, 0 < c a b) {φ : ℝ → ℝ} {J : Type*}
    [Fintype J] {block : J → Finset (LatticeLink d N)} {κ : J → LatticeLink d N → ℝ}
    (hκ : ∀ j z, z ∉ block j → IsInfluenceBoundW c (block j) (gaugeSpec (G := G) n φ (block j)) z (κ j z))
    {γ : ℝ} (hgds : GDS block κ γ) : GDS block (trim block κ) γ := by
  obtain ⟨a, b, hab⟩ := hcpos
  intro z
  refine le_trans (sum_le_sum fun j hj => ?_) (hgds z)
  simp only [mem_filter, mem_univ, true_and] at hj
  unfold trim
  split_ifs
  · exact le_rfl
  · exact (hκ j z hj).nonneg_of_pos hc0 hab

/-- An inversion-invariant cost is invariant under the link twist of `Θ`. -/
theorem cost_linkTwist {c : G → G → ℝ} (hinv : ∀ a b, c a⁻¹ b⁻¹ = c a b) (l : LatticeLink d N) (a b : G) :
    c (linkTwist l a) (linkTwist l b) = c a b := by
  unfold linkTwist
  split_ifs
  · exact hinv a b
  · rfl

/-- `F ∘ Θ` is Lipschitz in each link with the same uniform constant as `F` (inversion-invariant cost). -/
theorem lipBound_theta {c : G → G → ℝ} (hinv : ∀ a b, c a⁻¹ b⁻¹ = c a b) {F : GaugeConnection G d N → ℝ} {L : ℝ}
    (hF : LipBound c F (fun _ => L)) : LipBound c (fun U => F (thetaConn U)) (fun _ => L) := by
  intro U x t
  show |F (thetaConn U) - F (thetaConn (Function.update U x t))| ≤ L * c (U x) t
  rw [thetaConn_update]
  have h : |F (thetaConn U) - F (Function.update (thetaConn U) (mirrorLink x) (linkTwist (mirrorLink x) t))| ≤
      L * c (thetaConn U (mirrorLink x)) (linkTwist (mirrorLink x) t) := hF _ _ _
  rw [thetaConn_eq U (mirrorLink x), mirrorLink_involutive x, cost_linkTwist hinv] at h
  exact h

variable [(haarG G).IsInvInvariant]
variable (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)

include hc hU in
/-- **Theorem A (W) on the torus with the thin-cube family, for slab observables.** Cost `0 ≤ c ≤ D_c`,
inversion-invariant, not identically zero. Under W influence bounds `κ` for the thin cubes of side `ℓ ≥ 1` with
GDS(`γ`), and `γ e^{λ(ℓ + 1)} < 1`: for `F` depending on the time slab `[0, s]`, Lipschitz in each link
(`L_l(F) ≤ w_l`, `w ≥ 0`, `∑ w ≤ V`, `w ≤ L`), and `2M + 2s + 2 ≤ N`,
`|Cov_μ(F ∘ S_M, F ∘ Θ)| ≤ C e^{-λ M}`, `C = cubeConstW d ℓ γ λ V L D_c` (independent of `N`). -/
theorem corr_decay_cubes_W {c : G → G → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) {Dc : ℝ} (hcD : ∀ a b, c a b ≤ Dc)
    (hcpos : ∃ a b, 0 < c a b) (hinv : ∀ a b, c a⁻¹ b⁻¹ = c a b)
    {φ : ℝ → ℝ} (hφ : PosWeight n φ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {κ : FinLatticeSites d N → LatticeLink d N → ℝ}
    (hκ : ∀ x z, z ∉ thinCube ℓ x →
      IsInfluenceBoundW c (thinCube ℓ x) (gaugeSpec (G := G) n φ (thinCube ℓ x)) z (κ x z))
    {γ : ℝ} (hγ : 0 ≤ γ) (hgds : GDS (thinCube (d := d) (N := N) ℓ) κ γ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hρ : γ * Real.exp (lam * ((ℓ : ℝ) + 1)) < 1)
    {F : GaugeConnection G d N → ℝ} (hF : BM F) {s : ℕ} (hFs : DepOn F (timeSlab 0 s))
    {w : LatticeLink d N → ℝ} (hw0 : ∀ l, 0 ≤ w l) (hw : LipBound c F w) {V L : ℝ} (hV : ∑ l, w l ≤ V)
    (hL : ∀ l, w l ≤ L) {M : ℕ} (hNM : 2 * M + 2 * s + 2 ≤ N) :
    |corr n φ F M| ≤ cubeConstW d ℓ γ lam V L Dc * Real.exp (-(lam * M)) := by
  have := isProbabilityMeasure_gaugeMeasure (d := d) (N := N) hc hU hφ
  have l₀ : LatticeLink d N := ⟨fun _ => 0, 0⟩
  have : Nonempty (LatticeLink d N) := ⟨l₀⟩
  obtain ⟨g₁, g₂, hg12⟩ := hcpos
  have hDc : 0 ≤ Dc := (hc0 g₁ g₂).trans (hcD _ _)
  have hL0 : 0 ≤ L := (hw0 l₀).trans (hL l₀)
  have hv : OscBound F (fun l => w l * Dc) := hw.oscBound hw0 hcD
  obtain ⟨CF, hCF⟩ := hF.bdd
  set P := gaugeBlockSpec (d := d) (N := N) hc hU hφ (thinCube (d := d) (N := N) ℓ)
  set A := (timeSlab (d := d) (N := N) 0 s).image (shiftLink (M : ZMod N))
  set Sg := (timeSlab (d := d) (N := N) 0 s).image mirrorLink
  have hf : BM (fun U => F (tShift (M : ZMod N) U)) :=
    ⟨hF.meas.comp (measurable_tShift _), ⟨CF, fun U => hCF _⟩⟩
  have hg : BM (fun U => F (thetaConn U)) :=
    ⟨hF.meas.comp measurePreserving_thetaConn.measurable, ⟨CF, fun U => hCF _⟩⟩
  have hfA : DepOn (fun U => F (tShift (M : ZMod N) U)) A := by
    intro U V h
    apply hFs
    intro l hl
    exact h _ (mem_image_of_mem _ hl)
  have hgS : DepOn (fun U => F (thetaConn U)) Sg := by
    intro U V h
    apply hFs
    intro l hl
    have := h _ (mem_image_of_mem _ hl)
    simp only [thetaConn, this]
  have hvf : OscBound (fun U => F (tShift (M : ZMod N) U))
      (fun a => w (shiftLink (-(M : ZMod N)) a) * Dc) := by
    intro U x t
    show |F (tShift (M : ZMod N) U) - F (tShift (M : ZMod N) (Function.update U x t))| ≤ _
    rw [tShift_update]
    exact hv _ _ _
  have hvg : LipBound c (fun U => F (thetaConn U)) (fun _ => L) :=
    lipBound_theta hinv (hw.mono hc0 hL)
  have hR : ∀ a ∈ A, ∀ b ∈ Sg, (M : ℝ) ≤ linkDist a b := by
    intro a ha b hb
    obtain ⟨l, hl, rfl⟩ := mem_image.1 ha
    obtain ⟨l', hl', rfl⟩ := mem_image.1 hb
    exact sep_shift_mirror hNM hl hl'
  have h := P.theoremA_W hc0 hcD (trim (thinCube ℓ) κ) (fun j z hz => influence_trim_W hκ j z hz) hγ
    (gds_trim_W hc0 ⟨g₁, g₂, hg12⟩ hκ hgds)
    (cmin := 1) (cmax := (ℓ + 1) ^ d) (b := d * (ℓ + 1) ^ d) le_rfl
    (fun x => one_le_coverage hℓ x) (fun x => coverage_le ℓ x) (fun j => card_thinCube_le ℓ j)
    linkDist linkDist_self linkDist_triangle (D₀ := (ℓ : ℝ)) (D₁ := (ℓ : ℝ) + 1)
    (fun _ _ hx _ hy => linkDist_le_of_mem_thinCube hx hy)
    (fun _ _ _ _ hy hk => dist_shell_le (shell_of_trim_ne hk) hy)
    hlam hρ hf hg hfA hgS hvf hL0 hvg hR
  have hsumA : ∑ a ∈ A, w (shiftLink (-(M : ZMod N)) a) * Dc ≤ Dc * V := by
    rw [← sum_mul, mul_comm _ Dc]
    refine mul_le_mul_of_nonneg_left ?_ hDc
    calc ∑ a ∈ A, w (shiftLink (-(M : ZMod N)) a) ≤ ∑ a, w (shiftLink (-(M : ZMod N)) a) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun a _ _ => hw0 _)
      _ = ∑ l, w l := Equiv.sum_comp (shiftLinkEquiv (-(M : ZMod N))) w
      _ ≤ V := hV
  have hD : 0 < 1 - γ * Real.exp (lam * ((ℓ : ℝ) + 1)) := by linarith
  have hX : 0 ≤ ((d * (ℓ + 1) ^ d : ℕ) : ℝ) * Dc /
      (((1 : ℕ) : ℝ) * (1 - γ * Real.exp (lam * ((ℓ : ℝ) + 1)))) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hDc) (by rw [Nat.cast_one, one_mul]; exact hD.le)
  have he : Real.exp (-(lam * ((M : ℝ) - ℓ))) = Real.exp (lam * ℓ) * Real.exp (-(lam * M)) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold corr
  refine h.trans ?_
  calc _ ≤ ((d * (ℓ + 1) ^ d : ℕ) : ℝ) * Dc / (((1 : ℕ) : ℝ) * (1 - γ * Real.exp (lam * ((ℓ : ℝ) + 1)))) *
          ((((ℓ + 1) ^ d : ℕ) : ℝ) * (Dc * V)) * L * Real.exp (-(lam * ((M : ℝ) - ℓ))) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_right _ hL0
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsumA (Nat.cast_nonneg _)) hX
    _ = cubeConstW d ℓ γ lam V L Dc * Real.exp (-(lam * M)) := by
        rw [he]; unfold cubeConstW cubeConst; ring

variable (hN : Even N)

include hc hU hN in
/-- **Theorem C (W) on the finite torus under W-GDS for thin cubes.** For `r ≥ 1` and `N ≥ 2^{r+1} m + 2s + 2`:
`H(0) ≥ 0` and `|H(m)| ≤ H(0)^{1 - 2^{-r}} C^{2^{-r}} e^{-λ m}`, `C = cubeConstW d ℓ γ λ V L D_c`. -/
theorem gauge_theoremC_cubes_W {c : G → G → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) {Dc : ℝ} (hcD : ∀ a b, c a b ≤ Dc)
    (hcpos : ∃ a b, 0 < c a b) (hinv : ∀ a b, c a⁻¹ b⁻¹ = c a b)
    {φ : ℝ → ℝ} (hφ : PosWeight n φ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {κ : FinLatticeSites d N → LatticeLink d N → ℝ}
    (hκ : ∀ x z, z ∉ thinCube ℓ x →
      IsInfluenceBoundW c (thinCube ℓ x) (gaugeSpec (G := G) n φ (thinCube ℓ x)) z (κ x z))
    {γ : ℝ} (hγ : 0 ≤ γ) (hgds : GDS (thinCube (d := d) (N := N) ℓ) κ γ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hρ : γ * Real.exp (lam * ((ℓ : ℝ) + 1)) < 1)
    {F : GaugeConnection G d N → ℝ} (hF : BM F) {s : ℕ} (hFs : DepOn F (timeSlab 0 s))
    {w : LatticeLink d N → ℝ} (hw0 : ∀ l, 0 ≤ w l) (hw : LipBound c F w) {V L : ℝ} (hV : ∑ l, w l ≤ V)
    (hL : ∀ l, w l ≤ L) {m r : ℕ} (hr : 1 ≤ r) (hNr : 2 ^ (r + 1) * m + 2 * s + 2 ≤ N) :
    0 ≤ corr n φ F 0 ∧
      |corr n φ F m| ≤ corr n φ F 0 ^ (1 - (1 / 2 : ℝ) ^ r) * cubeConstW d ℓ γ lam V L Dc ^ ((1 / 2 : ℝ) ^ r) *
        Real.exp (-(lam * m)) := by
  have l₀ : LatticeLink d N := ⟨fun _ => 0, 0⟩
  obtain ⟨g₁, g₂, hg12⟩ := hcpos
  have hDc : 0 ≤ Dc := (hc0 g₁ g₂).trans (hcD _ _)
  have hL0 : 0 ≤ L := (hw0 l₀).trans (hL l₀)
  have hV0 : 0 ≤ V := (sum_nonneg fun l _ => hw0 l).trans hV
  have hD : 0 < 1 - γ * Real.exp (lam * ((ℓ : ℝ) + 1)) := by linarith
  set K := 2 ^ (r - 1) * m with hK
  have hpow : 2 ^ (r + 1) * m = 4 * K := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp only [hK, Nat.add_sub_cancel, pow_succ]
    ring
  have hNK : 4 * K + 2 * s + 2 ≤ N := by rw [← hpow]; exact hNr
  have hpos : ∀ j, j ≤ K → LinkDep (fun U => F (tShift (j : ZMod N) U)) (posHalfLinks d N) :=
    fun j hj => linkDep_tShift_of_slab hFs (by omega)
  have hdec := corr_decay_cubes_W hc hU hc0 hcD ⟨g₁, g₂, hg12⟩ hinv hφ hℓ hκ hγ hgds hlam hρ hF hFs hw0 hw hV hL
    (M := 2 ^ r * m) (by rw [show 2 * (2 ^ r * m) = 2 ^ (r + 1) * m by ring]; exact hNr)
  exact torus_theoremC_corr hc hU hN hφ hF hpos hr le_rfl (cubeConstW_nonneg hD hV0 hL0 hDc) hdec

include hc hU hN in
/-- **Finite-volume decay (W), uniform in `N`.** For `r ≥ 1` and every torus with `N ≥ 2^{r+1} m + 2s + 2`:
`|H_N(m)| ≤ (H_N(0) + 2^{-r} C) e^{-λ m}`, `C = cubeConstW d ℓ γ λ V L D_c` independent of `N`. -/
theorem gauge_decay_finiteVolume_W {c : G → G → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) {Dc : ℝ} (hcD : ∀ a b, c a b ≤ Dc)
    (hcpos : ∃ a b, 0 < c a b) (hinv : ∀ a b, c a⁻¹ b⁻¹ = c a b)
    {φ : ℝ → ℝ} (hφ : PosWeight n φ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {κ : FinLatticeSites d N → LatticeLink d N → ℝ}
    (hκ : ∀ x z, z ∉ thinCube ℓ x →
      IsInfluenceBoundW c (thinCube ℓ x) (gaugeSpec (G := G) n φ (thinCube ℓ x)) z (κ x z))
    {γ : ℝ} (hγ : 0 ≤ γ) (hgds : GDS (thinCube (d := d) (N := N) ℓ) κ γ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hρ : γ * Real.exp (lam * ((ℓ : ℝ) + 1)) < 1)
    {F : GaugeConnection G d N → ℝ} (hF : BM F) {s : ℕ} (hFs : DepOn F (timeSlab 0 s))
    {w : LatticeLink d N → ℝ} (hw0 : ∀ l, 0 ≤ w l) (hw : LipBound c F w) {V L : ℝ} (hV : ∑ l, w l ≤ V)
    (hL : ∀ l, w l ≤ L) {m r : ℕ} (hr : 1 ≤ r) (hNr : 2 ^ (r + 1) * m + 2 * s + 2 ≤ N) :
    |corr n φ F m| ≤ (corr n φ F 0 + (1 / 2 : ℝ) ^ r * cubeConstW d ℓ γ lam V L Dc) * Real.exp (-(lam * m)) := by
  obtain ⟨h0, h⟩ := gauge_theoremC_cubes_W hc hU hN hc0 hcD hcpos hinv hφ hℓ hκ hγ hgds hlam hρ hF hFs hw0 hw hV hL
    hr hNr
  have l₀ : LatticeLink d N := ⟨fun _ => 0, 0⟩
  obtain ⟨g₁, g₂, hg12⟩ := hcpos
  have hDc : 0 ≤ Dc := (hc0 g₁ g₂).trans (hcD _ _)
  have hL0 : 0 ≤ L := (hw0 l₀).trans (hL l₀)
  have hV0 : 0 ≤ V := (sum_nonneg fun l _ => hw0 l).trans hV
  have hD : 0 < 1 - γ * Real.exp (lam * ((ℓ : ℝ) + 1)) := by linarith
  have hC := cubeConstW_nonneg (d := d) hD hV0 hL0 hDc
  set q : ℝ := (1 / 2 : ℝ) ^ r
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hy := Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.2 hq1) hq0 h0 hC (by ring)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  nlinarith [mul_nonneg hq0 h0]

end GaugeW

/-! ## Corollary B from `UniformGDS_W` -/

section LevelsW

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [HasHaarProbability G] [(haarG G).IsInvInvariant] {n : ℕ}
  [HasGaugeTrace G n]

variable (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)

include hc hU in
/-- **`UniformGDS_W` gives `LevelDecay`.** As `levelDecay_of_uniformGDS`, with the W-form hypothesis and Lipschitz
observables: cost `0 ≤ c ≤ D_c`, inversion-invariant, not identically zero; at level `k` on torus `j` the observable
`F_{k,j}` is bounded measurable, depends on the time slab `[0, s_k]` and is Lipschitz in each link,
`|F(U) - F(U with U_l := t)| ≤ w_l c(U_l, t)` with `w ≥ 0`, `∑_l w_l ≤ V_k`, `w_l ≤ L_k`. -/
theorem levelDecay_of_uniformGDS_W {c : G → G → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) {Dc : ℝ} (hcD : ∀ a b, c a b ≤ Dc)
    (hcpos : ∃ a b, 0 < c a b) (hinv : ∀ a b, c a⁻¹ b⁻¹ = c a b)
    {L₀ γ : ℝ} (hL₀ : 0 < L₀) (hγ0 : 0 < γ) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k)
    (Ns : ℕ → ℕ → ℕ) [∀ k j, NeZero (Ns k j)] (hEven : ∀ k j, Even (Ns k j))
    (hNs : ∀ k, Tendsto (Ns k) atTop atTop) {φ : ℕ → ℝ → ℝ} (hφ : ∀ k, PosWeight n (φ k))
    (hGDS : ∀ j, UniformGDS_W (d := d) (G := G) n c (fun k => Ns k j) φ L₀ γ a)
    (F : ∀ k j, GaugeConnection G d (Ns k j) → ℝ) (hF : ∀ k j, BM (F k j)) (s : ℕ → ℕ)
    (hFs : ∀ k j, DepOn (F k j) (timeSlab 0 (s k))) (w : ∀ k j, LatticeLink d (Ns k j) → ℝ)
    (hw0 : ∀ k j l, 0 ≤ w k j l) (hw : ∀ k j, LipBound c (F k j) (w k j)) (V L : ℕ → ℝ)
    (hV : ∀ k j, ∑ l, w k j l ≤ V k) (hL : ∀ k j l, w k j l ≤ L k) (h : ℕ → ℕ → ℝ)
    (hlim : ∀ k t, Tendsto (fun j => corr n (φ k) (F k j) t) atTop (𝓝 (h k t))) :
    LevelDecay L₀ γ a h := by
  intro k lam hlam0 hlam t
  have hℓ : 1 ≤ side L₀ a k := Nat.ceil_pos.2 (div_pos hL₀ (ha k))
  have hρ : γ * Real.exp (lam * ((side L₀ a k : ℝ) + 1)) < 1 := rate_lt_of_lt hγ0 (by positivity) hlam
  set C := cubeConstW d (side L₀ a k) γ lam (V k) (L k) Dc
  set E := Real.exp (-(lam * t))
  have hfin : ∀ r : ℕ, 1 ≤ r → ∀ᶠ j in atTop,
      |corr n (φ k) (F k j) t| ≤ (corr n (φ k) (F k j) 0 + (1 / 2 : ℝ) ^ r * C) * E := by
    intro r hr
    filter_upwards [tendsto_atTop.1 (hNs k) (2 ^ (r + 1) * t + 2 * s k + 2)] with j hj
    obtain ⟨κ, hκ, hg⟩ := hGDS j k
    exact gauge_decay_finiteVolume_W hc hU (hEven k j) hc0 hcD hcpos hinv (hφ k) hℓ hκ hγ0.le hg hlam0 hρ
      (hF k j) (hFs k j) (hw0 k j) (hw k j) (hV k j) (hL k j) hr hj
  have hr_bound : ∀ r : ℕ, 1 ≤ r → |h k t| ≤ (h k 0 + (1 / 2 : ℝ) ^ r * C) * E := fun r hr =>
    le_of_tendsto_of_tendsto (hlim k t).abs (((hlim k 0).add_const _).mul_const E) (hfin r hr)
  have hq : Tendsto (fun r : ℕ => (h k 0 + (1 / 2 : ℝ) ^ r * C) * E) atTop (𝓝 ((h k 0 + 0 * C) * E)) :=
    (tendsto_const_nhds.add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const C)).mul_const E
  rw [zero_mul, add_zero] at hq
  exact ge_of_tendsto hq (eventually_atTop.2 ⟨1, fun r hr => hr_bound r hr⟩)

include hc hU in
/-- **Corollary B (lattice part, physical units) with `UniformGDS_W` — the open hypothesis of the project — as the
only open hypothesis.** In the setting of `levelDecay_of_uniformGDS_W`, with `γ < 1` and `a_k → 0`:
1. `|h_k(t)| ≤ h_k(0) · exp(-(log(1/γ)/(L₀ + 2a_k)) · t a_k)` (decay in physical time `t a_k`);
2. `m_k = log(1/γ)/((ℓ_k + 1) a_k) ≥ log(1/γ)/(L₀ + 2a_k)`;
3. `m_k → log(1/γ)/L₀`.
The same conclusions as `corollaryB_of_uniformGDS` (H form); the observables are Lipschitz in each link for the cost
`c` with a uniform constant `L_k`, instead of having bounded oscillations. -/
theorem corollaryB_of_uniformGDS_W {c : G → G → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) {Dc : ℝ} (hcD : ∀ a b, c a b ≤ Dc)
    (hcpos : ∃ a b, 0 < c a b) (hinv : ∀ a b, c a⁻¹ b⁻¹ = c a b)
    {L₀ γ : ℝ} (hL₀ : 0 < L₀) (hγ0 : 0 < γ) (hγ1 : γ < 1) {a : ℕ → ℝ}
    (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (Ns : ℕ → ℕ → ℕ) [∀ k j, NeZero (Ns k j)] (hEven : ∀ k j, Even (Ns k j))
    (hNs : ∀ k, Tendsto (Ns k) atTop atTop) {φ : ℕ → ℝ → ℝ} (hφ : ∀ k, PosWeight n (φ k))
    (hGDS : ∀ j, UniformGDS_W (d := d) (G := G) n c (fun k => Ns k j) φ L₀ γ a)
    (F : ∀ k j, GaugeConnection G d (Ns k j) → ℝ) (hF : ∀ k j, BM (F k j)) (s : ℕ → ℕ)
    (hFs : ∀ k j, DepOn (F k j) (timeSlab 0 (s k))) (w : ∀ k j, LatticeLink d (Ns k j) → ℝ)
    (hw0 : ∀ k j l, 0 ≤ w k j l) (hw : ∀ k j, LipBound c (F k j) (w k j)) (V L : ℕ → ℝ)
    (hV : ∀ k j, ∑ l, w k j l ≤ V k) (hL : ∀ k j l, w k j l ≤ L k) (h : ℕ → ℕ → ℝ)
    (hlim : ∀ k t, Tendsto (fun j => corr n (φ k) (F k j) t) atTop (𝓝 (h k t))) :
    (∀ k t, |h k t| ≤ h k 0 * Real.exp (-(Real.log (1 / γ) / (L₀ + 2 * a k) * (t * a k)))) ∧
    (∀ k, Real.log (1 / γ) / (L₀ + 2 * a k) ≤ physMass L₀ γ a k) ∧
    Tendsto (physMass L₀ γ a) atTop (𝓝 (Real.log (1 / γ) / L₀)) :=
  corollaryB_lattice hL₀ hγ0 hγ1 ha ha0
    (levelDecay_of_uniformGDS_W hc hU hc0 hcD hcpos hinv hL₀ hγ0 ha Ns hEven hNs hφ hGDS F hF s hFs w hw0 hw V L hV
      hL h hlim)

end LevelsW

end OneScale.CubeChain
