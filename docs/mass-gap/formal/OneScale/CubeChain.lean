/-
The one-scale reduction, the chain `UniformGDS` → `LevelDecay` → Corollary B (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/PROOF-NOTE.md`, §1.7 (cube families), §4.1 (Theorem A), §4.2 (torus
instance), §6.4 (Theorem C), §6.5 (Corollary C1), §7 (Corollary B).
-/

import OneScale.TimeShift
import OneScale.CorollaryB

/-!
# From the open hypothesis `UniformGDS` to the physical-units decay statement

This file closes the formal chain of Corollary B (lattice part) for the H form; the W form, the project's open hypothesis, has the same chain in `OneScale/CorollaryBW.lean`. Here the only open hypothesis is
`OneScale.CorollaryB.UniformGDS` (GDS for thin cubes of side `ℓ_k = ⌈L₀/a_k⌉` at every level `k`), required here on
every torus of a sequence `N_{k,j} → ∞` (`j ∈ ℕ`) at each level.

**Thin cubes on the torus.**
* `one_le_coverage`, `coverage_le`, `card_thinCube_le`: every link lies in at least one and at most `(ℓ + 1)^d` thin
  cubes, and a thin cube has at most `d (ℓ + 1)^d` links (crude, but independent of `N`; the constant of Theorem A
  disappears in Theorem C, so its size does not matter).
* `linkDist_le_of_mem_thinCube`: thin cubes have diameter `≤ ℓ` (`D₀ = ℓ`) for `OneScale.LinkDist.linkDist`.
* `InShell`, `trim`: the shell of a block (links in a plaquette touching it) and the influence coefficients restricted
  to it. A link outside the shell does not influence the block specification (`gaugeSpec_update_of_not_shell`), so
  `trim κ` is still an influence bound (`influence_trim`) and still satisfies GDS (`gds_trim`); shell links are within
  distance `ℓ + 1` of every cube link (`dist_shell_le`, `D₁ = ℓ + 1`, as in the note).

**Theorem A for slab observables** (`corr_decay_cubes`): Theorem A (`OneScale.BlockSpec.theoremA_H`) with the block
family of all thin-cube translates, applied to `f = F ∘ S_M` and `g = F ∘ Θ` for an observable `F` of the time slab
`[0, s]`: `|Cov(F_M, F ∘ Θ)| ≤ C e^{-λ M}` whenever `2M + 2s + 2 ≤ N`, with `C = cubeConst` independent of `N`.

**Theorem C on the finite torus** (`gauge_theoremC_cubes`) and its finite-volume, prefactor-free form
(`gauge_decay_finiteVolume`): for `r ≥ 1` and `N ≥ 2^{r+1} m + 2s + 2`,
`|H_N(m)| ≤ (H_N(0) + 2^{-r} C) e^{-λ m}` (by `x^{1-q} y^q ≤ (1-q)x + qy`). This is uniform in `N`, and the error
`2^{-r} C` can be made as small as wanted by taking the torus large.

**Corollary B** (`levelDecay_of_uniformGDS`, `corollaryB_of_uniformGDS`): if `h_k(t)` is the limit of the torus
correlations `H_{N_{k,j}}(t)` as `j → ∞` (for slab observables with uniformly bounded oscillations), then
`LevelDecay` holds, and with it the physical-units conclusions of `OneScale.CorollaryB.corollaryB_lattice`.

**What changed relative to the proof note.**
1. No infinite-volume limit states (note Lemma 6.3) are used: the limits are limits of real numbers (the correlation
   values), and `gauge_decay_finiteVolume` is a finite-volume statement with no limit at all. The limits `h_k(t)` are a
   hypothesis `hlim` (they exist along subsequences by Bolzano–Weierstrass, which is not formalised here).
2. The note's hypothesis (OS_k) is GDS on `ℤ^d`; the formal hypothesis is `UniformGDS` on each torus of the sequence
   (`∀ j, UniformGDS n (fun k => N_{k,j}) …`). On `ℤ^d` the former implies the latter for `N ≥ ℓ_k + 3` (note §1.7);
   that transfer is not formalised.
3. The observable at level `k` may vary with the torus; what is needed is a time slab `[0, s_k]` (base times of links)
   and uniform bounds `∑_l δ_l(F) ≤ V_k`, `δ_l(F) ≤ L_k` (for example the same local observable on every torus).
4. "Gap" means the exponential decay rate of the reflected connected correlations, as in `CorollaryB`; the spectral
   statement (note Theorem C2, transfer matrix) is not formalised.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete Positivity
open OneScale.LinkDist OneScale.TimeShift OneScale.Gauge OneScale.CorollaryB

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace OneScale.CubeChain

variable {d N : ℕ} [NeZero d] [NeZero N]

/-! ## Thin cubes: counting and diameter -/

theorem mem_thinCube {ℓ : ℕ} {x : FinLatticeSites d N} {l : LatticeLink d N} :
    l ∈ thinCube ℓ x ↔ ∀ i, (l.site i - x i).val ≤ ℓ ∧ (l.target i - x i).val ≤ ℓ := by
  simp [thinCube]

theorem self_mem_thinCube {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (l : LatticeLink d N) : l ∈ thinCube ℓ l.site := by
  rw [mem_thinCube]
  intro i
  refine ⟨by simp, ?_⟩
  simp only [LatticeLink.target, siteShift, Function.update_apply]
  split_ifs with h
  · subst h
    rw [add_sub_cancel_left, ZMod.val_one_eq_one_mod]
    exact (Nat.mod_le 1 N).trans hℓ
  · simp

/-- Every link lies in at least one thin cube (`ℓ ≥ 1`). -/
theorem one_le_coverage {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (z : LatticeLink d N) :
    1 ≤ coverage (thinCube (d := d) (N := N) ℓ) z := by
  unfold coverage
  exact Finset.card_pos.2 ⟨z.site, by simp only [mem_filter, mem_univ, true_and]; exact self_mem_thinCube hℓ z⟩

/-- Every link lies in at most `(ℓ + 1)^d` thin cubes. -/
theorem coverage_le (ℓ : ℕ) (z : LatticeLink d N) : coverage (thinCube (d := d) (N := N) ℓ) z ≤ (ℓ + 1) ^ d := by
  unfold coverage
  have h : (univ.filter fun x => z ∈ thinCube (d := d) (N := N) ℓ x).card ≤
      (univ : Finset (Fin d → Fin (ℓ + 1))).card := by
    refine card_le_card_of_injOn
      (fun x i => ⟨min ((z.site i - x i).val) ℓ, Nat.lt_succ_of_le (min_le_right _ _)⟩)
      (fun _ _ => mem_coe.2 (mem_univ _)) ?_
    intro x hx y hy hxy
    rw [mem_coe] at hx hy
    funext i
    have h1 := ((mem_thinCube.1 (mem_filter.1 hx).2) i).1
    have h2 := ((mem_thinCube.1 (mem_filter.1 hy).2) i).1
    have h3 := congrFun hxy i
    simp only [Fin.mk.injEq, min_eq_left h1, min_eq_left h2] at h3
    exact sub_right_injective (ZMod.val_injective N h3)
  simpa using h

/-- A thin cube has at most `d (ℓ + 1)^d` links. -/
theorem card_thinCube_le (ℓ : ℕ) (x : FinLatticeSites d N) : (thinCube ℓ x).card ≤ d * (ℓ + 1) ^ d := by
  have h : (thinCube ℓ x).card ≤ (univ : Finset (Fin d × (Fin d → Fin (ℓ + 1)))).card := by
    refine card_le_card_of_injOn
      (fun l => (l.dir, fun i => ⟨min ((l.site i - x i).val) ℓ, Nat.lt_succ_of_le (min_le_right _ _)⟩))
      (fun _ _ => mem_coe.2 (mem_univ _)) ?_
    intro l hl l' hl' hll
    rw [mem_coe] at hl hl'
    simp only [Prod.mk.injEq] at hll
    obtain ⟨hdir, hsite⟩ := hll
    have hs : l.site = l'.site := by
      funext i
      have h1 := ((mem_thinCube.1 hl) i).1
      have h2 := ((mem_thinCube.1 hl') i).1
      have h3 := congrFun hsite i
      simp only [Fin.mk.injEq, min_eq_left h1, min_eq_left h2] at h3
      exact sub_left_injective (ZMod.val_injective N h3)
    rcases l with ⟨s, μ⟩
    rcases l' with ⟨s', μ'⟩
    simp only at hdir hs
    rw [hs, hdir]
  simpa [Fintype.card_prod] using h

/-- Thin cubes have diameter at most `ℓ` (`D₀ = ℓ`). -/
theorem linkDist_le_of_mem_thinCube {ℓ : ℕ} {x : FinLatticeSites d N} {l l' : LatticeLink d N}
    (hl : l ∈ thinCube ℓ x) (hl' : l' ∈ thinCube ℓ x) : linkDist l l' ≤ ℓ := by
  unfold linkDist
  have : siteDist l.site l'.site ≤ ℓ := siteDist_le fun i => by
    have e : l.site i - l'.site i = (l.site i - x i) - (l'.site i - x i) := by ring
    rw [e]
    exact cyc_sub_le_of_val_le ((mem_thinCube.1 hl i).1) ((mem_thinCube.1 hl' i).1)
  exact_mod_cast this

/-! ## Shells and trimmed influence coefficients -/

/-- `z` lies in the shell of `B`: in a plaquette that has a link in `B`. -/
def InShell (B : Finset (LatticeLink d N)) (z : LatticeLink d N) : Prop :=
  ∃ p : LatticePlaquette d N, z ∈ plaqLinks p ∧ ∃ y ∈ B, y ∈ plaqLinks p

/-- Influence coefficients restricted to the shell (`0` off the shell). -/
def trim {J : Type*} (block : J → Finset (LatticeLink d N)) (κ : J → LatticeLink d N → ℝ) (j : J)
    (z : LatticeLink d N) : ℝ :=
  if InShell (block j) z then κ j z else 0

theorem shell_of_trim_ne {J : Type*} {block : J → Finset (LatticeLink d N)} {κ : J → LatticeLink d N → ℝ} {j : J}
    {z : LatticeLink d N} (h : trim block κ j z ≠ 0) : InShell (block j) z := by
  unfold trim at h
  split_ifs at h with hs
  · exact hs
  · exact absurd rfl h

/-- Shell links are within distance `ℓ + 1` of every link of a thin cube (`D₁ = ℓ + 1`). -/
theorem dist_shell_le {ℓ : ℕ} {x : FinLatticeSites d N} {z y : LatticeLink d N} (hz : InShell (thinCube ℓ x) z)
    (hy : y ∈ thinCube ℓ x) : linkDist z y ≤ (ℓ : ℝ) + 1 := by
  obtain ⟨p, hzp, y₀, hy₀, hy₀p⟩ := hz
  have h1 := linkDist_le_one_of_plaq hy₀p hzp
  have h2 := linkDist_le_of_mem_thinCube hy₀ hy
  linarith [linkDist_triangle z y₀ y]

/-- An influence bound is nonnegative (test with `F = 0`). -/
theorem IsInfluenceBound.nonneg {ι S : Type*} [DecidableEq ι] [MeasurableSpace S] {B : Finset ι}
    {q : (ι → S) → Measure (ι → S)} {z : ι} {k : ℝ} (h : IsInfluenceBound B q z k) (σ : ι → S) (s : S) : 0 ≤ k := by
  have := h σ s (fun _ => 0) 1 (BM.const 0) (fun _ _ _ => rfl) (fun _ _ _ _ => by simp)
  simpa using this

section Gauge

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [HasHaarProbability G] {n : ℕ} [HasGaugeTrace G n]

/-- A link outside a block and its shell does not influence the block specification. -/
theorem gaugeSpec_update_of_not_shell {φ : ℝ → ℝ} {B : Finset (LatticeLink d N)} {z : LatticeLink d N}
    (hzB : z ∉ B) (hz : ¬InShell B z) (U : GaugeConnection G d N) (s : G) :
    gaugeSpec n φ B (Function.update U z s) = gaugeSpec n φ B U := by
  have hW : ∀ ξ, plaqProd n φ (touching B) (splice B (Function.update U z s) ξ) =
      plaqProd n φ (touching B) (splice B U ξ) := by
    intro ξ
    rw [splice_update_left hzB]
    unfold plaqProd
    refine prod_congr rfl fun p hp => ?_
    have hzp : z ∉ plaqLinks p := by
      intro hzp
      apply hz
      simp only [touching, mem_filter, mem_univ, true_and] at hp
      obtain ⟨l, hl, hlB⟩ := hp
      exact ⟨p, hzp, l, hlB, hl⟩
    congr 1
    unfold xp
    congr 1
    refine plaquetteHolonomy_dependsOn p _ _ fun l hl => ?_
    have : l ≠ z := fun h => hzp (h ▸ hl)
    simp [Function.update_of_ne this]
  unfold gaugeSpec locSpec locZ
  simp_rw [hW]

/-- The trimmed coefficients are influence bounds. -/
theorem influence_trim {φ : ℝ → ℝ} {J : Type*} {block : J → Finset (LatticeLink d N)} {κ : J → LatticeLink d N → ℝ}
    (hκ : ∀ j z, z ∉ block j → IsInfluenceBound (block j) (gaugeSpec (G := G) n φ (block j)) z (κ j z)) :
    ∀ j z, z ∉ block j → IsInfluenceBound (block j) (gaugeSpec (G := G) n φ (block j)) z (trim block κ j z) := by
  intro j z hz
  unfold trim
  split_ifs with hs
  · exact hκ j z hz
  · intro U s F L _ _ _
    rw [gaugeSpec_update_of_not_shell hz hs U s, sub_self, abs_zero, zero_mul]

/-- The trimmed coefficients satisfy GDS whenever the original ones do. -/
theorem gds_trim {φ : ℝ → ℝ} {J : Type*} [Fintype J] {block : J → Finset (LatticeLink d N)}
    {κ : J → LatticeLink d N → ℝ}
    (hκ : ∀ j z, z ∉ block j → IsInfluenceBound (block j) (gaugeSpec (G := G) n φ (block j)) z (κ j z))
    {γ : ℝ} (hgds : GDS block κ γ) : GDS block (trim block κ) γ := by
  intro z
  refine le_trans (sum_le_sum fun j hj => ?_) (hgds z)
  simp only [mem_filter, mem_univ, true_and] at hj
  unfold trim
  split_ifs
  · exact le_rfl
  · exact IsInfluenceBound.nonneg (hκ j z hj) (fun _ => 1) 1

/-! ## Translation and reflection of single-link updates -/

theorem tShift_update (j : ZMod N) (U : GaugeConnection G d N) (x : LatticeLink d N) (t : G) :
    tShift j (Function.update U x t) = Function.update (tShift j U) (shiftLink (-j) x) t := by
  funext l
  simp only [tShift, Function.update_apply]
  have hiff : shiftLink j l = x ↔ l = shiftLink (-j) x := by
    constructor
    · rintro rfl; simp [shiftLink_add, shiftLink_zero]
    · rintro rfl; simp [shiftLink_add, shiftLink_zero]
  simp only [hiff]

theorem thetaConn_update (U : GaugeConnection G d N) (x : LatticeLink d N) (t : G) :
    thetaConn (Function.update U x t) = Function.update (thetaConn U) (mirrorLink x) (linkTwist (mirrorLink x) t) := by
  funext l
  rw [thetaConn_eq]
  by_cases h : l = mirrorLink x
  · subst h
    rw [mirrorLink_involutive x]
    simp
  · have hne : mirrorLink l ≠ x := fun h' => h (by rw [← h', mirrorLink_involutive])
    rw [Function.update_of_ne hne, Function.update_of_ne h, thetaConn_eq]

/-! ## Slab separation for `F ∘ S_M` against `F ∘ Θ` -/

/-- Links of the slab `[0, s]` translated by `M`, against mirrored links of the slab: distance `≥ M` when
`2M + 2s + 2 ≤ N`. -/
theorem sep_shift_mirror {s M : ℕ} (hN : 2 * M + 2 * s + 2 ≤ N) {l l' : LatticeLink d N} (hl : l ∈ timeSlab 0 s)
    (hl' : l' ∈ timeSlab 0 s) : (M : ℝ) ≤ linkDist (shiftLink (M : ZMod N) l) (mirrorLink l') := by
  rw [linkDist_symm]
  rw [mem_timeSlab] at hl hl'
  have key : ∃ w : ℕ, M ≤ w ∧ w ≤ M + 2 * s + 1 ∧
      (shiftLink (M : ZMod N) l).site 0 - (mirrorLink l').site 0 = (w : ZMod N) := by
    by_cases hd : l'.dir = 0
    · refine ⟨(l.site 0).val + M + (l'.site 0).val + 1, by omega, by omega, ?_⟩
      simp only [shiftLink, shiftSite_zero_coord, mirrorLink, hd, ↓reduceIte, tflipSite_zero]
      push_cast [ZMod.natCast_zmod_val]
      ring
    · refine ⟨(l.site 0).val + M + (l'.site 0).val, by omega, by omega, ?_⟩
      simp only [shiftLink, shiftSite_zero_coord, mirrorLink, hd, ↓reduceIte, reflSite_zero]
      push_cast [ZMod.natCast_zmod_val]
      ring
  obtain ⟨w, hw1, hw2, hw⟩ := key
  have hwN : w < N := by omega
  apply le_linkDist_of_time
  · rw [hw, ZMod.val_cast_of_lt hwN]; exact hw1
  · rw [hw, ZMod.val_cast_of_lt hwN]; omega

/-! ## Theorem A for slab observables, thin-cube blocks -/

/-- The constant of Theorem A for the thin-cube family (independent of `N`). -/
def cubeConst (d ℓ : ℕ) (γ lam V L : ℝ) : ℝ :=
  ((d * (ℓ + 1) ^ d : ℕ) : ℝ) / (((1 : ℕ) : ℝ) * (1 - γ * Real.exp (lam * ((ℓ : ℝ) + 1)))) *
    ((((ℓ + 1) ^ d : ℕ) : ℝ) * V) * L * Real.exp (lam * ℓ)

theorem cubeConst_nonneg {d ℓ : ℕ} {γ lam V L : ℝ} (hD : 0 < 1 - γ * Real.exp (lam * ((ℓ : ℝ) + 1)))
    (hV : 0 ≤ V) (hL : 0 ≤ L) : 0 ≤ cubeConst d ℓ γ lam V L := by
  unfold cubeConst
  have hX : 0 ≤ ((d * (ℓ + 1) ^ d : ℕ) : ℝ) / (((1 : ℕ) : ℝ) * (1 - γ * Real.exp (lam * ((ℓ : ℝ) + 1)))) :=
    div_nonneg (Nat.cast_nonneg _) (by rw [Nat.cast_one, one_mul]; exact hD.le)
  exact mul_nonneg (mul_nonneg (mul_nonneg hX (mul_nonneg (Nat.cast_nonneg _) hV)) hL) (Real.exp_pos _).le

variable [(haarG G).IsInvInvariant]
variable (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)

include hc hU in
/-- **Theorem A on the torus with the thin-cube family, for slab observables.** Under influence bounds `κ` for the thin
cubes of side `ℓ ≥ 1` with GDS(`γ`), and `γ e^{λ(ℓ + 1)} < 1`: for `F` depending on the time slab `[0, s]` with
`δ_l(F) ≤ v_l`, `∑ v ≤ V`, `v ≤ L`, and `2M + 2s + 2 ≤ N`,
`|Cov_μ(F ∘ S_M, F ∘ Θ)| ≤ C e^{-λ M}`, `C = cubeConst d ℓ γ λ V L` (independent of `N`). -/
theorem corr_decay_cubes {φ : ℝ → ℝ} (hφ : PosWeight n φ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {κ : FinLatticeSites d N → LatticeLink d N → ℝ}
    (hκ : ∀ x z, z ∉ thinCube ℓ x → IsInfluenceBound (thinCube ℓ x) (gaugeSpec (G := G) n φ (thinCube ℓ x)) z (κ x z))
    {γ : ℝ} (hγ : 0 ≤ γ) (hgds : GDS (thinCube (d := d) (N := N) ℓ) κ γ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hρ : γ * Real.exp (lam * ((ℓ : ℝ) + 1)) < 1)
    {F : GaugeConnection G d N → ℝ} (hF : BM F) {s : ℕ} (hFs : DepOn F (timeSlab 0 s))
    {v : LatticeLink d N → ℝ} (hv : OscBound F v) {V L : ℝ} (hV : ∑ l, v l ≤ V) (hL : ∀ l, v l ≤ L)
    {M : ℕ} (hNM : 2 * M + 2 * s + 2 ≤ N) :
    |corr n φ F M| ≤ cubeConst d ℓ γ lam V L * Real.exp (-(lam * M)) := by
  have := isProbabilityMeasure_gaugeMeasure (d := d) (N := N) hc hU hφ
  have l₀ : LatticeLink d N := ⟨fun _ => 0, 0⟩
  have : Nonempty (LatticeLink d N) := ⟨l₀⟩
  have hv0 : ∀ l, 0 ≤ v l := fun l => hv.nonneg (fun _ => 1) l
  have hL0 : 0 ≤ L := (hv0 l₀).trans (hL l₀)
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
  have hvf : OscBound (fun U => F (tShift (M : ZMod N) U)) (fun a => v (shiftLink (-(M : ZMod N)) a)) := by
    intro U x t
    show |F (tShift (M : ZMod N) U) - F (tShift (M : ZMod N) (Function.update U x t))| ≤ _
    rw [tShift_update]
    exact hv _ _ _
  have hvg : OscBound (fun U => F (thetaConn U)) (fun _ => L) := by
    intro U x t
    show |F (thetaConn U) - F (thetaConn (Function.update U x t))| ≤ _
    rw [thetaConn_update]
    exact (hv _ _ _).trans (hL _)
  have hR : ∀ a ∈ A, ∀ b ∈ Sg, (M : ℝ) ≤ linkDist a b := by
    intro a ha b hb
    obtain ⟨l, hl, rfl⟩ := mem_image.1 ha
    obtain ⟨l', hl', rfl⟩ := mem_image.1 hb
    exact sep_shift_mirror hNM hl hl'
  have h := P.theoremA_H (trim (thinCube ℓ) κ) (fun j z hz => influence_trim hκ j z hz) hγ (gds_trim hκ hgds)
    (cmin := 1) (cmax := (ℓ + 1) ^ d) (b := d * (ℓ + 1) ^ d) le_rfl
    (fun x => one_le_coverage hℓ x) (fun x => coverage_le ℓ x) (fun j => card_thinCube_le ℓ j)
    linkDist linkDist_self linkDist_triangle (D₀ := (ℓ : ℝ)) (D₁ := (ℓ : ℝ) + 1)
    (fun _ _ hx _ hy => linkDist_le_of_mem_thinCube hx hy)
    (fun _ _ _ _ hy hk => dist_shell_le (shell_of_trim_ne hk) hy)
    hlam hρ hf hg hfA hgS hvf hL0 hvg hR
  have hsumA : ∑ a ∈ A, v (shiftLink (-(M : ZMod N)) a) ≤ V := by
    calc ∑ a ∈ A, v (shiftLink (-(M : ZMod N)) a) ≤ ∑ a, v (shiftLink (-(M : ZMod N)) a) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun a _ _ => hv0 _)
      _ = ∑ l, v l := Equiv.sum_comp (shiftLinkEquiv (-(M : ZMod N))) v
      _ ≤ V := hV
  have hD : 0 < 1 - γ * Real.exp (lam * ((ℓ : ℝ) + 1)) := by linarith
  have hX : 0 ≤ ((d * (ℓ + 1) ^ d : ℕ) : ℝ) / (((1 : ℕ) : ℝ) * (1 - γ * Real.exp (lam * ((ℓ : ℝ) + 1)))) :=
    div_nonneg (Nat.cast_nonneg _) (by rw [Nat.cast_one, one_mul]; exact hD.le)
  have he : Real.exp (-(lam * ((M : ℝ) - ℓ))) = Real.exp (lam * ℓ) * Real.exp (-(lam * M)) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold corr
  refine h.trans ?_
  calc _ ≤ ((d * (ℓ + 1) ^ d : ℕ) : ℝ) / (((1 : ℕ) : ℝ) * (1 - γ * Real.exp (lam * ((ℓ : ℝ) + 1)))) *
          ((((ℓ + 1) ^ d : ℕ) : ℝ) * V) * L * Real.exp (-(lam * ((M : ℝ) - ℓ))) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_right _ hL0
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsumA (Nat.cast_nonneg _)) hX
    _ = cubeConst d ℓ γ lam V L * Real.exp (-(lam * M)) := by
        rw [he]; unfold cubeConst; ring

/-! ## Theorem C on the finite torus, all hypotheses discharged except GDS -/

variable (hN : Even N)

include hc hU hN in
/-- **Theorem C on the finite torus under GDS for thin cubes.** For `r ≥ 1` and `N ≥ 2^{r+1} m + 2s + 2`:
`H(0) ≥ 0` and `|H(m)| ≤ H(0)^{1 - 2^{-r}} C^{2^{-r}} e^{-λ m}`, with `H(m) = Cov_μ(F ∘ S_m, F ∘ Θ)` and
`C = cubeConst d ℓ γ λ V L` independent of `N`. -/
theorem gauge_theoremC_cubes {φ : ℝ → ℝ} (hφ : PosWeight n φ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {κ : FinLatticeSites d N → LatticeLink d N → ℝ}
    (hκ : ∀ x z, z ∉ thinCube ℓ x → IsInfluenceBound (thinCube ℓ x) (gaugeSpec (G := G) n φ (thinCube ℓ x)) z (κ x z))
    {γ : ℝ} (hγ : 0 ≤ γ) (hgds : GDS (thinCube (d := d) (N := N) ℓ) κ γ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hρ : γ * Real.exp (lam * ((ℓ : ℝ) + 1)) < 1)
    {F : GaugeConnection G d N → ℝ} (hF : BM F) {s : ℕ} (hFs : DepOn F (timeSlab 0 s))
    {v : LatticeLink d N → ℝ} (hv : OscBound F v) {V L : ℝ} (hV : ∑ l, v l ≤ V) (hL : ∀ l, v l ≤ L)
    {m r : ℕ} (hr : 1 ≤ r) (hNr : 2 ^ (r + 1) * m + 2 * s + 2 ≤ N) :
    0 ≤ corr n φ F 0 ∧
      |corr n φ F m| ≤ corr n φ F 0 ^ (1 - (1 / 2 : ℝ) ^ r) * cubeConst d ℓ γ lam V L ^ ((1 / 2 : ℝ) ^ r) *
        Real.exp (-(lam * m)) := by
  have l₀ : LatticeLink d N := ⟨fun _ => 0, 0⟩
  have hv0 : ∀ l, 0 ≤ v l := fun l => hv.nonneg (fun _ => 1) l
  have hL0 : 0 ≤ L := (hv0 l₀).trans (hL l₀)
  have hV0 : 0 ≤ V := (sum_nonneg fun l _ => hv0 l).trans hV
  have hD : 0 < 1 - γ * Real.exp (lam * ((ℓ : ℝ) + 1)) := by linarith
  set K := 2 ^ (r - 1) * m with hK
  have hpow : 2 ^ (r + 1) * m = 4 * K := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp only [hK, Nat.add_sub_cancel, pow_succ]
    ring
  have hNK : 4 * K + 2 * s + 2 ≤ N := by rw [← hpow]; exact hNr
  have hpos : ∀ j, j ≤ K → LinkDep (fun U => F (tShift (j : ZMod N) U)) (posHalfLinks d N) :=
    fun j hj => linkDep_tShift_of_slab hFs (by omega)
  have hdec := corr_decay_cubes hc hU hφ hℓ hκ hγ hgds hlam hρ hF hFs hv hV hL (M := 2 ^ r * m)
    (by rw [show 2 * (2 ^ r * m) = 2 ^ (r + 1) * m by ring]; exact hNr)
  exact torus_theoremC_corr hc hU hN hφ hF hpos hr le_rfl (cubeConst_nonneg hD hV0 hL0) hdec

include hc hU hN in
/-- **Finite-volume decay, uniform in `N`, with an arbitrarily small additive error instead of a prefactor.**
For `r ≥ 1` and every torus with `N ≥ 2^{r+1} m + 2s + 2`:
`|H_N(m)| ≤ (H_N(0) + 2^{-r} C) e^{-λ m}`, `C = cubeConst d ℓ γ λ V L` independent of `N`. -/
theorem gauge_decay_finiteVolume {φ : ℝ → ℝ} (hφ : PosWeight n φ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {κ : FinLatticeSites d N → LatticeLink d N → ℝ}
    (hκ : ∀ x z, z ∉ thinCube ℓ x → IsInfluenceBound (thinCube ℓ x) (gaugeSpec (G := G) n φ (thinCube ℓ x)) z (κ x z))
    {γ : ℝ} (hγ : 0 ≤ γ) (hgds : GDS (thinCube (d := d) (N := N) ℓ) κ γ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hρ : γ * Real.exp (lam * ((ℓ : ℝ) + 1)) < 1)
    {F : GaugeConnection G d N → ℝ} (hF : BM F) {s : ℕ} (hFs : DepOn F (timeSlab 0 s))
    {v : LatticeLink d N → ℝ} (hv : OscBound F v) {V L : ℝ} (hV : ∑ l, v l ≤ V) (hL : ∀ l, v l ≤ L)
    {m r : ℕ} (hr : 1 ≤ r) (hNr : 2 ^ (r + 1) * m + 2 * s + 2 ≤ N) :
    |corr n φ F m| ≤ (corr n φ F 0 + (1 / 2 : ℝ) ^ r * cubeConst d ℓ γ lam V L) * Real.exp (-(lam * m)) := by
  obtain ⟨h0, h⟩ := gauge_theoremC_cubes hc hU hN hφ hℓ hκ hγ hgds hlam hρ hF hFs hv hV hL hr hNr
  have l₀ : LatticeLink d N := ⟨fun _ => 0, 0⟩
  have hv0 : ∀ l, 0 ≤ v l := fun l => hv.nonneg (fun _ => 1) l
  have hL0 : 0 ≤ L := (hv0 l₀).trans (hL l₀)
  have hV0 : 0 ≤ V := (sum_nonneg fun l _ => hv0 l).trans hV
  have hD : 0 < 1 - γ * Real.exp (lam * ((ℓ : ℝ) + 1)) := by linarith
  have hC := cubeConst_nonneg (d := d) hD hV0 hL0
  set q : ℝ := (1 / 2 : ℝ) ^ r
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hy := Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.2 hq1) hq0 h0 hC (by ring)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  nlinarith [mul_nonneg hq0 h0]

end Gauge

/-! ## Corollary B from `UniformGDS` -/

section Levels

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [HasHaarProbability G] [(haarG G).IsInvInvariant] {n : ℕ}
  [HasGaugeTrace G n]

variable (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)

include hc hU in
/-- **`UniformGDS` gives `LevelDecay`.** Setting: lattice spacings `a_k > 0`, `L₀ > 0`, `0 < γ`; at each level `k` a
sequence of even tori `N_{k,j} → ∞` (`j → ∞`), weights `φ_k` satisfying (Φ), and the open hypothesis `UniformGDS` on
every torus of the sequences. Observables: at level `k` on torus `j`, `F_{k,j}` bounded measurable, depending on the
time slab `[0, s_k]`, with `∑_l δ_l(F_{k,j}) ≤ V_k` and `δ_l(F_{k,j}) ≤ L_k`. If `h_k(t)` is the limit as `j → ∞` of the
reflected connected correlations `Cov(F_{k,j} ∘ S_t, F_{k,j} ∘ Θ)`, then `|h_k(t)| ≤ h_k(0) e^{-λ t}` for every
`0 ≤ λ < log(1/γ)/(ℓ_k + 1)`, i.e. `LevelDecay L₀ γ a h`. -/
theorem levelDecay_of_uniformGDS {L₀ γ : ℝ} (hL₀ : 0 < L₀) (hγ0 : 0 < γ) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k)
    (Ns : ℕ → ℕ → ℕ) [∀ k j, NeZero (Ns k j)] (hEven : ∀ k j, Even (Ns k j))
    (hNs : ∀ k, Tendsto (Ns k) atTop atTop) {φ : ℕ → ℝ → ℝ} (hφ : ∀ k, PosWeight n (φ k))
    (hGDS : ∀ j, UniformGDS (d := d) (G := G) n (fun k => Ns k j) φ L₀ γ a)
    (F : ∀ k j, GaugeConnection G d (Ns k j) → ℝ) (hF : ∀ k j, BM (F k j)) (s : ℕ → ℕ)
    (hFs : ∀ k j, DepOn (F k j) (timeSlab 0 (s k))) (v : ∀ k j, LatticeLink d (Ns k j) → ℝ)
    (hv : ∀ k j, OscBound (F k j) (v k j)) (V L : ℕ → ℝ) (hV : ∀ k j, ∑ l, v k j l ≤ V k)
    (hL : ∀ k j l, v k j l ≤ L k) (h : ℕ → ℕ → ℝ)
    (hlim : ∀ k t, Tendsto (fun j => corr n (φ k) (F k j) t) atTop (𝓝 (h k t))) :
    LevelDecay L₀ γ a h := by
  intro k lam hlam0 hlam t
  have hℓ : 1 ≤ side L₀ a k := Nat.ceil_pos.2 (div_pos hL₀ (ha k))
  have hρ : γ * Real.exp (lam * ((side L₀ a k : ℝ) + 1)) < 1 := rate_lt_of_lt hγ0 (by positivity) hlam
  set C := cubeConst d (side L₀ a k) γ lam (V k) (L k)
  set E := Real.exp (-(lam * t))
  -- the finite-volume bound, eventually in `j`, for each `r`
  have hfin : ∀ r : ℕ, 1 ≤ r → ∀ᶠ j in atTop,
      |corr n (φ k) (F k j) t| ≤ (corr n (φ k) (F k j) 0 + (1 / 2 : ℝ) ^ r * C) * E := by
    intro r hr
    filter_upwards [tendsto_atTop.1 (hNs k) (2 ^ (r + 1) * t + 2 * s k + 2)] with j hj
    obtain ⟨κ, hκ, hg⟩ := hGDS j k
    exact gauge_decay_finiteVolume hc hU (hEven k j) (hφ k) hℓ hκ hγ0.le hg hlam0 hρ (hF k j) (hFs k j) (hv k j)
      (hV k j) (hL k j) hr hj
  -- the limit in `j`
  have hr_bound : ∀ r : ℕ, 1 ≤ r → |h k t| ≤ (h k 0 + (1 / 2 : ℝ) ^ r * C) * E := fun r hr =>
    le_of_tendsto_of_tendsto (hlim k t).abs (((hlim k 0).add_const _).mul_const E) (hfin r hr)
  -- the limit `r → ∞`
  have hq : Tendsto (fun r : ℕ => (h k 0 + (1 / 2 : ℝ) ^ r * C) * E) atTop (𝓝 ((h k 0 + 0 * C) * E)) :=
    (tendsto_const_nhds.add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const C)).mul_const E
  rw [zero_mul, add_zero] at hq
  exact ge_of_tendsto hq (eventually_atTop.2 ⟨1, fun r hr => hr_bound r hr⟩)

include hc hU in
/-- **Corollary B (lattice part, physical units) with `UniformGDS` as the only open hypothesis.** In the setting of
`levelDecay_of_uniformGDS`, with `γ < 1` and `a_k → 0`:
1. `|h_k(t)| ≤ h_k(0) · exp(-(log(1/γ)/(L₀ + 2a_k)) · t a_k)` (decay in physical time `t a_k`);
2. `m_k = log(1/γ)/((ℓ_k + 1) a_k) ≥ log(1/γ)/(L₀ + 2a_k)`;
3. `m_k → log(1/γ)/L₀`.
The remaining hypotheses are structural: weights in class (Φ), unitary continuous representation, inversion-invariant
Haar probability, even tori growing to infinity, slab observables with uniform oscillation bounds, and `h` the limit of
the torus correlations. -/
theorem corollaryB_of_uniformGDS {L₀ γ : ℝ} (hL₀ : 0 < L₀) (hγ0 : 0 < γ) (hγ1 : γ < 1) {a : ℕ → ℝ}
    (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (Ns : ℕ → ℕ → ℕ) [∀ k j, NeZero (Ns k j)] (hEven : ∀ k j, Even (Ns k j))
    (hNs : ∀ k, Tendsto (Ns k) atTop atTop) {φ : ℕ → ℝ → ℝ} (hφ : ∀ k, PosWeight n (φ k))
    (hGDS : ∀ j, UniformGDS (d := d) (G := G) n (fun k => Ns k j) φ L₀ γ a)
    (F : ∀ k j, GaugeConnection G d (Ns k j) → ℝ) (hF : ∀ k j, BM (F k j)) (s : ℕ → ℕ)
    (hFs : ∀ k j, DepOn (F k j) (timeSlab 0 (s k))) (v : ∀ k j, LatticeLink d (Ns k j) → ℝ)
    (hv : ∀ k j, OscBound (F k j) (v k j)) (V L : ℕ → ℝ) (hV : ∀ k j, ∑ l, v k j l ≤ V k)
    (hL : ∀ k j l, v k j l ≤ L k) (h : ℕ → ℕ → ℝ)
    (hlim : ∀ k t, Tendsto (fun j => corr n (φ k) (F k j) t) atTop (𝓝 (h k t))) :
    (∀ k t, |h k t| ≤ h k 0 * Real.exp (-(Real.log (1 / γ) / (L₀ + 2 * a k) * (t * a k)))) ∧
    (∀ k, Real.log (1 / γ) / (L₀ + 2 * a k) ≤ physMass L₀ γ a k) ∧
    Tendsto (physMass L₀ γ a) atTop (𝓝 (Real.log (1 / γ) / L₀)) :=
  corollaryB_lattice hL₀ hγ0 hγ1 ha ha0
    (levelDecay_of_uniformGDS hc hU hL₀ hγ0 ha Ns hEven hNs hφ hGDS F hF s hFs v hv V L hV hL h hlim)

end Levels

end OneScale.CubeChain
