/-
Proof phase, cycle 8, workstream 3 (c8c-concrete): the wall-cut one-box criterion and decay under arbitrary
boundary conditions in every cube (Chatterjee's Definition 2.3) (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c8c-concrete/NOTE.md`, section 3.
-/

import ProofPhase.OneBox2.Anchor
import ProofPhase.SectorS.ConjS

/-!
# The one-box sum for boxes cut by the walls of a cube

**The cube law** `cubeLaw β Q σ₀`: the Wilson measure on the links of the region `Q` (a cube, or any finite set of links)
with every link outside `Q` frozen at the boundary condition `σ₀`: `q_Q^{σ₀}` pushed through `splice Q σ₀`.

**Cut boxes.** The block `(Λ₀ + t)` of cells meets the cube in the fine links `Q ∩ cellPre (Λ₀ + t)`; the cells cut by
the walls keep their outside links frozen at `σ₀`.  `cutSpec` is the DLR kernel of such a cut block *inside the cube
measure*: the torus kernel of the block at the boundary `splice Q σ₀ τ`.  `cubeBlockSpec` proves these kernels form a
`BlockSpec` of the cube law (**DLR consistency for the cube**: the nested identity `dlr_locSpec` for the weight
`W(splice Q σ₀ ·)`), and `cubeLifted` lifts it to cells (`Lift.lean`), with `σ₀` as the frozen reference on the cut
cells.  Every cell, cut or not, is covered by exactly `|Λ₀|` blocks (`coverage_box`), so no extra blocks are needed
for the frozen part.

**The criterion** `WallCutOneBox T`: as `WilsonOneBox`, but the influence bounds are required for the cut block laws of
**every** cube `Q` and **every** boundary condition `σ₀` (the box-influence is the unrestricted one: all bounded test
functions of the box, gauge-blind; by the Haar-alignment argument of the note it equals the gauge-invariant one).
`Q = univ` is the uncut criterion.

**The theorem** `cubeDecay_of_wallCut`: `WallCutOneBox T ⇒ CubeDecay T`: for every level `k ≥ k₀`, torus, region `Q`,
boundary condition `σ₀` and bounded measurable `F`, `G` (not necessarily gauge invariant) with supports at physical
distance `≥ D`, `|Cov_{cubeLaw}(F, G)| ≤ c_R e^{-mD}`: uniform in level, volume, region and boundary condition.
This is the content of Chatterjee's Definition 2.3 (see `ChatterjeeTheorem24`).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  ProofPhase.Torus ProofPhase.V3 ProofPhase.V4 ProofPhase.OneBox

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.OneBox2

/-! ## The unrestricted one-box theorem (gauge-blind influences, arbitrary `g`) -/

section Unres

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] {J U : Type*} [Fintype J] [DecidableEq J]
  [Fintype U] [DecidableEq U] {μ : Measure (ι → S)}

/-- **One box gives decay, with the unrestricted (gauge-blind) box influence and an arbitrary second function.**
`OneBox.abs_cov_le_of_oneBox` without covariance and invariance; the box influences are tested on all bounded test
functions of the box. -/
theorem abs_cov_le_of_oneBox_unres [IsProbabilityMeasure μ] [Nonempty ι] (P : BlockSpec μ J) (rel : J → ι → U)
    (Λ₀ : Finset U) (hbox : IsBoxFamily P.block rel Λ₀) (hΛ : 1 ≤ Λ₀.card) (κ Ehat : U → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBound (P.block j) (P.spec j) z (κ (rel j z)))
    {b : ℕ} (hb : ∀ j, (P.block j).card ≤ b)
    (dist : ι → ι → ℝ) (hd0 : ∀ x, dist x x = 0) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    {D₀ : ℝ} (hD₀ : ∀ j, ∀ x ∈ P.block j, ∀ y ∈ P.block j, dist x y ≤ D₀)
    (hE : ∀ j x y, x ∉ P.block j → y ∈ P.block j → dist x y ≤ Ehat (rel j x))
    {lam γ : ℝ} (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hsum : OneBoxSum κ Ehat Λ₀ lam γ)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A Sg : Finset ι} (hfA : DepOn f A)
    (hgS : DepOn g Sg) {vf : ι → ℝ} (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : OscBound g (fun _ => Lg))
    {R : ℝ} (hR : ∀ x ∈ A, ∀ y ∈ Sg, R ≤ dist x y) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * ∫ σ, g σ ∂μ| ≤
      b / (1 - γ) * (∑ x ∈ A, vf x) * Lg * Real.exp (-(lam * (R - D₀))) := by
  have hcov : ∀ x, Λ₀.card ≤ coverage P.block x := fun x => (coverage_box hbox x).ge
  have hcmax : ∀ x, coverage P.block x ≤ Λ₀.card := fun x => (coverage_box hbox x).le
  have h := Attempts.R3.theoremA_w P (fun j x => κ (rel j x)) hk hΛ hcov hcmax hb dist hd0 htri hD₀
    (fun j x => Ehat (rel j x)) hE hlam hγ hγ1 (gdsw_of_oneBox hbox hsum) hf hg hfA hgS hvf hLg hvg hR
  refine h.trans (le_of_eq ?_)
  have hc : (Λ₀.card : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ Λ₀.card := by exact_mod_cast hΛ
    linarith
  field_simp

end Unres

/-! ## The cube law and the cut kernels -/

section CubeLaw

variable {N : ℕ} [NeZero N]

theorem splice_splice_same {ι S' : Type*} [DecidableEq ι] (B : Finset ι) (σ ξ : ι → S') :
    splice B σ (splice B σ ξ) = splice B σ ξ := by
  funext i; by_cases h : i ∈ B <;> simp [splice, h]

theorem splice_comm_sub {ι S' : Type*} [DecidableEq ι] {B Q : Finset ι} (hBQ : B ⊆ Q) (σ₀ ξ η : ι → S') :
    splice B (splice Q σ₀ ξ) η = splice Q σ₀ (splice B ξ η) := by
  funext i
  by_cases hB : i ∈ B
  · simp [splice, hB, hBQ hB]
  · by_cases hQ : i ∈ Q <;> simp [splice, hB, hQ]

/-- **The cube law**: the Wilson measure on the links of `Q` with the links outside `Q` frozen at `σ₀`. -/
def cubeLaw (β : ℝ) (Q : Finset (LatticeLink 4 N)) (σ₀ : GaugeConnection SU2 4 N) :
    Measure (GaugeConnection SU2 4 N) :=
  (gaugeSpec (G := SU2) (d := 4) (N := N) 2 (wilsonWeight β) Q σ₀).map (splice Q σ₀)

/-- The kernel of a cut block inside the cube measure: the torus kernel at the boundary `splice Q σ₀ τ`. -/
def cutSpec (β : ℝ) (Q : Finset (LatticeLink 4 N)) (σ₀ : GaugeConnection SU2 4 N) (B : Finset (LatticeLink 4 N))
    (τ : GaugeConnection SU2 4 N) : Measure (GaugeConnection SU2 4 N) :=
  gaugeSpec (G := SU2) (d := 4) (N := N) 2 (wilsonWeight β) B (splice Q σ₀ τ)

theorem localWeight_wilsonBlock (β : ℝ) (B : Finset (LatticeLink 4 N)) :
    LocalWeight (plaqProd (G := SU2) (d := 4) (N := N) 2 (wilsonWeight β) (touching B)) :=
  localWeight_plaqProd su2_hc' su2_hU' (posWeight_wilson 2 β) _

instance isProbabilityMeasure_cubeLaw (β : ℝ) (Q : Finset (LatticeLink 4 N)) (σ₀ : GaugeConnection SU2 4 N) :
    IsProbabilityMeasure (cubeLaw β Q σ₀) := by
  have := (localWeight_wilsonBlock β Q).isProbabilityMeasure_locSpec (ν := haarG SU2) (B := Q) σ₀
  exact (Measure.isProbabilityMeasure_map_iff (measurable_splice_right Q σ₀).aemeasurable).2
    (by unfold gaugeSpec; exact this)

/-- Cutting a kernel to a sub-block `B ⊆ Q` of the region: the torus kernel of `B` at `splice Q σ₀ ξ` is the kernel
of the weight `W(splice Q σ₀ ·)` at `ξ`. -/
theorem locSpec_cut {B Q : Finset (LatticeLink 4 N)} (hBQ : B ⊆ Q) (W : GaugeConnection SU2 4 N → ℝ)
    (σ₀ ξ : GaugeConnection SU2 4 N) :
    locSpec (haarG SU2) B (fun ζ => W (splice Q σ₀ ζ)) ξ = locSpec (haarG SU2) B W (splice Q σ₀ ξ) := by
  unfold locSpec locZ
  simp_rw [← splice_comm_sub hBQ]

/-- A plaquette that does not touch `B` does not read the block `B` of the cut configuration. -/
theorem xp_cut_splice {B : Finset (LatticeLink 4 N)} {p : LatticePlaquette 4 N} (hp : ¬∃ l ∈ plaqLinks p, l ∈ B)
    (Q : Finset (LatticeLink 4 N)) (σ₀ σ ξ : GaugeConnection SU2 4 N) :
    xp 2 p (splice Q σ₀ (splice B σ ξ)) = xp 2 p (splice Q σ₀ σ) := by
  unfold xp
  congr 1
  refine plaquetteHolonomy_dependsOn p _ _ fun l hl => ?_
  have : l ∉ B := fun h => hp ⟨l, hl, h⟩
  by_cases hQ : l ∈ Q <;> simp [splice, hQ, this]

end CubeLaw

/-! ## The cube law has the cut kernels as its conditional laws -/

section CubeSpec

variable {N : ℕ} [NeZero N]

theorem localWeight_comp_splice {ι S' : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S'] {W : (ι → S') → ℝ}
    (hW : LocalWeight W) (Q : Finset ι) (σ₀ : ι → S') : LocalWeight (fun ζ => W (splice Q σ₀ ζ)) :=
  ⟨hW.meas.comp (measurable_splice_right Q σ₀), hW.lower.imp fun c hc => ⟨hc.1, fun σ => hc.2 _⟩,
    hW.upper.imp fun C hC σ => hC _⟩

instance isProbabilityMeasure_cutSpec (β : ℝ) (Q : Finset (LatticeLink 4 N)) (σ₀ : GaugeConnection SU2 4 N)
    (B : Finset (LatticeLink 4 N)) (τ : GaugeConnection SU2 4 N) : IsProbabilityMeasure (cutSpec β Q σ₀ B τ) :=
  (localWeight_wilsonBlock β B).isProbabilityMeasure_locSpec (ν := haarG SU2) (B := B) (splice Q σ₀ τ)

theorem measurable_cutSpec (β : ℝ) (Q : Finset (LatticeLink 4 N)) (σ₀ : GaugeConnection SU2 4 N)
    (B : Finset (LatticeLink 4 N)) : Measurable (cutSpec β Q σ₀ B) :=
  (measurable_gaugeSpec β B).comp (measurable_splice_right Q σ₀)

theorem measurable_blockAvg_cut (β : ℝ) (Q : Finset (LatticeLink 4 N)) (σ₀ : GaugeConnection SU2 4 N)
    (B : Finset (LatticeLink 4 N)) {h : GaugeConnection SU2 4 N → ℝ} (hh : BM h) :
    Measurable (blockAvg B (cutSpec β Q σ₀ B) h) := by
  have e : blockAvg B (cutSpec β Q σ₀ B) h = fun τ =>
      ∫ ξ, (fun p : GaugeConnection SU2 4 N × GaugeConnection SU2 4 N => h (splice B p.1 p.2)) (τ, ξ)
        ∂(cutSpec β Q σ₀ B τ) := rfl
  rw [e]
  exact measurable_integral_spec (q := cutSpec β Q σ₀ B) (measurable_cutSpec β Q σ₀ B)
    (hh.meas.comp (measurable_splice B))

theorem integral_cubeLaw (β : ℝ) (Q : Finset (LatticeLink 4 N)) (σ₀ : GaugeConnection SU2 4 N)
    {g : GaugeConnection SU2 4 N → ℝ} (hg : Measurable g) :
    ∫ τ, g τ ∂(cubeLaw β Q σ₀) =
      ∫ ξ, g (splice Q σ₀ ξ) ∂(locSpec (haarG SU2) Q (plaqProd (G := SU2) (d := 4) (N := N) 2 (wilsonWeight β)
        (touching Q)) σ₀) :=
  integral_map (measurable_splice_right Q σ₀).aemeasurable hg.aestronglyMeasurable

/-- **The cut kernels are the conditional laws of the cube law** (DLR consistency inside the cube): for blocks
`B_j ⊆ Q`, the kernels `τ ↦ q_{B_j}(splice Q σ₀ τ)` form a block specification of `cubeLaw β Q σ₀`. -/
def cubeBlockSpec (β : ℝ) (Q : Finset (LatticeLink 4 N)) (σ₀ : GaugeConnection SU2 4 N) {J : Type*}
    (Bf : J → Finset (LatticeLink 4 N)) (hBQ : ∀ j, Bf j ⊆ Q) : BlockSpec (cubeLaw β Q σ₀) J where
  block := Bf
  spec j := cutSpec β Q σ₀ (Bf j)
  isProb j τ := isProbabilityMeasure_cutSpec β Q σ₀ (Bf j) τ
  spec_congr j τ τ' h := by
    unfold cutSpec gaugeSpec
    exact (localWeight_wilsonBlock β (Bf j)).locSpec_congr _ _ (fun i hi => by
      by_cases hQ : i ∈ Q <;> simp [splice, hQ, h i hi])
  meas_avg j h hh := measurable_blockAvg_cut β Q σ₀ (Bf j) hh
  dlr j h hh := by
    set B := Bf j with hBdef
    have hBQ' : B ⊆ Q := hBQ j
    set φ := wilsonWeight β
    set WQ := plaqProd (G := SU2) (d := 4) (N := N) 2 φ (touching Q)
    set WB := plaqProd (G := SU2) (d := 4) (N := N) 2 φ (touching B)
    have hWQ : LocalWeight (fun ζ => WQ (splice Q σ₀ ζ)) := localWeight_comp_splice (localWeight_wilsonBlock β Q) Q σ₀
    have hWB : LocalWeight (fun ζ => WB (splice Q σ₀ ζ)) := localWeight_comp_splice (localWeight_wilsonBlock β B) Q σ₀
    set Rf : GaugeConnection SU2 4 N → ℝ := fun ζ =>
      ∏ p ∈ touching Q \ touching B, φ (xp 2 p (splice Q σ₀ ζ)) with hRf
    have hRB : ∀ σ ξ, Rf (splice B σ ξ) = Rf σ := by
      intro σ ξ
      simp only [hRf]
      refine prod_congr rfl fun p hp => ?_
      have hpB : ¬∃ l ∈ plaqLinks p, l ∈ B := by
        intro h'
        have := (mem_sdiff.1 hp).2
        simp only [touching, mem_filter, mem_univ, true_and] at this
        exact this h'
      rw [xp_cut_splice hpB]
    have hsub : touching B ⊆ touching Q := by
      intro p hp
      simp only [touching, mem_filter, mem_univ, true_and] at hp ⊢
      obtain ⟨l, hl, hlB⟩ := hp
      exact ⟨l, hl, hBQ' hlB⟩
    have hW : ∀ ζ, WQ (splice Q σ₀ ζ) = WB (splice Q σ₀ ζ) * Rf ζ := by
      intro ζ
      simp only [WQ, WB, plaqProd, hRf]
      rw [mul_comm, prod_sdiff hsub]
    have hlocQ : locSpec (haarG SU2) Q WQ σ₀ = weightMeasure (haarG SU2) (fun ζ => WQ (splice Q σ₀ ζ)) := rfl
    have hb : ∀ ξ, blockAvg B (cutSpec β Q σ₀ B) h (splice Q σ₀ ξ) =
        blockAvg B (locSpec (haarG SU2) B (fun ζ => WB (splice Q σ₀ ζ))) (fun ζ => h (splice Q σ₀ ζ)) ξ := by
      intro ξ
      unfold blockAvg cutSpec gaugeSpec
      rw [splice_splice_same, locSpec_cut hBQ' WB σ₀ ξ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
      simp only [splice_comm_sub hBQ']
    have hhs : BM (fun ζ => h (splice Q σ₀ ζ)) :=
      ⟨hh.meas.comp (measurable_splice_right Q σ₀), hh.bdd.imp fun C hC ζ => hC _⟩
    rw [integral_cubeLaw β Q σ₀ ((measurable_blockAvg_cut β Q σ₀ B hh)), integral_cubeLaw β Q σ₀ hh.meas, hlocQ]
    simp_rw [hb]
    exact dlr_locSpec hWB hRB hW hWQ.bm (fun ζ => (hWQ.pos ζ).le) hhs

end CubeSpec

/-! ## Cut boxes of cells -/

section CubeLifted

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- The fine links of the cube `Q` that lie in the cells of the block `b`: the cut block. -/
def cutPre (Q : Finset (LatticeLink 4 N)) (cell : LatticeLink 4 N → LatticeLink 4 M) (b : Finset (LatticeLink 4 M)) :
    Finset (LatticeLink 4 N) := Q ∩ cellPre cell b

/-- **The law of the cut box of cells `b` inside the cube law**, given everything outside, regrouped by cells; the cut
cells keep their outside links frozen at `σ₀`. -/
def cubeBoxSpec (cell : LatticeLink 4 N → LatticeLink 4 M) (β : ℝ) (Q : Finset (LatticeLink 4 N))
    (σ₀ : GaugeConnection SU2 4 N) (b : Finset (LatticeLink 4 M)) :
    (LatticeLink 4 M → (LatticeLink 4 N → SU2)) → Measure (LatticeLink 4 M → (LatticeLink 4 N → SU2)) :=
  liftSpec cell (1 : SU2) b (cutPre Q cell b) σ₀ (cutSpec β Q σ₀ (cutPre Q cell b))

/-- **The block specification of the lifted cube law by the cut boxes `Λ₀ + t`.** -/
def cubeLifted (cell : LatticeLink 4 N → LatticeLink 4 M) (β : ℝ) (Q : Finset (LatticeLink 4 N))
    (σ₀ : GaugeConnection SU2 4 N) (Λ₀ : Finset (FinLatticeSites 4 M)) :
    BlockSpec ((cubeLaw β Q σ₀).map (cellLift cell (1 : SU2))) (FinLatticeSites 4 M) :=
  liftBlockSpec
    (cubeBlockSpec β Q σ₀ (fun t => cutPre Q cell (boxBlock Λ₀ t)) (fun t => inter_subset_left))
    cell (1 : SU2) (boxBlock Λ₀) σ₀
    (fun t e he => mem_cellPre.1 (mem_inter.1 he).2)
    (fun t => measurable_cutSpec β Q σ₀ _)
    (fun t σ σ' h => by
      show cutSpec β Q σ₀ _ σ = cutSpec β Q σ₀ _ σ'
      unfold cutSpec gaugeSpec
      refine (localWeight_wilsonBlock β _).locSpec_congr _ _ (fun i hi => ?_)
      by_cases hQ : i ∈ Q
      · have : cell i ∉ boxBlock Λ₀ t := fun hc => hi (mem_inter.2 ⟨hQ, mem_cellPre.2 hc⟩)
        simp [splice, hQ, h i this]
      · simp [splice, hQ])
    (fun t => by
      have hS : MeasurableSet {U : GaugeConnection SU2 4 N |
          ∀ e, cell e ∈ boxBlock Λ₀ t → e ∉ cutPre Q cell (boxBlock Λ₀ t) → U e = σ₀ e} := by
        have : {U : GaugeConnection SU2 4 N |
            ∀ e, cell e ∈ boxBlock Λ₀ t → e ∉ cutPre Q cell (boxBlock Λ₀ t) → U e = σ₀ e} =
            ⋂ e, {U | cell e ∈ boxBlock Λ₀ t → e ∉ cutPre Q cell (boxBlock Λ₀ t) → U e = σ₀ e} := by
          ext U; simp
        rw [this]
        refine MeasurableSet.iInter fun e => ?_
        by_cases h : cell e ∈ boxBlock Λ₀ t ∧ e ∉ cutPre Q cell (boxBlock Λ₀ t)
        · have : {U : GaugeConnection SU2 4 N | cell e ∈ boxBlock Λ₀ t → e ∉ cutPre Q cell (boxBlock Λ₀ t) →
              U e = σ₀ e} = {U | U e = σ₀ e} := by
            ext U; simp [h.1, h.2]
          rw [this]
          exact measurableSet_eq_fun (measurable_pi_apply e) measurable_const
        · have : {U : GaugeConnection SU2 4 N | cell e ∈ boxBlock Λ₀ t → e ∉ cutPre Q cell (boxBlock Λ₀ t) →
              U e = σ₀ e} = Set.univ := by
            ext U
            simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
            intro h1 h2
            exact absurd ⟨h1, h2⟩ h
          rw [this]
          exact MeasurableSet.univ
      refine (ae_map_iff (measurable_splice_right Q σ₀).aemeasurable hS).2 (ae_of_all _ fun ξ e h1 h2 => ?_)
      have hQ : e ∉ Q := fun hQ => h2 (mem_inter.2 ⟨hQ, mem_cellPre.2 h1⟩)
      simp [splice, hQ])

theorem cubeLifted_block (cell : LatticeLink 4 N → LatticeLink 4 M) (β : ℝ) (Q : Finset (LatticeLink 4 N))
    (σ₀ : GaugeConnection SU2 4 N) (Λ₀ : Finset (FinLatticeSites 4 M)) (t : FinLatticeSites 4 M) :
    (cubeLifted cell β Q σ₀ Λ₀).block t = boxBlock Λ₀ t := rfl

theorem cubeLifted_spec (cell : LatticeLink 4 N → LatticeLink 4 M) (β : ℝ) (Q : Finset (LatticeLink 4 N))
    (σ₀ : GaugeConnection SU2 4 N) (Λ₀ : Finset (FinLatticeSites 4 M)) (t : FinLatticeSites 4 M) :
    (cubeLifted cell β Q σ₀ Λ₀).spec t = cubeBoxSpec cell β Q σ₀ (boxBlock Λ₀ t) := rfl

/-- **The uncut box law is the case `Q = univ` of the cut one.** -/
theorem cubeBoxSpec_univ (cell : LatticeLink 4 N → LatticeLink 4 M) (β : ℝ) (σ₀ : GaugeConnection SU2 4 N)
    (b : Finset (LatticeLink 4 M)) : cubeBoxSpec cell β univ σ₀ b = wilsonBoxSpec cell β b := by
  have hpre : cutPre univ cell b = cellPre cell b := by unfold cutPre; exact univ_inter _
  have hspl : ∀ τ : GaugeConnection SU2 4 N, splice univ σ₀ τ = τ := fun τ => by
    funext i; simp [splice]
  have hBf : ∀ e, e ∈ cellPre cell b ↔ cell e ∈ b := fun e => mem_cellPre
  funext W
  unfold cubeBoxSpec wilsonBoxSpec liftSpec
  rw [hpre]
  have e1 : cutSpec β univ σ₀ (cellPre cell b) (cellProj cell W) =
      gaugeSpec (G := SU2) (d := 4) (N := N) 2 (wilsonWeight β) (cellPre cell b) (cellProj cell W) := by
    unfold cutSpec; rw [hspl]
  rw [e1]
  have e2 : liftMap cell (1 : SU2) b (cellPre cell b) σ₀ W =
      liftMap cell (1 : SU2) b (cellPre cell b) (fun _ => 1) W := by
    funext U'
    rw [liftMap_eq_full cell 1 b _ σ₀ hBf, liftMap_eq_full cell 1 b _ _ hBf]
  rw [e2]

end CubeLifted

/-! ## The criterion and the decay -/

/-- **The one-box criterion for boxes cut by the walls of every cube** (Wilson measure, physical cell scale).
As `WilsonOneBox`, but the box influences (unrestricted: all bounded test functions of the box, gauge-blind) are
required for the cut box laws `cubeBoxSpec` of **every** region `Q` and **every** boundary condition `σ₀`. The cut
cells keep their outside links frozen at `σ₀`; `Q = univ` is the uncut criterion (`cubeBoxSpec_univ`). -/
def WallCutOneBox (T : Tuning) : Prop :=
  ∃ (cell : ∀ k j, LatticeLink 4 (T.side k j) → LatticeLink 4 (coarseSide j)) (c₀ c₁ : ℝ),
    CellGeometry T cell c₀ c₁ ∧
    ∃ (lam γ D₀ : ℝ) (nmax : ℕ), 0 < lam ∧ 0 ≤ γ ∧ γ < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j,
      ∃ (Λ₀ : Finset (FinLatticeSites 4 (coarseSide j))) (κ : FinLatticeSites 4 (coarseSide j) → ℝ),
        1 ≤ Λ₀.card ∧ Λ₀.card ≤ nmax ∧ (∀ u ∈ Λ₀, ∀ u' ∈ Λ₀, (siteDist u u' : ℝ) ≤ D₀) ∧
        (∀ (Q : Finset (LatticeLink 4 (T.side k j))) (σ₀ : GaugeConnection SU2 4 (T.side k j))
          (t : FinLatticeSites 4 (coarseSide j)) (z : LatticeLink 4 (coarseSide j)), z ∉ boxBlock Λ₀ t →
          IsInfluenceBound (boxBlock Λ₀ t) (cubeBoxSpec (cell k j) (T.β k) Q σ₀ (boxBlock Λ₀ t)) z
            (κ (z.site - t))) ∧
        OneBoxSum κ (boxReach Λ₀) Λ₀ lam γ

/-- **Decay under arbitrary boundary conditions in every cube** (the content of Chatterjee's Definition 2.3, in the
form of the region measures of the torus family): one physical rate `m > 0`; for every extent `R` a constant `c` and a
level `k₀` such that for every level `k ≥ k₀`, torus, region `Q` of links, boundary condition `σ₀` outside `Q` and
bounded measurable `F`, `G` (**not** necessarily gauge invariant), `F` of physical extent `≤ R`, at physical
distance `≥ D`: `|Cov_{cubeLaw}(F, G)| ≤ c e^{-mD}`. -/
def CubeDecay (T : Tuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (Q : Finset (LatticeLink 4 (T.side k j))) (σ₀ : GaugeConnection SU2 4 (T.side k j))
    (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink 4 (T.side k j))) (D : ℝ),
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * linkDist e e') →
    |∫ U, F U * G U ∂(cubeLaw (T.β k) Q σ₀) - (∫ U, F U ∂(cubeLaw (T.β k) Q σ₀)) *
        ∫ U, G U ∂(cubeLaw (T.β k) Q σ₀)| ≤ c * Real.exp (-(m * D))

/-- **The wall-cut one-box criterion gives decay under every boundary condition in every cube** (S). Rate `λ/L₁`,
constant `4 n_max/(1 − γ) · 2K_R · 2 · e^{λ(c₀ + D₀)}`, `K_R = 4(2⌊R/L₁ + c₁⌋ + 1)⁴`: the constants of
`fineDecayInv_of_fineOneBox`, uniform also in the region and the boundary condition. -/
theorem cubeDecay_of_wallCutOneBox {T : Tuning} (h : WallCutOneBox T) : CubeDecay T := by
  obtain ⟨cell, c₀, c₁, ⟨geo1, geo2⟩, lam, γ, D₀, nmax, hlam, hγ0, hγ1, k₀, H⟩ := h
  have hL1 := T.L₁_pos
  have hg1 : 0 < 1 - γ := by linarith
  refine ⟨lam / T.L₁, by positivity, fun R => ?_⟩
  set r : ℕ := ⌊R / T.L₁ + c₁⌋₊
  set K : ℝ := ((4 * (2 * r + 1) ^ 4 : ℕ) : ℝ)
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  set c := 4 * (nmax : ℝ) / (1 - γ) * (2 * K) * 2 * Real.exp (lam * (c₀ + D₀))
  have hc : 0 ≤ c := by positivity
  refine ⟨c, hc, k₀, fun k hk j Q σ₀ F G A₀ B₀ D mF mG bF bG dF dG eA hsep => ?_⟩
  obtain ⟨Λ₀, κ, hΛ1, hΛn, hdiam, hinf, hsum⟩ := H k hk j
  set P := cubeLifted (cell k j) (T.β k) Q σ₀ Λ₀ with hP
  have : IsProbabilityMeasure ((cubeLaw (T.β k) Q σ₀).map (cellLift (cell k j) (1 : SU2))) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_cellLift _ _).aemeasurable).2 inferInstance
  have : Nonempty (LatticeLink 4 (coarseSide j)) := ⟨⟨fun _ => 0, 0⟩⟩
  have hbox : IsBoxFamily P.block (fun t (x : LatticeLink 4 (coarseSide j)) => x.site - t) Λ₀ := by
    have := isBoxFamily_torus Λ₀
    exact ⟨this.bij, fun t x => this.mem t x⟩
  have hf : BM (fun W => F (cellProj (cell k j) W)) := ⟨mF.comp (measurable_cellProj _), 1, fun W => bF _⟩
  have hg : BM (fun W => G (cellProj (cell k j) W)) := ⟨mG.comp (measurable_cellProj _), 1, fun W => bG _⟩
  have hvf : OscBound (fun W => F (cellProj (cell k j) W)) (fun _ => (2 : ℝ)) := fun W x s =>
    (abs_sub _ _).trans (by linarith [bF (cellProj (cell k j) W), bF (cellProj (cell k j) (Function.update W x s))])
  have hvg : OscBound (fun W => G (cellProj (cell k j) W)) (fun _ => (2 : ℝ)) := fun W x s =>
    (abs_sub _ _).trans (by linarith [bG (cellProj (cell k j) W), bG (cellProj (cell k j) (Function.update W x s))])
  have hR : ∀ a ∈ A₀.image (cell k j), ∀ s ∈ B₀.image (cell k j), D / T.L₁ - c₀ ≤ linkDist a s := by
    intro a ha s hs
    obtain ⟨e, he, rfl⟩ := mem_image.1 ha
    obtain ⟨e', he', rfl⟩ := mem_image.1 hs
    have h1 := geo1 k j e e'
    have h2 := hsep e he e' he'
    rw [sub_le_iff_le_add, div_le_iff₀ hL1]
    nlinarith
  have hcov := abs_cov_le_of_oneBox_unres P (fun t x => x.site - t) Λ₀ hbox hΛ1 κ (boxReach Λ₀)
    (fun t z hz => hinf Q σ₀ t z hz) (b := 4 * nmax)
    (fun t => (card_boxBlock Λ₀ t).trans (by omega))
    linkDist linkDist_self linkDist_triangle (D₀ := D₀)
    (fun t => boxBlock_diam hdiam t)
    (fun t x y _ hy => boxBlock_reach Λ₀ t x y hy) hlam.le hγ0 hγ1 hsum
    hf hg (depOn_comp_cellProj dF (cell k j)) (depOn_comp_cellProj dG (cell k j)) hvf (by norm_num) hvg hR
  have e := OneScale.Effective.cov_map (cubeLaw (T.β k) Q σ₀) (measurable_cellLift (cell k j) (1 : SU2)) hf hg
  simp only [cellProj_cellLift] at e
  rw [e]
  refine hcov.trans ?_
  have hcard : (((A₀.image (cell k j)).card : ℕ) : ℝ) ≤ K := by
    have hsd : ∀ x ∈ A₀.image (cell k j), ∀ x' ∈ A₀.image (cell k j), siteDist x.site x'.site ≤ r := by
      intro x hx x' hx'
      obtain ⟨e, he, rfl⟩ := mem_image.1 hx
      obtain ⟨e', he', rfl⟩ := mem_image.1 hx'
      have h1 := geo2 k j e e'
      have h2 := eA e he e' he'
      have h3 : linkDist (cell k j e) (cell k j e') ≤ R / T.L₁ + c₁ := by
        rw [div_add' _ _ _ hL1.ne', le_div_iff₀ hL1]; nlinarith
      exact Nat.le_floor (by exact_mod_cast h3)
    have hc := card_le_of_siteDist hsd
    simp only [K]
    exact_mod_cast hc
  rw [Finset.sum_const, nsmul_eq_mul]
  have eexp : Real.exp (-(lam * (D / T.L₁ - c₀ - D₀))) =
      Real.exp (lam * (c₀ + D₀)) * Real.exp (-(lam / T.L₁ * D)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [eexp]
  have hn : ((4 * nmax : ℕ) : ℝ) = 4 * (nmax : ℝ) := by push_cast; ring
  rw [hn]
  have hpre : 0 ≤ 4 * (nmax : ℝ) / (1 - γ) := by positivity
  have hcK : ((A₀.image (cell k j)).card : ℝ) * 2 ≤ 2 * K := by linarith
  calc 4 * (nmax : ℝ) / (1 - γ) * (((A₀.image (cell k j)).card : ℝ) * 2) * 2 *
        (Real.exp (lam * (c₀ + D₀)) * Real.exp (-(lam / T.L₁ * D)))
      ≤ 4 * (nmax : ℝ) / (1 - γ) * (2 * K) * 2 *
        (Real.exp (lam * (c₀ + D₀)) * Real.exp (-(lam / T.L₁ * D))) := by gcongr
    _ = c * Real.exp (-(lam / T.L₁ * D)) := by simp only [c]; ring

/-- **EXTERNAL THEOREM (named, not proved here): Chatterjee's Theorem 2.4.**
S. Chatterjee, *A probabilistic mechanism for quark confinement*, Commun. Math. Phys. 385 (2021), arXiv:2006.16229
(v5): for pure lattice gauge theory on `ℤ^d` with a compact gauge group with non-trivial centre, **Definition 2.3**
(exponential decay of correlations under arbitrary boundary conditions in every cube, constants depending only on the
group, the coupling and `d`) implies, **Theorem 2.4**, unbroken centre symmetry and the area law for rectangular
Wilson loops in a representation that is non-trivial on the centre. (Statement numbers as recorded in
`c7d-onebox-lit/LITERATURE.md`, row 19.)

Here it is transcribed to the objects of this development as an implication, the named premise of the confinement
corollary: `CubeDecay T → AreaLaw T`. **What the transcription adds to the cited statement, to be checked against the
paper:** (i) the cited theorem is in infinite volume and lattice units at one fixed coupling, here the area law is for
limit points of the torus measures along the tuning and in physical units, uniform in the level; (ii) the cited
decay constants are those of Definition 2.3 for one coupling, here they are the level-uniform constants of
`CubeDecay` (with extent-dependent prefactor). Whether the string tension that the paper's proof extracts from the
decay constants survives the physical-unit uniformity is the point to read off the paper. -/
def ChatterjeeTheorem24 (T : Tuning) : Prop := CubeDecay T → ProofPhase.SectorS.AreaLaw T

/-- **The wall-cut one-box criterion implies confinement, given Chatterjee's theorem** (S, modulo the named external
theorem): `WallCutOneBox T` gives `CubeDecay T` (Lean, `cubeDecay_of_wallCutOneBox`), and
`ChatterjeeTheorem24 T` turns it into the area law. -/
theorem areaLaw_of_wallCutOneBox {T : Tuning} (hChat : ChatterjeeTheorem24 T) (h : WallCutOneBox T) :
    ProofPhase.SectorS.AreaLaw T :=
  hChat (cubeDecay_of_wallCutOneBox h)

end ProofPhase.OneBox2
