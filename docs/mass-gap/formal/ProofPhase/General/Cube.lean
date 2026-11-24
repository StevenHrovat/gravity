/-
Proof phase, generalisation phase 1b: boxes cut by the walls of cubes, over any gauge group and dimension (2026-11-24).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 1b.
-/

import ProofPhase.General.Anchor
import ProofPhase.OneBox2.Cube

/-!
# Wall-cut one-box criterion and cube decay, over any gauge group and dimension

`OneBox2/Cube` for any `Gr` of the package in dimension `d`: the cube law (`cubeLaw`: the Wilson measure on the links of
`Q` with the others frozen), the cut kernels (`cutSpec`, `cubeBoxSpec`), their lift to cells (`cubeLifted`), the
criterion `WallCutOneBox`, the decay statement `CubeDecay` and `cubeDecay_of_wallCutOneBox` with the cell count
`K_R = d (2⌊R/L₁ + c₁⌋ + 1)^d`. The group-free lemmas of `Cube.lean` (`splice_splice_same`, `splice_comm_sub`,
`abs_cov_le_of_oneBox_unres`, `localWeight_comp_splice`) are reused. `ChatterjeeTheorem24` and `areaLaw_of_wallCutOneBox`
are not ported: they name the SU(2) area law of the transfer-matrix layer (`SectorS.AreaLaw`).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist

open ProofPhase.OneBox (liftAct OneBoxSum ActAdm ActInv SpecCovariant IsBoxFamily)
open ProofPhase.OneBox2 (liftMap liftSpec liftBlockSpec liftSpec_covariant splice_splice_same splice_comm_sub measurable_integral_spec liftMap_eq_full
  abs_cov_le_of_oneBox_unres localWeight_comp_splice)
open ProofPhase.V3 (cellLift cellProj measurable_cellLift measurable_cellProj depOn_comp_cellProj cellProj_cellLift)

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

section Cube

variable {Gr : Type*} [Group Gr] [TopologicalSpace Gr] [MeasurableSpace Gr] [HasHaarProbability Gr]
  (nr : ℕ) [HasGaugeTrace Gr nr] [GaugeGroupBase Gr] [GaugeRep Gr nr] {d : ℕ} [NeZero d]

section Region

variable {N : ℕ} [NeZero N]

def cubeLaw (β : ℝ) (Q : Finset (LatticeLink d N)) (σ₀ : GaugeConnection Gr d N) :
    Measure (GaugeConnection Gr d N) :=
  (gaugeSpec (G := Gr) (d := d) (N := N) nr (wilsonWeight β) Q σ₀).map (splice Q σ₀)

def cutSpec (β : ℝ) (Q : Finset (LatticeLink d N)) (σ₀ : GaugeConnection Gr d N) (B : Finset (LatticeLink d N))
    (τ : GaugeConnection Gr d N) : Measure (GaugeConnection Gr d N) :=
  gaugeSpec (G := Gr) (d := d) (N := N) nr (wilsonWeight β) B (splice Q σ₀ τ)

theorem localWeight_wilsonBlock (β : ℝ) (B : Finset (LatticeLink d N)) :
    LocalWeight (plaqProd (G := Gr) (d := d) (N := N) nr (wilsonWeight β) (touching B)) :=
  localWeight_plaqProd GaugeRep.continuous_rep GaugeRep.unitary_rep (posWeight_wilson nr β) _

instance isProbabilityMeasure_cubeLaw (β : ℝ) (Q : Finset (LatticeLink d N)) (σ₀ : GaugeConnection Gr d N) :
    IsProbabilityMeasure (cubeLaw nr β Q σ₀) := by
  have := (localWeight_wilsonBlock nr β Q).isProbabilityMeasure_locSpec (ν := haarG Gr) (B := Q) σ₀
  exact (Measure.isProbabilityMeasure_map_iff (measurable_splice_right Q σ₀).aemeasurable).2
    (by unfold gaugeSpec; exact this)

theorem locSpec_cut {B Q : Finset (LatticeLink d N)} (hBQ : B ⊆ Q) (W : GaugeConnection Gr d N → ℝ)
    (σ₀ ξ : GaugeConnection Gr d N) :
    locSpec (haarG Gr) B (fun ζ => W (splice Q σ₀ ζ)) ξ = locSpec (haarG Gr) B W (splice Q σ₀ ξ) := by
  unfold locSpec locZ
  simp_rw [← splice_comm_sub hBQ]

theorem xp_cut_splice {B : Finset (LatticeLink d N)} {p : LatticePlaquette d N} (hp : ¬∃ l ∈ plaqLinks p, l ∈ B)
    (Q : Finset (LatticeLink d N)) (σ₀ σ ξ : GaugeConnection Gr d N) :
    xp nr p (splice Q σ₀ (splice B σ ξ)) = xp nr p (splice Q σ₀ σ) := by
  unfold xp
  congr 1
  refine plaquetteHolonomy_dependsOn p _ _ fun l hl => ?_
  have : l ∉ B := fun h => hp ⟨l, hl, h⟩
  by_cases hQ : l ∈ Q <;> simp [splice, hQ, this]

instance isProbabilityMeasure_cutSpec (β : ℝ) (Q : Finset (LatticeLink d N)) (σ₀ : GaugeConnection Gr d N)
    (B : Finset (LatticeLink d N)) (τ : GaugeConnection Gr d N) : IsProbabilityMeasure (cutSpec nr β Q σ₀ B τ) :=
  (localWeight_wilsonBlock nr β B).isProbabilityMeasure_locSpec (ν := haarG Gr) (B := B) (splice Q σ₀ τ)

theorem measurable_cutSpec (β : ℝ) (Q : Finset (LatticeLink d N)) (σ₀ : GaugeConnection Gr d N)
    (B : Finset (LatticeLink d N)) : Measurable (cutSpec nr β Q σ₀ B) :=
  (measurable_gaugeSpec nr β B).comp (measurable_splice_right Q σ₀)

theorem measurable_blockAvg_cut (β : ℝ) (Q : Finset (LatticeLink d N)) (σ₀ : GaugeConnection Gr d N)
    (B : Finset (LatticeLink d N)) {h : GaugeConnection Gr d N → ℝ} (hh : BM h) :
    Measurable (blockAvg B (cutSpec nr β Q σ₀ B) h) := by
  have e : blockAvg B (cutSpec nr β Q σ₀ B) h = fun τ =>
      ∫ ξ, (fun p : GaugeConnection Gr d N × GaugeConnection Gr d N => h (splice B p.1 p.2)) (τ, ξ)
        ∂(cutSpec nr β Q σ₀ B τ) := rfl
  rw [e]
  exact measurable_integral_spec (q := cutSpec nr β Q σ₀ B) (measurable_cutSpec nr β Q σ₀ B)
    (hh.meas.comp (measurable_splice B))

theorem integral_cubeLaw (β : ℝ) (Q : Finset (LatticeLink d N)) (σ₀ : GaugeConnection Gr d N)
    {g : GaugeConnection Gr d N → ℝ} (hg : Measurable g) :
    ∫ τ, g τ ∂(cubeLaw nr β Q σ₀) =
      ∫ ξ, g (splice Q σ₀ ξ) ∂(locSpec (haarG Gr) Q (plaqProd (G := Gr) (d := d) (N := N) nr (wilsonWeight β)
        (touching Q)) σ₀) :=
  integral_map (measurable_splice_right Q σ₀).aemeasurable hg.aestronglyMeasurable

def cubeBlockSpec (β : ℝ) (Q : Finset (LatticeLink d N)) (σ₀ : GaugeConnection Gr d N) {J : Type*}
    (Bf : J → Finset (LatticeLink d N)) (hBQ : ∀ j, Bf j ⊆ Q) : BlockSpec (cubeLaw nr β Q σ₀) J where
  block := Bf
  spec j := cutSpec nr β Q σ₀ (Bf j)
  isProb j τ := isProbabilityMeasure_cutSpec nr β Q σ₀ (Bf j) τ
  spec_congr j τ τ' h := by
    unfold cutSpec gaugeSpec
    exact (localWeight_wilsonBlock nr β (Bf j)).locSpec_congr _ _ (fun i hi => by
      by_cases hQ : i ∈ Q <;> simp [splice, hQ, h i hi])
  meas_avg j h hh := measurable_blockAvg_cut nr β Q σ₀ (Bf j) hh
  dlr j h hh := by
    set B := Bf j with hBdef
    have hBQ' : B ⊆ Q := hBQ j
    set φ := wilsonWeight β
    set WQ := plaqProd (G := Gr) (d := d) (N := N) nr φ (touching Q)
    set WB := plaqProd (G := Gr) (d := d) (N := N) nr φ (touching B)
    have hWQ : LocalWeight (fun ζ => WQ (splice Q σ₀ ζ)) := localWeight_comp_splice (localWeight_wilsonBlock nr β Q) Q σ₀
    have hWB : LocalWeight (fun ζ => WB (splice Q σ₀ ζ)) := localWeight_comp_splice (localWeight_wilsonBlock nr β B) Q σ₀
    set Rf : GaugeConnection Gr d N → ℝ := fun ζ =>
      ∏ p ∈ touching Q \ touching B, φ (xp nr p (splice Q σ₀ ζ)) with hRf
    have hRB : ∀ σ ξ, Rf (splice B σ ξ) = Rf σ := by
      intro σ ξ
      simp only [hRf]
      refine prod_congr rfl fun p hp => ?_
      have hpB : ¬∃ l ∈ plaqLinks p, l ∈ B := by
        intro h'
        have := (mem_sdiff.1 hp).2
        simp only [touching, mem_filter, mem_univ, true_and] at this
        exact this h'
      rw [xp_cut_splice nr hpB]
    have hsub : touching B ⊆ touching Q := by
      intro p hp
      simp only [touching, mem_filter, mem_univ, true_and] at hp ⊢
      obtain ⟨l, hl, hlB⟩ := hp
      exact ⟨l, hl, hBQ' hlB⟩
    have hW : ∀ ζ, WQ (splice Q σ₀ ζ) = WB (splice Q σ₀ ζ) * Rf ζ := by
      intro ζ
      simp only [WQ, WB, plaqProd, hRf]
      rw [mul_comm, prod_sdiff hsub]
    have hlocQ : locSpec (haarG Gr) Q WQ σ₀ = weightMeasure (haarG Gr) (fun ζ => WQ (splice Q σ₀ ζ)) := rfl
    have hb : ∀ ξ, blockAvg B (cutSpec nr β Q σ₀ B) h (splice Q σ₀ ξ) =
        blockAvg B (locSpec (haarG Gr) B (fun ζ => WB (splice Q σ₀ ζ))) (fun ζ => h (splice Q σ₀ ζ)) ξ := by
      intro ξ
      unfold blockAvg cutSpec gaugeSpec
      rw [splice_splice_same, locSpec_cut hBQ' WB σ₀ ξ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
      simp only [splice_comm_sub hBQ']
    have hhs : BM (fun ζ => h (splice Q σ₀ ζ)) :=
      ⟨hh.meas.comp (measurable_splice_right Q σ₀), hh.bdd.imp fun C hC ζ => hC _⟩
    rw [integral_cubeLaw nr β Q σ₀ ((measurable_blockAvg_cut nr β Q σ₀ B hh)), integral_cubeLaw nr β Q σ₀ hh.meas, hlocQ]
    simp_rw [hb]
    exact dlr_locSpec hWB hRB hW hWQ.bm (fun ζ => (hWQ.pos ζ).le) hhs

end Region

section Lift

variable (Gr) [T2Space Gr] {N M : ℕ} [NeZero N] [NeZero M]

def cutPre (Q : Finset (LatticeLink d N)) (cell : LatticeLink d N → LatticeLink d M) (b : Finset (LatticeLink d M)) :
    Finset (LatticeLink d N) := Q ∩ cellPre cell b

def cubeBoxSpec (cell : LatticeLink d N → LatticeLink d M) (β : ℝ) (Q : Finset (LatticeLink d N))
    (σ₀ : GaugeConnection Gr d N) (b : Finset (LatticeLink d M)) :
    (LatticeLink d M → (LatticeLink d N → Gr)) → Measure (LatticeLink d M → (LatticeLink d N → Gr)) :=
  liftSpec cell (1 : Gr) b (cutPre Q cell b) σ₀ (cutSpec nr β Q σ₀ (cutPre Q cell b))

def cubeLifted (cell : LatticeLink d N → LatticeLink d M) (β : ℝ) (Q : Finset (LatticeLink d N))
    (σ₀ : GaugeConnection Gr d N) (Λ₀ : Finset (FinLatticeSites d M)) :
    BlockSpec ((cubeLaw nr β Q σ₀).map (cellLift cell (1 : Gr))) (FinLatticeSites d M) :=
  liftBlockSpec
    (cubeBlockSpec nr β Q σ₀ (fun t => cutPre Q cell (boxBlock Λ₀ t)) (fun t => inter_subset_left))
    cell (1 : Gr) (boxBlock Λ₀) σ₀
    (fun t e he => mem_cellPre.1 (mem_inter.1 he).2)
    (fun t => measurable_cutSpec nr β Q σ₀ _)
    (fun t σ σ' h => by
      show cutSpec nr β Q σ₀ _ σ = cutSpec nr β Q σ₀ _ σ'
      unfold cutSpec gaugeSpec
      refine (localWeight_wilsonBlock nr β _).locSpec_congr _ _ (fun i hi => ?_)
      by_cases hQ : i ∈ Q
      · have : cell i ∉ boxBlock Λ₀ t := fun hc => hi (mem_inter.2 ⟨hQ, mem_cellPre.2 hc⟩)
        simp [splice, hQ, h i this]
      · simp [splice, hQ])
    (fun t => by
      have hS : MeasurableSet {U : GaugeConnection Gr d N |
          ∀ e, cell e ∈ boxBlock Λ₀ t → e ∉ cutPre Q cell (boxBlock Λ₀ t) → U e = σ₀ e} := by
        have : {U : GaugeConnection Gr d N |
            ∀ e, cell e ∈ boxBlock Λ₀ t → e ∉ cutPre Q cell (boxBlock Λ₀ t) → U e = σ₀ e} =
            ⋂ e, {U | cell e ∈ boxBlock Λ₀ t → e ∉ cutPre Q cell (boxBlock Λ₀ t) → U e = σ₀ e} := by
          ext U; simp
        rw [this]
        refine MeasurableSet.iInter fun e => ?_
        by_cases h : cell e ∈ boxBlock Λ₀ t ∧ e ∉ cutPre Q cell (boxBlock Λ₀ t)
        · have : {U : GaugeConnection Gr d N | cell e ∈ boxBlock Λ₀ t → e ∉ cutPre Q cell (boxBlock Λ₀ t) →
              U e = σ₀ e} = {U | U e = σ₀ e} := by
            ext U; simp [h.1, h.2]
          rw [this]
          exact measurableSet_eq_fun (measurable_pi_apply e) measurable_const
        · have : {U : GaugeConnection Gr d N | cell e ∈ boxBlock Λ₀ t → e ∉ cutPre Q cell (boxBlock Λ₀ t) →
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

theorem cubeLifted_block (cell : LatticeLink d N → LatticeLink d M) (β : ℝ) (Q : Finset (LatticeLink d N))
    (σ₀ : GaugeConnection Gr d N) (Λ₀ : Finset (FinLatticeSites d M)) (t : FinLatticeSites d M) :
    (cubeLifted Gr nr cell β Q σ₀ Λ₀).block t = boxBlock Λ₀ t := rfl

theorem cubeLifted_spec (cell : LatticeLink d N → LatticeLink d M) (β : ℝ) (Q : Finset (LatticeLink d N))
    (σ₀ : GaugeConnection Gr d N) (Λ₀ : Finset (FinLatticeSites d M)) (t : FinLatticeSites d M) :
    (cubeLifted Gr nr cell β Q σ₀ Λ₀).spec t = cubeBoxSpec Gr nr cell β Q σ₀ (boxBlock Λ₀ t) := rfl

theorem cubeBoxSpec_univ (cell : LatticeLink d N → LatticeLink d M) (β : ℝ) (σ₀ : GaugeConnection Gr d N)
    (b : Finset (LatticeLink d M)) : cubeBoxSpec Gr nr cell β univ σ₀ b = wilsonBoxSpec Gr nr cell β b := by
  have hpre : cutPre univ cell b = cellPre cell b := by unfold cutPre; exact univ_inter _
  have hspl : ∀ τ : GaugeConnection Gr d N, splice univ σ₀ τ = τ := fun τ => by
    funext i; simp [splice]
  have hBf : ∀ e, e ∈ cellPre cell b ↔ cell e ∈ b := fun e => mem_cellPre
  funext W
  unfold cubeBoxSpec wilsonBoxSpec liftSpec
  rw [hpre]
  have e1 : cutSpec nr β univ σ₀ (cellPre cell b) (cellProj cell W) =
      gaugeSpec (G := Gr) (d := d) (N := N) nr (wilsonWeight β) (cellPre cell b) (cellProj cell W) := by
    unfold cutSpec; rw [hspl]
  rw [e1]
  have e2 : liftMap cell (1 : Gr) b (cellPre cell b) σ₀ W =
      liftMap cell (1 : Gr) b (cellPre cell b) (fun _ => 1) W := by
    funext U'
    rw [liftMap_eq_full cell 1 b _ σ₀ hBf, liftMap_eq_full cell 1 b _ _ hBf]
  rw [e2]

end Lift

section Explicit

variable (Gr) (d) [T2Space Gr]

def WallCutOneBox (T : Tuning) : Prop :=
  ∃ (cell : ∀ k j, LatticeLink d (T.side k j) → LatticeLink d (coarseSide j)) (c₀ c₁ : ℝ),
    CellGeometry T cell c₀ c₁ ∧
    ∃ (lam γ D₀ : ℝ) (nmax : ℕ), 0 < lam ∧ 0 ≤ γ ∧ γ < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j,
      ∃ (Λ₀ : Finset (FinLatticeSites d (coarseSide j))) (κ : FinLatticeSites d (coarseSide j) → ℝ),
        1 ≤ Λ₀.card ∧ Λ₀.card ≤ nmax ∧ (∀ u ∈ Λ₀, ∀ u' ∈ Λ₀, (siteDist u u' : ℝ) ≤ D₀) ∧
        (∀ (Q : Finset (LatticeLink d (T.side k j))) (σ₀ : GaugeConnection Gr d (T.side k j))
          (t : FinLatticeSites d (coarseSide j)) (z : LatticeLink d (coarseSide j)), z ∉ boxBlock Λ₀ t →
          IsInfluenceBound (boxBlock Λ₀ t) (cubeBoxSpec Gr nr (cell k j) (T.β k) Q σ₀ (boxBlock Λ₀ t)) z
            (κ (z.site - t))) ∧
        OneBoxSum κ (boxReach Λ₀) Λ₀ lam γ

def CubeDecay (T : Tuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (Q : Finset (LatticeLink d (T.side k j))) (σ₀ : GaugeConnection Gr d (T.side k j))
    (F G : GaugeConnection Gr d (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink d (T.side k j))) (D : ℝ),
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * linkDist e e') →
    |∫ U, F U * G U ∂(cubeLaw nr (T.β k) Q σ₀) - (∫ U, F U ∂(cubeLaw nr (T.β k) Q σ₀)) *
        ∫ U, G U ∂(cubeLaw nr (T.β k) Q σ₀)| ≤ c * Real.exp (-(m * D))

theorem cubeDecay_of_wallCutOneBox {T : Tuning} (h : WallCutOneBox Gr nr d T) : CubeDecay Gr nr d T := by
  obtain ⟨cell, c₀, c₁, ⟨geo1, geo2⟩, lam, γ, D₀, nmax, hlam, hγ0, hγ1, k₀, H⟩ := h
  have hL1 := T.L₁_pos
  have hg1 : 0 < 1 - γ := by linarith
  refine ⟨lam / T.L₁, by positivity, fun R => ?_⟩
  set r : ℕ := ⌊R / T.L₁ + c₁⌋₊
  set K : ℝ := ((d * (2 * r + 1) ^ d : ℕ) : ℝ)
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  set c := d * (nmax : ℝ) / (1 - γ) * (2 * K) * 2 * Real.exp (lam * (c₀ + D₀))
  have hc : 0 ≤ c := by positivity
  refine ⟨c, hc, k₀, fun k hk j Q σ₀ F G A₀ B₀ D mF mG bF bG dF dG eA hsep => ?_⟩
  obtain ⟨Λ₀, κ, hΛ1, hΛn, hdiam, hinf, hsum⟩ := H k hk j
  set P := cubeLifted Gr nr (cell k j) (T.β k) Q σ₀ Λ₀ with hP
  have : IsProbabilityMeasure ((cubeLaw nr (T.β k) Q σ₀).map (cellLift (cell k j) (1 : Gr))) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_cellLift _ _).aemeasurable).2 inferInstance
  have : Nonempty (LatticeLink d (coarseSide j)) := ⟨⟨fun _ => 1, ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩⟩
  have hbox : IsBoxFamily P.block (fun t (x : LatticeLink d (coarseSide j)) => x.site - t) Λ₀ := by
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
    (fun t z hz => hinf Q σ₀ t z hz) (b := d * nmax)
    (fun t => (card_boxBlock Λ₀ t).trans (Nat.mul_le_mul_left d hΛn))
    linkDist linkDist_self linkDist_triangle (D₀ := D₀)
    (fun t => boxBlock_diam hdiam t)
    (fun t x y _ hy => boxBlock_reach Λ₀ t x y hy) hlam.le hγ0 hγ1 hsum
    hf hg (depOn_comp_cellProj dF (cell k j)) (depOn_comp_cellProj dG (cell k j)) hvf (by norm_num) hvg hR
  have e := OneScale.Effective.cov_map (cubeLaw nr (T.β k) Q σ₀) (measurable_cellLift (cell k j) (1 : Gr)) hf hg
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
  have hn : ((d * nmax : ℕ) : ℝ) = d * (nmax : ℝ) := by push_cast; ring
  rw [hn]
  have hpre : 0 ≤ d * (nmax : ℝ) / (1 - γ) := by positivity
  have hcK : ((A₀.image (cell k j)).card : ℝ) * 2 ≤ 2 * K := by linarith
  calc d * (nmax : ℝ) / (1 - γ) * (((A₀.image (cell k j)).card : ℝ) * 2) * 2 *
        (Real.exp (lam * (c₀ + D₀)) * Real.exp (-(lam / T.L₁ * D)))
      ≤ d * (nmax : ℝ) / (1 - γ) * (2 * K) * 2 *
        (Real.exp (lam * (c₀ + D₀)) * Real.exp (-(lam / T.L₁ * D))) := by gcongr
    _ = c * Real.exp (-(lam / T.L₁ * D)) := by simp only [c]; ring

end Explicit

end Cube


/-! ## The SU(2), `d = 4` instances -/

section Instance

variable {N M : ℕ} [NeZero N] [NeZero M]

theorem cubeLaw_four (β : ℝ) (Q : Finset (LatticeLink 4 N)) (σ₀ : GaugeConnection SU2 4 N) :
    cubeLaw (Gr := SU2) 2 β Q σ₀ = ProofPhase.OneBox2.cubeLaw β Q σ₀ := rfl

theorem cubeBoxSpec_four (cell : LatticeLink 4 N → LatticeLink 4 M) (β : ℝ) (Q : Finset (LatticeLink 4 N))
    (σ₀ : GaugeConnection SU2 4 N) (b : Finset (LatticeLink 4 M)) :
    cubeBoxSpec SU2 2 cell β Q σ₀ b = ProofPhase.OneBox2.cubeBoxSpec cell β Q σ₀ b := rfl

theorem wallCutOneBox_iff (T : Tuning) : ProofPhase.OneBox2.WallCutOneBox T ↔ WallCutOneBox SU2 2 4 T := Iff.rfl

theorem cubeDecay_iff (T : Tuning) : ProofPhase.OneBox2.CubeDecay T ↔ CubeDecay SU2 2 4 T := Iff.rfl

/-- `ProofPhase.OneBox2.cubeDecay_of_wallCutOneBox` from the generic theorem at `SU2`, `n = 2`, `d = 4`. -/
theorem cubeDecay_of_wallCutOneBox_su2 {T : Tuning} (h : ProofPhase.OneBox2.WallCutOneBox T) :
    ProofPhase.OneBox2.CubeDecay T :=
  cubeDecay_of_wallCutOneBox SU2 2 4 h

example : @ProofPhase.OneBox2.cubeDecay_of_wallCutOneBox = @cubeDecay_of_wallCutOneBox_su2 := rfl

end Instance

end ProofPhase.General
