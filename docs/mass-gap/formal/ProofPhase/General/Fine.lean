/-
Proof phase, generalisation phase 1b: the one-box criterion for the Wilson measure at the physical cell scale, over any
gauge group and dimension (2026-11-24). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 1b.
-/

import ProofPhase.General.CondMass
import ProofPhase.General.Torus
import ProofPhase.OneBox.Fine

/-!
# One box of the Wilson measure at the cell scale, over any gauge group and dimension

`OneBox/Fine` for any `Gr` of the package in dimension `d`: the lattice gauge action link by link (`gaugeAct`), the
criterion `FineOneBox`, the decay statement `FineDecayInv`, and `fineDecayInv_of_fineOneBox` with the constant
`d n_max/(1 − γ) · 2K_R · 2 · e^{λ(c₀ + D₀)}`, `K_R = d (2⌊R/L₁ + c₁⌋ + 1)^d` (the block bound `card_boxBlock` and the
link count `card_le_of_siteDist` of phase 1). The step to `TorusDecayLoc` (`torusDecayLoc_of_fineDecayInv`) and the
assembly `yang_mills_assembly_onebox` are not ported: they need the slab-observable layer and `OnLCP'`, `NonTrivial`
(flux limits, phase 3).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity

open ProofPhase.OneBox (liftAct actInv_comp_cellProj measurable_liftAct)
open ProofPhase.V3 (cellLift cellProj measurable_cellLift measurable_cellProj depOn_comp_cellProj
  cellProj_cellLift)
open ProofPhase.OneBox (IsBoxFamily abs_cov_le_of_oneBox OneBoxSum ActAdm SpecCovariant ActInv IsInfluenceBoundOn)
open ProofPhase.UV

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

section Fine

variable {Gr : Type*} [Group Gr] [TopologicalSpace Gr] [MeasurableSpace Gr] [HasHaarProbability Gr]
  (nr : ℕ) [HasGaugeTrace Gr nr] [GaugeGroupBase Gr] {d : ℕ} [NeZero d]

/-- **The lattice gauge action, link by link**: `U_l ↦ g(l.site) U_l g(l.target)⁻¹`. -/
def gaugeAct (N : ℕ) : GaugeTransform Gr d N → LatticeLink d N → Gr → Gr :=
  fun g l u => g l.site * u * (g l.target)⁻¹

theorem actInv_of_gaugeInvariant {N : ℕ} [NeZero N] {F : GaugeConnection Gr d N → ℝ} (hF : GaugeInvariant F) :
    ActInv (gaugeAct N) F := fun g U => hF g U

theorem measurable_gaugeAct (N : ℕ) (g : GaugeTransform Gr d N) (l : LatticeLink d N) :
    Measurable (gaugeAct N g l) :=
  ((continuous_const.mul continuous_id).mul continuous_const).measurable

section Explicit

variable (Gr) (d)

def FineOneBox (T : Tuning) : Prop :=
  ∃ (cell : ∀ k j, LatticeLink d (T.side k j) → LatticeLink d (coarseSide j)) (c₀ c₁ : ℝ),
    CellGeometry T cell c₀ c₁ ∧
    ∃ (lam γ D₀ : ℝ) (nmax : ℕ), 0 < lam ∧ 0 ≤ γ ∧ γ < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j,
      ∃ (Λ₀ : Finset (FinLatticeSites d (coarseSide j))) (κ : FinLatticeSites d (coarseSide j) → ℝ)
        (P : BlockSpec ((ymLaw (G := Gr) nr d T k j).map (cellLift (cell k j) (1 : Gr))) (FinLatticeSites d (coarseSide j))),
        1 ≤ Λ₀.card ∧ Λ₀.card ≤ nmax ∧ (∀ u ∈ Λ₀, ∀ u' ∈ Λ₀, (siteDist u u' : ℝ) ≤ D₀) ∧
        (∀ t, P.block t = boxBlock Λ₀ t) ∧
        (∀ t, SpecCovariant (liftAct (cell k j) (gaugeAct (T.side k j))) (P.spec t)) ∧
        (∀ t z, z ∉ P.block t →
          IsInfluenceBoundOn (ActAdm (liftAct (cell k j) (gaugeAct (T.side k j))) (P.block t)) (P.block t)
            (P.spec t) z (κ (z.site - t))) ∧
        OneBoxSum κ (boxReach Λ₀) Λ₀ lam γ

def FineDecayInv (T : Tuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection Gr d (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink d (T.side k j))) (D : ℝ),
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * linkDist e e') →
    |∫ U, F U * G U ∂(ymLaw (G := Gr) nr d T k j) - (∫ U, F U ∂(ymLaw (G := Gr) nr d T k j)) * ∫ U, G U ∂(ymLaw (G := Gr) nr d T k j)| ≤ c * Real.exp (-(m * D))

variable [GaugeRep Gr nr]

theorem fineDecayInv_of_fineOneBox {T : Tuning} (h : FineOneBox Gr nr d T) : FineDecayInv Gr nr d T := by
  obtain ⟨cell, c₀, c₁, ⟨geo1, geo2⟩, lam, γ, D₀, nmax, hlam, hγ0, hγ1, k₀, H⟩ := h
  have hL1 := T.L₁_pos
  have hg1 : 0 < 1 - γ := by linarith
  refine ⟨lam / T.L₁, by positivity, fun R => ?_⟩
  set r : ℕ := ⌊R / T.L₁ + c₁⌋₊
  set K : ℝ := ((d * (2 * r + 1) ^ d : ℕ) : ℝ)
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  set c := d * (nmax : ℝ) / (1 - γ) * (2 * K) * 2 * Real.exp (lam * (c₀ + D₀))
  have hc : 0 ≤ c := by positivity
  refine ⟨c, hc, k₀, fun k hk j F G A₀ B₀ D mF mG bF bG gG dF dG eA hsep => ?_⟩
  obtain ⟨Λ₀, κ, P, hΛ1, hΛn, hdiam, hblock, hcovar, hk, hsum⟩ := H k hk j
  have := isProbabilityMeasure_wilsonMeasure (G := Gr) (n := nr) d (T.side k j) (T.β k)
  have : IsProbabilityMeasure ((ymLaw (G := Gr) nr d T k j).map (cellLift (cell k j) (1 : Gr))) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_cellLift _ _).aemeasurable).2 inferInstance
  have : Nonempty (LatticeLink d (coarseSide j)) := ⟨⟨fun _ => 1, ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩⟩
  have hbox : IsBoxFamily P.block (fun t (x : LatticeLink d (coarseSide j)) => x.site - t) Λ₀ := by
    have := isBoxFamily_torus Λ₀
    exact ⟨this.bij, fun t x => by rw [hblock t]; exact this.mem t x⟩
  have hf : BM (fun W => F (cellProj (cell k j) W)) := ⟨mF.comp (measurable_cellProj _), 1, fun W => bF _⟩
  have hg : BM (fun W => G (cellProj (cell k j) W)) := ⟨mG.comp (measurable_cellProj _), 1, fun W => bG _⟩
  have hvf : OscBound (fun W => F (cellProj (cell k j) W)) (fun _ => (2 : ℝ)) := fun W x s =>
    (abs_sub _ _).trans (by linarith [bF (cellProj (cell k j) W), bF (cellProj (cell k j) (Function.update W x s))])
  have hvg : OscBound (fun W => G (cellProj (cell k j) W)) (fun _ => (2 : ℝ)) := fun W x s =>
    (abs_sub _ _).trans (by linarith [bG (cellProj (cell k j) W), bG (cellProj (cell k j) (Function.update W x s))])
  have hgI : ActInv (liftAct (cell k j) (gaugeAct (T.side k j))) (fun W => G (cellProj (cell k j) W)) :=
    actInv_comp_cellProj (actInv_of_gaugeInvariant gG)
  have hR : ∀ a ∈ A₀.image (cell k j), ∀ s ∈ B₀.image (cell k j), D / T.L₁ - c₀ ≤ linkDist a s := by
    intro a ha s hs
    obtain ⟨e, he, rfl⟩ := mem_image.1 ha
    obtain ⟨e', he', rfl⟩ := mem_image.1 hs
    have h1 := geo1 k j e e'
    have h2 := hsep e he e' he'
    rw [sub_le_iff_le_add, div_le_iff₀ hL1]
    nlinarith
  have hcov := abs_cov_le_of_oneBox (a := liftAct (cell k j) (gaugeAct (T.side k j))) P
    (fun t x => x.site - t) Λ₀ hbox hΛ1 (measurable_liftAct _ (measurable_gaugeAct _)) hcovar κ (boxReach Λ₀)
    (fun t z hz => hk t z hz) (b := d * nmax)
    (fun t => by rw [hblock t]; exact (card_boxBlock Λ₀ t).trans (Nat.mul_le_mul_left d hΛn))
    linkDist linkDist_self linkDist_triangle (D₀ := D₀)
    (fun t => by rw [hblock t]; exact boxBlock_diam hdiam t)
    (fun t x y _ hy => by rw [hblock t] at hy; exact boxBlock_reach Λ₀ t x y hy) hlam.le hγ0 hγ1 hsum
    hf hg hgI (depOn_comp_cellProj dF (cell k j)) (depOn_comp_cellProj dG (cell k j)) hvf (by norm_num) hvg hR
  have e := OneScale.Effective.cov_map (ymLaw (G := Gr) nr d T k j) (measurable_cellLift (cell k j) (1 : Gr)) hf hg
  simp only [cellProj_cellLift] at e
  rw [e]
  refine hcov.trans ?_
  -- the cells met by `F`
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

end Fine


/-! ## The SU(2), `d = 4` instances -/

section Instance

theorem gaugeAct_four (N : ℕ) : gaugeAct (Gr := SU2) (d := 4) N = ProofPhase.OneBox.gaugeAct N := rfl

theorem fineOneBox_iff (T : Tuning) : ProofPhase.OneBox.FineOneBox T ↔ FineOneBox SU2 2 4 T := Iff.rfl

theorem fineDecayInv_iff (T : Tuning) : ProofPhase.OneBox.FineDecayInv T ↔ FineDecayInv SU2 2 4 T := Iff.rfl

/-- `ProofPhase.OneBox.fineDecayInv_of_fineOneBox` from the generic theorem at `SU2`, `n = 2`, `d = 4`. -/
theorem fineDecayInv_of_fineOneBox_su2 {T : Tuning} (h : ProofPhase.OneBox.FineOneBox T) :
    ProofPhase.OneBox.FineDecayInv T :=
  fineDecayInv_of_fineOneBox SU2 2 4 h

example : @ProofPhase.OneBox.fineDecayInv_of_fineOneBox = @fineDecayInv_of_fineOneBox_su2 := rfl

end Instance

end ProofPhase.General
