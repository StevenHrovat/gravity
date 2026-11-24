/-
Proof phase, cycle 7, workstream 1 (c7c-onebox): the one-box criterion for the Wilson measure itself, at the physical
cell scale, gauge-correct; the route that needs no blocking and no ultraviolet transfer (2026-11-22). Released under
Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c7c-onebox/NOTE.md`, sections 1 to 4.
-/

import ProofPhase.OneBox.Torus

/-!
# One box of the Wilson measure, at the physical cell scale

**Cells.** As in `V3.CondMass`: every fine link belongs to the cell of one coarse link (`cell k j`), cells have
physical size `L₁` (`V3.CellGeometry`), and the fine configuration is regrouped into one super-site value per cell
(`V3.cellLift`). The criterion is stated for the **unconditioned** SU(2) Wilson measure lifted to cells.

**Gauge.** The gauge group acts link by link (`gaugeAct`: `U_l ↦ g(l.site) U_l g(l.target)⁻¹`), hence cell by cell on
super-sites (`liftAct`). The box influences are tested only on gauge-invariant functions of the box with frozen
boundary (`ActAdm`), and the box specification is gauge covariant (`SpecCovariant`, true for the DLR specification of
the Wilson action with Haar prior). The conclusion is decay for gauge-invariant observables (`FineDecayInv`), which is
all that the slab correlations consume (`SlabObs.gauge`).

**The criterion** (`FineOneBox T`, gap strength, the open input of this route): from some level on, in every volume,
the lifted Wilson measure has a gauge-covariant block specification whose blocks are the translates of one box `Λ₀` of
coarse sites (at most `n_max` sites, diameter `≤ D₀`), with gauge-invariant box influences `κ(u)` from the relative
outside positions `u`, and the one-box sum `∑_{u ∉ Λ₀} κ(u) e^{λ Ê(u)} ≤ γ|Λ₀|`, `γ < 1`; all constants uniform.

**The theorems.**
* `fineDecayInv_of_fineOneBox` (S): `FineOneBox ⇒ FineDecayInv` (covariance of bounded observables, the second one gauge
  invariant, of physical extent `≤ R` at physical distance `≥ D`, is `≤ c_R e^{−(λ/L₁) D}`, uniformly in level, volume and
  the number of fine links).
* `torusDecayLoc_of_fineDecayInv` (S): `FineDecayInv ⇒ TorusDecayLoc`.
* **`yang_mills_assembly_onebox`** (S): `OnLCP' ∧ NonTrivial ∧ FineOneBox ⇒ TorusDecayLoc ∧ MassGapLoc ∧ MassGapMFLoc ∧
  LimitRP ∧ NonTrivial`. No blocking family and no ultraviolet transfer (`ObsTransferPhysTW`) are needed: the one-box
  criterion at the physical cell scale, uniform in the level, carries both.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity ProofPhase.Torus ProofPhase.V3 ProofPhase.V4 ProofPhase.RouteA

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.OneBox

/-! ## The gauge action, link by link and cell by cell -/

section Lift

variable {L C S : Type*} [Fintype C] [DecidableEq C] [MeasurableSpace S] {Γ : Type*}

/-- The action on super-sites: the cell `c` acts on its own links. -/
def liftAct (cell : L → C) (α : Γ → L → S → S) : Γ → C → (L → S) → (L → S) :=
  fun γ c w e => if cell e = c then α γ e (w e) else w e

theorem cellProj_act (cell : L → C) (α : Γ → L → S → S) (γ : Γ) (W : C → (L → S)) :
    cellProj cell (act (liftAct cell α) γ W) = act α γ (cellProj cell W) := by
  funext e; simp [cellProj, act, liftAct]

theorem actInv_comp_cellProj [Fintype L] [DecidableEq L] {cell : L → C} {α : Γ → L → S → S} {F : (L → S) → ℝ}
    (hF : ActInv α F) : ActInv (liftAct cell α) (fun W => F (cellProj cell W)) := by
  intro γ W
  show F (cellProj cell (act (liftAct cell α) γ W)) = F (cellProj cell W)
  rw [cellProj_act, hF]

theorem measurable_liftAct (cell : L → C) {α : Γ → L → S → S} (hα : ∀ γ e, Measurable (α γ e)) (γ : Γ) (c : C) :
    Measurable (liftAct cell α γ c) := by
  refine measurable_pi_iff.mpr fun e => ?_
  by_cases h : cell e = c
  · simp only [liftAct, h, ↓reduceIte]; exact (hα γ e).comp (measurable_pi_apply e)
  · simp only [liftAct, h, ↓reduceIte]; exact measurable_pi_apply e

end Lift

/-- **The lattice gauge action, link by link**: `U_l ↦ g(l.site) U_l g(l.target)⁻¹`. -/
def gaugeAct (N : ℕ) : GaugeTransform SU2 4 N → LatticeLink 4 N → SU2 → SU2 :=
  fun g l u => g l.site * u * (g l.target)⁻¹

theorem actInv_of_gaugeInvariant {N : ℕ} [NeZero N] {F : GaugeConnection SU2 4 N → ℝ} (hF : GaugeInvariant F) :
    ActInv (gaugeAct N) F := fun g U => hF g U

theorem measurable_gaugeAct (N : ℕ) (g : GaugeTransform SU2 4 N) (l : LatticeLink 4 N) :
    Measurable (gaugeAct N g l) :=
  ((continuous_const.mul continuous_id).mul continuous_const).measurable

/-! ## The criterion -/

/-- **The one-box criterion for the Wilson measure at the physical cell scale (gap strength; named, open).** Cells of
physical size `L₁` (`CellGeometry`), constants `λ > 0`, `0 ≤ γ < 1`, `D₀`, `n_max` and a level `k₀`; for every level
`k ≥ k₀` and volume `j`: a box `Λ₀` of at most `n_max` coarse sites with diameter `≤ D₀`, influence numbers `κ` on the
relative positions, and a block specification `P` of the lifted Wilson measure such that the blocks of `P` are the
translates of `Λ₀`, `P` is gauge covariant, the influence of the outside cell `z` on the block `t`, **tested on
gauge-invariant functions of the box with frozen boundary**, is `≤ κ(z.site − t)`, and the one-box sum holds. -/
def FineOneBox (T : Tuning) : Prop :=
  ∃ (cell : ∀ k j, LatticeLink 4 (T.side k j) → LatticeLink 4 (coarseSide j)) (c₀ c₁ : ℝ),
    CellGeometry T cell c₀ c₁ ∧
    ∃ (lam γ D₀ : ℝ) (nmax : ℕ), 0 < lam ∧ 0 ≤ γ ∧ γ < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j,
      ∃ (Λ₀ : Finset (FinLatticeSites 4 (coarseSide j))) (κ : FinLatticeSites 4 (coarseSide j) → ℝ)
        (P : BlockSpec ((T.ym k j).map (cellLift (cell k j) (1 : SU2))) (FinLatticeSites 4 (coarseSide j))),
        1 ≤ Λ₀.card ∧ Λ₀.card ≤ nmax ∧ (∀ u ∈ Λ₀, ∀ u' ∈ Λ₀, (siteDist u u' : ℝ) ≤ D₀) ∧
        (∀ t, P.block t = boxBlock Λ₀ t) ∧
        (∀ t, SpecCovariant (liftAct (cell k j) (gaugeAct (T.side k j))) (P.spec t)) ∧
        (∀ t z, z ∉ P.block t →
          IsInfluenceBoundOn (ActAdm (liftAct (cell k j) (gaugeAct (T.side k j))) (P.block t)) (P.block t)
            (P.spec t) z (κ (z.site - t))) ∧
        OneBoxSum κ (boxReach Λ₀) Λ₀ lam γ

/-- **Decay of the Wilson measure for gauge-invariant observables of bounded physical extent**, uniform in level and
volume: one rate `m > 0`; for every extent `R` a constant `c` and a level `k₀`; for bounded measurable `F`, `G` with `G`
gauge invariant, `F` of physical extent `≤ R`, at physical distance `≥ D`: `|Cov(F, G)| ≤ c e^{−mD}`. -/
def FineDecayInv (T : Tuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink 4 (T.side k j))) (D : ℝ),
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * linkDist e e') →
    |∫ U, F U * G U ∂(T.ym k j) - (∫ U, F U ∂(T.ym k j)) * ∫ U, G U ∂(T.ym k j)| ≤ c * Real.exp (-(m * D))

/-- **One box of the Wilson measure gives decay in every volume, uniformly in the level** (S). Rate `λ/L₁`, constant
`4 n_max/(1 − γ) · 2K_R · 2 · e^{λ(c₀ + D₀)}` with `K_R = 4(2⌊R/L₁ + c₁⌋ + 1)⁴`. -/
theorem fineDecayInv_of_fineOneBox {T : Tuning} (h : FineOneBox T) : FineDecayInv T := by
  obtain ⟨cell, c₀, c₁, ⟨geo1, geo2⟩, lam, γ, D₀, nmax, hlam, hγ0, hγ1, k₀, H⟩ := h
  have hL1 := T.L₁_pos
  have hg1 : 0 < 1 - γ := by linarith
  refine ⟨lam / T.L₁, by positivity, fun R => ?_⟩
  set r : ℕ := ⌊R / T.L₁ + c₁⌋₊
  set K : ℝ := ((4 * (2 * r + 1) ^ 4 : ℕ) : ℝ)
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  set c := 4 * (nmax : ℝ) / (1 - γ) * (2 * K) * 2 * Real.exp (lam * (c₀ + D₀))
  have hc : 0 ≤ c := by positivity
  refine ⟨c, hc, k₀, fun k hk j F G A₀ B₀ D mF mG bF bG gG dF dG eA hsep => ?_⟩
  obtain ⟨Λ₀, κ, P, hΛ1, hΛn, hdiam, hblock, hcovar, hk, hsum⟩ := H k hk j
  have := UV.ymProb T k j
  have : IsProbabilityMeasure ((T.ym k j).map (cellLift (cell k j) (1 : SU2))) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_cellLift _ _).aemeasurable).2 inferInstance
  have : Nonempty (LatticeLink 4 (coarseSide j)) := ⟨⟨fun _ => 0, 0⟩⟩
  have hbox : IsBoxFamily P.block (fun t (x : LatticeLink 4 (coarseSide j)) => x.site - t) Λ₀ := by
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
    (fun t z hz => hk t z hz) (b := 4 * nmax)
    (fun t => by rw [hblock t]; exact (card_boxBlock Λ₀ t).trans (by omega))
    linkDist linkDist_self linkDist_triangle (D₀ := D₀)
    (fun t => by rw [hblock t]; exact boxBlock_diam hdiam t)
    (fun t x y _ hy => by rw [hblock t] at hy; exact boxBlock_reach Λ₀ t x y hy) hlam.le hγ0 hγ1 hsum
    hf hg hgI (depOn_comp_cellProj dF (cell k j)) (depOn_comp_cellProj dG (cell k j)) hvf (by norm_num) hvg hR
  have e := OneScale.Effective.cov_map (T.ym k j) (measurable_cellLift (cell k j) (1 : SU2)) hf hg
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
  have hn : ((4 * nmax : ℕ) : ℝ) = 4 * (nmax : ℝ) := by push_cast; ring
  rw [hn]
  have hpre : 0 ≤ 4 * (nmax : ℝ) / (1 - γ) := by positivity
  have hcK : ((A₀.image (cell k j)).card : ℝ) * 2 ≤ 2 * K := by linarith
  calc 4 * (nmax : ℝ) / (1 - γ) * (((A₀.image (cell k j)).card : ℝ) * 2) * 2 *
        (Real.exp (lam * (c₀ + D₀)) * Real.exp (-(lam / T.L₁ * D)))
      ≤ 4 * (nmax : ℝ) / (1 - γ) * (2 * K) * 2 *
        (Real.exp (lam * (c₀ + D₀)) * Real.exp (-(lam / T.L₁ * D))) := by gcongr
    _ = c * Real.exp (-(lam / T.L₁ * D)) := by simp only [c]; ring

/-- **Decay for gauge-invariant observables gives the torus decay of slab correlations** (S). -/
theorem torusDecayLoc_of_fineDecayInv {T : Tuning} (h : FineDecayInv T) : TorusDecayLoc T.toV := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun s R => ?_⟩
  obtain ⟨c, hc, k₀, Hk⟩ := H R
  refine ⟨k₀, c, hc, fun k hk Vb j O hO n hn => ?_⟩
  obtain ⟨hdA, hdB, -, -, hsep⟩ := slab_transfer_data T O hn
  have eA : PhysExtent T k (((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image (shiftLink (n : ZMod (T.side k j))))
      R := by
    intro e he e' he'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 he'
    rw [linkDist_shiftLink]
    exact hO k j l (Finset.mem_inter.1 hl).1 l' (Finset.mem_inter.1 hl').1
  have hb := Hk k hk j _ _ _ _ ((n : ℝ) * T.a k) ((O.meas k j).comp (measurable_tShift _))
    ((O.meas k j).comp measurePreserving_thetaConn.measurable) (fun U => O.bdd k j _) (fun U => O.bdd k j _)
    (gaugeInvariant_thetaConn (O.gauge k j)) hdA hdB eA hsep
  show |T.wcorr k j (O.F k j) n| ≤ _
  unfold Tuning.wcorr corr
  exact hb

/-- **Assembly with the one-box criterion for the Wilson measure** (S). SU(2) lattice Yang–Mills with the Wilson action
on 4D tori along the tuning `T`. If the line of constant physics holds in its weakened form, the limit is non-trivial,
and the Wilson measure satisfies the one-box criterion at the physical cell scale (**the gap-strength input**, a
finite-volume condition on one box under all boundary conditions, uniform in the level), then: torus decay for slab
observables of bounded physical extent, the gap in both orders of limits, reflection positivity, non-triviality. No
blocking family and no ultraviolet transfer input. -/
theorem yang_mills_assembly_onebox {T : Tuning} (hL : OnLCP' T) (hN : NonTrivial T) (h : FineOneBox T) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T := by
  have hT := torusDecayLoc_of_fineDecayInv (fineDecayInv_of_fineOneBox h)
  obtain ⟨hVF, hMF⟩ := bothOrdersLoc_of_torusDecayLoc hL.tendsto_a hT
  exact ⟨hT, hVF, hMF, limitRP T, hN⟩

end ProofPhase.OneBox
