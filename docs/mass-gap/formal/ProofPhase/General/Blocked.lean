/-
Proof phase, generalisation phase 1c: the blocked route over any gauge group and dimension (2026-11-24).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 1c.
-/

import ProofPhase.General.Slab
import ProofPhase.General.Noisy
import ProofPhase.General.Filter
import ProofPhase.RouteA.BlockedSlab

/-!
# The blocked route to the reflected correlation, over any gauge group and dimension

`H1Local` and `LimitDprime` (the blocked laws are Gibbs measures with locally converging coarse potentials satisfying
D′_λ), `blockGap_of_blockedRoute` (Dobrushin decay of the blocked laws), `wcorr_le_blocked` (the reflected correlation of
a slab observable through the blocking: `(1 − γ)⁻¹ K_v · 2 e^{−λ n a_k/(2L₁)} + 5ε`) and `slab_transfer_data` (the slab
pair is separated in time). From `Assembly` and `RouteA/BlockedSlab`.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity

open ProofPhase.RouteA (cov_transfer DepOn.inter gaugeInvariant_tShift gaugeInvariant_thetaConn)
open OneScale.CubeChain (sep_shift_mirror)
open ProofPhase.UV

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

section Blocked

variable {Gr : Type*} [Group Gr] [TopologicalSpace Gr] [MeasurableSpace Gr] [HasHaarProbability Gr]
  (nr : ℕ) [HasGaugeTrace Gr nr] [GaugeGroupBase Gr] {d : ℕ} [NeZero d]

def H1Local (T : Tuning) (B : BlockingFamily Gr d T) (lam : ℝ) (Vk : ∀ j, ℕ → CoarsePot Gr d j) (Vinf : ∀ j, CoarsePot Gr d j) :
    Prop :=
  (∀ k j, blockedLaw nr T B k j = Attempts.R3.gibbsMeasure (haarG Gr) (Vk j k)) ∧
  (∀ j k, Attempts.R3.Potential (fun A => A) (Vk j k)) ∧
  Attempts.R3.LocalConvergenceW (fun _ A => A) (fun _ => linkDist) lam Vk Vinf

def LimitDprime (lam : ℝ) (Vinf : ∀ j, CoarsePot Gr d j) : Prop :=
  Attempts.R3.LimitFlatW (fun _ A => A) (fun _ => linkDist) lam Vinf

variable [GaugeRep Gr nr]

theorem blockGap_of_blockedRoute {T : Tuning} (B : BlockingFamily Gr d T) {lam : ℝ} (hlam : 0 ≤ lam)
    {Vk : ∀ j, ℕ → CoarsePot Gr d j} {Vinf : ∀ j, CoarsePot Gr d j} (h1 : H1Local nr T B lam Vk Vinf)
    (h2 : LimitDprime lam Vinf) :
    ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
      (f g : GaugeConnection Gr d (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink d (coarseSide j)))
      (vf : LatticeLink d (coarseSide j) → ℝ) (Lg R : ℝ),
      BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) →
      (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
      |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j) -
          (∫ U, f ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j)) * ∫ U, g ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j)| ≤
        (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)) := by
  obtain ⟨hgibbs, hpot, hconv⟩ := h1
  obtain ⟨γ, hγ0, hγ1, k₀, hlev⟩ := Attempts.R3.levelFlat_of_local (fun _ A => A) (fun _ => linkDist) Vk Vinf hconv h2
  refine ⟨Effective.effGamma γ, (Effective.effGamma_pos hγ0).le, Effective.effGamma_lt_one hγ1, k₀,
    fun k hk j f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR => ?_⟩
  obtain ⟨Sb, hS, hflat⟩ := hlev k hk j
  have : Nonempty (LatticeLink d (coarseSide j)) := ⟨⟨fun _ => 1, ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩⟩
  rw [Effective.cov_map (ymLaw (G := Gr) nr d T k j) (B k j).meas hf hg]
  have e : (ymLaw (G := Gr) nr d T k j).map (B k j).B = Attempts.R3.gibbsMeasure (haarG Gr) (Vk j k) := hgibbs k j
  rw [e]
  exact Attempts.R3.decay_of_flatW (haarG Gr) (hpot j k) hS linkDist linkDist_self linkDist_triangle hlam
    (Effective.effGamma_pos hγ0).le (Effective.effGamma_lt_one hγ1) hflat hf hg hfA hgS hvf hLg hvg hR

theorem wcorr_le_blocked (T : Tuning) (B : BlockingFamily Gr d T) {k j : ℕ} {s : ℝ} {V : ℕ → ℕ} (O : SlabObs Gr d T s V)
    (n : ℕ) {γ lam ε Kv : ℝ}
    (hgap : ∀ (f g : GaugeConnection Gr d (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink d (coarseSide j)))
      (vf : LatticeLink d (coarseSide j) → ℝ) (Lg R : ℝ),
      OneScale.BM f → OneScale.BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) →
      (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
      |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j) -
          (∫ U, f ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j)) * ∫ U, g ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j)| ≤
        (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)))
    (hγ : γ < 1)
    (f g : GaugeConnection Gr d (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink d (coarseSide j)))
    (mf : Measurable f) (mg : Measurable g) (bf : ∀ V, |f V| ≤ 1) (bg : ∀ V, |g V| ≤ 1)
    (dfA : DepOn f A') (dgB : DepOn g B') (vf : LatticeLink d (coarseSide j) → ℝ) (hvf : OscBound f vf)
    (hsumv : ∑ a ∈ A', vf a ≤ Kv)
    (hsep : ∀ x ∈ A', ∀ y ∈ B', (n * T.a k) / 2 ≤ T.L₁ * linkDist x y)
    (hEF : ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j)
        (fun U => O.F k j (tShift (n : ZMod (T.side k j)) U)) U - f ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j) ≤ ε)
    (hEG : ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j)
        (fun U => O.F k j (thetaConn U)) U - g ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j) ≤ ε)
    (hdec : |∫ U, O.F k j (tShift (n : ZMod (T.side k j)) U) * O.F k j (thetaConn U) ∂(ymLaw (G := Gr) nr d T k j) -
        ∫ U, condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j)
            (fun U => O.F k j (tShift (n : ZMod (T.side k j)) U)) U *
          condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) (fun U => O.F k j (thetaConn U)) U
            ∂(ymLaw (G := Gr) nr d T k j)| ≤ ε) :
    |wcorr nr T k j (O.F k j) n| ≤
      (1 - γ)⁻¹ * Kv * 2 * Real.exp (-(lam * ((n * T.a k) / (2 * T.L₁)))) + 5 * ε := by
  have := isProbabilityMeasure_wilsonMeasure (G := Gr) (n := nr) d (T.side k j) (T.β k)
  have hFm := O.meas k j
  have hF1 := O.bdd k j
  have htr := cov_transfer (ymLaw (G := Gr) nr d T k j) (B k j).meas (hFm.comp (measurable_tShift _))
    (hFm.comp measurePreserving_thetaConn.measurable) (fun U => hF1 _) (fun U => hF1 _) mf mg bf bg hEF hEG hdec
  -- the block-gap bound for `f`, `g`
  have hvg : OscBound g (fun _ => (2 : ℝ)) := by
    intro σ x s'
    have := bg σ; have := bg (Function.update σ x s')
    exact (abs_sub _ _).trans (by linarith)
  have hL1 := T.L₁_pos
  have hR : ∀ x ∈ A', ∀ y ∈ B', (n * T.a k) / (2 * T.L₁) ≤ linkDist x y := by
    intro x hx y hy
    rw [div_le_iff₀ (by positivity)]
    have := hsep x hx y hy
    nlinarith
  have hblk := hgap f g A' B' vf 2 _ ⟨mf, 1, bf⟩ ⟨mg, 1, bg⟩ dfA dgB hvf (by norm_num) hvg hR
  have hγ' : 0 ≤ (1 - γ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hblk' : |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j) -
      (∫ U, f ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j)) * ∫ U, g ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j)| ≤
      (1 - γ)⁻¹ * Kv * 2 * Real.exp (-(lam * ((n * T.a k) / (2 * T.L₁)))) := by
    refine hblk.trans ?_
    gcongr
  unfold wcorr corr
  exact htr.trans (by linarith)

theorem slab_transfer_data (T : Tuning) {k j : ℕ} {s : ℝ} {V : ℕ → ℕ} (O : SlabObs Gr d T s V) {n : ℕ}
    (hn : 2 * n + 2 * T.thick k s + 2 ≤ T.side k j) :
    let A₀ := ((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image (shiftLink (n : ZMod (T.side k j)))
    let B₀ := ((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image mirrorLink
    DepOn (fun U => O.F k j (tShift (n : ZMod (T.side k j)) U)) A₀ ∧
      DepOn (fun U => O.F k j (thetaConn U)) B₀ ∧ A₀.card ≤ V k ∧ B₀.card ≤ V k ∧
      ∀ e ∈ A₀, ∀ e' ∈ B₀, n * T.a k ≤ T.a k * linkDist e e' := by
  intro A₀ B₀
  have hdep := DepOn.inter (O.dep k j) (O.slab k j)
  have hc : ((O.supp k j) ∩ timeSlab 0 (T.thick k s)).card ≤ V k :=
    (Finset.card_le_card Finset.inter_subset_left).trans (O.supp_card k j)
  refine ⟨?_, ?_, (Finset.card_image_le).trans hc, (Finset.card_image_le).trans hc, ?_⟩
  · intro U U' h
    apply hdep
    intro l hl
    exact h _ (mem_image_of_mem _ hl)
  · intro U U' h
    apply hdep
    intro l hl
    have := h _ (mem_image_of_mem _ hl)
    simp only [thetaConn, this]
  · intro e he e' he'
    obtain ⟨l, hl, rfl⟩ := mem_image.1 he
    obtain ⟨l', hl', rfl⟩ := mem_image.1 he'
    have := sep_shift_mirror hn (Finset.mem_inter.mp hl).2 (Finset.mem_inter.mp hl').2
    rw [mul_comm (n : ℝ) (T.a k)]
    exact mul_le_mul_of_nonneg_left this (T.a_pos k).le

end Blocked

/-! ## The SU(2), `d = 4` instances -/

section Instance

theorem h1Local_iff (T : Tuning) (B : ProofPhase.BlockingFamily T) (lam : ℝ) (Vk : ∀ j, ℕ → ProofPhase.CoarsePot j)
    (Vinf : ∀ j, ProofPhase.CoarsePot j) :
    ProofPhase.H1Local T B lam Vk Vinf ↔ H1Local (Gr := SU2) 2 (d := 4) T B lam Vk Vinf := Iff.rfl

theorem limitDprime_iff (lam : ℝ) (Vinf : ∀ j, ProofPhase.CoarsePot j) :
    ProofPhase.LimitDprime lam Vinf ↔ LimitDprime (Gr := SU2) (d := 4) lam Vinf := Iff.rfl

theorem blockGap_of_blockedRoute_su2 {T : Tuning} (B : ProofPhase.BlockingFamily T) {lam : ℝ} (hlam : 0 ≤ lam)
    {Vk : ∀ j, ℕ → ProofPhase.CoarsePot j} {Vinf : ∀ j, ProofPhase.CoarsePot j} (h1 : ProofPhase.H1Local T B lam Vk Vinf)
    (h2 : ProofPhase.LimitDprime lam Vinf) :
    ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
      (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink 4 (coarseSide j)))
      (vf : LatticeLink 4 (coarseSide j) → ℝ) (Lg R : ℝ),
      BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) →
      (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
      |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(T.ym k j) -
          (∫ U, f ((B k j).B U) ∂(T.ym k j)) * ∫ U, g ((B k j).B U) ∂(T.ym k j)| ≤
        (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)) :=
  blockGap_of_blockedRoute (Gr := SU2) 2 (d := 4) B hlam h1 h2

theorem wcorr_le_blocked_su2 (T : Tuning) (B : ProofPhase.BlockingFamily T) {k j : ℕ} {s : ℝ} {V : ℕ → ℕ} (O : ProofPhase.SlabObs T s V)
    (n : ℕ) {γ lam ε Kv : ℝ}
    (hgap : ∀ (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink 4 (coarseSide j)))
      (vf : LatticeLink 4 (coarseSide j) → ℝ) (Lg R : ℝ),
      OneScale.BM f → OneScale.BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) →
      (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
      |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(T.ym k j) -
          (∫ U, f ((B k j).B U) ∂(T.ym k j)) * ∫ U, g ((B k j).B U) ∂(T.ym k j)| ≤
        (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)))
    (hγ : γ < 1)
    (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink 4 (coarseSide j)))
    (mf : Measurable f) (mg : Measurable g) (bf : ∀ V, |f V| ≤ 1) (bg : ∀ V, |g V| ≤ 1)
    (dfA : DepOn f A') (dgB : DepOn g B') (vf : LatticeLink 4 (coarseSide j) → ℝ) (hvf : OscBound f vf)
    (hsumv : ∑ a ∈ A', vf a ≤ Kv)
    (hsep : ∀ x ∈ A', ∀ y ∈ B', (n * T.a k) / 2 ≤ T.L₁ * linkDist x y)
    (hEF : ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j)
        (fun U => O.F k j (tShift (n : ZMod (T.side k j)) U)) U - f ((B k j).B U)| ∂(T.ym k j) ≤ ε)
    (hEG : ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j)
        (fun U => O.F k j (thetaConn U)) U - g ((B k j).B U)| ∂(T.ym k j) ≤ ε)
    (hdec : |∫ U, O.F k j (tShift (n : ZMod (T.side k j)) U) * O.F k j (thetaConn U) ∂(T.ym k j) -
        ∫ U, condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j)
            (fun U => O.F k j (tShift (n : ZMod (T.side k j)) U)) U *
          condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) (fun U => O.F k j (thetaConn U)) U
            ∂(T.ym k j)| ≤ ε) :
    |T.wcorr k j (O.F k j) n| ≤
      (1 - γ)⁻¹ * Kv * 2 * Real.exp (-(lam * ((n * T.a k) / (2 * T.L₁)))) + 5 * ε :=
  wcorr_le_blocked (Gr := SU2) 2 (d := 4) T B (SlabObs.ofOld O) n hgap hγ f g A' B' mf mg bf bg dfA dgB vf hvf hsumv hsep hEF hEG hdec

theorem slab_transfer_data_su2 (T : Tuning) {k j : ℕ} {s : ℝ} {V : ℕ → ℕ} (O : ProofPhase.SlabObs T s V) {n : ℕ}
    (hn : 2 * n + 2 * T.thick k s + 2 ≤ T.side k j) :
    let A₀ := ((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image (shiftLink (n : ZMod (T.side k j)))
    let B₀ := ((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image mirrorLink
    DepOn (fun U => O.F k j (tShift (n : ZMod (T.side k j)) U)) A₀ ∧
      DepOn (fun U => O.F k j (thetaConn U)) B₀ ∧ A₀.card ≤ V k ∧ B₀.card ≤ V k ∧
      ∀ e ∈ A₀, ∀ e' ∈ B₀, n * T.a k ≤ T.a k * linkDist e e' :=
  slab_transfer_data (Gr := SU2) (d := 4) T (SlabObs.ofOld O) hn

example : @ProofPhase.blockGap_of_blockedRoute = @blockGap_of_blockedRoute_su2 := rfl
example : @ProofPhase.RouteA.wcorr_le_blocked = @wcorr_le_blocked_su2 := rfl
example : @ProofPhase.RouteA.slab_transfer_data = @slab_transfer_data_su2 := rfl

end Instance

end ProofPhase.General
