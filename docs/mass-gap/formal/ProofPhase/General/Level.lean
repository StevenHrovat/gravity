/-
Proof phase, generalisation phase 1c: the level routes and the time-separated torus decay over any gauge group and
dimension (2026-11-24). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 1c.
-/

import ProofPhase.General.TorusLoc
import ProofPhase.General.CondMass
import ProofPhase.General.Gap
import ProofPhase.H1.Level
import ProofPhase.V3.TimeSep

/-!
# D′ along the levels, the uniform block gap, and the time-separated route, over any gauge group and dimension

`H1/Level` and `V3/TimeSep` for the Wilson measure of any `Gr` of the package in dimension `d`: `LevelDprime`,
`BlockGapUnif`, `torusDecayLoc_of_blockGapUnif`, the routes `BlockedTorusRoute`, `LevelTorusRoute`, `LevelTorusRouteT` and
their consequences in both orders of limits; `slab_time_sep` and `torusDecayLoc_of_blockGapUnifT` for the
time-separated transfer. The constant `24/a^4` becomes `d!/a^d` (`poly_exp_le` of phase 1).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity

open ProofPhase (IsLimitPoint)
open ProofPhase.RouteA (gaugeInvariant_tShift gaugeInvariant_thetaConn)
open ProofPhase.V3 (timeDist timeDist_le_linkDist sep_shift_mirror_time)
open ProofPhase.UV

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

section Level

variable {Gr : Type*} [Group Gr] [TopologicalSpace Gr] [MeasurableSpace Gr] [HasHaarProbability Gr]
  (nr : ℕ) [HasGaugeTrace Gr nr] [GaugeGroupBase Gr] {d : ℕ} [NeZero d]

def LevelDprime (T : Tuning) (B : BlockingFamily Gr d T) (lam : ℝ) : Prop :=
  ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j, ∃ V : CoarsePot Gr d j,
    blockedLaw nr T B k j = Attempts.R3.gibbsMeasure (haarG Gr) V ∧ Attempts.R3.Potential (fun A => A) V ∧
    ∃ Sb : LatticeLink d (coarseSide j) → LatticeLink d (coarseSide j) → ℝ,
      Attempts.R3.PairOsc (fun A => A) V Sb ∧ Attempts.R3.FlatCriterionW linkDist lam Sb γ

def BlockGapUnif (T : Tuning) (B : BlockingFamily Gr d T) (lam : ℝ) : Prop :=
  ∃ γ : ℝ, γ < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (f g : GaugeConnection Gr d (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink d (coarseSide j)))
    (vf : LatticeLink d (coarseSide j) → ℝ) (Lg R : ℝ),
    BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) →
    (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
    |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j) -
        (∫ U, f ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j)) * ∫ U, g ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j)| ≤
      (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R))

variable [GaugeRep Gr nr]

theorem levelDprime_of_h1Local {T : Tuning} {B : BlockingFamily Gr d T} {lam : ℝ} {Vk : ∀ j, ℕ → CoarsePot Gr d j}
    {Vinf : ∀ j, CoarsePot Gr d j} (h1 : H1Local nr T B lam Vk Vinf) (h2 : LimitDprime lam Vinf) : LevelDprime nr T B lam := by
  obtain ⟨hgibbs, hpot, hconv⟩ := h1
  obtain ⟨γ, hγ0, hγ1, k₀, hlev⟩ := Attempts.R3.levelFlat_of_local (fun _ A => A) (fun _ => linkDist) Vk Vinf hconv h2
  refine ⟨Effective.effGamma γ, (Effective.effGamma_pos hγ0).le, Effective.effGamma_lt_one hγ1, k₀, fun k hk j => ?_⟩
  obtain ⟨Sb, hS, hflat⟩ := hlev k hk j
  exact ⟨Vk j k, hgibbs k j, hpot j k, Sb, hS, hflat⟩

theorem blockGapUnif_of_levelDprime {T : Tuning} (B : BlockingFamily Gr d T) {lam : ℝ} (hlam : 0 ≤ lam)
    (h : LevelDprime nr T B lam) : BlockGapUnif nr T B lam := by
  obtain ⟨γ, hγ0, hγ1, k₀, hlev⟩ := h
  refine ⟨γ, hγ1, k₀, fun k hk j f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR => ?_⟩
  obtain ⟨V, hgibbs, hpot, Sb, hS, hflat⟩ := hlev k hk j
  have : Nonempty (LatticeLink d (coarseSide j)) := ⟨⟨fun _ => 1, ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩⟩
  rw [Effective.cov_map (ymLaw (G := Gr) nr d T k j) (B k j).meas hf hg]
  have e : (ymLaw (G := Gr) nr d T k j).map (B k j).B = Attempts.R3.gibbsMeasure (haarG Gr) V := hgibbs
  rw [e]
  exact Attempts.R3.decay_of_flatW (haarG Gr) hpot hS linkDist linkDist_self linkDist_triangle hlam hγ0 hγ1 hflat
    hf hg hfA hgS hvf hLg hvg hR

theorem blockGapUnif_of_blockedRoute {T : Tuning} (B : BlockingFamily Gr d T) {lam : ℝ} (hlam : 0 ≤ lam)
    {Vk : ∀ j, ℕ → CoarsePot Gr d j} {Vinf : ∀ j, CoarsePot Gr d j} (h1 : H1Local nr T B lam Vk Vinf) (h2 : LimitDprime lam Vinf) :
    BlockGapUnif nr T B lam :=
  blockGapUnif_of_levelDprime nr B hlam (levelDprime_of_h1Local nr h1 h2)

theorem torusDecayLoc_of_blockGapUnif {T : Tuning} (B : BlockingFamily Gr d T) {lam : ℝ} (hlam : 0 < lam)
    (hB : BlockGapUnif nr T B lam) (h3 : ObsTransferPhys nr T B) : TorusDecayLoc Gr nr d T.toV := by
  obtain ⟨γ, hγ1, k₀, hgap⟩ := hB
  obtain ⟨m, hm, htrP⟩ := h3
  have hL1 := T.L₁_pos
  set a := lam / 4
  have ha : 0 < a := by positivity
  set m' := min (lam / (4 * T.L₁)) m
  have hm' : 0 < m' := lt_min (by positivity) hm
  refine ⟨m', hm', fun s R => ?_⟩
  obtain ⟨c, K, hc, k₁, htr⟩ := htrP (R + T.L₁)
  set K' := |K|
  have hγ' : 0 ≤ (1 - γ)⁻¹ := inv_nonneg.mpr (by linarith)
  refine ⟨max k₀ k₁, (1 - γ)⁻¹ * (2 * K') * 2 * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a) + 5 * c, by positivity,
    fun k hk Vb j O hO n hn => ?_⟩
  have hk₀ : k₀ ≤ k := (le_max_left _ _).trans hk
  have hk₁ : k₁ ≤ k := (le_max_right _ _).trans hk
  obtain ⟨hdA, hdB, -, -, hsep⟩ := slab_transfer_data T O hn
  have hak := T.a_pos k
  have haL : T.a k ≤ T.L₁ := div_le_self hL1.le (by exact_mod_cast T.ℓ_pos k)
  have eA : PhysExtent T k (((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image (shiftLink (n : ZMod (T.side k j))))
      (R + T.L₁) := by
    intro e he e' he'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 he'
    rw [linkDist_shiftLink]
    have : T.a k * linkDist l l' ≤ R := hO k j l (Finset.mem_inter.1 hl).1 l' (Finset.mem_inter.1 hl').1
    linarith
  have eB : PhysExtent T k (((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image mirrorLink) (R + T.L₁) := by
    intro e he e' he'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 he'
    have h1 : T.a k * linkDist l l' ≤ R := hO k j l (Finset.mem_inter.1 hl).1 l' (Finset.mem_inter.1 hl').1
    have h2 := mul_le_mul_of_nonneg_left (linkDist_mirrorLink_le l l') hak.le
    nlinarith
  set D := (n : ℝ) * T.a k
  have hD : 0 ≤ D := by positivity
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, ⟨vf, hvf, hsv⟩, hsep', hEF, hEG, hdec⟩ :=
    htr k hk₁ j _ _ _ _ D ((O.meas k j).comp (measurable_tShift _))
      ((O.meas k j).comp measurePreserving_thetaConn.measurable) (fun U => O.bdd k j _) (fun U => O.bdd k j _)
      (gaugeInvariant_tShift (O.gauge k j) _) (gaugeInvariant_thetaConn (O.gauge k j)) hdA hdB eA eB hsep
  have hx : 0 ≤ D / T.L₁ := by positivity
  have hsv' : ∑ a ∈ A', vf a ≤ 2 * (K' * (1 + D / T.L₁) ^ d) := by
    refine hsv.trans ?_
    have : K * (1 + D / T.L₁) ^ d ≤ K' * (1 + D / T.L₁) ^ d :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    linarith
  have hmain := wcorr_le_blocked nr T B O n (hgap k hk₀ j) hγ1 f g A' B' mf mg bf bg dfA dgB vf hvf hsv' hsep' hEF hEG
    hdec
  have hpoly := poly_exp_le d ha hx
  have e1 : lam * (D / (2 * T.L₁)) = 2 * a * (D / T.L₁) := by simp only [a]; field_simp; ring
  have e2 : a * (D / T.L₁) = lam / (4 * T.L₁) * D := by simp only [a]; field_simp
  have hE1 : Real.exp (-(lam / (4 * T.L₁) * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left (lam / (4 * T.L₁)) m])
  have hE2 : Real.exp (-(m * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right (lam / (4 * T.L₁)) m])
  have hK' : 0 ≤ K' := abs_nonneg K
  show |wcorr nr T k j (O.F k j) n| ≤ _
  calc |wcorr nr T k j (O.F k j) n|
      ≤ (1 - γ)⁻¹ * (2 * (K' * (1 + D / T.L₁) ^ d)) * 2 * Real.exp (-(lam * (D / (2 * T.L₁)))) +
          5 * (c * Real.exp (-(m * D))) := hmain
    _ = (1 - γ)⁻¹ * (2 * K') * 2 * ((1 + D / T.L₁) ^ d * Real.exp (-(2 * a * (D / T.L₁)))) +
          5 * c * Real.exp (-(m * D)) := by rw [e1]; ring
    _ ≤ (1 - γ)⁻¹ * (2 * K') * 2 * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a * Real.exp (-(a * (D / T.L₁)))) +
          5 * c * Real.exp (-(m' * D)) := by
        gcongr
    _ = (1 - γ)⁻¹ * (2 * K') * 2 * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a) * Real.exp (-(lam / (4 * T.L₁) * D)) +
          5 * c * Real.exp (-(m' * D)) := by rw [e2]; ring
    _ ≤ (1 - γ)⁻¹ * (2 * K') * 2 * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a) * Real.exp (-(m' * D)) +
          5 * c * Real.exp (-(m' * D)) := by gcongr
    _ = ((1 - γ)⁻¹ * (2 * K') * 2 * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a) + 5 * c) * Real.exp (-(m' * (n * T.a k))) := by
        ring

theorem slab_time_sep (T : Tuning) {k j : ℕ} {s : ℝ} {V : ℕ → ℕ} (O : SlabObs Gr d T s V) {n : ℕ}
    (hn : 2 * n + 2 * T.thick k s + 2 ≤ T.side k j) :
    ∀ e ∈ ((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image (shiftLink (n : ZMod (T.side k j))),
      ∀ e' ∈ ((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image mirrorLink, n * T.a k ≤ T.a k * timeDist e e' := by
  intro e he e' he'
  obtain ⟨l, hl, rfl⟩ := mem_image.1 he
  obtain ⟨l', hl', rfl⟩ := mem_image.1 he'
  have := sep_shift_mirror_time hn (Finset.mem_inter.mp hl).2 (Finset.mem_inter.mp hl').2
  rw [mul_comm (n : ℝ) (T.a k)]
  exact mul_le_mul_of_nonneg_left this (T.a_pos k).le

theorem torusDecayLoc_of_blockGapUnifT {T : Tuning} (B : BlockingFamily Gr d T) {lam : ℝ} (hlam : 0 < lam)
    (hB : BlockGapUnif nr T B lam) (h3 : ObsTransferPhysT nr T B) : TorusDecayLoc Gr nr d T.toV := by
  obtain ⟨γ, hγ1, k₀, hgap⟩ := hB
  obtain ⟨m, hm, htrP⟩ := h3
  have hL1 := T.L₁_pos
  set a := lam / 4
  have ha : 0 < a := by positivity
  set m' := min (lam / (4 * T.L₁)) m
  have hm' : 0 < m' := lt_min (by positivity) hm
  refine ⟨m', hm', fun s R => ?_⟩
  obtain ⟨c, K, hc, k₁, htr⟩ := htrP (R + T.L₁)
  set K' := |K|
  have hγ' : 0 ≤ (1 - γ)⁻¹ := inv_nonneg.mpr (by linarith)
  refine ⟨max k₀ k₁, (1 - γ)⁻¹ * (2 * K') * 2 * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a) + 5 * c, by positivity,
    fun k hk Vb j O hO n hn => ?_⟩
  have hk₀ : k₀ ≤ k := (le_max_left _ _).trans hk
  have hk₁ : k₁ ≤ k := (le_max_right _ _).trans hk
  obtain ⟨hdA, hdB, -, -, -⟩ := slab_transfer_data T O hn
  have hsepT := slab_time_sep T O hn
  have hak := T.a_pos k
  have haL : T.a k ≤ T.L₁ := div_le_self hL1.le (by exact_mod_cast T.ℓ_pos k)
  have eA : PhysExtent T k (((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image (shiftLink (n : ZMod (T.side k j))))
      (R + T.L₁) := by
    intro e he e' he'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 he'
    rw [linkDist_shiftLink]
    have : T.a k * linkDist l l' ≤ R := hO k j l (Finset.mem_inter.1 hl).1 l' (Finset.mem_inter.1 hl').1
    linarith
  have eB : PhysExtent T k (((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image mirrorLink) (R + T.L₁) := by
    intro e he e' he'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 he'
    have h1 : T.a k * linkDist l l' ≤ R := hO k j l (Finset.mem_inter.1 hl).1 l' (Finset.mem_inter.1 hl').1
    have h2 := mul_le_mul_of_nonneg_left (linkDist_mirrorLink_le l l') hak.le
    nlinarith
  set D := (n : ℝ) * T.a k
  have hD : 0 ≤ D := by positivity
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, ⟨vf, hvf, hsv⟩, hsep', hEF, hEG, hdec⟩ :=
    htr k hk₁ j _ _ _ _ D hD ((O.meas k j).comp (measurable_tShift _))
      ((O.meas k j).comp measurePreserving_thetaConn.measurable) (fun U => O.bdd k j _) (fun U => O.bdd k j _)
      (gaugeInvariant_tShift (O.gauge k j) _) (gaugeInvariant_thetaConn (O.gauge k j)) hdA hdB eA eB hsepT
  have hx : 0 ≤ D / T.L₁ := by positivity
  have hsv' : ∑ a ∈ A', vf a ≤ 2 * (K' * (1 + D / T.L₁) ^ d) := by
    refine hsv.trans ?_
    have : K * (1 + D / T.L₁) ^ d ≤ K' * (1 + D / T.L₁) ^ d :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    linarith
  have hmain := wcorr_le_blocked nr T B O n (hgap k hk₀ j) hγ1 f g A' B' mf mg bf bg dfA dgB vf hvf hsv' hsep' hEF hEG
    hdec
  have hpoly := poly_exp_le d ha hx
  have e1 : lam * (D / (2 * T.L₁)) = 2 * a * (D / T.L₁) := by simp only [a]; field_simp; ring
  have e2 : a * (D / T.L₁) = lam / (4 * T.L₁) * D := by simp only [a]; field_simp
  have hE1 : Real.exp (-(lam / (4 * T.L₁) * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left (lam / (4 * T.L₁)) m])
  have hE2 : Real.exp (-(m * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right (lam / (4 * T.L₁)) m])
  have hK' : 0 ≤ K' := abs_nonneg K
  show |wcorr nr T k j (O.F k j) n| ≤ _
  calc |wcorr nr T k j (O.F k j) n|
      ≤ (1 - γ)⁻¹ * (2 * (K' * (1 + D / T.L₁) ^ d)) * 2 * Real.exp (-(lam * (D / (2 * T.L₁)))) +
          5 * (c * Real.exp (-(m * D))) := hmain
    _ = (1 - γ)⁻¹ * (2 * K') * 2 * ((1 + D / T.L₁) ^ d * Real.exp (-(2 * a * (D / T.L₁)))) +
          5 * c * Real.exp (-(m * D)) := by rw [e1]; ring
    _ ≤ (1 - γ)⁻¹ * (2 * K') * 2 * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a * Real.exp (-(a * (D / T.L₁)))) +
          5 * c * Real.exp (-(m' * D)) := by
        gcongr
    _ = (1 - γ)⁻¹ * (2 * K') * 2 * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a) * Real.exp (-(lam / (4 * T.L₁) * D)) +
          5 * c * Real.exp (-(m' * D)) := by rw [e2]; ring
    _ ≤ (1 - γ)⁻¹ * (2 * K') * 2 * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a) * Real.exp (-(m' * D)) +
          5 * c * Real.exp (-(m' * D)) := by gcongr
    _ = ((1 - γ)⁻¹ * (2 * K') * 2 * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a) + 5 * c) * Real.exp (-(m' * (n * T.a k))) := by
        ring

section Explicit

variable (Gr) (d)

def BlockedTorusRoute (T : Tuning) : Prop :=
  ∃ (B : BlockingFamily Gr d T) (lam : ℝ) (Vk : ∀ j, ℕ → CoarsePot Gr d j) (Vinf : ∀ j, CoarsePot Gr d j),
    0 < lam ∧ H1Local nr T B lam Vk Vinf ∧ LimitDprime lam Vinf ∧ ObsTransferPhys nr T B

def BlockedSlabRoute (T : Tuning) : Prop :=
  ∃ (B : BlockingFamily Gr d T) (lam : ℝ) (Vk : ∀ j, ℕ → CoarsePot Gr d j) (Vinf : ∀ j, CoarsePot Gr d j),
    0 < lam ∧ H1Local nr T B lam Vk Vinf ∧ LimitDprime lam Vinf ∧ ObsTransfer nr T B

def LevelTorusRoute (T : Tuning) : Prop :=
  ∃ (B : BlockingFamily Gr d T) (lam : ℝ), 0 < lam ∧ LevelDprime nr T B lam ∧ ObsTransferPhys nr T B

def LevelTorusRouteT (T : Tuning) : Prop :=
  ∃ (B : BlockingFamily Gr d T) (lam : ℝ), 0 < lam ∧ LevelDprime nr T B lam ∧ ObsTransferPhysT nr T B

theorem levelTorusRoute_of_blockedTorusRoute {T : Tuning} (h : BlockedTorusRoute Gr nr d T) : LevelTorusRoute Gr nr d T := by
  obtain ⟨B, lam, Vk, Vinf, hlam, h1, h2, h3⟩ := h
  exact ⟨B, lam, hlam, levelDprime_of_h1Local nr h1 h2, h3⟩

theorem bothOrdersLoc_of_levelRoute {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (h : LevelTorusRoute Gr nr d T) :
    TorusDecayLoc Gr nr d T.toV ∧ MassGapLoc Gr nr d T ∧ MassGapMFLoc Gr nr d T.toV := by
  obtain ⟨B, lam, hlam, hD, h3⟩ := h
  have hT := torusDecayLoc_of_blockGapUnif nr B hlam (blockGapUnif_of_levelDprime nr B hlam.le hD) h3
  exact ⟨hT, bothOrdersLoc_of_torusDecayLoc Gr nr d ha hT⟩

theorem levelTorusRouteT_of_level {T : Tuning} (h : LevelTorusRoute Gr nr d T) : LevelTorusRouteT Gr nr d T := by
  obtain ⟨B, lam, hlam, hD, h3⟩ := h
  exact ⟨B, lam, hlam, hD, obsTransferPhysT_of_phys nr h3⟩

theorem bothOrdersLoc_of_levelRouteT {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (h : LevelTorusRouteT Gr nr d T) :
    TorusDecayLoc Gr nr d T.toV ∧ MassGapLoc Gr nr d T ∧ MassGapMFLoc Gr nr d T.toV := by
  obtain ⟨B, lam, hlam, hD, h3⟩ := h
  have hT := torusDecayLoc_of_blockGapUnifT nr B hlam (blockGapUnif_of_levelDprime nr B hlam.le hD) h3
  exact ⟨hT, bothOrdersLoc_of_torusDecayLoc Gr nr d ha hT⟩

end Explicit

end Level

/-! ## The SU(2), `d = 4` instances -/

section Instance

variable (T : Tuning) (B : ProofPhase.BlockingFamily T)

theorem levelDprime_iff (lam : ℝ) : ProofPhase.H1.LevelDprime T B lam ↔ LevelDprime (Gr := SU2) 2 (d := 4) T B lam :=
  Iff.rfl

theorem blockGapUnif_iff (lam : ℝ) : ProofPhase.H1.BlockGapUnif T B lam ↔ BlockGapUnif (Gr := SU2) 2 (d := 4) T B lam :=
  Iff.rfl

theorem blockedTorusRoute_iff : ProofPhase.BlockedTorusRoute T ↔ BlockedTorusRoute SU2 2 4 T := Iff.rfl

theorem blockedSlabRoute_iff : ProofPhase.BlockedSlabRoute T ↔ BlockedSlabRoute SU2 2 4 T := Iff.rfl

theorem levelTorusRoute_iff : ProofPhase.H1.LevelTorusRoute T ↔ LevelTorusRoute SU2 2 4 T := Iff.rfl

theorem levelTorusRouteT_iff : ProofPhase.V3.LevelTorusRouteT T ↔ LevelTorusRouteT SU2 2 4 T := Iff.rfl

variable {T B}

/-- `ProofPhase.H1.levelDprime_of_h1Local` from the generic theorem. -/
theorem levelDprime_of_h1Local_su2 {lam : ℝ} {Vk : ∀ j, ℕ → ProofPhase.CoarsePot j}
    {Vinf : ∀ j, ProofPhase.CoarsePot j} (h1 : ProofPhase.H1Local T B lam Vk Vinf)
    (h2 : ProofPhase.LimitDprime lam Vinf) : ProofPhase.H1.LevelDprime T B lam :=
  levelDprime_of_h1Local (Gr := SU2) 2 (d := 4) h1 h2

/-- `ProofPhase.H1.blockGapUnif_of_levelDprime` from the generic theorem. -/
theorem blockGapUnif_of_levelDprime_su2 {lam : ℝ} (hlam : 0 ≤ lam) (h : ProofPhase.H1.LevelDprime T B lam) :
    ProofPhase.H1.BlockGapUnif T B lam :=
  blockGapUnif_of_levelDprime (Gr := SU2) 2 (d := 4) B hlam h

/-- `ProofPhase.H1.blockGapUnif_of_blockedRoute` from the generic theorem. -/
theorem blockGapUnif_of_blockedRoute_su2 {lam : ℝ} (hlam : 0 ≤ lam) {Vk : ∀ j, ℕ → ProofPhase.CoarsePot j}
    {Vinf : ∀ j, ProofPhase.CoarsePot j} (h1 : ProofPhase.H1Local T B lam Vk Vinf)
    (h2 : ProofPhase.LimitDprime lam Vinf) : ProofPhase.H1.BlockGapUnif T B lam :=
  blockGapUnif_of_blockedRoute (Gr := SU2) 2 (d := 4) B hlam h1 h2

/-- `ProofPhase.H1.torusDecayLoc_of_blockGapUnif` from the generic theorem. -/
theorem torusDecayLoc_of_blockGapUnif_su2 {lam : ℝ} (hlam : 0 < lam) (hB : ProofPhase.H1.BlockGapUnif T B lam)
    (h3 : ProofPhase.ObsTransferPhys T B) : ProofPhase.Torus.TorusDecayLoc T.toV :=
  (torusDecayLoc_iff _).2 (torusDecayLoc_of_blockGapUnif (Gr := SU2) 2 (d := 4) B hlam hB h3)

/-- `ProofPhase.V3.torusDecayLoc_of_blockGapUnifT` from the generic theorem. -/
theorem torusDecayLoc_of_blockGapUnifT_su2 {lam : ℝ} (hlam : 0 < lam) (hB : ProofPhase.H1.BlockGapUnif T B lam)
    (h3 : ProofPhase.V3.ObsTransferPhysT T B) : ProofPhase.Torus.TorusDecayLoc T.toV :=
  (torusDecayLoc_iff _).2 (torusDecayLoc_of_blockGapUnifT (Gr := SU2) 2 (d := 4) B hlam hB h3)

/-- `ProofPhase.V3.slab_time_sep` from the generic theorem. -/
theorem slab_time_sep_su2 (T : Tuning) {k j : ℕ} {s : ℝ} {V : ℕ → ℕ} (O : ProofPhase.SlabObs T s V) {n : ℕ}
    (hn : 2 * n + 2 * T.thick k s + 2 ≤ T.side k j) :
    ∀ e ∈ ((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image (shiftLink (n : ZMod (T.side k j))),
      ∀ e' ∈ ((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image mirrorLink,
        n * T.a k ≤ T.a k * ProofPhase.V3.timeDist e e' :=
  slab_time_sep (Gr := SU2) (d := 4) T (SlabObs.ofOld O) hn

/-- `ProofPhase.H1.levelTorusRoute_of_blockedTorusRoute` from the generic theorem. -/
theorem levelTorusRoute_of_blockedTorusRoute_su2 (h : ProofPhase.BlockedTorusRoute T) :
    ProofPhase.H1.LevelTorusRoute T :=
  (levelTorusRoute_iff T).2 (levelTorusRoute_of_blockedTorusRoute SU2 2 4 ((blockedTorusRoute_iff T).1 h))

/-- `ProofPhase.H1.bothOrdersLoc_of_levelRoute` from the generic theorem. -/
theorem bothOrdersLoc_of_levelRoute_su2 (ha : Tendsto T.a atTop (𝓝 0)) (h : ProofPhase.H1.LevelTorusRoute T) :
    ProofPhase.Torus.TorusDecayLoc T.toV ∧ ProofPhase.MassGapLoc T ∧ ProofPhase.Torus.MassGapMFLoc T.toV := by
  have := bothOrdersLoc_of_levelRoute SU2 2 4 ha ((levelTorusRoute_iff T).1 h)
  exact ⟨(torusDecayLoc_iff _).2 this.1, (massGapLoc_iff T).2 this.2.1, (massGapMFLoc_iff _).2 this.2.2⟩

/-- `ProofPhase.V3.levelTorusRouteT_of_level` from the generic theorem. -/
theorem levelTorusRouteT_of_level_su2 (h : ProofPhase.H1.LevelTorusRoute T) : ProofPhase.V3.LevelTorusRouteT T :=
  (levelTorusRouteT_iff T).2 (levelTorusRouteT_of_level SU2 2 4 ((levelTorusRoute_iff T).1 h))

/-- `ProofPhase.V3.bothOrdersLoc_of_levelRouteT` from the generic theorem. -/
theorem bothOrdersLoc_of_levelRouteT_su2 (ha : Tendsto T.a atTop (𝓝 0)) (h : ProofPhase.V3.LevelTorusRouteT T) :
    ProofPhase.Torus.TorusDecayLoc T.toV ∧ ProofPhase.MassGapLoc T ∧ ProofPhase.Torus.MassGapMFLoc T.toV := by
  have := bothOrdersLoc_of_levelRouteT SU2 2 4 ha ((levelTorusRouteT_iff T).1 h)
  exact ⟨(torusDecayLoc_iff _).2 this.1, (massGapLoc_iff T).2 this.2.1, (massGapMFLoc_iff _).2 this.2.2⟩


example : @ProofPhase.H1.levelDprime_of_h1Local = @levelDprime_of_h1Local_su2 := rfl
example : @ProofPhase.H1.levelTorusRoute_of_blockedTorusRoute = @levelTorusRoute_of_blockedTorusRoute_su2 := rfl
example : @ProofPhase.H1.bothOrdersLoc_of_levelRoute = @bothOrdersLoc_of_levelRoute_su2 := rfl
example : @ProofPhase.V3.levelTorusRouteT_of_level = @levelTorusRouteT_of_level_su2 := rfl
example : @ProofPhase.V3.bothOrdersLoc_of_levelRouteT = @bothOrdersLoc_of_levelRouteT_su2 := rfl
example : @ProofPhase.V3.slab_time_sep = @slab_time_sep_su2 := rfl

end Instance

end ProofPhase.General
