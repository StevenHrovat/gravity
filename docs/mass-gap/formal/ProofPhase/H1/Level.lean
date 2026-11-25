/-
Proof phase, cycle 3, workstream D (c3d-h1): the route needs D′ along the levels, not a limit (2026-11-22).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c3d-h1/NOTE.md`.
-/

import ProofPhase.Torus.Top
import ProofPhase.H1.Split

/-!
# `H1Local ∧ LimitDprime` is used only through D′ at the levels

In the blocked route, `H1Local T B λ Vk Vinf` (convergence of the blocked potentials to limit potentials, uniformly in
the volume) and `LimitDprime λ Vinf` (D′ for the limit) enter **only** through round 3's openness lemma
`Attempts.R3.levelFlat_of_local`: from some level on, the blocked lattice potentials themselves satisfy D′. The limit
theory is a vehicle. This file makes that the hypothesis.

* `LevelDprime T B λ` (**named hypothesis, open; the crossover at `L₁` in depth-uniform form**): there are `γ < 1` and a
  level `k₀` such that for every level `k ≥ k₀` and every volume `j` the blocked SU(2) Wilson law at `L₁` is the Gibbs
  measure of bounded coarse potentials whose pair oscillations satisfy D′_λ with that `γ`. No limit, no convergence.
* `levelDprime_of_h1Local` (D): `H1Local ∧ LimitDprime ⇒ LevelDprime` (so `LevelDprime` is weaker or equal).
* `BlockGapUnif T B λ` (**the interface**, definitional: what every later step consumes): block covariances of the
  Wilson measure decay at rate `λ` per coarse unit with constant `(1 − γ)⁻¹`, for all levels `k ≥ k₀` and all volumes.
  `blockGapUnif_of_levelDprime` (S, through Theorem A with weights): `LevelDprime ⇒ BlockGapUnif`.
* `torusDecayLoc_of_blockGapUnif` (S, the proof of `ProofPhase.Torus.torusDecayLoc_of_blockedRoute` with the block gap as
  input): `BlockGapUnif (λ > 0) ∧ ObsTransferPhys ⇒ TorusDecayLoc`.
* `yang_mills_assembly_level`: on a line of constant physics, with non-triviality, `LevelTorusRoute` (a blocking family,
  `λ > 0`, `LevelDprime`, `ObsTransferPhys`) gives torus decay with a level-uniform constant, the gap in both orders of
  limits for observables of bounded physical extent, reflection positivity and non-triviality.
  `levelTorusRoute_of_blockedTorusRoute`: the assembly's `BlockedTorusRoute` implies `LevelTorusRoute`.

**Claim level.** Nothing open is discharged: `LevelDprime` is the conjunction's real content with the limit removed. What
changes is the bookkeeping: the open inputs of the torus route become `LevelDprime ∧ ObsTransferPhys` (plus the line of
constant physics and `NonTrivial`), and `H1Local`'s convergence half (`NearUniform`, existence and uniqueness of a limit
effective action at `L₁`) is **not needed for the gap**. Group-blind proof, SU(2) Wilson statement.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift OneScale.CubeChain Positivity ProofPhase.Existence ProofPhase.RouteA ProofPhase.Torus

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.H1

/-- **D′ along the levels (named hypothesis, open).** From some level `k₀` on, in every volume, the blocked SU(2) Wilson
law at `L₁` is the Gibbs measure of bounded coarse potentials whose pair oscillations satisfy D′_λ with one `γ < 1`. -/
def LevelDprime (T : Tuning) (B : BlockingFamily T) (lam : ℝ) : Prop :=
  ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j, ∃ V : CoarsePot j,
    blockedLaw T B k j = Attempts.R3.gibbsMeasure (haarG SU2) V ∧ Attempts.R3.Potential (fun A => A) V ∧
    ∃ Sb : LatticeLink 4 (coarseSide j) → LatticeLink 4 (coarseSide j) → ℝ,
      Attempts.R3.PairOsc (fun A => A) V Sb ∧ Attempts.R3.FlatCriterionW linkDist lam Sb γ

/-- **`H1Local ∧ LimitDprime ⇒ LevelDprime`** (D; round 3's openness lemma). -/
theorem levelDprime_of_h1Local {T : Tuning} {B : BlockingFamily T} {lam : ℝ} {Vk : ∀ j, ℕ → CoarsePot j}
    {Vinf : ∀ j, CoarsePot j} (h1 : H1Local T B lam Vk Vinf) (h2 : LimitDprime lam Vinf) : LevelDprime T B lam := by
  obtain ⟨hgibbs, hpot, hconv⟩ := h1
  obtain ⟨γ, hγ0, hγ1, k₀, hlev⟩ := Attempts.R3.levelFlat_of_local (fun _ A => A) (fun _ => linkDist) Vk Vinf hconv h2
  refine ⟨Effective.effGamma γ, (Effective.effGamma_pos hγ0).le, Effective.effGamma_lt_one hγ1, k₀, fun k hk j => ?_⟩
  obtain ⟨Sb, hS, hflat⟩ := hlev k hk j
  exact ⟨Vk j k, hgibbs k j, hpot j k, Sb, hS, hflat⟩

/-- **The block gap, uniform in level and volume** (the interface the later steps consume; definitional content: a
decay statement for block observables). -/
def BlockGapUnif (T : Tuning) (B : BlockingFamily T) (lam : ℝ) : Prop :=
  ∃ γ : ℝ, γ < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink 4 (coarseSide j)))
    (vf : LatticeLink 4 (coarseSide j) → ℝ) (Lg R : ℝ),
    BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) →
    (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
    |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(T.ym k j) -
        (∫ U, f ((B k j).B U) ∂(T.ym k j)) * ∫ U, g ((B k j).B U) ∂(T.ym k j)| ≤
      (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R))

/-- **D′ along the levels gives the uniform block gap** (S: Theorem A with exponential weights on each blocked law). -/
theorem blockGapUnif_of_levelDprime {T : Tuning} (B : BlockingFamily T) {lam : ℝ} (hlam : 0 ≤ lam)
    (h : LevelDprime T B lam) : BlockGapUnif T B lam := by
  obtain ⟨γ, hγ0, hγ1, k₀, hlev⟩ := h
  refine ⟨γ, hγ1, k₀, fun k hk j f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR => ?_⟩
  obtain ⟨V, hgibbs, hpot, Sb, hS, hflat⟩ := hlev k hk j
  have : Nonempty (LatticeLink 4 (coarseSide j)) := ⟨⟨fun _ => 0, 0⟩⟩
  rw [Effective.cov_map (T.ym k j) (B k j).meas hf hg]
  have e : (T.ym k j).map (B k j).B = Attempts.R3.gibbsMeasure (haarG SU2) V := hgibbs
  rw [e]
  exact Attempts.R3.decay_of_flatW (haarG SU2) hpot hS linkDist linkDist_self linkDist_triangle hlam hγ0 hγ1 hflat
    hf hg hfA hgS hvf hLg hvg hR

/-- The assembly's blocked route gives the uniform block gap (`blockGap_of_blockedRoute`, restated). -/
theorem blockGapUnif_of_blockedRoute {T : Tuning} (B : BlockingFamily T) {lam : ℝ} (hlam : 0 ≤ lam)
    {Vk : ∀ j, ℕ → CoarsePot j} {Vinf : ∀ j, CoarsePot j} (h1 : H1Local T B lam Vk Vinf) (h2 : LimitDprime lam Vinf) :
    BlockGapUnif T B lam :=
  blockGapUnif_of_levelDprime B hlam (levelDprime_of_h1Local h1 h2)

/-- **Torus decay from the uniform block gap and the physical-size transfer** (S; the proof of
`ProofPhase.Torus.torusDecayLoc_of_blockedRoute`, which uses `H1Local ∧ LimitDprime` only through the block gap). -/
theorem torusDecayLoc_of_blockGapUnif {T : Tuning} (B : BlockingFamily T) {lam : ℝ} (hlam : 0 < lam)
    (hB : BlockGapUnif T B lam) (h3 : ObsTransferPhys T B) : TorusDecayLoc T.toV := by
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
  refine ⟨max k₀ k₁, (1 - γ)⁻¹ * (2 * K') * 2 * (24 / a ^ 4 * Real.exp a) + 5 * c, by positivity,
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
  have hsv' : ∑ a ∈ A', vf a ≤ 2 * (K' * (1 + D / T.L₁) ^ 4) := by
    refine hsv.trans ?_
    have : K * (1 + D / T.L₁) ^ 4 ≤ K' * (1 + D / T.L₁) ^ 4 :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    linarith
  have hmain := wcorr_le_blocked T B O n (hgap k hk₀ j) hγ1 f g A' B' mf mg bf bg dfA dgB vf hvf hsv' hsep' hEF hEG
    hdec
  have hpoly := poly_exp_le ha hx
  have e1 : lam * (D / (2 * T.L₁)) = 2 * a * (D / T.L₁) := by simp only [a]; field_simp; ring
  have e2 : a * (D / T.L₁) = lam / (4 * T.L₁) * D := by simp only [a]; field_simp
  have hE1 : Real.exp (-(lam / (4 * T.L₁) * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left (lam / (4 * T.L₁)) m])
  have hE2 : Real.exp (-(m * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right (lam / (4 * T.L₁)) m])
  have hK' : 0 ≤ K' := abs_nonneg K
  show |T.wcorr k j (O.F k j) n| ≤ _
  calc |T.wcorr k j (O.F k j) n|
      ≤ (1 - γ)⁻¹ * (2 * (K' * (1 + D / T.L₁) ^ 4)) * 2 * Real.exp (-(lam * (D / (2 * T.L₁)))) +
          5 * (c * Real.exp (-(m * D))) := hmain
    _ = (1 - γ)⁻¹ * (2 * K') * 2 * ((1 + D / T.L₁) ^ 4 * Real.exp (-(2 * a * (D / T.L₁)))) +
          5 * c * Real.exp (-(m * D)) := by rw [e1]; ring
    _ ≤ (1 - γ)⁻¹ * (2 * K') * 2 * (24 / a ^ 4 * Real.exp a * Real.exp (-(a * (D / T.L₁)))) +
          5 * c * Real.exp (-(m' * D)) := by
        gcongr
    _ = (1 - γ)⁻¹ * (2 * K') * 2 * (24 / a ^ 4 * Real.exp a) * Real.exp (-(lam / (4 * T.L₁) * D)) +
          5 * c * Real.exp (-(m' * D)) := by rw [e2]; ring
    _ ≤ (1 - γ)⁻¹ * (2 * K') * 2 * (24 / a ^ 4 * Real.exp a) * Real.exp (-(m' * D)) +
          5 * c * Real.exp (-(m' * D)) := by gcongr
    _ = ((1 - γ)⁻¹ * (2 * K') * 2 * (24 / a ^ 4 * Real.exp a) + 5 * c) * Real.exp (-(m' * (n * T.a k))) := by
        ring

/-- **Route A, torus form, with D′ along the levels** (open inputs): a blocking family, `λ > 0`, `LevelDprime`,
`ObsTransferPhys`. -/
def LevelTorusRoute (T : Tuning) : Prop :=
  ∃ (B : BlockingFamily T) (lam : ℝ), 0 < lam ∧ LevelDprime T B lam ∧ ObsTransferPhys T B

/-- The assembly's torus route implies the level form (D): `LevelTorusRoute` is weaker or equal. -/
theorem levelTorusRoute_of_blockedTorusRoute {T : Tuning} (h : BlockedTorusRoute T) : LevelTorusRoute T := by
  obtain ⟨B, lam, Vk, Vinf, hlam, h1, h2, h3⟩ := h
  exact ⟨B, lam, hlam, levelDprime_of_h1Local h1 h2, h3⟩

/-- **The torus route with D′ along the levels gives the gap in both orders of limits.** -/
theorem bothOrdersLoc_of_levelRoute {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (h : LevelTorusRoute T) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV := by
  obtain ⟨B, lam, hlam, hD, h3⟩ := h
  have hT := torusDecayLoc_of_blockGapUnif B hlam (blockGapUnif_of_levelDprime B hlam.le hD) h3
  exact ⟨hT, bothOrdersLoc_of_torusDecayLoc ha hT⟩

/-- **The assembly with `LevelDprime` in place of `H1Local ∧ LimitDprime`.** For SU(2) lattice Yang–Mills along a
tuning `T` on a line of constant physics, with non-triviality: if a reflection-respecting blocking onto `L₁` cells
satisfies D′_λ along the levels (`LevelDprime`, `λ > 0`) and the physical-size observable transfer, then torus decay with
a level-uniform constant holds for slab observables of bounded physical extent, the gap holds for them in both orders of
limits, every limit point is reflection positive, and the limit is non-trivial. -/
theorem yang_mills_assembly_level {T : Tuning} (hL : OnLCP T) (hN : NonTrivial T) (h : LevelTorusRoute T) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T := by
  obtain ⟨hT, hVF, hMF⟩ := bothOrdersLoc_of_levelRoute hL.tendsto_a h
  exact ⟨hT, hVF, hMF, limitRP T, hN⟩

end ProofPhase.H1
