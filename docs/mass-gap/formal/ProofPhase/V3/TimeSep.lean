/-
Proof phase, cycle 4, workstream 1 (c4a-condmass): the observable transfer for time-separated pairs only (2026-11-22).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c4a-condmass/NOTE.md`.
-/

import ProofPhase.H1.Level

/-!
# `ObsTransferPhysT`: the transfer for time-separated pairs is enough for the torus route

`ProofPhase.ObsTransferPhys` (cycle 2) asks its three estimates for every pair of fine observables of bounded physical
extent at physical distance `≥ D`, in any direction. The torus route uses it once, for the pair `F ∘ S_n` (the slab
observable translated by `n` lattice steps in time) and `F ∘ Θ` (its time reflection): these are separated **in the time
direction** (`sep_shift_mirror_time`). c3a-uv proposed the time-separated form; c3a's Gaussian photon test passes in time
and fails in space for the staple kernel at `w = 0.5, 1` (the spatial checkerboard defect), so the weaker form matters.

* `timeDist e e'`: the cyclic distance of the time coordinates of the base sites; `timeDist_le_linkDist`.
* `sep_shift_mirror_time` (D, a re-run of `OneScale.CubeChain.sep_shift_mirror` for the time coordinate): a link of the
  slab `[0, s]` translated by `M` and a mirrored link of the same slab are at time distance `≥ M` while
  `2M + 2s + 2 ≤ N`.
* `ObsTransferPhysT T B` (**named hypothesis, open**): `ObsTransferPhys` restricted to `D ≥ 0` and to pairs whose
  supports are at physical **time** distance `≥ D` (`D ≤ a_k · timeDist e e'` for all `e ∈ A₀`, `e' ∈ B₀`). Weaker than
  `ObsTransferPhys` (`obsTransferPhysT_of_phys`, D).
* `torusDecayLoc_of_blockGapUnifT` (S, the proof of `H1.torusDecayLoc_of_blockGapUnif` with the time separation):
  `BlockGapUnif (λ > 0) ∧ ObsTransferPhysT ⇒ TorusDecayLoc`.
* `LevelTorusRouteT`, `levelTorusRouteT_of_level` (D), `bothOrdersLoc_of_levelRouteT` (S): the torus route with
  `LevelDprime ∧ ObsTransferPhysT` gives the gap for bounded physical extent in both orders of limits.

**Answer to the brief's question 2: yes.** Reflection positivity and the torus route only ever pair an observable with a
time-translate of its reflection; the transfer is needed for time-separated pairs only, and the assembly goes through
with `ObsTransferPhysT` (Lean, `torusDecayLoc_of_blockGapUnifT`). Group-blind proof, SU(2) Wilson statement.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift OneScale.CubeChain Positivity ProofPhase.Existence ProofPhase.RouteA ProofPhase.Torus
  ProofPhase.H1

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.V3

/-! ## Time distance -/

section TimeDist

variable {d N : ℕ} [NeZero d] [NeZero N]

/-- The **time distance** of two links: the cyclic distance of the time coordinates of their base sites. -/
def timeDist (e e' : LatticeLink d N) : ℝ := (cyc (e.site 0 - e'.site 0) : ℝ)

theorem timeDist_le_linkDist (e e' : LatticeLink d N) : timeDist e e' ≤ linkDist e e' :=
  cyc_time_le_linkDist e e'

theorem timeDist_nonneg (e e' : LatticeLink d N) : 0 ≤ timeDist e e' := Nat.cast_nonneg _

/-- **The slab pair is separated in time** (the time-coordinate form of `OneScale.CubeChain.sep_shift_mirror`). -/
theorem sep_shift_mirror_time {s M : ℕ} (hN : 2 * M + 2 * s + 2 ≤ N) {l l' : LatticeLink d N}
    (hl : l ∈ timeSlab 0 s) (hl' : l' ∈ timeSlab 0 s) :
    (M : ℝ) ≤ timeDist (shiftLink (M : ZMod N) l) (mirrorLink l') := by
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
  unfold timeDist
  rw [hw]
  have hv : ((w : ZMod N)).val = w := ZMod.val_cast_of_lt hwN
  have : M ≤ cyc (w : ZMod N) := le_cyc (by rw [hv]; exact hw1) (by rw [hv]; omega)
  exact_mod_cast this

end TimeDist

/-- The slab pair of `slab_transfer_data` is at physical time distance `≥ n a_k`. -/
theorem slab_time_sep (T : Tuning) {k j : ℕ} {s : ℝ} {V : ℕ → ℕ} (O : SlabObs T s V) {n : ℕ}
    (hn : 2 * n + 2 * T.thick k s + 2 ≤ T.side k j) :
    ∀ e ∈ ((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image (shiftLink (n : ZMod (T.side k j))),
      ∀ e' ∈ ((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image mirrorLink, n * T.a k ≤ T.a k * timeDist e e' := by
  intro e he e' he'
  obtain ⟨l, hl, rfl⟩ := mem_image.1 he
  obtain ⟨l', hl', rfl⟩ := mem_image.1 he'
  have := sep_shift_mirror_time hn (Finset.mem_inter.mp hl).2 (Finset.mem_inter.mp hl').2
  rw [mul_comm (n : ℝ) (T.a k)]
  exact mul_le_mul_of_nonneg_left this (T.a_pos k).le

/-! ## The time-separated transfer -/

/-- **P5.2 for time-separated pairs (named hypothesis, open).** `ObsTransferPhys` restricted to `D ≥ 0` and to fine
observables `F`, `G` whose supports `A₀`, `B₀` (physical extent `≤ R`) are at physical **time** distance `≥ D`. The three
estimates are those of `ObsTransferPhys`: (a) a block approximant `f` with Dobrushin oscillation sum
`≤ 2K (1 + D/L₁)⁴`, uniform in the level; (b) `E[F|Φ] ≈ f ∘ Φ`, `E[G|Φ] ≈ g ∘ Φ` in `L¹`; (c) conditional decoupling. -/
def ObsTransferPhysT (T : Tuning) (B : BlockingFamily T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c K : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink 4 (T.side k j))) (D : ℝ), 0 ≤ D →
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R →
    (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * timeDist e e') →
    ∃ (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink 4 (coarseSide j))),
      Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A' ∧ DepOn g B' ∧
      (∃ vf : LatticeLink 4 (coarseSide j) → ℝ, OscBound f vf ∧ ∑ a ∈ A', vf a ≤ 2 * K * (1 + D / T.L₁) ^ 4) ∧
      (∀ x ∈ A', ∀ y ∈ B', D / 2 ≤ T.L₁ * linkDist x y) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) F U - f ((B k j).B U)| ∂(T.ym k j)
        ≤ c * Real.exp (-(m * D)) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) G U - g ((B k j).B U)| ∂(T.ym k j)
        ≤ c * Real.exp (-(m * D)) ∧
      |∫ U, F U * G U ∂(T.ym k j) -
          ∫ U, condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) F U *
            condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) G U ∂(T.ym k j)|
        ≤ c * Real.exp (-(m * D))

/-- `ObsTransferPhys` implies the time-separated form (D): time distance bounds the distance from below. -/
theorem obsTransferPhysT_of_phys {T : Tuning} {B : BlockingFamily T} (h : ObsTransferPhys T B) :
    ObsTransferPhysT T B := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, K, hc, k₀, Hk⟩ := H R
  refine ⟨c, K, hc, k₀, fun k hk j F G A₀ B₀ D _ mF mG bF bG gF gG dF dG eA eB hsep => ?_⟩
  exact Hk k hk j F G A₀ B₀ D mF mG bF bG gF gG dF dG eA eB fun e he e' he' =>
    (hsep e he e' he').trans (mul_le_mul_of_nonneg_left (timeDist_le_linkDist e e') (T.a_pos k).le)

/-- **Torus decay from the uniform block gap and the time-separated transfer** (S; the proof of
`H1.torusDecayLoc_of_blockGapUnif` with `slab_time_sep` in place of the all-direction separation). -/
theorem torusDecayLoc_of_blockGapUnifT {T : Tuning} (B : BlockingFamily T) {lam : ℝ} (hlam : 0 < lam)
    (hB : BlockGapUnif T B lam) (h3 : ObsTransferPhysT T B) : TorusDecayLoc T.toV := by
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

/-- **The torus route with D′ along the levels and the time-separated transfer** (open inputs): a blocking family,
`λ > 0`, `LevelDprime`, `ObsTransferPhysT`. -/
def LevelTorusRouteT (T : Tuning) : Prop :=
  ∃ (B : BlockingFamily T) (lam : ℝ), 0 < lam ∧ LevelDprime T B lam ∧ ObsTransferPhysT T B

/-- Cycle 3's level route implies the time-separated one (D): `LevelTorusRouteT` is weaker or equal. -/
theorem levelTorusRouteT_of_level {T : Tuning} (h : LevelTorusRoute T) : LevelTorusRouteT T := by
  obtain ⟨B, lam, hlam, hD, h3⟩ := h
  exact ⟨B, lam, hlam, hD, obsTransferPhysT_of_phys h3⟩

/-- **The time-separated level route gives the gap in both orders of limits** (S). -/
theorem bothOrdersLoc_of_levelRouteT {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (h : LevelTorusRouteT T) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV := by
  obtain ⟨B, lam, hlam, hD, h3⟩ := h
  have hT := torusDecayLoc_of_blockGapUnifT B hlam (blockGapUnif_of_levelDprime B hlam.le hD) h3
  exact ⟨hT, bothOrdersLoc_of_torusDecayLoc ha hT⟩

end ProofPhase.V3
