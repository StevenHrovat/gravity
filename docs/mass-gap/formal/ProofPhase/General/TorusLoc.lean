/-
Proof phase, generalisation phase 1c: torus decay for bounded physical extent over any gauge group and dimension
(2026-11-24). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 1c.
-/

import ProofPhase.General.Blocked

/-!
# Torus decay for observables of bounded physical extent, over any gauge group and dimension

`Torus/Local` for the Wilson measure of any `Gr` of the package in dimension `d`: `TorusDecayLoc` (one physical rate,
a level-uniform constant, for slab observables of bounded physical extent), the passage from one family's torus decay to
its gap in both orders of limits (`gapVF_of_family`, `gapMF_of_family`), `MassGapMFLoc`, `bothOrdersLoc_of_torusDecayLoc`,
and the blocked route `torusDecayLoc_of_blockedRoute`, `bothOrdersLoc_of_blockedRoute` (the tail constant `d!/a^d`
replaces `24/a^4`). `torusDecayLoc_of_torusDecay` (from workstream 4's `TorusDecay`) is not ported.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity

open ProofPhase (IsLimitPoint)
open ProofPhase.UV
open ProofPhase.Existence (side_ge)
open ProofPhase.RouteA (gaugeInvariant_tShift gaugeInvariant_thetaConn)
open OneScale.TimeShift (shiftSite)

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

section Loc

variable {Gr : Type*} [Group Gr] [TopologicalSpace Gr] [MeasurableSpace Gr] [HasHaarProbability Gr]
  (nr : ℕ) [HasGaugeTrace Gr nr] [GaugeGroupBase Gr] {d : ℕ} [NeZero d]

section Geometry

variable {N : ℕ} [NeZero N]

theorem shiftSite_sub (j : ZMod N) (x y : FinLatticeSites d N) (i : Fin d) :
    shiftSite j x i - shiftSite j y i = x i - y i := by
  by_cases h : i = 0
  · subst h; simp only [shiftSite, Function.update_self]; ring
  · simp only [shiftSite, Function.update_of_ne h]

theorem linkDist_shiftLink (j : ZMod N) (e e' : LatticeLink d N) :
    linkDist (shiftLink j e) (shiftLink j e') = linkDist e e' := by
  unfold linkDist siteDist
  simp only [shiftLink, shiftSite_sub]

theorem mirrorLink_site (l : LatticeLink d N) : ∃ ε : ZMod N, (ε = 0 ∨ ε = 1) ∧
    (mirrorLink l).site 0 = -(l.site 0) - ε ∧ ∀ i, i ≠ 0 → (mirrorLink l).site i = l.site i := by
  by_cases h : l.dir = 0
  · refine ⟨1, Or.inr rfl, ?_, fun i hi => ?_⟩
    · simp only [mirrorLink, h, ↓reduceIte, tflipSite_zero]
    · simp only [mirrorLink, h, ↓reduceIte, tflipSite, Function.update_of_ne hi]
  · refine ⟨0, Or.inl rfl, ?_, fun i hi => ?_⟩
    · simp only [mirrorLink, h, ↓reduceIte, reflSite_zero, sub_zero]
    · simp only [mirrorLink, h, ↓reduceIte, reflSite, Function.update_of_ne hi]

theorem siteDist_mirror_le (e e' : LatticeLink d N) :
    siteDist (mirrorLink e).site (mirrorLink e').site ≤ siteDist e.site e'.site + 1 := by
  obtain ⟨ε, hε, h0, hi⟩ := mirrorLink_site e
  obtain ⟨ε', hε', h0', hi'⟩ := mirrorLink_site e'
  refine siteDist_le fun i => ?_
  by_cases h : i = 0
  · subst h
    rw [h0, h0', show -(e.site 0) - ε - (-(e'.site 0) - ε') = (e'.site 0 - e.site 0) + (ε' - ε) by ring]
    have hc : cyc (ε' - ε) ≤ 1 := by
      rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl
      · simp [cyc_zero]
      · rw [sub_zero]; exact cyc_one_le
      · rw [zero_sub, cyc_neg]; exact cyc_one_le
      · simp [cyc_zero]
    have h1 : cyc (e'.site 0 - e.site 0) ≤ siteDist e.site e'.site := by
      rw [cyc_sub_comm]; exact cyc_le_siteDist _ _ 0
    exact (cyc_add_le _ _).trans (by omega)
  · rw [hi i h, hi' i h]
    exact (cyc_le_siteDist _ _ i).trans (Nat.le_succ _)

theorem linkDist_mirrorLink_le (e e' : LatticeLink d N) :
    linkDist (mirrorLink e) (mirrorLink e') ≤ linkDist e e' + 1 := by
  unfold linkDist
  exact_mod_cast siteDist_mirror_le e e'

end Geometry

theorem gapVF_of_family [GaugeRep Gr nr] {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) {m s : ℝ} (hm : 0 ≤ m) {Vb : ℕ → ℕ}
    (O : SlabObs Gr d T s Vb)
    (hdec : ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∃ C : ℝ, 0 ≤ C ∧ ∀ (j n : ℕ), 2 * n + 2 * T.thick k s + 2 ≤ T.side k j →
      |wcorr nr T k j (O.F k j) n| ≤ C * Real.exp (-(m * (n * T.a k))))
    {τ : ℝ} (hτ : 0 ≤ τ) {h : ℕ → ℝ} {g : ℝ}
    (hh : ∀ k, IsLimitPoint (fun j => wcorr nr T k j (O.F k j) (T.steps k τ)) (h k)) (hg : IsLimitPoint h g) :
    |g| ≤ 2 * Real.exp (-(m * τ)) := by
  obtain ⟨k₀, hk₀⟩ := hdec
  have hlev : ∀ k, k₀ ≤ k → |h k| ≤ 2 * Real.exp (-(m * (T.steps k τ * T.a k))) := by
    intro k hk
    obtain ⟨C, hC, hCk⟩ := hk₀ k hk
    set E := Real.exp (-(m * (T.steps k τ * T.a k)))
    have hE : Real.exp (-((m * T.a k) * T.steps k τ)) = E := by congr 1; ring
    have hr_bound : ∀ r : ℕ, 1 ≤ r → |h k| ≤ (2 + (1 / 2 : ℝ) ^ r * C) * E := by
      intro r hr
      refine (hh k).abs_le ?_
      filter_upwards [tendsto_atTop.1 (T.tendsto_side k) (2 ^ (r + 1) * T.steps k τ + 2 * T.thick k s + 2)]
        with j hj
      have := corr_le_of_decay (d := d) (N := T.side k j) (G := Gr) GaugeRep.continuous_rep
        GaugeRep.unitary_rep (T.even_side k j) (posWeight_wilson nr (T.β k))
        (O.meas k j) (O.bdd k j) (O.slab k j) hC (lam := m * T.a k)
        (fun t' ht' => by
          have := hCk j t' ht'
          rw [show -(m * T.a k * t') = -(m * (t' * T.a k)) by ring]
          exact this) hr hj
      rw [hE] at this
      exact this
    have hq : Tendsto (fun r : ℕ => (2 + (1 / 2 : ℝ) ^ r * C) * E) atTop (𝓝 ((2 + 0 * C) * E)) :=
      (tendsto_const_nhds.add
        ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const C)).mul_const E
    rw [zero_mul, add_zero] at hq
    exact ge_of_tendsto hq (eventually_atTop.2 ⟨1, fun r hr => hr_bound r hr⟩)
  have hb : ∀ k, k₀ ≤ k → |h k| ≤ 2 * Real.exp (-(m * (τ - T.a k))) := by
    intro k hk
    refine (hlev k hk).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    have := T.steps_mul_ge k hτ
    nlinarith
  obtain ⟨φ, hφ, ht⟩ := hg
  have hlim : Tendsto (fun k => 2 * Real.exp (-(m * (τ - T.a (φ k))))) atTop (𝓝 (2 * Real.exp (-(m * τ)))) := by
    have h1 : Tendsto (fun k => T.a (φ k)) atTop (𝓝 0) := ha.comp hφ.tendsto_atTop
    have h2 : Tendsto (fun k => -(m * (τ - T.a (φ k)))) atTop (𝓝 (-(m * (τ - 0)))) :=
      ((tendsto_const_nhds.sub h1).const_mul m).neg
    rw [sub_zero] at h2
    exact (Real.continuous_exp.tendsto _ |>.comp h2).const_mul 2
  refine le_of_tendsto_of_tendsto ht.abs hlim ?_
  filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop k₀)] with k hk
  exact hb (φ k) hk

theorem gapMF_of_family [GaugeRep Gr nr] {V : ProofPhase.Existence.VTuning} (ha : Tendsto V.T.a atTop (𝓝 0)) {m s : ℝ} (hm : 0 ≤ m) {Vb : ℕ → ℕ}
    (O : SlabObs Gr d V.T s Vb)
    (hdec : ∃ k₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k, k₀ ≤ k → ∀ (j n : ℕ), 2 * n + 2 * V.T.thick k s + 2 ≤ V.T.side k j →
      |vwcorr nr V k j (O.F k j) n| ≤ C * Real.exp (-(m * (n * V.T.a k))))
    {τ : ℝ} (hτ : 0 ≤ τ) {vol : ℕ → ℕ} (hvol : StrictMono vol) {h : ℕ → ℝ} {g : ℝ}
    (hh : ∀ p, IsLimitPoint (fun k => vwcorr nr V k (vol p) (O.F k (vol p)) (V.T.steps k τ)) (h p))
    (hg : IsLimitPoint h g) :
    |g| ≤ 2 * Real.exp (-(m * τ)) := by
  obtain ⟨k₀, C, hC, hCk⟩ := hdec
  set E := Real.exp (-(m * τ))
  have hr_bound : ∀ r : ℕ, 1 ≤ r → |g| ≤ (2 + (1 / 2 : ℝ) ^ r * C) * E := by
    intro r hr
    have hL := V.T.L₁_pos
    have hvolp : ∀ᶠ p in atTop, 2 ^ (r + 1) * τ + 2 * |s| + 4 * V.T.L₁ ≤ 2 * ((vol p : ℝ) + 1) * V.T.L₁ := by
      filter_upwards [(tendsto_natCast_atTop_atTop.comp hvol.tendsto_atTop).eventually_ge_atTop
        ((2 ^ (r + 1) * τ + 2 * |s| + 4 * V.T.L₁) / (2 * V.T.L₁))] with p hp
      have h1 := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * V.T.L₁)).1 hp
      simp only [Function.comp_apply] at h1
      nlinarith
    refine hg.abs_le ?_
    filter_upwards [hvolp] with p hp'
    have hB : Tendsto (fun k => (2 + (1 / 2 : ℝ) ^ r * C) * Real.exp (-(m * (τ - V.T.a k)))) atTop
        (𝓝 ((2 + (1 / 2 : ℝ) ^ r * C) * E)) := by
      have h1 : Tendsto (fun k => -(m * (τ - V.T.a k))) atTop (𝓝 (-(m * (τ - 0)))) :=
        ((tendsto_const_nhds.sub ha).const_mul m).neg
      rw [sub_zero] at h1
      exact (Real.continuous_exp.tendsto _ |>.comp h1).const_mul _
    refine _root_.ProofPhase.Existence.IsLimitPoint.abs_le_of_tendsto ?_ hB (hh p)
    filter_upwards [eventually_ge_atTop k₀] with k hk
    have hN := side_ge V.T k (vol p) hτ r hp'
    have hc := corr_le_of_decay (d := d) (N := V.T.side k (vol p)) (G := Gr) GaugeRep.continuous_rep
      GaugeRep.unitary_rep (V.T.even_side k (vol p))
      (posWeight_wilson nr (V.βv k (vol p))) (O.meas k (vol p)) (O.bdd k (vol p)) (O.slab k (vol p)) hC
      (lam := m * V.T.a k)
      (fun t' ht' => by
        have := hCk k hk (vol p) t' ht'
        rw [show -(m * V.T.a k * t') = -(m * (t' * V.T.a k)) by ring]
        exact this) hr hN
    refine hc.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity))
    nlinarith [mul_le_mul_of_nonneg_left (V.T.steps_mul_ge k hτ) hm]
  have hq : Tendsto (fun r : ℕ => (2 + (1 / 2 : ℝ) ^ r * C) * E) atTop (𝓝 ((2 + 0 * C) * E)) :=
    (tendsto_const_nhds.add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const C)).mul_const E
  rw [zero_mul, add_zero] at hq
  exact ge_of_tendsto hq (eventually_atTop.2 ⟨1, fun r hr => hr_bound r hr⟩)

section Explicit

variable (Gr) (d)

def TorusDecayLoc (V : ProofPhase.Existence.VTuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ (s R : ℝ), ∃ k₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k, k₀ ≤ k →
    ∀ (Vb : ℕ → ℕ) (j : ℕ) (O : SlabObs Gr d V.T s Vb), O.Extent R → ∀ n : ℕ,
      2 * n + 2 * V.T.thick k s + 2 ≤ V.T.side k j → |vwcorr nr V k j (O.F k j) n| ≤ C * Real.exp (-(m * (n * V.T.a k)))

def MassGapMFLoc (V : ProofPhase.Existence.VTuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ (s R : ℝ) (Vb : ℕ → ℕ) (O : SlabObs Gr d V.T s Vb), O.Extent R → ∀ (τ : ℝ), 0 ≤ τ →
    ∀ (vol : ℕ → ℕ), StrictMono vol → ∀ (h : ℕ → ℝ) (g : ℝ),
    (∀ p, IsLimitPoint (fun k => vwcorr nr V k (vol p) (O.F k (vol p)) (V.T.steps k τ)) (h p)) → IsLimitPoint h g →
      |g| ≤ 2 * Real.exp (-(m * τ))

variable [GaugeRep Gr nr]

theorem torusDecayLoc_of_blockedRoute {T : Tuning} (B : BlockingFamily Gr d T) {lam : ℝ} (hlam : 0 < lam)
    {Vk : ∀ j, ℕ → CoarsePot Gr d j} {Vinf : ∀ j, CoarsePot Gr d j} (h1 : H1Local nr T B lam Vk Vinf)
    (h2 : LimitDprime lam Vinf) (h3 : ObsTransferPhys nr T B) : TorusDecayLoc Gr nr d T.toV := by
  obtain ⟨γ, -, hγ1, k₀, hgap⟩ := blockGap_of_blockedRoute nr B hlam.le h1 h2
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
  -- the translated and the mirrored supports have physical extent `≤ R + L₁`
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

theorem bothOrdersLoc_of_torusDecayLoc {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (h : TorusDecayLoc Gr nr d T.toV) :
    MassGapLoc Gr nr d T ∧ MassGapMFLoc Gr nr d T.toV := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨⟨m, hm, fun s R Vb O hO τ hτ hk g hhk hg => ?_⟩, ⟨m, hm, fun s R Vb O hO τ hτ vol hvol hp g hhp hg => ?_⟩⟩
  · obtain ⟨k₀, C, hC, Hk⟩ := H s R
    exact gapVF_of_family nr ha hm.le O ⟨k₀, fun k hk => ⟨C, hC, fun j n hn => Hk k hk Vb j O hO n hn⟩⟩ hτ hhk hg
  · obtain ⟨k₀, C, hC, Hk⟩ := H s R
    exact gapMF_of_family nr (V := T.toV) ha hm.le O ⟨k₀, C, hC, fun k hk j n hn => Hk k hk Vb j O hO n hn⟩ hτ hvol hhp hg

theorem bothOrdersLoc_of_blockedRoute {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (B : BlockingFamily Gr d T) {lam : ℝ}
    (hlam : 0 < lam) {Vk : ∀ j, ℕ → CoarsePot Gr d j} {Vinf : ∀ j, CoarsePot Gr d j} (h1 : H1Local nr T B lam Vk Vinf)
    (h2 : LimitDprime lam Vinf) (h3 : ObsTransferPhys nr T B) :
    TorusDecayLoc Gr nr d T.toV ∧ MassGapLoc Gr nr d T ∧ MassGapMFLoc Gr nr d T.toV :=
  have hT := torusDecayLoc_of_blockedRoute Gr nr d B hlam h1 h2 h3
  ⟨hT, bothOrdersLoc_of_torusDecayLoc Gr nr d ha hT⟩

end Explicit

end Loc


/-! ## The SU(2), `d = 4` instances -/

section Instance

theorem linkDist_shiftLink_four {N : ℕ} [NeZero N] (j : ZMod N) (e e' : LatticeLink 4 N) :
    linkDist (shiftLink j e) (shiftLink j e') = linkDist e e' := linkDist_shiftLink j e e'

theorem linkDist_mirrorLink_le_four {N : ℕ} [NeZero N] (e e' : LatticeLink 4 N) :
    linkDist (mirrorLink e) (mirrorLink e') ≤ linkDist e e' + 1 := linkDist_mirrorLink_le (d := 4) e e'

example : @ProofPhase.Torus.linkDist_shiftLink = @linkDist_shiftLink_four := rfl
example : @ProofPhase.Torus.linkDist_mirrorLink_le = @linkDist_mirrorLink_le_four := rfl

theorem torusDecayLoc_iff (V : ProofPhase.Existence.VTuning) :
    ProofPhase.Torus.TorusDecayLoc V ↔ TorusDecayLoc SU2 2 4 V :=
  ⟨fun ⟨m, hm, H⟩ => ⟨m, hm, fun s R => by
      obtain ⟨k₀, C, hC, Hk⟩ := H s R
      exact ⟨k₀, C, hC, fun k hk Vb j O hO n hn => Hk k hk Vb j O.toOld hO n hn⟩⟩,
   fun ⟨m, hm, H⟩ => ⟨m, hm, fun s R => by
      obtain ⟨k₀, C, hC, Hk⟩ := H s R
      exact ⟨k₀, C, hC, fun k hk Vb j O hO n hn => Hk k hk Vb j (SlabObs.ofOld O) hO n hn⟩⟩⟩

theorem massGapMFLoc_iff (V : ProofPhase.Existence.VTuning) :
    ProofPhase.Torus.MassGapMFLoc V ↔ MassGapMFLoc SU2 2 4 V :=
  ⟨fun ⟨m, hm, H⟩ => ⟨m, hm, fun s R Vb O hO τ hτ vol hvol h g hh hg =>
      H s R Vb O.toOld hO τ hτ vol hvol h g hh hg⟩,
   fun ⟨m, hm, H⟩ => ⟨m, hm, fun s R Vb O hO τ hτ vol hvol h g hh hg =>
      H s R Vb (SlabObs.ofOld O) hO τ hτ vol hvol h g hh hg⟩⟩

theorem gapVF_of_family_su2 {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) {m s : ℝ} (hm : 0 ≤ m) {Vb : ℕ → ℕ}
    (O : ProofPhase.SlabObs T s Vb)
    (hdec : ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∃ C : ℝ, 0 ≤ C ∧ ∀ (j n : ℕ), 2 * n + 2 * T.thick k s + 2 ≤ T.side k j →
      |T.wcorr k j (O.F k j) n| ≤ C * Real.exp (-(m * (n * T.a k))))
    {τ : ℝ} (hτ : 0 ≤ τ) {h : ℕ → ℝ} {g : ℝ}
    (hh : ∀ k, IsLimitPoint (fun j => T.wcorr k j (O.F k j) (T.steps k τ)) (h k)) (hg : IsLimitPoint h g) :
    |g| ≤ 2 * Real.exp (-(m * τ)) :=
  gapVF_of_family (Gr := SU2) 2 (d := 4) ha hm (SlabObs.ofOld O) hdec hτ hh hg

theorem gapMF_of_family_su2 {V : ProofPhase.Existence.VTuning} (ha : Tendsto V.T.a atTop (𝓝 0)) {m s : ℝ} (hm : 0 ≤ m) {Vb : ℕ → ℕ}
    (O : ProofPhase.SlabObs V.T s Vb)
    (hdec : ∃ k₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k, k₀ ≤ k → ∀ (j n : ℕ), 2 * n + 2 * V.T.thick k s + 2 ≤ V.T.side k j →
      |V.wcorr k j (O.F k j) n| ≤ C * Real.exp (-(m * (n * V.T.a k))))
    {τ : ℝ} (hτ : 0 ≤ τ) {vol : ℕ → ℕ} (hvol : StrictMono vol) {h : ℕ → ℝ} {g : ℝ}
    (hh : ∀ p, IsLimitPoint (fun k => V.wcorr k (vol p) (O.F k (vol p)) (V.T.steps k τ)) (h p))
    (hg : IsLimitPoint h g) :
    |g| ≤ 2 * Real.exp (-(m * τ)) :=
  gapMF_of_family (Gr := SU2) 2 (d := 4) ha hm (SlabObs.ofOld O) hdec hτ hvol hh hg

theorem torusDecayLoc_of_blockedRoute_su2 {T : Tuning} (B : ProofPhase.BlockingFamily T) {lam : ℝ} (hlam : 0 < lam)
    {Vk : ∀ j, ℕ → ProofPhase.CoarsePot j} {Vinf : ∀ j, ProofPhase.CoarsePot j} (h1 : ProofPhase.H1Local T B lam Vk Vinf)
    (h2 : ProofPhase.LimitDprime lam Vinf) (h3 : ProofPhase.ObsTransferPhys T B) : ProofPhase.Torus.TorusDecayLoc T.toV :=
  (torusDecayLoc_iff _).2 (torusDecayLoc_of_blockedRoute SU2 2 4 B hlam h1 h2 h3)

theorem bothOrdersLoc_of_torusDecayLoc_su2 {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (h : ProofPhase.Torus.TorusDecayLoc T.toV) :
    ProofPhase.MassGapLoc T ∧ ProofPhase.Torus.MassGapMFLoc T.toV :=
  by
    have := bothOrdersLoc_of_torusDecayLoc SU2 2 4 ha ((torusDecayLoc_iff _).1 h)
    exact ⟨(massGapLoc_iff T).2 this.1, (massGapMFLoc_iff _).2 this.2⟩

theorem bothOrdersLoc_of_blockedRoute_su2 {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (B : ProofPhase.BlockingFamily T) {lam : ℝ}
    (hlam : 0 < lam) {Vk : ∀ j, ℕ → ProofPhase.CoarsePot j} {Vinf : ∀ j, ProofPhase.CoarsePot j} (h1 : ProofPhase.H1Local T B lam Vk Vinf)
    (h2 : ProofPhase.LimitDprime lam Vinf) (h3 : ProofPhase.ObsTransferPhys T B) :
    ProofPhase.Torus.TorusDecayLoc T.toV ∧ ProofPhase.MassGapLoc T ∧ ProofPhase.Torus.MassGapMFLoc T.toV :=
  by
    have := bothOrdersLoc_of_blockedRoute SU2 2 4 ha B hlam h1 h2 h3
    exact ⟨(torusDecayLoc_iff _).2 this.1, (massGapLoc_iff T).2 this.2.1, (massGapMFLoc_iff _).2 this.2.2⟩

example : @ProofPhase.Torus.gapVF_of_family = @gapVF_of_family_su2 := rfl
example : @ProofPhase.Torus.gapMF_of_family = @gapMF_of_family_su2 := rfl

end Instance

end ProofPhase.General
