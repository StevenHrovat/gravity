/-
Proof phase, cycle 2, workstream C: the observable transfer counted in physical size (L₁ cells), torus decay with a
level-uniform constant for observables of bounded physical extent, and the gap in both orders of limits (2026-11-22).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c2c-torus/NOTE.md`.
-/

import ProofPhase.RouteA.BlockedSlab

/-!
# `ObsTransferPhys` and `TorusDecayLoc`: the blocked route reaches the gap in both orders of limits

**Why `ObsTransfer` reaches only `SlabDecay`** (workstream 3, `ws3-quantum/NOTE.md` §4.3; workstream 1, §3.2): it bounds
the number of coarse links of the block approximant by `K (|A₀| + 1)(1 + D/L₁)⁴`, with `|A₀|` the number of **fine**
links of the observable. An observable of fixed physical size has of order `(R/a_k)⁴` fine links, so the constant of
`SlabDecay` grows with the level.

**The restatement.** `ProofPhase.ObsTransferPhys` (in `ProofPhase.Assembly`, because `OpenPieces` names it) asks the
same three estimates (quasi-locality of `E[F|Φ]` twice, conditional decoupling) only for observables whose support has
**physical extent** `≤ R` (`PhysExtent`: any two links at physical distance `≤ R`), with a block approximant whose
Dobrushin oscillation sum is at most `2K_R (1 + D/L₁)⁴`, uniformly in the level. Its literal "counted in `L₁` cells" form
`ObsTransferCell` (coarse support `≤ K (1 + R/L₁)⁴ (1 + D/L₁)⁴` links, one `K` for all `R`) implies it
(`obsTransferPhys_of_cell`), and so does workstream 1's `ObsTransferU` (`obsTransferPhys_of_U`, through the counting
lemma `card_le_of_siteDist`: a set of links of `ℓ^∞` diameter `≤ r` has at most `4 (2r + 1)⁴` elements). So
`ObsTransferPhys` is the weakest of the three transfer hypotheses that give a level-uniform constant.

**The theorems.**
* `torusDecayLoc_of_blockedRoute` (**substantive reduction**): `H1Local ∧ LimitDprime (λ > 0) ∧ ObsTransferPhys ⇒
  TorusDecayLoc T.toV`: one physical rate `min(λ/(4L₁), m)`; for every slab thickness `s` and physical extent `R` one
  level `k₀` and one constant `C`, independent of the level, the volume and the number of fine links, such that every
  slab observable family of physical extent `≤ R` decays on every torus as `C e^{-m n a_k}` while it fits.
* `bothOrdersLoc_of_torusDecayLoc`: `TorusDecayLoc ⇒ MassGapLoc ∧ MassGapMFLoc` (volume first then spacing, and spacing
  first at fixed physical volume then volume, the OpenAI order), through the per-family forms `gapVF_of_family`,
  `gapMF_of_family` of the assembly's Theorem C argument and workstream 4's `massGapMF_of_torusDecay`.
* `torusDecayLoc_of_torusDecay`: workstream 4's `TorusDecay` (all observables, constant depending on the support bound)
  implies `TorusDecayLoc`, so the new target is weaker. `massGapMFLoc_of_massGapMF`: likewise for the gap.

**The observable class** (`SlabObs.Extent O R`): measurable, gauge-invariant slab observables `|F| ≤ 1` whose support
has physical extent `≤ R` at every level and volume, any number of fine links. It contains every fixed local
gauge-invariant observable of bounded physical extent (Wilson loops of physical size, smeared or averaged fields over a
bounded region) and every lattice-scale family (extent `→ 0`). It misses only families whose physical extent is
unbounded (volume averages over the whole torus, loops winding around the torus, families spreading as `k → ∞`). For the
Clay gap these do not matter: the vectors `F Ω` of bounded-extent local observables are dense in the reconstructed
Hilbert space, so one rate for all of them gives the spectral gap (`spectral_gap_of_decay` per vector; see the note).

**Claim level.** All physics is in `H1Local`, `LimitDprime`, `ObsTransferPhys` (open); the reduction is group-blind in its
proof but stated for the SU(2) Wilson measure along a tuning.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift OneScale.CubeChain Positivity ProofPhase.Existence ProofPhase.RouteA

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Torus

/-! ## Geometry: translations keep the link distance, reflections change it by at most one -/

section Geometry

variable {N : ℕ} [NeZero N]

theorem shiftSite_sub (j : ZMod N) (x y : FinLatticeSites 4 N) (i : Fin 4) :
    shiftSite j x i - shiftSite j y i = x i - y i := by
  by_cases h : i = 0
  · subst h; simp only [shiftSite, Function.update_self]; ring
  · simp only [shiftSite, Function.update_of_ne h]

theorem linkDist_shiftLink (j : ZMod N) (e e' : LatticeLink 4 N) :
    linkDist (shiftLink j e) (shiftLink j e') = linkDist e e' := by
  unfold linkDist siteDist
  simp only [shiftLink, shiftSite_sub]

/-- The mirror image of a link: time coordinate `−t` (spatial links) or `−t − 1` (temporal links), other coordinates
unchanged. -/
theorem mirrorLink_site (l : LatticeLink 4 N) : ∃ ε : ZMod N, (ε = 0 ∨ ε = 1) ∧
    (mirrorLink l).site 0 = -(l.site 0) - ε ∧ ∀ i, i ≠ 0 → (mirrorLink l).site i = l.site i := by
  by_cases h : l.dir = 0
  · refine ⟨1, Or.inr rfl, ?_, fun i hi => ?_⟩
    · simp only [mirrorLink, h, ↓reduceIte, tflipSite_zero]
    · simp only [mirrorLink, h, ↓reduceIte, tflipSite, Function.update_of_ne hi]
  · refine ⟨0, Or.inl rfl, ?_, fun i hi => ?_⟩
    · simp only [mirrorLink, h, ↓reduceIte, reflSite_zero, sub_zero]
    · simp only [mirrorLink, h, ↓reduceIte, reflSite, Function.update_of_ne hi]

theorem siteDist_mirror_le (e e' : LatticeLink 4 N) :
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

theorem linkDist_mirrorLink_le (e e' : LatticeLink 4 N) :
    linkDist (mirrorLink e) (mirrorLink e') ≤ linkDist e e' + 1 := by
  unfold linkDist
  exact_mod_cast siteDist_mirror_le e e'

/-- **Counting**: a set of links whose base sites are pairwise at `ℓ^∞` cyclic distance `≤ r` has at most
`4 (2r + 1)⁴` elements (independent of the torus). -/
theorem card_le_of_siteDist {A : Finset (LatticeLink 4 N)} {r : ℕ}
    (h : ∀ e ∈ A, ∀ e' ∈ A, siteDist e.site e'.site ≤ r) : A.card ≤ 4 * (2 * r + 1) ^ 4 := by
  rcases A.eq_empty_or_nonempty with hA | ⟨e₀, he₀⟩
  · simp [hA]
  set S : Finset ((Fin 4 → ℤ) × Fin 4) :=
    Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(r : ℤ)) r) ×ˢ Finset.univ with hS
  have hsub : A ⊆ S.image (fun p => (⟨fun i => e₀.site i + ((p.1 i : ℤ) : ZMod N), p.2⟩ : LatticeLink 4 N)) := by
    intro e he
    refine Finset.mem_image.2 ⟨(fun i => (e.site i - e₀.site i).valMinAbs, e.dir), ?_, ?_⟩
    · refine Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, Finset.mem_univ _⟩
      have h1 : cyc (e.site i - e₀.site i) ≤ r := (cyc_le_siteDist _ _ i).trans (h e he e₀ he₀)
      have h2 : |(e.site i - e₀.site i).valMinAbs| ≤ (r : ℤ) := by
        rw [Int.abs_eq_natAbs]; exact_mod_cast h1
      exact Finset.mem_Icc.2 (abs_le.1 h2)
    · obtain ⟨site, dir⟩ := e
      show LatticeLink.mk _ _ = LatticeLink.mk site dir
      congr 1
      funext i
      simp only [ZMod.coe_valMinAbs]
      ring
  have hI : (Finset.Icc (-(r : ℤ)) r).card = 2 * r + 1 := by rw [Int.card_Icc]; omega
  calc A.card ≤ (S.image _).card := Finset.card_le_card hsub
    _ ≤ S.card := Finset.card_image_le
    _ = 4 * (2 * r + 1) ^ 4 := by
      rw [hS, Finset.card_product, Fintype.card_piFinset, Finset.card_univ, Fintype.card_fin]
      simp only [hI, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring

/-- Physical extent `≤ R` at level `k` bounds the lattice diameter by `⌊R/a_k⌋`. -/
theorem siteDist_le_floor {T : Tuning} {k : ℕ} {A : Finset (LatticeLink 4 N)} {R : ℝ} (h : PhysExtent T k A R) :
    ∀ e ∈ A, ∀ e' ∈ A, siteDist e.site e'.site ≤ ⌊R / T.a k⌋₊ := by
  intro e he e' he'
  apply Nat.le_floor
  rw [le_div_iff₀ (T.a_pos k)]
  have := h e he e' he'
  unfold linkDist at this
  rw [mul_comm] at this
  exact this

/-- A family of physical extent `≤ R` has at most `4 (2⌊R/a_k⌋ + 1)⁴` fine links at level `k`. -/
theorem card_le_of_physExtent {T : Tuning} {k : ℕ} {A : Finset (LatticeLink 4 N)} {R : ℝ} (h : PhysExtent T k A R) :
    A.card ≤ 4 * (2 * ⌊R / T.a k⌋₊ + 1) ^ 4 :=
  card_le_of_siteDist (siteDist_le_floor h)

end Geometry

/-! ## The transfer hypotheses compared -/

/-- **P5.2 counted in `L₁` cells (literal form).** As `ObsTransfer` (one `c`, `m`, `K`), but for observables whose
supports have physical extent `≤ R`, with the coarse support of the approximant bounded by
`K (1 + R/L₁)⁴ (1 + D/L₁)⁴` links (the number of `L₁` cells of a region of extent `R + D`, up to a constant) instead of
`K (|A₀| + 1)(1 + D/L₁)⁴`. -/
def ObsTransferCell (T : Tuning) (B : BlockingFamily T) : Prop :=
  ∃ c m K : ℝ, 0 ≤ c ∧ 0 < m ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (R : ℝ) (j : ℕ)
    (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink 4 (T.side k j))) (D : ℝ),
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R →
    (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * linkDist e e') →
    ∃ (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink 4 (coarseSide j))),
      Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A' ∧ DepOn g B' ∧
      (A'.card : ℝ) ≤ K * (1 + R / T.L₁) ^ 4 * (1 + D / T.L₁) ^ 4 ∧
      (B'.card : ℝ) ≤ K * (1 + R / T.L₁) ^ 4 * (1 + D / T.L₁) ^ 4 ∧
      (∀ x ∈ A', ∀ y ∈ B', D / 2 ≤ T.L₁ * linkDist x y) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) F U - f ((B k j).B U)| ∂(T.ym k j)
        ≤ c * Real.exp (-(m * D)) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) G U - g ((B k j).B U)| ∂(T.ym k j)
        ≤ c * Real.exp (-(m * D)) ∧
      |∫ U, F U * G U ∂(T.ym k j) -
          ∫ U, condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) F U *
            condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) G U ∂(T.ym k j)|
        ≤ c * Real.exp (-(m * D))

/-- **The cell count implies the physical-size form** (a coarse support of `n` links carries the oscillation bound
`2·1_{A'}`, of total `2n`). -/
theorem obsTransferPhys_of_cell {T : Tuning} {B : BlockingFamily T} (h : ObsTransferCell T B) :
    ObsTransferPhys T B := by
  obtain ⟨c, m, K, hc, hm, k₀, H⟩ := h
  refine ⟨m, hm, fun R => ⟨c, K * (1 + R / T.L₁) ^ 4, hc, k₀,
    fun k hk j F G A₀ B₀ D mF mG bF bG gF gG dF dG eA eB hsep => ?_⟩⟩
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hA', -, hsep', hEF, hEG, hdec⟩ :=
    H k hk R j F G A₀ B₀ D mF mG bF bG gF gG dF dG eA eB hsep
  obtain ⟨hvf, hsum⟩ := oscBound_indicator bf dfA
  refine ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, ⟨_, hvf, ?_⟩, hsep', hEF, hEG, hdec⟩
  rw [hsum]
  calc 2 * (A'.card : ℝ) ≤ 2 * (K * (1 + R / T.L₁) ^ 4 * (1 + D / T.L₁) ^ 4) := by linarith
    _ = 2 * (K * (1 + R / T.L₁) ^ 4) * (1 + D / T.L₁) ^ 4 := by ring

/-- **Workstream 1's level-uniform transfer implies the physical-size form**: an observable of physical extent `≤ R`
at level `k` has at most `4 (2⌊R/a_k⌋ + 1)⁴` fine links, so `ObsTransferU` with that support bound applies. Hence
`ObsTransferPhys` is the weaker hypothesis; it asks nothing of observables spread over the torus (workstream 1's hard
case for `ObsTransferU`). -/
theorem obsTransferPhys_of_U {T : Tuning} {B : BlockingFamily T} (h : ObsTransferU T B) : ObsTransferPhys T B := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, K, hc, k₀, Hk⟩ := H (fun k => 4 * (2 * ⌊R / T.a k⌋₊ + 1) ^ 4)
  exact ⟨c, K, hc, k₀, fun k hk j F G A₀ B₀ D mF mG bF bG gF gG dF dG eA eB hsep =>
    Hk k hk j F G A₀ B₀ D mF mG bF bG gF gG dF dG (card_le_of_physExtent eA) (card_le_of_physExtent eB) hsep⟩

/-! ## Torus decay for observables of bounded physical extent -/

/-- **Torus decay for observables of bounded physical extent, uniform in depth and volume**: one physical rate `m > 0`;
for every slab thickness `s` and physical extent `R` one level `k₀` and one constant `C` (independent of the level, the
volume and the number of fine links) such that every slab observable family of physical extent `≤ R` satisfies
`|Cov(F ∘ S_n, F ∘ Θ)| ≤ C e^{-m n a_k}` on every torus at every level `k ≥ k₀` while it fits. -/
def TorusDecayLoc (V : VTuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ (s R : ℝ), ∃ k₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k, k₀ ≤ k →
    ∀ (Vb : ℕ → ℕ) (j : ℕ) (O : SlabObs V.T s Vb), O.Extent R → ∀ n : ℕ,
      2 * n + 2 * V.T.thick k s + 2 ≤ V.T.side k j → |V.wcorr k j (O.F k j) n| ≤ C * Real.exp (-(m * (n * V.T.a k)))

/-- `TorusDecay` (workstream 4, all observables) implies `TorusDecayLoc`: a family of extent `≤ R` is a family with the
support bound `4 (2⌊R/a_k⌋ + 1)⁴`. -/
theorem torusDecayLoc_of_torusDecay {V : VTuning} (h : TorusDecay V) : TorusDecayLoc V := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun s R => ?_⟩
  obtain ⟨k₀, C, hC, Hk⟩ := H s (fun k => 4 * (2 * ⌊R / V.T.a k⌋₊ + 1) ^ 4)
  refine ⟨k₀, C, hC, fun k hk Vb j O hO n hn => ?_⟩
  let O' : SlabObs V.T s (fun k => 4 * (2 * ⌊R / V.T.a k⌋₊ + 1) ^ 4) :=
    { F := O.F, meas := O.meas, bdd := O.bdd, gauge := O.gauge, slab := O.slab, supp := O.supp,
      supp_card := fun k j => card_le_of_physExtent (fun e he e' he' => hO k j e he e' he'), dep := O.dep }
  exact Hk k hk j O' n hn

/-- **The blocked route with the transfer counted in physical size gives torus decay for observables of bounded
physical extent** (substantive reduction). For a reflection-respecting blocking family `B` of the SU(2) Wilson measure
along `T` and `λ > 0`: `H1Local ∧ LimitDprime ∧ ObsTransferPhys ⇒ TorusDecayLoc T.toV`, with the physical rate
`min(λ/(4L₁), m)`. The constant depends on `R` (through `ObsTransferPhys` at extent `R + L₁`) and on nothing else. -/
theorem torusDecayLoc_of_blockedRoute {T : Tuning} (B : BlockingFamily T) {lam : ℝ} (hlam : 0 < lam)
    {Vk : ∀ j, ℕ → CoarsePot j} {Vinf : ∀ j, CoarsePot j} (h1 : H1Local T B lam Vk Vinf)
    (h2 : LimitDprime lam Vinf) (h3 : ObsTransferPhys T B) : TorusDecayLoc T.toV := by
  obtain ⟨γ, -, hγ1, k₀, hgap⟩ := blockGap_of_blockedRoute B hlam.le h1 h2
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

/-! ## From torus decay of one family to its gap, in both orders of limits -/

/-- **Volume first, then spacing, for one family** (Theorem C on the torus removes the level constant, as in
`latticeGap_of_slabDecay` and `massGap_of_latticeGap`). -/
theorem gapVF_of_family {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) {m s : ℝ} (hm : 0 ≤ m) {Vb : ℕ → ℕ}
    (O : SlabObs T s Vb)
    (hdec : ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∃ C : ℝ, 0 ≤ C ∧ ∀ (j n : ℕ), 2 * n + 2 * T.thick k s + 2 ≤ T.side k j →
      |T.wcorr k j (O.F k j) n| ≤ C * Real.exp (-(m * (n * T.a k))))
    {τ : ℝ} (hτ : 0 ≤ τ) {h : ℕ → ℝ} {g : ℝ}
    (hh : ∀ k, IsLimitPoint (fun j => T.wcorr k j (O.F k j) (T.steps k τ)) (h k)) (hg : IsLimitPoint h g) :
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
      have := corr_le_of_decay (d := 4) (N := T.side k j) (G := SU2) continuous_subtype_val
        (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) (T.even_side k j) (posWeight_wilson 2 (T.β k))
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

/-- **Spacing first at fixed physical volume, then volume, for one family** (workstream 4's
`massGapMF_of_torusDecay`, per family; needs the level-uniform constant). -/
theorem gapMF_of_family {V : VTuning} (ha : Tendsto V.T.a atTop (𝓝 0)) {m s : ℝ} (hm : 0 ≤ m) {Vb : ℕ → ℕ}
    (O : SlabObs V.T s Vb)
    (hdec : ∃ k₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k, k₀ ≤ k → ∀ (j n : ℕ), 2 * n + 2 * V.T.thick k s + 2 ≤ V.T.side k j →
      |V.wcorr k j (O.F k j) n| ≤ C * Real.exp (-(m * (n * V.T.a k))))
    {τ : ℝ} (hτ : 0 ≤ τ) {vol : ℕ → ℕ} (hvol : StrictMono vol) {h : ℕ → ℝ} {g : ℝ}
    (hh : ∀ p, IsLimitPoint (fun k => V.wcorr k (vol p) (O.F k (vol p)) (V.T.steps k τ)) (h p))
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
    have hc := corr_le_of_decay (d := 4) (N := V.T.side k (vol p)) (G := SU2) continuous_subtype_val
      (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) (V.T.even_side k (vol p))
      (posWeight_wilson 2 (V.βv k (vol p))) (O.meas k (vol p)) (O.bdd k (vol p)) (O.slab k (vol p)) hC
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

/-- **The gap in the OpenAI order for observables of bounded physical extent** (`MassGapMF` restricted to
`SlabObs.Extent`). -/
def MassGapMFLoc (V : VTuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ (s R : ℝ) (Vb : ℕ → ℕ) (O : SlabObs V.T s Vb), O.Extent R → ∀ (τ : ℝ), 0 ≤ τ →
    ∀ (vol : ℕ → ℕ), StrictMono vol → ∀ (h : ℕ → ℝ) (g : ℝ),
    (∀ p, IsLimitPoint (fun k => V.wcorr k (vol p) (O.F k (vol p)) (V.T.steps k τ)) (h p)) → IsLimitPoint h g →
      |g| ≤ 2 * Real.exp (-(m * τ))

theorem massGapMFLoc_of_massGapMF {V : VTuning} (h : MassGapMF V) : MassGapMFLoc V := by
  obtain ⟨m, hm, H⟩ := h
  exact ⟨m, hm, fun s _ Vb O _ τ hτ vol hvol hp g hhp hg => H s Vb O τ hτ vol hvol hp g hhp hg⟩

/-- **Both orders of limits from torus decay for bounded physical extent.** -/
theorem bothOrdersLoc_of_torusDecayLoc {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (h : TorusDecayLoc T.toV) :
    MassGapLoc T ∧ MassGapMFLoc T.toV := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨⟨m, hm, fun s R Vb O hO τ hτ hk g hhk hg => ?_⟩, ⟨m, hm, fun s R Vb O hO τ hτ vol hvol hp g hhp hg => ?_⟩⟩
  · obtain ⟨k₀, C, hC, Hk⟩ := H s R
    exact gapVF_of_family ha hm.le O ⟨k₀, fun k hk => ⟨C, hC, fun j n hn => Hk k hk Vb j O hO n hn⟩⟩ hτ hhk hg
  · obtain ⟨k₀, C, hC, Hk⟩ := H s R
    exact gapMF_of_family (V := T.toV) ha hm.le O ⟨k₀, C, hC, fun k hk j n hn => Hk k hk Vb j O hO n hn⟩ hτ hvol hhp hg

/-- **The blocked route at `L₁` with the transfer in physical size gives the gap for observables of bounded physical
extent in both orders of limits.** -/
theorem bothOrdersLoc_of_blockedRoute {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (B : BlockingFamily T) {lam : ℝ}
    (hlam : 0 < lam) {Vk : ∀ j, ℕ → CoarsePot j} {Vinf : ∀ j, CoarsePot j} (h1 : H1Local T B lam Vk Vinf)
    (h2 : LimitDprime lam Vinf) (h3 : ObsTransferPhys T B) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV :=
  have hT := torusDecayLoc_of_blockedRoute B hlam h1 h2 h3
  ⟨hT, bothOrdersLoc_of_torusDecayLoc ha hT⟩

end ProofPhase.Torus
