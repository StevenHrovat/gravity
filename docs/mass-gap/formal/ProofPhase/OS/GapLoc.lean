/-
Proof phase, windowed OS reconstruction (os-windowed), module 3: from the windowed estimate to `MassGapLoc` through
limit points (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/os-windowed/NOTE.md`; pack `m1-tools/PACK-OSDATA.md`, route A.
-/

import ProofPhase.OS.Torus

/-!
# The windowed route to `MassGapLoc`

`MassGapLoc` asks only for limit points of finite-volume correlations (volume first, then spacing). So no
infinite-volume measure and no OS Hilbert space are needed: at a fixed level `k` the finite-volume estimate
`torus_gap_approx` has three error terms, and each vanishes in the right limit.

* `2^{-r} C_ℓ` (the approximant's constant): `r → ∞` as the torus grows, at fixed block index `ℓ`;
* `2√(2ε_ℓ) + ε_ℓ` and `(2 + 2M)√ε_ℓ` (the approximation error): `ε_ℓ → 0` as the block index `ℓ → ∞`, uniformly
  in the volume.

**Data per family and level.**
* `WinApprox T λ k F`: approximants `g ℓ j` (bounded measurable, on a time slab `[0, w_ℓ]` independent of the volume)
  with OS distance `≤ ε_ℓ → 0` uniformly in the volume `j`, and a decay bound for their connected correlations
  `|wcorr (g ℓ j) t| ≤ C_ℓ e^{-λ t}` with `C_ℓ` uniform in the volume, while it fits. This is the block-level gap for
  the approximants only: no block subspace has to be `τ`-invariant, and the constants may depend on `ℓ`.
* `UVTVApprox T λ k F`: the same, with the OS distance supplied by **M1's split**: `g ℓ j` is a bounded version of
  `E[F | 𝓗_ℓ]`, and M1's (B) and (A) terms are bounded by `b_B ℓ`, `b_A ℓ` (uniformly in the volume), both `→ 0`.
  `UVTVApprox.toWinApprox` turns it into `WinApprox` with `ε = b_B + 2 b_A` (`approx_le_of_UVTV`).

**Results.**
* `level_gap`: at a level with `WinApprox`, every infinite-volume limit point `h` of `wcorr k j (F k j) t` satisfies
  `|h| ≤ 2 e^{-λ t}`.
* `massGapLoc_of_winBlockGap`, `massGapLoc_of_UVTVBlockGap` (**headline**): if `a_k → 0` and every slab family of
  bounded physical extent has, from some level on, windowed block data at the physical rate `m` (lattice rate
  `m a_k`), then `MassGapLoc T`. The second form takes M1's (A)/(B) bounds directly, so M1's `OSData` hypothesis (the OS
  reconstruction) is no longer an input: only the block-level gap of the approximants and the UV-TV bounds are.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.OS

/-- **Windowed block data for one family at level `k`**: approximants with OS distance `ε_ℓ → 0` and a block-level
decay bound, both uniform in the volume. -/
structure WinApprox (T : Tuning) (lam : ℝ) (k : ℕ) (F : ∀ j, GaugeConnection SU2 4 (T.side k j) → ℝ) where
  /-- The time slab `[0, w ℓ]` of the approximants at block index `ℓ`. -/
  w : ℕ → ℕ
  /-- The approximants. -/
  g : ℕ → ∀ j, GaugeConnection SU2 4 (T.side k j) → ℝ
  M : ℝ
  meas : ∀ ℓ j, Measurable (g ℓ j)
  bdd : ∀ ℓ j U, |g ℓ j U| ≤ M
  slab : ∀ ℓ j, LinkDep (g ℓ j) (timeSlab 0 (w ℓ))
  /-- The approximation error in the OS seminorm, uniform in the volume. -/
  ε : ℕ → ℝ
  ε_lim : Tendsto ε atTop (𝓝 0)
  approx : ∀ ℓ j, ∫ U, (F j (thetaConn U) - g ℓ j (thetaConn U)) * (F j U - g ℓ j U) ∂(T.ym k j) ≤ ε ℓ
  /-- The block-level gap of the approximants, with a constant uniform in the volume. -/
  C : ℕ → ℝ
  C_nonneg : ∀ ℓ, 0 ≤ C ℓ
  decay : ∀ ℓ j t, 2 * t + 2 * w ℓ + 2 ≤ T.side k j → |T.wcorr k j (g ℓ j) t| ≤ C ℓ * Real.exp (-(lam * t))

theorem timeSlab_mono {d N : ℕ} [NeZero d] [NeZero N] {a b : ℕ} (h : a ≤ b) :
    (timeSlab 0 a : Finset (LatticeLink d N)) ⊆ timeSlab 0 b := by
  intro l hl
  rw [mem_timeSlab] at hl ⊢
  exact ⟨hl.1, hl.2.trans h⟩

/-- **The gap at one level, through infinite-volume limit points.** -/
theorem level_gap {T : Tuning} {lam : ℝ} {k : ℕ} {s : ℝ} {Vb : ℕ → ℕ} (O : SlabObs T s Vb)
    (A : WinApprox T lam k (O.F k)) (t : ℕ) {h : ℝ} (hh : IsLimitPoint (fun j => T.wcorr k j (O.F k j) t) h) :
    |h| ≤ 2 * Real.exp (-(lam * t)) := by
  set E := Real.exp (-(lam * t))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  -- the finite-volume estimate, eventually in the volume, for every `ℓ` and `r ≥ 1`
  have hbound : ∀ ℓ r : ℕ, 1 ≤ r → |h| ≤ (2 + 2 * Real.sqrt (2 * A.ε ℓ) + A.ε ℓ + (1 / 2 : ℝ) ^ r * A.C ℓ) * E +
      (2 + 2 * A.M) * Real.sqrt (A.ε ℓ) := by
    intro ℓ r hr
    set W := max (T.thick k s) (A.w ℓ)
    refine hh.abs_le ?_
    filter_upwards [tendsto_atTop.1 (T.tendsto_side k) (2 ^ (r + 1) * t + 2 * W + 2)] with j hj
    have hFs : LinkDep (O.F k j) (timeSlab 0 W) := LinkDep.mono (O.slab k j) (timeSlab_mono (le_max_left _ _))
    have hgs : LinkDep (A.g ℓ j) (timeSlab 0 W) := LinkDep.mono (A.slab ℓ j) (timeSlab_mono (le_max_right _ _))
    have hW : A.w ℓ ≤ W := le_max_right _ _
    exact torus_gap_approx (d := 4) (N := T.side k j) (G := SU2) continuous_subtype_val
      (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) (T.even_side k j) (posWeight_wilson 2 (T.β k))
      (O.meas k j) (O.bdd k j) (A.meas ℓ j) (A.bdd ℓ j) hFs hgs (A.approx ℓ j) (A.C_nonneg ℓ)
      (fun t' ht' => A.decay ℓ j t' (by omega)) hr hj
  -- `r → ∞`
  have hbound' : ∀ ℓ, |h| ≤ (2 + 2 * Real.sqrt (2 * A.ε ℓ) + A.ε ℓ) * E + (2 + 2 * A.M) * Real.sqrt (A.ε ℓ) := by
    intro ℓ
    have hq : Tendsto (fun r : ℕ => (2 + 2 * Real.sqrt (2 * A.ε ℓ) + A.ε ℓ + (1 / 2 : ℝ) ^ r * A.C ℓ) * E +
        (2 + 2 * A.M) * Real.sqrt (A.ε ℓ)) atTop
        (𝓝 ((2 + 2 * Real.sqrt (2 * A.ε ℓ) + A.ε ℓ + 0 * A.C ℓ) * E + (2 + 2 * A.M) * Real.sqrt (A.ε ℓ))) :=
      ((tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const
        (A.C ℓ))).mul_const E).add tendsto_const_nhds
    rw [zero_mul, add_zero] at hq
    exact ge_of_tendsto hq (eventually_atTop.2 ⟨1, fun r hr => hbound ℓ r hr⟩)
  -- `ℓ → ∞`
  have h1 : Tendsto (fun ℓ => Real.sqrt (2 * A.ε ℓ)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto (2 * 0)).comp (A.ε_lim.const_mul 2)
    rw [mul_zero, Real.sqrt_zero] at this
    exact this
  have h2 : Tendsto (fun ℓ => Real.sqrt (A.ε ℓ)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp A.ε_lim
    rw [Real.sqrt_zero] at this
    exact this
  have hq : Tendsto (fun ℓ => (2 + 2 * Real.sqrt (2 * A.ε ℓ) + A.ε ℓ) * E + (2 + 2 * A.M) * Real.sqrt (A.ε ℓ))
      atTop (𝓝 ((2 + 2 * 0 + 0) * E + (2 + 2 * A.M) * 0)) :=
    (((tendsto_const_nhds.add (h1.const_mul 2)).add A.ε_lim).mul_const E).add (h2.const_mul _)
  have e : (2 + 2 * 0 + 0) * E + (2 + 2 * A.M) * 0 = 2 * E := by ring
  rw [e] at hq
  exact ge_of_tendsto hq (Eventually.of_forall hbound')

/-- **Windowed block gap** (the named input): one physical rate `m > 0`; every slab family of bounded physical extent
has, from some level on, windowed block data at the lattice rate `m a_k`. -/
def WinBlockGap (T : Tuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ (s R : ℝ) (Vb : ℕ → ℕ) (O : SlabObs T s Vb), O.Extent R →
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → Nonempty (WinApprox T (m * T.a k) k (O.F k))

/-- **`MassGapLoc` from the windowed block gap** (volume first, then spacing). -/
theorem massGapLoc_of_winBlockGap {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (h : WinBlockGap T) :
    MassGapLoc T := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun s R Vb O hO τ hτ hk g hhk hg => ?_⟩
  obtain ⟨k₀, Hk⟩ := H s R Vb O hO
  have hlev : ∀ k, k₀ ≤ k → |hk k| ≤ 2 * Real.exp (-(m * (τ - T.a k))) := by
    intro k hkk
    have h1 := level_gap O (Hk k hkk).some (T.steps k τ) (hhk k)
    refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num))
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
  exact hlev (φ k) hk

/-! ### M1's split as the approximation input -/

/-- **Windowed block data with the approximation error from M1's split**: the approximants are bounded versions of
`E[F | 𝓗_ℓ]`, and M1's (B) and (A) terms are bounded uniformly in the volume by `b_B ℓ, b_A ℓ → 0`. -/
structure UVTVApprox (T : Tuning) (lam : ℝ) (k : ℕ) (F : ∀ j, GaugeConnection SU2 4 (T.side k j) → ℝ) where
  w : ℕ → ℕ
  g : ℕ → ∀ j, GaugeConnection SU2 4 (T.side k j) → ℝ
  M : ℝ
  meas : ∀ ℓ j, Measurable (g ℓ j)
  bdd : ∀ ℓ j U, |g ℓ j U| ≤ M
  slab : ∀ ℓ j, LinkDep (g ℓ j) (timeSlab 0 (w ℓ))
  /-- The σ-algebras of M1's split: `𝓗` the block state near `supp F`, `𝓕` the full block state. -/
  𝓕 : ∀ j, ℕ → MeasurableSpace (GaugeConnection SU2 4 (T.side k j))
  𝓗 : ∀ j, ℕ → MeasurableSpace (GaugeConnection SU2 4 (T.side k j))
  𝓕_le : ∀ j ℓ, 𝓕 j ℓ ≤ MeasurableSpace.pi
  𝓗_le : ∀ j ℓ, 𝓗 j ℓ ≤ MeasurableSpace.pi
  𝓗_𝓕 : ∀ j ℓ, 𝓗 j ℓ ≤ 𝓕 j ℓ
  θ𝓗_𝓕 : ∀ j ℓ, (𝓗 j ℓ).comap thetaConn ≤ 𝓕 j ℓ
  /-- `g ℓ j` is a version of the conditional expectation. -/
  version : ∀ ℓ j, g ℓ j =ᵐ[T.ym k j] (T.ym k j)[F j|𝓗 j ℓ]
  bA : ℕ → ℝ
  bB : ℕ → ℝ
  bA_lim : Tendsto bA atTop (𝓝 0)
  bB_lim : Tendsto bB atTop (𝓝 0)
  /-- M1's (B) term. -/
  hB : ∀ ℓ j, ∫ U, |M1.UVTV.ccov (T.ym k j) (𝓕 j ℓ) (F j ∘ thetaConn) (F j) U| ∂(T.ym k j) ≤ bB ℓ
  /-- M1's (A) term. -/
  hA : ∀ ℓ j, ∫ U, |(T.ym k j)[F j ∘ thetaConn|𝓕 j ℓ] U -
    (T.ym k j)[F j ∘ thetaConn|(𝓗 j ℓ).comap thetaConn] U| ∂(T.ym k j) ≤ bA ℓ
  C : ℕ → ℝ
  C_nonneg : ∀ ℓ, 0 ≤ C ℓ
  decay : ∀ ℓ j t, 2 * t + 2 * w ℓ + 2 ≤ T.side k j → |T.wcorr k j (g ℓ j) t| ≤ C ℓ * Real.exp (-(lam * t))

/-- M1's split supplies the approximation error: `ε_ℓ = b_B ℓ + 2 b_A ℓ`. -/
def UVTVApprox.toWinApprox {T : Tuning} {lam : ℝ} {k : ℕ} {s : ℝ} {Vb : ℕ → ℕ} (O : SlabObs T s Vb)
    (A : UVTVApprox T lam k (O.F k)) : WinApprox T lam k (O.F k) where
  w := A.w
  g := A.g
  M := A.M
  meas := A.meas
  bdd := A.bdd
  slab := A.slab
  ε := fun ℓ => A.bB ℓ + 2 * A.bA ℓ
  ε_lim := by simpa using A.bB_lim.add (A.bA_lim.const_mul 2)
  approx ℓ j := approx_le_of_UVTV (d := 4) (N := T.side k j) (G := SU2) continuous_subtype_val
    (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) (posWeight_wilson 2 (T.β k)) (A.𝓕 j) (A.𝓗 j) ℓ
    (A.𝓕_le j ℓ) (A.𝓗_le j ℓ) (A.𝓗_𝓕 j ℓ) (A.θ𝓗_𝓕 j ℓ) (O.meas k j) (O.bdd k j) (A.version ℓ j) (A.hB ℓ j)
    (A.hA ℓ j)
  C := A.C
  C_nonneg := A.C_nonneg
  decay := A.decay

/-- **The UV-TV block gap** (the named input in M1's terms): one physical rate `m > 0`; every slab family of bounded
physical extent has, from some level on, approximants that are versions of `E[F | 𝓗_ℓ]` with M1's (A)/(B) bounds
`→ 0` uniformly in the volume, and a block-level gap at the lattice rate `m a_k` uniform in the volume. -/
def UVTVBlockGap (T : Tuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ (s R : ℝ) (Vb : ℕ → ℕ) (O : SlabObs T s Vb), O.Extent R →
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → Nonempty (UVTVApprox T (m * T.a k) k (O.F k))

theorem winBlockGap_of_UVTVBlockGap {T : Tuning} (h : UVTVBlockGap T) : WinBlockGap T := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun s R Vb O hO => ?_⟩
  obtain ⟨k₀, Hk⟩ := H s R Vb O hO
  exact ⟨k₀, fun k hk => ⟨(Hk k hk).some.toWinApprox O⟩⟩

/-- **Headline: `MassGapLoc` from M1's (A)/(B) bounds and the block-level gap, with no OS reconstruction
hypothesis.** The torus reflection positivity (`rp_gaugeMeasure`) does the work that `OSData` and the infinite-volume
`RPMeasure` did in `M1.UVTV.RPMeasure.gap_of_measure`. -/
theorem massGapLoc_of_UVTVBlockGap {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (h : UVTVBlockGap T) :
    MassGapLoc T :=
  massGapLoc_of_winBlockGap ha (winBlockGap_of_UVTVBlockGap h)

end ProofPhase.OS
