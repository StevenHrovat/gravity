/-
Proof phase, workstream 4 (existence and identification): the statement bridge to the OpenAI Wilson construction
(2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/ws4-existence/NOTE.md`. Nothing here imports or copies the OpenAI
code (Lean 4.32, about 988k lines); their public definitions are restated in our vocabulary from the mathematics, and
the fidelity of each restatement is checked by reading (file:line in the note), not by Lean.
-/

import ProofPhase.Assembly

/-!
# The statement bridge: their lattice family on our objects, and the gap in their order of limits

**1. The lattice law.** The OpenAI public statement (`PublicWilson.lean`, `wilsonLaw`) uses the plaquette energy
`E(U) = Σ_p (1 − Re tr U_p / n)` (one plaquette per site and pair of axes `i < j`, `n` the matrix size) and the law
`Z⁻¹ e^{−β' E(U)}` times product probability Haar measure. `plaqLaw n β'` restates it on our types;
`plaqLaw_eq_wilsonMeasure` proves it **equals our `wilsonMeasure G n (β'/n)`** for every compact group with a matrix
representation (the constant `e^{−β'·#plaquettes}` cancels in the normalisation). For SU(2): `β_ours = β'/2`.

**2. Their family as a tuning with a volume-dependent coupling.** Their bare coupling `β_{N,p}` may depend on the
volume index `p` (it is shot per cutoff and volume so that the flow lands on a fixed reference value), while our
`Tuning` has one `β_k` per level. `VTuning` allows `β_{k,j}`; `Tuning.toV` embeds ours (`toV_wcorr` is `rfl`).
`WilsonData` holds the lattice data of their family (period `L_p` with `4 ∣ L_p`, strictly increasing; denominator
`D_N`; `β_{N,p}`), and `WilsonData.toV` places it on our tori: unit `L₁ = 1` (their unit), resolution `ℓ_N = D_N`,
torus index `j = L_p/2 − 1`. Proved: `side_vol` (their lattice side `L_p·D_N` is our side at `j = vol p`),
`βv_vol` (the coupling there is `β_{N,p}/2`), `ym_vol` (our SU(2) Wilson measure there is their law).

**3. The order of limits.** Our `MassGap` takes the volume first, then the spacing. Their construction takes the
mesh limit at fixed physical volume first, then the volume along a subsequence. `MassGapMF` is the gap in their order
(every volume subsequence, every limit point). `TorusDecay` is `SlabDecay` with a constant independent of the level
(one physical rate, one constant, every level from some on, **every torus**: the "uniform at every finite depth"
statement of the owner's DMP reading). Proved: `massGapMF_of_torusDecay` (their order) and
`bothOrders_of_torusDecay` (`TorusDecay` gives `MassGap` and `MassGapMF`), using Theorem C on the torus
(`corr_le_of_decay`) to bring the constant down to `2` as the volume grows.

**Strength.** `TorusDecay` is `SlabDecay` with a level-uniform constant, so it is stronger than `SlabDecay` (route A's
crossover field) and slightly stronger than the Clay gap (it is a lattice-uniform bound, like `LatticeGap`). On small
tori it is vacuous beyond the trivial bound: the decay is asked only for `2n + 2·thick + 2 ≤ side`, so a deconfined
small box costs only a larger constant.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Existence

/-! ## 1. The lattice law in their convention equals our Wilson measure -/

section Law

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [HasHaarProbability G] {n : ℕ} [HasGaugeTrace G n]

/-- The plaquette energy in the convention of the OpenAI public statement: `Σ_p (1 − Re tr U_p / n)`. -/
def plaqEnergy (n : ℕ) [HasGaugeTrace G n] (U : GaugeConnection G d N) : ℝ :=
  ∑ p : LatticePlaquette d N, (1 - xp n p U / n)

/-- Their normalised Wilson law, restated on our types: `Z⁻¹ e^{−β' E(U)}` times product Haar measure. -/
def plaqLaw (n : ℕ) [HasGaugeTrace G n] (β' : ℝ) : Measure (GaugeConnection G d N) :=
  (productHaar G d N).withDensity fun U =>
    ENNReal.ofReal (Real.exp (-β' * plaqEnergy n U) /
      ∫ V, Real.exp (-β' * plaqEnergy n V) ∂(productHaar G d N))

theorem exp_plaqEnergy (β' : ℝ) (U : GaugeConnection G d N) :
    Real.exp (-β' * plaqEnergy n U) =
      Real.exp (-β' * (Fintype.card (LatticePlaquette d N) : ℝ)) * plaqProd n (wilsonWeight (β' / n)) univ U := by
  unfold plaqEnergy plaqProd wilsonWeight
  rw [← Real.exp_sum, ← Real.exp_add]
  congr 1
  have e2 : ∑ p : LatticePlaquette d N, β' / n * xp n p U = β' * ∑ p : LatticePlaquette d N, xp n p U / n := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
  rw [e2, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

/-- **Their law is our Wilson measure**: `plaqLaw n β' = wilsonMeasure G n (β'/n)`. -/
theorem plaqLaw_eq_wilsonMeasure (β' : ℝ) :
    plaqLaw (d := d) (N := N) (G := G) n β' = wilsonMeasure G n (β' / n) d N := by
  show _ = weightMeasure (haarG G) (plaqProd n (wilsonWeight (β' / n)) univ)
  unfold plaqLaw weightMeasure
  congr 1
  funext U
  congr 1
  simp_rw [exp_plaqEnergy (n := n) β']
  rw [integral_const_mul, mul_div_mul_left _ _ (Real.exp_pos _).ne']
  rfl

end Law

/-- For SU(2) (`n = 2`): our Wilson measure at `β` is their law at `β' = 2β`. -/
theorem wilsonMeasure_SU2_eq_plaqLaw (β : ℝ) (N : ℕ) [NeZero N] :
    wilsonMeasure SU2 2 β 4 N = plaqLaw (d := 4) (N := N) (G := SU2) 2 (2 * β) := by
  rw [plaqLaw_eq_wilsonMeasure]; congr 1; push_cast; ring

/-! ## 2. Tunings with a volume-dependent coupling -/

/-- **A tuning with a volume-dependent bare coupling** `β_{k,j}` (level `k`, torus `j`): the lattice geometry of `T`
(unit `L₁`, resolution `ℓ_k`, tori of side `2(j+1)ℓ_k`) with `T.β` ignored. -/
structure VTuning where
  T : Tuning
  βv : ℕ → ℕ → ℝ

namespace VTuning

variable (V : VTuning)

/-- The SU(2) Wilson measure at level `k` on torus `j`. -/
abbrev ym (k j : ℕ) : Measure (GaugeConnection SU2 4 (V.T.side k j)) :=
  wilsonMeasure SU2 2 (V.βv k j) 4 (V.T.side k j)

/-- The reflected connected correlation `Cov(F ∘ S_n, F ∘ Θ)` at level `k`, torus `j`. -/
def wcorr (k j : ℕ) (F : GaugeConnection SU2 4 (V.T.side k j) → ℝ) (n : ℕ) : ℝ :=
  corr (d := 4) (N := V.T.side k j) (G := SU2) 2 (wilsonWeight (V.βv k j)) F n

end VTuning

/-- Our tunings are the volume-independent case. -/
def _root_.ProofPhase.Tuning.toV (T : Tuning) : VTuning := ⟨T, fun k _ => T.β k⟩

theorem toV_wcorr (T : Tuning) (k j : ℕ) (F : GaugeConnection SU2 4 (T.side k j) → ℝ) (n : ℕ) :
    T.toV.wcorr k j F n = T.wcorr k j F n := rfl

/-- **Lattice data of a Wilson family in the OpenAI statement**: volume index `p` with period (physical side, in their
unit) `L_p`, divisible by 4 and strictly increasing; cutoff index `N` with denominator `D_N` (mesh `1/D_N`); bare
coupling `β_{N,p}` in their convention (`e^{−β' Σ(1 − Re tr/n)}`). -/
structure WilsonData where
  period : ℕ → ℕ
  period_pos : ∀ p, 0 < period p
  period_four : ∀ p, 4 ∣ period p
  period_strict : StrictMono period
  den : ℕ → ℕ
  den_pos : ∀ N, 0 < den N
  beta : ℕ → ℕ → ℝ

namespace WilsonData

variable (D : WilsonData)

/-- Our torus index of their volume `p`: physical side `2(j+1) = L_p`. -/
def vol (p : ℕ) : ℕ := D.period p / 2 - 1

theorem two_vol (p : ℕ) : 2 * (D.vol p + 1) = D.period p := by
  obtain ⟨c, hc⟩ := D.period_four p
  have hp := D.period_pos p
  unfold vol; omega

/-- The bare coupling on our torus `j`: `β_{N,p}/2` when `j = vol p` (junk elsewhere). -/
def βof (k j : ℕ) : ℝ := if h : ∃ p, D.vol p = j then D.beta k h.choose / 2 else 0

/-- Their family on our tori: unit `L₁ = 1`, resolution `ℓ_N = D_N`, coupling `βof`. -/
def toV : VTuning := ⟨⟨1, one_pos, D.den, D.den_pos, fun _ => 0⟩, D.βof⟩

theorem vol_strict : StrictMono D.vol := by
  intro p q hpq
  have h1 := D.two_vol p
  have h2 := D.two_vol q
  have h3 := D.period_strict hpq
  omega

/-- **Their lattice at `(N, p)` is our torus at level `N`, index `vol p`**: side `L_p · D_N`. -/
theorem side_vol (k p : ℕ) : D.toV.T.side k (D.vol p) = D.period p * D.den k := by
  show 2 * (D.vol p + 1) * D.den k = _
  rw [D.two_vol p]

theorem βv_vol (k p : ℕ) : D.toV.βv k (D.vol p) = D.beta k p / 2 := by
  show D.βof k (D.vol p) = _
  have h : ∃ p', D.vol p' = D.vol p := ⟨p, rfl⟩
  unfold βof
  rw [dite_cond_eq_true (eq_true h), D.vol_strict.injective h.choose_spec]

/-- **The measure there is their law** (SU(2), restated): our Wilson measure at `β_{N,p}/2` on that torus equals
`Z⁻¹ e^{−β_{N,p} Σ(1 − Re tr/2)}` times product Haar measure. -/
theorem ym_vol (k p : ℕ) :
    D.toV.ym k (D.vol p) = plaqLaw (d := 4) (N := D.toV.T.side k (D.vol p)) (G := SU2) 2 (D.beta k p) := by
  show wilsonMeasure SU2 2 (D.toV.βv k (D.vol p)) 4 _ = _
  rw [D.βv_vol, wilsonMeasure_SU2_eq_plaqLaw]; congr 1; ring

end WilsonData

/-! ## 3. The gap in both orders of limits -/

/-- The volume-first gap for a `VTuning` (our `MassGap`, with `β_{k,j}`). -/
def MassGapVF (V : VTuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ (s : ℝ) (Vb : ℕ → ℕ) (O : SlabObs V.T s Vb) (τ : ℝ), 0 ≤ τ → ∀ (h : ℕ → ℝ) (g : ℝ),
    (∀ k, IsLimitPoint (fun j => V.wcorr k j (O.F k j) (V.T.steps k τ)) (h k)) → IsLimitPoint h g →
      |g| ≤ 2 * Real.exp (-(m * τ))

theorem massGapVF_toV_iff (T : Tuning) : MassGapVF T.toV ↔ MassGap T := Iff.rfl

/-- **The gap in the OpenAI order of limits** (mesh first at fixed physical volume, then the volume along any
strictly increasing sequence of tori): one rate `m > 0`; for every slab observable family, every physical time
`τ ≥ 0`, every volume sequence `vol`, every choice of continuum limit points `h p` (level `k → ∞` on torus `vol p`)
and every limit point `g` of `h`: `|g| ≤ 2 e^{-mτ}`. -/
def MassGapMF (V : VTuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ (s : ℝ) (Vb : ℕ → ℕ) (O : SlabObs V.T s Vb) (τ : ℝ), 0 ≤ τ → ∀ (vol : ℕ → ℕ), StrictMono vol →
    ∀ (h : ℕ → ℝ) (g : ℝ),
    (∀ p, IsLimitPoint (fun k => V.wcorr k (vol p) (O.F k (vol p)) (V.T.steps k τ)) (h p)) → IsLimitPoint h g →
      |g| ≤ 2 * Real.exp (-(m * τ))

/-- **Torus decay, uniform in depth and volume**: one physical rate `m > 0`; for every slab thickness `s` and support
bound `Vb` one constant `C` and one level `k₀`; on every torus at every level `k ≥ k₀`, the reflected slab correlation
decays as `C e^{-m n a_k}` while it fits (`2n + 2·thick + 2 ≤ side`). `SlabDecay` with a level-independent constant. -/
def TorusDecay (V : VTuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ (s : ℝ) (Vb : ℕ → ℕ), ∃ k₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k, k₀ ≤ k →
    ∀ (j : ℕ) (O : SlabObs V.T s Vb) (n : ℕ), 2 * n + 2 * V.T.thick k s + 2 ≤ V.T.side k j →
      |V.wcorr k j (O.F k j) n| ≤ C * Real.exp (-(m * (n * V.T.a k)))

theorem slabDecay_of_torusDecay {T : Tuning} (h : TorusDecay T.toV) : SlabDecay T := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun s Vb => ?_⟩
  obtain ⟨k₀, C, hC, Hk⟩ := H s Vb
  exact ⟨k₀, fun k hk => ⟨C, hC, fun j O n hn => Hk k hk j O n hn⟩⟩

theorem IsLimitPoint.abs_le_of_tendsto {u B : ℕ → ℝ} {h b : ℝ} (hu : ∀ᶠ k in atTop, |u k| ≤ B k)
    (hB : Tendsto B atTop (𝓝 b)) (hh : IsLimitPoint u h) : |h| ≤ b := by
  obtain ⟨φ, hφ, ht⟩ := hh
  exact le_of_tendsto_of_tendsto ht.abs (hB.comp hφ.tendsto_atTop) (hφ.tendsto_atTop.eventually hu)

/-- The torus is long enough for Theorem C with `2^{r+1}` steps of physical time `τ` once its physical side
`2(j+1)L₁` exceeds `2^{r+1}τ + 2|s| + 4L₁`. -/
theorem side_ge (T : Tuning) (k j : ℕ) {τ s : ℝ} (hτ : 0 ≤ τ) (r : ℕ)
    (hj : 2 ^ (r + 1) * τ + 2 * |s| + 4 * T.L₁ ≤ 2 * ((j : ℝ) + 1) * T.L₁) :
    2 ^ (r + 1) * T.steps k τ + 2 * T.thick k s + 2 ≤ T.side k j := by
  have hL := T.L₁_pos
  have hℓ : (1 : ℝ) ≤ T.ℓ k := by exact_mod_cast T.ℓ_pos k
  have ha := T.a_pos k
  set q : ℝ := T.ℓ k / T.L₁ with hq_def
  have hq : 0 < q := div_pos (by linarith) hL
  have hLq : T.L₁ * q = T.ℓ k := by rw [hq_def]; field_simp
  have e : ∀ x : ℝ, x / T.a k = x * q := fun x => by
    rw [hq_def]; unfold Tuning.a; field_simp
  have f1 : (T.steps k τ : ℝ) ≤ τ * q := by
    rw [← e]; exact Nat.floor_le (div_nonneg hτ ha.le)
  have f2 : (T.thick k s : ℝ) ≤ |s| * q + 1 := by
    rw [← e]
    have h2a : T.thick k s ≤ ⌈|s| / T.a k⌉₊ :=
      Nat.ceil_mono (div_le_div_of_nonneg_right (le_abs_self s) ha.le)
    have h2b : (⌈|s| / T.a k⌉₊ : ℝ) < |s| / T.a k + 1 := Nat.ceil_lt_add_one (div_nonneg (abs_nonneg s) ha.le)
    exact (Nat.cast_le.2 h2a).trans h2b.le
  have f3 := mul_le_mul_of_nonneg_left hj hq.le
  have f4 : (2 : ℝ) ^ (r + 1) * T.steps k τ ≤ 2 ^ (r + 1) * (τ * q) :=
    mul_le_mul_of_nonneg_left f1 (by positivity)
  have hside : (T.side k j : ℝ) = 2 * ((j : ℝ) + 1) * (T.L₁ * q) := by
    rw [hLq]; unfold Tuning.side; push_cast; ring
  have : (2 : ℝ) ^ (r + 1) * T.steps k τ + 2 * T.thick k s + 2 ≤ T.side k j := by
    rw [hside]; nlinarith
  exact_mod_cast this

/-- **The gap in their order from torus decay.** -/
theorem massGapMF_of_torusDecay {V : VTuning} (ha : Tendsto V.T.a atTop (𝓝 0)) (h : TorusDecay V) :
    MassGapMF V := by
  obtain ⟨m, hm, hdec⟩ := h
  refine ⟨m, hm, fun s Vb O τ hτ vol hvol hp g hhp hg => ?_⟩
  obtain ⟨k₀, C, hC, hCk⟩ := hdec s Vb
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
    refine _root_.ProofPhase.Existence.IsLimitPoint.abs_le_of_tendsto ?_ hB (hhp p)
    filter_upwards [eventually_ge_atTop k₀] with k hk
    have hN := side_ge V.T k (vol p) hτ r hp'
    have hc := corr_le_of_decay (d := 4) (N := V.T.side k (vol p)) (G := SU2) continuous_subtype_val
      (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) (V.T.even_side k (vol p))
      (posWeight_wilson 2 (V.βv k (vol p))) (O.meas k (vol p)) (O.bdd k (vol p)) (O.slab k (vol p)) hC
      (lam := m * V.T.a k)
      (fun t' ht' => by
        have := hCk k hk (vol p) O t' ht'
        rw [show -(m * V.T.a k * t') = -(m * (t' * V.T.a k)) by ring]
        exact this) hr hN
    refine hc.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity))
    nlinarith [mul_le_mul_of_nonneg_left (V.T.steps_mul_ge k hτ) hm.le]
  have hq : Tendsto (fun r : ℕ => (2 + (1 / 2 : ℝ) ^ r * C) * E) atTop (𝓝 ((2 + 0 * C) * E)) :=
    (tendsto_const_nhds.add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const C)).mul_const E
  rw [zero_mul, add_zero] at hq
  exact ge_of_tendsto hq (eventually_atTop.2 ⟨1, fun r hr => hr_bound r hr⟩)

/-- **Both orders of limits from one uniform-in-depth statement**: torus decay gives the mass gap volume first
(`MassGap`, through `SlabDecay` and the assembly's route A) and mesh first (`MassGapMF`, the OpenAI order). -/
theorem bothOrders_of_torusDecay {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (h : TorusDecay T.toV) :
    MassGap T ∧ MassGapMF T.toV :=
  ⟨massGap_of_latticeGap ha (latticeGap_of_slabDecay (slabDecay_of_torusDecay h)), massGapMF_of_torusDecay ha h⟩

/-- Their family (`WilsonData.toV`, unit 1, mesh `1/D_N`) has `a_k → 0` once `D_N → ∞` (strictly increasing in
their statement). -/
theorem WilsonData.tendsto_a (D : WilsonData) (hD : Tendsto D.den atTop atTop) :
    Tendsto D.toV.T.a atTop (𝓝 0) := by
  show Tendsto (fun k => (1 : ℝ) / (D.den k : ℝ)) atTop (𝓝 0)
  exact (tendsto_natCast_atTop_atTop.comp hD).const_div_atTop 1

end ProofPhase.Existence
