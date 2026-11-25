/-
Closures round (2026-11-24): non-triviality split into a per-box half (by construction, from reflection positivity)
and a scale-uniform half, and the uniform half compared with O1. Released under Apache 2.0.

Paper: Part III, III.9 (claim III.9.5, the non-triviality half of O2); `docs/paper/OPEN-CLAIMS-CLOSURES.md`.
-/

import ProofPhase.Assembly
import ProofPhase.Bridge.Spectral

/-!
# Non-triviality: per box by construction, uniformly in the scale a second edge

`NonTrivial T` (`Assembly.lean`) asks for one slab observable whose reflected correlation at a fixed physical time `τ`
has every continuum limit point at least `c > 0` in absolute value. "Non-trivial" here means a non-vanishing
correlation, the project's definition; it is weaker than "not a Gaussian field".

**1. Per box, by construction (S).** At every level `k` and volume `j` the reflected correlation at even lattice time
is the reflection-positivity square of the centred translate:
`rpForm (F_m − c, F_m − c) = Z · wcorr(2m)` (`wcorr_even_eq_rpForm`, the Hankel identity `hankel_corr` at `j = k = m`).
So it is `≥ 0` (`wcorr_even_nonneg`). Strict positivity would need the reflection form to be non-degenerate on the
centred translates (the transfer matrix injective on them); that is not in the library and not claimed.

**2. The reduction (S).** `nonTrivial_of_uniformLower`: if, from some level on and from some volume on, the correlation
at physical time `τ` is at least one `c > 0` (`UniformLower`), then `NonTrivial` holds.

**3. The uniform half against O1 (S, abstract spectral model of `Bridge/Spectral.lean`).** For a correlation
`t ↦ ∫ e^{−tE} dν(E)` with `ν ≥ 0` on `[0, ∞)`:
* a spectral weight `δ` below a mass `M` gives the lower bound `δ e^{−Mt}` (`lower_of_spectral_weight`, from
  `corr_ge`); this is the shape of the uniform half: the overlap with the low states bounded below and the mass bounded
  above, uniformly in the scale;
* O1's conclusion is the opposite edge, no weight below `m` (`spectral_gap_iff`); it does not give any lower bound:
  the zero measure has a gap at every `m` and a vanishing correlation (`gap_not_lower`);
* the two edges are compatible exactly as a window: a state at `E` with `m ≤ E < M` has both (`gap_and_lower_compatible`).

So the uniform half of non-triviality is **separate from O1**: not implied by it, not implying it, compatible with it.
It is the lower edge of the same spectral window whose upper edge is O1, and it is uniformity in the scale, the same
quantifier shape. Whether the paper's one assumption (Part X 4.4, "the one box is a running system") is read to include
it is a decision about the wording of the assumption, recorded in `docs/paper/OPEN-CLAIMS-CLOSURES.md`.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete Positivity OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift

noncomputable section

namespace ProofPhase.Closures.NonTrivialSplit

/-! ## 1. Per box, by construction -/

section PerBox

variable (T : Tuning) (k j : ℕ)

/-- The centred translate `F ∘ S_m − μ(F)` at level `k`, volume `j`. -/
def centred (F : GaugeConnection SU2 4 (T.side k j) → ℝ) (m : ℕ) : GaugeConnection SU2 4 (T.side k j) → ℝ :=
  fun U => F (tShift (m : ZMod (T.side k j)) U) -
    ∫ V, F V ∂(gaugeMeasure (d := 4) (N := T.side k j) (G := SU2) 2 (wilsonWeight (T.β k)))

/-- **The correlation at even time is a reflection-positivity square** (S), by construction: the Hankel identity at
`j = k = m`. -/
theorem wcorr_even_eq_rpForm {F : GaugeConnection SU2 4 (T.side k j) → ℝ} (hF : BM F) (m : ℕ) :
    OneScale.TorusRP.rpForm 2 (wilsonWeight (T.β k)) (centred T k j F m) (centred T k j F m) =
      partZ (d := 4) (N := T.side k j) (G := SU2) 2 (wilsonWeight (T.β k)) * T.wcorr k j F (2 * m) := by
  rw [two_mul]
  exact hankel_corr (d := 4) (N := T.side k j) continuous_subtype_val
    (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) (posWeight_wilson 2 (T.β k)) hF m m

/-- **Per box the correlation at even time is non-negative** (S): for a bounded measurable observable whose translates
up to `m` depend on the closed positive half only. -/
theorem wcorr_even_nonneg {F : GaugeConnection SU2 4 (T.side k j) → ℝ} (hF : BM F) {m : ℕ}
    (hpos : LinkDep (fun U => F (tShift (m : ZMod (T.side k j)) U)) (posHalfLinks 4 (T.side k j))) :
    0 ≤ T.wcorr k j F (2 * m) := by
  have hZ := partZ_pos (d := 4) (N := T.side k j) (G := SU2) continuous_subtype_val
    (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) (posWeight_wilson 2 (T.β k))
  have hG : LinkDep (centred T k j F m) (posHalfLinks 4 (T.side k j)) := fun U V h => by
    have e : F (tShift (m : ZMod (T.side k j)) U) = F (tShift (m : ZMod (T.side k j)) V) := hpos U V h
    simp only [centred]
    rw [e]
  have mG : Measurable (centred T k j F m) := (hF.meas.comp (measurable_tShift (m : ZMod (T.side k j)))).sub_const _
  obtain ⟨M, hM⟩ := hF.bdd
  have bG : ∃ C, ∀ U, |centred T k j F m U| ≤ C :=
    ⟨M + |∫ V, F V ∂(gaugeMeasure (d := 4) (N := T.side k j) (G := SU2) 2 (wilsonWeight (T.β k)))|,
      fun U => (abs_sub _ _).trans (add_le_add (hM _) le_rfl)⟩
  have h0 : 0 ≤ OneScale.TorusRP.rpForm 2 (wilsonWeight (T.β k)) (centred T k j F m) (centred T k j F m) :=
    rp_plaquette_weight (T.even_side k j) continuous_subtype_val
    (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
    (plaqWeight_of_posWeight (posWeight_wilson 2 (T.β k))) hG mG bG
  rw [wcorr_even_eq_rpForm T k j hF m] at h0
  exact nonneg_of_mul_nonneg_right h0 hZ

end PerBox

/-! ## 2. The reduction -/

/-- A lower bound that holds eventually along a sequence holds at each of its limit points. -/
theorem ge_of_limitPoint {u : ℕ → ℝ} {h B : ℝ} (hu : ∀ᶠ k in atTop, B ≤ u k) (hh : IsLimitPoint u h) : B ≤ h := by
  obtain ⟨φ, hφ, ht⟩ := hh
  exact ge_of_tendsto ht (hφ.tendsto_atTop.eventually hu)

/-- **The scale-uniform half**: one slab observable, one physical time `τ > 0` and one `c > 0` with the correlation at
least `c`, from some level on and, at each such level, from some volume on. -/
def UniformLower (T : Tuning) : Prop :=
  ∃ (s : ℝ) (V : ℕ → ℕ) (O : SlabObs T s V) (τ c : ℝ), 0 < τ ∧ 0 < c ∧
    ∀ᶠ k in atTop, ∀ᶠ j in atTop, c ≤ T.wcorr k j (O.F k j) (T.steps k τ)

/-- **The uniform half gives non-triviality** (S). -/
theorem nonTrivial_of_uniformLower {T : Tuning} (h : UniformLower T) : NonTrivial T := by
  obtain ⟨s, V, O, τ, c, hτ, hc, hev⟩ := h
  refine ⟨s, V, O, τ, c, hτ, hc, fun hk g hhk hg => ?_⟩
  have hk' : ∀ᶠ k in atTop, c ≤ hk k := hev.mono fun k hk2 => ge_of_limitPoint hk2 (hhk k)
  exact (ge_of_limitPoint hk' hg).trans (le_abs_self g)

/-! ## 3. The uniform half against O1, in the spectral model -/

/-- **Spectral weight below a mass gives a lower bound** (S): weight `δ` below `M` gives `δ e^{−Mt} ≤ corr ν t`. -/
theorem lower_of_spectral_weight {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ∀ᵐ E ∂ν, 0 ≤ E) {M δ t : ℝ}
    (ht : 0 ≤ t) (hδ : δ ≤ ν.real (Set.Iio M)) :
    δ * Real.exp (-(M * t)) ≤ ProofPhase.Bridge.corr ν t :=
  (mul_le_mul_of_nonneg_right hδ (Real.exp_pos _).le).trans (ProofPhase.Bridge.corr_ge hν M ht)

/-- **A gap gives no lower bound** (S): the zero measure has no weight below any `m` (a gap at every rate) and a
vanishing correlation, below every `δ e^{−Mt}` with `δ > 0`. -/
theorem gap_not_lower (m M δ t : ℝ) (hδ : 0 < δ) :
    (0 : Measure ℝ) (Set.Iio m) = 0 ∧ ¬ δ * Real.exp (-(M * t)) ≤ ProofPhase.Bridge.corr (0 : Measure ℝ) t := by
  refine ⟨by simp, ?_⟩
  simp only [ProofPhase.Bridge.corr, integral_zero_measure, not_le]
  positivity

/-- **The two edges are compatible as a window** (S): a state at `E`, `m ≤ E < M`, has no weight below `m` and full
weight below `M`. -/
theorem gap_and_lower_compatible {m M E : ℝ} (hmE : m ≤ E) (hEM : E < M) :
    (Measure.dirac E) (Set.Iio m) = 0 ∧ (Measure.dirac E).real (Set.Iio M) = 1 := by
  constructor
  · rw [Measure.dirac_apply' _ measurableSet_Iio]
    simp [not_lt.2 hmE]
  · simp [Measure.real, Measure.dirac_apply' _ measurableSet_Iio, hEM]

/-! ## 4. The running clause of the line of constant physics, by construction

The running clause of `OnLCP` (`β_k / log ℓ_k → 11/(6π²)`) is a statement about the tuning, the data, not about the
measure. On the one-loop line, the natural tuning of an asymptotically free theory, it holds by construction. What the
line of constant physics adds beyond it is the scheme clause (a physical quantity, the act rate of the unit box, stays
fixed along the tuning), a statement about the measure, uniform in the scale. -/

/-- **The tuning on the one-loop line**: `β_k = (11/(6π²)) log ℓ_k`. -/
def oneLoopTuning (L₁ : ℝ) (hL : 0 < L₁) (ℓ : ℕ → ℕ) (hℓ : ∀ k, 0 < ℓ k) : Tuning :=
  ⟨L₁, hL, ℓ, hℓ, fun k => oneLoopSlope * Real.log (ℓ k)⟩

/-- **The running clause holds on the one-loop line** (S), by construction, once the resolution grows. -/
theorem running_oneLoop (L₁ : ℝ) (hL : 0 < L₁) (ℓ : ℕ → ℕ) (hℓ : ∀ k, 0 < ℓ k) (hres : Tendsto ℓ atTop atTop) :
    Tendsto (fun k => (oneLoopTuning L₁ hL ℓ hℓ).β k / Real.log ((oneLoopTuning L₁ hL ℓ hℓ).ℓ k)) atTop
      (𝓝 oneLoopSlope) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hres.eventually_ge_atTop 2] with k hk
  have h1 : (1 : ℝ) < (ℓ k : ℝ) := by exact_mod_cast hk
  have hlog : Real.log (ℓ k) ≠ 0 := (Real.log_pos h1).ne'
  show oneLoopSlope = oneLoopSlope * Real.log (ℓ k) / Real.log (ℓ k)
  rw [mul_div_assoc, div_self hlog, mul_one]

end ProofPhase.Closures.NonTrivialSplit
