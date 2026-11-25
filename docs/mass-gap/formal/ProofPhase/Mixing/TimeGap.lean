/-
P vs NP dictionary, Lean part 2: the spectral gap in algorithmic time (2026-11-23). Released under Apache 2.0.

Paper: `docs/pnp/DICTIONARY.md`, section 3.
-/

import ProofPhase.Bridge.Spectral

/-!
# The spectral gap in time: the mass-gap statement for a Markov chain

**Setting.** `P` is a reversible Markov operator on `L²(μ)` that is positive (`0 ≤ P ≤ 1`; for example the
random-scan heat-bath operator, an average of orthogonal projections, or any lazy chain `(1 + P')/2`). For a function
`f` of mean zero, the spectral theorem gives a finite positive measure `ρ` on `[0, 1]` with
`⟨f, P^k f⟩ = ∫ λ^k dρ(λ)`: the spectral measure of `f`. This step is **assumed** (classical; Mathlib has no spectral
measure for self-adjoint operators): `ρ` is the data, with the hypotheses `0 ≤ λ ≤ 1` `ρ`-almost everywhere.
`acorr ρ k = ∫ λ^k dρ` is then the time correlation of `f` after `k` steps.

**Main results.**
* `time_gap_iff`: **exponential decay of time correlations at rate `m` iff no spectral mass above `e^{-m}`**:
  `(∃ K, ∀ k, acorr ρ k ≤ K e^{-m k}) ↔ ρ (Ioi e^{-m}) = 0`. In words: the chain forgets `f` at rate `m` exactly when
  the spectral gap of `P` on `f` (the distance from `1` to the top of the support of `ρ`) is at least `1 - e^{-m}`.
* `gap_of_geometric`, `geometric_of_gap`: the same with `θ = e^{-m}`: correlations `≤ K θ^k` iff `ρ (Ioi θ) = 0`.

**How.** The substitution `E = -log λ` turns `λ^k` into `e^{-k E}` and the measure `ρ` (its part on `λ > 0`) into a
positive measure `rateMeasure ρ` on `[0, ∞)`; the atom at `λ = 0` only touches `k = 0`. Then the bridge's
`ProofPhase.Bridge.spectral_gap_iff_nat` (decay rate = bottom of a positive spectral measure) is applied as it stands.
So this is the **same theorem** as the mass gap's "decay at rate `m` iff no spectral mass below `m`", read in
algorithmic time instead of Euclidean time: `E` is the relaxation rate of a mode, `m` the gap.

**Continuous time** needs no new statement: for a generator `L ≥ 0` (continuous-time Glauber dynamics) with spectral
measure `ν` of `f` on `[0, ∞)`, `⟨f, e^{-tL} f⟩ = corr ν t` and the bridge's `spectral_gap_iff` is the statement.

**New here:** `rateMeasure`, the change of variables `corr_rateMeasure`, the mass identity `rateMeasure_Iio`, and the
three theorems. **From the bridge:** `corr`, `spectral_gap_iff_nat`.
-/

open MeasureTheory Set ProofPhase.Bridge

noncomputable section

namespace ProofPhase.Mixing

/-- The time correlation `∫ λ^k dρ(λ)` (`= ⟨f, P^k f⟩` when `ρ` is the spectral measure of `f`). -/
def acorr (ρ : Measure ℝ) (k : ℕ) : ℝ := ∫ l, l ^ k ∂ρ

/-- The relaxation-rate measure: the part of `ρ` on `λ > 0`, pushed forward by `E = -log λ`. -/
def rateMeasure (ρ : Measure ℝ) : Measure ℝ := (ρ.restrict (Ioi 0)).map (fun l => -Real.log l)

theorem measurable_negLog : Measurable fun l : ℝ => -Real.log l := Real.measurable_log.neg

variable {ρ : Measure ℝ}

theorem rateMeasure_nonneg (h1 : ∀ᵐ l ∂ρ, l ≤ 1) : ∀ᵐ E ∂(rateMeasure ρ), 0 ≤ E := by
  rw [rateMeasure, ae_map_iff measurable_negLog.aemeasurable (measurableSet_Ici : MeasurableSet (Ici (0 : ℝ)))]
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [h1] with l hl hpos
  exact neg_nonneg.mpr (Real.log_nonpos (le_of_lt hpos) hl)

/-- **The mass identity.** No rate below `m` is no spectral value above `e^{-m}`. -/
theorem rateMeasure_Iio (m : ℝ) : rateMeasure ρ (Iio m) = ρ (Ioi (Real.exp (-m))) := by
  rw [rateMeasure, Measure.map_apply measurable_negLog measurableSet_Iio,
    Measure.restrict_apply (measurable_negLog measurableSet_Iio)]
  congr 1
  ext l
  simp only [mem_inter_iff, mem_preimage, mem_Iio, mem_Ioi]
  constructor
  · rintro ⟨h, hl⟩
    have : -m < Real.log l := by linarith
    exact (Real.lt_log_iff_exp_lt hl).mp this
  · intro h
    have hl : 0 < l := (Real.exp_pos _).trans h
    have := (Real.lt_log_iff_exp_lt hl).mpr h
    exact ⟨by linarith, hl⟩

/-- **The change of variables.** For `k ≥ 1`, `corr (rateMeasure ρ) k = ∫ λ^k dρ`. -/
theorem corr_rateMeasure (h0 : ∀ᵐ l ∂ρ, 0 ≤ l) {k : ℕ} (hk : k ≠ 0) :
    corr (rateMeasure ρ) k = acorr ρ k := by
  rw [corr, rateMeasure, integral_map measurable_negLog.aemeasurable (by fun_prop)]
  have h1 : ∫ l, Real.exp (-(k * -Real.log l)) ∂(ρ.restrict (Ioi 0)) = ∫ l in Ioi 0, l ^ k ∂ρ := by
    refine setIntegral_congr_fun measurableSet_Ioi fun l hl => ?_
    rw [mul_neg, neg_neg, Real.exp_nat_mul, Real.exp_log hl]
  rw [h1, acorr]
  refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
  filter_upwards [h0] with l hl hnot
  have : l = 0 := le_antisymm (not_lt.mp hnot) hl
  rw [this, zero_pow hk]

theorem corr_zero (ν : Measure ℝ) : corr ν 0 = ν.real univ := by
  simp [corr]

theorem acorr_zero (ρ : Measure ℝ) : acorr ρ 0 = ρ.real univ := by
  simp [acorr]

variable [IsFiniteMeasure ρ]

instance : IsFiniteMeasure (rateMeasure ρ) := by
  rw [rateMeasure]; infer_instance

/-- **The spectral gap in time.** For a positive spectral measure on `[0, 1]`: the time correlations decay at rate
`m` (`≤ K e^{-m k}` for all `k`) iff there is no spectral mass above `e^{-m}`. Through the bridge's
`spectral_gap_iff_nat`. -/
theorem time_gap_iff (h0 : ∀ᵐ l ∂ρ, 0 ≤ l) (h1 : ∀ᵐ l ∂ρ, l ≤ 1) (m : ℝ) :
    (∃ K : ℝ, ∀ k : ℕ, acorr ρ k ≤ K * Real.exp (-(m * k))) ↔ ρ (Ioi (Real.exp (-m))) = 0 := by
  have hν := rateMeasure_nonneg h1
  rw [← rateMeasure_Iio, ← spectral_gap_iff_nat hν m]
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨max K ((rateMeasure ρ).real univ), fun k => ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [corr_zero]
    · rw [corr_rateMeasure h0 hk.ne']
      exact (hK k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · rintro ⟨K, hK⟩
    refine ⟨max K (ρ.real univ), fun k => ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [acorr_zero]
    · rw [← corr_rateMeasure h0 hk.ne']
      exact (hK k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

theorem exp_neg_neg_log {θ : ℝ} (hθ : 0 < θ) (k : ℕ) : Real.exp (-(-Real.log θ * k)) = θ ^ k := by
  rw [neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hθ]

/-- **Geometric decay gives the gap.** If `∫ λ^k dρ ≤ K θ^k` for all `k`, with `θ > 0`, there is no spectral mass
above `θ`: the spectral gap is at least `1 - θ`. -/
theorem gap_of_geometric (h0 : ∀ᵐ l ∂ρ, 0 ≤ l) (h1 : ∀ᵐ l ∂ρ, l ≤ 1) {θ K : ℝ} (hθ : 0 < θ)
    (hdec : ∀ k : ℕ, acorr ρ k ≤ K * θ ^ k) : ρ (Ioi θ) = 0 := by
  have := (time_gap_iff h0 h1 (-Real.log θ)).mp ⟨K, fun k => by rw [exp_neg_neg_log hθ]; exact hdec k⟩
  rwa [neg_neg, Real.exp_log hθ] at this

/-- **The gap gives geometric decay.** -/
theorem geometric_of_gap (h0 : ∀ᵐ l ∂ρ, 0 ≤ l) (h1 : ∀ᵐ l ∂ρ, l ≤ 1) {θ : ℝ} (hθ : 0 < θ)
    (hgap : ρ (Ioi θ) = 0) : ∃ K : ℝ, ∀ k : ℕ, acorr ρ k ≤ K * θ ^ k := by
  obtain ⟨K, hK⟩ := (time_gap_iff h0 h1 (-Real.log θ)).mpr (by rwa [neg_neg, Real.exp_log hθ])
  exact ⟨K, fun k => by rw [← exp_neg_neg_log hθ]; exact hK k⟩

end ProofPhase.Mixing
