/-
RH-YM bridge, step 1, module 6: the link from the spectral side to the OS layer. What connects the block-level decay
hypothesis `hdec` of `gap_of_RP` to the spectral measure, stated with the spectral measure as a hypothesis
(2026-11-23). Released under Apache 2.0.

Note: `docs/rh-guide/bridge/BRIDGE.md`, addendum.
-/

import ProofPhase.Bridge.Spectral
import ProofPhase.M1.UVTVOS

/-!
# From a spectral measure to the hypothesis of `gap_of_RP`

`ProofPhase.M1.UVTV.RPData.gap_of_RP` takes, for every block observable `g`, the decay hypothesis
`hdec : ∃ C, ∀ n, Q g (τ^n g) ≤ C e^{-m n}`.

**What the spectral theorem would give.** `RPData.T` (built in `M1/UVTVOS.lean`) is a bounded, symmetric, positive
operator on the OS Hilbert space, and a contraction (`RPData.contraction`). By the spectral theorem for bounded
self-adjoint operators, the vector `Φ g` has a spectral measure `μ_g` on `[0, 1]` (the spectrum of `T`) with
`⟪Φ g, T^n Φ g⟫ = ∫ λ^n dμ_g(λ)`, and `⟪Φ g, T^n Φ g⟫ = Q g (τ^n g)` (`T_pow_Φ`, `inner_Φ`). Mathlib has the
continuous functional calculus but not spectral measures, so this step is **taken as a hypothesis**:
`TransferSpectralRep R g`, a finite measure on `[0, 1]` representing the moments `Q g (τ^n g)`.

**What is proved.**
* `moment_gap_iff`: for a finite measure on `[0, 1]`, `(∃ C, ∀ n, ∫ λ^n dμ ≤ C e^{-m n}) ↔ μ (λ > e^{-m}) = 0`.
* `hdec_iff_spectral`: given representations for all `g ∈ Blk`, the hypothesis `hdec` of `gap_of_RP` holds **if and
  only if** every `μ_g` puts no mass on `(e^{-m}, 1]`, i.e. the spectrum of `T` seen by block observables lies in
  `[0, e^{-m}]`, i.e. `H = -log T ≥ m` on them.
* `gap_of_RP_spectral`: `gap_of_RP` with `hdec` replaced by that spectral condition.
* `hdec_iff_energy`: the same in the energy variable `E = -log λ` (`spectral_gap_iff_nat`), for a representation
  `Q g (τ^n g) = ∫ e^{-n E} dν(E)` with `ν` on `[0, ∞)`. (The two forms differ only by a possible atom of `μ_g` at
  `λ = 0`, the kernel of `T`, which contributes to `n = 0` only.)
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace ProofPhase.Bridge

open ProofPhase.M1.UVTV

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The hypothesis that replaces the spectral theorem.** A finite measure on `[0, 1]` whose moments are the
transfer correlations of `g`. -/
structure TransferSpectralRep (R : RPData V) (g : V) where
  /-- The spectral measure of `Φ g` for the transfer operator `T`. -/
  μ : Measure ℝ
  finite : IsFiniteMeasure μ
  supp : ∀ᵐ x ∂μ, 0 ≤ x ∧ x ≤ 1
  rep : ∀ n : ℕ, R.Q g ((R.τ ^ n) g) = ∫ x, x ^ n ∂μ

/-- The energy form: a finite measure on `[0, ∞)` with `Q g (τ^n g) = ∫ e^{-n E} dν(E)`. -/
structure EnergySpectralRep (R : RPData V) (g : V) where
  ν : Measure ℝ
  finite : IsFiniteMeasure ν
  supp : ∀ᵐ E ∂ν, 0 ≤ E
  rep : ∀ n : ℕ, R.Q g ((R.τ ^ n) g) = corr ν n

theorem integrable_pow_of_unit {μ : Measure ℝ} [IsFiniteMeasure μ] (hs : ∀ᵐ x ∂μ, 0 ≤ x ∧ x ≤ 1) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) μ := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (hs.mono fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx.1 n)]
  exact pow_le_one₀ hx.1 hx.2

/-- **Moments of a measure on `[0, 1]`: exponential decay ⟺ no mass above `e^{-m}`.** -/
theorem moment_gap_iff {μ : Measure ℝ} [IsFiniteMeasure μ] (hs : ∀ᵐ x ∂μ, 0 ≤ x ∧ x ≤ 1) (m : ℝ) :
    (∃ C : ℝ, ∀ n : ℕ, ∫ x, x ^ n ∂μ ≤ C * Real.exp (-(m * n))) ↔ μ (Ioi (Real.exp (-m))) = 0 := by
  set a := Real.exp (-m) with ha
  have hapos : 0 < a := Real.exp_pos _
  have hpow : ∀ n : ℕ, a ^ n = Real.exp (-(m * n)) := fun n => by
    rw [ha, ← Real.exp_nat_mul]; congr 1; ring
  constructor
  · rintro ⟨C, hC⟩
    have key : ∀ b > a, μ (Ioi b) = 0 := by
      intro b hb
      have hbpos : 0 < b := hapos.trans hb
      have hle : ∀ n : ℕ, μ.real (Ioi b) ≤ C * (a / b) ^ n := by
        intro n
        have h1 := setIntegral_ge_of_const_le (c := b ^ n) (measurableSet_Ioi (a := b)) (measure_ne_top μ _)
          (fun x hx => pow_le_pow_left₀ hbpos.le (le_of_lt hx) n) (integrable_pow_of_unit hs n).integrableOn
        have h2 := setIntegral_le_integral (s := Ioi b) (integrable_pow_of_unit hs n)
          (hs.mono fun x hx => pow_nonneg hx.1 n)
        rw [smul_eq_mul] at h1
        have h3 : μ.real (Ioi b) * b ^ n ≤ C * a ^ n := by
          rw [hpow n]; linarith [hC n]
        have hbn : 0 < b ^ n := pow_pos hbpos n
        rw [div_pow, ← mul_div_assoc, le_div_iff₀ hbn]
        exact h3
      have hlt : a / b < 1 := (div_lt_one hbpos).mpr hb
      have htend : Tendsto (fun n : ℕ => C * (a / b) ^ n) atTop (𝓝 (C * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hapos.le hbpos.le) hlt).const_mul C
      have h0 : μ.real (Ioi b) ≤ 0 := by simpa using ge_of_tendsto' htend hle
      have hz : μ.real (Ioi b) = 0 := le_antisymm h0 measureReal_nonneg
      rwa [measureReal_eq_zero_iff (measure_ne_top μ _)] at hz
    have hU : Ioi a = ⋃ k : ℕ, Ioi (a + 1 / ((k : ℝ) + 1)) := by
      ext x
      simp only [mem_Ioi, mem_iUnion]
      constructor
      · intro hx
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
        exact ⟨k, by linarith⟩
      · rintro ⟨k, hk⟩
        have : 0 < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    rw [hU]
    exact measure_iUnion_null fun k => key _ (by
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith)
  · intro h0
    have hae : ∀ᵐ x ∂μ, x ≤ a := by
      rw [ae_iff]
      convert h0 using 2
      ext x; simp
    refine ⟨μ.real univ, fun n => ?_⟩
    have hb : ∀ᵐ x ∂μ, x ^ n ≤ a ^ n :=
      (hae.and hs).mono fun x hx => pow_le_pow_left₀ hx.2.1 hx.1 n
    calc ∫ x, x ^ n ∂μ ≤ ∫ _x, a ^ n ∂μ := integral_mono_ae (integrable_pow_of_unit hs n) (integrable_const _) hb
      _ = μ.real univ * Real.exp (-(m * n)) := by rw [integral_const, smul_eq_mul, hpow n]

/-- **`hdec` of `gap_of_RP` is exactly a spectral condition.** Given spectral representations of all block
observables, the block-level decay at rate `m` holds iff every spectral measure puts no mass on `(e^{-m}, 1]`. -/
theorem hdec_iff_spectral (R : RPData V) (Blk : Submodule ℝ V) (rep : ∀ g ∈ Blk, TransferSpectralRep R g)
    (m : ℝ) :
    (∀ g ∈ Blk, ∃ C : ℝ, ∀ n : ℕ, R.Q g ((R.τ ^ n) g) ≤ C * Real.exp (-(m * n))) ↔
      ∀ g (hg : g ∈ Blk), (rep g hg).μ (Ioi (Real.exp (-m))) = 0 := by
  constructor
  · intro h g hg
    have := (rep g hg).finite
    refine (moment_gap_iff (rep g hg).supp m).mp ?_
    obtain ⟨C, hC⟩ := h g hg
    exact ⟨C, fun n => (rep g hg).rep n ▸ hC n⟩
  · intro h g hg
    have := (rep g hg).finite
    obtain ⟨C, hC⟩ := (moment_gap_iff (rep g hg).supp m).mpr (h g hg)
    exact ⟨C, fun n => ((rep g hg).rep n).symm ▸ hC n⟩

/-- **The energy form of the same link** (via `spectral_gap_iff_nat`). -/
theorem hdec_iff_energy (R : RPData V) (Blk : Submodule ℝ V) (rep : ∀ g ∈ Blk, EnergySpectralRep R g) (m : ℝ) :
    (∀ g ∈ Blk, ∃ C : ℝ, ∀ n : ℕ, R.Q g ((R.τ ^ n) g) ≤ C * Real.exp (-(m * n))) ↔
      ∀ g (hg : g ∈ Blk), (rep g hg).ν (Iio m) = 0 := by
  constructor
  · intro h g hg
    have := (rep g hg).finite
    refine (spectral_gap_iff_nat (rep g hg).supp m).mp ?_
    obtain ⟨C, hC⟩ := h g hg
    exact ⟨C, fun n => (rep g hg).rep n ▸ hC n⟩
  · intro h g hg
    have := (rep g hg).finite
    obtain ⟨C, hC⟩ := (spectral_gap_iff_nat (rep g hg).supp m).mpr (h g hg)
    exact ⟨C, fun n => ((rep g hg).rep n).symm ▸ hC n⟩

/-- **`gap_of_RP` from the spectral condition.** If every block observable has a spectral measure for `T` with no
mass on `(e^{-m}, 1]`, and `F` has block approximants as in Lemma UV-TV, then `Q F (τ^n F) ≤ e^{-mn} Q F F`. -/
theorem gap_of_RP_spectral (R : RPData V) (Blk : Submodule ℝ V) (hτ : ∀ g ∈ Blk, R.τ g ∈ Blk) (m : ℝ)
    (rep : ∀ g ∈ Blk, TransferSpectralRep R g)
    (hgap : ∀ g (hg : g ∈ Blk), (rep g hg).μ (Ioi (Real.exp (-m))) = 0)
    (F : V) (f : ℕ → V) (hf : ∀ k, f k ∈ Blk) (bA bB : ℕ → ℝ)
    (hsplit : ∀ k, R.Q (F - f k) (F - f k) ≤ bB k + 2 * bA k)
    (hA : Tendsto bA atTop (𝓝 0)) (hB : Tendsto bB atTop (𝓝 0)) (n : ℕ) :
    R.Q F ((R.τ ^ n) F) ≤ Real.exp (-(m * n)) * R.Q F F :=
  R.gap_of_RP Blk hτ m ((hdec_iff_spectral R Blk rep m).mpr hgap) F f hf bA bB hsplit hA hB n

end ProofPhase.Bridge
