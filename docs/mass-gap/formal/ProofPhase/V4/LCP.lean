/-
Proof phase, cycle 5, workstream 1 (c5a-v4): the weakened line of constant physics `OnLCP'` (2026-11-22).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c5a-v4/NOTE.md`.
-/

import ProofPhase.Assembly

/-!
# `OnLCP'`: the line of constant physics with a two-sided renormalisation condition

`OnLCP` (`ProofPhase.Assembly`) asks, in its `scheme` clause, that the act number `ℓ_k · fluxRate h_k` of the unit box
**converge** to one `z⋆ > 0` for every choice of flux time limits. Nothing in the assembly uses the convergence (review
W11, S7). `OnLCP'` keeps clauses (i) and (ii) and replaces (iii) by a **two-sided bound**: from some level on, every flux
time limit of the unit box has act number in `[z_lo, z_hi]`, `0 < z_lo ≤ z_hi`. With the tuning's unit read as `L_*`
(version 4) this fixes `L_*` as a physical length up to a bounded factor, which is all a renormalisation condition must do.

* `OnLCP.toOnLCP'` (S): `OnLCP → OnLCP'` (interval `[z⋆/2, 2z⋆]`; uniformity over the flux limits by the choice
  argument of `OnLCP.eventually_actRate`). The converse fails (a bounded act number need not converge).
* Every use of `OnLCP` in the assembly needs only `OnLCP'`: the routes use `OnLCP.tendsto_a` (clause (i) alone;
  `OnLCP'.tendsto_a` here), route B uses `OnLCP.eventually_actRate` (a lower bound only; `OnLCP'.eventually_actRate`,
  and `fluxGrowth_of_conjW'`, `assembly_routeA'` restate the two consumers), and the noise test uses clause (ii)
  (`not_onLCP'_of_bounded`). Clause (ii) and `NonTrivial` stay unused by any proof: they identify Yang–Mills.

**Claim level.** Definitions and bookkeeping. The scheme clause is a bound on a decay **rate in a fixed finite spatial
box** (the flux energy of the unit box); it holds for the free photon (exact `z_e = 2πα`, r4-conjw), so it is not of gap
strength (gap table in the note).
-/

open MeasureTheory Filter Topology

open scoped Classical

noncomputable section

namespace ProofPhase

/-- **P6.7, the line of constant physics, weakened (version 4; open).** (i) `ℓ_k → ∞`; (ii) `β_k / log ℓ_k → 11/(6π²)`;
(iii′) the renormalisation condition as a **two-sided bound**: there are `0 < z_lo ≤ z_hi` and a level `k₀` such that for
every `k ≥ k₀` every flux time limit `h` of the 4D SU(2) Wilson measure on `ℤ/Tℤ × (ℤ/ℓ_kℤ)³` (the box of side one
unit) has act number `ℓ_k · fluxRate h ∈ [z_lo, z_hi]`. In version 4 the unit is read as `L_*` (the end of segment 1). -/
structure OnLCP' (T : Tuning) : Prop where
  resolution : Tendsto T.ℓ atTop atTop
  running : Tendsto (fun k => T.β k / Real.log (T.ℓ k)) atTop (𝓝 oneLoopSlope)
  scheme : ∃ zlo zhi : ℝ, 0 < zlo ∧ zlo ≤ zhi ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ h : ℕ → ℝ,
    IsFluxLimitSU2 (T.β k) (T.box k 0) h → zlo ≤ actRate (T.box k 0) h ∧ actRate (T.box k 0) h ≤ zhi

/-- Clause (i) alone gives `a_k → 0` (the only content of `OnLCP` the routes of the assembly use). -/
theorem OnLCP'.tendsto_a {T : Tuning} (h : OnLCP' T) : Tendsto T.a atTop (𝓝 0) := by
  have h1 : Tendsto (fun k => (T.ℓ k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp h.resolution
  show Tendsto (fun k => T.L₁ / (T.ℓ k : ℝ)) atTop (𝓝 0)
  exact h1.const_div_atTop T.L₁

/-- **The scheme of `OnLCP`, uniformly over flux time limits**: every neighbourhood of `z⋆` contains, from some level
on, the act number of every flux time limit of the unit box (choice argument as in `OnLCP.eventually_actRate`). -/
theorem OnLCP.eventually_mem_nhds {T : Tuning} (hL : OnLCP T) :
    ∃ zs : ℝ, 0 < zs ∧ ∀ U ∈ 𝓝 zs, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ h : ℕ → ℝ,
      IsFluxLimitSU2 (T.β k) (T.box k 0) h → actRate (T.box k 0) h ∈ U := by
  obtain ⟨zs, hzs, hz⟩ := hL.scheme
  refine ⟨zs, hzs, fun U hU => ?_⟩
  by_contra hne
  push Not at hne
  let bad : ℕ → Prop := fun k => ∃ h, IsFluxLimitSU2 (T.β k) (T.box k 0) h ∧ actRate (T.box k 0) h ∉ U
  let hs : ℕ → ℕ → ℝ := fun k =>
    if hb : bad k then hb.choose else (exists_fluxLimitSU2 (T.β k) (T.box k 0)).choose
  have hsl : ∀ k, IsFluxLimitSU2 (T.β k) (T.box k 0) (hs k) := by
    intro k
    by_cases hb : bad k
    · simp only [hs, dite_eq_left hb]; exact hb.choose_spec.1
    · simp only [hs, dite_eq_right hb]; exact (exists_fluxLimitSU2 (T.β k) (T.box k 0)).choose_spec
  have hfreq : ∃ᶠ k in atTop, actRate (T.box k 0) (hs k) ∉ U := by
    rw [frequently_atTop]
    intro k₀
    obtain ⟨k, hk, h, hh, hn⟩ := hne k₀
    have hb : bad k := ⟨h, hh, hn⟩
    refine ⟨k, hk, ?_⟩
    simp only [hs, dite_eq_left hb]
    exact hb.choose_spec.2
  have hev : ∀ᶠ k in atTop, actRate (T.box k 0) (hs k) ∈ U := (hz hs hsl).eventually_mem hU
  exact hfreq (hev.mono fun k hk => not_not.2 hk)

/-- **`OnLCP → OnLCP'`** (S), with the interval `[z⋆/2, 2z⋆]`. -/
theorem OnLCP.toOnLCP' {T : Tuning} (hL : OnLCP T) : OnLCP' T := by
  obtain ⟨zs, hzs, H⟩ := hL.eventually_mem_nhds
  obtain ⟨k₀, hk₀⟩ := H (Set.Icc (zs / 2) (2 * zs)) (Icc_mem_nhds (by linarith) (by linarith))
  exact ⟨hL.resolution, hL.running, zs / 2, 2 * zs, by positivity, by linarith, k₀,
    fun k hk h hh => hk₀ k hk h hh⟩

/-- Route B's use of the scheme (a lower bound), from `OnLCP'`. -/
theorem OnLCP'.eventually_actRate {T : Tuning} (hL : OnLCP' T) :
    ∃ zs : ℝ, 0 < zs ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ h : ℕ → ℝ, IsFluxLimitSU2 (T.β k) (T.box k 0) h →
      zs / 2 ≤ actRate (T.box k 0) h := by
  obtain ⟨zlo, zhi, hlo, -, k₀, H⟩ := hL.scheme
  exact ⟨2 * zlo, by positivity, k₀, fun k hk h hh => by have := (H k hk h hh).1; linarith⟩

/-- **W + the weakened renormalisation condition give flux confinement** (route B's Lean content, from `OnLCP'`). -/
theorem fluxGrowth_of_conjW' {T : Tuning} (hL : OnLCP' T) (hW : ConjW T) : FluxGrowth T := by
  obtain ⟨δ, hδ, hW⟩ := hW
  obtain ⟨zs, hzs, k₀, hk₀⟩ := hL.eventually_actRate
  refine ⟨δ, hδ, zs / 2, by linarith, k₀, fun k hk j => ?_⟩
  induction j with
  | zero => intro h hh; simpa using hk₀ k hk h hh
  | succ j ih =>
    intro h' hh'
    obtain ⟨h, hh⟩ := exists_fluxLimitSU2 (T.β k) (T.box k j)
    calc zs / 2 * (1 + δ) ^ (2 * (j + 1)) = (1 + δ) ^ 2 * (zs / 2 * (1 + δ) ^ (2 * j)) := by ring
      _ ≤ (1 + δ) ^ 2 * actRate (T.box k j) h := mul_le_mul_of_nonneg_left (ih h hh) (by positivity)
      _ ≤ actRate (T.box k (j + 1)) h' := hW k j h h' hh hh'

/-- **Route A's assembly from `OnLCP'`** (it used `OnLCP` only through `tendsto_a`). -/
theorem assembly_routeA' {T : Tuning} (hL : OnLCP' T) (hA : SlabDecay T) :
    MassGap T ∧ LatticeGap T ∧ LimitRP T :=
  ⟨massGap_of_latticeGap hL.tendsto_a (latticeGap_of_slabDecay hA), latticeGap_of_slabDecay hA, limitRP T⟩

/-- **Bounded bare coupling is not on the weakened line either** (clause (ii) is unchanged): pure noise and strong
coupling fail `OnLCP'`. -/
theorem not_onLCP'_of_bounded {T : Tuning} {B : ℝ} (hB : ∀ k, |T.β k| ≤ B) : ¬ OnLCP' T := by
  intro hL
  have hlog : Tendsto (fun k => Real.log (T.ℓ k)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hL.resolution)
  have h0 : Tendsto (fun k => T.β k / Real.log (T.ℓ k)) atTop (𝓝 0) := by
    have hB' : Tendsto (fun k => B / Real.log (T.ℓ k)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero (fun k => abs_nonneg _) (fun k => ?_) (tendsto_zero_iff_abs_tendsto_zero _ |>.1 hB')
    show |T.β k / Real.log (T.ℓ k)| ≤ |B / Real.log (T.ℓ k)|
    rw [abs_div, abs_div]
    exact div_le_div_of_nonneg_right ((hB k).trans (le_abs_self B)) (abs_nonneg _)
  have := tendsto_nhds_unique h0 hL.running
  exact oneLoopSlope_pos.ne this

end ProofPhase
