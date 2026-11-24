/-
Proof phase (round 5), workstream 3: limit states at fixed spacing (PROOF-NOTE Lemma 6.3, compactness part)
(2026-11-22). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/PROOF-NOTE.md` §6.6 (Lemma 6.3);
`docs/mass-gap/weak-coupling/proof-phase/ws3-quantum/NOTE.md` (this workstream).
-/

import ProofPhase.Existence.Bridge

/-!
# Infinite-volume limit points and limit states at fixed spacing

The gap statements `LatticeGap`, `MassGap` (and workstream 4's `MassGapMF`) quantify over **every** limit point. A
universally quantified statement over an empty set would be vacuous; this file proves that the sets are never empty,
and constructs the infinite-volume limit states of PROOF-NOTE Lemma 6.3 (compactness part) on the real objects. The bare
coupling may depend on the volume (`ProofPhase.Existence.VTuning`), as in the OpenAI construction.

**Real limit points (elementary).**
* `exists_limitPoint_of_bdd`: a bounded real sequence has a limit point (Bolzano–Weierstrass).
* `exists_infVol_limitPoint`: at every level, for every family of measurable `|F_j| ≤ 1` and every lattice time, the
  reflected correlations `V.wcorr k j (F j) n` have an infinite-volume limit point (they are bounded by `2`).
* `massGap_nonvacuous`: for every tuning, slab family and physical time, there are choices `h_k` of infinite-volume
  limit points at every level and a continuum limit point `g` of them: the quantifiers of `MassGap` range over a
  non-empty set, so `MassGap` is not vacuously true.

**Limit states (substantive compactness, Prokhorov + Tychonoff).** The infinite lattice `ℤ⁴` has the countable link
set `InfLink = (Fin 4 → ℤ) × Fin 4`; `Ω = InfLink → SU(2)` is a compact metrizable space. The periodic extension
`periodize` maps a configuration on `(ℤ/Nℤ)⁴` to `Ω`; `wilsonState V k j` is the image of the SU(2) Wilson measure on
torus `j` at level `k`, a probability measure on `Ω`.
* **`exists_limitState`**: for every level `k` and every sequence of volumes, a subsequence converges weakly to a
  probability measure `μ_∞` on `Ω` (an infinite-volume limit state at fixed spacing).
* `tendsto_integral_limitState`: along it, `∫ F ∘ periodize dμ_{k,j} → ∫ F dμ_∞` for every continuous `F` on `Ω`
  (in particular every continuous function of finitely many links of `ℤ⁴`).

**Not here (paper).** Lemma 6.3 also claims convergence for every **bounded measurable** local `F` (through a density
bound on the marginals) and translation/reflection invariance of `μ_∞`; and the identification of the real limit
points of `wcorr` with correlations of a limit state needs "the same continuous observable in every volume", while
`SlabObs` allows arbitrary measurable families. These are not formalised.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.TimeShift Positivity

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Quantum

open ProofPhase.Existence

/-! ## Real limit points -/

/-- **Bolzano–Weierstrass**: a bounded real sequence has a limit point. -/
theorem exists_limitPoint_of_bdd {u : ℕ → ℝ} {B : ℝ} (hu : ∀ n, |u n| ≤ B) : ∃ h, IsLimitPoint u h := by
  have hmem : ∀ n, u n ∈ Metric.closedBall (0 : ℝ) B := fun n => by
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]; exact hu n
  obtain ⟨a, -, φ, hφ, ha⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hmem
  exact ⟨a, φ, hφ, ha⟩

theorem vwcorr_abs_le (V : VTuning) (k j : ℕ) {F : GaugeConnection SU2 4 (V.T.side k j) → ℝ}
    (hF : Measurable F) (hF1 : ∀ U, |F U| ≤ 1) (n : ℕ) : |V.wcorr k j F n| ≤ 2 :=
  abs_corr_le_two (d := 4) continuous_subtype_val (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
    (posWeight_wilson 2 (V.βv k j)) hF hF1 n

/-- **Infinite-volume limit points exist** at every level, for every family of measurable `|F_j| ≤ 1`, every lattice
time (volume-dependent coupling allowed). -/
theorem exists_infVol_limitPoint (V : VTuning) (k : ℕ) (F : ∀ j, GaugeConnection SU2 4 (V.T.side k j) → ℝ)
    (hF : ∀ j, Measurable (F j)) (hF1 : ∀ j U, |F j U| ≤ 1) (n : ℕ) :
    ∃ h, IsLimitPoint (fun j => V.wcorr k j (F j) n) h :=
  exists_limitPoint_of_bdd fun j => vwcorr_abs_le V k j (hF j) (hF1 j) n

/-- **The quantifiers of `MassGap` are never vacuous.** For every tuning, slab family and physical time there are
infinite-volume limit points `h_k` at every level and a limit point `g` of `h`. -/
theorem massGap_nonvacuous (T : Tuning) {s : ℝ} {Vb : ℕ → ℕ} (O : SlabObs T s Vb) (τ : ℝ) :
    ∃ (h : ℕ → ℝ) (g : ℝ), (∀ k, IsLimitPoint (fun j => T.wcorr k j (O.F k j) (T.steps k τ)) (h k)) ∧
      IsLimitPoint h g := by
  have hk : ∀ k, ∃ hk, IsLimitPoint (fun j => T.wcorr k j (O.F k j) (T.steps k τ)) hk := fun k =>
    exists_infVol_limitPoint T.toV k (O.F k) (O.meas k) (O.bdd k) _
  choose h hh using hk
  have hb : ∀ k, |h k| ≤ 2 := fun k =>
    (hh k).abs_le (Eventually.of_forall fun j => T.abs_wcorr_le k j (O.meas k j) (O.bdd k j) _)
  obtain ⟨g, hg⟩ := exists_limitPoint_of_bdd hb
  exact ⟨h, g, hh, hg⟩

/-! ## Limit states on the infinite lattice -/

/-- The links of `ℤ⁴`: a base site and a direction. -/
abbrev InfLink := (Fin 4 → ℤ) × Fin 4

/-- Configurations of SU(2) link variables on `ℤ⁴`. -/
abbrev InfConf := InfLink → SU2

/-- The periodic extension of a configuration on `(ℤ/Nℤ)⁴` to `ℤ⁴`. -/
def periodize (N : ℕ) (U : GaugeConnection SU2 4 N) : InfConf := fun ℓ => U ⟨fun i => (ℓ.1 i : ZMod N), ℓ.2⟩

theorem measurable_periodize (N : ℕ) : Measurable (periodize N) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

theorem continuous_periodize (N : ℕ) : Continuous (periodize N) :=
  continuous_pi fun _ => continuous_apply _

theorem ym_isProbV (V : VTuning) (k j : ℕ) : IsProbabilityMeasure (V.ym k j) :=
  isProbabilityMeasure_gaugeMeasure (d := 4) (N := V.T.side k j) continuous_subtype_val
    (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) (posWeight_wilson 2 (V.βv k j))

/-- The SU(2) Wilson measure at level `k` on torus `j`, periodically extended to `ℤ⁴`: a probability measure on `Ω`. -/
def wilsonState (V : VTuning) (k j : ℕ) : ProbabilityMeasure InfConf :=
  ⟨(V.ym k j).map (periodize (V.T.side k j)), by
    have := ym_isProbV V k j
    exact (Measure.isProbabilityMeasure_map_iff (measurable_periodize _).aemeasurable).2 this⟩

/-- **Infinite-volume limit states exist at fixed spacing (Lemma 6.3, compactness part).** For every level `k` and
every sequence of volumes `j_n`, a subsequence of the periodically extended SU(2) Wilson measures converges weakly to a
probability measure on the configurations of `ℤ⁴`. -/
theorem exists_limitState (V : VTuning) (k : ℕ) (jseq : ℕ → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ μ : ProbabilityMeasure InfConf,
      Tendsto (fun n => wilsonState V k (jseq (φ n))) atTop (𝓝 μ) := by
  obtain ⟨μ, -, φ, hφ, h⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (ProbabilityMeasure InfConf))).tendsto_subseq
      (fun n => Set.mem_univ (wilsonState V k (jseq n)))
  exact ⟨φ, hφ, μ, h⟩

/-- Along a convergent subsequence of `exists_limitState`, the expectations of every continuous function of the
periodically extended field converge to the limit state's. -/
theorem tendsto_integral_limitState (V : VTuning) (k : ℕ) {jseq : ℕ → ℕ} {μ : ProbabilityMeasure InfConf}
    (h : Tendsto (fun n => wilsonState V k (jseq n)) atTop (𝓝 μ)) {F : InfConf → ℝ} (hF : Continuous F) :
    Tendsto (fun n => ∫ U, F (periodize (V.T.side k (jseq n)) U) ∂(V.ym k (jseq n))) atTop
      (𝓝 (∫ ω, F ω ∂(μ : Measure InfConf))) := by
  have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h) (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩)
  refine this.congr fun n => ?_
  show ∫ ω, F ω ∂((V.ym k (jseq n)).map (periodize _)) = _
  rw [integral_map (measurable_periodize _).aemeasurable hF.aestronglyMeasurable]

end ProofPhase.Quantum
