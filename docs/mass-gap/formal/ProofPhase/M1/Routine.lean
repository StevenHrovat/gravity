/-
Proof phase, M1 tools (m1-tools): the measure-theoretic cores of rows X1.H1 and X2 (2026-11-22). Released under
Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/ROUTINE-ROWS.md`, sections 1-2.
-/

import Mathlib

/-!
# Fibre densities exist; gauge fixing at a leaf is exact

* `fibre_rep_of_map_le` (row X1.H1): if the pushforward of the reference measure under the conditioning map is bounded
  by a multiple of the reference measure on the conditioning variable (this is what the fibre-mass bound E7.J gives),
  then every finite term `ν.withDensity ρ` has a fibre density `N` with
  `(ν.withDensity ρ).map φ = lam.withDensity N` — the hypothesis `fibreN` of `Assembly.lean` (and `fibreD` likewise).
  `N` is the Radon-Nikodym derivative, i.e. the δ-function integral `N(W) = ∫ dV δ(V̄ W⁻¹) ρ(V)`.
* `lintegral_gauge_leaf` (row X2): for a leaf `v` of the gauge-fixing tree, with tree bond variable `g` (Haar
  probability measure) and the other variables `ω` (on which the gauge transformation at `v` acts measure-preservingly),
  a gauge-invariant integrand, `F(g, ω) = F(1, g • ω)`, integrates to the same value with the tree bond set to `1`.
  Peeling leaves one at a time gives the axial-gauge identity `∫ F dU = ∫ F|_{U = 1 on the tree}` (Jacobian 1).

**Claim level.** Both proved (standard axioms). The induction over the leaves of a tree and the identification of the
objects with Balaban's are on paper (`ROUTINE-ROWS.md`).
-/

open MeasureTheory Measure
open scoped ENNReal

namespace ProofPhase.M1

/-- **Row X1.H1: fibre densities exist.** A pushforward bounded by `K • lam` (`K < ∞`) is absolutely continuous, so
every finite term has a density on the conditioning variable. -/
theorem fibre_rep_of_map_le {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ] (ν : Measure α)
    (lam : Measure γ) [SigmaFinite lam] {φ : α → γ} (hφ : Measurable φ) (ρ : α → ℝ≥0∞)
    [IsFiniteMeasure ((ν.withDensity ρ).map φ)] {K : ℝ≥0∞} (hK : ν.map φ ≤ K • lam) :
    (ν.withDensity ρ).map φ = lam.withDensity (((ν.withDensity ρ).map φ).rnDeriv lam) := by
  have h1 : (ν.withDensity ρ).map φ ≪ ν.map φ :=
    (withDensity_absolutelyContinuous ν ρ).map hφ
  have h2 : ν.map φ ≪ lam :=
    (Measure.absolutelyContinuous_of_le hK).trans
      (Measure.AbsolutelyContinuous.smul_left (Measure.AbsolutelyContinuous.refl lam) K)
  exact (Measure.withDensity_rnDeriv_eq _ _ (h1.trans h2)).symm

/-- **Row X2: gauge fixing at a leaf is exact.** -/
theorem lintegral_gauge_leaf {G Ω : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace Ω] (μ : Measure G)
    [IsProbabilityMeasure μ] (ν : Measure Ω) [SFinite ν] (act : G → Ω → Ω)
    (hact : ∀ g, MeasurePreserving (act g) ν ν) (F : G × Ω → ℝ≥0∞) (hF : Measurable F)
    (hinv : ∀ g ω, F (g, ω) = F (1, act g ω)) :
    ∫⁻ p, F p ∂(μ.prod ν) = ∫⁻ ω, F (1, ω) ∂ν := by
  have h1 : Measurable fun ω => F (1, ω) := hF.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ hF.aemeasurable]
  have hin : ∀ g, ∫⁻ ω, F (g, ω) ∂ν = ∫⁻ ω, F (1, ω) ∂ν := by
    intro g
    simp_rw [hinv g]
    exact (hact g).lintegral_comp h1
  simp_rw [hin]
  rw [lintegral_const, measure_univ, mul_one]

end ProofPhase.M1
