/-
Proof phase, cycle 4, workstream 1 (c4a-condmass): the conditional-decoupling input, joined with c4c's filter form
(2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c4a-condmass/NOTE.md`.
-/

import ProofPhase.V3.W1Route
import ProofPhase.Seg2.Filter

/-!
# Part (c) of the time-separated transfer: one input, three sufficient conditions

The assembly needs part (c) of the transfer only for time-separated pairs of gauge-invariant observables of bounded
physical extent: that is c4c-seg2's `Seg2.CondDecouple T B (sepT T)` with the time-separation predicate `sepT`. This file
makes it the input and proves it from three sides:

* `CondMassAnn T B` (**named hypothesis, open; the recommended form of `CondMass`**): the conditional covariance given the
  block field, **averaged over the block field** (annealed), is exponentially small for time-separated gauge-invariant
  observables of bounded physical extent. `condDecouple_of_condMassAnn` (S, small): `CondMassAnn ⇒ CondDecouple`.
* `CondMass` (Dobrushin–Shlosman, local on super-sites, quenched almost surely): `condMassAnn_of_condMassDecay` (S, small)
  and `condDecouple_of_condMass` (S): `CondMass ⇒ CondMassDecay ⇒ CondMassAnn ⇒ CondDecouple`.
* c4c's `Seg2.SmootherStable T B (sepT T)` (filter form; Markov split at slices plus smoother stability):
  `Seg2.condDecouple_of_smootherStable` (c4c, Lean), and `Seg2.AnnealedContraction ⇒ SmootherStable` (c4c, Lean).

Then `obsTransferPhysT_of_condDecouple` and `obsTransferPhysTW_of_condDecouple` (S): `CondDecouple ∧ ObsQuasiLocT(W) ⇒
ObsTransferPhysT(W)`.

**Why the annealed form is the one to prove** (c3a §2.1, c4c §0 and §4): a quenched bound for every block configuration
can be false by the Rebeschini–van Handel mechanism (strong observations of composite quantities can create a phase
transition of the conditioned system); the annealed form only asks that such configurations be rare, which is how large
fields are handled in Balaban's programme. `CondMass` (quenched a.e., uniform constants) is the Lean-checkable Dobrushin
form and is strictly stronger; it stays as one sufficient condition.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  ProofPhase.Torus ProofPhase.H1 ProofPhase.Certified

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.V3

/-- **Time separation at physical distance `D ≥ 0`** as a separation predicate for c4c's `CondDecouple`. -/
def sepT (T : Tuning) : Seg2.SepPred T :=
  fun k _ A₀ B₀ D => 0 ≤ D ∧ ∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * timeDist e e'

/-- **`CondMass`, annealed (named hypothesis, open).** One rate `m > 0`; for every physical extent `R` a constant `c` and a
level `k₀` such that for gauge-invariant measurable `|F|, |G| ≤ 1` with supports of physical extent `≤ R` at physical
time distance `≥ D ≥ 0`, the mean absolute conditional covariance given the block field is `≤ c e^{−mD}`. -/
def CondMassAnn (T : Tuning) (B : BlockingFamily T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink 4 (T.side k j))) (D : ℝ),
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R → sepT T k j A₀ B₀ D →
    ∫ U, |condCov (T.ym k j) (MeasurableSpace.comap (B k j).B inferInstance) F G U| ∂(T.ym k j)
      ≤ c * Real.exp (-(m * D))

/-- **The quenched decay form gives the annealed one** (S, small). -/
theorem condMassAnn_of_condMassDecay {T : Tuning} {B : BlockingFamily T} (h : CondMassDecay T B) :
    CondMassAnn T B := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, hc, k₀, Hk⟩ := H R
  refine ⟨c, hc, k₀, fun k hk j F G A₀ B₀ D mF mG bF bG _ _ dF dG eA _ hsep => ?_⟩
  have := UV.ymProb T k j
  have hae := Hk k hk j F G A₀ B₀ D mF mG bF bG dF dG eA
    (fun e he e' he' => (hsep.2 e he e' he').trans
      (mul_le_mul_of_nonneg_left (timeDist_le_linkDist e e') (T.a_pos k).le))
  have h2 := norm_integral_le_of_norm_le_const (μ := T.ym k j)
    (f := fun U => |condCov (T.ym k j) (MeasurableSpace.comap (B k j).B inferInstance) F G U|)
    (C := c * Real.exp (-(m * D))) (hae.mono fun U hU => by rwa [Real.norm_eq_abs, abs_abs])
  have h3 : |∫ U, |condCov (T.ym k j) (MeasurableSpace.comap (B k j).B inferInstance) F G U| ∂(T.ym k j)| ≤
      c * Real.exp (-(m * D)) := by simpa using h2
  exact (le_abs_self _).trans h3

/-- **`CondMassAnn` gives part (c) for time-separated pairs** (S, small): `|condDefect| = |∫ condCov| ≤ ∫ |condCov|`. -/
theorem condDecouple_of_condMassAnn {T : Tuning} {B : BlockingFamily T} (h : CondMassAnn T B) :
    Seg2.CondDecouple T B (sepT T) := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, hc, k₀, Hk⟩ := H R
  refine ⟨c, hc, k₀, fun k hk j F G A₀ B₀ D mF mG bF bG gF gG dF dG eA eB hS => ?_⟩
  have := UV.ymProb T k j
  rw [condDefect_eq_integral_condCov (B k j).meas.comap_le (UV.Bdd1.of_measurable mF bF)
    (UV.Bdd1.of_measurable mG bG)]
  exact abs_integral_le_integral_abs.trans (Hk k hk j F G A₀ B₀ D mF mG bF bG gF gG dF dG eA eB hS)

/-- **`CondMass` (Dobrushin–Shlosman form) gives part (c) for time-separated pairs** (S). -/
theorem condDecouple_of_condMass {T : Tuning} {B : BlockingFamily T} (h : CondMass T B) :
    Seg2.CondDecouple T B (sepT T) :=
  condDecouple_of_condMassAnn (condMassAnn_of_condMassDecay (condMassDecay_of_condMass h))

/-- **Part (c) and quasi-locality give the time-separated transfer** (S). -/
theorem obsTransferPhysT_of_condDecouple {T : Tuning} {B : BlockingFamily T} (h1 : Seg2.CondDecouple T B (sepT T))
    (h2 : ObsQuasiLocT T B) : ObsTransferPhysT T B := by
  obtain ⟨m₁, hm₁, H1⟩ := h1
  obtain ⟨m₂, hm₂, H2⟩ := h2
  refine ⟨min m₁ m₂, lt_min hm₁ hm₂, fun R => ?_⟩
  obtain ⟨c₁, hc₁, k₁, Hk1⟩ := H1 R
  obtain ⟨c₂, K, hc₂, k₂, Hk2⟩ := H2 R
  refine ⟨c₁ + c₂, K, by positivity, max k₁ k₂,
    fun k hk j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eA eB hsep => ?_⟩
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hv, hsep', hEF, hEG⟩ :=
    Hk2 k ((le_max_right _ _).trans hk) j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eA eB hsep
  have hdec := Hk1 k ((le_max_left _ _).trans hk) j F G A₀ B₀ D mF mG bF bG gF gG dF dG eA eB ⟨hD, hsep⟩
  have hE1 : Real.exp (-(m₁ * D)) ≤ Real.exp (-(min m₁ m₂ * D)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left m₁ m₂])
  have hE2 : Real.exp (-(m₂ * D)) ≤ Real.exp (-(min m₁ m₂ * D)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right m₁ m₂])
  have hx := Real.exp_pos (-(min m₁ m₂ * D))
  refine ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hv, hsep', ?_, ?_, ?_⟩
  · refine hEF.trans ?_
    calc c₂ * Real.exp (-(m₂ * D)) ≤ c₂ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE2 hc₂
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le
  · refine hEG.trans ?_
    calc c₂ * Real.exp (-(m₂ * D)) ≤ c₂ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE2 hc₂
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le
  · refine hdec.trans ?_
    calc c₁ * Real.exp (-(m₁ * D)) ≤ c₁ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE1 hc₁
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le

/-- **Part (c) and Lipschitz quasi-locality give the W₁ time-separated transfer** (S). -/
theorem obsTransferPhysTW_of_condDecouple {T : Tuning} {B : BlockingFamily T} (h1 : Seg2.CondDecouple T B (sepT T))
    (h2 : ObsQuasiLocTW T B) : ObsTransferPhysTW T B := by
  obtain ⟨m₁, hm₁, H1⟩ := h1
  obtain ⟨m₂, hm₂, H2⟩ := h2
  refine ⟨min m₁ m₂, lt_min hm₁ hm₂, fun R => ?_⟩
  obtain ⟨c₁, hc₁, k₁, Hk1⟩ := H1 R
  obtain ⟨c₂, K, hc₂, hK, k₂, Hk2⟩ := H2 R
  refine ⟨c₁ + c₂, K, by positivity, hK, max k₁ k₂,
    fun k hk j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eA eB hsep => ?_⟩
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hv, hlip, hsep', hEF, hEG⟩ :=
    Hk2 k ((le_max_right _ _).trans hk) j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eA eB hsep
  have hdec := Hk1 k ((le_max_left _ _).trans hk) j F G A₀ B₀ D mF mG bF bG gF gG dF dG eA eB ⟨hD, hsep⟩
  have hE1 : Real.exp (-(m₁ * D)) ≤ Real.exp (-(min m₁ m₂ * D)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left m₁ m₂])
  have hE2 : Real.exp (-(m₂ * D)) ≤ Real.exp (-(min m₁ m₂ * D)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right m₁ m₂])
  have hx := Real.exp_pos (-(min m₁ m₂ * D))
  refine ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hv, hlip, hsep', ?_, ?_, ?_⟩
  · refine hEF.trans ?_
    calc c₂ * Real.exp (-(m₂ * D)) ≤ c₂ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE2 hc₂
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le
  · refine hEG.trans ?_
    calc c₂ * Real.exp (-(m₂ * D)) ≤ c₂ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE2 hc₂
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le
  · refine hdec.trans ?_
    calc c₁ * Real.exp (-(m₁ * D)) ≤ c₁ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE1 hc₁
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le

/-- The time-separated transfer contains its part (c) (D). -/
theorem condDecouple_of_obsTransferPhysT {T : Tuning} {B : BlockingFamily T} (h : ObsTransferPhysT T B) :
    Seg2.CondDecouple T B (sepT T) := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, K, hc, k₀, Hk⟩ := H R
  refine ⟨c, hc, k₀, fun k hk j F G A₀ B₀ D mF mG bF bG gF gG dF dG eA eB hS => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hdec⟩ :=
    Hk k hk j F G A₀ B₀ D hS.1 mF mG bF bG gF gG dF dG eA eB hS.2
  exact hdec

end ProofPhase.V3
