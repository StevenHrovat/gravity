/-
The DMP reading "bounded reach / bounded time to live" as theorems about lattice Yang–Mills at strong coupling (area-law project,
2026-11-21). Released under Apache 2.0.

# What is stated

* `HasReach E ξ C`: the state `E` (an expectation on observables) has reach `ξ`: for bounded local observables `f`, `g` on
  disjoint link sets `L_F`, `L_G` whose touching plaquettes are at distance at least `r` in the plaquette graph, the connected
  correlation is at most `C(|L_F|, |L_G|) e^{-r/ξ}`.
* `strong_coupling_has_reach`: for a compact group as in `wilson_clustering_explicit` and `0 < q < 1`,
  `q = (16 d)² (1 − e^{−4n|β|})`, the Wilson measure has reach `ξ = 1 / log(1/q)` on every lattice `(ℤ/Nℤ)^d`, with `ξ` and the
  constant `8 d |L_F| / (1 − q)` independent of `N`. SU(2) and U(n): `strong_coupling_has_reach_SU2`, `strong_coupling_has_reach_Un`.
* `existence_floor_of_reach`: the real-number version of `Dmp.mg_reach_existence_floor` (`evidence/Dmp/Reach.lean`): existence
  times extent equal to one quantum `Q`, extent within the reach `R`, give existence at least `Q / R`.
* `strong_coupling_existence_floor` (and the SU(2), U(n) versions): with one quantum = 1 in lattice units and the reach `ξ` above,
  existence is at least `1 / ξ = log(1/q)`: the mass gap in lattice units at strong coupling.

The covariance is computed over two independent copies of the configuration (`AreaLaw.Clustering.cov_two_copies`,
`two_copies_weighted`); the proof is in `AreaLaw/Clustering.lean`.

# What is not stated

This is the gap at strong coupling (`|β|` small: for `d = 4`, `n = 2`, `|β|` below about `3 × 10⁻⁵`), known physics
(Osterwalder–Seiler 1978), proved here in the same framework as the area law. It says nothing about weak coupling or the continuum
limit, where the Yang–Mills mass gap is open. "Existence × extent = one quantum" is a DMP postulate, entered here as a hypothesis;
Lean checks only the arithmetic that follows from it.
-/

import AreaLaw.Clustering

open scoped Classical

open Finset MeasureTheory AreaLaw.Assembly AreaLaw.Clustering AreaLaw.Concrete

set_option linter.unusedSectionVars false

noncomputable section

namespace AreaLaw.Reach

section Defs

variable {G : Type*} [Group G] [MeasurableSpace G] {d N : ℕ} [Fintype (LatticePlaquette d N)]

/-- A bounded local observable: measurable, bounded by one, depending only on the links in `L`. -/
def IsLocalObs (f : GaugeConnection G d N → ℝ) (L : Finset (LatticeLink d N)) : Prop :=
  Measurable f ∧ (∀ U, |f U| ≤ 1) ∧ LinkDep f L

/-- The plaquettes touching `L_F` and those touching `L_G` are at distance at least `r` in the plaquette graph. -/
def PlaqSep (LF LG : Finset (LatticeLink d N)) (r : ℕ) : Prop :=
  ∀ a ∈ touchPlaqs LF, ∀ b ∈ touchPlaqs LG, r ≤ (plaqGraph d N).dist a b

/-- **Reach.** The state `E` has reach `ξ` with constant `C`: connected correlations of bounded local observables on disjoint
    supports at plaquette distance at least `r` are at most `C(|L_F|, |L_G|) e^{-r/ξ}`. -/
def HasReach (E : (GaugeConnection G d N → ℝ) → ℝ) (ξ : ℝ) (C : ℕ → ℕ → ℝ) : Prop :=
  ∀ (f g : GaugeConnection G d N → ℝ) (LF LG : Finset (LatticeLink d N)) (r : ℕ),
    IsLocalObs f LF → IsLocalObs g LG → Disjoint LF LG → PlaqSep LF LG r →
      |E (fun U => f U * g U) - E f * E g| ≤ C LF.card LG.card * Real.exp (-(r : ℝ) / ξ)

end Defs

/-- `e^{-r/ξ} = q^r` for `ξ = 1 / (-log q)`, `q > 0`. -/
theorem exp_neg_div_reach {q : ℝ} (h0 : 0 < q) (r : ℕ) : Real.exp (-(r : ℝ) / (1 / -Real.log q)) = q ^ r := by
  rw [show -(r : ℝ) / (1 / -Real.log q) = r * Real.log q by rw [div_div_eq_mul_div, div_one]; ring,
    Real.exp_nat_mul, Real.exp_log h0]

/-- **The existence floor, real numbers** (the real version of `Dmp.mg_reach_existence_floor`). If existence `x` times extent `e`
    is one quantum `Q ≥ 0` and the extent lies within the reach (`0 < e ≤ R`), then `x ≥ Q / R`. Read in time (extent = time to
    live, reach = longest renewal time), the same lemma is the TTL floor. -/
theorem existence_floor_of_reach {Q R x e : ℝ} (hQ : 0 ≤ Q) (he : 0 < e) (hreach : e ≤ R) (hact : x * e = Q) :
    Q / R ≤ x := by
  have hx : x = Q / e := by rw [← hact, mul_div_cancel_right₀ _ he.ne']
  rw [hx]
  exact div_le_div_of_nonneg_left hQ he hreach

section General

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {n : ℕ} [HasGaugeTrace G n] [HasHaarProbability G]

/-- **Strong coupling has reach.** For a group with a continuous representation, `|Re tr| ≤ n` and a probability measure on a link,
    and `0 < q < 1`, `q = (16 d)² (1 − e^{−4n|β|})`: on every lattice `(ℤ/Nℤ)^d` the Wilson measure has reach `ξ = 1 / log(1/q)`
    with constant `8 d |L_F| / (1 − q)`. Neither depends on `N`. -/
theorem strong_coupling_has_reach (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (hbd : ∀ g : G, |gaugeReTr G n g| ≤ n) (β : ℝ) (h0 : 0 < qClust d n β) (hq : qClust d n β < 1) :
    ∀ (N : ℕ) [NeZero N], HasReach (G := G) (d := d) (N := N) (wilsonExpect n β) (1 / -Real.log (qClust d n β))
      (fun a _ => 8 * d * a / (1 - qClust d n β)) := by
  intro N _ f g LF LG r hf hg hdisj hr
  obtain ⟨mf, hf1, hfd⟩ := hf
  obtain ⟨mg, hg1, hgd⟩ := hg
  have h := (wilson_clustering_explicit hc hbd β hq hfd hgd mf mg hf1 hg1 hdisj hr).2
  rw [exp_neg_div_reach h0]
  calc _ ≤ 8 * d * LF.card * qClust d n β ^ r / (1 - qClust d n β) := h
    _ = _ := by ring

/-- **The existence floor at strong coupling.** In the window of `strong_coupling_has_reach`, `m = log(1/q) > 0`, the Wilson
    measure has reach `ξ = 1 / m` uniformly in `N`, and under the postulate "existence × extent = one quantum" (one quantum = 1 in
    lattice units, hypothesis `x * e = 1`) every act whose extent lies within the reach has existence at least `m`. -/
theorem strong_coupling_existence_floor (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (hbd : ∀ g : G, |gaugeReTr G n g| ≤ n) (β : ℝ) (h0 : 0 < qClust d n β) (hq : qClust d n β < 1) :
    0 < -Real.log (qClust d n β) ∧
    (∀ (N : ℕ) [NeZero N], HasReach (G := G) (d := d) (N := N) (wilsonExpect n β) (1 / -Real.log (qClust d n β))
      (fun a _ => 8 * d * a / (1 - qClust d n β))) ∧
    ∀ x e : ℝ, 0 < e → e ≤ 1 / -Real.log (qClust d n β) → x * e = 1 → -Real.log (qClust d n β) ≤ x := by
  refine ⟨neg_pos.mpr (Real.log_neg h0 hq), strong_coupling_has_reach hc hbd β h0 hq, fun x e he hreach hact => ?_⟩
  have h := existence_floor_of_reach zero_le_one he hreach hact
  rwa [one_div_one_div] at h

end General

/-- **SU(2) has reach at strong coupling**: `0 < q = (16 d)² (1 − e^{−8|β|}) < 1` gives reach `ξ = 1 / log(1/q)`, uniformly in `N`. -/
theorem strong_coupling_has_reach_SU2 {d : ℕ} (β : ℝ) (h0 : 0 < qClust d 2 β) (hq : qClust d 2 β < 1) :
    ∀ (N : ℕ) [NeZero N], HasReach (G := SU2) (d := d) (N := N) (wilsonExpect 2 β) (1 / -Real.log (qClust d 2 β))
      (fun a _ => 8 * d * a / (1 - qClust d 2 β)) :=
  strong_coupling_has_reach (G := SU2) continuous_subtype_val
    (fun g => abs_re_trace_le_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)) β h0 hq

/-- **U(n) has reach at strong coupling**: `0 < q = (16 d)² (1 − e^{−4n|β|}) < 1` gives reach `ξ = 1 / log(1/q)`, uniformly in `N`. -/
theorem strong_coupling_has_reach_Un {d : ℕ} (n : ℕ) (β : ℝ) (h0 : 0 < qClust d n β) (hq : qClust d n β < 1) :
    ∀ (N : ℕ) [NeZero N], HasReach (G := Un n) (d := d) (N := N) (wilsonExpect n β) (1 / -Real.log (qClust d n β))
      (fun a _ => 8 * d * a / (1 - qClust d n β)) :=
  strong_coupling_has_reach (G := Un n) continuous_subtype_val (fun g => abs_re_trace_le_of_unitary g.2) β h0 hq

/-- **The existence floor for SU(2) at strong coupling**: existence at least `log(1/q)` in lattice units. -/
theorem strong_coupling_existence_floor_SU2 {d : ℕ} (β : ℝ) (h0 : 0 < qClust d 2 β) (hq : qClust d 2 β < 1) :
    0 < -Real.log (qClust d 2 β) ∧
    ∀ x e : ℝ, 0 < e → e ≤ 1 / -Real.log (qClust d 2 β) → x * e = 1 → -Real.log (qClust d 2 β) ≤ x := by
  obtain ⟨h1, -, h3⟩ := strong_coupling_existence_floor (G := SU2) (d := d) continuous_subtype_val
    (fun g => abs_re_trace_le_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)) β h0 hq
  exact ⟨h1, h3⟩

/-- **The existence floor for U(n) at strong coupling**: existence at least `log(1/q)` in lattice units. -/
theorem strong_coupling_existence_floor_Un {d : ℕ} (n : ℕ) (β : ℝ) (h0 : 0 < qClust d n β) (hq : qClust d n β < 1) :
    0 < -Real.log (qClust d n β) ∧
    ∀ x e : ℝ, 0 < e → e ≤ 1 / -Real.log (qClust d n β) → x * e = 1 → -Real.log (qClust d n β) ≤ x := by
  obtain ⟨h1, -, h3⟩ := strong_coupling_existence_floor (G := Un n) (d := d) continuous_subtype_val
    (fun g => abs_re_trace_le_of_unitary g.2) β h0 hq
  exact ⟨h1, h3⟩

end AreaLaw.Reach
