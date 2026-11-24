/-
The one-scale reduction, gauge instance (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/PROOF-NOTE.md`, §1.2 (hypothesis (Φ)), §1.3, §1.4, Lemma 2.1.
-/

import OneScale.Product
import AreaLaw.Concrete

/-!
# Block specifications of lattice gauge measures on the torus

The torus measure `μ_φ ∝ ∏_p φ(Re tr U_p) d(productHaar)` on `(ℤ/Nℤ)^d` with a weight satisfying (Φ):
`φ` measurable and `0 < φ_min ≤ φ ≤ φ_max` on `[-n, n]` (Wilson `φ = exp (β ·)` for every real `β`, soft admissible
weights, ...). For any finite family of link sets `B_j` (blocks of any shape: single links, cubes, ...):

* `touching B`: the plaquettes with a link in `B`;
* `gaugeSpec n φ B`: the block specification `q_B^U ∝ ∏_{p touching B} φ(Re tr U_p)` relative to the product Haar measure
  of the block links, with the outside links of `U` fixed;
* `gaugeBlockSpec`: these form a `BlockSpec` for `gaugeMeasure n φ`: probability measures, local, measurable averages,
  and the DLR identity (Lemma 2.1, via `OneScale.dlr_locSpec`: plaquettes not touching `B` do not read `B`).

So Theorem A (`OneScale.BlockSpec.theoremA_H`) applies to `gaugeMeasure n φ` for every block family on the torus; what
remains in any application is the influence bound and GDS.
-/

open MeasureTheory Finset AreaLaw.Concrete

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace OneScale.Gauge

variable {d N : ℕ} [NeZero N]

/-- The plaquettes touching a set of links. -/
def touching (B : Finset (LatticeLink d N)) : Finset (LatticePlaquette d N) :=
  univ.filter fun p => ∃ l ∈ plaqLinks p, l ∈ B

/-- The plaquettes not touching a set of links. -/
def notTouching (B : Finset (LatticeLink d N)) : Finset (LatticePlaquette d N) :=
  univ.filter fun p => ¬∃ l ∈ plaqLinks p, l ∈ B

variable {G : Type*} [Group G] {n : ℕ} [HasGaugeTrace G n]

/-- `∏_{p ∈ s} φ(Re tr U_p)`. -/
def plaqProd (n : ℕ) [HasGaugeTrace G n] (φ : ℝ → ℝ) (s : Finset (LatticePlaquette d N))
    (U : GaugeConnection G d N) : ℝ :=
  ∏ p ∈ s, φ (xp n p U)

/-- **Hypothesis (Φ)** of the proof note: `φ` measurable with `0 < φ_min ≤ φ ≤ φ_max` on `[-n, n]`. -/
structure PosWeight (n : ℕ) (φ : ℝ → ℝ) : Prop where
  meas : Measurable φ
  lower : ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, |x| ≤ n → c ≤ φ x
  upper : ∃ C : ℝ, ∀ x : ℝ, |x| ≤ n → φ x ≤ C

/-- The Wilson weight `exp (β ·)` satisfies (Φ) for every real `β`. -/
theorem posWeight_exp (n : ℕ) (β : ℝ) : PosWeight n (fun x => Real.exp (β * x)) where
  meas := Real.measurable_exp.comp (measurable_const.mul measurable_id)
  lower := ⟨Real.exp (-(|β| * n)), Real.exp_pos _, fun x hx => Real.exp_le_exp.2 (by
    have : |β * x| ≤ |β| * n := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    linarith [neg_abs_le (β * x)])⟩
  upper := ⟨Real.exp (|β| * n), fun x hx => Real.exp_le_exp.2 (by
    have : |β * x| ≤ |β| * n := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    linarith [le_abs_self (β * x)])⟩

/-- A plaquette not touching `B` does not read the links of `B`. -/
theorem xp_splice_of_not_touching {B : Finset (LatticeLink d N)} {p : LatticePlaquette d N}
    (hp : ¬∃ l ∈ plaqLinks p, l ∈ B) (U ξ : GaugeConnection G d N) : xp n p (splice B U ξ) = xp n p U := by
  unfold xp
  congr 1
  refine plaquetteHolonomy_dependsOn p _ _ fun l hl => ?_
  have : l ∉ B := fun h => hp ⟨l, hl, h⟩
  exact splice_of_not_mem this U ξ

section Measure

variable [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] [HasHaarProbability G]

variable (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)

include hU in
theorem abs_xp_le (p : LatticePlaquette d N) (U : GaugeConnection G d N) : |xp n p U| ≤ n := by
  unfold xp gaugeReTr gaugeTrace
  exact abs_re_trace_le_of_unitary (hU _)

include hc hU in
/-- Under (Φ), every partial plaquette product is a local weight. -/
theorem localWeight_plaqProd {φ : ℝ → ℝ} (hφ : PosWeight n φ) (s : Finset (LatticePlaquette d N)) :
    LocalWeight (plaqProd (G := G) n φ s) := by
  obtain ⟨c, hc0, hcφ⟩ := hφ.lower
  obtain ⟨C, hCφ⟩ := hφ.upper
  refine ⟨Finset.measurable_prod s fun p _ => hφ.meas.comp (measurable_xp hc p), ⟨c ^ s.card, pow_pos hc0 _,
    fun U => ?_⟩, ⟨C ^ s.card, fun U => ?_⟩⟩
  · unfold plaqProd
    rw [← prod_const]
    exact prod_le_prod₀ (fun _ _ => hc0.le) fun p _ => hcφ _ (abs_xp_le hU p U)
  · unfold plaqProd
    rw [← prod_const]
    exact prod_le_prod₀ (fun p _ => hc0.le.trans (hcφ _ (abs_xp_le hU p U))) fun p _ => hCφ _ (abs_xp_le hU p U)

include hc hU in
theorem plaqProd_pos {φ : ℝ → ℝ} (hφ : PosWeight n φ) (s : Finset (LatticePlaquette d N))
    (U : GaugeConnection G d N) : 0 < plaqProd n φ s U :=
  (localWeight_plaqProd hc hU hφ s).pos U

/-- The torus measure `μ_φ = Z⁻¹ ∏_p φ(Re tr U_p) · productHaar`. -/
def gaugeMeasure (n : ℕ) [HasGaugeTrace G n] (φ : ℝ → ℝ) : Measure (GaugeConnection G d N) :=
  weightMeasure (haarG G) (plaqProd n φ univ)

/-- The block specification `q_B^U ∝ ∏_{p touching B} φ(Re tr U_p)`. -/
def gaugeSpec (n : ℕ) [HasGaugeTrace G n] (φ : ℝ → ℝ) (B : Finset (LatticeLink d N)) :
    GaugeConnection G d N → Measure (GaugeConnection G d N) :=
  locSpec (haarG G) B (plaqProd n φ (touching B))

include hc hU in
theorem isProbabilityMeasure_gaugeMeasure {φ : ℝ → ℝ} (hφ : PosWeight n φ) :
    IsProbabilityMeasure (gaugeMeasure (d := d) (N := N) (G := G) n φ) := by
  have hW := localWeight_plaqProd (d := d) (N := N) hc hU hφ univ
  refine isProbabilityMeasure_weightMeasure hW.bm (fun U => (hW.pos U).le) ?_
  obtain ⟨c, hc0, h⟩ := hW.lower
  have := integral_mono (integrable_const c) (hW.bm.integrable (prodMeasure (ι := LatticeLink d N) (haarG G))) h
  simp only [integral_const, probReal_univ, one_smul] at this
  exact hc0.trans_le this

/-- `∏_p = ∏_{p touching B} · ∏_{p not touching B}`. -/
theorem plaqProd_univ_eq (φ : ℝ → ℝ) (B : Finset (LatticeLink d N)) (U : GaugeConnection G d N) :
    plaqProd n φ univ U = plaqProd n φ (touching B) U * plaqProd n φ (notTouching B) U := by
  unfold plaqProd touching notTouching
  rw [prod_filter_mul_prod_filter_not]

include hc hU in
/-- **The block specification of a gauge measure** (Lemma 2.1 for every block family on the torus). -/
def gaugeBlockSpec {φ : ℝ → ℝ} (hφ : PosWeight n φ) {J : Type*} (block : J → Finset (LatticeLink d N)) :
    BlockSpec (gaugeMeasure (d := d) (N := N) (G := G) n φ) J :=
  productBlockSpec (ν := haarG G) (plaqProd n φ univ) block (fun j => plaqProd n φ (touching (block j)))
    (fun j => plaqProd n φ (notTouching (block j)))
    (fun j => localWeight_plaqProd hc hU hφ _)
    (fun j U ξ => by
      unfold plaqProd
      refine prod_congr rfl fun p hp => ?_
      simp only [notTouching, mem_filter, mem_univ, true_and] at hp
      rw [xp_splice_of_not_touching hp])
    (fun j U => plaqProd_univ_eq φ (block j) U)
    (localWeight_plaqProd hc hU hφ univ).bm (fun U => (plaqProd_pos hc hU hφ univ U).le)

theorem gaugeBlockSpec_block {φ : ℝ → ℝ} (hφ : PosWeight n φ) {J : Type*} (block : J → Finset (LatticeLink d N))
    (j : J) : (gaugeBlockSpec hc hU hφ block).block j = block j := rfl

theorem gaugeBlockSpec_spec {φ : ℝ → ℝ} (hφ : PosWeight n φ) {J : Type*} (block : J → Finset (LatticeLink d N))
    (j : J) : (gaugeBlockSpec hc hU hφ block).spec j = gaugeSpec n φ (block j) := rfl

end Measure

end OneScale.Gauge
