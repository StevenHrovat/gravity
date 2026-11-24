/-
Proof phase, cycle 8, workstream 3 (c8c-concrete): the fine box law of the Wilson measure, measurability and gauge
covariance (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c8c-concrete/NOTE.md`, section 1.
-/

import ProofPhase.OneBox2.Lift

/-!
# The fine box specification of the SU(2) Wilson measure: measurable and gauge covariant

The conditional law of the links of a block `B` given all the others is `OneScale.Gauge.gaugeSpec` (the DLR box
kernel, `exp(β ∑_{p touching B} Re tr U_p) × Haar`).  `OneScale.Gauge.gaugeBlockSpec` already proves that these form a
`BlockSpec` of the Wilson measure for every family of blocks (probability, locality, measurable block averages, DLR).
This file adds what the one-box criterion still needed:

* `measurable_gaugeSpec`: the kernel is measurable as a measure-valued map of the boundary condition (so that the
  lifted block averages are measurable);
* `xp_gauge`, `plaqProd_gauge`: the plaquette weight is invariant under every gauge transformation;
* `gaugeSpec_covariant`: **gauge covariance** `q(g·σ) = g_* q(σ)` for **every** gauge transformation `g` of the
  whole torus (hence in particular for those of the box interior), as an equality of measures on all configurations.
-/

open MeasureTheory Finset OneScale OneScale.Gauge AreaLaw.Concrete ProofPhase.V3 ProofPhase.OneBox

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.OneBox2

/-! ## Measurability of the kernel -/

section Meas

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] {ν : Measure S} [IsProbabilityMeasure ν]

/-- **The local specification is a measurable kernel** of the boundary condition. -/
theorem measurable_locSpec {B : Finset ι} {W : (ι → S) → ℝ} (hW : LocalWeight W) :
    Measurable (locSpec ν B W) := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  have e : (fun σ => locSpec ν B W σ A) = fun σ =>
      ∫⁻ ξ, A.indicator (fun ξ => ENNReal.ofReal (W (splice B σ ξ) / locZ ν B W σ)) ξ ∂(prodMeasure ν) := by
    funext σ
    unfold locSpec
    rw [withDensity_apply _ hA, ← lintegral_indicator hA]
  rw [e]
  have hm : Measurable (fun p : (ι → S) × (ι → S) =>
      A.indicator (fun ξ => ENNReal.ofReal (W (splice B p.1 ξ) / locZ ν B W p.1)) p.2) := by
    have h1 : Measurable (fun p : (ι → S) × (ι → S) =>
        ENNReal.ofReal (W (splice B p.1 p.2) / locZ ν B W p.1)) :=
      (((hW.meas.comp (measurable_splice B)).div (hW.measurable_locZ.comp measurable_fst))).ennreal_ofReal
    exact Measurable.ite (measurableSet_preimage measurable_snd hA) h1 measurable_const
  exact hm.lintegral_prod_right'

end Meas

/-! ## SU(2) Wilson: constants -/

theorem su2_hc' : Continuous (HasGaugeTrace.rep (G := SU2) (n := 2)) := continuous_subtype_val

theorem su2_hU' : ∀ g : SU2, HasGaugeTrace.rep (G := SU2) (n := 2) g ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2

theorem posWeight_wilson' (β : ℝ) : PosWeight 2 (fun x => Real.exp (β * x)) := posWeight_exp 2 β

theorem measurable_gaugeSpec {N : ℕ} [NeZero N] (β : ℝ) (B : Finset (LatticeLink 4 N)) :
    Measurable (gaugeSpec (G := SU2) (d := 4) (N := N) 2 (fun x => Real.exp (β * x)) B) :=
  measurable_locSpec (localWeight_plaqProd su2_hc' su2_hU' (posWeight_wilson' β) _)

/-! ## Gauge invariance of the plaquette weight -/

section GaugeInv

variable {N : ℕ} [NeZero N]

theorem plaquetteHolonomy_gauge (g : GaugeTransform SU2 4 N) (U : GaugeConnection SU2 4 N)
    (p : LatticePlaquette 4 N) :
    plaquetteHolonomy (gaugeTransformConnection g U) p = g p.site * plaquetteHolonomy U p * (g p.site)⁻¹ := by
  have hc := siteShift_comm 4 N p.site p.dir1 p.dir2 (ne_of_lt p.h_lt)
  simp only [plaquetteHolonomy, gaugeTransformConnection, LatticePlaquette.boundaryLinks, LatticeLink.target, hc]
  group

theorem gaugeTrace_conj (a b : SU2) : gaugeTrace SU2 2 (a * b * a⁻¹) = gaugeTrace SU2 2 b := by
  unfold gaugeTrace
  rw [map_mul, map_mul, Matrix.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem xp_gauge (g : GaugeTransform SU2 4 N) (U : GaugeConnection SU2 4 N) (p : LatticePlaquette 4 N) :
    xp 2 p (gaugeTransformConnection g U) = xp 2 p U := by
  unfold xp gaugeReTr
  rw [plaquetteHolonomy_gauge, gaugeTrace_conj]

theorem plaqProd_gauge (φ : ℝ → ℝ) (s : Finset (LatticePlaquette 4 N)) (g : GaugeTransform SU2 4 N)
    (U : GaugeConnection SU2 4 N) :
    plaqProd (G := SU2) 2 φ s (gaugeTransformConnection g U) = plaqProd 2 φ s U := by
  unfold plaqProd
  exact prod_congr rfl fun p _ => by rw [xp_gauge]

end GaugeInv

/-! ## Gauge covariance of the box kernel -/

section Cov

variable {N : ℕ} [NeZero N]

/-- Pushing a density forward along a measurable equivalence. -/
theorem map_withDensity_equiv {X : Type*} [MeasurableSpace X] (e : X ≃ᵐ X) (μ : Measure X) (f : X → ENNReal)
    (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm) := by
  ext A hA
  rw [Measure.map_apply e.measurable hA, withDensity_apply _ (e.measurable hA), withDensity_apply _ hA,
    setLIntegral_map hA (hf.comp e.symm.measurable) e.measurable]
  simp only [Function.comp, MeasurableEquiv.symm_apply_apply]

theorem act_act_inv (g : GaugeTransform SU2 4 N) (U : GaugeConnection SU2 4 N) :
    act (gaugeAct N) g (act (gaugeAct N) (fun x => (g x)⁻¹) U) = U := by
  funext l; simp only [act, gaugeAct]; group

theorem act_inv_act (g : GaugeTransform SU2 4 N) (U : GaugeConnection SU2 4 N) :
    act (gaugeAct N) (fun x => (g x)⁻¹) (act (gaugeAct N) g U) = U := by
  funext l; simp only [act, gaugeAct]; group

/-- The gauge transformation `g` as a measurable equivalence of the configuration space. -/
def gaugeEquiv (g : GaugeTransform SU2 4 N) : GaugeConnection SU2 4 N ≃ᵐ GaugeConnection SU2 4 N where
  toFun := act (gaugeAct N) g
  invFun := act (gaugeAct N) (fun x => (g x)⁻¹)
  left_inv U := act_inv_act g U
  right_inv U := act_act_inv g U
  measurable_toFun := measurable_act (measurable_gaugeAct N) g
  measurable_invFun := measurable_act (a := gaugeAct N) (measurable_gaugeAct N) (fun x => (g x)⁻¹)

theorem haar_map_conj (a c : SU2) : (haarG SU2).map (fun u => a * u * c) = haarG SU2 := by
  have h1 : (fun u : SU2 => a * u * c) = (fun u => u * c) ∘ (fun u => a * u) := rfl
  rw [h1, ← Measure.map_map (measurable_mul_const c) (measurable_const_mul a),
    (measurePreserving_mul_left (haarG SU2) a).map_eq, (measurePreserving_mul_right (haarG SU2) c).map_eq]

/-- **The product Haar measure is invariant under every gauge transformation.** -/
theorem prod_map_act (g : GaugeTransform SU2 4 N) :
    (prodMeasure (ι := LatticeLink 4 N) (haarG SU2)).map (act (gaugeAct N) g) =
      prodMeasure (haarG SU2) := by
  have h := Measure.pi_map_pi (μ := fun _ : LatticeLink 4 N => haarG SU2)
    (f := fun l u => gaugeAct N g l u) (fun l => (measurable_gaugeAct N g l).aemeasurable)
  refine h.trans ?_
  unfold prodMeasure
  congr 1
  funext l
  exact haar_map_conj _ _

/-- A local specification with a gauge-invariant weight is gauge covariant. -/
theorem locSpec_covariant (B : Finset (LatticeLink 4 N)) {W : GaugeConnection SU2 4 N → ℝ} (hW : LocalWeight W)
    (hinv : ∀ (g : GaugeTransform SU2 4 N) U, W (act (gaugeAct N) g U) = W U) :
    SpecCovariant (gaugeAct N) (locSpec (haarG SU2) B W) := by
  intro g σ
  set π := prodMeasure (ι := LatticeLink 4 N) (haarG SU2)
  set e := gaugeEquiv g
  have he : ⇑e = act (gaugeAct N) g := rfl
  have hesymm : ⇑e.symm = act (gaugeAct N) (fun x => (g x)⁻¹) := rfl
  have key : ∀ ξ, W (splice B (act (gaugeAct N) g σ) ξ) = W (splice B σ (e.symm ξ)) := by
    intro ξ
    have h1 : splice B (act (gaugeAct N) g σ) ξ = act (gaugeAct N) g (splice B σ (e.symm ξ)) := by
      rw [← splice_act, hesymm, act_act_inv]
    rw [h1, hinv]
  have hZ : locZ (haarG SU2) B W (act (gaugeAct N) g σ) = locZ (haarG SU2) B W σ := by
    unfold locZ
    simp_rw [key]
    have := prod_map_act (N := N) (fun x => (g x)⁻¹)
    rw [← hesymm] at this
    rw [← integral_map (φ := e.symm) (f := fun ξ => W (splice B σ ξ)) e.symm.measurable.aemeasurable
      ((hW.meas.comp (measurable_splice_right B σ)).aestronglyMeasurable), this]
  have hf : Measurable (fun ξ => ENNReal.ofReal (W (splice B σ ξ) / locZ (haarG SU2) B W σ)) :=
    ((hW.meas.comp (measurable_splice_right B σ)).div_const _).ennreal_ofReal
  unfold locSpec
  simp_rw [key, hZ]
  rw [show (act (gaugeAct N) g) = ⇑e from he.symm, map_withDensity_equiv e π _ hf, show π.map e = π from prod_map_act g]
  rfl

/-- **Gauge covariance of the DLR box kernel** of the SU(2) Wilson measure: for every block `B` and every gauge
transformation `g` of the torus, `q_B(g·σ) = g_* q_B(σ)` as measures on all configurations. -/
theorem gaugeSpec_covariant (β : ℝ) (B : Finset (LatticeLink 4 N)) :
    SpecCovariant (gaugeAct N) (gaugeSpec (G := SU2) (d := 4) (N := N) 2 (fun x => Real.exp (β * x)) B) :=
  locSpec_covariant B (localWeight_plaqProd su2_hc' su2_hU' (posWeight_wilson' β) _)
    (fun g U => plaqProd_gauge _ _ g U)

end Cov

end ProofPhase.OneBox2
