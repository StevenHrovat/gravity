/-
Proof phase, generalisation phase 1b: gauge covariance of the Wilson box kernel over any gauge group and dimension
(2026-11-24). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 1b.
-/

import ProofPhase.General.Fine
import ProofPhase.OneBox2.Wilson

/-!
# The Wilson box kernel is gauge covariant, over any gauge group

`OneBox2/Wilson` for any `Gr` of the package in dimension `d` (representation dimension `nr`): the plaquette weight is
gauge invariant (`xp_gauge`, from `gaugeReTr` being a class function), the product Haar measure is invariant under the
link-by-link gauge action (`prod_map_act`, which needs left **and right** invariance of the Haar measure; right
invariance is derived from left and inversion invariance, `haar_map_mul_right`), and the DLR box kernel of the Wilson
measure is gauge covariant (`gaugeSpec_covariant`). The measurable-kernel part of the old file (`measurable_locSpec`) is
group-free and is reused.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity

open ProofPhase.OneBox (act ActInv SpecCovariant measurable_act splice_act)
open ProofPhase.OneBox2 (measurable_locSpec map_withDensity_equiv)

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

section Wilson

variable {Gr : Type*} [Group Gr] [TopologicalSpace Gr] [MeasurableSpace Gr] [HasHaarProbability Gr]
  (nr : ℕ) [HasGaugeTrace Gr nr] [GaugeGroupBase Gr] [GaugeRep Gr nr] {d : ℕ} [NeZero d]

/-- **Right invariance of the Haar measure**, from left and inversion invariance. -/
theorem haar_map_mul_right (c : Gr) : (haarG Gr).map (fun u => u * c) = haarG Gr := by
  have hi : Measure.map (Inv.inv : Gr → Gr) (haarG Gr) = haarG Gr := Measure.inv_eq_self (haarG Gr)
  have h1 : (fun u : Gr => u * c) = (Inv.inv : Gr → Gr) ∘ (fun u => c⁻¹ * u) ∘ (Inv.inv : Gr → Gr) := by
    funext u; simp
  rw [h1, ← Measure.map_map (measurable_inv) ((measurable_const_mul c⁻¹).comp measurable_inv),
    ← Measure.map_map (measurable_const_mul c⁻¹) measurable_inv, hi,
    (measurePreserving_mul_left (haarG Gr) c⁻¹).map_eq, hi]

section N

variable {N : ℕ} [NeZero N]

theorem measurable_gaugeSpec (β : ℝ) (B : Finset (LatticeLink d N)) :
    Measurable (gaugeSpec (G := Gr) (d := d) (N := N) nr (fun x => Real.exp (β * x)) B) :=
  measurable_locSpec (localWeight_plaqProd GaugeRep.continuous_rep GaugeRep.unitary_rep (posWeight_exp nr β) _)

theorem plaquetteHolonomy_gauge (g : GaugeTransform Gr d N) (U : GaugeConnection Gr d N)
    (p : LatticePlaquette d N) :
    plaquetteHolonomy (gaugeTransformConnection g U) p = g p.site * plaquetteHolonomy U p * (g p.site)⁻¹ := by
  have hc := siteShift_comm d N p.site p.dir1 p.dir2 (ne_of_lt p.h_lt)
  simp only [plaquetteHolonomy, gaugeTransformConnection, LatticePlaquette.boundaryLinks, LatticeLink.target, hc]
  group

theorem gaugeTrace_conj (a b : Gr) : gaugeTrace Gr nr (a * b * a⁻¹) = gaugeTrace Gr nr b := by
  unfold gaugeTrace
  rw [map_mul, map_mul, Matrix.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem xp_gauge (g : GaugeTransform Gr d N) (U : GaugeConnection Gr d N) (p : LatticePlaquette d N) :
    xp nr p (gaugeTransformConnection g U) = xp nr p U := by
  unfold xp gaugeReTr
  rw [plaquetteHolonomy_gauge, gaugeTrace_conj]

theorem plaqProd_gauge (φ : ℝ → ℝ) (s : Finset (LatticePlaquette d N)) (g : GaugeTransform Gr d N)
    (U : GaugeConnection Gr d N) :
    plaqProd (G := Gr) nr φ s (gaugeTransformConnection g U) = plaqProd nr φ s U := by
  unfold plaqProd
  exact prod_congr rfl fun p _ => by rw [xp_gauge]

theorem act_act_inv (g : GaugeTransform Gr d N) (U : GaugeConnection Gr d N) :
    act (gaugeAct N) g (act (gaugeAct N) (fun x => (g x)⁻¹) U) = U := by
  funext l; simp only [act, gaugeAct]; group

theorem act_inv_act (g : GaugeTransform Gr d N) (U : GaugeConnection Gr d N) :
    act (gaugeAct N) (fun x => (g x)⁻¹) (act (gaugeAct N) g U) = U := by
  funext l; simp only [act, gaugeAct]; group

def gaugeEquiv (g : GaugeTransform Gr d N) : GaugeConnection Gr d N ≃ᵐ GaugeConnection Gr d N where
  toFun := act (gaugeAct N) g
  invFun := act (gaugeAct N) (fun x => (g x)⁻¹)
  left_inv U := act_inv_act g U
  right_inv U := act_act_inv g U
  measurable_toFun := measurable_act (measurable_gaugeAct N) g
  measurable_invFun := measurable_act (a := gaugeAct N) (measurable_gaugeAct N) (fun x => (g x)⁻¹)

theorem haar_map_conj (a c : Gr) : (haarG Gr).map (fun u => a * u * c) = haarG Gr := by
  have h1 : (fun u : Gr => a * u * c) = (fun u => u * c) ∘ (fun u => a * u) := rfl
  rw [h1, ← Measure.map_map (measurable_mul_const c) (measurable_const_mul a),
    (measurePreserving_mul_left (haarG Gr) a).map_eq, haar_map_mul_right c]

theorem prod_map_act (g : GaugeTransform Gr d N) :
    (prodMeasure (ι := LatticeLink d N) (haarG Gr)).map (act (gaugeAct N) g) =
      prodMeasure (haarG Gr) := by
  have h := Measure.pi_map_pi (μ := fun _ : LatticeLink d N => haarG Gr)
    (f := fun l u => gaugeAct N g l u) (fun l => (measurable_gaugeAct N g l).aemeasurable)
  refine h.trans ?_
  unfold prodMeasure
  congr 1
  funext l
  exact haar_map_conj _ _

theorem locSpec_covariant (B : Finset (LatticeLink d N)) {W : GaugeConnection Gr d N → ℝ} (hW : LocalWeight W)
    (hinv : ∀ (g : GaugeTransform Gr d N) U, W (act (gaugeAct N) g U) = W U) :
    SpecCovariant (gaugeAct N) (locSpec (haarG Gr) B W) := by
  intro g σ
  set π := prodMeasure (ι := LatticeLink d N) (haarG Gr)
  set e := gaugeEquiv g
  have he : ⇑e = act (gaugeAct N) g := rfl
  have hesymm : ⇑e.symm = act (gaugeAct N) (fun x => (g x)⁻¹) := rfl
  have key : ∀ ξ, W (splice B (act (gaugeAct N) g σ) ξ) = W (splice B σ (e.symm ξ)) := by
    intro ξ
    have h1 : splice B (act (gaugeAct N) g σ) ξ = act (gaugeAct N) g (splice B σ (e.symm ξ)) := by
      rw [← splice_act, hesymm, act_act_inv]
    rw [h1, hinv]
  have hZ : locZ (haarG Gr) B W (act (gaugeAct N) g σ) = locZ (haarG Gr) B W σ := by
    unfold locZ
    simp_rw [key]
    have := prod_map_act (N := N) (fun x => (g x)⁻¹)
    rw [← hesymm] at this
    rw [← integral_map (φ := e.symm) (f := fun ξ => W (splice B σ ξ)) e.symm.measurable.aemeasurable
      ((hW.meas.comp (measurable_splice_right B σ)).aestronglyMeasurable), this]
  have hf : Measurable (fun ξ => ENNReal.ofReal (W (splice B σ ξ) / locZ (haarG Gr) B W σ)) :=
    ((hW.meas.comp (measurable_splice_right B σ)).div_const _).ennreal_ofReal
  unfold locSpec
  simp_rw [key, hZ]
  rw [show (act (gaugeAct N) g) = ⇑e from he.symm, map_withDensity_equiv e π _ hf, show π.map e = π from prod_map_act g]
  rfl

theorem gaugeSpec_covariant (β : ℝ) (B : Finset (LatticeLink d N)) :
    SpecCovariant (gaugeAct N) (gaugeSpec (G := Gr) (d := d) (N := N) nr (fun x => Real.exp (β * x)) B) :=
  locSpec_covariant B (localWeight_plaqProd GaugeRep.continuous_rep GaugeRep.unitary_rep (posWeight_exp nr β) _)
    (fun g U => plaqProd_gauge nr _ _ g U)

end N

end Wilson


/-! ## The SU(2), `d = 4` instances -/

section Instance

variable {N : ℕ} [NeZero N]

/-- `ProofPhase.OneBox2.gaugeSpec_covariant` from the generic theorem. -/
theorem gaugeSpec_covariant_su2 (β : ℝ) (B : Finset (LatticeLink 4 N)) :
    ProofPhase.OneBox.SpecCovariant (ProofPhase.OneBox.gaugeAct N)
      (gaugeSpec (G := SU2) (d := 4) (N := N) 2 (fun x => Real.exp (β * x)) B) :=
  gaugeSpec_covariant (Gr := SU2) 2 (d := 4) β B

/-- `ProofPhase.OneBox2.prod_map_act` from the generic theorem. -/
theorem prod_map_act_su2 (g : GaugeTransform SU2 4 N) :
    (prodMeasure (ι := LatticeLink 4 N) (haarG SU2)).map (act (ProofPhase.OneBox.gaugeAct N) g) =
      prodMeasure (haarG SU2) :=
  prod_map_act (Gr := SU2) (d := 4) g

/-- `ProofPhase.OneBox2.xp_gauge` from the generic theorem. -/
theorem xp_gauge_su2 (g : GaugeTransform SU2 4 N) (U : GaugeConnection SU2 4 N) (p : LatticePlaquette 4 N) :
    xp 2 p (gaugeTransformConnection g U) = xp 2 p U :=
  xp_gauge (Gr := SU2) 2 (d := 4) g U p

/-- `ProofPhase.OneBox2.measurable_gaugeSpec` from the generic theorem. -/
theorem measurable_gaugeSpec_su2 (β : ℝ) (B : Finset (LatticeLink 4 N)) :
    Measurable (gaugeSpec (G := SU2) (d := 4) (N := N) 2 (fun x => Real.exp (β * x)) B) :=
  measurable_gaugeSpec (Gr := SU2) 2 (d := 4) β B

example : @ProofPhase.OneBox2.gaugeSpec_covariant = @gaugeSpec_covariant_su2 := rfl
example : @ProofPhase.OneBox2.prod_map_act = @prod_map_act_su2 := rfl
example : @ProofPhase.OneBox2.xp_gauge = @xp_gauge_su2 := rfl
example : @ProofPhase.OneBox2.measurable_gaugeSpec = @measurable_gaugeSpec_su2 := rfl

end Instance

end ProofPhase.General
