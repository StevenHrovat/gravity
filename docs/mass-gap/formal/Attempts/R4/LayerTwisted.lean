/-
Round 4, attempt r4-layer, 2026-11-21. Released under Apache 2.0.

# The flux sector in a magnetically twisted box ('t Hooft's `m_z ∥ e_z` setting), and the U(n) instance (the photon test)

Note: `docs/mass-gap/weak-coupling/attempts/r4-layer/NOTE.md`, section 1.

The magnetic twist multiplies the spatial plaquettes of a set `S` (for 't Hooft's `m_z`: the `xy`-plaquettes at `(x, y) = (−1, −1)`,
all `z`) by a central element `w`. The twisted temporal-gauge kernel

  `K_β^{w,S}(U, V) = exp( β/2 Σ_p Re tr(w^{[p ∈ S]} U_p) + β/2 Σ_p Re tr(w^{[p ∈ S]} V_p) + β Σ_l Re tr(U_l V_l⁻¹) )`

is again bounded, measurable, non-negative and symmetric, and 't Hooft's centre transformation `Ω̂_{μ₀}` commutes with it for
**every** set `S` (each plaquette holonomy is `Ω̂`-invariant). So the electric-flux sector of the twisted box is a transfer-matrix
sector with `E_e ≥ 0` and flux correlators decaying like `e^{−E_e n}` (`twisted_fluxEnergy_nonneg`, `su2_twisted_fluxEnergy_nonneg`,
`su2_twisted_flux_correlator_decay`). `un_fluxEnergy_nonneg`: the same statement for U(n) with `z = −1` (U(1): the photon); it
holds there too, since it claims no gap.
-/

import Attempts.R4.LayerKernel

open MeasureTheory Finset AreaLaw.Concrete AreaLaw.Twist Positivity

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace Attempts.R4.Layer

variable {ds N : ℕ} [NeZero ds] [NeZero N]
variable {G : Type*} [Group G] {n : ℕ} [HasGaugeTrace G n]

/-- The magnetically twisted spatial Wilson sum `Σ_p Re tr(w^{[p ∈ S]} U_p)`. -/
def twSpatialAct (n : ℕ) [HasGaugeTrace G n] (w : G) (S : Finset (LatticePlaquette ds N)) (U : GaugeConnection G ds N) : ℝ :=
  ∑ p : LatticePlaquette ds N, gaugeReTr G n ((if p ∈ S then w else 1) * plaquetteHolonomy U p)

/-- **The Wilson transfer kernel of the magnetically twisted box** (temporal gauge). -/
def twKernel (n : ℕ) [HasGaugeTrace G n] (β : ℝ) (w : G) (S : Finset (LatticePlaquette ds N))
    (U V : GaugeConnection G ds N) : ℝ :=
  Real.exp (β / 2 * twSpatialAct n w S U + β / 2 * twSpatialAct n w S V + β * temporalAct n U V)

theorem twSpatialAct_centreFlip {z : G} (hz : ∀ g : G, Commute z g) (μ₀ : Fin ds) (w : G)
    (S : Finset (LatticePlaquette ds N)) (U : GaugeConnection G ds N) :
    twSpatialAct n w S (centreFlip z μ₀ U) = twSpatialAct n w S U := by
  unfold twSpatialAct
  exact Finset.sum_congr rfl fun p _ => by rw [plaquetteHolonomy_centreFlip hz]

theorem temporalAct_centreFlip {z : G} (hz : ∀ g : G, Commute z g) (μ₀ : Fin ds) (U V : GaugeConnection G ds N) :
    temporalAct n (centreFlip z μ₀ U) (centreFlip z μ₀ V) = temporalAct n U V := by
  unfold temporalAct centreFlip twistAt
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · rw [show z * U l * (z * V l)⁻¹ = z * (U l * (V l)⁻¹) * z⁻¹ by group, centre_conj hz]
  · rfl

/-- **`Ω̂` commutes with the twisted transfer operator**, for every magnetic insertion `(w, S)`. -/
theorem twKernel_centreFlip {z : G} (hz : ∀ g : G, Commute z g) (μ₀ : Fin ds) (β : ℝ) (w : G)
    (S : Finset (LatticePlaquette ds N)) (U V : GaugeConnection G ds N) :
    twKernel n β w S (centreFlip z μ₀ U) (centreFlip z μ₀ V) = twKernel n β w S U V := by
  unfold twKernel
  rw [twSpatialAct_centreFlip hz, twSpatialAct_centreFlip hz, temporalAct_centreFlip hz]

section Unitary

variable (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)
include hU

theorem twKernel_symm (β : ℝ) (w : G) (S : Finset (LatticePlaquette ds N)) (U V : GaugeConnection G ds N) :
    twKernel n β w S U V = twKernel n β w S V U := by
  unfold twKernel; rw [temporalAct_symm hU U V]; ring_nf

theorem abs_twSpatialAct_le (w : G) (S : Finset (LatticePlaquette ds N)) (U : GaugeConnection G ds N) :
    |twSpatialAct n w S U| ≤ Fintype.card (LatticePlaquette ds N) * n := by
  unfold twSpatialAct
  calc |∑ p : LatticePlaquette ds N, gaugeReTr G n ((if p ∈ S then w else 1) * plaquetteHolonomy U p)|
        ≤ ∑ p : LatticePlaquette ds N, |gaugeReTr G n ((if p ∈ S then w else 1) * plaquetteHolonomy U p)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : LatticePlaquette ds N, (n : ℝ) := Finset.sum_le_sum fun p _ => abs_re_trace_le_of_unitary (hU _)
    _ = _ := by simp

theorem twKernel_le (β : ℝ) (w : G) (S : Finset (LatticePlaquette ds N)) (U V : GaugeConnection G ds N) :
    twKernel n β w S U V ≤ kernelBound ds N n β := by
  unfold twKernel kernelBound
  apply Real.exp_le_exp.mpr
  have h1 : β / 2 * twSpatialAct n w S U ≤ |β / 2| * (Fintype.card (LatticePlaquette ds N) * n) :=
    mul_le_abs_mul (abs_twSpatialAct_le hU w S U)
  have h2 : β / 2 * twSpatialAct n w S V ≤ |β / 2| * (Fintype.card (LatticePlaquette ds N) * n) :=
    mul_le_abs_mul (abs_twSpatialAct_le hU w S V)
  have h3 : β * temporalAct n U V ≤ |β| * (Fintype.card (LatticeLink ds N) * n) := mul_le_abs_mul (abs_temporalAct_le hU U V)
  have hb : |β / 2| = |β| / 2 := by rw [abs_div]; norm_num
  rw [hb] at h1 h2
  nlinarith

end Unitary

section Measurable

variable [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem measurable_hol (p : LatticePlaquette ds N) :
    Measurable (fun U : GaugeConnection G ds N => plaquetteHolonomy U p) := by
  show Measurable fun U : GaugeConnection G ds N => U (p.boundaryLinks 0) * U (p.boundaryLinks 1) *
    (U (p.boundaryLinks 2))⁻¹ * (U (p.boundaryLinks 3))⁻¹
  exact (((measurable_pi_apply (p.boundaryLinks 0)).mul (measurable_pi_apply (p.boundaryLinks 1))).mul
    (measurable_pi_apply (p.boundaryLinks 2)).inv).mul (measurable_pi_apply (p.boundaryLinks 3)).inv

theorem measurable_twSpatialAct (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (w : G)
    (S : Finset (LatticePlaquette ds N)) : Measurable (twSpatialAct (G := G) (ds := ds) (N := N) n w S) :=
  Finset.measurable_sum _ fun p _ => (continuous_gaugeReTr hc).measurable.comp (measurable_const.mul (measurable_hol p))

theorem measurable_twKernel (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (β : ℝ) (w : G)
    (S : Finset (LatticePlaquette ds N)) :
    Measurable (Function.uncurry (twKernel (G := G) (ds := ds) (N := N) n β w S)) := by
  have hs := measurable_twSpatialAct (ds := ds) (N := N) hc w S
  have ht : Measurable (fun q : GaugeConnection G ds N × GaugeConnection G ds N => temporalAct n q.1 q.2) := by
    unfold temporalAct
    exact Finset.measurable_sum _ fun l _ => (continuous_gaugeReTr hc).measurable.comp
      (((measurable_pi_apply l).comp measurable_fst).mul ((measurable_pi_apply l).comp measurable_snd).inv)
  show Measurable fun q : GaugeConnection G ds N × GaugeConnection G ds N =>
    Real.exp (β / 2 * twSpatialAct n w S q.1 + β / 2 * twSpatialAct n w S q.2 + β * temporalAct n q.1 q.2)
  exact Real.measurable_exp.comp ((((hs.comp measurable_fst).const_mul _).add ((hs.comp measurable_snd).const_mul _)).add
    (ht.const_mul _))

variable [HasHaarProbability G]

/-- The twisted Wilson transfer kernel as a `TKernel`. -/
def twTKernel (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ) (β : ℝ) (w : G)
    (S : Finset (LatticePlaquette ds N)) : TKernel (GaugeConnection G ds N) where
  K := twKernel n β w S
  meas := measurable_twKernel hc β w S
  nonneg := fun _ _ => (Real.exp_pos _).le
  bound := kernelBound ds N n β
  le_bound := twKernel_le hU β w S

/-- 't Hooft's centre transformation as a `CentreSym` of the twisted transfer operator. -/
def twCentre (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ) {z : G}
    (hz : ∀ g : G, Commute z g) (hzz : z * z = 1) (hzm : MeasurePreserving (z * ·) (haarG G) (haarG G)) (β : ℝ) (w : G)
    (S : Finset (LatticePlaquette ds N)) (μ₀ : Fin ds) :
    CentreSym (productHaar G ds N) (twTKernel (ds := ds) (N := N) hc hU β w S) where
  σ := centreFlip z μ₀
  meas := (measurePreserving_twistAt z hzm (rowSet ds N μ₀)).measurable
  invol := centreFlip_involutive hzz μ₀
  pres := measurePreserving_twistAt z hzm (rowSet ds N μ₀)
  kinv := twKernel_centreFlip hz μ₀ β w S

/-- **The electric flux energy of the magnetically twisted box is non-negative** (every compact group with central `z`, `z² = 1`;
    any magnetic insertion `(w, S)`; any class `Q` closed under `|·|`). -/
theorem twisted_fluxEnergy_nonneg (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ) {z : G}
    (hz : ∀ g : G, Commute z g) (hzz : z * z = 1) (hzm : MeasurePreserving (z * ·) (haarG G) (haarG G)) (β : ℝ) (w : G)
    (S : Finset (LatticePlaquette ds N)) (μ₀ : Fin ds) (Q : (GaugeConnection G ds N → ℝ) → Prop)
    (hQ : ∀ ψ, Q ψ → Q (fun x => |ψ x|)) : 0 ≤ fluxEnergy (twCentre hc hU hz hzz hzm β w S μ₀) Q :=
  fluxEnergy_nonneg _ Q hQ

end Measurable

/-! ## SU(2) in the twisted box -/

/-- 't Hooft's `m ∥ e` box for SU(2): magnetic insertion `(−1, S)`, electric flux along `μ₀`. -/
abbrev su2TwCentre (β : ℝ) (S : Finset (LatticePlaquette ds N)) (μ₀ : Fin ds) :=
  twCentre (ds := ds) (N := N) su2_hc su2_hU negOneSU2_central negOneSU2_sq su2_hzm β negOneSU2 S μ₀

/-- **SU(2) Yang–Mills in a magnetically twisted box: `E_e ≥ 0` for the electric flux sector.** -/
theorem su2_twisted_fluxEnergy_nonneg (β : ℝ) (S : Finset (LatticePlaquette ds N)) (μ₀ : Fin ds)
    (Q : (GaugeConnection SU2 ds N → ℝ) → Prop) (hQ : ∀ ψ, Q ψ → Q (fun x => |ψ x|)) :
    0 ≤ fluxEnergy (su2TwCentre (N := N) β S μ₀) Q :=
  fluxEnergy_nonneg _ Q hQ

/-- **SU(2) in a magnetically twisted box: flux correlators decay like `e^{−E_e n}`** relative to the vacuum sector. -/
theorem su2_twisted_flux_correlator_decay (β : ℝ) (S : Finset (LatticePlaquette ds N)) (μ₀ : Fin ds)
    (Q : (GaugeConnection SU2 ds N → ℝ) → Prop) (hQ : ∀ ψ, Q ψ → Q (fun x => |ψ x|))
    (hQT : ∀ ψ, BM ψ → Q ψ →
      Q (top (productHaar SU2 ds N) (twTKernel (ds := ds) (N := N) su2_hc su2_hU β negOneSU2 S) ψ))
    {φ ψ : GaugeConnection SU2 ds N → ℝ} (hφ : BM φ) (hψ : Sec (su2TwCentre (N := N) β S μ₀) Q (-1) ψ) (m : ℕ) :
    (∫ x, φ x * (top (productHaar SU2 ds N) (twTKernel (ds := ds) (N := N) su2_hc su2_hU β negOneSU2 S))^[m] ψ x
        ∂(productHaar SU2 ds N)) ^ 2 ≤
      ((lamVac (su2TwCentre (N := N) β S μ₀) Q) ^ m *
          Real.exp (-(fluxEnergy (su2TwCentre (N := N) β S μ₀) Q * m))) ^ 2 *
        nrm (productHaar SU2 ds N) φ * nrm (productHaar SU2 ds N) ψ :=
  flux_correlator_decay _ Q hQ hQT hφ hψ m

/-! ## U(n), U(1) included (the photon test) -/

theorem negOneUn_central (k : ℕ) : ∀ g : Un k, Commute (negOneUn k) g :=
  fun g => Subtype.ext (show (-1 : Matrix (Fin k) (Fin k) ℂ) * g.val = g.val * -1 by simp)

theorem negOneUn_sq (k : ℕ) : negOneUn k * negOneUn k = 1 :=
  Subtype.ext (show (-1 : Matrix (Fin k) (Fin k) ℂ) * -1 = 1 by simp)

/-- **U(n), in particular U(1): the flux sector exists and `E_e ≥ 0`.** Nothing here gives a gap, as the photon test requires. -/
theorem un_fluxEnergy_nonneg (k : ℕ) (β : ℝ) (μ₀ : Fin ds) (Q : (GaugeConnection (Un k) ds N → ℝ) → Prop)
    (hQ : ∀ ψ, Q ψ → Q (fun x => |ψ x|)) :
    0 ≤ fluxEnergy (wilsonCentre (ds := ds) (N := N) (n := k) continuous_subtype_val (fun g => g.2)
      (negOneUn_central k) (negOneUn_sq k) (measurePreserving_mul_left _ _) β μ₀) Q :=
  fluxEnergy_nonneg _ Q hQ

end Attempts.R4.Layer
