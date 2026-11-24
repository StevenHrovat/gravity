/-
Round 4, attempt r4-layer, 2026-11-21. Released under Apache 2.0.

# The Wilson transfer kernel in temporal gauge, its centre symmetry, and the flux sector of SU(2)

Note: `docs/mass-gap/weak-coupling/attempts/r4-layer/NOTE.md`, section 1.

The spatial slice is the periodic lattice `(ℤ/Nℤ)^ds` (`ds = 3` for 4D Yang–Mills); a slice configuration is a gauge connection
`U : LatticeLink ds N → G`. In temporal gauge the Wilson weight `∏_p exp(β Re tr U_p)` of the `(ds+1)`-dimensional lattice is a
product of transfer kernels between consecutive slices `U` (time `t`) and `V` (time `t + 1`):

  `K_β(U, V) = exp( β/2 Σ_{p spatial} Re tr U_p + β/2 Σ_p Re tr V_p + β Σ_{l} Re tr(U_l V_l⁻¹) )`,

the last sum being the temporal plaquettes (their holonomy in temporal gauge is `V_l U_l⁻¹`, whose real trace equals that of
`U_l V_l⁻¹` for a unitary representation). 't Hooft's centre transformation `Ω̂` multiplies the `μ₀`-links of the last row
`x_{μ₀} = −1` by a central `z` (`centreFlip`); it is the twisted gauge transformation whose eigenvalues are the electric flux `e_{μ₀}`.

Proved, for every group with a unitary representation, continuous, and a central `z` with `z² = 1` preserving the Haar measure:
* `wilsonKernel_nonneg`, `wilsonKernel_symm`, `wilsonKernel_le`, `measurable_wilsonKernel`: the kernel is a bounded, measurable,
  non-negative, symmetric kernel.
* `xp_centreFlip`, `wilsonKernel_centreFlip`: `Ω̂` leaves every spatial plaquette and every temporal plaquette invariant, so it
  commutes with the transfer operator.
* `wilsonTKernel`, `wilsonCentre`: the data of `LayerSector.lean` (A).
* `wilson_fluxEnergy_nonneg`, `wilson_flux_correlator_decay`: the flux sector of the Wilson transfer operator has `E_e ≥ 0` and its
  correlators decay like `e^{−E_e n}` relative to the vacuum sector; `su2_fluxEnergy_nonneg`, `su2_flux_correlator_decay`: the same
  for G = SU(2), `z = −1`.

Stated gap (standard, not formalised): that `K_β` reproduces the 4D Wilson partition function in temporal gauge, `Z = tr(P_G Tⁿ)` with
`P_G` the projection on gauge-invariant states (Gauss law), and `Z_tw = tr(Ω̂ P_G Tⁿ)`. The gauge-invariant states can be taken as the
class `Q` of `LayerSector.lean` (it is closed under `|·|`; that `T` preserves it is the gauge invariance of `K_β` and of the Haar
measure, standard, not formalised here).
-/

import Attempts.R4.LayerSector
import Positivity
import AreaLaw.TwistVanish

open MeasureTheory Finset AreaLaw.Concrete AreaLaw.Twist Positivity

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace Attempts.R4.Layer

variable {ds N : ℕ} [NeZero ds] [NeZero N]
variable {G : Type*} [Group G] {n : ℕ} [HasGaugeTrace G n]

/-- The spatial Wilson sum `Σ_p Re tr U_p` of one slice. -/
def spatialAct (n : ℕ) [HasGaugeTrace G n] (U : GaugeConnection G ds N) : ℝ :=
  ∑ p : LatticePlaquette ds N, xp n p U

/-- The temporal Wilson sum `Σ_l Re tr(U_l V_l⁻¹)` between two slices in temporal gauge. -/
def temporalAct (n : ℕ) [HasGaugeTrace G n] (U V : GaugeConnection G ds N) : ℝ :=
  ∑ l : LatticeLink ds N, gaugeReTr G n (U l * (V l)⁻¹)

/-- **The Wilson transfer kernel in temporal gauge.** -/
def wilsonKernel (n : ℕ) [HasGaugeTrace G n] (β : ℝ) (U V : GaugeConnection G ds N) : ℝ :=
  Real.exp (β / 2 * spatialAct n U + β / 2 * spatialAct n V + β * temporalAct n U V)

theorem wilsonKernel_nonneg (β : ℝ) (U V : GaugeConnection G ds N) : 0 ≤ wilsonKernel n β U V :=
  (Real.exp_pos _).le

theorem mul_le_abs_mul {β a A : ℝ} (h : |a| ≤ A) : β * a ≤ |β| * A :=
  (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg _))

section Unitary

variable (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)
include hU

theorem temporalAct_symm (U V : GaugeConnection G ds N) : temporalAct n U V = temporalAct n V U := by
  unfold temporalAct
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← gaugeReTr_inv_of_unitary hU (U l * (V l)⁻¹), mul_inv_rev, inv_inv]

/-- The kernel is symmetric. -/
theorem wilsonKernel_symm (β : ℝ) (U V : GaugeConnection G ds N) : wilsonKernel n β U V = wilsonKernel n β V U := by
  unfold wilsonKernel; rw [temporalAct_symm hU U V]; ring_nf

theorem abs_spatialAct_le (U : GaugeConnection G ds N) :
    |spatialAct n U| ≤ Fintype.card (LatticePlaquette ds N) * n := by
  unfold spatialAct
  calc |∑ p : LatticePlaquette ds N, xp n p U| ≤ ∑ p : LatticePlaquette ds N, |xp n p U| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : LatticePlaquette ds N, (n : ℝ) := Finset.sum_le_sum fun p _ => abs_re_trace_le_of_unitary (hU _)
    _ = _ := by simp

theorem abs_temporalAct_le (U V : GaugeConnection G ds N) :
    |temporalAct n U V| ≤ Fintype.card (LatticeLink ds N) * n := by
  unfold temporalAct
  calc |∑ l : LatticeLink ds N, gaugeReTr G n (U l * (V l)⁻¹)| ≤ ∑ l : LatticeLink ds N, |gaugeReTr G n (U l * (V l)⁻¹)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : LatticeLink ds N, (n : ℝ) := Finset.sum_le_sum fun l _ => abs_re_trace_le_of_unitary (hU _)
    _ = _ := by simp

/-- The kernel bound `K_max = exp(|β| (#plaquettes + #links) n)`. -/
def kernelBound (ds N n : ℕ) [NeZero N] (β : ℝ) : ℝ :=
  Real.exp (|β| * (Fintype.card (LatticePlaquette ds N) * n + Fintype.card (LatticeLink ds N) * n))

omit hU in
theorem kernelBound_def (β : ℝ) : kernelBound ds N n β =
    Real.exp (|β| * (Fintype.card (LatticePlaquette ds N) * n + Fintype.card (LatticeLink ds N) * n)) := rfl

theorem wilsonKernel_le (β : ℝ) (U V : GaugeConnection G ds N) : wilsonKernel n β U V ≤ kernelBound ds N n β := by
  unfold wilsonKernel kernelBound
  apply Real.exp_le_exp.mpr
  have h1 : β / 2 * spatialAct n U ≤ |β / 2| * (Fintype.card (LatticePlaquette ds N) * n) :=
    mul_le_abs_mul (abs_spatialAct_le hU U)
  have h2 : β / 2 * spatialAct n V ≤ |β / 2| * (Fintype.card (LatticePlaquette ds N) * n) :=
    mul_le_abs_mul (abs_spatialAct_le hU V)
  have h3 : β * temporalAct n U V ≤ |β| * (Fintype.card (LatticeLink ds N) * n) := mul_le_abs_mul (abs_temporalAct_le hU U V)
  have hb : |β / 2| = |β| / 2 := by rw [abs_div]; norm_num
  rw [hb] at h1 h2
  nlinarith

end Unitary

section Measurable

variable [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem measurable_spatialAct (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n))) :
    Measurable (spatialAct (G := G) (ds := ds) (N := N) n) :=
  Finset.measurable_sum _ fun p _ => measurable_xp hc p

/-- The kernel is jointly measurable. -/
theorem measurable_wilsonKernel (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (β : ℝ) :
    Measurable (Function.uncurry (wilsonKernel (G := G) (ds := ds) (N := N) n β)) := by
  have hs := measurable_spatialAct (ds := ds) (N := N) hc
  have ht : Measurable (fun q : GaugeConnection G ds N × GaugeConnection G ds N => temporalAct n q.1 q.2) := by
    unfold temporalAct
    exact Finset.measurable_sum _ fun l _ => (continuous_gaugeReTr hc).measurable.comp
      (((measurable_pi_apply l).comp measurable_fst).mul ((measurable_pi_apply l).comp measurable_snd).inv)
  show Measurable fun q : GaugeConnection G ds N × GaugeConnection G ds N =>
    Real.exp (β / 2 * spatialAct n q.1 + β / 2 * spatialAct n q.2 + β * temporalAct n q.1 q.2)
  exact Real.measurable_exp.comp ((((hs.comp measurable_fst).const_mul _).add ((hs.comp measurable_snd).const_mul _)).add
    (ht.const_mul _))

end Measurable

/-! ## The centre transformation `Ω̂` -/

/-- The `μ₀`-links of the last row `x_{μ₀} = −1`. -/
def rowSet (ds N : ℕ) [NeZero N] (μ₀ : Fin ds) : Finset (LatticeLink ds N) :=
  univ.filter fun l => l.dir = μ₀ ∧ l.site μ₀ = -1

/-- **'t Hooft's centre transformation** `Ω̂_z`: multiply the `μ₀`-links of the last row by `z`. This is the gauge transformation
    that is periodic only up to the centre element, `g(x + N e_{μ₀}) = z g(x)` (take `g = 1` on the fundamental domain: only the
    links crossing from `x_{μ₀} = −1` to `0` change). On Gauss-law states (invariant under all periodic gauge transformations, the
    class `Q` of `LayerSector.lean`) its eigenvalue `(−1)^{e_{μ₀}}` is the electric flux: the flux sectors are **sectors of
    Gauss-law states, labelled by their response to a gauge transformation twisted by the centre** ('t Hooft's definition). -/
def centreFlip (z : G) (μ₀ : Fin ds) (U : GaugeConnection G ds N) : GaugeConnection G ds N :=
  twistAt z (rowSet ds N μ₀) U

theorem centre_conj {z : G} (hz : ∀ g : G, Commute z g) (w : G) : z * w * z⁻¹ = w := by
  rw [(hz w).eq, mul_inv_cancel_right]

theorem hol_central {z : G} (hz : ∀ g : G, Commute z g) (a b c e : G) (s t : Prop) [Decidable s] [Decidable t] :
    (if s then z * a else a) * (if t then z * b else b) * (if s then z * c else c)⁻¹ * (if t then z * e else e)⁻¹ =
      a * b * c⁻¹ * e⁻¹ := by
  have hc := centre_conj hz
  split_ifs
  · calc z * a * (z * b) * (z * c)⁻¹ * (z * e)⁻¹ = z * (a * (z * (b * c⁻¹) * z⁻¹) * e⁻¹) * z⁻¹ := by group
      _ = a * b * c⁻¹ * e⁻¹ := by rw [hc, hc]; group
  · calc z * a * b * (z * c)⁻¹ * e⁻¹ = z * (a * b * c⁻¹) * z⁻¹ * e⁻¹ := by group
      _ = a * b * c⁻¹ * e⁻¹ := by rw [hc]
  · calc a * (z * b) * c⁻¹ * (z * e)⁻¹ = a * (z * (b * c⁻¹ * e⁻¹) * z⁻¹) := by group
      _ = a * b * c⁻¹ * e⁻¹ := by rw [hc]; group
  · rfl

theorem mem_rowSet {μ₀ : Fin ds} {l : LatticeLink ds N} : l ∈ rowSet ds N μ₀ ↔ l.dir = μ₀ ∧ l.site μ₀ = -1 := by
  simp [rowSet]

/-- `Ω̂` leaves every spatial plaquette invariant: the two `μ₀`-links of a plaquette lie in the same row. -/
theorem plaquetteHolonomy_centreFlip {z : G} (hz : ∀ g : G, Commute z g) (μ₀ : Fin ds) (U : GaugeConnection G ds N)
    (p : LatticePlaquette ds N) : plaquetteHolonomy (centreFlip z μ₀ U) p = plaquetteHolonomy U p := by
  have h12 := p.h_lt
  have e02 : p.boundaryLinks 0 ∈ rowSet ds N μ₀ ↔ p.boundaryLinks 2 ∈ rowSet ds N μ₀ := by
    simp only [mem_rowSet, LatticePlaquette.boundaryLinks]
    constructor
    · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩
      rw [siteShift, Function.update_of_ne (by rintro rfl; exact (lt_irrefl _ (h1 ▸ h12)))]; exact h2
    · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩
      rwa [siteShift, Function.update_of_ne (by rintro rfl; exact (lt_irrefl _ (h1 ▸ h12)))] at h2
  have e13 : p.boundaryLinks 1 ∈ rowSet ds N μ₀ ↔ p.boundaryLinks 3 ∈ rowSet ds N μ₀ := by
    simp only [mem_rowSet, LatticePlaquette.boundaryLinks]
    constructor
    · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩
      rwa [siteShift, Function.update_of_ne (by rintro rfl; exact (lt_irrefl _ (h1 ▸ h12)))] at h2
    · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩
      rw [siteShift, Function.update_of_ne (by rintro rfl; exact (lt_irrefl _ (h1 ▸ h12)))]; exact h2
  unfold plaquetteHolonomy centreFlip twistAt
  simp only
  rw [show (if p.boundaryLinks 2 ∈ rowSet ds N μ₀ then z * U (p.boundaryLinks 2) else U (p.boundaryLinks 2)) =
      (if p.boundaryLinks 0 ∈ rowSet ds N μ₀ then z * U (p.boundaryLinks 2) else U (p.boundaryLinks 2)) by
        simp only [e02],
    show (if p.boundaryLinks 3 ∈ rowSet ds N μ₀ then z * U (p.boundaryLinks 3) else U (p.boundaryLinks 3)) =
      (if p.boundaryLinks 1 ∈ rowSet ds N μ₀ then z * U (p.boundaryLinks 3) else U (p.boundaryLinks 3)) by
        simp only [e13]]
  exact hol_central hz _ _ _ _ _ _

theorem xp_centreFlip {z : G} (hz : ∀ g : G, Commute z g) (μ₀ : Fin ds) (U : GaugeConnection G ds N)
    (p : LatticePlaquette ds N) : xp n p (centreFlip z μ₀ U) = xp n p U := by
  unfold xp; rw [plaquetteHolonomy_centreFlip hz]

/-- **`Ω̂` commutes with the transfer operator:** `K_β(Ω̂U, Ω̂V) = K_β(U, V)`. -/
theorem wilsonKernel_centreFlip {z : G} (hz : ∀ g : G, Commute z g) (μ₀ : Fin ds) (β : ℝ)
    (U V : GaugeConnection G ds N) :
    wilsonKernel n β (centreFlip z μ₀ U) (centreFlip z μ₀ V) = wilsonKernel n β U V := by
  have hs : ∀ W : GaugeConnection G ds N, spatialAct n (centreFlip z μ₀ W) = spatialAct n W := fun W => by
    unfold spatialAct; exact Finset.sum_congr rfl fun p _ => xp_centreFlip hz μ₀ W p
  have ht : temporalAct n (centreFlip z μ₀ U) (centreFlip z μ₀ V) = temporalAct n U V := by
    unfold temporalAct centreFlip twistAt
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [show z * U l * (z * V l)⁻¹ = z * (U l * (V l)⁻¹) * z⁻¹ by group, centre_conj hz]
    · rfl
  unfold wilsonKernel; rw [hs, hs, ht]

theorem centreFlip_involutive {z : G} (hzz : z * z = 1) (μ₀ : Fin ds) :
    Function.Involutive (centreFlip (ds := ds) (N := N) z μ₀) := by
  intro U; funext l
  unfold centreFlip twistAt
  split_ifs <;> simp [← mul_assoc, hzz]

/-! ## The flux sector of the Wilson transfer operator -/

section Flux

variable [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [HasHaarProbability G]
variable (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)

/-- The Wilson transfer kernel as a `TKernel`. -/
def wilsonTKernel (β : ℝ) : TKernel (GaugeConnection G ds N) where
  K := wilsonKernel n β
  meas := measurable_wilsonKernel hc β
  nonneg := wilsonKernel_nonneg β
  bound := kernelBound ds N n β
  le_bound := wilsonKernel_le hU β

/-- 't Hooft's centre transformation as a `CentreSym` of the Wilson transfer operator. -/
def wilsonCentre {z : G} (hz : ∀ g : G, Commute z g) (hzz : z * z = 1)
    (hzm : MeasurePreserving (z * ·) (haarG G) (haarG G)) (β : ℝ) (μ₀ : Fin ds) : CentreSym (productHaar G ds N) (wilsonTKernel (ds := ds) (N := N) hc hU β) where
  σ := centreFlip z μ₀
  meas := (measurePreserving_twistAt z hzm (rowSet ds N μ₀)).measurable
  invol := centreFlip_involutive hzz μ₀
  pres := measurePreserving_twistAt z hzm (rowSet ds N μ₀)
  kinv := wilsonKernel_centreFlip hz μ₀ β

variable {z : G} (hz : ∀ g : G, Commute z g) (hzz : z * z = 1)
  (hzm : MeasurePreserving (z * ·) (haarG G) (haarG G))

/-- **The electric-flux energy of the Wilson transfer operator is non-negative**, for every compact gauge group with a central
    element of order 2, every `β`, every box `(ℤ/Nℤ)^ds` and every flux direction `μ₀`; `Q` is any class of states closed under `|·|`
    (e.g. the gauge-invariant states). -/
theorem wilson_fluxEnergy_nonneg (β : ℝ) (μ₀ : Fin ds) (Q : (GaugeConnection G ds N → ℝ) → Prop)
    (hQ : ∀ ψ, Q ψ → Q (fun x => |ψ x|)) : 0 ≤ fluxEnergy (wilsonCentre hc hU hz hzz hzm β μ₀) Q :=
  fluxEnergy_nonneg _ Q hQ

/-- **The flux sector's time to live, Wilson transfer operator:** for a flux-sector state `ψ` (`ψ ∘ Ω̂ = −ψ`) and any bounded `φ`,
    `(∫ φ · Tⁿψ)² ≤ (lamVac^n e^{−E_e n})² ‖φ‖² ‖ψ‖²`. -/
theorem wilson_flux_correlator_decay (β : ℝ) (μ₀ : Fin ds) (Q : (GaugeConnection G ds N → ℝ) → Prop)
    (hQ : ∀ ψ, Q ψ → Q (fun x => |ψ x|))
    (hQT : ∀ ψ, BM ψ → Q ψ → Q (top (productHaar G ds N) (wilsonTKernel (ds := ds) (N := N) hc hU β) ψ))
    {φ ψ : GaugeConnection G ds N → ℝ} (hφ : BM φ) (hψ : Sec (wilsonCentre hc hU hz hzz hzm β μ₀) Q (-1) ψ) (m : ℕ) :
    (∫ x, φ x * (top (productHaar G ds N) (wilsonTKernel (ds := ds) (N := N) hc hU β))^[m] ψ x ∂(productHaar G ds N)) ^ 2 ≤
      ((lamVac (wilsonCentre hc hU hz hzz hzm β μ₀) Q) ^ m *
          Real.exp (-(fluxEnergy (wilsonCentre hc hU hz hzz hzm β μ₀) Q * m))) ^ 2 *
        nrm (productHaar G ds N) φ * nrm (productHaar G ds N) ψ :=
  flux_correlator_decay _ Q hQ hQT hφ hψ m

end Flux

/-! ## SU(2) -/

section SU2

theorem negOneSU2_central : ∀ g : SU2, Commute negOneSU2 g :=
  fun g => Subtype.ext (show (-1 : Matrix (Fin 2) (Fin 2) ℂ) * g.val = g.val * -1 by simp)

theorem negOneSU2_sq : negOneSU2 * negOneSU2 = 1 :=
  Subtype.ext (show (-1 : Matrix (Fin 2) (Fin 2) ℂ) * -1 = 1 by simp)

theorem su2_hc : Continuous (HasGaugeTrace.rep (G := SU2) (n := 2)) := continuous_subtype_val

theorem su2_hU : ∀ g : SU2, HasGaugeTrace.rep (G := SU2) (n := 2) g ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2

theorem su2_hzm : MeasurePreserving (negOneSU2 * ·) (haarG SU2) (haarG SU2) := measurePreserving_mul_left _ _

/-- 't Hooft's centre transformation (`z = −1`) for the SU(2) Wilson transfer operator on `(ℤ/Nℤ)^ds`. -/
abbrev su2Centre (β : ℝ) (μ₀ : Fin ds) :=
  wilsonCentre (ds := ds) (N := N) su2_hc su2_hU negOneSU2_central negOneSU2_sq su2_hzm β μ₀

/-- **SU(2) Yang–Mills, temporal-gauge transfer operator: the electric flux energy `E_e` of the sector `e_{μ₀} = 1` relative to
    the vacuum sector is non-negative**, for every `β`, every spatial box `(ℤ/Nℤ)^ds` and every class `Q` of states closed under
    `|·|`. -/
theorem su2_fluxEnergy_nonneg (β : ℝ) (μ₀ : Fin ds) (Q : (GaugeConnection SU2 ds N → ℝ) → Prop)
    (hQ : ∀ ψ, Q ψ → Q (fun x => |ψ x|)) : 0 ≤ fluxEnergy (su2Centre (N := N) β μ₀) Q :=
  fluxEnergy_nonneg _ Q hQ

/-- **SU(2): flux correlators decay like `e^{−E_e n}`** relative to the vacuum sector. -/
theorem su2_flux_correlator_decay (β : ℝ) (μ₀ : Fin ds) (Q : (GaugeConnection SU2 ds N → ℝ) → Prop)
    (hQ : ∀ ψ, Q ψ → Q (fun x => |ψ x|))
    (hQT : ∀ ψ, BM ψ → Q ψ → Q (top (productHaar SU2 ds N) (wilsonTKernel (ds := ds) (N := N) su2_hc su2_hU β) ψ))
    {φ ψ : GaugeConnection SU2 ds N → ℝ} (hφ : BM φ) (hψ : Sec (su2Centre (N := N) β μ₀) Q (-1) ψ) (m : ℕ) :
    (∫ x, φ x * (top (productHaar SU2 ds N) (wilsonTKernel (ds := ds) (N := N) su2_hc su2_hU β))^[m] ψ x
        ∂(productHaar SU2 ds N)) ^ 2 ≤
      ((lamVac (su2Centre (N := N) β μ₀) Q) ^ m * Real.exp (-(fluxEnergy (su2Centre (N := N) β μ₀) Q * m))) ^ 2 *
        nrm (productHaar SU2 ds N) φ * nrm (productHaar SU2 ds N) ψ :=
  flux_correlator_decay _ Q hQ hQT hφ hψ m

end SU2

end Attempts.R4.Layer
