/-
Proof phase (round 5), workstream 1 (Route A): the centre-blind check (free win 4), 2026-11-22. Released under
Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/ws1-routeA/NOTE.md`, section 1.
-/

import ProofPhase.RouteA.Blocking
import Attempts.Positivity.Adjoint

/-!
# Centre-blind (adjoint, SO(3)) variables do not see the fundamental observables

Free win 4 proposed imposing the Dobrushin condition on centre-blind block variables only, on the grounds that local
gauge-invariant observables are centre-neutral. Two elementary facts, both relevant to the verdict of `NOTE.md` §1:

* `xp_not_adjointOnly`: the **fundamental plaquette** `Re tr U_p` of SU(2) (a slab observable: measurable, gauge invariant,
  local) is **not** a function of the adjoint images of the links (`Attempts.Positivity.AdjointOnly`): flipping one link
  by the centre element `−1` keeps every adjoint image and changes `Re tr U_p` from `2` to `−2`. Local gauge-invariant
  observables are neutral under the **global** centre symmetry, not functions of the centre-blind variables; so decay of
  centre-blind variables alone does not reach `SlabDecay`.
* `cov_adjointOnly_comm` (the photon test, formal half): for an **abelian** gauge group (U(1), Z₂) every centre-blind
  observable is constant, so its covariance with anything vanishes under every measure. A Dobrushin condition on
  centre-blind variables is then satisfied with `γ = 0` by the free photon; if it implied decay of every local
  gauge-invariant observable, the photon would have a gap (Guth; Froehlich–Spencer: it does not). So no theorem of the
  form "centre-blind D′ ⇒ SlabDecay" holds uniformly in the gauge group.

**Claim level.** Both are elementary (group theory and one computation); they are counterexample-type statements, not
dynamics.
-/

open MeasureTheory Finset AreaLaw.Concrete Attempts.Positivity

noncomputable section

namespace ProofPhase.RouteA

/-- **The fundamental plaquette is not centre-blind.** On a periodic lattice of side `N ≥ 2`, the SU(2) plaquette
variable `Re tr U_p` is not a function of the adjoint images of the links. -/
theorem xp_not_adjointOnly {d N : ℕ} (hN : 2 ≤ N) (p : LatticePlaquette d N) :
    ¬ AdjointOnly (fun U : GaugeConnection SU2 d N => xp 2 p U) := by
  intro h
  have : Fact (1 < N) := ⟨hN⟩
  set l0 := p.boundaryLinks 0
  set V : GaugeConnection SU2 d N := Function.update (fun _ => (1 : SU2)) l0 negOneSU2
  have hne : p.dir1 ≠ p.dir2 := ne_of_lt p.h_lt
  have h1 : p.boundaryLinks 1 ≠ l0 := fun e => hne (congrArg LatticeLink.dir e).symm
  have h3 : p.boundaryLinks 3 ≠ l0 := fun e => hne (congrArg LatticeLink.dir e).symm
  have h2 : p.boundaryLinks 2 ≠ l0 := by
    intro e
    have e' := congrFun (congrArg LatticeLink.site e) p.dir2
    simp only [l0, LatticePlaquette.boundaryLinks, siteShift, Function.update_self] at e'
    have : (1 : ZMod N) = 0 := by linear_combination e'
    exact one_ne_zero this
  have hadj : ∀ (i : LatticeLink d N) (x : SU2), (fun _ => (1 : SU2)) i * x * ((fun _ => (1 : SU2)) i)⁻¹ =
      V i * x * (V i)⁻¹ := by
    intro i x
    by_cases hi : i = l0
    · simp only [V, hi, Function.update_self, one_mul, inv_one, mul_one]
      rw [(Attempts.R4.Layer.negOneSU2_central x).eq, mul_assoc, mul_inv_cancel, mul_one]
    · simp [V, Function.update_of_ne hi]
  have heq := h _ _ hadj
  have hV : plaquetteHolonomy V p = negOneSU2 := by
    simp only [plaquetteHolonomy, V, l0, Function.update_self, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, inv_one, mul_one]
  have hl : xp 2 p (fun _ => (1 : SU2)) = 2 := by
    simp [xp, gaugeReTr, gaugeTrace, plaquetteHolonomy, HasGaugeTrace.rep]
  have hr : xp 2 p V = -2 := by
    simp only [xp, hV]
    simp [gaugeReTr, gaugeTrace, negOneSU2, HasGaugeTrace.rep]
  have heq' : xp 2 p (fun _ => (1 : SU2)) = xp 2 p V := heq
  rw [hl, hr] at heq'
  norm_num at heq'

/-- **For an abelian gauge group, centre-blind observables have zero covariance with everything**, under every
probability measure (they are constant: `AdjointOnly.const_of_comm`). -/
theorem cov_adjointOnly_comm {G : Type*} [CommGroup G] {ι : Type*} [MeasurableSpace (ι → G)]
    (μ : Measure (ι → G)) [IsProbabilityMeasure μ] {F H : (ι → G) → ℝ} (hF : AdjointOnly F) :
    ∫ U, F U * H U ∂μ - (∫ U, F U ∂μ) * ∫ U, H U ∂μ = 0 := by
  have hc : ∀ U, F U = F 1 := fun U => AdjointOnly.const_of_comm hF U 1
  simp only [hc, integral_const_mul, integral_const, smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one]
  ring

end ProofPhase.RouteA
