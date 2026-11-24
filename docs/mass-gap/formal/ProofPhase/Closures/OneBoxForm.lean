/-
Closures round (2026-11-24): O1 in one Lean form for the Wilson measure, linked to the assembly it feeds; the gap from
O1 needs only the resolution clause of the line of constant physics. Released under Apache 2.0.

Paper: Part III, III.5.6 care points and III.9 (claims III.5.7, III.5.9, III.9.5); `docs/paper/OPEN-CLAIMS-CLOSURES.md`.
-/

import ProofPhase.OneBox.Fine
import ProofPhase.OneBox2.Concrete
import ProofPhase.Saturation.Reduction

/-!
# O1 in one form, and the assembly it feeds

**The one form (claim III.5.9).** The Lean assemblies take the one-box input in several named forms. This file fixes
one: `O1Form T := OneBox.FineOneBox T`, the one-box criterion for the SU(2) Wilson measure at the physical cell scale,
under **every** boundary condition (the quantifier "uniformly over every well-defined outside" of III.5.6), uniform in
the level and the volume. The other forms are linked to it:

* `o1Form_of_wilson` (S): the concrete form with the actual DLR box kernel (`OneBox2.WilsonOneBox`) implies it;
* `o1Form_of_split` (S): the split form (`Saturation.FineOneBoxSplit`, centre and adjoint influences) implies it;
* `BlockGapBddW` (`V4/Gap.lean`) is not a one-box form: it is the decay input of the separate blocking route, and
  `FineOneBoxPat` (`Adjoint2/PatternAssembly.lean`) is an alternative criterion with its own assembly
  (`yang_mills_assembly_pat`). Neither is needed by this route.

**The per-box costs multiply (claim III.5.7).** In this form the influence bounds are per outside (quenched), so no
identification of an annealed torus free energy with a per-outside influence is used: the composition of the per-box
influences over the lattice is the theorem `fineDecayInv_of_fineOneBox` (S), re-exported as `decay_of_o1Form`. The
annealed-to-quenched step is needed only to read a torus measurement of `F_e` as evidence about O1; there it is a
property of the measurement, not a step of the proof.

**The gap from O1 alone (claim III.9.5).** `gap_of_o1Form` (S): a tuning whose resolution `ℓ_k` (lattice spacings per
physical cell) tends to infinity, and `O1Form`, give torus decay, the gap in both orders of limits and reflection
positivity. The running clause, the scheme clause of the line of constant physics and non-triviality are **not**
used: they identify the gapped limit as Yang-Mills, they are not inputs of the gap mechanism.
`yang_mills_assembly_onebox_of_resolution` (S) recovers the original assembly from these weaker hypotheses.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity ProofPhase.Torus ProofPhase.V3 ProofPhase.V4 ProofPhase.RouteA ProofPhase.OneBox

noncomputable section

namespace ProofPhase.Closures.OneBoxForm

/-- **O1 in its one Lean form** for the Wilson measure: the one-box criterion `FineOneBox` at the physical cell scale,
under every boundary condition, uniform in level and volume. -/
abbrev O1Form (T : Tuning) : Prop := FineOneBox T

/-- The concrete form (the actual DLR box kernel, no assumed covariance) implies the one form (S). -/
theorem o1Form_of_wilson {T : Tuning} (h : ProofPhase.OneBox2.WilsonOneBox T) : O1Form T :=
  ProofPhase.OneBox2.fineOneBox_of_wilsonOneBox h

/-- The split form (centre and adjoint influences separately) implies the one form (S). -/
theorem o1Form_of_split {T : Tuning} (h : ProofPhase.Saturation.FineOneBoxSplit T) : O1Form T :=
  ProofPhase.Saturation.fineOneBox_of_split h

/-- **The per-box influences compose** (S): the one form gives exponential decay of gauge-invariant covariances,
uniformly in level and volume. This is the multiplication over boxes that claim III.5.7 asked for. -/
theorem decay_of_o1Form {T : Tuning} (h : O1Form T) : FineDecayInv T :=
  fineDecayInv_of_fineOneBox h

/-- The resolution clause alone gives `a_k → 0`. -/
theorem tendsto_a_of_resolution {T : Tuning} (hres : Tendsto T.ℓ atTop atTop) : Tendsto T.a atTop (𝓝 0) := by
  have h1 : Tendsto (fun k => (T.ℓ k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hres
  show Tendsto (fun k => T.L₁ / (T.ℓ k : ℝ)) atTop (𝓝 0)
  exact h1.const_div_atTop T.L₁

/-- **The gap from O1 alone** (S): resolution to infinity and the one form give torus decay, the gap in both orders of
limits and reflection positivity. No running or scheme clause, no non-triviality. -/
theorem gap_of_o1Form {T : Tuning} (hres : Tendsto T.ℓ atTop atTop) (h : O1Form T) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T := by
  have hT := torusDecayLoc_of_fineDecayInv (fineDecayInv_of_fineOneBox h)
  obtain ⟨hVF, hMF⟩ := bothOrdersLoc_of_torusDecayLoc (tendsto_a_of_resolution hres) hT
  exact ⟨hT, hVF, hMF, limitRP T⟩

/-- **The original assembly from the weaker hypotheses** (S): `yang_mills_assembly_onebox` uses of the line of
constant physics only its resolution clause, and passes non-triviality through unchanged. -/
theorem yang_mills_assembly_onebox_of_resolution {T : Tuning} (hres : Tendsto T.ℓ atTop atTop) (hN : NonTrivial T)
    (h : O1Form T) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T := by
  obtain ⟨h1, h2, h3, h4⟩ := gap_of_o1Form hres h
  exact ⟨h1, h2, h3, h4, hN⟩

/-- The weakened line of constant physics contains the resolution clause, so the original assembly is a special case. -/
theorem resolution_of_onLCP' {T : Tuning} (hL : OnLCP' T) : Tendsto T.ℓ atTop atTop := hL.resolution

end ProofPhase.Closures.OneBoxForm
