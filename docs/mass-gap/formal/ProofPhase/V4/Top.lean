/-
Proof phase, cycle 5, workstream 1 (c5a-v4): assembly version 4, cut at L_* (2026-11-22). Released under Apache 2.0.

Field-by-field map: `docs/mass-gap/weak-coupling/proof-phase/ASSEMBLY.md` (section "Assembly v4").
Note: `docs/mass-gap/weak-coupling/proof-phase/c5a-v4/NOTE.md`.
-/

import ProofPhase.V4.Recursion
import ProofPhase.V4.UV
import ProofPhase.V3.Top

/-!
# Assembly v4: identification, one ultraviolet input, one infrared input

The tuning's unit `L₁` is read as **`L_*`**, the scale where segment 1 ends (the running coupling is a small fixed
number). The blocking family `B` blocks onto `L_*` cells; it is any `BlockingFamily` (a noisy local family is being built
in parallel by c5c and can be plugged in once it is one).

**The inputs, by layer.**
* ID: `OnLCP' T` (resolution, one-loop running, a two-sided renormalisation condition; `ProofPhase.V4.LCP`) and
  `NonTrivial T`.
* UV(`L_*`): `ObsTransferPhysTW T B` (Lemma UV at `L_*`: quasi-locality of `E[F | Φ_*]` and conditional decoupling, for
  time-separated observables of bounded physical extent).
* IR(`L_*`): `BlockGapUnifW T B λ`, `λ > 0` (the W₁ block gap of the `L_*` theory, uniform in level and volume), or its
  bounded form `BlockGapBddW T B λ` (`ProofPhase.V4.Gap`; implied by it). **The one input of gap strength.**

**The theorems.**
* `yang_mills_assembly_v4` (the draft's statement): `OnLCP' ∧ NonTrivial ∧ BlockGapUnifW T B λ (λ > 0) ∧
  ObsTransferPhysTW T B ⇒ TorusDecayLoc ∧ MassGapLoc ∧ MassGapMFLoc ∧ LimitRP ∧ NonTrivial`.
* `yang_mills_assembly_v4_bdd`: the same with the weaker `BlockGapBddW` (a stronger theorem; the recursion lemma lands
  there). `OpenInputsV4` and `yang_mills_assembly_v4_inputs` package it.
* `yang_mills_assembly_v4_strategyA`: strategy (a) for IR wired in (`V4.blockGapBddW_of_levelDprimeWOn`): v3's D′ at
  `L₁ = s·L_*` and stage 2, both stated for the `L_*` theory, in place of the infrared input.
* `openInputsV4_of_levelTorusRouteW`: v3's preferred inputs at the same unit imply v4's (`LevelDprimeW ⇒ BlockGapUnifW`,
  `OnLCP ⇒ OnLCP'`); v3's sup branch does not (no Lipschitz approximant), so the sup family is retired, as is route B.
* `not_trivial_v4`: pure noise fails the inputs.

Not in the top statement any more (files kept): route B (`ConjW ∧ SectorTransfer`), the sup family (`LevelDprime`,
`LimitDprime`, `H1Local`, `ObsTransferPhysT`), `H1LocalLipW ∧ LimitDprimeW` (they now prove the infrared input only inside
strategy (a), through `LevelDprimeW`), and `Seg1` (a supplier of the `L_*` theory for the ultraviolet layer,
`ProofPhase.V4.UV`, not an input of the infrared one).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  ProofPhase.Torus ProofPhase.V3

noncomputable section

namespace ProofPhase.V4

/-- **Assembly v4** (as drafted). SU(2) lattice Yang–Mills with the Wilson action on 4D tori along the tuning `T`, whose
unit is read as `L_*`; `B` a blocking family onto `L_*` cells. If the line of constant physics holds in its weakened form,
the limit is non-trivial, the `L_*` theory has the W₁ block gap at rate `λ > 0` (**the gap-strength input**) and the
ultraviolet transfer to `L_*` cells holds, then: torus decay with a level-uniform constant for slab observables of bounded
physical extent, the gap for them in both orders of limits, reflection positivity of every limit point, non-triviality. -/
theorem yang_mills_assembly_v4 {T : Tuning} (hL : OnLCP' T) (hN : NonTrivial T) (B : BlockingFamily T) {lam : ℝ}
    (hlam : 0 < lam) (hIR : BlockGapUnifW T B lam) (hUV : ObsTransferPhysTW T B) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T := by
  have hT := torusDecayLoc_of_blockGapUnifW B hlam hIR hUV
  obtain ⟨hVF, hMF⟩ := bothOrdersLoc_of_torusDecayLoc hL.tendsto_a hT
  exact ⟨hT, hVF, hMF, limitRP T, hN⟩

/-- **Assembly v4 with the bounded infrared input** (stronger theorem: `BlockGapBddW` is implied by `BlockGapUnifW`). -/
theorem yang_mills_assembly_v4_bdd {T : Tuning} (hL : OnLCP' T) (hN : NonTrivial T) (B : BlockingFamily T) {lam : ℝ}
    (hlam : 0 < lam) (hIR : BlockGapBddW T B lam) (hUV : ObsTransferPhysTW T B) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T := by
  have hT := torusDecayLoc_of_blockGapBddW B hlam hIR hUV
  obtain ⟨hVF, hMF⟩ := bothOrdersLoc_of_torusDecayLoc hL.tendsto_a hT
  exact ⟨hT, hVF, hMF, limitRP T, hN⟩

/-- **The open inputs of the proof, version 4** (tuning unit read as `L_*`). -/
structure OpenInputsV4 (T : Tuning) : Prop where
  /-- ID: the line of constant physics, weakened (two-sided renormalisation condition). -/
  lcp : OnLCP' T
  /-- ID: non-triviality. -/
  nontrivial : NonTrivial T
  /-- UV and IR at `L_*`: a blocking family onto `L_*` cells, the bounded W₁ block gap (gap strength) and the
  time-separated transfer with a Lipschitz approximant (ultraviolet). -/
  layers : ∃ (B : BlockingFamily T) (lam : ℝ), 0 < lam ∧ BlockGapBddW T B lam ∧ ObsTransferPhysTW T B

/-- **Assembly v4, packaged.** -/
theorem yang_mills_assembly_v4_inputs {T : Tuning} (P : OpenInputsV4 T) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T := by
  obtain ⟨B, lam, hlam, hIR, hUV⟩ := P.layers
  exact yang_mills_assembly_v4_bdd P.lcp P.nontrivial B hlam hIR hUV

/-- The draft's inputs give the packaged ones. -/
theorem openInputsV4_of_unifW {T : Tuning} (hL : OnLCP' T) (hN : NonTrivial T) (B : BlockingFamily T) {lam : ℝ}
    (hlam : 0 < lam) (hIR : BlockGapUnifW T B lam) (hUV : ObsTransferPhysTW T B) : OpenInputsV4 T :=
  ⟨hL, hN, B, lam, hlam, blockGapBddW_of_unifW hIR, hUV⟩

/-- **v3's preferred route implies v4's inputs at the same unit** (D): `OnLCP ⇒ OnLCP'`, `LevelDprimeW ⇒ BlockGapUnifW`. -/
theorem openInputsV4_of_levelTorusRouteW {T : Tuning} (hL : OnLCP T) (hN : NonTrivial T) (h : LevelTorusRouteW T) :
    OpenInputsV4 T := by
  obtain ⟨B, lam, hlam, hD, hUV⟩ := h
  exact openInputsV4_of_unifW hL.toOnLCP' hN B hlam (blockGapUnifW_of_levelDprimeW B hlam.le hD) hUV

/-- **Assembly v4 with strategy (a) for the infrared input** (the recursion lemma wired in). `B₁` blocks onto `L_*`
cells, `B₂ k j` blocks the `L_*` torus onto an `L₁` torus of side `M j` (scale ratio `s = L₁/L_*`). Inputs: `OnLCP'`,
`NonTrivial`, v3's D′ in W₁ form for the `L₁` laws `(blockedLaw T B₁ k j).map (B₂ k j)` (`LevelDprimeWOn`), stage 2 for
the `L_*` theory (`StageTwoW`, Lemma X), and the ultraviolet transfer to `L_*` (`ObsTransferPhysTW T B₁`). -/
theorem yang_mills_assembly_v4_strategyA {T : Tuning} (hL : OnLCP' T) (hN : NonTrivial T) (B₁ : BlockingFamily T)
    {M : ℕ → ℕ} [∀ j, NeZero (M j)]
    (B₂ : ∀ k j : ℕ, GaugeConnection SU2 4 (coarseSide j) → GaugeConnection SU2 4 (M j))
    (hB₂ : ∀ k j : ℕ, Measurable (B₂ k j)) {s lam₂ : ℝ} (hs : 0 < s) (hlam₂ : 0 < lam₂)
    (hD : LevelDprimeWOn (fun k j => (blockedLaw T B₁ k j).map (B₂ k j)) lam₂)
    (hX : StageTwoW (blockedLaw T B₁) B₂ s) (hUV : ObsTransferPhysTW T B₁) :
    OpenInputsV4 T ∧ TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T := by
  obtain ⟨lam, hlam, hIR⟩ := blockGapBddW_of_levelDprimeWOn B₁ B₂ hB₂ hs hlam₂ hD hX
  have P : OpenInputsV4 T := ⟨hL, hN, B₁, lam, hlam, hIR, hUV⟩
  exact ⟨P, yang_mills_assembly_v4_inputs P⟩

/-- **Non-triviality of the hypotheses:** the pure-noise family `β_k = 0` does not satisfy the v4 inputs. -/
theorem not_trivial_v4 (T : Tuning) (h0 : ∀ k, T.β k = 0) : ¬ OpenInputsV4 T := fun P =>
  not_onLCP'_of_bounded (B := 0) (fun k => by rw [h0 k, abs_zero]) P.lcp

end ProofPhase.V4
