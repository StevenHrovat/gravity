/-
Proof phase, cycle 4, workstream 1 (c4a-condmass): assembly v3 (2026-11-22). Released under Apache 2.0.

Field-by-field map: `docs/mass-gap/weak-coupling/proof-phase/ASSEMBLY.md` (section "Assembly v3").
Note: `docs/mass-gap/weak-coupling/proof-phase/c4a-condmass/NOTE.md`.
-/

import ProofPhase.V3.CondInputs

/-!
# Assembly v3: the current minimal open inputs, with cycle 3's results wired in

**The open inputs** (`OpenInputsV3 T`, all about SU(2) lattice Yang–Mills with the Wilson action on 4D tori along the
tuning `T` and its blocked laws):

* `lcp : OnLCP T` — the line of constant physics (unchanged from cycle 2).
* `nontrivial : NonTrivial T` — non-triviality (unchanged).
* `crossover : LevelTorusRouteW T ∨ LevelTorusRouteT T` — the torus route in its two current forms:
  * **W₁ form (preferred after c3b):** a blocking family `B`, `λ > 0`, `LevelDprimeW T B λ` (D′ in W₁ form along the
    levels, single-link geodesic W₁ influences, column sums `≤ γ` with `γ e^{λD₁} < 1`) and `ObsTransferPhysTW T B` (the
    time-separated transfer with a Lipschitz approximant).
  * **sup form:** `LevelDprime T B λ` (cycle 3, c3d) and `ObsTransferPhysT T B` (time-separated transfer).

**What each input is proved from (sufficient conditions, Lean):**
* `LevelDprimeW ⇐ H1LocalLipW ∧ LimitDprimeW` (`levelDprimeW_of_h1LocalLip`, the W₁ openness lemma) and, for a limit in
  c3c's certified window, `⇐ CertifiedAdjointW ∧ H1LocalLipW` (`levelDprimeW_of_certified`).
* `ObsTransferPhysT(W) ⇐ CondDecouple ∧ ObsQuasiLocT(W)` (`obsTransferPhysT(W)_of_condDecouple`), with part (c)
  `CondDecouple = Seg2.CondDecouple T B (sepT T)` (c4c's statement with time separation) from any of: `CondMassAnn`
  (annealed conditional covariance, the recommended form), `CondMass` (Dobrushin–Shlosman on super-sites, quenched a.e.;
  `CondMass ⇒ CondMassDecay ⇒ CondMassAnn`), c4c's `SmootherStable` (filter form).
* `LevelDprime ⇐ H1Local ∧ LimitDprime` (cycle 3), `ObsTransferPhysT ⇐ ObsTransferPhys` (`obsTransferPhysT_of_phys`);
  hence cycle 2's `BlockedTorusRoute` and cycle 3's `LevelTorusRoute` imply the sup form (`openInputsV3_of_level`,
  `openInputsV3_of_blockedTorusRoute`).

**The theorems.**
* `yang_mills_assembly_v3 : OpenInputsV3 T → TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧
  NonTrivial T` (both orders of limits).
* `yang_mills_assembly_v3_W1` (the named form of the preferred route): `OnLCP`, `NonTrivial`, a blocking family `B`,
  `H1LocalLipW T B Vk Vinf`, `LimitDprimeW Vinf`, `CondMassAnn T B`, `ObsQuasiLocTW T B` ⇒ the open inputs and the
  conclusion. Variants: `_dec` (part (c) as input), `_condMass` (Dobrushin form), `_smoother` (c4c's filter form).
* `yang_mills_assembly_v3_certified`: the same with `Vinf` the two-coupling action in a certified corner and
  `CertifiedAdjointW` in place of `LimitDprimeW`.
* `yang_mills_assembly_v3_sup`: the sup form with `LevelDprime`, `CondMassAnn`, `ObsQuasiLocT`.
* `not_trivial_v3`: pure noise (`β_k = 0`) fails the open inputs.

**Hypotheses do not contain the conclusion** (checked, NOTE.md §5): no input is a decay statement for fine observables
of the Wilson measure. `LevelDprime(W)` is about the blocked laws (coarse), `CondMass` about conditional laws given the
block field (it holds for the photon, which has no gap), `ObsQuasiLoc` about conditional expectations (no decay of any
covariance). Part (c) of the transfer is equivalent to fine decay **given** the coarse decay (c3a's difficulty
conservation), so the `_dec` variant is a law-of-total-covariance reduction; the content of `CondMassAnn` is that the
conditioned system mixes, which the photon satisfies without a gap.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  ProofPhase.Torus ProofPhase.H1 ProofPhase.Certified

noncomputable section

namespace ProofPhase.V3

/-- **The open inputs of the proof, version 3.** -/
structure OpenInputsV3 (T : Tuning) : Prop where
  /-- P6.7: the line of constant physics. -/
  lcp : OnLCP T
  /-- P6.2: non-triviality. -/
  nontrivial : NonTrivial T
  /-- The crossover: the torus route in W₁ form (preferred) or in sup form. -/
  crossover : LevelTorusRouteW T ∨ LevelTorusRouteT T

/-- **Assembly v3.** For SU(2) lattice Yang–Mills (Wilson action, 4D tori) along a tuning `T`: if the open inputs hold,
torus decay holds with a level-uniform constant for slab observables of bounded physical extent, the gap holds for them
in both orders of limits, every limit point is reflection positive, and the limit is non-trivial. -/
theorem yang_mills_assembly_v3 {T : Tuning} (P : OpenInputsV3 T) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T := by
  rcases P.crossover with hW | hS
  · obtain ⟨hT, hVF, hMF⟩ := bothOrdersLoc_of_levelRouteW P.lcp.tendsto_a hW
    exact ⟨hT, hVF, hMF, limitRP T, P.nontrivial⟩
  · obtain ⟨hT, hVF, hMF⟩ := bothOrdersLoc_of_levelRouteT P.lcp.tendsto_a hS
    exact ⟨hT, hVF, hMF, limitRP T, P.nontrivial⟩

/-- **Assembly v3, preferred (W₁) route, with part (c) as the input** (`Seg2.CondDecouple` with time separation). -/
theorem yang_mills_assembly_v3_W1_dec {T : Tuning} (hL : OnLCP T) (hN : NonTrivial T) (B : BlockingFamily T)
    {Vk : ∀ j, ℕ → CoarsePot j}
    {Vinf : ∀ j, LatticePlaquette 4 (coarseSide j) → GaugeConnection SU2 4 (coarseSide j) → ℝ}
    (hH1 : H1LocalLipW T B Vk Vinf) (hD : LimitDprimeW Vinf) (hC : Seg2.CondDecouple T B (sepT T))
    (hQ : ObsQuasiLocTW T B) :
    OpenInputsV3 T ∧ TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T := by
  obtain ⟨lam, hlam, hLW⟩ := levelDprimeW_of_h1LocalLip hH1 hD
  have P : OpenInputsV3 T := ⟨hL, hN, Or.inl ⟨B, lam, hlam, hLW, obsTransferPhysTW_of_condDecouple hC hQ⟩⟩
  exact ⟨P, yang_mills_assembly_v3 P⟩

/-- **Assembly v3, named form of the preferred (W₁) route.** Inputs: the line of constant physics, non-triviality, a
reflection-respecting blocking family `B` onto `L₁` cells, H1 in W₁ form (`H1LocalLipW`), D′ in W₁ form for the limit
plaquette action at `L₁` (`LimitDprimeW`), `CondMassAnn` (the fine field conditioned on the block field mixes at the
block scale, on average over the block field), and the quasi-locality part of the time-separated transfer
(`ObsQuasiLocTW`). -/
theorem yang_mills_assembly_v3_W1 {T : Tuning} (hL : OnLCP T) (hN : NonTrivial T) (B : BlockingFamily T)
    {Vk : ∀ j, ℕ → CoarsePot j}
    {Vinf : ∀ j, LatticePlaquette 4 (coarseSide j) → GaugeConnection SU2 4 (coarseSide j) → ℝ}
    (hH1 : H1LocalLipW T B Vk Vinf) (hD : LimitDprimeW Vinf) (hC : CondMassAnn T B) (hQ : ObsQuasiLocTW T B) :
    OpenInputsV3 T ∧ TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T :=
  yang_mills_assembly_v3_W1_dec hL hN B hH1 hD (condDecouple_of_condMassAnn hC) hQ

/-- **The same with `CondMass` in Dobrushin–Shlosman form** (super-sites, quenched almost surely). -/
theorem yang_mills_assembly_v3_W1_condMass {T : Tuning} (hL : OnLCP T) (hN : NonTrivial T) (B : BlockingFamily T)
    {Vk : ∀ j, ℕ → CoarsePot j}
    {Vinf : ∀ j, LatticePlaquette 4 (coarseSide j) → GaugeConnection SU2 4 (coarseSide j) → ℝ}
    (hH1 : H1LocalLipW T B Vk Vinf) (hD : LimitDprimeW Vinf) (hC : CondMass T B) (hQ : ObsQuasiLocTW T B) :
    OpenInputsV3 T ∧ TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T :=
  yang_mills_assembly_v3_W1_dec hL hN B hH1 hD (condDecouple_of_condMass hC) hQ

/-- **The same with c4c's filter form** (`Seg2.SmootherStable` with time separation). -/
theorem yang_mills_assembly_v3_W1_smoother {T : Tuning} (hL : OnLCP T) (hN : NonTrivial T) (B : BlockingFamily T)
    {Vk : ∀ j, ℕ → CoarsePot j}
    {Vinf : ∀ j, LatticePlaquette 4 (coarseSide j) → GaugeConnection SU2 4 (coarseSide j) → ℝ}
    (hH1 : H1LocalLipW T B Vk Vinf) (hD : LimitDprimeW Vinf) (hC : Seg2.SmootherStable T B (sepT T))
    (hQ : ObsQuasiLocTW T B) :
    OpenInputsV3 T ∧ TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T :=
  yang_mills_assembly_v3_W1_dec hL hN B hH1 hD (Seg2.condDecouple_of_smootherStable hC) hQ

/-- **Assembly v3 with the certified window**: as `yang_mills_assembly_v3_W1`, with the limit action the two-coupling
plaquette action in a certified corner and the computer-assisted `CertifiedAdjointW` in place of `LimitDprimeW`. -/
theorem yang_mills_assembly_v3_certified {T : Tuning} (hL : OnLCP T) (hN : NonTrivial T) (B : BlockingFamily T)
    (hcert : CertifiedAdjointW) (c : Fin 6) {βF βA : ℝ} (hA : |βA| ≤ cornerA c) (hF : |βF| ≤ cornerF c)
    {Vk : ∀ j, ℕ → CoarsePot j} (hH1 : H1LocalLipW T B Vk (fun _ => twoCoupling βF βA)) (hC : CondMassAnn T B)
    (hQ : ObsQuasiLocTW T B) :
    OpenInputsV3 T ∧ TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T :=
  yang_mills_assembly_v3_W1 hL hN B hH1 (limitDprimeW_twoCoupling hcert c hA hF) hC hQ

/-- **Assembly v3, named form of the sup route**: `LevelDprime`, `CondMassAnn`, `ObsQuasiLocT`. -/
theorem yang_mills_assembly_v3_sup {T : Tuning} (hL : OnLCP T) (hN : NonTrivial T) (B : BlockingFamily T)
    {lam : ℝ} (hlam : 0 < lam) (hD : LevelDprime T B lam) (hC : CondMassAnn T B) (hQ : ObsQuasiLocT T B) :
    OpenInputsV3 T ∧ TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T := by
  have P : OpenInputsV3 T :=
    ⟨hL, hN, Or.inr ⟨B, lam, hlam, hD, obsTransferPhysT_of_condDecouple (condDecouple_of_condMassAnn hC) hQ⟩⟩
  exact ⟨P, yang_mills_assembly_v3 P⟩

/-- Cycle 3's level route implies the v3 inputs (D). -/
theorem openInputsV3_of_level {T : Tuning} (hL : OnLCP T) (hN : NonTrivial T) (h : LevelTorusRoute T) :
    OpenInputsV3 T :=
  ⟨hL, hN, Or.inr (levelTorusRouteT_of_level h)⟩

/-- Cycle 2's torus route implies the v3 inputs (D). -/
theorem openInputsV3_of_blockedTorusRoute {T : Tuning} (hL : OnLCP T) (hN : NonTrivial T)
    (h : BlockedTorusRoute T) : OpenInputsV3 T :=
  openInputsV3_of_level hL hN (levelTorusRoute_of_blockedTorusRoute h)

/-- **Non-triviality of the hypotheses:** the pure-noise family `β_k = 0` does not satisfy the v3 inputs. -/
theorem not_trivial_v3 (T : Tuning) (h0 : ∀ k, T.β k = 0) : ¬ OpenInputsV3 T := fun P =>
  not_onLCP_of_bounded (B := 0) (fun k => by rw [h0 k, abs_zero]) P.lcp

end ProofPhase.V3
