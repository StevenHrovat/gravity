# R11: the formal assembly accepts a measurable blocking

File: `formal/ProofPhase/Interface/MeasBlocking.lean` (namespace `ProofPhase.Interface`). No existing file was edited.
Build: green (9018 jobs); axioms: see `axioms.log` (standard three only; no sorry, native_decide or axiom).

## Verified: the theta/half claim is true
Every use of the fields `.theta` / `.half` of `RPBlocking` in the formal tree:
* `Objects.lean` 421-422: `blocked_wilson_rp` (reflection positivity of the blocked Wilson measure).
* `Repair/MulNoise.lean` 146, 156 and `Repair/Noisy.lean` 83-84, 114-131: noisy / multiplicative-noise blockings
  (they feed `noisy_blocked_wilson_rp`).
* `RouteA/Blocking.lean` 572-596: construction and composition of blockings (smear block, identity, composition).
None is on the gap/transfer path. The path of `yang_mills_assembly_v4_bdd` is: `BlockGapBddW` and `ObsTransferPhysTW`
(statements use only `(B k j).B`), `torusDecayLoc_of_blockGapBddW` (proof uses `(B k j).B`, `(B k j).meas` and, through
`cov_map`/`cov_transfer`, nothing else), `bothOrdersLoc_of_torusDecayLoc`, `limitRP` (bare measure). So the claim holds.

## Proved
* `MeasBlocking G d N M` (fields `B`, `meas`), `MeasBlockingFamily T`, `RPBlocking.toMeas`, `blockingFamilyToMeas`.
* `MeasBlockGapBddW`, `MeasBlockGapUnifW`, `MeasObsTransferPhysTW`: the same statements as the originals for the bare map;
  `*_toMeas_iff` lemmas (all `Iff.rfl`) show the originals are the special case.
* `measTorusDecayLoc_of_blockGapBddW`: the body of the original proof, verbatim (it never used more than `B`, `meas`).
* `yang_mills_assembly_v4_bdd_meas`, `yang_mills_assembly_v4_meas` (homogeneous gap), `MeasOpenInputsV4`,
  `yang_mills_assembly_v4_inputs_meas`, `measOpenInputsV4_of_openInputsV4`: same five-fold conclusion as v4
  (`TorusDecayLoc ∧ MassGapLoc ∧ MassGapMFLoc ∧ LimitRP ∧ NonTrivial`).
* `MeasBlocking.viaState`, `measBlockedLaw_viaState`: a blocking through any measurable intermediate block state with a
  measurable SU(2) encoding (this is the slot for M1's SO(3) x Z2 state).

## Open / not done
* The SU(2) encoding of SO(3) x Z2 itself (lift of SO(3) bonds times z, Z2 axial gauge, gauge covariance) is NOT done: the
  development has no SO(3) x Z2 state type, and a measurable SO(3) -> SU(2) section is a large development. `viaState` is
  the interface it plugs into. The encoding's gauge-covariance is also what `GaugeInvariant` observables in
  `MeasObsTransferPhysTW` will need.
* Variants not ported: `_strategyA`, the V3 chain (`LevelDprimeW`, `H1LocalLipW`), `OneBox`, `Book/TwoSize`. They also use
  only `.B`/`.meas` on the gap side but were not requested.
* A measurable blocking is not required to give reflection positivity of blocked layers (`blocked_wilson_rp`); the
  assembly never needs it, since `LimitRP` comes from the bare measure. Anything wanting RP of block observables still
  needs `RPBlocking`.
