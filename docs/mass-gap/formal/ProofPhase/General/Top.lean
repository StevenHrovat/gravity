/-
Proof phase, generalisation phase 1: the top file of the generic layer (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`.
-/

import ProofPhase.General.Counting
import ProofPhase.General.Torus
import ProofPhase.General.GaugeGroup
import ProofPhase.General.SU2Instance
import ProofPhase.General.Instances
import ProofPhase.General.Combined
import ProofPhase.General.Noisy
import ProofPhase.General.Filter
import ProofPhase.General.Local
import ProofPhase.General.PerVolume

/-!
# The generic layer over any gauge group and dimension (phase 1)

Imports the modules of `ProofPhase/General/`. Nothing outside this folder is edited; every generic theorem re-derives
the old SU(2), `d = 4` statement as an instance (see `NOTE.md`).
-/
