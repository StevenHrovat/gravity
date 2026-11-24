/-
Proof phase, workstream 2 (Route B): where the sector transfer P5.1 lands (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/ws2-routeB/NOTE.md`, section 2.
-/

import ProofPhase.Existence.Bridge

/-!
# P5.1 lands on Route A: the sector transfer is discharged by neutral-sector decay, and by nothing found on the flux side

The note (section 2) reads Kanazawa's generalised Tomboulis–Yaffe inequality (Annals Phys. 324 (2009), arXiv:0808.3442),
Tomboulis–Yaffe (1985) and Chatterjee (CMP 385 (2021), arXiv:2006.16229) and finds that every known rigorous
twist/flux-to-decay inequality concludes decay of **centre-charged** correlations (Polyakov lines, Wilson loops), because
its key hypothesis (Kanazawa's (100), zero average of the observable over the twisted symmetry group) excludes every
centre-neutral observable, and the slab observables of `MassGap` are centre-neutral. So no statement about twisted free
energies (or about the act number, which is one by `ProofPhase.RouteB.electric_eq_magnetic` and the sector Fourier
identity) is known to imply `MassGap`, and the product counterexample of the note (SU(2) × U(1)) shows that no such
implication can follow from reflection positivity, centre structure and flux growth alone.

What this file records in Lean is only the **meeting point**: `SectorTransfer` is implied by route A's neutral-sector
hypotheses (`SlabDecay`, or workstream 4's `TorusDecay`). Both proofs are **definitional** (they compose the assembly's
route-A theorems and ignore `FluxGrowth`); they say that P5.1 is at most as hard as route A's crossover piece, and the
note says why no route through the flux sector is known.
-/

open Filter Topology ProofPhase.Existence

noncomputable section

namespace ProofPhase.RouteB

/-- **Meeting point (definitional).** On a line of constant physics, route A's `SlabDecay` discharges route B's sector
transfer. -/
theorem sectorTransfer_of_slabDecay {T : Tuning} (hL : OnLCP T) (hA : SlabDecay T) : SectorTransfer T :=
  fun _ => (assembly_routeA hL hA).1

/-- **Meeting point with workstream 4 (definitional).** `TorusDecay` (level-uniform constant) discharges the sector
transfer whenever the lattice spacing goes to zero. -/
theorem sectorTransfer_of_torusDecay {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (h : TorusDecay T.toV) :
    SectorTransfer T :=
  fun _ => (bothOrders_of_torusDecay ha h).1

/-- **Route B adds nothing to the vacuum sector once route A holds (definitional):** the crossover disjunction of the
assembly is implied by `SlabDecay` alone, whatever `ConjW` says. -/
theorem crossover_of_slabDecay {T : Tuning} (hA : SlabDecay T) : SlabDecay T ∨ (ConjW T ∧ SectorTransfer T) :=
  Or.inl hA

end ProofPhase.RouteB
