/-
Proof phase, cycle 2, workstream C: the top-level assembly theorem (2026-11-22). Released under Apache 2.0.

Field-by-field map to the blueprint: `docs/mass-gap/weak-coupling/proof-phase/ASSEMBLY.md`.
-/

import ProofPhase.Torus.Local

/-!
# The assembly: SU(2) Yang–Mills inside the hypotheses, the sharpest open inputs as hypotheses, the gap as conclusion

The open pieces are the structure `ProofPhase.OpenPieces` (`ProofPhase.Assembly`): the line of constant physics `OnLCP`
(with the 4D flux energy in its renormalisation condition), non-triviality `NonTrivial`, and the crossover by its
sharpest open inputs: `BlockedTorusRoute` (`H1Local ∧ LimitDprime ∧ ObsTransferPhys`), `BlockedSlabRoute`
(`H1Local ∧ LimitDprime ∧ ObsTransfer`) or route B (`ConjW ∧ SectorTransfer`). This module holds the top-level theorem
because the blocked route's last link is proved in modules that import `ProofPhase.Assembly`.

* **`yang_mills_assembly : OpenPieces T → MassGapLoc T ∧ LimitRP T ∧ NonTrivial T`**: every continuum limit point
  (volume first, then spacing) has the mass gap for all observables of bounded physical extent, is reflection positive
  (proved) and non-trivial (passed through). The torus form of route A uses
  `ProofPhase.Torus.torusDecayLoc_of_blockedRoute`; the slab form uses workstream 1's
  `ProofPhase.RouteA.slabDecay_of_blockedRoute` (workstream 3's independent proof
  `ProofPhase.Quantum.slabDecay_of_blockedRoute` gives the same and is not imported here); route B uses
  `assembly_routeB`. The slab form and route B give the full `MassGap`; the common conclusion is `MassGapLoc`, the form
  the Clay gap needs (density of bounded-extent local vectors, see `ASSEMBLY.md`).
* **`yang_mills_assembly_torus`**: with the torus form of route A, the open pieces hold and the conclusion holds in
  **both orders of limits**: `TorusDecayLoc` (level-uniform constant), `MassGapLoc` (volume first) and `MassGapMFLoc`
  (spacing first at fixed physical volume, then volume: the order of the OpenAI construction).
* The pure-noise check is unchanged: `ProofPhase.not_trivial` (pure noise, and every bounded coupling, fails
  `OpenPieces` through `OnLCP.running`), restated here as `not_trivial_top`.
-/

open Filter Topology

noncomputable section

namespace ProofPhase

/-- **The assembly theorem.** For SU(2) lattice Yang–Mills (Wilson action, 4D tori) along a tuning `T`: if the open
pieces hold, every continuum limit point (volume first, then spacing) has a mass gap for every slab observable family of
bounded physical extent (`MassGapLoc`, one rate for all extents), is reflection positive (`LimitRP`, proved) and is
non-trivial (`NonTrivial`, passed through from P6.2). -/
theorem yang_mills_assembly {T : Tuning} (P : OpenPieces T) : MassGapLoc T ∧ LimitRP T ∧ NonTrivial T := by
  rcases P.crossover with ⟨B, lam, Vk, Vinf, hlam, h1, h2, h3⟩ | ⟨B, lam, Vk, Vinf, hlam, h1, h2, h3⟩ | ⟨hW, hS⟩
  · exact ⟨(Torus.bothOrdersLoc_of_blockedRoute P.lcp.tendsto_a B hlam h1 h2 h3).2.1, limitRP T, P.nontrivial⟩
  · exact ⟨massGapLoc_of_massGap (RouteA.massGap_of_blockedRoute P.lcp B hlam h1 h2 h3).1, limitRP T, P.nontrivial⟩
  · exact ⟨massGapLoc_of_massGap (assembly_routeB P.lcp hW hS).1, limitRP T, P.nontrivial⟩

/-- **The assembly in both orders of limits** (route A, torus form): on a line of constant physics, with
non-triviality, `H1Local ∧ LimitDprime ∧ ObsTransferPhys` for a reflection-respecting blocking give the open pieces,
torus decay with a level-uniform constant for bounded physical extent, the gap volume first and spacing first, and
reflection positivity of the limit. -/
theorem yang_mills_assembly_torus {T : Tuning} (hL : OnLCP T) (hN : NonTrivial T) (h : BlockedTorusRoute T) :
    OpenPieces T ∧ Torus.TorusDecayLoc T.toV ∧ MassGapLoc T ∧ Torus.MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T := by
  obtain ⟨B, lam, Vk, Vinf, hlam, h1, h2, h3⟩ := h
  obtain ⟨hT, hVF, hMF⟩ := Torus.bothOrdersLoc_of_blockedRoute hL.tendsto_a B hlam h1 h2 h3
  exact ⟨⟨hL, hN, Or.inl ⟨B, lam, Vk, Vinf, hlam, h1, h2, h3⟩⟩, hT, hVF, hMF, limitRP T, hN⟩

/-- **The assembly through the slab form of route A** (full slab class, volume first only). -/
theorem yang_mills_assembly_slab {T : Tuning} (hL : OnLCP T) (hN : NonTrivial T) (h : BlockedSlabRoute T) :
    OpenPieces T ∧ SlabDecay T ∧ MassGap T ∧ LatticeGap T ∧ LimitRP T ∧ NonTrivial T := by
  obtain ⟨B, lam, Vk, Vinf, hlam, h1, h2, h3⟩ := h
  have hS := RouteA.slabDecay_of_blockedRoute B hlam h1 h2 h3
  obtain ⟨hM, hLG, hRP⟩ := assembly_routeA hL hS
  exact ⟨⟨hL, hN, Or.inr (Or.inl ⟨B, lam, Vk, Vinf, hlam, h1, h2, h3⟩)⟩, hS, hM, hLG, hRP, hN⟩

/-- **Non-triviality of the hypotheses (re-checked after cycle 2):** the pure-noise family `β_k = 0` does not satisfy
the open pieces, whatever the crossover option. -/
theorem not_trivial_top (T : Tuning) (h0 : ∀ k, T.β k = 0) : ¬ OpenPieces T := not_trivial T h0

end ProofPhase
