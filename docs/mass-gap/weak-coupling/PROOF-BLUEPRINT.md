# Proof blueprint (the map of the proof phase; version 2, 2026-11-22, after the round-4 review)

The Clay statement (Jaffe–Witten): for every compact simple gauge group G, a quantum Yang–Mills theory on ℝ⁴ exists (satisfying the
Osterwalder–Schrader or Wightman axioms, with local gauge-invariant fields) and has a mass gap Δ > 0. We work with SU(2) first and state
which pieces generalise. Statuses: **Lean** (machine-checked, content as stated), **Lean (definitional)** (machine-checked but true by
definition or for any model: no physics content), **paper**, **known** (literature, cited), **external** (a claim read, not built or
verified by us), **numerical**, **open**. Claim discipline: `attempts/RULES.md`; reviews: `attempts/r3-review/REVIEW.md`,
`attempts/r4-review/REVIEW.md` (version 1 of this file joined two routes and overstated statuses; corrected here).

## Two routes, not one

- **Route A (Dobrushin):** build the lattice theory, block it with a good blocking to a physical scale L₁ where the coupling is of order
  one, and show the blocked limit theory satisfies a worst-case Dobrushin condition D′ (P4.1); then block observables decay (P2.3) and,
  with the field and axiom pieces, the gap follows. D′ is strictly stronger than the gap and false for L₁ < 1/T_c.
- **Route B (flux / act number):** show the act number z(L) = E_e·L of the twisted box grows by a margin per doubling (Conjecture W,
  P4.2): that is **flux confinement**, not the gap. Route B reaches the vacuum gap only through the sector transfer P5.1, for which no route
  is known. Deconfined Z₂ has a gap and no flux floor: floor and gap are different properties.

The owner's DMP reading organises both (existence as an act; the act conserved because it runs; tie to G0 = reach; the inversion =
duality), and is recorded in `PREP.md`; it guides, it does not prove.

## Pieces

### P1. Lattice theory and structure

| piece | statement | status | where |
|---|---|---|---|
| P1.1 | Wilson measure on the 4D torus, SU(2) and general compact G | Lean | `formal/AreaLaw/ConcreteSUn.lean`, `formal/OneScale/` |
| P1.2 | reflection positivity, site and link | Lean | `formal/Positivity/` |
| P1.3 | temporal-gauge transfer kernel; centre flip of one row as a symmetry; parity-sector norm ordering | Lean (kernel, symmetry, ordering); Gauss law not formalised; `Z_Wilson = tr(P_G Tⁿ)` not formalised; strict E_e > 0 open | `R4/LayerKernel.lean`, `LayerSector.lean` |
| P1.3′ | the flux energy on the real 4D measure: anisotropic torus as a chain of slices, RP, Hankel identity; for the summed Wilson line (centre-odd) effective masses decrease to `fluxRate ≥ 0` with |h(t)| ≤ h(0)e^{−rate·t} | Lean (`ProofPhase/RouteB/Chain.lean`, `FluxEnergy.lean`); holds for any group, says nothing about the value; uniqueness of the T → ∞ limit open | `proof-phase/ws2-routeB/NOTE.md` |
| P1.4 | sector Fourier identity Z_e = (Z ± Z_tw)/2 | Lean (definitional) | `LayerSector.lean` (`twist_centre_transform`) |
| P1.4′ | 't Hooft duality proper: the lattice rotation maps the temporal twist to the spatial twist on the symmetric box (T = L) | Lean (`tHooft_rotation`, Euclidean form) | `ProofPhase/RouteB/Duality.lean` |
| P1.5 | decimation by 2: gauge covariant, centre-flip and reflection commuting | Lean | `R4/LayerDecimation.lean` |
| P1.5′ | "act conserved": image measures keep total mass | Lean (definitional) | `LayerTransport.lean` |
| P1.5″ | the image of the twisted ensemble is the twist of one local coarse action (real flux-sector transport) | open | `r4-layer/NOTE.md` |
| P1.6 | reflection positivity of a decimated layer, one step | Lean; but decimation at fixed L₁ has a pure-noise limit, so it is not the route's blocking | `decimated_wilson_rp_SU2` |
| P1.8 | **a good blocking**: centre-covariant, reflection-positive at every level, non-trivial continuum limit at fixed L₁ | Lean for the construction (spatial staple smearing within time slices, temporal decimation) and RP at every layer (`goodBlocking_rp`); non-trivial limit: power counting plus a one-loop check; covariance off a null set: paper | `ProofPhase/RouteA/Blocking.lean`, `proof-phase/ws1-routeA/NOTE.md` |

### P2. Decay machinery (Route A, conditional)

| piece | statement | status | where |
|---|---|---|---|
| P2.1 | Dobrushin uniqueness with exponential weights, finite Gibbs systems | Lean | `R3/TailDecay.lean` (`theoremA_w`) |
| P2.2 | D′ ⇒ single-site GDS; openness under local perturbation | Lean | `R3/FlatFactors.lean`, `R3/Robust.lean` |
| P2.3 | decay of block observables from D′ at L₁ | Lean (abstract Gibbs systems; satisfied by pure noise) | `gap_of_localFactorsW`, `continuum_decay` |
| P2.4 | Corollary B: physical units | Lean | `formal/OneScale/CorollaryB*.lean` |
| P2.5 | strong-coupling gap, any compact group; soft swap | Lean / paper (widest window: `OneScale/SingleLink.lean`, 18·tanh(nβ) < 1) | `OneScale/SingleLink.lean`, `AreaLaw.Clustering`, `R2/CouplingSwap.lean` |

### P3. Quantum half (weak coupling)

| piece | statement | status | where |
|---|---|---|---|
| P3.1 | one noisy blocking step: large-field lower bound; per volume W_p by compactness | Lean (core) | `R3/WpNoise.lean` |
| P3.2 | Lemma T (relative closeness survives blocking, uniformly in the boundary) | paper | `r2-stepscaling/NOTE.md` §4 |
| P3.3 | per-volume gap theorem joining P3.1 to P2.3 | paper (reviewer: correct in the order mesh, volume, observable) | `r3-wp/NOTE.md` |
| P3.4 | ultraviolet stability, small-field control, one-loop running | external (OpenAI construction, read at stage level; controls the weak-coupling unit scale, not L₁); Balaban's published results give stability of the partition function, not of correlation functions | `H1-OPENAI.md` |

### P4. The crossover (open; the core)

| piece | statement | status | where |
|---|---|---|---|
| P4.1 | Route A, **gap strength** (free win 2): torus slab covariances of the Wilson theory along the line of constant physics decay at one physical rate, any prefactor (`LevelDecay`, what `corollaryB_lattice` consumes). Sufficient conditions: D′ at L₁ (stronger than the gap, false below 1/T_c), or D′ on centre-blind (SO(3)) block variables (free win 4, to check) | open | `ROUND-3.md`, `attempts/r4-review/FREE-WINS.md` |
| P4.1′ | blocked route (Lean, `slabDecay_of_blockedRoute`): good blocking ∧ `H1Local` ∧ `LimitDprime` ∧ `ObsTransfer` ⇒ `SlabDecay`; with `ObsTransferU` ⇒ `TorusDecay` (both orders of limits). Refined D′ (paper): a centre half (confinement-type; proxy holds from L₁√σ ≈ 2–2.5) and an **adjoint half, the real obstruction** (proxy factor ~6 short at L₁√σ = 3); centre-blind D′ alone fails the photon test | open: `H1Local`, `LimitDprime` (adjoint half), `ObsTransfer(U)` | `ProofPhase/RouteA/BlockedSlab.lean`, `proof-phase/ws1-routeA/NOTE.md` |
| P4.2 | Route B: Conjecture W (summed form W_Σ: z grows by a margin per doubling along the line of constant physics) | open; photon marginality (Villain/free form) and finite-group failure: paper | `r4-conjw/NOTE.md`, `R4/ConjW.lean` (toy) |
| P4.3 | (B1) minimal action on T³×ℝ is 4π²/g² | numerical only; certifiable | `r4-conjw/NOTE.md` |
| P4.4 | (B2) fluctuation prefactor along the line of constant physics (where b₀ enters) | open; needs constructive renormalisation | `r4-conjw/NOTE.md` |
| P4.5 | (B3) order of limits: time to infinity before doubling | open | `r4-conjw/NOTE.md` |
| P4.6 | no infrared fixed point for pure SU(2) | open; not on the critical path to the gap (neither needed nor sufficient) | `r4-minting/NOTE.md` |
| P4.7 | universality of blocked actions up to O(a²) (assumption (U), restated; literally false as "Wilson at another coupling") | open; tested by the act-number collapse | `r4-minting/NOTE.md` |

The one-sided step every route meets: comparing the blocked measure with the original on the same box.

### P5. From block observables / flux sector to the gap

| piece | statement | status |
|---|---|---|
| P5.1 | Route B only: sector transfer, flux-sector gap ⇒ vacuum (glueball) gap | no route through twist or flux inequalities (Kanazawa's twist insensitivity gives only centre-charged decay; the SU(2)×U(1) product theory has flux growth and no gap); discharged only through Route A (`SlabDecay`/`TorusDecay` ⇒ `SectorTransfer`, definitional): **Route B lands on Route A** |
| P5.2 | block observables at L₁ ⇒ all local gauge-invariant observables | paper with a stated gap (`r3-robust/NOTE.md`, H1-fine) |
| P5.3 | the gap for the whole field algebra: one rate for all truncated correlations; uniqueness of the vacuum | open |

### P6. Existence, identification, fields and axioms (updated after workstream 4, `proof-phase/ws4-existence/NOTE.md`)

The OpenAI construction, read in its Lean source (statements verified; proofs not rebuilt by us, their correctness rests on the
committee's audit): for every compact group with simple non-abelian Lie algebra, Wilson law, one-loop tuning, mesh limit at fixed volume
then volume along a subsequence, renormalised local insertions; OS axioms (reflection positivity, translations, O(4)) and Wightman W0–W3
for a selected phase of a phase average; `nonfree`. Not proved there: uniqueness, any decay rate, a gap.

| piece | statement | status |
|---|---|---|
| P6.1 | existence of the continuum limit | external, statement verified in source, for their objects and order of limits; bridge to ours: `ProofPhase/Existence/Bridge.lean` (same lattice law up to β' = n·β, same tori, `VTuning`) |
| P6.2 | non-triviality and uniqueness | non-triviality external for their selected phase (trace two-point asymptotics); open for our `NonTrivial`; uniqueness open (gap ⇒ single phase: paper sketch) |
| P6.3 | OS positivity of the limit | ours Lean (`limitRP`); theirs external |
| P6.4 | Euclidean invariance | external for their objects; not statable for ours (needs P6.8) |
| P6.5 | infinite-volume limit | external, subsequential; `MassGapMF` (their order) does not need uniqueness |
| P6.6 | Wightman reconstruction | external for their selected phase; standard for ours once OS axioms hold on a field algebra |
| P6.7 | tuning / line of constant physics | open; slope corrected (our β = 2/g², slope 11/(6π²)); relation of their β(unit) = bar to our act-number condition open |
| P6.8 | local gauge-invariant fields as distributions | external, partial (their fixed-stencil insertions); adopt as our field notion |
| P6.9 | short-distance agreement | external, partial |
| P6.10 | every compact simple G | existence external; `plaqLaw_eq_wilsonMeasure` generic; our `Tuning` SU(2) only |
| P6.11 | order of limits | `TorusDecay` (level-uniform constant) ⇒ `MassGap` ∧ `MassGapMF` (`bothOrders_of_torusDecay`, Lean); `SlabDecay` reaches only ours |
| P6.12 | observable bridge: our bounded slab observables vs their unbounded local fields | open (ratio/L² form of lattice decay: paper sketch) |

### P7. Assembly

| piece | statement | status |
|---|---|---|
| P7.1 | `ProofPhase.yang_mills_assembly`: for SU(2) Wilson on 4D tori along a tuning, `OpenPieces` (line of constant physics with one-loop running and a converging act number; `NonTrivial`; crossover = Route A `SlabDecay` at gap strength, or Route B `ConjW` ∧ `SectorTransfer`) ⇒ `MassGap` (continuum decay, volume then spacing) ∧ `LimitRP` (proved) ∧ `NonTrivial` (passed through) | Lean (the two routes joined by a case split; they do not compose) |
| P7.2 | Lean content of the assembly: Theorem C removes level-dependent constants and carries decay through both limits (`corr_le_of_decay`, `massGap_of_latticeGap`); `slabDecay_of_uniformGDS` (D′ is a sufficient condition); `blocked_wilson_rp` for any reflection-respecting blocking | Lean |
| P7.3 | non-triviality: pure noise and every bounded coupling fail the hypotheses (`not_trivial`, `not_onLCP_of_bounded`); pure noise does satisfy `SlabDecay` alone, so identification rests on the line of constant physics and `NonTrivial` | Lean |
| P7.4 | the blocked route at L₁ (H1Local ∧ LimitDprime ∧ ObsTransfer ⇒ SlabDecay) | paper only; not in `OpenPieces` |
| P7.5 | not statable on these objects yet: rotation invariance, uniqueness of the limit, the infinite-volume limit as its own piece, the flux energy from the 4D measure (needs anisotropic tori), other compact groups | open (`proof-phase/ASSEMBLY.md`) |

## Unit tests (every claimed discharge)

Photon, Z₂ (and its gap without a flux floor), finite subgroups of SU(2) and the order-12 binary dihedral group, deconfinement,
triviality, Banks–Zaks. A group-blind theorem passes them all and proves nothing about Yang–Mills: say so when it happens.

## The owner's readings that organise the map (`PREP.md`)

Act identity (P4.2), the act conserved because it runs (P1.5″, P4.7), tie to G0 = inward reach (P3.4), outward reach = confinement
(P4.2), inversion = duality (P1.4′), something must run (P4.6), the centre reached through the causal round trip (necessary condition in
P4.2), Gauss's law as internal verification (P1.3′), what exists is the finite-depth family (P6.1, P6.7).
