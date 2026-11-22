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
| P3.2 | Lemma T (relative closeness survives blocking, uniformly in the boundary) | Lean (`ProofPhase/Quantum/LemmaT.lean`, instantiated for SU(2) Wilson; part (b) for image variables paper) | `proof-phase/ws3-quantum/NOTE.md` |
| P3.3 | per-volume gap theorem joining P3.1 to P2.3 | Lean (`NoisyBlocking.perVolumeGap`, conditional on H2-all: D′ for every mesh limit point, one γ for all volumes) | `ProofPhase/Quantum/PerVolume.lean` |
| P3.5 | `H1Local` split (cycle 3, c3d): `H1Local` ⇔ representation ∧ bounded pair sums ∧ small tails ∧ uniform near convergence (`h1Local_iff_split`); `H1Local` ⇐ representation ∧ uniform envelope `EnvelopeW` (λ′ > λ) ∧ per-volume convergence ∧ `NearStable` (`h1Local_of_quasiLocal`). Per volume, D′ from a level k₀(j) ~ |Λ_j|·e^{λ diam_j}: the whole gap is volume-uniformity (the tail clause). Two segments: lattice spacing → L_* (ḡ small; `EnvelopeW` plausible from Balaban/OpenAI upper bounds, Kotecký–Preiss, paper) and L_* → L₁ (fixed number of steps, coupling of order one; large fields and crossover are one obstruction there). Upper bounds suffice for the envelope; ratio bounds only for volume-uniform convergence | Lean (split and sufficient condition); `EnvelopeW` at L₁ open | `ProofPhase/H1/Split.lean`, `proof-phase/c3d-h1/NOTE.md` |
| P3.4 | ultraviolet stability, small-field control, one-loop running | external (OpenAI construction, read at stage level; controls the weak-coupling unit scale, not L₁); Balaban's published results give stability of the partition function, not of correlation functions | `H1-OPENAI.md` |

### P4. The crossover (open; the core)

| piece | statement | status | where |
|---|---|---|---|
| P4.1 | Route A, **gap strength** (free win 2): torus slab covariances of the Wilson theory along the line of constant physics decay at one physical rate, any prefactor (`LevelDecay`, what `corollaryB_lattice` consumes). Sufficient conditions: D′ at L₁ (stronger than the gap, false below 1/T_c), or D′ on centre-blind (SO(3)) block variables (free win 4, to check) | open | `ROUND-3.md`, `attempts/r4-review/FREE-WINS.md` |
| P4.1′ | blocked route (Lean, `slabDecay_of_blockedRoute`): good blocking ∧ `H1Local` ∧ `LimitDprime` ∧ `ObsTransfer` ⇒ `SlabDecay`; with `ObsTransferU` ⇒ `TorusDecay` (both orders of limits). Refined D′ (paper): a centre half (confinement-type; proxy holds from L₁√σ ≈ 2–2.5) and an **adjoint half, the real obstruction** (proxy factor ~6 short at L₁√σ = 3); centre-blind D′ alone fails the photon test | open: `H1Local`, `LimitDprime` (adjoint half), `ObsTransfer(U)` | `ProofPhase/RouteA/BlockedSlab.lean`, `proof-phase/ws1-routeA/NOTE.md` |
| P4.1″ | `LimitDprime` ⇐ AdjointHalf ∧ CentreHalf (γ_A + γ_C < 1) (Lean, `limitDprime_of_halves`, `blockedTorusRoute_of_halves`); two-type Dobrushin (Lean, `decay_twoType_blocks`); W₁ form valid on SU(2) sites with H1 in a Lipschitz norm. Leg C at β 2.3: halves not excluded from L√σ ≈ 2.5, but the deterministic block variable's adjoint signal is consistent with zero there (**noise-limit trap**: a Dobrushin condition at L₁ becomes cheap when the blocking loses the signal, and the difficulty moves into the observable transfer). Real test: refit with the good blocking and a ≥ 3σ content check | open | `ProofPhase/Adjoint/`, `proof-phase/c2a-adjoint/NOTE.md` |
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
| P5.1′ | Conjecture S (sector transfer for simple groups, from the owner's reading): `AreaLaw → MassGap` | open; breaks exactly at small loops (`areaLaw_iff_large`: the area law is silent on loops below a fixed area, while the gap is decided on generators, `norm_pow_le_of_generators`, and loops of ≤ 3 plaquettes generate); a reflection-positive, invariant mixture has an area law and no gap (`not_expDecay_mix`); Heller's SU(3) endpoint (numerical). Lands on Route A: the gap is decay of small Wilson loops at one rate | `ProofPhase/SectorS/`, `proof-phase/c2b-conjS/NOTE.md` |
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
| P6.5 | infinite-volume limit | external, subsequential; ours: limit states exist (Lean, weak convergence, `exists_limitState`); invariance of the limit state paper; `MassGapMF` does not need uniqueness |
| P6.6 | Wightman reconstruction | external for their selected phase; standard for ours once OS axioms hold on a field algebra |
| P6.7 | tuning / line of constant physics | open; slope corrected (our β = 2/g², slope 11/(6π²)); relation of their β(unit) = bar to our act-number condition open |
| P6.8 | local gauge-invariant fields as distributions | external, partial (their fixed-stencil insertions); adopt as our field notion |
| P6.9 | short-distance agreement | external, partial |
| P6.10 | every compact simple G | existence external; `plaqLaw_eq_wilsonMeasure` generic; our `Tuning` SU(2) only |
| P6.11 | order of limits | `TorusDecay` (level-uniform constant) ⇒ `MassGap` ∧ `MassGapMF` (`bothOrders_of_torusDecay`, Lean); `SlabDecay` reaches only ours |
| P6.12 | observable bridge: our bounded slab observables vs their unbounded local fields | open (ratio/L² form of lattice decay: paper sketch) |

### P7. Assembly (after cycle 2, workstream C)

| piece | statement | status |
|---|---|---|
| P7.1 | `yang_mills_assembly` (`ProofPhase/Torus/Top.lean`): `OpenPieces` ⇒ `MassGapLoc` (one rate for every slab observable of bounded physical extent) ∧ `LimitRP` ∧ `NonTrivial`. `OpenPieces` = line of constant physics (one-loop running with slope 11/(6π²); act number L·`fluxRate` → z⋆ > 0) ∧ `NonTrivial` ∧ crossover, one of: **torus route** (good blocking ∧ `H1Local` ∧ `LimitDprime` ∧ `ObsTransferPhys`), slab route (same with `ObsTransfer`), Route B (`ConjW` ∧ `SectorTransfer`) | Lean |
| P7.2 | `yang_mills_assembly_torus`: the torus route gives `TorusDecayLoc` and the gap in **both orders of limits** (`MassGapLoc` ∧ `MassGapMFLoc`) | Lean |
| P7.2′ | `yang_mills_assembly_level` (cycle 3, c3d): the route uses `H1Local ∧ LimitDprime` only through D′ of the blocked lattice laws themselves. `LevelDprime` (D′_λ with one γ < 1, every level k ≥ k₀, every volume; no limit) ∧ `ObsTransferPhys` ∧ LCP ∧ `NonTrivial` ⇒ `TorusDecayLoc` ∧ `MassGapLoc` ∧ `MassGapMFLoc` ∧ `LimitRP` ∧ `NonTrivial`; `levelTorusRoute_of_blockedTorusRoute` (the old route implies the new). A reshuffle of open inputs, not a discharge: drops only existence and uniqueness of a limit effective action at L₁ | Lean (`ProofPhase/H1/Level.lean`) |
| P7.3 | non-triviality: pure noise and every bounded coupling fail `OpenPieces` (`not_trivial`) | Lean |
| P7.4 | the blocked route's last link, twice independently (`RouteA/BlockedSlab.lean`, `Quantum/BlockedRoute.lean`); with `ObsTransferPhys` to `TorusDecayLoc` (`Torus/Local.lean`) | Lean |
| P7.5 | `MassGapLoc` ⇒ spectral gap needs density of bounded-extent local vectors in the reconstructed space and the reconstruction itself | paper |
| P7.6 | rotation invariance, uniqueness of the limit, other compact groups | open |

**Cycle 3 update (c3d):** with `yang_mills_assembly_level` the torus route's open inputs are `LevelDprime` (D′ along the levels at L₁, uniform in the volume), `ObsTransferPhys`, the line of constant physics and `NonTrivial`; `H1Local` becomes one sufficient condition (with `LimitDprime`). Suggested for cycle 4: one hypothesis `CondMass` (the fine field conditioned on the block field has a uniform mass at the block scale) feeding both `EnvelopeW` and `ObsTransferPhys`(c).

**Cycle 3 update (c3a):** `ObsTransferPhys` is reduced (Lean, `ProofPhase/UV/Split.lean`, `twoStage_blocked`) to **Lemma UV** (ultraviolet, weak coupling up to L₀ = L₁/2^r; needs b₀ > 0 and Balaban-type large-field bounds extended to conditional correlations; Gaussian level verified numerically in the time direction) and **Lemma X** (the L₀ → L₁ crossover, not ultraviolet at the L₁ where `LimitDprime` can hold). Difficulty conservation (Lean, `condDefect_eq`): given `LimitDprime`, part (c) holds iff the fine covariance decays; for decimation `ObsTransferPhys` is the gap. The noise-limit trap is the information bound |(c) − Cov| ≤ ‖E[F|Φ] − EF‖₁ (`abs_condDefect_sub_cov_le`). Good-blocking design (P1.8, Gaussian, exploratory): the staple kernel at w = 1/2 is exactly blind to the spatial checkerboard at the coarse zone corner; w = 0.1 sees it but drifts towards decimation; w = 2 (the refit's weight) keeps rank 3 at the corner with a weak mode about 5 % of the others, stable in ℓ. Proposed: `ObsTransferPhysT` (time-separated pairs only; the assembly uses only those) and a Route A′ with a super-site condition at L₁.

**Cycle 3 update (c3c):** the adjoint coefficient is exactly k_A = 1/16 (paper proof, checked numerically), so the linearised window is exactly β_A < 1/3. Certified by interval arithmetic (`proof-phase/c3c-certified/`): the **W₁** single-link Dobrushin column of the two-coupling action is < 1 for −0.22 ≤ β_A ≤ 0.21 at β_F = 0, with six certified (|β_A|, |β_F|) corners; ceiling: the criterion fails at β_A ≥ 0.275 and ≤ −0.29 (explicit configurations). The sup-form `AdjointHalf` of `CentreSplit.lean` is false for |β_A| ≥ 0.0834 in this family, so Lean (`ProofPhase/Certified/AdjointW.lean`) proves the W₁ form: `CertifiedAdjointW` (the computer-assisted input, a named hypothesis) ⇒ `LimitDprimeW` and volume-uniform decay for every action in the window. The W₁ route needs `H1LocalLip` (H1 in a Lipschitz norm; openness bound on paper) instead of `H1Local`; the W₁ blocked route is paper only. Statements about the effective action only, far weaker than the gap.

**GPU results (2026-11-22):** Leg C (deterministic block variable): pre-registered β-scaling check FAILED, click table indicative only (near-noise variable). Good-blocking refit (c3b, strict content rule): one counted point, β = 2.3, **L√σ = 2.80**, content PASS (adjoint ts at 3.7σ); H_TV 2.37 EXCLUDED (centre half binds), linearised H_W 0.676 NOT_EXCLUDED: **the W₁ window is reached, the sup window is not**, so the route needs the W₁ form (`LimitDprimeW`, `H1LocalLip`). Scaling check consistent. Open: certify the W₁ column for the measured anisotropic action (β_F ss 0.171 lies outside c3c's certified β_F range), and the truncation (large closure residuals). Act-number queue stopped after its bench (19.7 h projected; per-sweep overhead to fix).

**Cycle 4 (2026-11-22): assembly v3, the two segments, the certified measured point.**
- **Assembly v3 (c4a, `ProofPhase/V3/`, 43 theorems):** `yang_mills_assembly_v3_W1` has the open inputs `OnLCP`, `NonTrivial`, `H1LocalLipW` (W₁ closeness of the blocked actions to their limit), `LimitDprimeW` (W₁ Dobrushin at L₁; or `CertifiedAdjointW` in a certified corner), `CondMassAnn` (annealed conditional covariance of time-separated observables given the block field decays) and `ObsQuasiLocTW` (parts (a), (b) of the transfer). Time-separated observables suffice for the torus route (`ObsTransferPhysT`). `CondMass` (cell Dobrushin, quenched) ⇒ `CondMassAnn` ⇒ part (c); it does **not** give (a), (b) for a deterministic blocking, and `CondMass ⇒ EnvelopeW` is paper only (needs a noisy local blocking and the quenched form). Honest reading: `CondMassAnn` is close to a restatement of part (c); its point is that it should be gap-free (holds for the photon); the gap content stays in `LimitDprimeW`/`LevelDprimeW`.
- **Segment 1 (c4b, `ProofPhase/Seg1/`, 76 theorems):** Kotecky–Preiss in Lean (configuration-dependent hard-core gas, cluster bound ≤ log 2, volume-uniform) and the bridge `PolymerRepW` (named hypothesis, the target form of Balaban-type small/large-field bounds) ⇒ `EnvelopeW` at L_* uniformly in level and volume. Correction to c3d §1.4: the exact-cover large-field gases used by Balaban and the OpenAI note need a **lower** bound on single-block weights (or Balaban's exponentiation); upper bounds suffice only for weight-1 gases. Blocking mismatch: bridge by the composite `B_good ∘ B_Balaban` (obligation: Balaban's averaging is an `RPBlocking`). Lemma UV (fine field given block field, two observables) is not in the literature for non-abelian gauge fields: a paper-sized extension, not a new non-perturbative problem. Balaban's papers were not read in full text (zbMATH reviews and memory, marked as such).
- **Segment 2 (c4c, `ProofPhase/Seg2/`, 14 theorems):** Lemma X stated as smoother (filter) stability in Euclidean time (hidden state = fine slice, observations = block links; Markov split along slices). Filter stability does not carry segment 2 by itself: the volume-uniform theorems need a Dobrushin condition (= `CondMass`), and Rebeschini–van Handel (EJP 2015) show exact strong observations of composites can destabilise the filter, so `CondMass` must be annealed. New unit test: **unobserved symmetry** (a centre-blind blocking in the deconfined phase: (c) fails). GPU test of `SmootherStable` pre-registered, needs new code, not run.
- **Certified measured point (c4d, `Certified/Measured.lean`):** the nonlinear W₁ column (both halves, sup over conditional laws) of the fitted action at **L√σ = 2.80**, certified over the ±3σ box: base **0.732**, ext_T 0.761, ext_R 0.964, ext_TR 0.99988 (knife edge: inconclusive over the box, < 1 at the central fit). Lean: `CertifiedMeasured` (named hypothesis) ⇒ `LimitDprimeW` and uniform decay for every action in the box (plaquette fits). Truncation margin: a further centre-charged loop family with coupling above about 0.0013 would push the column past 1. Isotropic certified b_F window at β_A = 0: 0.0685 → 0.1924. Statement about the fitted, truncated action only.
- **Act number:** per-sweep overhead removed (`SPEEDFIX.md`; plan 1.46 h instead of 19.7 h; equivalence checked). Rerun 12:00: **photon gate FAILED** (L = 8, 10 not counted: cold-start and hot-start chains disagree); queue stopped by the rule before any SU(2) run. Diagnosis (old code and 10× thermalisation give the same split): not the speed fix, not thermalisation; likely frozen U(1) flux sectors in the Coulomb phase, contradicting the pre-registration's "no barrier" assumption. Remedy is a pre-registration change, put to the owner (`attempts/r4-actnumber/PREREG.md`).

**The open inputs, as of cycle 4** (`yang_mills_assembly_v3_W1`): `OnLCP`, `NonTrivial`, `H1LocalLipW` (segments 1 and 2), `LimitDprimeW` (segment 2, the crossover: the gap content), `CondMassAnn` (segments 1 and 2; gap-free if the blocking keeps content), `ObsQuasiLocTW` (Lemma UV in segment 1, Lemma X in segment 2). Segment 1 is reduced to `PolymerRepW` (a published-bound reading plus a lower-bound lemma) and the conditional extension; segment 2 is the core obstruction.

**After cycle 4: the Fable review and blueprint v4 (`proof-phase/c4-fable/`).** The current map is `proof-phase/c4-fable/BLUEPRINT-v4-DRAFT.md` (owner-approved as the basis of cycle 5), with the cycle-5 corrections below. In one line: every route ends at one statement of gap strength, the lattice gap for block observables at one weak-coupling scale L_* uniformly in the volume (IR); nothing in the map proves it; the reachable result is a machine-checked "ID ∧ UV ∧ IR ⇒ gap". Review findings confirmed by the coordinator in the source: the v3 W₁ inputs could not be met by the true theory as stated (finite range, plaquette-only limit, bounded potential for a deterministic blocking).

**Cycle 5 (2026-11-22).**
- **Assembly v4 (c5a, `ProofPhase/V4/`, 26 theorems):** `yang_mills_assembly_v4(_bdd)`: `OnLCP'` ∧ `NonTrivial` ∧ `ObsTransferPhysTW` ∧ **`BlockGapBddW`** (the one gap-strength input, named; `BlockGapUnifW` implies it) ⇒ the gap in both orders of limits. `OnLCP'` (two-sided act-number bound) is implied by `OnLCP` and suffices everywhere. The drafted recursion lemma was false; the corrected one (`LevelDprimeWOn` at L₁ + `StageTwoW` ⇒ `BlockGapBddW` at L_*) is proved: cycles 2–4 are now strategy (a) for IR. Open bookkeeping: the L_* → L₁ blocking for every volume (cells of two sizes). Segment 1 is stated on the L_* laws (`UV1Polymer`) but has no consumer yet.
- **Repairs (c5c, `ProofPhase/Repair/`, 50 theorems):** weighted W₁ Theorem A (no finite range; `LevelDprimeWw`), general-support reference actions (`RefDprimeWw`, `CloseWw` replace `LimitDprimeW`/`H1LocalLipW`), noisy reflection-positive blocking (`noisy_blocked_wilson_rp`, blocked laws Gibbs given a kernel density), bridge to `BlockGapBddW`. Old statements are special cases. Open: the kernel density of heat-kernel noise (paper).
- **Segment-1 supplier and rare defects (c5d, `ProofPhase/Defects/`, 31 theorems):** the OpenAI construction gives the defect form of UV1 except (G1) a probability bound on the bad set, (G2) closeness to one fixed Wilson β, and only at g² ≲ 4·10⁻⁶ (G3). Balaban not yet read in full text (download script `c5d-supplier/get-balaban.ps1` for the owner). `UVRepDefect` ⇒ dominated bad-set law (Lean). The rare-defect Dobrushin theorem bounds the averaged conditional covariance only; the environment term is a separate input (mixture counterexample); it applies at a strong-coupling scale, not at L_*.
- **DMP-native line (c5e, `ProofPhase/DMP/`, 30 theorems):** vacuum act number z₀ (attained box gap of centre-even observables), doubling theorem `su2_box_gap_of_DS_DT` (start + doubling law with summable loss ⇒ one gap for all dyadic boxes); frozen (photon, z₀ = 2π) and bounded act numbers fail it in Lean. The cross-volume step D-T is the inequality left unproved in Tomboulis' argument; DMP names it, does not supply it; every DMP object formalised so far is group-blind. Joint z₀/z_e measurement pre-registered (about 2.5 GPU h), waiting on the owner's photon-control decision (A: exact formula).
- **Block-field content (c5b):** CPU regression lower bounds on R² find content only at b = 2; the photon control failed, so the b ≥ 4 zeros are inconclusive; R² alone cannot decide Lemma X (the conditioned share R_c(D) does). GPU conditional-replica measurement pre-registered, not run (about 14 h); next: make the photon control see long-wavelength content first.
- **Owner readings (PREP.md, cycle 5):** two clocks (universal information tick 1/e, gravitational existence tick = curvature), confinement as forced-binary existence with a spanned boundary, crossing an existence boundary (only existence crosses; act = information in nats across the dimension swap; loss = entropy), and the possibility space with the reflected assertion: the corner restated as the **flip probability** of the binary flux sector across a box, p(L) = 1/(1 + e^{F_tw(L)}), bounded above by ½ through reflection positivity (proved) and needing a floor that does not fade with L (open; Tomboulis' vortex criterion).

**Cycle 6 (2026-11-22): the flip probability, the doubling law with loss, Balaban.**
- **Flip probability (c6a, `ProofPhase/Flip/`, 60 theorems):** p = Z_tw/(Z_tw + Z) on the SU(2) Wilson chain; `su2_flipProb_le_half` (Z_tw ≤ Z, even time extent, every β; false for odd extents at β < 0). Identities 1 − 2p = e^{−F_e}, ½ − p = ½·tanh(F_tw/2). A floor on p is equivalent to a bounded twist free energy and is too weak (photon, 2I); saturation p → ½ gives confinement (Tomboulis–Yaffe, paper), **not the gap**: p is centre-odd and the 0⁺⁺ sector is blind to twists (counterexamples: photon, SU(2)×U(1), Heller endpoint). **The gap target in Lean: `su2_gap_of_doubling_defect`** — z₀(2L) ≥ 2z₀(L) − c with c < z₀(L₀) ⇒ E₀ ≥ (z₀(L₀) − c)/L₀ on all larger dyadic boxes, with decay of all centre-even correlations. The DMP "not lowering" reading is a gluing deficit δ(L) between a box and its mirror (`gap_of_deficit`, finite-spectrum level); bounding δ(L) is the content.
- **Data (c6b):** no direct SU(2) Z_tw/Z measurement exists; via the Lean duality, p stays at ½ (0.486–0.500) on L√σ 2.1–4.2 and the flux act grows ≈ (L√σ)² − 0.9; no data below 2.1. A bare floor separates nothing (photon, finite groups have one too).
- **Literature (c6c):** Tomboulis' failing step is one comparison inequality (Ito–Seiler (3.5)), proved only at strong coupling and group-blind as used. Exact super-additivity of z₀ is **false** (box gaps approach m from above in exactly gapped models; SU(2) small boxes); the repaired form with a fixed loss is the doubling law above. The flux act is super-additive. Candidate F2 (centre-layer comparison to Z₂ by Ginibre + Griffiths II) gives confinement from one block scale (now c7b).
- **Content (c6d):** improved instrument sees photon content at b = 4, but its pre-registered photon gate still fails narrowly; SU(2) not run; the content question stays with the GPU conditional-replica measurement.
- **Bookkeeping (c6e, `ProofPhase/Book/`):** the noisy good blocking's laws are Gibbs measures with no named hypothesis (von Mises–Fisher noise); strategy (a) holds for every volume (two-size cells).
- **Balaban (read in full, c5d-supplier/BALABAN-READING.md):** his large-field control preserves partition functions, not laws; no probability bound on large fields; history-based bad sets not rare in 4D; stability conditional on CMP 109 Theorem 2 (proof announced, never published; checked). No later work supplies a law-level version (c6f LITERATURE). **M1** (law-preserving R step): one-step paper test SURVIVES WITH A NEW LEMMA (core dilution), about 35–45 new pages (c6f ONE-STEP); its tools are being built in a background thread (m1-tools).
- **Owner readings (PREP.md, cycle 6):** the floor holds by causality; light only exists (a point, one quantum 2π), a duality has existence (an arrow, two assertions); the fixed loss is the cost of asserting existence over the doubled possibility space. In the doubling law: loss ≤ one quantum, start box ≥ two quanta (z₀(L₀) ≥ 4π) ⇒ gap ≥ 2π/L₀. Data: z₀ ≈ 7.2 at L√σ = 2.1 (a flux pair), ≈ 13 at 3.5.
- **Running:** the joint z₀/z_e measurement (9 doubling pairs, photon control by the exact formula, owner's decision) measures the per-doubling loss and the start box directly; c7a (flux act ⇒ vacuum doubling?), c7b (centre-layer comparison in Lean).

**Cycle 7 (2026-11-22): the one-box route, the centre layer, the joint measurement.**
- **Joint z₀/z_e measurement (c5e, result):** all six resolved doubling pairs DOUBLE; the per-doubling loss is negative on L√σ 1.03–4.20; z₀ crosses 4π between L√σ 2.92 and 4.13; scaling holds only at 4.1–4.2. c7a's predictions scored: P3, P5 confirmed, P1 refuted, P4 split, P2 not resolved.
- **Centre layer (c7b, `ProofPhase/Centre/`):** comparison of the binary centre layer to Z₂ by Ginibre and Griffiths II, `centre_area_law`.
- **One-box criterion (c7c, `ProofPhase/OneBox/`, 39 theorems):** `yang_mills_assembly_onebox`: `OnLCP'` + `NonTrivial` + `FineOneBox` ⇒ gap in both orders of limits, with no blocking and no UV transfer input. The criterion is Dobrushin–Shlosman type and gauge-correct: Q(ℓ) = (1/ℓ⁴)Σκ(u) < 1 over cells of about one correlation length. Its failure mechanisms are theorems: power-law influence (light) and ties (2I, deconfined Z₂). Literature (c7d): Chatterjee 2021 Def. 2.3 ⇒ Thm 2.4 gives confinement from the same kind of condition.
- **Numerics (c7b-onebox-num):** Tier 1 was exploratory by pre-registration and stopped on the owner's decision after a roughly 100-fold runtime overrun; the logs are kept.

**Cycle 8 (2026-11-22/23): saturation, the concrete one-box route, the strict flip bound.**
- **Vortex saturation (c8a, `ProofPhase/Saturation/`):** `vortex_saturation`. For any group with a central involution, |Z − Z_tw| ≤ satB(Z + Z_tw) (Tomboulis–Yaffe area-rate form) inside an explicit window. A split criterion `FineOneBoxSplit` (centre budget γ_Z + adjoint budget γ_A < 1) ⇒ gap. The named SU(2) hypothesis is H_sat (centre layer weakly coupled at block scale). The adjoint half γ_A is not supplied: fitted-action coefficients are not worst-case bounds.
- **One-box route concrete (c8c, `ProofPhase/OneBox2/`):** the actual Wilson box law (DLR, gauge covariance) ⇒ `WilsonOneBox` ⇒ gap; a strong-coupling anchor shows the criterion is non-empty; the wall-cut version ⇒ area law, given Chatterjee's Theorem 2.4 as a named external input.
- **Strict flip bound (c8d, `ProofPhase/Flip/Strict.lean`, 91 theorems):** `su2_Ztw_lt_Z`, `su2_flipProb_lt_half` for every β ≠ 0 (equality at β = 0). It gives no size control: the strict "existence is always ahead" of the owner's reading.
- **Decisive-test tools (c8b):** the coupling upper bound is vacuous above β ≈ 0.25 (SU(2)), and the tie test is validated on Z₂. SU(2) at β 2.3 shows no tie on boxes 5 and 9. The GPU queue was stopped with the one-box queue; neither is needed for the proof.
- **Interface (`ProofPhase/Interface/`):** the assembly is proved for measurable and for randomised blockings, with the same conclusions (`yang_mills_assembly_v4_bdd_meas`, `_rand`). `spectral_upgrade` turns decay on a dense class into uniform decay without the spectral theorem; it must be applied uniformly in the volume or in the limit, never on one fixed torus.

**M1 (2026-11-22/23): the law-preserving large-field step, complete at paper level.** Redesigned after REVIEW-1 found a fatal counting error in the trapping design. The current main line (`proof-phase/m1-tools/M1-PLAN.md` §0, `UV-TV.md` §37):
- **The split and the decoder:** SU(2) = SO(3) × closed Z₂ layer; a local decoder (nearest closed layer) blocked by mod-2 Stokes.
- **Averaging and law preservation:** Balaban's average on SO(3), with deep plaquettes excised for one step; the conditional step for exact law preservation.
- **Release and carrying:** every large field is released into R-terms; long-lived sheets are carried by attribution; labels form a positive gas with a one-box contraction.
- **Hand-over at L_*:** the law in inductive form, the L¹ transfer for block observables, and (Lemma UV-TV) OS-norm density of the block observables. Density is obtained by a coupling-form Dobrushin–Shlosman theorem (Lean, `OneBox/CouplingDS.lean`, 37 theorems) with composite boxes (bad cluster + collar, Lemma C), a polymer-level pattern gas (Kotecký–Preiss, van den Berg–Maes), a front-advance recursion, and the law of total covariance along the scales.
Three independent reviews (REVIEW-1 to -3, with follow-ups) and an independent reading of Balaban's normalisation terms (`m1-review/EK-DERIVATION.md`) leave no open FATAL or GAP finding. M1 rests on:
- Lean (57 + 37 theorems);
- one re-proof: (c), [V] (1.80)–(1.97) with a kept slack e^{−c p₀²} per birth-scale cube, checked three ways;
- citations;
- three citation-level readings: what E_k(Z) is, admissibility, and the rim S(Z)\Z;
- two citation-level uses: the label term and R7′;
- two adaptations: Balaban's machinery on thin shells, and the SO(3) carry-over;
- external: [I] Theorem 2 with its rate.

**The open inputs, as of M1:**
- **ID:** `OnLCP'`, `NonTrivial`.
- **UV:** supplied by M1 at paper level, up to its named readings and adaptations. Owed: the Lean instantiation of the coupling theorem, and the interface change to the (SO(3), closed Z₂) block state with `MassGapLoc` reached through the limit.
- **Crossover P4 (L_* → L₁):** open; this is the core.
- **IR:** `BlockGapBddW` / the one-box route: `FineOneBox` along the continuum line, with the adjoint budget γ_A and H_sat open.
- **External:** [I] Theorem 2.

**The open inputs, as of cycle 6:** ID (`OnLCP'`, `NonTrivial`); UV (`ObsTransferPhysTW`; segment 1 needs M1 + M2); IR = `BlockGapBddW` at L_*, in its sharpest form now the two premises of `su2_gap_of_doubling_defect`: a bounded loss per doubling (the cross-volume step) and a start box with act above the loss.

**The open inputs of the preferred (torus) route, as of cycle 2:** `H1Local` (quantum half at L₁, uniform in the lattice), `LimitDprime`
(the Dobrushin condition at L₁; its core is the **adjoint half**, cycle 2 workstream A), `ObsTransferPhys` (ultraviolet quasi-locality of
the good blocking), the line of constant physics, and `NonTrivial`.

## Unit tests (every claimed discharge)

Added in cycle 2: **mixture test** (a reflection-positive invariant mixture of two states: area law, no gap) and **Heller endpoint** (a simple-group local action with finite string tension and massless 0⁺⁺, numerical). Photon, Z₂ (and its gap without a flux floor), finite subgroups of SU(2) and the order-12 binary dihedral group, deconfinement,
triviality, Banks–Zaks. A group-blind theorem passes them all and proves nothing about Yang–Mills: say so when it happens.

## The owner's readings that organise the map (`PREP.md`)

Act identity (P4.2), the act conserved because it runs (P1.5″, P4.7), tie to G0 = inward reach (P3.4), outward reach = confinement
(P4.2), inversion = duality (P1.4′), something must run (P4.6), the centre reached through the causal round trip (necessary condition in
P4.2), Gauss's law as internal verification (P1.3′), what exists is the finite-depth family (P6.1, P6.7).
