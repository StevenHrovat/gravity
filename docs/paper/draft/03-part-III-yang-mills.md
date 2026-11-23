# Part III. Yang-Mills: everything reduces to one box at one scale

*Dense skeleton, draft 1, 2026-11-23. Every result with its status and source. Lean paths relative to `docs/mass-gap/formal/`
(note: the modules of the earlier attempt rounds R2 to R4 live under `Attempts/`); notes relative to `docs/mass-gap/weak-coupling/`.
The full chain with all 91 pieces is in `PROOF-BLUEPRINT.md`. Claim labels (III.n) are listed in `../CLAIMS.md`.*

## III.0 What is proved and what is not

**The Clay statement** (Jaffe-Witten): for every compact simple gauge group G, a quantum Yang-Mills theory on R^4 exists, satisfying
the Osterwalder-Schrader or Wightman axioms with local gauge-invariant fields, and has a mass gap Delta > 0.

**This part does not prove it.** It proves, for SU(2):

1. the minting half (I.5): from a gap certificate at one box scale to the mass gap of the lattice theory in both orders of limits,
   with reflection positivity of the limit **[Lean]**, conditional on stated inputs;
2. the global structure of the pressing half: the per-box rate, the conserved carrier, superadditivity along the chain, and the
   uniformity along it, so that the **gap mechanism** reduces to one statement about one box **[Lean]** + **[classical]**.

It leaves open:

* **(O1) the one-box statement** (III.3): the loss rate of one DB is below one at one box scale, for every well-defined outside;
* **(O2) the identification inputs**: the line of constant physics (OnLCP) and non-triviality, the two hypotheses that make the
  lattice family Yang-Mills and not some other gapped family (III.5);
* **(O3) the continuum field theory**: Euclidean invariance, local fields as distributions, uniqueness of the limit and Wightman
  reconstruction. For the external construction this project uses (III.5) these are claimed there **[external]**; for this
  project's own objects rotation invariance cannot even be stated (the lattice has only the hypercubic group) **[open]**;
* **(O4) other groups**: the Lean setting has a tuning for SU(2) only; the SU(N) package and the audit of what generalises are
  partial (`ProofPhase/General/`, `proof-phase/GENERALISE-AUDIT.md`).

"Everything reduces to one box at one scale" is exact for the gap mechanism (O1) and is the sense used in this part's title. It is
not true of the Clay statement as a whole, which also needs O2 to O4.

## III.1 The lattice theory and its positivity (G0 by construction)

| # | Result | Status | Source |
|---|---|---|---|
| III.1.1 | Wilson measure on the 4D torus for SU(2) and general compact G | **[Lean]** | `AreaLaw/ConcreteSUn.lean`, `OneScale/` |
| III.1.2 | Reflection positivity, site and link | **[Lean]** | `Positivity/Wilson.lean` (`wilson_rp`), `Positivity/LinkWilson.lean`, `Positivity/Concrete.lean` (`wilson_rp_SU2`) |
| III.1.3 | Temporal-gauge transfer kernel; centre flip of one row is a symmetry; sector identity Z_e = (Z + Z_tw)/2 | **[Lean]** (identity definitional) | `Attempts/R4/LayerKernel.lean`, `LayerSector.lean` |
| III.1.4 | 't Hooft duality: the lattice rotation maps the temporal twist to the spatial twist on the symmetric box | **[Lean]** | `ProofPhase/RouteB/Duality.lean`, `tHooft_rotation` |
| III.1.5 | A good blocking: centre-covariant and reflection-positive at every level | **[Lean]**; non-trivial limit at fixed L1 **[paper]** | `ProofPhase/RouteA/Blocking.lean`, `goodBlocking_rp`; `proof-phase/ws1-routeA/NOTE.md` |
| III.1.6 | Strict flip bound Z_tw < Z for every beta != 0, every box, every twist position ("existence = non-existence + 1", I.7) | **[Lean]** | `ProofPhase/Flip/Strict.lean`, `su2_Ztw_lt_Z` |

## III.2 The minting half: from a certificate to the gap

| # | Result | Status | Source |
|---|---|---|---|
| III.2.1 | Dobrushin uniqueness with exponential weights; D' gives decay of block observables at one rate (abstract Gibbs systems) | **[Lean]** | `Attempts/R3/TailDecay.lean` (`theoremA_w`), `Attempts/R3/Robust.lean` (`gap_of_localFactorsW`) |
| III.2.2 | Block decay converted to physical units (Corollary B) | **[Lean]** | `OneScale/CorollaryB.lean`, `corollaryB_lattice` |
| III.2.3 | OS route: a windowed block gap gives MassGapLoc and the transfer operator's gap on the reconstructed space | **[Lean]** | `ProofPhase/OS/GapLoc.lean` (`massGapLoc_of_UVTVBlockGap`), `ProofPhase/M1/UVTVOS.lean` (`gap_of_RP`) |
| III.2.4 | The top-level assembly: OpenPieces implies MassGapLoc, LimitRP and NonTrivial; reflection positivity of the limit is proved, not assumed | **[Lean]** | `ProofPhase/Torus/Top.lean` (`yang_mills_assembly`), `ProofPhase/Assembly.lean` (`OpenPieces`) |
| III.2.5 | The gap in both orders of limits (torus route) | **[Lean]** | `ProofPhase/Torus/Top.lean` (`yang_mills_assembly_torus`); `ProofPhase/Existence/Bridge.lean` (`bothOrders_of_torusDecay`) |
| III.2.6 | Non-triviality of the hypotheses: pure noise and every bounded coupling fail OpenPieces | **[Lean]** | `ProofPhase/Assembly.lean`, `not_trivial` |
| III.2.7 | MassGapLoc implies a spectral gap of the continuum Hamiltonian (needs density of local vectors and the reconstruction) | **[paper]**; spectral bridge **[Lean]** | `ProofPhase/Bridge/Spectral.lean`, `ProofPhase/Bridge/OSLink.lean` |
| III.2.8 | Strong-coupling gap for any compact group (widest window 18 tanh(n beta) < 1) | **[Lean]** / **[paper]** | `OneScale/SingleLink.lean` |

## III.3 The pressing half: reduction to one box

| # | Result | Status | Source |
|---|---|---|---|
| III.3.1 | Per-box hand-over rate: max(F_tw, F_e) >= log(1 + sqrt 2) = 0.881 at every box size (II.5) | **[Lean]** (hypothesis 0 < Z_tw stated) | `ProofPhase/Crossover/HandOver.lean`, `su2_handover` |
| III.3.2 | A flux-carrying outside forces at least one sheet through the box (the quantum) | **[Lean]** | `ProofPhase/Crossover/FluxRate.lean`, `exists_sheet_of_flux` |
| III.3.3 | Superadditivity along the chain: F_e(kL) >= k(F_e(L) - 2C); the rate multiplies iff F_e(L) > 2c(L) at one scale | **[Lean]** (abstract transfer-matrix form) | `ProofPhase/Crossover/CompositeHTF.lean`, `flux_superadd`, `flux_superadd_iter`; `proof-phase/c9a-crossover/HTF.md` |
| III.3.4 | Uniformity along the chain: every DB applies the same transfer step, so the loss rate eta is the same everywhere (II.4.5) | **[classical]** | translation invariance in Euclidean time; homogeneous Markov chain |
| III.3.5 | The doubling law with a fixed loss gives the gap on all larger dyadic boxes | **[Lean]** (implication) | `ProofPhase/Flip/Floor.lean`, `su2_gap_of_doubling_defect` |
| III.3.6 | Vortex saturation, any group with a central involution, in an explicit window | **[Lean]**; the SU(2) hypothesis H_sat **[open]** | `ProofPhase/Saturation/Vortex.lean`, `vortex_saturation` |
| III.3.7 | Uncontained sheets weigh nothing (dichotomy part b) | **[Lean]** | `ProofPhase/Crossover/Dichotomy.lean`, `measure_uncontained` |
| III.3.8 | **(O1) The one-box statement:** at one box scale L, eta < 1, i.e. F_e(L) > 2c(L), for every well-defined outside | **[open]** | `docs/OPEN-QUESTIONS-DMP.md`, section 0 |

The DMP reading behind III.3.3 and III.3.4 (all **[reading]**): crossing a DB re-encodes into a new G0 and loses what the encoder
cannot carry (a strong data-processing contraction); the arrow of causality makes the step the same at every DB.

**Care point (to be settled before the final paper).** The Lean assemblies take the one-box input in several named forms
(`OneBox/Fine.lean`, `FineOneBox`; `Saturation/Reduction.lean`, `FineOneBoxSplit`; `V4/Gap.lean`, `BlockGapBddW`). The notes do not
yet state which of them is exactly III.3.8. The final paper must state one form and prove the link to the assembly it feeds.

## III.4 The one box, from inside: the dichotomy and its residue

| # | Result | Status | Source |
|---|---|---|---|
| III.4.1 | Dichotomy part (a) fails uniformly: at the SO(3) cut (tr U_p = 0) a sheet plaquette costs nothing | **[paper]** | `proof-phase/c9a-crossover/DICHOTOMY.md`, 0.2 |
| III.4.2 | What survives: for every outside the box contracts, or one of two bad events holds (flux-carrying outsides with near-degenerate spanning surfaces; SO(3) cut along a would-be sheet) | **[paper]** | `DICHOTOMY.md`, 0.4 |
| III.4.3 | Rarity and saturation are disjoint; the window between them is about 0.18 to at least 1.79 nats per plaquette (d = 4) | **[Lean]** (disjointness, `window_gap`) + **[paper]** (numbers) | `ProofPhase/Crossover/Dichotomy.lean`; `DICHOTOMY.md`, 0.3 |
| III.4.4 | Y2, the inside residue: a positional tie of two cheapest surfaces, or a spanning near-cut network | **[open]** | `docs/OPEN-QUESTIONS-DMP.md`, Y2 |
| III.4.5 | Coarse test: at beta = 3.5 the near-cut set stays in finite clusters with exponential tails at blockings 1, 2, 4; at beta = 2.3 it spans (20 %, 37 %, 79 %) | **[numerical]** (exploratory, plan fixed before data) | `proof-phase/c9a-crossover/COARSE-TEST.md` |
| III.4.6 | Y3, the hand-over between rarity and disorder through the window | **[open]** | `docs/OPEN-QUESTIONS-DMP.md`, Y3 |
| III.4.7 | Y4, condition A uniformly: collar conditional mass m > 0 for every outside (measured about 4 in block units on typical configurations) | **[open]**; measurement **[numerical]** | `docs/OPEN-QUESTIONS-DMP.md`, Y4; `ProofPhase/General/CondMass.lean` |
| III.4.8 | Y5, uniformity in volume of M1's bounds and the block gap | **[open]**; per-volume gap **[Lean]** conditional on H2-all | `ProofPhase/Quantum/PerVolume.lean`, `perVolumeGap` |
| III.4.9 | The IR column at L1 below one (about 0.96 of it within cell distance 7); at the measured point L sqrt(sigma) = 2.80 the W1 column is certified at 0.99988 over the +/-3 sigma box (computer-assisted certificate as a named hypothesis) | **[open]**; implication **[Lean]** | `ProofPhase/Certified/Measured.lean`; `proof-phase/c9b-adjoint/ROUTE3.md` |

Measurements can refute the one-box statement; they cannot establish it (provability rule, `proof-phase/c9b-adjoint/REDESIGN.md`,
section 8).

## III.5 The weak-coupling side and the continuum (inputs from outside the gap mechanism)

| # | Result | Status | Source |
|---|---|---|---|
| III.5.1 | UV stability, small-field control and one-loop running at the weak-coupling unit scale (a recent construction by others) | **[external]** | `H1-OPENAI.md` |
| III.5.2 | Balaban's large-field control preserves partition functions, not laws | **[classical]**, read in full | `proof-phase/c5d-supplier/BALABAN-READING.md` |
| III.5.3 | M1: the law-preserving large-field step | **[paper]**, complete at paper level; Lean parts | `ProofPhase/M1/Assembly.lean` (`m1_assembly`); `proof-phase/m1-tools/M1-PLAN.md` |
| III.5.4 | The continuum limit exists (mesh limit at fixed volume, then volume along a subsequence) | **[external]** | `H1-OPENAI.md`; `ProofPhase/Existence/Bridge.lean` (`plaqLaw_eq_wilsonMeasure`) |
| III.5.5 | (O2) Line of constant physics (one-loop slope 11/(6 pi^2)) and non-triviality, as inputs of the assembly | **[open]** | `ProofPhase/Assembly.lean` (`OnLCP`, `NonTrivial`); `ProofPhase/V4/LCP.lean` |
| III.5.6 | (O3) Euclidean invariance, local fields as distributions, uniqueness of the limit, Wightman reconstruction | **[external]** for the external construction; **[open]** for ours | `PROOF-BLUEPRINT.md`, P6.4 to P6.9, P7.6 |
| III.5.7 | (O4) Every compact simple group: existence external; this project's tuning SU(2) only | **[external]** / **[open]** | `PROOF-BLUEPRINT.md`, P6.10 |

## III.6 DMP readings attached to this part (all [reading])

* WHKs: group plus one scale fix everything (dimensional transmutation, **[classical]**).
* Pressing = the scale-by-scale construction up to the one-box certificate; minting = III.2, done in Lean.
* Mass gap = the arrow of causality exists (I.7).
* The worst case is collapse into CMOS: either the box contracts, or the non-contracting part is contained (and carries a cost) or
  uncontained (and weighs nothing). This is the dichotomy of III.4; its part (b) is Lean, its part (a) fails uniformly.
* Every running act sits between a spanned, unsaturated existence and a well-defined non-existence: supported at beta = 3.5,
  contradicted at beta = 2.3 at every scale tested (III.4.5); at the confining scale the roles turn (vortex percolation).
* Only 3+1 transmutes: g^2 is dimensionless only in d = 4 **[classical]**.

## III.7 What would close it

O1: a worst-case argument for one DB (VI.3). O2: the line of constant physics and non-triviality as theorems, not inputs. O3: an
observable bridge from this project's bounded slab observables to local fields, or adoption of the external construction's field
notion with its audit. O4: a tuning for general G. O1 is the mathematical core; O2 to O4 are the remaining distance from the gap
mechanism to the Clay statement.
