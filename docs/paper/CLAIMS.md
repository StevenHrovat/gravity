# Claims ledger of the paper draft (draft 1, 2026-11-23)

Every claim made in `draft/`, with its status, its source and what would upgrade it. One row per claim. A claim with two parts of
different status is split or carries the weaker status first. The status column holds exactly one primary mark:

| Mark | Meaning |
|---|---|
| Lean | Machine-checked in this repository, standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), no `sorry`. Path relative to `docs/mass-gap/formal/` unless it starts with `docs/`. |
| classical | Known mathematics or physics; reference given. |
| external | A result by others, read in the source but not rebuilt or re-checked here. |
| conditional | Classical, but under a complexity or cryptographic assumption (named). |
| paper | Argued in this project in prose; not machine-checked. |
| numerical | Measured here. Can refute; never proves a for-all statement. |
| reading | A DMP interpretation. Never mathematics. |
| open | Not settled by anyone. |

Verification of this ledger (2026-11-23): every Lean module cited below exists; the axiom logs next to the notes
(`docs/rh-guide/**/axioms*.log`, `docs/pnp/axioms*.log`, `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/axioms*.log`) list
standard axioms only; a grep over `docs/mass-gap/formal/` finds no `sorry`, `admit` or `axiom` declaration. Logs were read, not
regenerated. External and classical references are cited as the project notes cite them and were not re-read for this draft.

---

## Abstract and introduction (`draft/00-abstract-introduction.md`)

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| 0.1 | None of the three problems is solved in this paper | (statement of scope) | Parts III to V, section 0 of each | changes only when O1-O4, IV.4 and V.5 close |
| 0.2 | The SU(2) gap mechanism reduces to one box at one scale | Lean + classical | III.3 | III.3.8 |
| 0.3 | RH and Dirichlet GRH are proved in Lean by others (released 2026-11-20, certified 2026-11-21), not via positivity | external | `docs/rh-guide/SOURCES.md` S1-S4; `GUIDE.md` 1, 5 | independent rebuild and axiom check of the library |
| 0.4 | GRH beyond Dirichlet L-functions is open | open | `GUIDE.md` 1, 5 | a proof |
| 0.5 | Computations can refute or guide, never establish a for-all statement | paper (design rule) | `docs/mass-gap/weak-coupling/proof-phase/c9b-adjoint/REDESIGN.md` 8 | none needed |

## Part I. DMP (`draft/01-part-I-dmp.md`)

Definitions of DMP are quoted from `vendor/dmp/01-constitution.md` (DMP 0.9.9) and the author's notes in
`docs/mass-gap/weak-coupling/PREP.md`; they are not claims. The readings are claims of interpretation only.

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| I.1 | Existence (the trust half) reads as a positive weight; Z > 0 in all three problems | reading | `docs/SYNTHESIS-DMP.md` 1 | none (a reading stays a reading) |
| I.1a | SAT iff #SAT > 0; e^{-S} > 0 gives Z > 0 | classical | elementary | none |
| I.2 | G0 reads as the definition of the system; positivity is in G0 for YM, not for GRH, and is the question itself for P vs NP | reading | `PREP.md` 2026-11-23 entries | none |
| I.3 | A DB reads as a box with its outside; crossing it is a lossy channel | reading | `PREP.md`, "The HTF must be lossy" | none |
| I.4a | A contradiction excised leaves a refutation; refutations always exist | Lean | `ProofPhase/Proof/Complete.lean`, `refutable_iff` | none |
| I.4b | The act carrier reads as a conserved quantity; Gauss law mod 2 | reading (Lean for the law: V.3.6, III.3.2) | `PREP.md`, "Answer to open question 1" | none |
| I.5a | Pressing reads as construction up to a one-box certificate; minting as OS reconstruction and limits | reading | `PREP.md`, "Stamping and minting" | none |
| I.5b | Pure YM has no free dimensionless parameter; group plus one scale fix everything (WHKs reading) | classical | dimensional transmutation; `PREP.md`, "What the WKHs are" | none |
| I.6a | Quantized descent arrives, real descent need not | Lean | `ProofPhase/Native/Method.lean`, `fixed_after`, `real_never_arrives` | none |
| I.6b | A finite box has a Doeblin rate per step for every outside | Lean (abstract kernel) + paper (lattice instantiation) | `ProofPhase/Mixing/Doeblin.lean`, `contracts_of_doeblin`; `PREP.md`, "Three answers" (a) | Lean instantiation for the Wilson box |
| I.6c | Error bars use max(statistical floor, 1/T) | paper (project rule) | `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/ONEBOX-CHECK.md` 7 | none |
| I.7a | Cantor: the power set is strictly larger; 1 = {0} | classical | Cantor; von Neumann | none |
| I.7b | "Existence = non-existence + 1" reads as the strict flip bound | reading | `PREP.md`, "The final pieces" | none |
| I.7c | Mass gap reads as "the arrow of causality exists" | reading (on II.2) | `PREP.md`, 2026-11-22 | none |

## Part II. The tools (`draft/02-part-II-tools.md`)

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| II.0 | Links 2-4 of the chain follow from link 1 in each column | classical (GNS, OS, spectral theorem); finite forms Lean | II.1-II.2 | Lean spectral theorem for bounded self-adjoint operators (Mathlib) |
| II.1.1 | Reconstruction from a positive form; symmetric contraction descends to a positive self-adjoint T | Lean (abstract) | `ProofPhase/M1/UVTVOS.lean`, `inner_Φ`, `T_symm`, `T_pos`, `contraction` | none |
| II.1.2 | Reflection positivity of the Wilson action, site and link | Lean | `Positivity/Wilson.lean`, `Positivity/LinkWilson.lean`, `Positivity/Concrete.lean` | none |
| II.1.3 | Finite Weil criterion | Lean | `ProofPhase/GRH/Weil.lean`, `weil_criterion_finite` | none |
| II.1.4 | Weil's criterion for zeta and Dirichlet L-functions | classical | Weil 1952; Bombieri 2000 | Lean with the explicit formula (IV.1.5) |
| II.1.5 | Heat-bath correlations have a spectral measure on [0, 1] | Lean | `ProofPhase/Mixing/FiniteSpectral.lean`, `timeCorr_spectral` | continuous spin spaces |
| II.2.1 | Decay rate = bottom of the spectrum | Lean | `ProofPhase/Bridge/Spectral.lean`, `spectral_gap_iff`, `decayRates_eq`; `ProofPhase/Mixing/TimeGap.lean`, `time_gap_iff` | none |
| II.2.2 | Gap from reflection positivity and block decay | Lean | `ProofPhase/M1/UVTVOS.lean`, `gap_of_RP`; `ProofPhase/Bridge/OSLink.lean`, `gap_of_RP_spectral` | spectral representation from RPData (open, `bridge/ADDENDUM-STEP1.md` 2) |
| II.2.3 | Real spectrum = zeros on the line (Hilbert-Polya form); spectral gap = fast mixing | classical | Hilbert-Polya; Jerrum-Sinclair | none |
| II.3.1 | Pringsheim extension (no sign hypothesis in the core) | Lean | `ProofPhase/Bridge/Pringsheim.lean`, `pringsheim_extension` | none |
| II.3.2 | Landau's theorem for L-series with non-negative coefficients | Lean | `ProofPhase/Bridge/Landau.lean`, `landau` | none |
| II.3.3 | Laplace transforms of positive measures: the real edge is a singularity | Lean | `ProofPhase/Bridge/Laplace.lean`, `laplace_landau` | none |
| II.3.4 | Resolvent of H >= 0 singular at the bottom of the spectrum | Lean | `ProofPhase/Bridge/Spectral.lean`, `resolvent_singular` | none |
| II.3.5 | Over function fields one positive duality gives both 1/2s; over Z none is known | classical / open | `docs/rh-guide/bridge/BRIDGE.md` 0, 2.3, 4 | an arithmetic Hodge index |
| II.4.1 | Data processing composes: eta(KL) <= eta(K) eta(L), eta^n for n steps | Lean | `ProofPhase/Mixing/Chain.lean`, `contracts_kchain`, `contracts_kpow`, `tv_pushv_kpow_le_pow` | none |
| II.4.2 | Doeblin: eta <= 1 - eps, sharp | Lean | `ProofPhase/Mixing/Doeblin.lean`, `contracts_of_doeblin`, `doeblin_sharp` | standard Borel spaces |
| II.4.3 | Column sums <= alpha < 1 give a spectral gap (1 - alpha)/N | Lean | `ProofPhase/Mixing/FiniteSpectral.lean`, `spectral_gap_dobrushin`; `ProofPhase/Mixing/Link.lean`, `spectral_gap_of_column` | continuous spins; volume uniformity |
| II.4.3b | With exponential weights, exponential decay of correlations | Lean | `Attempts/R3/TailDecay.lean`, `theoremA_w` | none |
| II.4.4 | Per-channel Doeblin bounds cannot give a column below 1 for k >= 2, C >= log 2 | Lean | `ProofPhase/Mixing/Chain.lean`, `column_sum_ge_one`, `column_sum_lt_one_iff` | a joint floor for all channels |
| II.4.5 | A homogeneous chain contracts like eta^n once eta < 1 at one step | classical (+ Lean composition) | II.4.1 | none |
| II.4.5r | "The uniformity is given by the arrow of causality" | reading | `PREP.md` 2026-11-23 | none |
| II.5.1 | Hand-over: 0 < Z_tw < Z implies max(F_tw, F_e) >= log(1 + sqrt 2), sharp | Lean | `ProofPhase/Crossover/HandOver.lean`, `log_one_add_sqrt_two_le_max`, `handover_ratio`; `ProofPhase/Flip/Floor.lean`, `elecF_eq_dual` | none |
| II.6.1 | The dichotomy local / crossing flux / residue as a strategy | paper | `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/DICHOTOMY.md`; `docs/pnp/DICHOTOMY-TRANSFER.md` | a proof in one problem (III.3.8) |
| II.6.2 | Gauss law mod 2 for Z_2 flux; odd charge unsatisfiable | Lean | `ProofPhase/Proof/Crossing.lean`, `gauss`, `flux_fixed`, `unsat_of_odd` | none |
| II.6.3 | Flux-carrying outside forces a sheet, even crossings | Lean | `ProofPhase/Crossover/FluxRate.lean`, `exists_sheet_of_flux`, `even_card_fluxCells` | none |
| II.6.4 | Uncontained sheets weigh nothing | Lean | `ProofPhase/Crossover/Dichotomy.lean`, `not_uncontained`, `measure_uncontained` | none |
| II.6.5 | Every refutation of an expanding formula crosses (two-premise systems) | Lean (two graph hypotheses stated) | `ProofPhase/Proof/Crossing.lean`, `cross_any_system` | formalise the hypotheses (V.3.5) |
| II.6.6 | Rarity and saturation regimes are disjoint | Lean | `ProofPhase/Crossover/Dichotomy.lean`, `window_gap` | none |
| II.7.1 | Quantized descent reaches a fixed point within mu(x) steps | Lean | `ProofPhase/Native/Method.lean`, `fixed_after`, `reaches_floor` | none |
| II.7.2 | Pointer jumping: one layer after ceil(log2 d) passes | Lean | `ProofPhase/Native/Method.lean`, `iterate_clog_pairUp` | none |
| II.7.3 | Per-layer kernel cost finite, linear in building blocks | numerical | `docs/pnp/NATIVE-METHOD.md` 0, 1 | a proof for a kernel cost model |
| II.8 | None of the tools creates positivity | paper (observation) | II.1-II.7 | none |

## Part III. Yang-Mills (`draft/03-part-III-yang-mills.md`)

Full chain: `docs/mass-gap/weak-coupling/PROOF-BLUEPRINT.md` (version 2).

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| III.0 | The Clay statement is not proved here | (scope) | III.0 | O1-O4 |
| III.1.1 | Wilson measure, SU(2) and compact G | Lean | `AreaLaw/ConcreteSUn.lean`, `OneScale/` | none |
| III.1.2 | Reflection positivity, site and link | Lean | `Positivity/` | none |
| III.1.3 | Transfer kernel, centre flip symmetry, sector identity | Lean (identity definitional) | `Attempts/R4/LayerKernel.lean`, `LayerSector.lean` | Gauss law and Z = tr(P T^n) formalised |
| III.1.4 | 't Hooft duality, Euclidean form | Lean | `ProofPhase/RouteB/Duality.lean`, `tHooft_rotation` | none |
| III.1.5a | Good blocking: centre-covariant, RP at every level | Lean | `ProofPhase/RouteA/Blocking.lean`, `goodBlocking_rp` | none |
| III.1.5b | Good blocking has a non-trivial limit at fixed L1 | paper | `proof-phase/ws1-routeA/NOTE.md` | rigorous proof |
| III.1.6 | Z_tw < Z for beta != 0 | Lean | `ProofPhase/Flip/Strict.lean`, `su2_Ztw_lt_Z` | none |
| III.2.1 | Dobrushin with weights; D' gives block decay (abstract) | Lean | `Attempts/R3/TailDecay.lean`, `Attempts/R3/Robust.lean` | D' at L1 (open) |
| III.2.2 | Corollary B, physical units | Lean | `OneScale/CorollaryB.lean`, `corollaryB_lattice` | none |
| III.2.3 | Windowed OS route to MassGapLoc | Lean | `ProofPhase/OS/GapLoc.lean`, `massGapLoc_of_UVTVBlockGap` | none |
| III.2.4 | Assembly: OpenPieces -> MassGapLoc, LimitRP, NonTrivial | Lean | `ProofPhase/Torus/Top.lean`, `yang_mills_assembly`; `ProofPhase/Assembly.lean`, `OpenPieces` | discharge OpenPieces |
| III.2.5 | Gap in both orders of limits | Lean | `ProofPhase/Torus/Top.lean`, `yang_mills_assembly_torus`; `ProofPhase/Existence/Bridge.lean`, `bothOrders_of_torusDecay` | inputs |
| III.2.6 | Pure noise and bounded couplings fail OpenPieces | Lean | `ProofPhase/Assembly.lean`, `not_trivial` | none |
| III.2.7 | MassGapLoc implies a spectral gap of the continuum Hamiltonian | paper | `ProofPhase/Bridge/Spectral.lean`, `OSLink.lean` (partial) | density and reconstruction in Lean |
| III.2.8 | Strong-coupling gap, any compact group | Lean / paper | `OneScale/SingleLink.lean` | split Lean and paper parts explicitly |
| III.3.1 | Per-box hand-over rate >= 0.881 | Lean (0 < Z_tw as hypothesis) | `ProofPhase/Crossover/HandOver.lean`, `su2_handover` | formalise 0 < Z_tw |
| III.3.2 | Flux-carrying outside forces a sheet | Lean | `ProofPhase/Crossover/FluxRate.lean`, `exists_sheet_of_flux` | none |
| III.3.3 | Superadditivity along the chain; rate multiplies iff F_e(L) > 2c(L) | Lean (abstract) | `ProofPhase/Crossover/CompositeHTF.lean`, `flux_superadd`, `flux_superadd_iter` | concrete instantiation |
| III.3.4 | Uniformity along the chain | classical | translation invariance | none |
| III.3.5 | Doubling law with fixed loss gives the gap | Lean (implication) | `ProofPhase/Flip/Floor.lean`, `su2_gap_of_doubling_defect` | its premises |
| III.3.6 | Vortex saturation in a window | Lean; H_sat open | `ProofPhase/Saturation/Vortex.lean`, `vortex_saturation` | H_sat for SU(2) |
| III.3.7 | Uncontained sheets weigh nothing | Lean | `ProofPhase/Crossover/Dichotomy.lean`, `measure_uncontained` | none |
| III.3.8 | **O1: one-box statement** eta < 1 at one scale for every well-defined outside | open | `docs/OPEN-QUESTIONS-DMP.md` 0 | a worst-case argument for one DB; then fix which Lean input form it is (`OneBox/Fine.lean`, `Saturation/Reduction.lean`, `V4/Gap.lean`) |
| III.4.1 | Dichotomy part (a) fails uniformly at the SO(3) cut | paper | `c9a-crossover/DICHOTOMY.md` 0.2 | none (a negative result) |
| III.4.2 | Reduction to two bad events | paper | `DICHOTOMY.md` 0.4 | bounds on both events |
| III.4.3 | Window 0.18 to >= 1.79 nats per plaquette | Lean (disjointness) + paper (numbers) | `ProofPhase/Crossover/Dichotomy.lean`, `window_gap` | none |
| III.4.4 | Y2 inside residue | open | `OPEN-QUESTIONS-DMP.md` Y2 | why a tie is unstable or a spanning network contracts |
| III.4.5 | Coarse test: isolated at beta 3.5, spanning at 2.3 | numerical | `c9a-crossover/COARSE-TEST.md` | none (exploratory) |
| III.4.6 | Y3 hand-over through the window | open | `OPEN-QUESTIONS-DMP.md` Y3 | uniform hand-over |
| III.4.7 | Y4 condition A uniformly (measured m about 4 on typical configurations) | open (numerical support) | `OPEN-QUESTIONS-DMP.md` Y4; `ProofPhase/General/CondMass.lean` | uniform collar mass |
| III.4.8 | Y5 uniformity in volume | open; per-volume gap Lean conditional on H2-all | `ProofPhase/Quantum/PerVolume.lean`, `perVolumeGap` | H2-all |
| III.4.9 | IR column at L1 below one; W1 column certified 0.99988 at L sqrt(sigma) = 2.80 | open; implication Lean, certificate a named hypothesis | `ProofPhase/Certified/Measured.lean`; `c9b-adjoint/ROUTE3.md` | worst-case column bound |
| III.5.1 | UV stability and one-loop running (construction by others) | external | `docs/mass-gap/weak-coupling/H1-OPENAI.md` | audit |
| III.5.2 | Balaban's control preserves partition functions, not laws | classical | `proof-phase/c5d-supplier/BALABAN-READING.md` | none |
| III.5.3 | M1 law-preserving large-field step | paper (Lean parts) | `ProofPhase/M1/Assembly.lean`, `m1_assembly`; `proof-phase/m1-tools/M1-PLAN.md` | full Lean instantiation |
| III.5.4 | Continuum limit exists | external | `H1-OPENAI.md`; `ProofPhase/Existence/Bridge.lean` | audit |
| III.5.5 | O2: line of constant physics and non-triviality | open | `ProofPhase/Assembly.lean` (`OnLCP`, `NonTrivial`); `ProofPhase/V4/LCP.lean` | proofs |
| III.5.6 | O3: Euclidean invariance, fields, uniqueness, Wightman | external (theirs) / open (ours) | `PROOF-BLUEPRINT.md` P6.4-P6.9, P7.6 | observable bridge P6.12 |
| III.5.7 | O4: every compact simple group | external (existence) / open (our tuning) | `PROOF-BLUEPRINT.md` P6.10 | Tuning for general G |
| III.6 | DMP readings of Part III (WHKs, pressing/minting, CMOS collapse, spanned existence) | reading | `PREP.md` | none |
| III.6b | g^2 dimensionless only in d = 4 | classical | dimensional analysis | none |

## Part IV. GRH (`draft/04-part-IV-grh.md`)

Notes relative to `docs/rh-guide/`.

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| IV.0a | RH and Dirichlet GRH proved in Lean by others | external | `SOURCES.md` S1-S4; `GUIDE.md` 1 | rebuild and axiom check |
| IV.0b | Their endgame is Landau's theorem on a Stepanov-type balance, not positivity | external (traced) | `GUIDE.md` 2, 4, 5 | read the library files |
| IV.0c | GRH for Dedekind, Hecke, automorphic L-functions open | open | `GUIDE.md` 1, 5 | a proof |
| IV.1.1 | Finite Weil criterion | Lean | `ProofPhase/GRH/Weil.lean`, `weil_criterion_finite` | none |
| IV.1.2 | Line implies non-negative pairing | Lean | `GRH/Weil.lean`, `weilSum_re_nonneg_of_real` | none |
| IV.1.3 | Positivity implies line, given the approximation property | Lean (named hypothesis) | `GRH/Weil.lean`, `real_of_weilSum_nonneg` | approximation property for smooth tests |
| IV.1.4 | Weil's criterion | classical | Weil 1952; Bombieri 2000 | Lean (needs IV.1.5) |
| IV.1.5 | Lean form for real L-functions needs explicit formula and zero count, absent from Mathlib | paper (gap list) | `grh/ATTEMPT.md` 2 | formalise both |
| IV.1.6 | Similitude eigenvalues have modulus sqrt q | Lean | `GRH/Orbits.lean`, `similitude_eigenvalue` | none |
| IV.1.7 | Skew shift gives Re = 1/2 | Lean (finite dimension) | `GRH/Orbits.lean`, `skew_shift_re_half` | infinite dimension |
| IV.1.8 | Duality without positivity allows mirror pairs off the line | Lean | `GRH/Orbits.lean`, `krein_off_line` | none |
| IV.1.9 | Lee-Yang and Asano, small cases | Lean | `GRH/LeeYang.lean`, `asano`, `ising3_zeros_on_circle` | general lattice |
| IV.1.10 | Fixed points of f^n counted by periods | Lean | `GRH/Orbits.lean`, `card_fixed_pow_eq_sum` | none |
| IV.2.2 | Positive transforms exclude negative-residue poles; ray form | Lean | `ProofPhase/Bridge/Poles.lean`, `landau_ray_poles`, `lseries_residue_nonneg` | apply to a real L-function (IV.2.3) |
| IV.2.3 | A real zero in (theta, 1) gives a negative-residue pole | classical (not formalised) | `bridge/BRIDGE.md` 1.4; `bridge/ADDENDUM-STEP1.md` | Mellin explicit formula in Lean |
| IV.2.4 | Function fields: one positive duality gives both 1/2s | classical | Weil 1948; Hartshorne V.1; `bridge/BRIDGE.md` 2.3 | none |
| IV.2.5 | Stepanov and the Lean proof by others: the 1/2s meet only in the conclusion | classical / external (traced) | `bridge/BRIDGE.md` 2.3, 3 | none |
| IV.2.6 | Arithmetic positivity giving both 1/2s | open | `bridge/BRIDGE.md` 4 | an arithmetic Hodge index |
| IV.2.7 | Inversion and halving as one phenomenon | reading / analogy | `bridge/BRIDGE.md` 5 | IV.2.6 |
| IV.3.1 | Explicit formula normalisation agrees to 1e-16 | numerical | `grh/weil_numerics.log` | none |
| IV.3.2 | Smallest eigenvalue of Weil's form 2.4e-1 to 2.6e-9, no violation | numerical | `grh/ATTEMPT.md` 4 | exact arithmetic beyond a = 1 |
| IV.3.3 | Semilocal positivity needs the real place and all primes up to e^{2a} | numerical | `grh/SEMILOCAL.md` | none |
| IV.3.4 | Toeplitz frame; new prime acts only at the corner | classical + paper | `grh/INDUCTION.md` 0-2 | none |
| IV.3.5 | Each prime step holds up to a = 1.25 | numerical | `grh/INDUCTION.md` 2 | more cells, higher precision |
| IV.3.6 | Each step is an exact cancellation (prime term up to hundreds of radii) | numerical | `grh/INDUCTION.md` 2 | none |
| IV.3.7 | Weight scaling breaks positivity at 1e-3 to 1e-9 | numerical | `grh/INDUCTION.md` 4 | none |
| IV.3.8 | Weight positivity is not enough; Lambda = 0 at the edge | classical + paper | `grh/LEE-YANG.md` 5; Polya 1926; Rodgers-Tao 2020 | none |
| IV.4.1 | Form 1: zero-free arithmetic Hilbert space for Weil's form | open | `grh/ATTEMPT.md` step 4 | construction |
| IV.4.2 | Form 2: critical ferromagnet with block-spin law Phi | open | `grh/LEE-YANG.md` 5c | construction |
| IV.4.3 | Form 3: Deninger space with positive Hodge form | open | `grh/ORBITS.md` 6 | construction |
| IV.4.4 | Form 4: local rule for reflection coefficients | open | `grh/INDUCTION.md` 7 | construction |
| IV.4.5 | Form 5: Hermite-Biehler coupling for xi | open (framework classical; de Branges conjecture false, Conrey-Li 2000) | `grh/INDUCTION.md` 5 | construction |
| IV.4.6 | Forms 2, 3 imply form 1; not shown equivalent | paper | `grh/INDUCTION.md` 7; `grh/ORBITS.md` 4 | none |
| IV.5 | DMP readings of Part IV (real place carries existence, remnants of acts, coupling factor, arithmetic never runs) | reading | `PREP.md` | none |

## Part V. P vs NP (`draft/05-part-V-pnp.md`)

Notes relative to `docs/pnp/`.

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| V.1.1 | Dobrushin column < 1: heat-bath within n alpha^t after t sweeps | Lean | `ProofPhase/Mixing/Classical.lean`, `mixing_sweep_dobrushin`; `Mixing/Glauber.lean` | continuous spins |
| V.1.2 | Spectral gap (1 - alpha)/n | Lean | `ProofPhase/Mixing/FiniteSpectral.lean`, `spectral_gap_dobrushin` | none |
| V.1.3 | Gap in time iff spectral support | Lean | `ProofPhase/Mixing/TimeGap.lean`, `time_gap_iff` | none |
| V.1.4 | Doeblin and homogeneous chains | Lean | `ProofPhase/Mixing/Doeblin.lean`, `Mixing/Chain.lean` | none |
| V.1.5 | Dobrushin uniqueness; spatial mixing gives a uniform gap | classical | Dobrushin 1968, 1970; Stroock-Zegarlinski 1992; Martinelli-Olivieri 1994 | Lean Gibbs formalisation |
| V.1.6 | Sampling iff counting (self-reducible) | classical | Jerrum-Valiant-Vazirani 1986 | complexity layer in Lean |
| V.1.7 | Hard-core below lambda_c: counting and fast mixing | classical | Weitz 2006; Anari-Liu-Oveis Gharan 2020; Chen-Liu-Vigoda 2021 | none |
| V.1.8 | Certified class: existence, search, sampling, counting polynomial | classical (assembled; mixing step Lean) | `DICTIONARY.md` 6.2; Lovasz 1975; Moser-Tardos 2010; Moitra 2019 | Lean for LLL and Moser-Tardos |
| V.1.9 | Certified class = DMP-complete inputs | reading | `DICTIONARY.md` 6.1 | none |
| V.2.1 | Antiferromagnets beyond uniqueness: no FPRAS | conditional (NP != RP) | Sly 2010; Sly-Sun 2014; Galanis-Stefankovic-Vigoda 2015, 2016 | none |
| V.2.2 | k-CNF counting NP-hard above c 2^{k/2} | conditional (NP != RP) | Bezakova et al. 2019 | none |
| V.2.3 | Ferromagnetic Ising has an FPRAS at every temperature | classical | Jerrum-Sinclair 1993 | none |
| V.2.4 | Wilson action is on the ferromagnetic side | reading | `DICTIONARY.md` 5 | none |
| V.2.5 | All counting inside uniqueness is as strong as NP = RP; SAT into LLL impossible as stated | conditional / classical | `DICTIONARY.md` 6.3 | none |
| V.3.1 | Resolution sound and refutation-complete | Lean | `ProofPhase/Proof/Resolution.lean`; `ProofPhase/Proof/Complete.lean`, `refutable_iff` | none |
| V.3.2 | No inference creates assertion; middle clause; width >= boundary | Lean | `ProofPhase/Proof/Cut.lean`, `exists_middle`, `width_ge` | none |
| V.3.3 | Tree-like size-width | Lean | `ProofPhase/Proof/SizeWidth.lean`, `tl_size_gt` | none |
| V.3.4 | DAG size-width | classical | Ben-Sasson-Wigderson 2001 | Lean (random restriction) |
| V.3.5 | Tseitin width bound on expanders | Lean (two hypotheses) | `ProofPhase/Proof/Tseitin.lean`, `width_ge`, `tl_size_ge` | formalise path flipping and an explicit expander family |
| V.3.6 | Gauss law mod 2 | Lean | `ProofPhase/Proof/Crossing.lean`, `gauss`, `unsat_of_odd` | none |
| V.3.7 | Every refutation crosses (two-premise systems) | Lean (two hypotheses) | `ProofPhase/Proof/Crossing.lean`, `cross_any_system` | as V.3.5 |
| V.3.8 | One XOR names the flux; naming costs differ by system | Lean (`summary`) + classical | `DICHOTOMY-TRANSFER.md` 3 | none |
| V.3.9 | Known lower bounds (resolution, bounded-depth Frege, cutting planes) | classical | `PROOF-SYSTEMS.md` 2 | none |
| V.3.10 | Feasible interpolation and its cryptographic failure | classical / conditional | Krajicek 1997; Pudlak 1997; Krajicek-Pudlak 1998; Bonet-Pitassi-Raz 2000 | none |
| V.3.11 | No superpolynomial bound for AC^0[p]-Frege, Frege, EF; formulas about n^3 | open / classical | Hastad 1998; Tal 2014 | lower bounds |
| V.3.12 | Flux-loss principle reproduces Urquhart; for Frege as hard as formula bounds | reading on classical | `PROOF-SYSTEMS.md` 6 | none |
| V.4.1 | Native method (II.7) | Lean | `ProofPhase/Native/Method.lean` | none |
| V.4.2 | Applied: 16 to 12 theorems, 5 to 4 layers, same statements | Lean + numerical | `ProofPhase/Native/RouteBChain.lean`; `NATIVE-METHOD.md` 4 | none |
| V.4.3 | The method's floor bounds no minimum | reading | `NATIVE-METHOD.md` 5 | N1 |
| V.4.4 | Automating resolution is NP-hard | classical | Atserias-Mueller 2019 | none |
| V.5.N1 | Size of the remnant: is the irreducible core polynomial? | open | `docs/OPEN-QUESTIONS-DMP.md` 4 | a proof |
| V.5.N2 | Step T for Frege on random 3-CNF | open | `DICHOTOMY-TRANSFER.md` 5, 6 | a proof using absence of structure |
| V.5.N3 | Step H: formula lower bound beyond n^3 | open | `DICHOTOMY-TRANSFER.md` 4-6 | a lower bound |
| V.5.N4 | From the certified class to all inputs | open | `DICTIONARY.md` 6.3, 8 | a barrier-passing argument |
| V.5.B | Barriers: relativization, natural proofs, algebrization; Williams evades them | classical | Baker-Gill-Solovay 1975; Razborov-Rudich 1997; Aaronson-Wigderson 2009; Williams 2014 | none |
| V.6 | DMP readings of Part V | reading | `PREP.md`; `DICTIONARY.md` 7 | none |

## Part VI. The common open step (`draft/06-part-VI-common-step.md`)

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VI.1 | The three open steps share one shape (local positivity, missing for every case) | reading | `docs/OPEN-QUESTIONS-DMP.md` 1 | none |
| VI.2 | The act carrier settles composition for YM (reduction to one box), not for GRH or P vs NP | paper (on III.3) | `OPEN-QUESTIONS-DMP.md` 0, 6 | none |
| VI.4 | Only in YM is the starting positivity given by construction | paper (observation on II.1) | II.1 | none |
| VI.4b | YM is likely to close first | reading (expectation) | none | none |

---

## Counts by primary status

Counted on the rows above (each row once, by its first mark; scope rows 0.1 and III.0 not counted):

| Status | Count |
|---|---|
| Lean | 69 |
| classical | 27 |
| external | 7 |
| conditional | 3 |
| paper | 13 |
| numerical | 8 |
| reading | 18 |
| open | 20 |
| **Total** | **165** |

Counted by script on this file (first word of the status column). Mixed rows count once, under their first mark; for example
"Lean (implication); premises open" counts as Lean, so the open count understates how many rows carry an open part. The open
statements that decide the three problems are III.3.8 and III.5.5-III.5.7 (Yang-Mills), IV.0c and IV.4.1-IV.4.5 (GRH), and
V.5.N1-N4 (P vs NP).

## Discrepancies found in the source notes while building this ledger

These are for the owners of those notes; nothing outside `docs/paper/` was edited.

1. `docs/rh-guide/bridge/BRIDGE.md` describes `pringsheim_extension` with M >= 0; the Lean statement has no sign hypothesis (it is
   more general; the sign is used in the instances). The draft follows the Lean statement.
2. `docs/pnp/DICTIONARY.md` 8 still lists the Q construction and the finite spectral theorem as missing; `docs/pnp/ITEMS.md` closes
   both for finite systems. `DICTIONARY.md` cites Moitra as 2017 in the text, 2019 in the references.
3. `docs/pnp/PROOF-SYSTEMS.md` 1 marks resolution completeness classical; `DICHOTOMY-TRANSFER.md` marks it Lean
   (`Proof/Complete.lean`). Lean is correct.
4. `docs/rh-guide/grh/INDUCTION.md` 2 omits n = 8 from its margin table; `grh/induction.log` part 4 has it.
5. `PROOF-BLUEPRINT.md` cites the R2-R4 modules without the `Attempts/` prefix; `H1LocalLip` has no declaration (the Lean name is
   `H1LocalLipW`).
6. `docs/OPEN-QUESTIONS-DMP.md` 0 says "Everything global is in place". That holds for the gap mechanism; the Clay statement also
   needs O2-O4 (III.0). The paper states the narrower claim.
7. The notes do not yet say which Lean input form (`FineOneBox`, `FineOneBoxSplit`, `BlockGapBddW`) is exactly the one-box
   statement of `OPEN-QUESTIONS-DMP.md` 0.
