# Claims ledger of the paper draft (draft 2, 2026-11-23)

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
| 0.1 | None of the three problems is solved in this paper | (statement of scope) | Parts III to V, section 0 of each | changes only when O1-O4, IV.4 and V.6 close |
| 0.2 | The SU(2) gap mechanism reduces to one box of fixed physical size, one number (F_e(L) > log mu_4) | Lean + classical | III.3 to III.5 | III.5.6 |
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
| II.5.2 | 0.881 suffices for a chain (two channels), not for a grid: path entropy beats it in d >= 3 | Lean | `ProofPhase/Crossover/Containment.lean`, `path_entropy_beats_handover`; `Crossover/Neighbours.lean`, `handover_column_sum_iff` | none |
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

Full chain: `docs/mass-gap/weak-coupling/PROOF-BLUEPRINT.md` (version 2). Crossover notes: `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/`.

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| III.0 | The Clay statement is not proved here | (scope) | III.0 | O1-O4 |
| III.1.1 | Wilson measure, SU(2) and compact G | Lean | `AreaLaw/ConcreteSUn.lean`, `OneScale/` | none |
| III.1.2 | Reflection positivity, site and link | Lean | `Positivity/` (`wilson_rp`, `wilson_rp_SU2`) | none |
| III.1.3 | Transfer kernel, centre flip symmetry, sector identity | Lean (identity definitional) | `Attempts/R4/LayerKernel.lean`, `LayerSector.lean` | none |
| III.1.4 | 't Hooft duality, Euclidean form | Lean | `ProofPhase/RouteB/Duality.lean`, `tHooft_rotation` | none |
| III.1.5a | Good blocking: centre-covariant, RP at every level | Lean | `ProofPhase/RouteA/Blocking.lean`, `goodBlocking_rp` | none |
| III.1.5b | Good blocking has a non-trivial limit at fixed L1 | paper | `proof-phase/ws1-routeA/NOTE.md` | Lean |
| III.1.6 | Z_tw < Z for beta != 0 | Lean | `ProofPhase/Flip/Strict.lean`, `su2_Ztw_lt_Z` | none |
| III.1.7 | Transfer kernel at fixed cross-section strictly positive | Lean | `ProofPhase/Flip/Bound.lean`, `stepK_pos` | none |
| III.2.1 | Dobrushin with weights; D' gives block decay (abstract) | Lean | `Attempts/R3/TailDecay.lean`, `theoremA_w`; `Attempts/R3/Robust.lean`, `gap_of_localFactorsW` | none |
| III.2.2 | Corollary B, physical units | Lean | `OneScale/CorollaryB.lean`, `corollaryB_lattice` | none |
| III.2.3 | Windowed OS route to MassGapLoc | Lean | `ProofPhase/OS/GapLoc.lean`, `massGapLoc_of_UVTVBlockGap`; `ProofPhase/M1/UVTVOS.lean`, `gap_of_RP` | none |
| III.2.4 | Assembly: OpenPieces -> MassGapLoc, LimitRP, NonTrivial | Lean | `ProofPhase/Torus/Top.lean`, `yang_mills_assembly` | none |
| III.2.5 | Gap in both orders of limits | Lean | `ProofPhase/Torus/Top.lean`, `yang_mills_assembly_torus`; `ProofPhase/Existence/Bridge.lean`, `bothOrders_of_torusDecay` | none |
| III.2.6 | Pure noise and bounded couplings fail OpenPieces | Lean | `ProofPhase/Assembly.lean`, `not_trivial` | none |
| III.2.7 | MassGapLoc implies a spectral gap of the continuum Hamiltonian | paper (spectral bridge Lean) | `ProofPhase/Bridge/Spectral.lean`, `ProofPhase/Bridge/OSLink.lean` | Lean density/reconstruction |
| III.2.8 | Strong-coupling gap, any compact group | Lean / paper | `OneScale/SingleLink.lean` | split Lean/paper parts |
| III.2.9 | The crossover needs no description of its content; the certificate is checked on the actual blocked law, uniformly over outsides | paper | `PREP.md` (crossover entry, 2026-11-23) | none |
| III.3.1 | Per-box hand-over rate >= 0.881 | Lean (0 < Z_tw as hypothesis) | `ProofPhase/Crossover/HandOver.lean`, `su2_handover` | formalise 0 < Z_tw |
| III.3.2 | Flux-carrying outside forces a sheet; flux cells even | Lean | `ProofPhase/Crossover/FluxRate.lean`, `exists_sheet_of_flux`, `even_card_fluxCells` | none |
| III.3.3 | Flux law the same from inside and outside; no sources | Lean | `ProofPhase/Crossover/Dichotomy.lean`, `cob_restrict_eq_cob_restrict_compl`, `sum_cob_restrict_eq_zero` | none |
| III.3.4 | Superadditivity; rate multiplies iff F_e(L) > 2c(L) | Lean (abstract) | `ProofPhase/Crossover/CompositeHTF.lean`, `flux_superadd`, `flux_superadd_iter` | link to the measure |
| III.3.5 | Uniformity along the chain | classical | translation invariance; `ProofPhase/Mixing/Chain.lean`, `contracts_kpow` | none |
| III.3.6 | One-box contraction at fixed physical size gives a physical mass; uniform floor gives physical decay along a chain | Lean | `ProofPhase/Crossover/Neighbours.lean`, `phys_rate_of_uniform`; `ProofPhase/Crossover/RDoeblin.lean`, `rdoeblin_physical_decay` | none |
| III.3.7 | Doubling law with fixed loss gives the gap | Lean (implication) | `ProofPhase/Flip/Floor.lean`, `su2_gap_of_doubling_defect` | premises |
| III.3.8 | Uncontained sheets weigh nothing | Lean | `ProofPhase/Crossover/Dichotomy.lean`, `measure_uncontained` | none |
| III.4.1 | Hand-over covers at most two channels; grid needs F > log(2d) = 2.08 | Lean | `ProofPhase/Crossover/Neighbours.lean`, `handover_column_sum_iff`, `column_requirement` | none |
| III.4.2 | Doeblin mass per box goes to zero in the continuum | Lean | `ProofPhase/Crossover/Neighbours.lean`, `neg_log_one_sub_le`, `doeblin_mass_tendsto_zero` | none |
| III.4.3a | Grid needs floor exponent below log(8/7) or about 0.22 | Lean | `ProofPhase/Crossover/RDoeblin.lean`, `floor_column_requirement`, `floor_disagreement_requirement` | none |
| III.4.3b | At L_* the floor exponent is in the tens | paper | `RDOEBLIN.md` 0 | none |
| III.4.4a | 't Hooft multi-sector relation (1 + S_tw)(1 + S_e) = 2^n | paper | `TRANSFER.md` 0.1 | Lean |
| III.4.4b | The relation forces nothing for n >= 2; quantitative 't Hooft criterion | Lean | `ProofPhase/Crossover/Runs.lean`, `min_le_of_sector_product`, `selfdual_sector_ge_one`, `electric_sum_lt_one_iff` | none |
| III.4.5a | A gauge-covariant frame carries no gauge-invariant information (finite) | Lean | `ProofPhase/Crossover/CompositeHTF.lean`, `weight_fiber_eq`, `weight_fiber_mul_card` | none |
| III.4.5b | The same for compact groups; composite HTF exists on every collar | paper | `HTF.md` 0 | Lean |
| III.4.6 | At typical fields the summed boundary influence drops below one at about 7 cells | numerical | `NEIGHBOURS.md` 0.2 | supremum, not typical |
| III.5.1a | r < 1, r = (1 - e^{-F_e})/(1 + e^{-F_e}) <= F_e, F_e >= 0 | Lean | `ProofPhase/Crossover/Containment.lean`, `twist_ratio_eq`, `twist_ratio_le_elecF`, `elecF_nonneg` | none |
| III.5.1b | Small box: F_e = O(g(L)^2) | classical (recalled, not re-checked) | Luescher; van Baal; `CONTAINMENT.md` 1 | re-check |
| III.5.2a | At fixed cross-section F_e(T) grows without bound | Lean (core) + classical (Jentzsch) + paper (centre invariance) | `ProofPhase/Crossover/Containment.lean`, `elecF_lower_of_gap`, `exists_elecF_ge`; `CONTAINMENT.md` 2 | Lean Jentzsch step |
| III.5.2b | Cubic boxes: F_e(L) >= 0.881 at some L | open (near L = 4 at beta 2.3, numerical) | `CONTAINMENT.md` 2 | a confinement input at one scale |
| III.5.3 | Gauss's law makes influence path-like | paper (Lean pieces III.3.2, III.3.3) | `CONTAINMENT.md` 6.1 | Lean |
| III.5.4a | Path sums converge iff F > log mu; 0.881 loses for mu >= 3 | Lean | `ProofPhase/Crossover/Containment.lean`, `path_sum_summable_iff`, `tube_threshold`, `path_entropy_beats_handover` | none |
| III.5.4b | mu_4 = 6.77; log mu_4 in [1.39, 1.95] | classical (recalled) | `CONTAINMENT.md` 3 | none |
| III.5.5a | Bogomolny bound; fractional floor pi^2 beta for admissible fields | classical | Bogomolny; 't Hooft; Luescher; `CONTAINMENT.md` 6.2 | none |
| III.5.5b | The floor helps only outside (multi-plane twists) and loses to entropy as a -> 0 | paper (one-loop sketch) | `CONTAINMENT.md` 6.2 | determinants and measure |
| III.5.6 | **O1:** F_e(L) > log mu_4 = 1.91 (r > 0.74) at one box of fixed physical size, uniformly over outsides | open | `CONTAINMENT.md` 0, 5; `docs/OPEN-QUESTIONS-DMP.md` 0 | a worst-case argument for one box |
| III.5.7 | Per-box costs multiply along paths (annealed to quenched) | open (used as an assumption) | `RATE.md` 5'; `CONTAINMENT.md` 3 | a proof |
| III.5.8 | Relation of O1 to the chain criterion F_e(L) > 2c(L) in the cubic geometry | open (not written down) | III.5.6 care point | a lemma or a joint statement |
| III.5.9 | Which Lean input form (`FineOneBox`, `FineOneBoxSplit`, `BlockGapBddW`) is O1 | open (not written down) | `ProofPhase/OneBox/Fine.lean`; `ProofPhase/Saturation/Reduction.lean`; `ProofPhase/V4/Gap.lean` | one form, linked to the assembly |
| III.6.1 | Tick-unit floor Z_tw/Z >= e^{-2 beta L^2} | Lean | `ProofPhase/Crossover/Saturation.lean`, `ratio_floor_of_pointwise`, `exp_floor_ge_iff` | none |
| III.6.2 | A large electric free energy forces a saturated twist | Lean | `ProofPhase/Crossover/Saturation.lean`, `twist_ratio_of_elecF` | none |
| III.6.3a | Upper decimation normalisation >= 1 (Jensen) | Lean | `ProofPhase/Crossover/Saturation.lean`, `jensen_normalization` | none |
| III.6.3b | Bond-moving localises the interpolation step (Tomboulis) to one box; mismatch vanishes at fixed physical size | paper (sketch) | `SATURATION.md` 0 | a matched lower bound |
| III.6.3c | Tomboulis 2007 proposed confinement along this line; gaps pointed out (Ito, Seiler) | classical | `PREP.md` (duality entry) | none |
| III.6.4 | Kanazawa's bracket is the non-strict form of III.1.6 | classical | `SATURATION.md` 0 | none |
| III.6.5 | Dichotomy part (a) fails uniformly at the SO(3) cut | paper | `DICHOTOMY.md` 0.2 | none |
| III.6.6 | Reduction to two bad events | paper | `DICHOTOMY.md` 0.4 | bounds on both events |
| III.6.7 | Window 0.18 to >= 1.79 nats per plaquette | Lean (disjointness) + paper (numbers) | `ProofPhase/Crossover/Dichotomy.lean`, `window_gap`; `DICHOTOMY.md` 0.3 | none |
| III.6.8 | Y2-Y5: inside residue, window hand-over, condition A uniformly, uniformity in volume | open (per-volume gap Lean conditional on H2-all) | `docs/OPEN-QUESTIONS-DMP.md` 2; `ProofPhase/Quantum/PerVolume.lean`, `perVolumeGap` | pieces of O1 |
| III.6.9 | IR column at L1; W1 column certified 0.99988 at L sqrt(sigma) = 2.80 | open (implication Lean) | `ProofPhase/Certified/Measured.lean`; `proof-phase/c9b-adjoint/ROUTE3.md` | supremum certificate |
| III.6.10 | Coarse test: near-cut set isolated at beta 3.5, spanning at 2.3 | numerical | `COARSE-TEST.md` | none |
| III.7.1 | Small tori at beta 2.3: F_e(6) = 2.6 centrally, lower bound 0.96 with the floor | numerical (preliminary) | `CONTAINMENT.md` 1, 3; `SATURATION.md` 0 | refutation only |
| III.7.2 | Chain criterion refuted at cross-section 16^3, beta 3.5, L = 1 (pre-registered); L <= 2 post hoc | numerical | `ONEBOX-CHECK.md` 4, 7 | none (does not bear on O1) |
| III.7.3 | Universal error-bar floor max(statistical, 1/T) | paper (project rule) | `docs/mass-gap/weak-coupling/attempts/RULES.md`, last section | none |
| III.7.4a | 8 pi^2 = -4 zeta(2)/zeta(-1); zeta(-1) = -1/12 | Lean | `ProofPhase/GRH/Mirror.lean`, `eight_pi_sq_mirror`, `zeta_neg_one_val` | none |
| III.7.4b | O1 in effective-string units: L sqrt(sigma) > 1.72 to 1.80 | numerical (model-based) | `docs/rh-guide/MIRROR.md` 0.2 | none |
| III.7.4c | The mirror brackets F_e(L) between two ends and does not constrain the middle | reading | `docs/rh-guide/MIRROR.md` 0.2 | none |
| III.8.1 | "It runs" in two targets | Lean | `ProofPhase/Crossover/Runs.lean`, `no_phase_mode`, `iterate_contraction`, `runs_two_targets` | none |
| III.9.1 | UV stability and one-loop running (construction by others) | external | `H1-OPENAI.md` | audit |
| III.9.2 | Balaban's control preserves partition functions, not laws | classical | `proof-phase/c5d-supplier/BALABAN-READING.md` | none |
| III.9.3 | M1 law-preserving large-field step, weak coupling up to L_* | paper (Lean parts) | `ProofPhase/M1/Assembly.lean`, `m1_assembly`; `proof-phase/m1-tools/M1-PLAN.md` | Lean |
| III.9.4 | Continuum limit exists | external | `H1-OPENAI.md`; `ProofPhase/Existence/Bridge.lean`, `plaqLaw_eq_wilsonMeasure` | audit |
| III.9.5 | O2: line of constant physics and non-triviality | open | `ProofPhase/Assembly.lean` (`OnLCP`, `NonTrivial`); `ProofPhase/V4/LCP.lean` | theorems |
| III.9.6 | O3: Euclidean invariance, fields, uniqueness, Wightman | external (theirs) / open (ours) | `PROOF-BLUEPRINT.md` P6.4-P6.9, P7.6 | observable bridge or adoption |
| III.9.7 | O4: every compact simple group | external (existence) / open (our tuning) | `PROOF-BLUEPRINT.md` P6.10 | general tuning |
| III.9.8 | M1's floor at L_* gives a physical gap along a chain, not on a grid | paper | `RDOEBLIN.md` 0 | none |
| III.10 | DMP readings of Part III (containment, outrunning possibility, IM both sides, pressing as instanton, crossover without content, WHKs) | reading | `PREP.md` (2026-11-22, 2026-11-23) | none |
| III.10b | g^2 dimensionless only in d = 4 | classical | dimensional analysis | none |

## Part IV. GRH (`draft/04-part-IV-grh.md`)

Notes relative to `docs/rh-guide/`.

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| IV.0a | RH and Dirichlet GRH proved in Lean by others | external | `SOURCES.md` S1-S4; `GUIDE.md` 1 | rebuild and axiom check |
| IV.0b | Their endgame is Landau's theorem on a one-sided square-root bound (Stepanov-type balance), not positivity | external (traced) | `GUIDE.md` 2, 4, 5 | none |
| IV.0c | GRH for Dedekind, Hecke, automorphic L-functions open | open | `GUIDE.md` 1, 5 | a proof |
| IV.1.1 | Finite Weil criterion | Lean | `ProofPhase/GRH/Weil.lean`, `weil_criterion_finite` | none |
| IV.1.2 | Line implies non-negative pairing | Lean | `ProofPhase/GRH/Weil.lean`, `weilSum_re_nonneg_of_real` | none |
| IV.1.3 | Positivity implies line, given the approximation property | Lean (named hypothesis) | `ProofPhase/GRH/Weil.lean`, `real_of_weilSum_nonneg` | prove the property for a real class |
| IV.1.4 | Weil's criterion | classical | Weil 1952; Bombieri 2000 | Lean (needs IV.1.5) |
| IV.1.5 | Lean form for real L-functions needs explicit formula and zero count, absent from Mathlib | paper (observation) | `grh/ATTEMPT.md` 2 | formalise both |
| IV.1.6 | Similitude eigenvalues have modulus sqrt q | Lean | `ProofPhase/GRH/Orbits.lean`, `similitude_eigenvalue` | none |
| IV.1.7 | Skew shift gives Re = 1/2 | Lean (finite dimension) | `ProofPhase/GRH/Orbits.lean`, `skew_shift_re_half` | none |
| IV.1.8 | Lee-Yang and Asano, small cases | Lean | `ProofPhase/GRH/LeeYang.lean`, `asano`, `ising3_zeros_on_circle` | none |
| IV.1.9 | Fixed points of f^n counted by periods | Lean | `ProofPhase/GRH/Orbits.lean`, `card_fixed_pow_eq_sum` | none |
| IV.1.10 | A lossy exponential bound becomes exact on a finite spectrum | Lean | `ProofPhase/GRH/Induction.lean`, `norm_le_of_exp_bound` | none |
| IV.2.1 | Duality without positivity allows mirror pairs off the line | Lean | `ProofPhase/GRH/Orbits.lean`, `krein_off_line` | none |
| IV.2.2a | Local factors are pure phases on the line (unramified primes) | Lean | `ProofPhase/GRH/Tate.lean`, `local_factor_unimodular` | none |
| IV.2.2b | Functional equation for every even/odd function on Z/N (Mathlib); Davenport-Heilbronn has zeros off the line | classical (Mathlib name not checked here) | `grh/TATE.md` 0.2 | check the Mathlib name |
| IV.2.2c | Tate: completed L-function as product of local zeta integrals; global FE is adelic Poisson | classical | Tate's thesis; `grh/TATE.md` 0.1 | none |
| IV.2.3a | Lambda(n) >= 0 plus a one-sided square-root bound plus Landau excludes zeros right of 1/2 | paper | `grh/INDUCTION.md` 0.2; `grh/TATE.md` 0.3 | Lean (with IV.2.4a) |
| IV.2.3b | The one-sided bound is global (generalised primes violate it) | classical | Diamond-Montgomery-Vorhauer; `grh/TATE.md` 0.3 | none |
| IV.2.4a | Positive transforms exclude negative-residue poles; ray form | Lean | `ProofPhase/Bridge/Poles.lean`, `landau_ray_poles`, `lseries_residue_nonneg` | none |
| IV.2.4b | A real zero in (theta, 1) gives a negative-residue pole | classical (not formalised) | `bridge/BRIDGE.md` 1.4 | Lean |
| IV.2.5a | Function fields: one positive duality gives both 1/2s | classical | Weil 1948; `bridge/BRIDGE.md` 2.3 | none |
| IV.2.5b | Stepanov and the Lean proof by others: the 1/2s meet only in the conclusion | classical / external (traced) | `bridge/BRIDGE.md` 2.3, 3 | none |
| IV.2.5c | Arithmetic positivity giving both 1/2s | open | `bridge/BRIDGE.md` 4 | an arithmetic Hodge index |
| IV.2.6 | The mirror pair Weil uses is (1, 0); its constants are archimedean and give no sign | numerical (with IV.2.1) | `MIRROR.md` 0.3 | none |
| IV.2.7 | Inversion and halving as one phenomenon | reading / analogy | `bridge/BRIDGE.md` 5 | IV.2.5c |
| IV.3.1 | Toeplitz frame; each step one scalar condition at the corner | classical + paper | `grh/INDUCTION.md` 0.1 | none |
| IV.3.2a | Each step holds up to a = 1.25, reflection coefficients at most 0.68 | numerical | `grh/INDUCTION.md` 0.1, 0.5 | more cells, higher primes |
| IV.3.2b | Each step is an exact cancellation (prime term up to about 700 radii) | numerical | `grh/INDUCTION.md` 0.1 | none |
| IV.3.2c | Weight scaling breaks positivity at 1e-3 to 1e-9 | numerical | `grh/INDUCTION.md` 0.3 | none |
| IV.3.3a | Ground-state zeros on the circle, locking onto zeta's zeros | numerical | `grh/VARIATIONAL.md` 0.1 | none |
| IV.3.3b | Minimiser's zeros on the circle for every real symmetric Toeplitz section; positivity = remnant >= 0 | classical (Caratheodory-Fejer, Pisarenko) + Lean (grid form) | `ProofPhase/GRH/Induction.lean`, `atoms_on_circle`, `atomic_toep_nonneg` | none |
| IV.3.4a | Positive configurations convex; positivity = stability only as a tautology | Lean | `ProofPhase/GRH/Variational.lean`, `toep_pos_convex`, `line_min_iff`, `min_at_zero_iff` | none |
| IV.3.4b | The true primes sit about 1e-9 from the edge | numerical | `grh/VARIATIONAL.md` 0.4 | none |
| IV.3.5 | Only the full set of primes present is positive | numerical | `grh/TRANSFER.md` 0.1 | none |
| IV.3.6a | Per-step contraction on sections; product to zero (Kolmogorov-Szego) | numerical + classical | `grh/TRANSFER.md` 0.2 | none |
| IV.3.6b | A positive margin survives finitely many positive factors | Lean | `ProofPhase/GRH/Transfer.lean`, `margin_pos_of_factors`, `prod_one_sub_le_exp` | none |
| IV.3.7a | Weyl's two-term bound is the best separate bound | Lean | `ProofPhase/GRH/Transfer.lean`, `two_term_bound` | none |
| IV.3.7b | It fails by 7.9 t_0 at support 1.225; Krein's extension is the right two-term form | numerical + classical | `grh/TRANSFER.md` 0.3 | none |
| IV.3.8 | Disjoint prime lattices; prime blocks indefinite; place-by-place forces the real place to pay for all | Lean | `ProofPhase/GRH/Tate.lean`, `prime_lattices_disjoint`, `zero_diag_indefinite`, `form_two_point`, `local_assembly_forces_arch` | none |
| IV.3.9 | Real place alone indefinite from support 0.40 to 0.43; semilocal positivity needs the real place and all primes up to e^{2a} | numerical | `grh/TATE.md` 0.4; `grh/SEMILOCAL.md` | none |
| IV.3.10 | Weight positivity is not enough; Lambda = 0 at the edge | classical + paper | `grh/LEE-YANG.md` 5; Polya 1926; Rodgers-Tao 2020 | none |
| IV.3.11 | Explicit formula agrees to 1e-16; smallest eigenvalue 2.4e-1 to 2.6e-9, no violation | numerical | `grh/weil_numerics.log`; `grh/ATTEMPT.md` 4 | none |
| IV.4.1 | Face 1: zero-free arithmetic Weil Hilbert space | open | `grh/ATTEMPT.md` step 4 | construction |
| IV.4.2 | Face 2: critical ferromagnet with block-spin law Phi | open | `grh/LEE-YANG.md` 5c | construction |
| IV.4.3 | Face 3: Deninger space with positive Hodge form (and a gap) | open | `grh/ORBITS.md` 6; `grh/TRANSFER.md` 5 | construction |
| IV.4.4 | Face 4: Hermite-Biehler chain for xi | open (framework classical; de Branges conjecture false) | `grh/INDUCTION.md` 0.4 | construction |
| IV.4.5 | Face 5: step lemma | open | `grh/INDUCTION.md` 7 | a rule from arithmetic |
| IV.4.6 | Face 6: sign of the remnant | open | `grh/VARIATIONAL.md` 0.5 | a proof |
| IV.4.7 | Face 7: global sign; the norm in which the scaling flow runs | open | `grh/TATE.md` 0.5, 0.6 | a proof |
| IV.4.8 | Face 8: all-or-nothing step | open | `grh/TRANSFER.md` 5 | a proof |
| IV.4.9 | Faces 2, 3 imply face 1; faces 5, 6, 8 are one quantity read three ways; not shown equivalent | paper | `grh/INDUCTION.md` 7; `grh/ORBITS.md` 4; `grh/VARIATIONAL.md` 5; `grh/TRANSFER.md` 5 | equivalence proofs |
| IV.5.1 | Scaling flow preserves Weil's form on its completion | paper | `grh/TATE.md` 0.5 | Lean |
| IV.5.2 | Contraction + mirror pairing: every mode a phase | Lean | `ProofPhase/GRH/Tate.lean`, `runs_and_mirror_on_line` | none |
| IV.5.3 | Explicit formula as a trace formula of zeros and orbit lengths log p | classical | `grh/TRANSFER.md` 0.2 | none |
| IV.5.4 | Positive-by-construction spaces miss off-line zeros (Connes) or give a half-plane (Lax-Phillips) | classical (recalled) | `grh/TATE.md` 0.5 | none |
| IV.6a | RH iff M(x) = O(x^{1/2 + eps}) | classical | `PREP.md` (ODP tool entry) | none |
| IV.6 | DMP readings of Part IV (circle, virtual flux, excision at G0, GRH as the ODP's tool, remnants, coupling factor) | reading | `PREP.md` (2026-11-23) | none |

## Part V. P vs NP (`draft/05-part-V-pnp.md`)

Notes relative to `docs/pnp/`.

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| V.1.1 | Dobrushin sums < 1: heat-bath within n alpha^t after t sweeps; random scan | Lean | `ProofPhase/Mixing/Classical.lean`, `tv_sweep_dobrushin`, `tv_rs_dobrushin`, `mixing_sweep_dobrushin` | none |
| V.1.2 | Spectral gap (1 - alpha)/n; spectral measure in [0, 1] | Lean | `ProofPhase/Mixing/FiniteSpectral.lean`, `spectral_gap_dobrushin`, `timeCorr_spectral`, `exists_spectral_measure` | none |
| V.1.3 | Gap in time iff spectral support | Lean | `ProofPhase/Mixing/TimeGap.lean`, `time_gap_iff` | none |
| V.1.4 | Doeblin, sharpness, homogeneous chains, box bound | Lean | `ProofPhase/Mixing/Doeblin.lean`, `contracts_of_doeblin`, `doeblin_sharp`; `ProofPhase/Mixing/Chain.lean`, `contracts_kpow`, `box_bound` | none |
| V.1.5 | Dobrushin uniqueness; spatial mixing gives a uniform gap | classical | Dobrushin 1968, 1970; Stroock-Zegarlinski 1992; Martinelli-Olivieri 1994 | none |
| V.1.6 | Sampling iff counting (self-reducible) | classical | Jerrum-Valiant-Vazirani 1986 | none |
| V.1.7 | Hard-core below lambda_c: counting and fast mixing | classical | Weitz 2006; Anari-Liu-Oveis Gharan 2020; Chen-Liu-Vigoda 2021 | none |
| V.1.8 | Certified class: existence, search, sampling, counting polynomial | classical (assembled; mixing step Lean) | `DICTIONARY.md` 6.2; Lovasz 1975; Moser-Tardos 2010; Moitra 2019 | Lean for the assembly |
| V.1.9 | Not unconditional in Lean: continuous spins, hard constraints, systematic scan under columns | open (Lean) | `ITEMS.md` 3 | Lean |
| V.1.10 | Certified class = DMP-complete inputs | reading | `DICTIONARY.md` 6.1 | none |
| V.2.1 | Antiferromagnets beyond uniqueness: no FPRAS | conditional (NP != RP) | Sly 2010; Sly-Sun 2014; Galanis-Stefankovic-Vigoda | none |
| V.2.2 | k-CNF counting NP-hard above c 2^{k/2} | conditional (NP != RP) | Bezakova et al. 2019 | none |
| V.2.3 | Ferromagnetic Ising has an FPRAS at every temperature | classical | Jerrum-Sinclair 1993 | none |
| V.2.4 | Wilson action is on the ferromagnetic side | reading | `DICTIONARY.md` 5 | none |
| V.2.5 | All counting inside uniqueness is as strong as NP = RP; SAT into LLL impossible as stated | conditional / classical | `DICTIONARY.md` 6.3 | none |
| V.3.1 | Resolution sound and refutation-complete | Lean | `ProofPhase/Proof/Resolution.lean`; `ProofPhase/Proof/Complete.lean`, `refutable_iff` | none |
| V.3.2 | No inference creates assertion; middle clause; width >= boundary | Lean | `ProofPhase/Proof/Cut.lean`, `exists_middle`, `width_ge` | none |
| V.3.3 | Tree-like size-width | Lean | `ProofPhase/Proof/SizeWidth.lean`, `tl_size_gt` | none |
| V.3.4 | DAG-like size-width; with the cut principle | Lean (optimisation over b paper) | `ProofPhase/Proof/Dag.lean`, `size_width`, `size_width_exp`, `dag_size_ge` | none |
| V.3.5 | Tseitin width bound on expanders | Lean (two hypotheses) | `ProofPhase/Proof/Tseitin.lean`, `width_ge`, `tl_size_ge` | formalise the expander hypotheses |
| V.3.6 | Gauss law mod 2 | Lean | `ProofPhase/Proof/Crossing.lean`, `gauss`, `unsat_of_odd` | none |
| V.3.7 | Every refutation crosses (two-premise systems) | Lean (two hypotheses) | `ProofPhase/Proof/Crossing.lean`, `cross_any_system` | as V.3.5 |
| V.3.8 | One XOR names the flux; naming costs differ by system | Lean (`summary`) + classical | `DICHOTOMY-TRANSFER.md` 3 | none |
| V.3.9 | Known lower bounds (resolution, bounded-depth Frege, cutting planes) | classical | `PROOF-SYSTEMS.md` 2 | none |
| V.3.10 | Feasible interpolation and its cryptographic failure | classical / conditional | Krajicek 1997; Pudlak 1997; Krajicek-Pudlak 1998; Bonet-Pitassi-Raz 2000 | none |
| V.3.11 | No superpolynomial bound for AC^0[p]-Frege, Frege, EF; formulas about n^3 | open / classical | Hastad 1998; Tal 2014 | a lower bound |
| V.3.12 | Flux-loss principle reproduces Urquhart; for Frege as hard as formula bounds | reading on classical | `PROOF-SYSTEMS.md` 6 | none |
| V.4.1 | CP on random 3-CNF is the sharpest open case | classical + reading | `EDGE.md` 0.1 | none |
| V.4.2 | Incompressibility of the one formula gives expansion; natural proofs do not bite | classical + reading | `EDGE.md` 0.3 | none |
| V.4.3 | Expansion forces a crossing line in every CP refutation | Lean (hypotheses of V.3.5) | `ProofPhase/Proof/Crossing.lean`, `cross_any_system` | as V.3.5 |
| V.4.4 | Majority line: sensitive to all, survives restrictions of fewer than e/2 | Lean | `ProofPhase/Proof/Edge.lean`, `majority_line`, `thr_sensitive`, `thr_survives` | none |
| V.4.5 | Unit thresholds: duality floor (e + 1)/2 | Lean | `ProofPhase/Proof/CPDuality.lean`, `thr_duality` | none |
| V.4.6 | Weighted lines are cheap in both channels | Lean | `ProofPhase/Proof/CPDuality.lean`, `two_cheap` | none |
| V.4.7a | Interpolation split: disjoint boundary laws iff unsatisfiable | Lean (logical core) | `ProofPhase/Proof/CPDuality.lean`, `split_unsat_iff` | none |
| V.4.7b | Interface bounds pass clique-colouring and log-width random CNF, fail at width 3 | classical | Pudlak 1997; Hrubes-Pudlak; Fleming-Pankratov-Pitassi-Robere; Sokolov | none |
| V.4.8 | Creative pairs in every CP refutation of a 3-CNF; single roundings create nothing; additive pairs cheap | Lean | `ProofPhase/Proof/CPPairs.lean`, `creative_pair`, `round_single`, `fan_cheap` | none |
| V.4.9a | All-1/2 point survives sums, not rounding | Lean | `ProofPhase/Proof/CPDuality.lean`, `half_clause`, `half_breaks_rounding` | none |
| V.4.9b | Rank, not size; SOS degree does not transfer to CP size | classical | Buresh-Oppenheim et al.; Grigoriev 2001; Dadush-Tiwari 2020 | none |
| V.4.10 | **Interface hardness at width 3** (a size-forcing W_CP) | open | `EDGE.md` 0.4; `CP-DUALITY.md` 0.5 | a lower bound |
| V.5.1 | Native method: quantized descent, pointer jumping, work conserved | Lean | `ProofPhase/Native/Method.lean`, `fixed_after`, `real_never_arrives`, `iterate_clog_pairUp`, `sum_pairUp`, `reaches_floor` | none |
| V.5.2 | Applied: 16 to 12 theorems, 5 to 4 layers, same statements | Lean + numerical | `ProofPhase/Native/RouteBChain.lean`; `NATIVE-METHOD.md` 0.3 | none |
| V.5.3 | The method's floor bounds no minimum | reading | `NATIVE-METHOD.md` 5 | N1 |
| V.5.4 | Automating resolution is NP-hard | classical | Atserias-Mueller 2019 | none |
| V.6.N1 | Size of the remnant: is the irreducible core polynomial? | open | `docs/OPEN-QUESTIONS-DMP.md` 4 | a proof |
| V.6.N2 | Interface hardness at width 3 for CP (= V.4.10, not counted twice) | (cross-reference) | `EDGE.md`; `CP-DUALITY.md` | a lower bound |
| V.6.N3 | Steps T and H for Frege | open | `DICHOTOMY-TRANSFER.md` 4-6 | a lower bound |
| V.6.N4 | From the certified class to all inputs | open | `DICTIONARY.md` 6.3, 8 | a barrier-passing argument |
| V.7 | Barriers: relativization, natural proofs, algebrization; Williams evades them | classical | Baker-Gill-Solovay 1975; Razborov-Rudich 1997; Aaronson-Wigderson 2009; Williams 2014 | none |
| V.8 | DMP readings of Part V (two categories of lines, pairs as entanglement, confinement plus uncertainty, inside/across a DB) | reading | `PREP.md` (2026-11-23); `DICTIONARY.md` 7 | none |

## Part VI. The common open step (`draft/06-part-VI-common-step.md`)

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VI.1 | The three open steps share one shape (local positivity, missing for every case, no assembly with slack) | reading | `docs/OPEN-QUESTIONS-DMP.md` 1 | none |
| VI.2a | Side-by-side table of the sharpest open steps and the proved obstructions | paper (summary of III.5.6, IV.4, V.4.10 and their obstructions) | Parts III-V | none |
| VI.2b | "It runs" holds the YM and GRH targets side by side | Lean | `ProofPhase/Crossover/Runs.lean`, `runs_two_targets`; `ProofPhase/GRH/Tate.lean`, `runs_and_mirror_on_line` | none |
| VI.2c | The dag-like protocol is CP's size-indexed "it runs" object | paper | `CP-DUALITY.md` 0.5 | none |
| VI.3 | The act carrier settles composition for YM (one number at one scale), not for GRH or NP vs coNP | paper (on III.3-III.5) | `docs/OPEN-QUESTIONS-DMP.md` 0, 6; `CONTAINMENT.md` | none |
| VI.3b | Three answers: outrun possibility; every block at once; charge the pair at its interface | reading | VI.3 | none |
| VI.5 | Only in YM is the starting positivity given by construction | paper (observation on II.1) | II.1 | none |
| VI.5b | YM is likely to close first | reading (expectation) | none | none |

## Outlook. A settling machine (`draft/07-outlook-settling-machine.md`)

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VII.1 | The first author's concept of a DMP-native general intelligence (CMOS in IM tokens, one Milky Way gate, an externally set tick, total freedom inside) | reading | `PREP.md` (2026-11-23); the first author | none (outlook) |
| VII.1b | The system works directly on the vectors embedding existence, its meta layer for arbitrary logic, as long as a correct answer comes out | reading | the first author (2026-11-23) | none (outlook) |
| VII.1c | Fast weights and hypernetworks as the DMP-native form: an existence embedding with a meta layer, changed through IM (and GG) while existence stays guaranteed | reading | the first author (2026-11-23) | none (outlook) |
| VII.2c | Maps of running systems keep the ledger exactly; changes inside the contracting class keep the settle bound | Lean | `ProofPhase/ETM/RunSys.lean`, `Hom`, `Hom.iterate_comm`, `RunSys.contract`; `ETM/Machine.lean`, `reaches_of_contracting` | none |
| VII.2a | Settling within an explicit, computable number of steps when every step contracts (cost above the floor) | Lean | `ProofPhase/ETM/Machine.lean`, `reaches_of_contracting`, `balanceBound_ge`, `contracting_iff_costAboveFloor` | none |
| VII.2b | No procedure decides settling for all content | Lean | `ProofPhase/ETM/Machine.lean`, `etm_balance_undecidable` | none |
| VII.3 | The gate certifies integrity and freshness, not meaning; it must check acts, not self-reports | paper | VII.3 | none |

---

## Counts by primary status

Counted on the rows above (each row once, by its first mark; scope rows 0.1 and III.0 and the cross-reference row V.6.N2 not counted):

| Status | Draft 2 | Draft 1 |
|---|---|---|
| Lean | 104 | 69 |
| classical | 42 | 27 |
| external | 7 | 7 |
| conditional | 3 | 3 |
| paper | 27 | 13 |
| numerical | 17 | 8 |
| reading | 23 | 18 |
| open | 25 | 20 |
| **Total** | **248** | **165** |

Counted by script on this file (first word of the status column; "project rule" counts as paper). Mixed rows count once, under their
first mark; for example "Lean (implication); premises open" counts as Lean, so the open count understates how many rows carry an open
part. Most of the growth is new results of the crossover, GRH and cutting-planes rounds, not re-labelling; no draft-1 row lost a mark, and one was upgraded (DAG-like
size-width, V.3.4, classical to Lean).
The open statements that decide the three problems are III.5.6 (O1) with III.5.7 to III.5.9 and III.9.5 to III.9.7 (Yang-Mills),
IV.0c and IV.4.1 to IV.4.8 (GRH), and V.4.10 and V.6 (P vs NP).

Lean names (draft 2): every backticked identifier in this file and in Parts II to VI was checked by script against a declaration
(`theorem`, `lemma`, `def`, ...) under `docs/mass-gap/formal/`; all resolve except `H1LocalLip` (discrepancy 5). The new modules
(`Crossover/Containment.lean`, `Neighbours.lean`, `RDoeblin.lean`, `Runs.lean`, `Saturation.lean`, `GRH/Mirror.lean`, `Tate.lean`,
`Induction.lean`, `Variational.lean`, `Transfer.lean`, `Proof/Dag.lean`, `Edge.lean`, `CPDuality.lean`, `CPPairs.lean`) are tracked and
contain no `sorry`, `admit`, `native_decide` or `axiom` declaration. Axiom logs were read in the notes, not regenerated.

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
8. `docs/OPEN-QUESTIONS-DMP.md` 0 still states the one-box statement as F_e(L) > 2c(L) (the chain criterion); `CONTAINMENT.md`
   sharpens it to F_e(L) > log mu_4 for a grid. The relation between the two in the cubic geometry is not written down (III.5.8).
9. `docs/OPEN-QUESTIONS-DMP.md` G3 says "the same piece in five forms"; `grh/TRANSFER.md` 5 now counts eight faces.
10. `CONTAINMENT.md` 3 uses the per-box product structure along paths (annealed to quenched, `RATE.md` 5') as an assumption; the
    paper lists it as an open input (III.5.7), not as part of the Lean chain.
11. `grh/TATE.md` cites `ZMod.completedLFunction_one_sub_even` / `_odd` in Mathlib; Mathlib is not in this repository, so the name was
    not checked here (IV.2.2b).
