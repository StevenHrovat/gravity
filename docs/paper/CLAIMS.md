# Claims ledger of the paper draft (draft 3, 2026-11-24)

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
| certified | Enclosed in ball arithmetic, with its log; a numerical computation whose enclosures are rigorous. A Lean step that takes the enclosures as a named hypothesis is marked Lean (from X) in its own row. |
| reading | A DMP interpretation. Never mathematics. |
| open | Not settled by anyone. |

Verification of this ledger (2026-11-23): every Lean module cited below exists; the axiom logs next to the notes
(`docs/rh-guide/**/axioms*.log`, `docs/pnp/axioms*.log`, `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/axioms*.log`) list
standard axioms only; a grep over `docs/mass-gap/formal/` finds no `sorry`, `admit` or `axiom` declaration. Logs were read, not
regenerated. External and classical references are cited as the project notes cite them and were not re-read for this draft.

Audit of 2026-11-24 (`CLAIMS-AUDIT.md`): every Lean row's identifiers were matched by script to a declaration (Lean files of `docs/mass-gap/formal/` and the `im` repository); rows were checked against their chapters; 83 duplicate, folded or unused rows were removed (their labels are listed under "Folded labels" below, so chapter references still resolve) and 7 rows were added. A status written "Lean (from X)" means the theorem is proved and X is an `External`, `OpenStep` or `R136a1` slot or a named hypothesis of the statement.

---

## Abstract and introduction (`draft/00-abstract-introduction.md`)

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| 0.1 | None of the seven problems is solved in this paper; results that use the one assumption are conditional on it; closing any open step changes one row, one verdict line and one abstract item of the paper (the same rule as VII.8, VIII.7.2, IX.7.3, now folded here) | (statement of scope) | Parts IV to X, section 0 of each; Part III 4.4 | changes only when the open step of a card closes |
| 0.9 | GRH's transport bound and O1's decay bound, as conditions on a sequence of ticks of one per-tick distance, cannot both hold on the same sequence, and each holds without the other (a statement about the two bounds; no implication between the problems is proved either way) | Lean | Part III 2 (`uniform_margin_excludes_o1`, `transport_not_decay`, `decay_not_transport`) | none needed |
| 0.10 | Pitch modulo the octave is a circle on which a fifth (3/2) is a rotation; twelve pure fifths exceed seven octaves by the Pythagorean comma 3^12/2^19 = 1.01364 | classical | any text on tuning theory; arithmetic | none needed |
| 0.11 | Equal temperament distributes the comma evenly (fifth = 2^(7/12)); 19/12 is a convergent of log2(3) | classical | continued fraction of log2(3) = [1; 1, 1, 2, 2, 3, 1, ...] | none needed |
| 0.12 | In the explicit formula each nontrivial zero 1/2 + i gamma contributes an oscillation of frequency gamma in log x, of amplitude x^(1/2) on the critical line | classical | Part V; `ProofPhase/GRH/ContourShift*.lean` for the formula over all zeros | none needed |
| 0.13 | The tempered piano as a guide: the comma is the finite loss excised at the start {infinity, 2, 3}, temperament the balanced state, the final tone a describable, DMP-complete configuration; idea credited to Vsauce, under whose name the short was published | reading | owner, 2026-11-24 (`docs/mass-gap/weak-coupling/PREP.md`, entry "Existence as a piano") | none (a reading) |
| 0.20 | Attributions of the introduction: Osterwalder-Schrader built quantum field theories from reflection positivity; Weil reduced the Riemann hypothesis to one positivity; Hodge and Riemann found the same positivity on cohomology and Weil used it for curves over finite fields; Dobrushin: a contraction of local influences forces a unique equilibrium | classical | introduction (L101-105, L171-172); the references as the notes cite them, not re-read | none |
| 0.21 | Every problem is one box under one test: one command at one shared gate, a marker per step, DMP-complete when every marker agrees with the gate; one step certified on one box certifies every tick, and every scale under the one assumption | Lean (the scale part from III.64) | II.4a-II.4c; III.68, III.68a | none |
| 0.22 | O1 is exactly DMP-completeness of the Yang-Mills box, in both directions | Lean | IV.10c, IV.10d | none |
| 0.23 | In the energy-only model the Navier-Stokes box gives the wrong marker at some scale, so it is not DMP-complete | Lean (model) | VII.7g | none |
| 0.24 | Poincare for SU(N) holds for N <= 3 and fails from N = 4; Sp(2) is rigid; G2 has exactly two structures; G2 is rigid under the one assumption | external (SU(3)); paper (the rest); Lean from III.64 for the last | A.3j, A.3k, A.5j, A.5p, A.5u | A.5r |
| 0.25 | In ordinary terms the machine is multiplication by complex numbers: each step multiplies by one number of modulus at most one, whose modulus is the cost and whose phase the rotation | Lean | II.0a-II.0d; `ProofPhase/ETM/Complex.lean`, `complex_translation` | none |
| 0.5 | Computations can refute or guide, never establish a for-all statement | paper (design rule) | `docs/mass-gap/weak-coupling/proof-phase/c9b-adjoint/REDESIGN.md` 8 | none needed |

## Part I. DMP (`draft/01-part-I-dmp.md`)

Definitions of DMP are quoted from `vendor/dmp/01-constitution.md` (DMP 0.9.9) and the author's notes in
`docs/mass-gap/weak-coupling/PREP.md`; they are not claims. The readings are claims of interpretation only.

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| I.1 | Existence (the trust half) reads as a positive weight; Z > 0 for Yang-Mills and SAT, a non-negative Weil pairing for GRH | reading | `docs/SYNTHESIS-DMP.md` 1 | none (a reading stays a reading) |
| I.1a | SAT iff #SAT > 0; e^{-S} > 0 gives Z > 0 | classical | elementary | none |
| I.2 | G0 reads as the definition of the system; positivity is in G0 for YM, not for GRH, and is the question itself for P vs NP | reading | `PREP.md` 2026-11-23 entries | none |
| I.3 | A DB reads as a box with its outside; crossing it is a lossy channel | reading | `PREP.md`, "The HTF must be lossy" | none |
| I.4b | The act carrier reads as a conserved quantity; Gauss law mod 2 | reading (Lean for the law: II.14.2, II.14.3) | `PREP.md`, "Answer to open question 1" | none |
| I.5a | Pressing reads as construction up to a one-box certificate; minting as OS reconstruction and limits | reading | `PREP.md`, "Stamping and minting" | none |
| I.5b | Pure YM has no free dimensionless parameter; group plus one scale fix everything (WHKs reading) | classical | dimensional transmutation; `PREP.md`, "What the WKHs are" | none |
| I.6b | A finite Wilson box has a Doeblin floor for every outside (lattice instantiation; the abstract implication is II.12.2) | paper | `ProofPhase/Mixing/Doeblin.lean`, `contracts_of_doeblin`; `PREP.md`, "Three answers" (a) | Lean instantiation for the Wilson box |
| I.6c | Error bars use max(statistical floor, 1/T) | paper (project rule) | `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/ONEBOX-CHECK.md` 7 | none |
| I.7a | Cantor: the power set is strictly larger; 1 = {0} | classical | Cantor; von Neumann | none |
| I.7b | "Existence = non-existence + 1" reads as the strict flip bound | reading | `PREP.md`, "The final pieces" | none |
| I.7c | Mass gap reads as "the arrow of causality exists" | reading (on II.10) | `PREP.md`, 2026-11-22 | none |
| I.8a | DMP reads as an existence linter: Gravity is the linter, DMP the universally readable rule set that is its passing condition; existence is what the linter passes | reading | `docs/mass-gap/weak-coupling/PREP.md`, 2026-11-24, "DMP is a very well defined existence linter" | none |
| I.8b | Gravity's check passes only when the pinned DMP matches its hash, the setup file is complete, no source file uses an escape hatch, the build succeeds and every theorem rests on the three standard axioms | paper | `evidence/tools/check.sh`; `tools/check-pin.sh` (read; not run for this draft) | run the check |
| I.8c | The arsenal has the same shape at small size: its lint is the linter, "Mathlib v4.34.0 only, no escape hatch, an open part only as a named R136a1 hypothesis" the passing condition | paper | `im` repository, `arsenal/README.md`, `arsenal/tools/lint.sh` | none |
| I.8d | The root chain pins in both directions: Gravity holds a pinned copy of DMP; that DMP pins Gravity in turn is stated by the owner and the notes, not re-read | paper (Gravity's side read; DMP's side not re-read) | `vendor/dmp/PIN`; `tools/check-pin.sh`; `PREP.md`, 2026-11-24 | read DMP's check |
| I.8e | A linter certifies form, not content: passing does not say that DMP's sentences describe the world | paper | `PREP.md`, 2026-11-24, care point 1 | none |
| I.8f | The unlintable assumption is that the system runs, which is O1 in each card's terms | reading | `PREP.md`, 2026-11-24, care point 2, and "O1 ... must always be the open step" | none |
| I.8g | "Universally readable" holds for the form (plain text and Lean, checkable with the pinned toolchain); "universal superset" is a reading | reading | `PREP.md`, 2026-11-24, care point 3 | none |
| I.8h | A consistent, effectively axiomatised theory containing arithmetic cannot prove its own consistency (Goedel II) | classical | Goedel 1931 | none |
| I.9a | Excision at transmission: a wrong act is answered R136a1 at the gate and never crosses; only its remnant tail stays, the record that an excision happened; IM's verifier counts refusals without content | reading | `PREP.md`, 2026-11-24, "Correction to care point (2): 'transmitted' is the operative word"; DMP chapters 01 (C-infinity) and 06 as the notes cite them | none |
| I.9c | The gate excises what its checks recognise as wrong at that tick; a later recognition is a later tick, with its tail recorded then, never a revision | reading | `PREP.md`, 2026-11-24, same entry, care point | none |
| I.10a | Rights tied to identity give total freedom inside and security at the gate; asymptotic freedom (free at short distance, bound at long) reads the same way: free inside the box, bound at the boundary | reading | `PREP.md`, 2026-11-24, "Security in CMOS: rights tied to identity" | none |
| I.10b | A sentence passes IM's door only when both the security and the operational grant carry its kind; one grant alone never passes | Lean | `im` repository, `proof/Im/Laws.lean`, `Im.pass_needs_both_grants`, `Im.one_grant_never_passes` | none |
| I.10c | IM's grammar is closed: the space has exactly 72 shapes, and every sentence keeps every law (`lawfulB`, decided by the kernel) | Lean | `im` repository, `proof/Im/Closure.lean`, `Im.closure`, `Im.all_shapes_lawful`, `Im.space_size` | none |
| I.10d | A network of nodes that keep the guarantee on what their door lets in keeps it on any input | Lean | `im` repository, `proof/Im/Compose.lean`, `Im.sound`, `Im.galaxy_robust`, `Im.galaxy_is_a_node` | none |
| I.10e | Tokens only attenuate (by construction: attenuation is intersection with a caveat, the discipline of Macaroons, Biscuit and SPKI that IM cites, so the subset bound is an unfolding): an attenuated token's kinds are a subset of its parent's; a chain of attenuations is the intersection of the root with its caveats, in any order; along any chain the sentences a door passes only shrink; the empty grant attenuates only to itself (the C# token code is not proved to implement the model) | Lean | `im` repository, `proof/Im/Attenuate.lean`, `attenuate_sub`, `attenuateAll_eq`, `attenuateAll_perm`, `attenuateAll_sub`, `Grants.pass_of_attenuateAll`, `Grants.refuse_of_attenuateAll`, `Grants.attenuate_noGrants` | name the three hypotheses in DMP 04 or 06 (the second half of IM's IF9, the owner's) |
| I.10f | "Permissible" is as good as its specification; the gate certifies integrity and authority, not the truth of content; the binding is as strong as the custody of the key | reading | `PREP.md`, 2026-11-24, same entry, care points | none |
| I.10g | Asymptotic freedom: the Yang-Mills coupling vanishes in the ultraviolet | classical | Gross-Wilczek 1973; Politzer 1973 (recalled, not re-read) | none |
| I.11b | IM read a second way, Identity Multiplication: the arsenal's rotation API is multiplication by a number on the unit circle, which keeps the norm (on the circle the mass never changes, Lean, II.0c; the encoder's root, Lean, II.2); the name Interstellar Medium stays; a second reading with a meaning is a uniqueness that survives being contained | reading (the norm facts: Lean) | `PREP.md`, 2026-11-24, "IM, read a second way"; `ProofPhase/ETM/Complex.lean`, `cmach_lossless`; `ProofPhase/Unified/Encoder.lean`, `root` | none |
| I.11c | IM as a step up the DAG (this project requires IM's arsenal, pinned by commit; the package graph is acyclic: paper). Why the link is a rotation, the owner's argument: a DB allows only a gate that keeps the norm (the encoder's root, Lean; "only this gate" is the reading I.3); a linear gate that keeps every norm is a rotation (Lean, II.0f); so the link to another node is a rotation, the ultimate gate; the cost sits in the provability of a common root: the remainder after the provably shared part, norm(psi - conj(c) psi')^2 = norm(psi)^2 (1 - abs(c)^2), is exactly the step's cost (Lean) | reading (the edge: paper; the gate, the rotation and the remainder: Lean) | `PREP.md`, 2026-11-24, "IM is a step up the DAG", "Why only rotation links", "The cost sits in the provability of a common root"; `docs/mass-gap/formal/lakefile.toml`; `ProofPhase/Unified/Encoder.lean`, `root`, `ofRot`, `szego_remainder`; II.0f | none |
| I.11d | Ordinary multiplication is IM too: on the reals it is a cost (the modulus) times an identity-keeping multiplication (the sign, identity or half-turn); the rotation group shrinks to Z/2, which carries no order | reading (the decomposition: Lean, II.0g) | `PREP.md`, 2026-11-24, "Ordinary multiplication is IM too"; II.0g; III.70a | none |

## Part II. The machine and the tools (`draft/02-part-II-machine.md`)

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| II.0a | A sequence of complex multipliers of modulus at most one is a running system (floor 0) whose ledger law holds with equality; its run is the product of its steps, so moduli multiply and phases add | Lean | `ProofPhase/ETM/Complex.lean`, `cmach`, `cmach_pays_eq`, `cmach_iterate`, `cmach_mass_eq` | none |
| II.0b | Every running system is dominated by the product of its own factors e^delta fac, read as complex numbers | Lean | `ProofPhase/ETM/Complex.lean`, `dominated` | none |
| II.0c | Multipliers uniformly at most theta < 1 settle within any epsilon; multipliers on the unit circle never change the mass; every factor of the universal machine is 1 | Lean | `ProofPhase/ETM/Complex.lean`, `cmach_reaches`, `cmach_lossless`, `etm_fac_one`, `complex_translation` | none |
| II.0d | The reflection coefficients of a stream of encoders are such multipliers, with cost 1 - abs(c)^2 | Lean | `ProofPhase/ETM/Complex.lean`, `encMach`, `encMach_fac` | none |
| II.0e | The translation is exact for the cost and the rotation; the content a step carries (the universal machine's program) lives in the state, not in the number, and that is where its undecidability sits | paper | `ProofPhase/ETM/Complex.lean` (docstring); II.3 | none |
| II.0f | Multiplying every amplitude by a unit number is a morphism of the complex machine (keeps step, gate factor and mass); a complex-linear map of the line that keeps every norm is multiplication by a unit number | Lean | `ProofPhase/ETM/Complex.lean`, `rotHom`, `rot_of_isometry` | none (more dimensions: the unitary group) |
| II.0g | On the reals the unit circle is 1 and -1: a real-linear map of the line that keeps every norm is multiplication by 1 or -1 (the identity or the half-turn), and every real number is its modulus times 1 or -1 | Lean | `ProofPhase/ETM/Complex.lean`, `rot_of_isometry_real`, `real_eq_sign_mul_abs` | none |
| II.0h | The machine and test modules reached 100 declarations (the axiom script's count, at 41c76f3) exactly when + and - were given a modulus (II.0g); the count is a fact about the files (history 75, 77, 83, 96, 98, 100), not provable as mathematics | reading (the count: by counting, `docs/unified/rotation-axioms.log`) | `PREP.md`, 2026-11-24, "The 100 declarations"; `docs/unified/rotation-axioms.sh` | none |
| II.8 | Links 2-4 of the chain follow from link 1 in each column | classical (GNS, OS, spectral theorem); finite forms Lean | II.9-II.10 (`T_symm`, `T_pos`; `weil_criterion_finite`; `spectral_gap_iff`) | Lean spectral theorem for bounded self-adjoint operators (Mathlib) |
| II.9.1 | Reconstruction from a positive form; symmetric contraction descends to a positive self-adjoint T | Lean (abstract) | `ProofPhase/M1/UVTVOS.lean`, `inner_Φ`, `T_symm`, `T_pos`, `contraction` | none |
| II.9.2 | Reflection positivity of the Wilson action, site and link | Lean | `Positivity/Wilson.lean` (`wilson_rp`), `Positivity/LinkWilson.lean`, `Positivity/Concrete.lean` (`wilson_rp_SU2`) | none |
| II.9.3 | Finite Weil criterion | Lean | `ProofPhase/GRH/Weil.lean`, `weil_criterion_finite` | none |
| II.9.4 | Weil's criterion for zeta and Dirichlet L-functions | classical | Weil 1952; Bombieri 2000; also V.1.4 | Lean for Weil's criterion itself (the explicit formula for zeta is in Lean, V.1.5; Dirichlet L-functions are not, V.1.5b) |
| II.9.5 | Heat-bath correlations have a spectral measure on [0, 1] | Lean | `ProofPhase/Mixing/FiniteSpectral.lean`, `timeCorr_spectral`, `exists_spectral_measure` | continuous spin spaces |
| II.10.1 | Decay rate = bottom of the spectrum; in time: correlations decay at rate m iff there is no spectral mass above e^{-m} (`time_gap_iff`) | Lean | `ProofPhase/Bridge/Spectral.lean`, `spectral_gap_iff`, `decayRates_eq`; `ProofPhase/Mixing/TimeGap.lean`, `time_gap_iff` | none |
| II.10.2 | Gap from reflection positivity and block decay | Lean (hypotheses: the UV-TV block bounds `hsplit`, `hA`, `hB`) | `ProofPhase/M1/UVTVOS.lean`, `gap_of_RP`; `ProofPhase/Bridge/OSLink.lean`, `gap_of_RP_spectral` | spectral representation from RPData (open, `bridge/ADDENDUM-STEP1.md` 2) |
| II.10.3 | Real spectrum = zeros on the line (Hilbert-Polya form); spectral gap = fast mixing | classical | Hilbert-Polya; Jerrum-Sinclair | none |
| II.11.1 | Pringsheim extension (no sign hypothesis in the core) | Lean | `ProofPhase/Bridge/Pringsheim.lean`, `pringsheim_extension` | none |
| II.11.2 | Landau's theorem for L-series with non-negative coefficients | Lean | `ProofPhase/Bridge/Landau.lean`, `landau` | none |
| II.11.3 | Laplace transforms of positive measures: the real edge is a singularity | Lean | `ProofPhase/Bridge/Laplace.lean`, `laplace_landau` | none |
| II.11.4 | Resolvent of H >= 0 singular at the bottom of the spectrum (the Laplace integral of the correlation measure; its identification with the resolvent is classical) | Lean | `ProofPhase/Bridge/Spectral.lean`, `resolvent_singular` | none |
| II.12.1 | Data processing composes: eta(KL) <= eta(K) eta(L), eta^n for n steps | Lean | `ProofPhase/Mixing/Chain.lean`, `contracts_kchain`, `contracts_kpow`, `tv_pushv_kpow_le_pow` | none |
| II.12.2 | Doeblin: eta <= 1 - eps, sharp | Lean | `ProofPhase/Mixing/Doeblin.lean`, `contracts_of_doeblin`, `doeblin_sharp`; `ProofPhase/Mixing/Chain.lean`, `box_bound` | standard Borel spaces |
| II.12.3 | Column sums <= alpha < 1 give a spectral gap (1 - alpha)/N | Lean | `ProofPhase/Mixing/FiniteSpectral.lean`, `spectral_gap_dobrushin`; `ProofPhase/Mixing/Link.lean`, `spectral_gap_of_column` | continuous spins; volume uniformity |
| II.12.4 | Per-channel Doeblin bounds cannot give a column below 1 for k >= 2, C >= log 2 | Lean | `ProofPhase/Mixing/Chain.lean`, `column_sum_ge_one`, `column_sum_lt_one_iff` | a joint floor for all channels |
| II.12.5 | A homogeneous chain contracts like eta^n once eta < 1 at one step | classical (+ Lean composition) | II.12.1 | none |
| II.12.5r | "The uniformity is given by the arrow of causality" | reading | `PREP.md` 2026-11-23 | none |
| II.13.1 | Hand-over: 0 < Z_tw < Z implies max(F_tw, F_e) >= log(1 + sqrt 2), sharp | Lean | `ProofPhase/Crossover/HandOver.lean`, `log_one_add_sqrt_two_le_max`, `handover_ratio`; `ProofPhase/Flip/Floor.lean`, `elecF_eq_dual` | none |
| II.13.2 | 0.881 suffices for a chain (two channels), not for a grid: path entropy beats it in d >= 3; the grid needs F > log(2d) = 2.08 in d = 4 (IV.4.1) | Lean | `ProofPhase/Crossover/Containment.lean`, `path_entropy_beats_handover`; `Crossover/Neighbours.lean`, `handover_column_sum_iff`, `column_requirement` | none |
| II.14.1 | The dichotomy local / crossing flux / residue as a strategy | paper | `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/DICHOTOMY.md`; `docs/pnp/DICHOTOMY-TRANSFER.md` | a proof in one problem (IV.3.8) |
| II.14.2 | Gauss law mod 2 for Z_2 flux; odd charge unsatisfiable | Lean | `ProofPhase/Proof/Crossing.lean`, `gauss`, `flux_fixed`, `unsat_of_odd` | none |
| II.14.3 | Flux-carrying outside forces a sheet, even crossings (each plaquette in an even number of cells for the parity half) | Lean | `ProofPhase/Crossover/FluxRate.lean`, `exists_sheet_of_flux`, `even_card_fluxCells` | none |
| II.14.4 | Uncontained sheets weigh nothing (for a law carried by closed configurations) | Lean | `ProofPhase/Crossover/Dichotomy.lean`, `not_uncontained`, `measure_uncontained` | none |
| II.14.5 | Every refutation of an expanding formula crosses (two-premise systems) (also VI.3.7, VI.4.3) | Lean (two graph hypotheses stated) | `ProofPhase/Proof/Crossing.lean`, `cross_any_system` | formalise the hypotheses (VI.3.5) |
| II.14.6 | Rarity and saturation regimes are disjoint | Lean (hypotheses: entropy K' >= 2(d - 1), E_min <= E) | `ProofPhase/Crossover/Dichotomy.lean`, `window_gap` | none |
| II.15.1 | Quantized descent reaches a fixed point within mu(x) steps; real descent need not arrive (`real_never_arrives`, I.6a, VI.5.1) | Lean | `ProofPhase/Native/Method.lean`, `fixed_after`, `reaches_floor` | none |
| II.15.2 | Pointer jumping: one layer after ceil(log2 d) passes | Lean | `ProofPhase/Native/Method.lean`, `iterate_clog_pairUp`, `sum_pairUp` | none |
| II.15.3 | Per-layer kernel cost finite, bounded by the size of the finite building blocks | numerical | `docs/pnp/NATIVE-METHOD.md` 0, 1 | a proof for a kernel cost model |
| II.16 | None of the tools creates positivity | paper (observation) | II.9-II.15 | none |
| II.1.0 | The ledger: if M_{i+1} <= e^{delta - c_i} M_i then M_n <= e^{n delta - sum c} M_0; costs at least kappa > delta give decay at rate kappa - delta and a summable M; a lower bound on M_n bounds the total cost | Lean | `ProofPhase/Unified/Ledger.lean`, `Pays`, `ledger`, `decay`, `summable_of_gap`, `size`, `CostAboveFloor`, `rate_of_costAboveFloor`; `ProofPhase/ETM/RunSys.lean`, `RunSys.carry`, `RunSys.contract`, `RunSys.decay_cost` | none |
| II.1.1 | Bounded transport (was X.7a in draft 2): an uncertainty crossing contracting steps with fresh uncertainty at most R stays at most q^n e_0 + R/(1 - q) | Lean | `ProofPhase/Unified/Transport.lean`, `bounded_transport`, `transport_geom`, `acc_eq` | none |
| II.1.2 | Critical transport (was X.7b in draft 2): at cost = floor e_n <= e_0 + sum r_j; sharp; bounded exactly when the r_j are summable; a constant fresh uncertainty grows without limit | Lean | `ProofPhase/Unified/Transport.lean`, `critical_transport`, `critical_sharp`, `critical_bounded_iff`, `critical_unbounded` | none |
| II.1.3 | Sign preserved (was X.7c in draft 2): an uncertainty below the sign margin certifies the sign at every step | Lean | `ProofPhase/Unified/Transport.lean`, `sign_transport`, `sign_of_bounded`, `sign_of_critical` | none |
| II.1.4 | The ledger is the case of no fresh uncertainty (was X.7d in draft 2) | Lean | `ProofPhase/Unified/Transport.lean`, `pays_iff_transports`, `carry_of_transport`, `ETM.Ledger.transports`, `contract_of_transport` | none |
| II.1.5 | Zero slack, exactly (was X.7e in draft 2): an uncertainty and a margin paying the same cost have their ratio carried at cost = floor | Lean | `ProofPhase/Unified/Transport.lean`, `relative_transport`, `relative_critical` | none |
| II.2.1 | An encoder (state psi, rotated image psi' of the same norm) has one number, the reflection coefficient c = <psi, psi'>/norm(psi)^2, with abs(c) <= 1 from positivity; read from the other side c is conjugated | Lean | `ProofPhase/Unified/Encoder.lean`, `Encoder`, `Encoder.ofRot`, `refl`, `norm_refl_le`, `refl_swap` | none |
| II.2.2 | The Szego factor 1 - abs(c)^2 (the share of psi left after removing its projection on the mirror image) and the electric factor (1 - c)/(1 + c) (odd over even part) are fixed by c; the Szego factor lies in [0, 1] for every encoder and the electric factor in (0, 1) for 0 < c < 1; the cost is -log of the factor; a uniform factor bound below e^{-delta} is exactly a cost above the floor | Lean | `ProofPhase/Unified/Encoder.lean`, `szego`, `szego_mem`, `szego_pos_iff`, `szego_eq_one_iff`, `szego_remainder`, `elec`, `elec_mem`, `encoder_elec`, `pays_of_factors`, `costAboveFloor_of_factor_le`, `factor_le_of_costAboveFloor`, `oneBox_iff_refl` | none |
| II.2.3 | One distance, two functions: -log elec(c) = log((1 + c)/(1 - c)) = d, and szego(c) = 4 elec(c)/(1 + elec(c))^2 = 1/cosh^2(d/2) | Lean (the form 1/cosh^2(d/2) is elementary algebra, not in Lean) | `ProofPhase/Unified/GRHLens.lean`, `elec_cost`, `szego_of_elec` | none |
| II.2.4 | The half-turn: the electric factor is the Moebius map of (1/sqrt 2)[[-1, 1], [1, 1]], a symmetric matrix that squares to the identity; elec is an involution with antipodal fixed points sqrt 2 - 1 and -(1 + sqrt 2); it swaps product of reflection coefficients and hyperbolic addition of electric factors; its self-dual cost is log(1 + sqrt 2) | Lean | `ProofPhase/Unified/GRHLens.lean`, `halfTurn_mobius`, `halfTurn_transpose`, `halfTurn_mul_self`, `elec_elec`, `elec_selfdual`, `elec_fixed_neg`, `fixed_antipodal`, `elec_mul`, `elec_oplus`; `ProofPhase/Unified/Encoder.lean`, `selfdual_cost` | none |
| II.2.4b | As a Moebius map of the Riemann sphere that matrix is a rotation by 180 degrees | classical | `docs/unified/GRH-LENS.md` 6.1 | none |
| II.2.5 | The half-turn is a symmetry of the description: it exchanges the pictures, fixes its axis, and does not turn an upper bound on one encoder into a lower bound on another | paper | `docs/unified/GRH-LENS.md` 6.3 | none |
| II.2.6 | Applications of the encoder: Yang-Mills (twist ratio is c; O1 is c above (mu - 1)/(mu + 1) for every outside); GRH (the Verblunsky step at each scale is c); NP vs coNP (the crossing label passes at factor 1 with a cutting-planes line, so the encoder explains resolution's cost but supplies none for strong systems) | paper | `docs/unified/ENCODER.md` 1, 2 | none |
| II.3.1 | Running systems (states, step, factor in [0, 1], mass, ledger law) form a category whose terminal object is the space of ledgers; every running system has exactly one map into it; the ledger theorems hold on every one; maps keep the ledger exactly and changes inside the contracting class keep the settle bound (XI.2c) | Lean | `ProofPhase/ETM/RunSys.lean`, `RunSys`, `Hom`, `exists_unique_hom`, `univIsTerminal`, `RunSys.carry`, `RunSys.contract`, `Hom.iterate_comm` | none |
| II.3.2 | The settle theorem: in the contraction class (every factor at most theta, e^delta theta < 1, equivalently a cost above the floor) the run reaches balance within epsilon by the explicit computable step bound ceil(M q/(eps (1 - q))) + 1 (also stated in the Outlook, XI.2; 0.7, III.30) | Lean | `ProofPhase/ETM/Machine.lean`, `Contracting`, `contracting_iff_costAboveFloor`, `balanceBound`, `balanceBound_ge`, `reaches_of_contracting`, `reaches_iff_bounded`, `reaches_of_contracting'` | none |
| II.3.3 | The edge: the lossless machine that runs every partial recursive content lies outside the contraction class and its balance problem is undecidable; its truth value exists classically but is not computable (also stated in the Outlook, XI.2; 0.7, III.30) | Lean | `ProofPhase/ETM/Machine.lean`, `etm`, `etm_universal`, `etm_not_contracting`, `etm_balance_undecidable`, `etm_truth_edge`, `etm_edge` | none |
| II.5.1 | The API (`ProofPhase.API`) is a facade with one structure per concept (running system, settle bound, edge, chain, margin, encoder, uncertainty, problem card, `OpenStep`, `External`); slots are transparent hypotheses, never axioms; nothing in a card is an axiom (also VIII.2c, IX.2c) | Lean | `ProofPhase/API.lean`; `docs/unified/API.md` 2; `Problem`, `Problem.holds`, `OpenStep`, `External` | none |
| II.5.2 | Adding a problem takes seven steps (copy the template, write the input, fill a running system or chain and check the ledger inequality, write the open step, call the free theorems, add an uncertainty, state the card) | paper | `docs/unified/API.md` 3 | none |
| II.5.2c | The template's toy settles in 101 steps to 1/100 | Lean | `ProofPhase/API/Template.lean`, `toy_settle_101`, `ticksNeeded_correct` | none |
| II.5.3 | What runs: the settle count, the encoder factors on rational data and the ledger law on rational data are computable and decidable and proved right for the real system; the machine's step and balance test are primitive recursive; the real-valued structures and the undecidability are truth only | Lean | `ProofPhase/API.lean`, `szegoQ`, `elecQ`, `szegoQ_cast`, `elecQ_cast`, `PaysQ`, `PaysQ.pays`, `settle0`; `ProofPhase/ETM/Machine.lean`, `balanceBound`, `estep_primrec`, `halted_primrec` | none |
| II.5.4 | Every continuous character of G0's phase circle is z -> z^n for an integer n, so every label carried on it has integer charge; no hypothesis, true of every instance of the API (X.3.3) | Lean | `ProofPhase/API/Phase.lean`, `chargeQuantisation`, `PhaseLabel.integer_charge`; `ProofPhase/General/GUCharge.lean`, `circle_char` | none |
| II.5.5 | The API proves no open step and adds no mathematics; it does not build a running system for you; interface-only arguments cannot settle P vs NP | paper | `docs/unified/API.md` 5 | none |
| II.6.1 | The arsenal is the set of transferable Lean results that need Mathlib, in `arsenal/` of the `im` repository, pinned to Lean and Mathlib v4.34.0; first modules `Arsenal.R136a1` and `Arsenal.BSD` | paper | `im` repository, `arsenal/README.md`, `arsenal/lean-toolchain`, `arsenal/lakefile.toml` | none |
| II.6.2 | `R136a1 "name" P` is `P` as a named hypothesis, never an axiom; a theorem that needs it takes it as a hypothesis | Lean | `im` repository, `arsenal/Arsenal/R136a1.lean`, `R136a1`, `R136a1.out` | none |
| II.6.3 | `arsenal/tools/lint.sh` (static, no network, no build) fails unless the toolchain is Lean v4.34.0 with Mathlib v4.34.0 the one requirement, every module imports only Mathlib or the arsenal, no module uses an escape hatch (code only), and every module is reached from `Arsenal.lean`; it lists every R136a1 part by name | paper | `im` repository, `arsenal/tools/lint.sh` (read; run for this draft: "lint: OK (3 modules; Mathlib v4.34.0 only; no escape hatch)") | run `tools/lint-selftest.sh` and `tools/check.sh` |
| II.6.4 | What can be transferred moves to the `im` repository and is used from there as a dependency (by repository, subdirectory and commit), never vendored | paper | `im` repository, `arsenal/README.md`, "Using it"; `docs/unified/API.md` 7 | none |
| II.7.1 | Every Lean statement is re-checked by two kernels other than the one that built it (leanchecker replay; nanoda_lib on an export), against a stamped base of Mathlib and Lean core; the run at commit 2cb301c covered 358 modules including the IM arsenal: replay fail=0, no non-standard axiom, nanoda_lib 103,282 declarations with no type-checker error, no escape hatch in code | Lean (re-checked) | `docs/unified/INDEPENDENT-CHECK.md` (run of 2026-11-24); `tools/independent-check.sh` | a full run at the final commit |
| II.4a | The one-box test (the rotation API): a box has one command (the step at the one shared gate, the universal tick), the half-turn to read the other side, and a marker per step, inside or R136a1; the marker is correct when it agrees with the gate's own factor; DMP-complete means correct at every tick from the start | Lean (definitions) | `im` repository, `arsenal/Arsenal/Rotation.lean`, `Arsenal.Rotation.Marker`, `Box`, `Box.gate`, `Box.Correct`, `Box.DMPComplete`; `ProofPhase/ETM/Rotation.lean`, `Box.toArsenal` (the running-system box, equal to IM's by `rfl`) | none |
| II.4b | No outside input: a verdict read after the half-turn is the verdict read from inside; in the plaquette layer the flux read from a box and from its complement agree | Lean | `im` repository, `arsenal/Arsenal/Rotation.lean`, `Box.Gate`, `Box.complete_halfTurn`; `ProofPhase/ETM/RotationInstances.lean`, `crossoverGate`, `crossover_halfTurn` | none |
| II.4c | The test has content only when the marker is the system's own claim: a marker read off the gate afterwards always passes, and a box with a wrong marker exists | Lean | `im` repository, `arsenal/Arsenal/Rotation.lean`, `Box.selfMarked_complete`, `Box.exists_not_complete`; the same in `ProofPhase/ETM/Rotation.lean` for running systems | none |
| II.4d | Rigidity as a one-box test: a manifold's presentations (structure set) with its self-equivalences acting; the rigidity box (gate: reached from the manifold; marker: the claim "rigid") is DMP-complete exactly when the manifold is rigid; rigid from the shared gate (the sharing answered R136a1); a non-rigid case refutes the sharing; two presentations through a map to ZMod 2 are rigid exactly when it is onto; a non-rigid datum exists | Lean | `im` repository, `arsenal/Arsenal/Rigidity.lean`, `RigidityData.box_complete_iff`, `rigid_of_shared`, `not_shared_of_not_rigid`, `twoPoint_rigid_iff`, `exists_not_rigid` | none |

## Part IV. The one assumption and the rigid start (`draft/03-part-III-one-assumption.md`)

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| III.1 | The three open steps share one shape (local positivity, missing for every case, no assembly with slack) | reading | `docs/OPEN-QUESTIONS-DMP.md` 1 | none |
| III.2a | Side-by-side table of the sharpest open steps and the proved obstructions | paper (summary of IV.5.6, V.4, VI.4.10 and their obstructions) | Parts IV-VI | none |
| III.2c | The dag-like protocol is CP's size-indexed "it runs" object | paper | `CP-DUALITY.md` 0.5 | none |
| III.3 | The act carrier settles composition for YM (one number at one scale), not for GRH or NP vs coNP | paper (on IV.3-IV.5) | `docs/OPEN-QUESTIONS-DMP.md` 0, 6; `CONTAINMENT.md` | none |
| III.3b | Three answers: outrun possibility; every block at once; charge the pair at its interface | reading | III.3 | none |
| III.5 | Only in YM is the starting positivity given by construction | paper (observation on II.9) | II.9 | none |
| III.7f | Yang-Mills: the slab chain transports the boundary uncertainty with zero join loss; under a seam transport O1 holds once mu (theta^n u_0 + sigma/(1 - theta)) <= 1; any positive twist ratio clears O1 with enough layers on a fixed lattice | Lean | `ProofPhase/Unified/TransportBridges.lean`, `ym_slab_transport`, `ym_bridge`, `ym_layers_needed`, `elec_le_of_deficit` | none |
| III.7g | Yang-Mills: a cost above the floor at fixed physical length, uniform in the cutoff; in the box geometry the side seam per join (three slabs: at most (1/mu - (sqrt 2 - 1)^3)/sqrt 2) | open | `docs/unified/TRANSPORT.md` 3.1; `SeamTransport` (named) | a proof of either; O1 |
| III.7h | GRH: the margin's relative uncertainty crosses the scale steps at exactly cost = floor (zero slack); zeta's margin is certified with size while the summed remainders stay below log 2; the sign alone is decided step by step | Lean (model: abstract sequences; the identification with zeta's margin is the reading III.7n) | `ProofPhase/Unified/TransportBridges.lean`, `grh_log_transport`, `grh_sign`, `grh_sign_of_sum`, `grh_sign_szego`, `grh_sign_step` | none |
| III.7i | GRH: remainders, measured against the collapsing margin, summable with total below log 2, from the primes alone, beyond Dirichlet | open | `docs/unified/TRANSPORT.md` 3.2 | a proof; GRH beyond Dirichlet |
| III.7j | NP: carrying the line count across the hidden variables, a share e^{-q} each, is exactly a size bound; lifting gives q = c log n, a constant quantum q = c | Lean (from the named external `LiftCP` and the named open `LiftCPConst`) | `ProofPhase/Unified/TransportBridges.lean`, `hiddenTransport_iff_size`, `liftCP_hiddenTransport`, `liftCPConst_hiddenTransport`, `indGadget_quantum` | none |
| III.7k | NP: a constant cost c > 0 per hidden variable for a constant-size gadget (`LiftCPConst`) | open | `docs/unified/TRANSPORT.md` 3.3; `NP-LIFTING.md` 2.3 | a constant-gadget lifting theorem for cutting planes |
| III.7l | In the known lifting proofs the per-block hiding errors add up across all blocks with no damping, which forces the gadget to grow with n | reading (recalled; to be checked against the sources) | `docs/unified/TRANSPORT.md` 3.3; `hiding_accumulates` (Lean, the critical case) | read Mertz-Pitassi, Lovett-Meka-Mertz-Pitassi-Zhang |
| III.7m | The three bridges side by side: under each named hypothesis the uncertainty is transported below the margin and the sign holds | Lean | `ProofPhase/Unified/All.lean`, `three_bridges`, `ym_uncertainty_bound` | none |
| III.7n | Each named hypothesis is the running-state axiom R for its object; under R the three conclusions follow (III.7m), while R for the specific objects is the open step | reading (identification); implication Lean (III.7m) | `PREP.md` (owner, 2026-11-23); III.7m | none |
| III.7o | The transport theorem is not empty: a perturbed Doeblin chain keeps its law in [3/10, 7/10] at every step; without mixing the same kind of perturbation erases the margin | Lean | `ProofPhase/Unified/TransportInstances.lean`, `doeblin_example`, `ident_margin_lost` | none |
| III.54 | The one box is the confined inside: binary and free to assert itself; it exists only as an assertion against an outside (the inside cannot exist without an outside) | reading | `PREP.md`, 2026-11-22, "Inside and outside are one system"; 2026-11-24, last entry | none |
| III.55 | The outside must leave the possibility space free (0 < p < 1: might happen, need not; causality and the gap are one condition) and complete (every configuration has positive weight: compact group, finite action, "every possibility exists"); the two together are the container | reading | `PREP.md`, 2026-11-22, "The possibility space, binary existence, and the reflected assertion" and "Why the possibility space saturates at a definite size"; 2026-11-24, last entry | none |
| III.57 | Yang-Mills quantifier: `HandoverSide` (every cutoff, nontrivial sector and end-face outside: electric side at most sqrt 2 - 1 of the neutral) is O1 at mu = 1 + sqrt 2 at the single length L_h; it implies `HandoverSideRunning` (running outsides only) | Lean (the equivalence and the implication); both statements themselves open | `ProofPhase/Unified/ElectricSUNPress.lean`, `HandoverSide`, `handoverSide_iff`; `ProofPhase/Unified/ElectricSUNRunning.lean`, `HandoverSideRunning`, `handoverSideRunning_of_handoverSide`, `O1_slab_running`, `O1_box_running` | a proof of `HandoverSide` or `HandoverSideRunning`, uniformly in the cutoff (O1; IV.5.6) |
| III.57b | Frozen outsides are not running outsides and are not quantified over; they count as remnants, entering only through their exponentially small weight epsilon, a fresh uncertainty r = epsilon in the transport theorem | reading (identification); transport Lean | `PREP.md`, 2026-11-24, "Frozen faces aren't running outsides"; `ProofPhase/Unified/ElectricSUNRunning.lean`, `runningTransport`, `runningTransport_slab`; `docs/unified/ELECTRIC-SUN.md` 6 | a large-deviation bound on epsilon, uniform in the cutoff (open per `ElectricSUNRunning.lean`) |
| III.58 | GRH quantifier: Weil's form is positive for every test function of L2(-a, a) at the certified supports a = 0.60, 0.65, 0.69 (the universal start {infinity, 2, 3}), from enclosures computed in ball arithmetic (also 0.8) | certified | `docs/unified/GRH-ONEBOX-CERT.md`; `docs/unified/grh_onebox_cert.py`; `ProofPhase/GRH/OneBoxCert.lean`, `onebox_cert_3_5`, `onebox_cert_13_20`, `onebox_cert_69_100` | certify beyond a = 0.69 (V.4) |
| III.58b | The abstract step: a certified finite part, a cross-term bound and a tail bound give W f f >= c norm(f)^2 for every f (the enclosures are named hypotheses) | Lean | `ProofPhase/GRH/OneBoxCert.lean`, `schur_scalar`, `onebox_positive`, `onebox_cert_3_5`, `onebox_cert_13_20`, `onebox_cert_69_100` | none |
| III.59 | NP vs coNP quantifier: a refutation certifies that every assignment falsifies a clause; "every assignment" is the container's quantifier | reading (on Lean refutation completeness, cross-reference to I.4a, VI.3.1) | `ProofPhase/Proof/Complete.lean`, `refutable_iff`; `docs/pnp/DICTIONARY.md` | none |
| III.61 | The container is also where the open step sits: O1 is exactly the requirement that the one box holds for every outside, uniformly in the scale; the container is the precondition the cards share, not a result | reading (on Lean III.57) | `PREP.md`, 2026-11-24, last entry (care point) | O1 |
| III.62 | The container asks two things of each tick: from the inside a margin is carried, from the outside the twisted sector is refuted; these are the two edges of section 2 | reading | `PREP.md`, 2026-11-24, last entry; III.15 | none |
| III.63 | The care point of the container is answered by construction: the process from G0 to the hand-over (the ODP) is one established process, and once that is accepted every start gets a direction through {infinity, 2, 3} | reading | `PREP.md`, 2026-11-24, last entry ("The owner on the care point") | none |
| III.64 | The paper's one assumption: the process from G0 to the hand-over is established, i.e. the one box is a running, DMP-complete system (the MP-type existence assumption; O1 as the corollary of running, slotted as the named hypothesis R); stated once (Part III section 4.4), not proved | open | `PREP.md`, 2026-11-24, "O1 ... must always be the open step", "DMP being O1", last entry; III.7n, III.28, III.61 | a proof of the running state for each object (O1; V.4; VI.4.10) |
| III.64a | The one assumption has two edges: O1 (decay, upper) and the scale-uniform lower edge of non-triviality (IV.9.5b); the owner's reading puts both in it, since the ODP ends only at a dimensionless 1, so a DMP-complete system carries a unit and a correlation that does not vanish by construction; in Yang-Mills the unit is Lambda (dimensional transmutation) | reading (the fold); the two edges independent and compatible in the model: Lean | `PREP.md`, 2026-11-24, "Five answers", 1; `ProofPhase/Closures/NonTrivialSplit.lean`, `gap_not_lower`, `gap_and_lower_compatible`; Part I, I.5 | none for the fold; the lower edge itself is open with III.64 |
| III.64b | Definition (the owner): DMP-complete means runs on DMP, i.e. the object's running-state hypothesis R holds (III.28, III.7n); circular as DMP is, since R cannot be certified from inside (III.29) | reading | `PREP.md`, 2026-11-24, "Five answers", 4 | none |
| III.65 | At the start {infinity, 2, 3} the first tick is certified positive with a margin (Weil's form on supports up to a = 0.69: c = 1.5e-9, 3.4e-11, 6.4e-13 at a = 0.60, 0.65, 0.69), so the sign is fixed there | certified (ball-arithmetic enclosures); abstract step Lean (III.58b) | `docs/unified/GRH-ONEBOX-CERT.md`; `ProofPhase/GRH/OneBoxCert.lean` | certify beyond a = 0.69 |
| III.66 | Under the acceptance of III.64, the sign at the start, and with it the direction of every later tick, is fixed; for every tick past the start this is conditional on III.64 and is not a theorem that the margin survives (it collapses to about 3.6e-15 at a = 0.75) | conditional (on III.64) | `PREP.md`, 2026-11-24, last entry; `docs/unified/GRH-ONEBOX-CERT.md` | III.64 |
| III.67 | Reading rule for "conditional on the established process": a result so marked holds if III.64 holds; the Lean theorems of section 2, the transport theorem (II.1) and the certified start do not use III.64 | paper (editorial rule) | Part III section 4.4 | none |
| III.68 | One-box certificate: correct at the start and one step at the shared gate keeps it correct, hence correct at every tick (exact along the run) | Lean | `im` repository, `arsenal/Arsenal/Rotation.lean`, `Box.onebox_certificate`, `Box.dmpComplete_iff_orbit`; applied in `ProofPhase/ETM/Rotation.lean` | none |
| III.68a | Scale certificate: if every scale's box is rebuilt from the one box through its gate (same margin, a morphism keeping step, factor and mass, start to start, carrying the marker), a box certified at one scale is correct at every scale; a scale with a wrong marker refutes the sharing | Lean (from the named hypothesis III.64) | `im` repository, `arsenal/Arsenal/Rotation.lean`, `Box.scale_certificate` (the sharing answered R136a1); `ProofPhase/ETM/Rotation.lean`, `Box.SharedGate`, `Box.scale_certificate`, `Box.onebox_everywhere`, `Box.not_shared_of_wrong`, `Box.sharedGate_self` | a proof of III.64 |
| III.68b | Sharing the gate alone is free (every system maps uniquely into the terminal object); the content of III.64 is that the marker travels with the gate | Lean (the free part); reading (the content of III.64) | `ProofPhase/ETM/Rotation.lean`, `Box.gate_through_trace` | none |
| III.68c | The universal machine is a box whose DMP-completeness from a description is exactly "the description runs forever", undecidable over descriptions (as is settling); on the contraction class the test settles from the explicit tick balanceBound, so DMP-completeness is a finite check | Lean | `ProofPhase/ETM/Rotation.lean`, `etmBox`, `etmBox_complete_iff`, `etmBox_complete_undecidable`, `etmBox_settles_undecidable`, `Box.settles_of_contracting`, `Box.complete_iff_bounded`, `rotation_edge` | none |
| III.68d | The owner's ground for III.64: GRH gives meaning to anything translated through it, so assuming it is a valid encoder across scales, correctness is inferred; in the test a valid encoder between scales is the shared gate (a morphism keeping step, factor and mass, carrying the marker, same margin), and the inference is `scale_certificate`; the clause "same margin" carries the floor, which GRH alone does not supply (III.17), so the validity assumption is III.64 itself | conditional (on III.64; the inference Lean) | `ProofPhase/ETM/Rotation.lean`, `Box.SharedGate`, `Box.scale_certificate`; `ProofPhase/Unified/Encoder.lean`, `refl_map`; `docs/unified/ROTATION-API.md` 3(2); `PREP.md`, 2026-11-24, "The one-box test", "GRH as a valid encoder" | III.64 |
| III.69 | The rigid start: the largest start built from SU(N) that a description can certify is the point with 2 and 3 (A.3k), the shape of {infinity, 2, 3} | reading | `PREP.md`, 2026-11-24, "The rigid start"; A.3k | none |
| III.69a | SU(N) as the language of the encoder: the encoder is a norm-preserving map of an inner product space (Lean); the determinant-1 norm-preserving maps of C^N form SU(N), and every compact Lie group is a closed subgroup of some U(N) (Peter-Weyl); "language" is the owner's reading | classical (the facts); Lean (the encoder); reading (language) | `ProofPhase/Unified/Encoder.lean`, `Encoder`, `refl_map`; Peter-Weyl | none |
| III.69b | Speaking (a valid encoder, the shared gate) and being understood (a correct marker) give DMP-completeness at every scale | Lean (the implication; the identification is a reading) | `im` repository, `arsenal/Arsenal/Rotation.lean`, `Box.scale_certificate`; `ProofPhase/ETM/Rotation.lean`, `Box.scale_certificate` | none |
| III.69c | Anything that rotates correctly from the rigid start is correct if DMP is correct | conditional (on III.64) | III.69b; III.64 | III.64 |
| III.70 | A system is DMP-complete in the paper's sense exactly when its start forces a floor, so that the rotation test is decidable; a class positivity cannot act on (Z/2) sits on the undecidable side | reading | `PREP.md`, 2026-11-24, "Only a start that forces a decidable reading"; III.68c; III.65 | none |
| III.70a | No ordered ring has characteristic 2 (1 + 1 = 0 contradicts 1 > 0), so Z/2 carries no order and no floor can be stated in it | classical | elementary algebra | none |
| III.71 | The one assumption read as a leak axiom: anything within a DB shares a universal truth, so a subset cannot attach without it; for the gate this is a theorem (every running system maps uniquely into the universal one; a subsystem attached by inclusion shares its trace), and what stays assumed is that the marker travels with the gate | reading (the gate part: Lean) | `PREP.md`, 2026-11-24, "The one assumption as a leak axiom"; `ProofPhase/ETM/RunSys.lean`, `exists_unique_hom`, `trace_unique`, `univIsTerminal`, `subIncl`; III.68b | III.64 |
| III.9 | GRH asks of the tick distance: finite at every tick (sign); uniformly bounded, d_N <= D (multiplicative transport, enough for the sign, not needed by it) | open | `docs/unified/GRH-TO-O1.md` 3a; `ProofPhase/GRH/Transfer.lean`, `margin_pos_of_factors` (the finite part, Lean) | GRH beyond the finite model |
| III.10 | O1 holds exactly when some mu' > mu has mu' p1 <= p0 for every outside (uniform ratio bound), and exactly when p0 - mu p1 >= delta p1 uniformly (a strict margin); the electric cost is log(p0/p1); encoder form of the one-box step | Lean | `ProofPhase/Unified/GRHToO1.lean`, `ymOneBox_iff_ratio`, `ymOneBox_iff_margin`, `cost_eq_log_ratio`; `ProofPhase/Unified/Encoder.lean`, `oneBox_iff_refl` | none (O1 itself is IV.5.6) |
| III.11 | On one tick sequence with encoders at least theta > 0 from the lossless point, the carried Szego margin falls below every m > 0: a uniform margin and O1 at every tick exclude each other | Lean | `ProofPhase/Unified/GRHToO1.lean`, `o1_ticks_kill_margin`, `uniform_margin_excludes_o1` | none |
| III.12 | Multiplicative transport (a lower bound on the factors) and O1 in factor form (an upper bound below 1/mu) are independent: lossless ticks transport and fail O1; factors 2^{-n}/(2 mu) satisfy O1 and transport nothing | Lean | `ProofPhase/Unified/GRHToO1.lean`, `transport_not_decay`, `decay_not_transport` | none |
| III.13 | On the two-sector cone, bounded Birkhoff spread and O1 are independent (all ratios 1: spread 0, O1 false; ratios e^{-n}/(2 mu): O1, unbounded spread) | Lean | `ProofPhase/Unified/GRHToO1.lean`, `spread_without_o1`, `o1_without_spread` | none |
| III.14 | One tick sequence with factors in a band e^{-D} <= f <= e^{-kappa}, kappa > log mu, uniformly would give both edges; no known object has both the zero measure's Verblunsky steps and the box's sector ratios as ticks, and no known result supplies either edge | open | `docs/unified/GRH-TO-O1.md` 3a, "Named exactly" | a proof of either edge |
| III.15 | GRH prescribes the existence side, O1 the non-existence side, of the same distance (the two edges of one band) | reading | `PREP.md`, 2026-11-24, "What GRH and O1 share"; III.8 to III.14 | none |
| III.16 | For any statement H and any card with an input that fails the open step, "H implies every input meets the open step" is equivalent to "not H"; so "RH implies O1 on every input", the same for Dirichlet GRH and for the GRH card's open step, is equivalent to the statement being false | Lean | `ProofPhase/Unified/GRHToO1.lean`, `imp_all_iff_not`, `badInput`, `badInput_not_open`, `rh_imp_card_iff`, `dirichlet_imp_card_iff`, `grhCard_imp_card_iff`, `pair_model` | none |
| III.17 | In the finite model, under the card's open step the Toeplitz form at scale k is positive with margin exactly 0 (a null vector exists); no positive margin is certified at the closure | Lean | `ProofPhase/Unified/GRHToO1.lean`, `exists_null`, `toepForm_atoms_null`, `no_margin_at_closure`, `grh_margin_exactly_zero` | none |
| III.18 | Positive sector weights (encoder strictly inside the disk) with O1 false exist for every mu >= 1 | Lean | `ProofPhase/Unified/GRHToO1.lean`, `positivity_without_o1` | none |
| III.19 | `ZetaCoupling`: a bound on the sector ratio, valid for every outside and controlled by RH; the coupling and RH give O1, and O1 alone gives the coupling. Its content for 4D SU(N) is not known | Lean (definition and the two implications); content open | `ProofPhase/Unified/GRHToO1.lean`, `ZetaCoupling`, `o1_of_coupling`, `coupling_of_o1` | the coupling itself (no easier than O1) |
| III.20 | 2D SU(2) zero-area sectors: Z_{e=1} = 2^{-s} Z, Z_{e=0} = (1 - 2^{-s}) Z, Z = re zeta(s), sector domination iff mu + 1 <= 2^s, twist ratio 1 - 2^{1-s} (s = 2g - 2 > 1); zeta cancels from every sector ratio | Lean | `ProofPhase/Unified/GRHToO1.lean`, `Ze1_eq`, `Ze0_eq`, `zeta_re_eq`, `sector_dom_iff`, `twist_ratio` | none |
| III.21 | The SU(2) zero-area partition function on a closed surface of genus g >= 2 is zeta(2g - 2) | external | Witten, CMP 141 (1991); `docs/unified/GRH-TO-O1.md` 4, 7 | a re-read of the source |
| III.22 | A margin of Weil's form at scale k + 1 is one at scale k: growing the support is restriction to nested sections, not iteration | Lean | `ProofPhase/Unified/GRHToO1.lean`, `sec_restrict` | none |
| III.22b | Szego recursion steps are SU(1,1) isometries of the cone, whose image is the whole cone: Delta = infinity, Birkhoff-Hopf gives factor 1 (also at the start {infinity, 2, 3}) | classical | `docs/unified/GRH-TO-O1.md` 3a; `GRH-LENS.md` 6.5 | none |
| III.22c | Prime powers enter Weil's form additively as indefinite symmetrised translations; adding one consumes margin | classical | `docs/unified/GRH-TO-O1.md` 3a; `docs/rh-guide/grh/INDUCTION.md` 1; `ProofPhase/GRH/Transfer.lean`, `two_term_bound` (two-term bounds only add, Lean) | none |
| III.23 | GRH asks that something exists (a margin stays at every tick); O1 asks that something is falsifiable (every twisted state is refuted at every box): the duality inherent in the construction of DMP-complete systems | reading | `PREP.md`, 2026-11-24, same entry, the owner's sharpening | none |
| III.24 | RH is a Pi-0-1 statement: one computable counterexample refutes it (Lagarias' criterion; Davis-Matiyasevich-Robinson); the notes say the same of GRH for Dirichlet L-functions | classical | `PREP.md`, 2026-11-24, same entry; references as the notes cite them, not re-read here | check the references |
| III.25 | The Yang-Mills problem asks for an existence (a continuum theory with a gap) | classical | the Clay statement; Part V.0 | none |
| III.26 | Stated whole, each problem has the logical form of the other's role in the band: the duality appears twice (roles; statements, mirrored) | reading | `PREP.md`, 2026-11-24, same entry, care point; III.23 to III.25 | none |
| III.27 | Each of the three cards of Parts IV to VI is a `Problem` with one `OpenStep` slot, proved "open step gives conclusion"; slots are hypotheses, never axioms | Lean | `ProofPhase/API.lean`, `Problem`, `Problem.holds`, `OpenStep`, `External`; `ProofPhase/API/YangMills.lean`, `API/GRH.lean`, `API/NP.lean`; `docs/unified/API.md` 2 to 4; `API/YangMills.lean`, `API/GRH.lean`, `API/NP.lean` (`problem` in each) | none |
| III.28 | The structural sense of "O1 is always the open step": every card's open step is the running-state hypothesis R, "this object runs"; the form layer proves everything else | reading | `PREP.md`, 2026-11-24, "O1 ... must always be the open step"; `ProofPhase/Unified/All.lean`, `three_bridges` (Lean, see III.7m, III.7n) | none |
| III.29 | The logical sense: a system cannot certify its own running from inside (Goedel II; the settling machine cannot decide balance for all content); "open from inside" is not "unprovable"; DMP's own running assertion is its O1 | reading (on classical Goedel II and Lean II.3.3) | `PREP.md`, 2026-11-24, "O1 ... always the open step" and "DMP being O1" | none |
| III.31 | At G0 a gap and an arrow must be established: the gap makes each tick's answer binary (passes, or outside); the arrow orders the ticks, so a later excision is a later tick, never a revision | reading (on Lean II.3.2, II.3.3) | `PREP.md`, 2026-11-24, "The residue is why G0 must establish a gap and an arrow" | O1 (the floor in the continuum) |
| III.32 | The floor is at least the existence tied to the error bars; with the floor as hypothesis, a run settles to within the error bar in an explicit number of steps | reading (identification); Lean for the implication | `PREP.md`, 2026-11-24, "The floor is always at least ..."; `ProofPhase/ETM/Machine.lean`, `reaches_of_contracting` | none |
| III.34 | It would be circular to justify O1 by "the floor is at least the error bar" and then the error bar by O1's rate; the settle theorem takes the floor as a hypothesis, which keeps it honest | paper | `docs/unified/GRH-TO-O1.md` 6 | none |
| III.36 | Presburger arithmetic and Tarski's real closed fields are complete decidable fragments (Goedel's theorems for a whole consistent, effectively axiomatised theory containing arithmetic: I.8h) | classical | Goedel 1931; Presburger 1929; Tarski; `PREP.md`, 2026-11-24, "Point 3 is how DMP passes the incompleteness argument" | none |
| III.37 | DMP's excision is decision per tick, with R136a1 as the answer for "outside"; at tick n everything not yet decided is outside | reading (on Lean II.3.2, II.3.3; classical for "provable within n steps" being decidable) | `PREP.md`, 2026-11-24, same entry | none |
| III.38 | "Outside at tick n" can become "inside at a later tick": a new act, never a revision of the earlier tick; the set of all sentences ever decided is not decidable in general | reading | `PREP.md`, 2026-11-24, same entry, care point 1 | none |
| III.39 | The Clay statements, being arithmetic and analysis, cannot be excised as a class: an independent one would be answered R136a1, "outside", which is not settling; the owner: the assertion states that an O1 of that behaviour exists and lints everything that cannot survive it | reading | `PREP.md`, 2026-11-24, same entry, care point 2 and the owner's answer | none |
| III.40 | `sorry` (reported as `sorryAx`) and R136a1 (a named hypothesis the lint lists) are independent channels; a result passing both is certified twice, for form only | reading (mechanisms: Lean, III.35, and the pin and lint scripts, paper) | `PREP.md`, 2026-11-24, same entry; `INDEPENDENT-CHECK.md` | none |
| III.41 | A missing expected tick is an answer too: the part is outside (the time-to-live of every act; the cutoff of the settling machine) | reading | `PREP.md`, 2026-11-24, same entry, the owner's answer to point 1; Outlook | none |
| III.42 | The finite loss excised at the beginning is the floor at the error bars: a fixed finite cost paid once; every act is then constructible inside or R136a1 | reading | `PREP.md`, 2026-11-24, same entry, the owner's answer to point 3 | none |
| III.43 | Nothing in this construction makes a theory with arithmetic complete; the completeness is that of the generalisation over what is inside at each tick | classical (for the incompleteness side) | `PREP.md`, 2026-11-24, same entry, care point 3; III.36 | none |
| III.45b | A uniform margin (infimum above zero over all scales) is false for zeta's zero measure: the zero side is purely atomic, the product of Szego factors is exp(integral of log w) = 0 | classical | Szego-Kolmogorov-Krein; `docs/unified/GRH-TO-O1.md` 3a; `INDUCTION.md` 1 | none |
| III.46 | The continuum needs a uniform bound on the tick factors; which bound (lower edge for GRH, upper edge for O1) is the open step of each card | open | III.9, III.10; `PREP.md`, 2026-11-24, "Base existence as SU(p + (p+1))", the owner's refinement | the bounds of III.14 |
| III.47 | The tick operator is an act at a DB, rotating; the encoder's half-turn is its rotation | reading | `PREP.md`, 2026-11-24, "The multiplicative transport is the tick operator" | none |
| III.48 | A positive map whose image cone has finite Hilbert projective diameter Delta contracts the projective distance by tanh(Delta/4) | classical | Birkhoff 1957; Hopf 1963 (recalled, not re-read) | none |
| III.49 | Yang-Mills slab chain: the single-layer floor e^{-2s} gives abs(Z_{e=1}) <= tanh(s)^{n+1} Z_{e=0} for every end-face outside (SU(2) Wilson: s = beta N), with no join loss | Lean | `ProofPhase/Unified/JoinLossSlab.lean`, `kchain_tanh`, `kchain_elec`, `elec_exp_neg_two_mul` | none |
| III.51 | A file containing its own hash, or two files containing each other's current hashes, is a fixed point of sha256, which no one can compute; the hash itself is one-way | classical | design of the hash; `PREP.md`, 2026-11-24, "DMP as a recipe", "Rotatable, not negatable" | none |
| III.52 | "Rotatable hash": across versions the pin passes from one node to the other, one turn per tick, the same half-turn shape as the encoder's; no hash function is rotated, the roles of pinner and pinned are | reading | `PREP.md`, 2026-11-24, "Rotatable, not negatable" | none |
| III.53 | Inside the system the time-to-live of a certification is not a separate mechanism: every certification is re-made at each tick against the same shared root, so any hash's validity window is bounded by the interval between two ticks; what leaves the inside is the boundary's matter | reading | `PREP.md`, 2026-11-24, "Correction: the post-quantum world is the inside of CMOS" | none |

## Part IV. Yang-Mills (`draft/04-part-IV-yang-mills.md`)

Full chain: `docs/mass-gap/weak-coupling/PROOF-BLUEPRINT.md` (version 2). Crossover notes: `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/`.

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| IV.0 | The Clay statement is not proved here | (scope) | IV.0 | O1-O4 |
| IV.1.1 | Wilson measure, SU(2) and compact G | Lean | `AreaLaw/ConcreteSUn.lean`, `OneScale/` (`isCompact_SUn`) | name the Wilson measure declaration |
| IV.1.3 | Transfer kernel, centre flip symmetry, sector identity | Lean (identity definitional) | `Attempts/R4/LayerKernel.lean` (`wilsonKernel`, `wilsonKernel_nonneg`, `wilsonKernel_symm`), `LayerSector.lean` | name the declarations of the centre flip and the sector identity |
| IV.1.4 | 't Hooft duality, Euclidean form | Lean | `ProofPhase/RouteB/Duality.lean`, `tHooft_rotation` | none |
| IV.1.5a | Good blocking: centre-covariant, RP at every level | Lean (dyadic block sizes `T.ℓ k = 2^n k`; centre covariance is in the module header, not in `goodBlocking_rp`) | `ProofPhase/RouteA/Blocking.lean`, `goodBlocking_rp` | none |
| IV.1.5b | Good blocking has a non-trivial limit at fixed L1 | paper | `proof-phase/ws1-routeA/NOTE.md` | Lean |
| IV.1.6 | Z_tw,k < Z and 0 < Z_tw,k for beta != 0 (strict twist bound), every SU(N), every nontrivial centre element, every even time extent and spatial background; SU(2) is the case N = 2 | Lean | `ProofPhase/General/SUNTwistWilson.lean`, `sunZtw_lt`, `sunTwistRatio_mem`, `sunZtw_pos`; `ProofPhase/General/SUNTwistInstances.lean`, `su2N_Ztw_lt`, `su3_Ztw_lt`, `su5_Ztw_lt`, `su11_Ztw_lt`; `ProofPhase/Flip/Strict.lean`, `su2_Ztw_lt_Z`; `docs/unified/sunprimes-axioms.log` | none |
| IV.1.7 | Transfer kernel at fixed cross-section strictly positive | Lean | `ProofPhase/Flip/Bound.lean`, `stepK_pos` | none |
| IV.2.1 | Dobrushin with weights; D' gives block decay (abstract) (also II.12.3b: exponential decay of correlations with weights, `theoremA_w`) | Lean (abstract; hypotheses `GDSw`; `LocalConvergenceW`, `LimitFlatW`) | `Attempts/R3/TailDecay.lean`, `theoremA_w`; `Attempts/R3/Robust.lean`, `gap_of_localFactorsW` | none |
| IV.2.2 | Corollary B, physical units | Lean | `OneScale/CorollaryB.lean`, `corollaryB_lattice` | none |
| IV.2.3 | Windowed OS route to MassGapLoc | Lean (from `UVTVBlockGap`) | `ProofPhase/OS/GapLoc.lean`, `massGapLoc_of_UVTVBlockGap`; `ProofPhase/M1/UVTVOS.lean`, `gap_of_RP` | none |
| IV.2.4 | Assembly: OpenPieces -> MassGapLoc, LimitRP, NonTrivial | Lean (from `OpenPieces`) | `ProofPhase/Torus/Top.lean`, `yang_mills_assembly` | none |
| IV.2.5 | Gap in both orders of limits | Lean (hypotheses: `OnLCP`, `NonTrivial`, `BlockedTorusRoute`; `TorusDecay` and `Tendsto T.a atTop (nhds 0)` for the both-orders form) | `ProofPhase/Torus/Top.lean`, `yang_mills_assembly_torus`; `ProofPhase/Existence/Bridge.lean`, `bothOrders_of_torusDecay` | none |
| IV.2.6 | Pure noise and bounded couplings fail OpenPieces | Lean | `ProofPhase/Assembly.lean`, `not_trivial`, `not_onLCP_of_bounded` | none |
| IV.2.7 | MassGapLoc implies a spectral gap of the continuum Hamiltonian | paper (spectral bridge Lean) | `ProofPhase/Bridge/Spectral.lean`, `ProofPhase/Bridge/OSLink.lean` (`spectral_gap_iff`, `gap_of_RP_spectral`) | Lean density/reconstruction |
| IV.2.8 | Strong-coupling gap, any compact group | Lean / paper | `OneScale/SingleLink.lean` (`gds_single`, `wilson_singleLink_decay`) | split Lean/paper parts |
| IV.2.9 | The crossover needs no description of its content; the certificate is checked on the actual blocked law, uniformly over outsides | paper | `PREP.md` (crossover entry, 2026-11-23) | none |
| IV.3.1 | Per-box hand-over rate >= 0.881 | Lean (0 < Z_tw as hypothesis) | `ProofPhase/Crossover/HandOver.lean`, `su2_handover` | formalise 0 < Z_tw |
| IV.3.3 | Flux law the same from inside and outside; no sources | Lean | `ProofPhase/Crossover/Dichotomy.lean`, `cob_restrict_eq_cob_restrict_compl`, `sum_cob_restrict_eq_zero` | none |
| IV.3.4 | Superadditivity up to the excess terms; the rate multiplies if F_e(L) > 2c(L) (the converse is not proved) | Lean (abstract) | `ProofPhase/Crossover/CompositeHTF.lean`, `flux_superadd`, `flux_superadd_iter` | link to the measure |
| IV.3.5 | Uniformity along the chain | classical | translation invariance; `ProofPhase/Mixing/Chain.lean`, `contracts_kpow` | none |
| IV.3.6 | One-box contraction at fixed physical size gives a physical mass; uniform floor gives physical decay along a chain | Lean | `ProofPhase/Crossover/Neighbours.lean`, `phys_rate_of_uniform`; `ProofPhase/Crossover/RDoeblin.lean`, `rdoeblin_physical_decay` | none |
| IV.3.7 | Doubling law with fixed loss gives the gap | Lean (implication) | `ProofPhase/Flip/Floor.lean`, `su2_gap_of_doubling_defect` | premises |
| IV.4.2 | Doeblin mass per box goes to zero in the continuum | Lean | `ProofPhase/Crossover/Neighbours.lean`, `neg_log_one_sub_le`, `doeblin_mass_tendsto_zero` | none |
| IV.4.3a | Grid needs floor exponent below log(8/7) = 0.134 (column form, 2d = 8 channels; general k: C < log(k/(k-1))); in the disagreement-percolation form 1 - e^{-C} < p iff C < -log(1 - p) | Lean | `ProofPhase/Crossover/RDoeblin.lean`, `floor_column_requirement`, `floor_disagreement_requirement` | none |
| IV.4.3b | At L_* the floor exponent is in the tens | paper | `RDOEBLIN.md` 0 | none |
| IV.4.3c | The disagreement-percolation form of the floor requirement uses the site-percolation threshold of Z^4, p_c about 0.197, so -log(1 - p_c) is about 0.22 | classical (recalled) | `RDOEBLIN.md` 0, 3 | re-read |
| IV.4.4a | 't Hooft multi-sector relation (1 + S_tw)(1 + S_e) = 2^n | paper | `TRANSFER.md` 0.1 | Lean |
| IV.4.4b | The relation forces nothing for n >= 2; quantitative 't Hooft criterion | Lean | `ProofPhase/Crossover/Runs.lean`, `min_le_of_sector_product`, `selfdual_sector_ge_one`, `electric_sum_lt_one_iff` | none |
| IV.4.5a | A gauge-covariant frame carries no gauge-invariant information (finite) | Lean | `ProofPhase/Crossover/CompositeHTF.lean`, `weight_fiber_eq`, `weight_fiber_mul_card` | none |
| IV.4.5b | The same for compact groups; composite HTF exists on every collar | paper | `HTF.md` 0 | Lean |
| IV.4.6 | At typical fields the summed boundary influence drops below one at about 7 cells | numerical | `NEIGHBOURS.md` 0.2 | supremum, not typical |
| IV.5.1a | r < 1, r = (1 - e^{-F_e})/(1 + e^{-F_e}) <= F_e, F_e >= 0 | Lean | `ProofPhase/Crossover/Containment.lean`, `twist_ratio_eq`, `twist_ratio_le_elecF`, `elecF_nonneg` | none |
| IV.5.1b | Small box: F_e = O(g(L)^2) | classical (recalled, not re-checked) | Luescher; van Baal; `CONTAINMENT.md` 1 | re-check |
| IV.5.2a | At fixed cross-section F_e(T) grows without bound | Lean (core; hypothesis: gapped flux sector, `Z1 T <= C mu^T l^T` with mu < 1) + classical (Jentzsch) + paper (centre invariance) | `ProofPhase/Crossover/Containment.lean`, `elecF_lower_of_gap`, `exists_elecF_ge`; `CONTAINMENT.md` 2 | Lean Jentzsch step |
| IV.5.2b | Cubic boxes: F_e(L) >= 0.881 at some L | open (near L = 4 at beta 2.3, numerical) | `CONTAINMENT.md` 2 | a confinement input at one scale |
| IV.5.3 | Gauss's law makes influence path-like | paper (Lean pieces IV.3.2, IV.3.3) | `CONTAINMENT.md` 6.1 | Lean |
| IV.5.4a | Path sums converge iff F > log mu; 0.881 loses for mu >= 3 (the d >= 3 loss to the 0.881 hand-over is II.13.2) | Lean | `ProofPhase/Crossover/Containment.lean`, `path_sum_summable_iff`, `tube_threshold` | none |
| IV.5.4b | mu_4 = 6.77; log mu_4 in [1.39, 1.95] | classical (recalled) | `CONTAINMENT.md` 3 | none |
| IV.5.4c | The connective constant of self-avoiding walks on Z^d is at least d, so the 0.881 hand-over loses to path entropy in every d >= 3 | classical | elementary counting (Part IV 5) | none |
| IV.5.5a | Bogomolny bound; fractional floor pi^2 beta for admissible fields | classical | Bogomolny; 't Hooft; Luescher; `CONTAINMENT.md` 6.2 | none |
| IV.5.5b | The floor helps only outside (multi-plane twists) and loses to entropy as a -> 0 | paper (one-loop sketch) | `CONTAINMENT.md` 6.2 | determinants and measure |
| IV.5.6 | **O1:** F_e(L) - 2c(L) > log mu_4 = 1.91 at one box of fixed physical size, uniformly over outsides, with c(L) the neutral excess act; the familiar form F_e(L) > 1.91 (r > 0.74) drops it and is implied by it (c(L) >= 0), but alone does not give the chain (IV.5.8) | open | `CONTAINMENT.md` 0, 5; `docs/OPEN-QUESTIONS-DMP.md` 0 | a worst-case argument for one box |
| IV.5.7 | Per-box costs multiply over the lattice: with O1 in its per-outside Lean form (IV.5.9) the composition of the per-box influences is a theorem, and no annealed quantity enters; the annealed-to-quenched identification is needed only to read a torus measurement of F_e as evidence about O1 (IV.7) | Lean | `ProofPhase/OneBox/Fine.lean`, `fineDecayInv_of_fineOneBox`; `ProofPhase/Closures/OneBoxForm.lean`, `decay_of_o1Form`; in the API chain model `ProofPhase/Unified/YangMills.lean`, `pathSum_eq` | none (the open content is O1, IV.5.6) |
| IV.5.8 | In the transfer-matrix model the chain criterion F_e(L) > 2c(L) and the tube threshold F_e(L) > log mu are independent (examples both ways); the joint form F_e(L) - 2C > log mu, with C bounding the excess act on the multiples of L and mu >= 1 continuations, gives both, and the multiplied path sum mu^k e^{-F_e(kL)} decays at rate F_e(L) - 2C - log mu and is summable | Lean (model) | `ProofPhase/Closures/ChainJoint.lean`, `joint_gives_both`, `tube_not_chain`, `chain_not_tube` | none for the model; turning paths in the cubic geometry are carried by O1's per-outside form (IV.5.9), not by the model |
| IV.5.9 | O1 in one Lean form: `FineOneBox` (one box of the SU(2) Wilson measure at the physical cell scale, influence bounds under every boundary condition, uniform in level and volume). `WilsonOneBox` (the actual DLR kernel) and `FineOneBoxSplit` imply it; it feeds `yang_mills_assembly_onebox`. `BlockGapBddW` is the separate blocking route's decay input and `FineOneBoxPat` an alternative criterion with its own assembly; neither is needed | Lean | `ProofPhase/Closures/OneBoxForm.lean`, `O1Form`, `o1Form_of_wilson`, `o1Form_of_split`, `decay_of_o1Form`, `gap_of_o1Form` | none; reading the number F_e(L) > log mu_4 of IV.5.6 as `FineOneBox`'s one-box sum is path counting, paper |
| IV.6.1 | Tick-unit floor Z_tw/Z >= e^{-2 beta L^2} | Lean (the pointwise weight bound `hpt` for the Wilson action, giving c = e^{-2 beta L^2}, is an input) | `ProofPhase/Crossover/Saturation.lean`, `ratio_floor_of_pointwise`, `exp_floor_ge_iff` | none |
| IV.6.2 | A large electric free energy forces a saturated twist | Lean | `ProofPhase/Crossover/Saturation.lean`, `twist_ratio_of_elecF` | none |
| IV.6.3a | Upper decimation normalisation >= 1 (Jensen) | Lean | `ProofPhase/Crossover/Saturation.lean`, `jensen_normalization` | none |
| IV.6.3b | Bond-moving localises the interpolation step (Tomboulis) to one box; mismatch vanishes at fixed physical size | paper (sketch) | `SATURATION.md` 0 | a matched lower bound |
| IV.6.3c | Tomboulis 2007 proposed confinement along this line; gaps pointed out (Ito, Seiler) | classical | `PREP.md` (duality entry) | none |
| IV.6.4 | Kanazawa's bracket is the non-strict form of IV.1.6 | classical | `SATURATION.md` 0 | none |
| IV.6.5 | Dichotomy part (a) fails uniformly at the SO(3) cut | paper | `DICHOTOMY.md` 0.2 | none |
| IV.6.6 | Reduction to two bad events | paper | `DICHOTOMY.md` 0.4 | bounds on both events |
| IV.6.7 | Window 0.18 to >= 1.79 nats per plaquette (the disjointness of the windows is Lean, II.14.6) | paper | `DICHOTOMY.md` 0.3; II.14.6 for `window_gap` | none |
| IV.6.8 | Y2-Y5: inside residue, window hand-over, condition A uniformly, uniformity in volume | open (per-volume gap Lean conditional on H2-all) | `docs/OPEN-QUESTIONS-DMP.md` 2; `ProofPhase/Quantum/PerVolume.lean`, `perVolumeGap` | pieces of O1 |
| IV.6.9 | IR column at L1; W1 column certified 0.99988 at L sqrt(sigma) = 2.80 | open (implication Lean) | `ProofPhase/Certified/Measured.lean`; `proof-phase/c9b-adjoint/ROUTE3.md` | supremum certificate |
| IV.7.1 | Small tori at beta 2.3: F_e(6) = 2.6 centrally, lower bound 0.96 with the floor | numerical (preliminary) | `CONTAINMENT.md` 1, 3; `SATURATION.md` 0 | refutation only |
| IV.7.2 | Chain criterion refuted at cross-section 16^3, beta 3.5, L = 1 (pre-registered); L <= 2 post hoc | numerical | `ONEBOX-CHECK.md` 4, 7 | none (does not bear on O1) |
| IV.7.4a | 8 pi^2 = -4 zeta(2)/zeta(-1); zeta(-1) = -1/12 | Lean | `ProofPhase/GRH/Mirror.lean`, `eight_pi_sq_mirror`, `zeta_neg_one_val` | none |
| IV.7.4b | O1 in effective-string units: L sqrt(sigma) > 1.72 to 1.80 | numerical (model-based) | `docs/rh-guide/MIRROR.md` 0.2 | none |
| IV.7.4c | The mirror brackets F_e(L) between two ends and does not constrain the middle | reading | `docs/rh-guide/MIRROR.md` 0.2 | none |
| IV.8.1 | "It runs" in two targets | Lean | `ProofPhase/Crossover/Runs.lean`, `no_phase_mode`, `iterate_contraction`, `runs_two_targets` | none |
| IV.9.1 | UV stability and one-loop running (construction by others) | external | `H1-OPENAI.md` | audit |
| IV.9.2 | Balaban's control preserves partition functions, not laws | classical | `proof-phase/c5d-supplier/BALABAN-READING.md` | none |
| IV.9.3 | M1 law-preserving large-field step, weak coupling up to L_* | paper (Lean parts, from `M1Hypotheses`) | `ProofPhase/M1/Assembly.lean`, `m1_assembly`; `proof-phase/m1-tools/M1-PLAN.md` | Lean |
| IV.9.4 | Continuum limit exists | external | `H1-OPENAI.md`; `ProofPhase/Existence/Bridge.lean`, `plaqLaw_eq_wilsonMeasure` | audit |
| IV.9.5 | The gap needs of the line of constant physics only its resolution clause (l_k -> infinity): with O1 in its one form it gives torus decay, the gap in both orders of limits and reflection positivity; the running clause, the scheme clause and non-triviality are not used | Lean | `ProofPhase/Closures/OneBoxForm.lean`, `tendsto_a_of_resolution`, `gap_of_o1Form`, `yang_mills_assembly_onebox_of_resolution` | none |
| IV.9.5a | Per box, by construction: at every level and volume the reflected correlation at even lattice time is the reflection-positivity square of the centred translate, Z wcorr(2m) = rpForm(F_m - c, F_m - c), hence >= 0; a scale-uniform lower bound c > 0 at a fixed physical time gives `NonTrivial` ("non-trivial" in the project's sense, a non-vanishing correlation, weaker than "not a Gaussian field"); the running clause holds by construction on the one-loop line beta_k = (11/(6 pi^2)) log l_k. Strict per-box positivity (non-degeneracy of the reflection form on the centred translates) is not claimed | Lean (by construction for the per-box parts) | `ProofPhase/Closures/NonTrivialSplit.lean`, `wcorr_even_eq_rpForm`, `wcorr_even_nonneg`, `UniformLower`, `nonTrivial_of_uniformLower`, `oneLoopTuning`, `running_oneLoop` | none |
| IV.9.5b | The scale-uniform halves of O2: a lower bound c > 0 on one slab correlation at a fixed physical time, uniform in the cutoff (spectral form: weight >= delta below a mass M, uniformly), and the scheme clause of the line of constant physics. In the spectral model this is the lower edge of the window whose upper edge is O1's gap: not implied by O1 (a gap at every rate with vanishing correlation), not implying it, compatible with it (a state at m <= E < M). By the owner's reading it is the lower edge of the one assumption, not a second assumption (III.64a), placed at the ODP's end, the start {infinity, 2, 3}, from which it follows with nothing more to show | conditional (on III.64, as III.66; the placement is a reading; relation to O1: Lean, model) | `ProofPhase/Closures/NonTrivialSplit.lean`, `lower_of_spectral_weight`, `gap_not_lower`, `gap_and_lower_compatible`; `ProofPhase/Bridge/Spectral.lean`, `corr_ge`; `ProofPhase/Assembly.lean` (`NonTrivial`, `OnLCP`) | a proof of III.64 (decided 2026-11-24: folded into III.64, III.64a; conditional on it as III.66) |
| IV.9.6 | O3: Euclidean invariance, fields, uniqueness, Wightman | external (theirs) / open (ours) | `PROOF-BLUEPRINT.md` P6.4-P6.9, P7.6 | observable bridge or adoption |
| IV.9.7 | O4: every compact simple group | external (existence) / open (our tuning) | `PROOF-BLUEPRINT.md` P6.10 | general tuning |
| IV.9.8 | M1's floor at L_* gives a physical gap along a chain, not on a grid | paper | `RDOEBLIN.md` 0 | none |
| IV.10 | DMP readings of Part IV (containment, outrunning possibility, IM both sides, pressing as instanton, crossover without content, WHKs) | reading | `PREP.md` (2026-11-22, 2026-11-23) | none |
| IV.10b | g^2 dimensionless only in d = 4 | classical | dimensional analysis | none |
| IV.10c | O1 (chain form, `YMOneBox`) holds exactly when some margin makes every chain of outsides DMP-complete in the one-box test (gate factor min(1, e^-F_e), floor log mu, claim inside) | Lean | `ProofPhase/ETM/RotationInstances.lean`, `o1Box`, `o1_iff_complete` | none |
| IV.10d | `FineOneBox` holds exactly when, for some valid box geometry fixed across levels and some margin below 1, the Yang-Mills box is DMP-complete from its start level; it then gives the one-box assembly; the converse needs the geometry fixed across levels | Lean | `ProofPhase/ETM/RotationInstances.lean`, `ymBox`, `fineOneBox_iff`, `ym_complete_iff`, `fineOneBox_iff_complete`, `fineOneBox_correct`, `ym_assembly_of_complete` | none |
| IV.10e | The Yang-Mills box is DMP-complete (equivalently `FineOneBox`, i.e. O1) | open (conditional on III.64) | IV.10d; IV.5.6 | a proof of O1 |

## Part V. GRH (`draft/05-part-V-grh.md`)

Notes relative to `docs/rh-guide/`.

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| V.0a | RH and Dirichlet GRH proved in Lean by others | external | `SOURCES.md` S1-S4; `GUIDE.md` 1 | rebuild and axiom check |
| V.0b | Their endgame is Landau's theorem on a one-sided square-root bound (Stepanov-type balance), not positivity | external (traced) | `GUIDE.md` 2, 4, 5 | none |
| V.0c | GRH for Dedekind, Hecke, automorphic L-functions open | open | `GUIDE.md` 1, 5 | a proof |
| V.1.2 | Line implies non-negative pairing | Lean | `ProofPhase/GRH/Weil.lean`, `weilSum_re_nonneg_of_real` | none |
| V.1.3 | Positivity implies line, given the approximation property | Lean (named hypotheses: approximation property, finite multiplicities) | `ProofPhase/GRH/Weil.lean`, `real_of_weilSum_nonneg` | prove the property for a real class |
| V.1.5 | Weil's explicit formula for zeta, for every smooth compactly supported test function, by the contour shift (zero sum absolutely convergent), with a polynomial zero count per unit window; Mathlib-only core, no named step | Lean | `ProofPhase/GRH/ContourShift.lean`, `CS.contourShift`; `ProofPhase/GRH/ContourShiftTie.lean`, `explicit_formula_smooth`, `explicit_formula_of_smooth`; `ProofPhase/GRH/ContourShiftZeta.lean`, `zero_count_ball`, `zero_count_window`; `docs/unified/contourshift-axioms.log`; `docs/unified/CONTOUR-SHIFT.md` | Dirichlet and other L-functions (V.1.5b) |
| V.1.5b | The explicit formula for Dirichlet and other L-functions, for test functions of class C^2, and Weil's criterion are classical; they are not formalised in Lean here | classical (not in Lean) | Weil 1952 ("Sur les formules explicites de la theorie des nombres premiers"); Bombieri 2000 (recalled); `docs/unified/CONTOUR-SHIFT.md` 5 | formalise them |
| V.1.6 | Similitude eigenvalues have modulus sqrt q | Lean | `ProofPhase/GRH/Orbits.lean`, `similitude_eigenvalue` | none |
| V.1.7 | Skew shift gives Re = 1/2 | Lean (finite dimension) | `ProofPhase/GRH/Orbits.lean`, `skew_shift_re_half` | none |
| V.1.8 | Lee-Yang and Asano, small cases | Lean | `ProofPhase/GRH/LeeYang.lean`, `asano`, `ising3_zeros_on_circle` | none |
| V.1.9 | Fixed points of f^n counted by periods | Lean | `ProofPhase/GRH/Orbits.lean`, `card_fixed_pow_eq_sum` | none |
| V.1.10 | A lossy exponential bound becomes exact on a finite spectrum | Lean | `ProofPhase/GRH/Induction.lean`, `norm_le_of_exp_bound` | none |
| V.1.11 | From the named hypothesis `ExtRH` and the kernel bookkeeping, `ScaleSign` and the non-negativity of Weil's pairing hold for smooth compactly supported kernels (the zeta column of the ledger) | Lean (from `ExtRH`) | `ProofPhase/GRH/ContourShiftTie.lean`, `zeta_tie_in_smooth`; `docs/unified/GRH-TIE-IN.md` | none |
| V.2.1 | Duality without positivity allows mirror pairs off the line | Lean | `ProofPhase/GRH/Orbits.lean`, `krein_off_line` | none |
| V.2.2a | The ratio of the local factor at s and at 1 - s has modulus 1 on the line (unramified primes) | Lean | `ProofPhase/GRH/Tate.lean`, `local_factor_unimodular` | none |
| V.2.2b | Functional equation for every even/odd function on Z/N (Mathlib); Davenport-Heilbronn has zeros off the line | classical (in Mathlib: `completedLFunction_one_sub_even`, `completedLFunction_one_sub_odd`, `Mathlib/NumberTheory/LSeries/ZMod.lean`, Mathlib v4.34.0) | `grh/TATE.md` 0.2 | none |
| V.2.2c | Tate: completed L-function as product of local zeta integrals; global FE is adelic Poisson | classical | Tate's thesis; `grh/TATE.md` 0.1 | none |
| V.2.3a | Lambda(n) >= 0 plus a one-sided square-root bound plus Landau excludes zeros right of 1/2 | paper | `grh/INDUCTION.md` 0.2; `grh/TATE.md` 0.3 | Lean (with V.2.4a) |
| V.2.3b | The one-sided bound is global (generalised primes violate it) | classical | Diamond-Montgomery-Vorhauer; `grh/TATE.md` 0.3 | none |
| V.2.4a | Positive transforms exclude negative-residue poles; ray form | Lean | `ProofPhase/Bridge/Poles.lean`, `landau_ray_poles`, `lseries_residue_nonneg` | none |
| V.2.4b | A real zero in (theta, 1) gives a negative-residue pole | classical (not formalised) | `bridge/BRIDGE.md` 1.4 | Lean |
| V.2.5a | Function fields: one positive duality gives both 1/2s | classical | Weil 1948; `bridge/BRIDGE.md` 2.3 | none |
| V.2.5b | Stepanov and the Lean proof by others: the 1/2s meet only in the conclusion | classical / external (traced) | `bridge/BRIDGE.md` 2.3, 3 | none |
| V.2.5c | Arithmetic positivity giving both 1/2s (an arithmetic Hodge index on Spec Z x Spec Z, IX.5.3; also II.11.5, IX.1.4b) | open | `bridge/BRIDGE.md` 4 | an arithmetic Hodge index |
| V.2.6 | The mirror pair Weil uses is (1, 0); its constants are archimedean and give no sign | numerical (with V.2.1) | `MIRROR.md` 0.3 | none |
| V.2.7 | Inversion and halving as one phenomenon | reading / analogy | `bridge/BRIDGE.md` 5 | V.2.5c |
| V.3.1 | Toeplitz frame; each step one scalar condition at the corner | classical + paper | `grh/INDUCTION.md` 0.1 | none |
| V.3.2a | Each step holds up to a = 1.25, reflection coefficients at most 0.68 | numerical | `grh/INDUCTION.md` 0.1, 0.5 | more cells, higher primes |
| V.3.2b | Each step is an exact cancellation (prime term up to about 700 radii) | numerical | `grh/INDUCTION.md` 0.1 | none |
| V.3.2c | Weight scaling breaks positivity at 1e-3 to 1e-9 | numerical | `grh/INDUCTION.md` 0.3 | none |
| V.3.3a | Ground-state zeros on the circle, locking onto zeta's zeros | numerical | `grh/VARIATIONAL.md` 0.1 | none |
| V.3.3b | Minimiser's zeros on the circle for every real symmetric Toeplitz section; positivity = remnant >= 0 | classical (Caratheodory-Fejer, Pisarenko) + Lean (grid form) | `ProofPhase/GRH/Induction.lean`, `atoms_on_circle`, `atomic_toep_nonneg` | none |
| V.3.4a | Positive configurations convex; positivity = stability only as a tautology | Lean | `ProofPhase/GRH/Variational.lean`, `toep_pos_convex`, `line_min_iff`, `min_at_zero_iff` | none |
| V.3.4b | The true primes sit about 1e-9 from the edge | numerical | `grh/VARIATIONAL.md` 0.4 | none |
| V.3.5 | Only the full set of primes present is positive | numerical | `grh/TRANSFER.md` 0.1 | none |
| V.3.6a | Per-step contraction on sections; product to zero (Kolmogorov-Szego) | numerical + classical | `grh/TRANSFER.md` 0.2 | none |
| V.3.6b | A positive margin survives finitely many positive factors; a uniform lower bound q < 1 on the factors keeps the margin positive at every finite scale, at least c_0 q^n (III.45) | Lean | `ProofPhase/GRH/Transfer.lean`, `margin_pos_of_factors`, `prod_one_sub_le_exp`; `ProofPhase/Unified/Ledger.lean`, `survive`, `survive_pos` | none |
| V.3.7a | Weyl's two-term bound is the best separate bound | Lean | `ProofPhase/GRH/Transfer.lean`, `two_term_bound` | none |
| V.3.7b | It fails by 7.9 t_0 at support 1.225; Krein's extension is the right two-term form | numerical + classical | `grh/TRANSFER.md` 0.3 | none |
| V.3.7c | The place-by-place condition fails by 9.7 t_0 at support 1.225 while the whole form is positive | numerical | Part V 3.9 (source note not identified) | check against V.3.7b (7.9 t_0, same support) |
| V.3.8 | Disjoint prime lattices; prime blocks indefinite; place-by-place forces the real place to pay for all | Lean | `ProofPhase/GRH/Tate.lean`, `prime_lattices_disjoint`, `zero_diag_indefinite`, `form_two_point`, `local_assembly_forces_arch` | none |
| V.3.9 | Real place alone indefinite from support 0.40 to 0.43; semilocal positivity needs the real place and all primes up to e^{2a} | numerical | `grh/TATE.md` 0.4; `grh/SEMILOCAL.md` | none |
| V.3.10 | Weight positivity is not enough; Lambda = 0 at the edge | classical + paper | `grh/LEE-YANG.md` 5; Polya 1926; Rodgers-Tao 2020 | none |
| V.3.11 | Explicit formula agrees to 1e-16; smallest eigenvalue 2.4e-1 to 2.6e-9, no violation | numerical | `grh/weil_numerics.log`; `grh/ATTEMPT.md` 4 | none |
| V.4.1 | Face 1: zero-free arithmetic Weil Hilbert space | open | `grh/ATTEMPT.md` step 4 | construction |
| V.4.2 | Face 2: critical ferromagnet with block-spin law Phi | open | `grh/LEE-YANG.md` 5c | construction |
| V.4.3 | Face 3: Deninger space with positive Hodge form (and a gap) | open | `grh/ORBITS.md` 6; `grh/TRANSFER.md` 5 | construction |
| V.4.4 | Face 4: Hermite-Biehler chain for xi | open (framework classical; de Branges conjecture false) | `grh/INDUCTION.md` 0.4 | construction |
| V.4.5 | Face 5: step lemma | open | `grh/INDUCTION.md` 7 | a rule from arithmetic |
| V.4.6 | Face 6: sign of the remnant | open | `grh/VARIATIONAL.md` 0.5 | a proof |
| V.4.7 | Face 7: global sign; the norm in which the scaling flow runs | open | `grh/TATE.md` 0.5, 0.6 | a proof |
| V.4.8 | Face 8: all-or-nothing step | open | `grh/TRANSFER.md` 5 | a proof |
| V.4.9 | Faces 2, 3 imply face 1; faces 5, 6, 8 are one quantity read three ways; not shown equivalent | paper | `grh/INDUCTION.md` 7; `grh/ORBITS.md` 4; `grh/VARIATIONAL.md` 5; `grh/TRANSFER.md` 5 | equivalence proofs |
| V.5.1 | Scaling flow preserves Weil's form on its completion | paper | `grh/TATE.md` 0.5 | Lean |
| V.5.2 | Contraction + mirror pairing: every mode a phase | Lean | `ProofPhase/GRH/Tate.lean`, `runs_and_mirror_on_line` | none |
| V.5.3 | Explicit formula as a trace formula of zeros and orbit lengths log p | classical | `grh/TRANSFER.md` 0.2 | none |
| V.5.4 | Positive-by-construction spaces miss off-line zeros (Connes) or give a half-plane (Lax-Phillips) | classical (recalled) | `grh/TATE.md` 0.5 | none |
| V.6a | RH iff M(x) = O(x^{1/2 + eps}) | classical | `PREP.md` (ODP tool entry) | none |
| V.6 | DMP readings of Part V (circle, virtual flux, excision at G0, GRH as the ODP's tool, remnants, coupling factor) | reading | `PREP.md` (2026-11-23) | none |

## Part VI. P vs NP (`draft/06-part-VI-pnp.md`)

Notes relative to `docs/pnp/`.

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VI.1.1 | Dobrushin sums < 1: heat-bath within n alpha^t after t sweeps; random scan | Lean | `ProofPhase/Mixing/Classical.lean`, `tv_sweep_dobrushin`, `tv_rs_dobrushin`, `mixing_sweep_dobrushin` | none |
| VI.1.5 | Dobrushin uniqueness; spatial mixing gives a uniform gap | classical | Dobrushin 1968, 1970; Stroock-Zegarlinski 1992; Martinelli-Olivieri 1994 | none |
| VI.1.6 | Sampling iff counting (self-reducible) | classical | Jerrum-Valiant-Vazirani 1986 | none |
| VI.1.7 | Hard-core below lambda_c: counting and fast mixing | classical | Weitz 2006; Anari-Liu-Oveis Gharan 2020; Chen-Liu-Vigoda 2021 | none |
| VI.1.8 | Certified class: existence, search, sampling, counting polynomial | classical (assembled; mixing step Lean) | `DICTIONARY.md` 6.2; Lovasz 1975; Moser-Tardos 2010; Moitra 2019 (mixing step: `tv_sweep_dobrushin`, `mixing_sweep_dobrushin`, VI.1.1) | Lean for the assembly |
| VI.1.9 | On paper the Dobrushin and spectral-gap results hold for infinite or continuous single-site spaces, with hard constraints, and for systematic scan; in Lean they are not yet unconditional (the gauge-theory instance rests on the couplings and the L^2 spectral theorem as hypotheses) | classical (Lean conditional) | Dobrushin 1968; Georgii, *Gibbs Measures and Phase Transitions*, ch. 8 (general single-site spaces); Salas-Sokal 1997 (hard constraints); Dyer-Goldberg-Jerrum 2008, Hayes 2006 (systematic scan) (recalled); `ITEMS.md` 3 | Lean |
| VI.2.1 | Antiferromagnets beyond uniqueness: no FPRAS | conditional (NP != RP) | Sly 2010; Sly-Sun 2014; Galanis-Stefankovic-Vigoda | none |
| VI.2.2 | k-CNF counting NP-hard above c 2^{k/2} | conditional (NP != RP) | Bezakova et al. 2019 | none |
| VI.2.3 | Ferromagnetic Ising has an FPRAS at every temperature | classical | Jerrum-Sinclair 1993 | none |
| VI.2.4 | Wilson action is on the ferromagnetic side | reading | `DICTIONARY.md` 5 | none |
| VI.2.5 | All counting inside uniqueness is as strong as NP = RP; SAT into LLL impossible as stated | conditional / classical | `DICTIONARY.md` 6.3 | none |
| VI.3.1 | Resolution sound (`unsat`) and refutation-complete (tree-like, `refutable_iff`) | Lean | `ProofPhase/Proof/Resolution.lean`; `ProofPhase/Proof/Complete.lean`, `refutable_iff`, `unsat` | none |
| VI.3.2 | No inference creates assertion; middle clause; width >= boundary | Lean | `ProofPhase/Proof/Cut.lean`, `exists_middle`, `width_ge` | none |
| VI.3.3 | Tree-like size-width | Lean | `ProofPhase/Proof/SizeWidth.lean`, `tl_size_gt` | none |
| VI.3.4 | DAG-like size-width; with the cut principle | Lean (optimisation over b paper) | `ProofPhase/Proof/Dag.lean`, `size_width`, `size_width_exp`, `dag_size_ge` | none |
| VI.3.5 | Tseitin width bound on expanders | Lean (two hypotheses) | `ProofPhase/Proof/Tseitin.lean`, `width_ge`, `tl_size_ge` | formalise the expander hypotheses |
| VI.3.8 | One XOR names the flux; naming costs differ by system | Lean (`summary`) + classical | `DICHOTOMY-TRANSFER.md` 3; `ProofPhase/Proof/Crossing.lean`, `summary` | none |
| VI.3.9 | Known lower bounds (resolution, bounded-depth Frege, cutting planes) | classical | `PROOF-SYSTEMS.md` 2 | none |
| VI.3.10 | Feasible interpolation and its cryptographic failure | classical / conditional | Krajicek 1997; Pudlak 1997; Krajicek-Pudlak 1998; Bonet-Pitassi-Raz 2000 | none |
| VI.3.11 | No superpolynomial lower bound is known for AC^0[p]-Frege, Frege or extended Frege; best formula lower bounds about n^3 (a statement about the literature; the bounds themselves are open problems outside the card, whose open step is VI.4.10) | classical | Hastad 1998; Tal 2014; Krajicek, *Proof Complexity* (2019) (recalled) | none |
| VI.4.1 | CP on random 3-CNF is the sharpest open case | classical + reading | `EDGE.md` 0.1 | none |
| VI.4.2 | Incompressibility of the one formula gives expansion; natural proofs do not bite | classical + reading | `EDGE.md` 0.3 | none |
| VI.4.4 | Majority line: sensitive to all, survives restrictions of fewer than e/2 | Lean | `ProofPhase/Proof/Edge.lean`, `majority_line`, `thr_sensitive`, `thr_survives` | none |
| VI.4.5 | Unit thresholds: duality floor (e + 1)/2 | Lean | `ProofPhase/Proof/CPDuality.lean`, `thr_duality` | none |
| VI.4.6 | Weighted lines are cheap in both channels | Lean | `ProofPhase/Proof/CPDuality.lean`, `two_cheap` | none |
| VI.4.7a | Interpolation split: disjoint boundary laws iff unsatisfiable | Lean (logical core) | `ProofPhase/Proof/CPDuality.lean`, `split_unsat_iff` | none |
| VI.4.7b | Interface bounds pass clique-colouring and log-width random CNF, fail at constant width | classical | Pudlak 1997; Hrubes-Pudlak; Fleming-Pankratov-Pitassi-Robere; Sokolov | none |
| VI.4.8 | Creative pairs in every CP refutation of a 3-CNF that has a fractional point satisfying every axiom (the all-1/2 point), each axiom having a coefficient +-1; single roundings create nothing; additive pairs cheap | Lean | `ProofPhase/Proof/CPPairs.lean`, `creative_pair`, `round_single`, `fan_cheap` | none |
| VI.4.9a | All-1/2 point survives sums, not rounding | Lean | `ProofPhase/Proof/CPDuality.lean`, `half_clause`, `half_breaks_rounding` | none |
| VI.4.9b | Rank, not size; SOS degree does not transfer to CP size | classical | Buresh-Oppenheim et al.; Grigoriev 2001; Dadush-Tiwari 2020 | none |
| VI.4.10 | **Interface hardness at width 3** (a size-forcing W_CP) | open | `EDGE.md` 0.4; `CP-DUALITY.md` 0.5 | a lower bound |
| VI.4.11 | `ExtractAPI G c` (every cutting-planes refutation of F o G of size below exp(c (w + 1)) admits a narrow-clause labelling) is equivalent to `LiftCPConst G c`; neither is proved for any constant gadget | Lean | `ProofPhase/Proof/SoundAPI.lean`, `liftCPConst_iff_extract`; `docs/unified/soundapi-axioms.log` | a constant-gadget lifting theorem (III.7k) |
| VI.5.2 | Applied: 16 to 12 theorems, 5 to 4 layers, same statements | Lean + numerical | `ProofPhase/Native/RouteBChain.lean`; `NATIVE-METHOD.md` 0.3; `abs_ccorr_le'`, `abs_nCorr_le'` | none |
| VI.5.3 | The method's floor bounds no minimum | reading | `NATIVE-METHOD.md` 5 | N1 |
| VI.5.4 | Automating resolution is NP-hard | classical | Atserias-Mueller 2019 | none |
| VI.6.N1 | Size of the remnant: is the irreducible core polynomial? | open | `docs/OPEN-QUESTIONS-DMP.md` 4 | a proof |
| VI.6.N3 | Steps T and H for Frege | open | `DICHOTOMY-TRANSFER.md` 4-6 | a lower bound |
| VI.6.N4 | From the certified class to all inputs | open | `DICTIONARY.md` 6.3, 8 | a barrier-passing argument |
| VI.7 | Barriers: relativization, natural proofs, algebrization; Williams evades them | classical | Baker-Gill-Solovay 1975; Razborov-Rudich 1997; Aaronson-Wigderson 2009; Williams 2014 | none |
| VI.8 | DMP readings of Part VI (two categories of lines, pairs as entanglement, confinement plus uncertainty, inside/across a DB) | reading | `PREP.md` (2026-11-23); `DICTIONARY.md` 7 | none |

## Part VII. Navier-Stokes, with Poincare as validation (`draft/07-part-VII-navier-stokes.md`)

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VII.0a | Clay's statement (Fefferman): (A) smooth global solutions on R^3 with zero force, (B) the same on the torus, (C) breakdown on R^3 with a force, (D) the same on the torus | classical | Fefferman's official statement; NS 1.1 | none |
| VII.0b | (C) and (D) allow a force; an unforced blowup disproves (A) or (B) and so proves (C) or (D) with f = 0 | classical | NS 1.1 | none |
| VII.0e | This part proves no statement about the real Navier-Stokes equations | (statement of scope) | NS, header and 2.6 | none |
| VII.0f | (A) and (B) are open in this paper; an external claim (VII.0d) asserts they are false | open | NS 0, 7 | a proof, or the audit of VII.5.4 |
| VII.1.1a | Leray: a singularity at T* forces sup abs(u) >= c (nu/(T* - t))^{1/2} and norm(grad u)_{L^2} >= c (T* - t)^{-1/4} | classical | Leray 1934 (recalled); NS 1.2 | none |
| VII.1.1b | No nonzero backward self-similar solution at the Leray scaling in `L^3` (Necas-Ruzicka-Sverak), `L^p` and under local energy bounds (Tsai) | classical | Acta Math. 176 (1996); Arch. Ration. Mech. Anal. 143 (1998) (recalled); NS 1.2 | none |
| VII.1.1c | The singular set of a suitable weak solution has zero one-dimensional parabolic measure | classical | Caffarelli-Kohn-Nirenberg 1982 (recalled); NS 1.2 | none |
| VII.1.1d | A solution bounded in `L^infinity_t L^3_x` is smooth; at a singular time the `L^3` norm tends to infinity | classical | Escauriaza-Seregin-Sverak 2003; Seregin 2012 (recalled); NS 1.2 | none |
| VII.1.1e | No axisymmetric Type I blowup | classical | Chen-Strain-Tsai-Yau; Koch-Nadirashvili-Seregin-Sverak (recalled); NS 1.2 | none |
| VII.1.1f | Smooth backward discretely self-similar solutions obey the Type I bound; nonzero ones need a period bounded below | classical | Chae-Wolf; Pineau-Vicol (as cited by Alpoge-Buckmaster); NS 1.2 | none |
| VII.1.1g | The no-go results leave open discretely self-similar, asymptotically self-similar and Type II blowup | classical | NS 1.2 | none |
| VII.1.2 | Tao's averaged equations keep the energy identity and the standard estimates and blow up in finite time | classical | Tao, J. Amer. Math. Soc. 29 (2016) 601-674; NS 1.3 | none |
| VII.1.3 | Hou's axisymmetric numerical scenario: vorticity growth about 10^7 at nearly self-similar Leray-type rates; numerical evidence by others, not a proof | external | Hou, arXiv 2107.06509; NS 1.4 | a proof, or a refutation |
| VII.2.1 | The statements of the external tie (certificate exists; profile exists; Fefferman's (A); (B)) are named, not defined: the library has no Navier-Stokes object; the Lean modules contain no Navier-Stokes object (the checkable half of VII.0e) | paper (observation) | `ProofPhase/Unified/NavierStokesAPI.lean`, `ABInterface`; NS 6.3 | audit item 1 (real definitions) |
| VII.3.1a | The viscous term in the zoomed frame has weight (T* - t)^{1 - 2 alpha}; the local energy scales like (T* - t)^{5 alpha - 2} | classical | scaling computation; BL 4.2; NS 2.2 | none |
| VII.3.1b | The viscous floor: constant at alpha = 1/2, at most nu below it, summable below it, unbounded above it, bounded exactly when alpha <= 1/2 | Lean | `ProofPhase/Unified/NavierStokes.lean`, `nsViscous_half`, `nsViscous_le`, `nsViscous_summable`, `nsViscous_tendsto_atTop`, `nsViscous_bounded_iff` | none |
| VII.3.1c | Local energy bounded exactly for alpha >= 2/5; the Type I bound exactly for alpha >= 1/2 | Lean (model: the exponents of VII.3.1a) | `ProofPhase/Unified/NavierStokes.lean`, `ns_energy_window`, `ns_typeI_iff` | none |
| VII.3.1d | The window: bounded viscous floor and bounded local energy together exactly for 2/5 <= alpha <= 1/2 | Lean (model: the exponents of VII.3.1a) | `ProofPhase/Unified/NavierStokes.lean`, `ns_window` | none |
| VII.3.1e | Above the window no one-scale certificate covers all steps | Lean | `ProofPhase/Unified/NavierStokes.lean`, `ns_no_uniform_certificate` | none |
| VII.3.1f | The window decision runs on rational exponents and is proved right for the real statement | Lean | `ProofPhase/Unified/NavierStokesAPI.lean`, `windowQ`, `windowQ_admissible_iff`, `windowQ_leray_iff`, `windowQ_half`, `windowQ_correct` | none |
| VII.3.2a | A route I certificate has a non-steady profile (no exact self-similarity is used) | Lean (non-steadiness is the structure field `nonsteady`) | `ProofPhase/Unified/NavierStokes.lean`, `LerayDSSCertificate`, `LerayDSSCertificate.not_steady` | none |
| VII.3.2b | The free flow pays S/4 per period at floor 0; a period factor 0 < rho < 1 is a cost -log rho above floor 0 for one step type | Lean (model: the decay of the rescaled norm is supplied; its classical source is VII.3.2c) | `ProofPhase/Unified/NavierStokes.lean`, `ns_free_flow_pays`, `ns_dss_costAboveFloor` | none |
| VII.3.2c | The free flow contracts the rescaled `H^1` norm by e^{-s/4}, because `H^1` is subcritical by 1/4 | classical | NS 2.3; Alpoge-Buckmaster 1.1 (as read in the notes) | none |
| VII.3.2d | From the period-map inequality (hypothesis), the perturbation decays geometrically, the periods sum to the finite time 1, the `H^1` amplitude tends to infinity, the profile is not steady | Lean (from the period-map inequality; the non-steady conjunct is the field `nonsteady`) | `ProofPhase/Unified/NavierStokes.lean`, `ns_dss_converge`, `ns_period_hasSum`, `nsPeriodLength`, `ns_dss_amplitude`, `ns_blowup_of_dss` | none (the PDE inputs are VII.5.1) |
| VII.3.2e | Route I card: from the period contraction (open step) the perturbation settles onto the profile, with an explicit period count, and the three consequences of VII.3.2d hold | Lean | `ProofPhase/Unified/NavierStokesAPI.lean`, `routeI`, `system`, `contracting`, `settles_by` | none (the open step is VII.5.1) |
| VII.3.3a | Route II: from the Chen-Hou certificate with trapping condition (1 - q)^2 >= 4 C (epsilon + nu) and 2/5 <= alpha < 1/2: trapped perturbation, finite T*, unbounded amplitude; the same as a cost above a floor | Lean | `ProofPhase/Unified/NavierStokes.lean`, `EulerProfileCertificate`, `ns_blowup_of_euler_profile`, `ns_euler_gap_of_costAboveFloor` | none |
| VII.3.3b | Viscosity as a transported uncertainty: bounded below the Leray scaling even at cost = floor; constant and unbounded at the Leray scaling | Lean | `ProofPhase/Unified/NavierStokes.lean`, `ns_viscous_transport_bounded`, `ns_viscous_transport_unbounded_at_leray` | none |
| VII.3.3c | The API bounds the route II perturbation: M(n) <= M(0) + 2 (epsilon + nu)/(1 - q) | Lean | `ProofPhase/Unified/NavierStokesAPI.lean`, `eulerUncertainty`, `routeII_bounded` | none |
| VII.3.3d | No route II profile is known | open | NS 2.4 | a profile and its certificate |
| VII.3.4a | A summable budget never pays a uniform positive cost; shares whose partial sums stay below the start energy are such a budget | Lean | `ProofPhase/Unified/NavierStokes.lean`, `ns_energy_budget_not_costAboveFloor`, `ns_energy_identity_not_costAboveFloor`; `ProofPhase/Unified/NavierStokesAPI.lean`, `energy_cannot_fill` | none |
| VII.3.4b | Per dyadic scale the energy-only transfer bound K 2^{5k/2} overtakes the viscous cost nu 4^k at some scale, for every nu and K > 0 | Lean (model: the transfer bound and the viscous cost are given as exponents) | `ProofPhase/Unified/NavierStokesAPI.lean`, `dyadic_supercritical` | none |
| VII.3.4c | The scalings behind VII.3.4b (Bernstein), and that the same count is critical in two dimensions, which is why 2D is regular | classical | NS 5.2(b) | none |
| VII.3.4d | Regularity card: from a uniform cost per dyadic scale above the transfer floor (open step), the carried quantity decays at a positive rate and is summable | Lean | `ProofPhase/Unified/NavierStokesAPI.lean`, `DyadicInput`, `regularity` | none (the open step is VII.5.2) |
| VII.3.5a | Chen-Hou: stable nearly self-similar finite-time blowup for 2D Boussinesq and 3D axisymmetric Euler with smooth data and a wall, computer-assisted; not Navier-Stokes | external | Chen-Hou, arXiv 2210.07191, 2305.05660; BL 1 | none needed for this paper |
| VII.3.5b | One-step trapping: (1 - q)^2 >= 4 C r and a start in the ball keep the perturbation in the ball forever; the threshold is sharp | Lean | `ProofPhase/Unified/Blowup.lean`, `trap`, `trap_radius`, `trap_of_gap`, `escape_of_below`, `escape_pos` | none |
| VII.3.5c | The one-step certificate follows from `CostAboveFloor` of 1 - q over 2 sqrt(C r) for one step type (`CostAboveFloor` implies the trapping gap; the converse and the boundary case are not proved) | Lean | `ProofPhase/Unified/Blowup.lean`, `gap_of_costAboveFloor` | none |
| VII.3.5d | Under a focusing margin the durations are summable, T* is finite, the amplitude is unbounded; assembled certificate | Lean | `ProofPhase/Unified/Blowup.lean`, `durations`, `durations_pay`, `arrival`, `amplitude_unbounded`, `blowup_of_certificate` | none (the step inequality is a hypothesis) |
| VII.3.5e | Each rescaled step adds one fixed quantum to the Beale-Kato-Majda count (the Lean content is the identity: the sum of (durations)^-1 times durations is n; the count itself is not defined in Lean) | reading (Lean: the identity `boundary_quantum`) | `ProofPhase/Unified/Blowup.lean`, `boundary_quantum` | none |
| VII.3.5f | The BKM integral is infinite exactly when smooth continuation fails | classical | Beale-Kato-Majda; BL 3.2 | none |
| VII.4.1a | Alpoge-Buckmaster Theorem 1.1: one backward discretely self-similar viscous profile gives unforced blowup from smooth data at the rate (T - t)^{-1/4} in `H^1`, stable in finite codimension; unverified here | external | NS 1.5(a), 6.2 | refereeing, independent audit |
| VII.4.1b | Alpoge-Buckmaster Theorem 7.1 and Corollary 7.2: a certificate (explicit inequalities, Appendix B) gives an exact profile nearby; unverified here | external | NS 1.5(a), 6.2 | release and independent check of the certificate |
| VII.4.1c | The candidate profile: not axisymmetric, 19-fold symmetry about one axis and a half-turn about another, period about 0.36 | external | NS 1.5(a), 6.2 | the released certificate |
| VII.4.1d | The certificate is not released; only its SHA-256 hash, 3f7a335b84b6c7631742cacc5343dfcd11cf72f5221ff79b2b9268790b4b22c5, is public; the 128-bit interval check is outside their formalisation | external | NS 1.5(a), 6.1; the paper | release, hash check, independent interval check |
| VII.4.1e | Their Lean library (about 2,270 files, Lean 4.33) was patched on 2026-11-20 and not rebuilt; its formal Theorem 1.1 has no rate; the prose no longer follows the Lean proof | external | NS 1.5(a), 6.2 (their README and section 1.6) | rebuild and axiom audit (audit items 2, 3) |
| VII.4.1f | Tao (blog, 2026-11-20): technically human-readable, a clear strategy, a professional write-up still needed; no referee report | external | NS 1.5(a), 6.1 | a referee report |
| VII.4.1g | Their profile avoids the no-go results (depends on zoomed time; weak `L^3` but not `L^3`; not axisymmetric; period above the lower bound, constant not checked here) | external | NS 2.3, 6.2 | the released certificate and the constants |
| VII.4.1h | The external tie in the API: three `External` fields, one open-step card (the certificate), the paper's route gives the same conclusion; plumbing only | Lean | `ProofPhase/Unified/NavierStokesAPI.lean`, `ABInterface`, `abProblem`, `ab_paper_route` | none (content is VII.4.1a to VII.4.1e) |
| VII.4.2a | OpenAI: a smooth compactly supported force, zero initial velocity, bounded energy, sup norm unbounded as t -> 1, for every nu > 0; addresses (C) and (D) | external | NS 1.5(b) | refereeing |
| VII.4.2b | An independent build record of its Lean proof reports only the three standard axioms, no `sorry`, and a match to a public formalisation of (C) and (D); not rebuilt here | external | NS 1.5(b) | independent rebuild |
| VII.4.2c | Lemma-level departures of its Lean proof from the written proof are shown, with no claim about the written proof's correctness | external | arXiv 2610.08144; NS 1.5(b) | resolution by the authors |
| VII.4.3 | Smaller programmes: a computer-search target for unforced blowup (Petrillo-Glimm); cascade blowup in dyadic shell models (Cheskidov-Dai-Palasek); neither is Navier-Stokes blowup | external | arXiv 2609.23868, 2609.26790; NS 1.5(c) | none |
| VII.4.4a | Goedel completeness: if ZFC plus "some smooth datum blows up" is consistent, a model exists | classical | Goedel; NS 4 | none |
| VII.4.4b | A completeness model may be nonstandard and settles nothing about the real equations; only a proof settles the Clay question | classical | NS 4 (recalled absoluteness facts) | none |
| VII.4.4c | Whether regularity is independent of ZFC | open | NS 4 | a proof either way |
| VII.5.1 | **Route I open step:** one period of the zoomed flow from a non-steady periodic profile contracts the perturbation on the complement of finitely many directions, in a real norm, with rho + C delta < 1; in the tie, the Alpoge-Buckmaster certificate satisfies their Appendix B | open | `ProofPhase/Unified/NavierStokesAPI.lean`, `PeriodContraction`, `abProblem`; NS 5.2(c), 6.3 | the released and independently verified certificate |
| VII.5.2 | **Regularity slot:** every dyadic scale dissipates a uniform cost above the transfer floor from the true nonlinearity; the energy identity cannot supply it; false if VII.0d holds | open | `ProofPhase/Unified/NavierStokesAPI.lean`, `regularity`; NS 5.2(b) | a proof from the true nonlinearity |
| VII.5.3 | What continues past T* for a blowup solution (uniqueness of weak continuation) | open | BL 3.2, 6.3 | a theorem |
| VII.5.4 | The audit list has twelve items, none done; five are named in the draft (real statements, rebuild, certificate check, Lean-only steps, mapping of Appendix B onto `LerayDSSCertificate`) | paper | NS 6.4 | the audit |
| VII.5.5 | An independent construction of the profile and certificate from scratch is beyond reach now | reading | NS 3 | none |
| VII.7a | A blowup is a certificate that infinitely many steps fit in finite time; T* is the DB, the profile crosses it; the hand-over run in reverse | reading | BL 3.3 | none |
| VII.7b | One theorem (`summable_of_gap`) gives the finite correlation length in Yang-Mills and the finite T* here | reading (Lean for both uses: `ProofPhase/Unified/Ledger.lean`, `summable_of_gap`) | BL 2.5 | none |
| VII.7c | Scale invariance reads as the arrow of causality: the outside set has one element | reading | BL 2.4 | none |
| VII.7d | "Not DMP-complete, hence blows up": a reading of supercriticality that names the side the 2026 claims assert; it proves nothing | reading | NS 4(6); `PREP.md`, 2026-11-24 entries | none |
| VII.7e | The owner's reading, with DMP-completeness defined as running on DMP (III.64b): Navier-Stokes does not build (the energy ledger pays no uniform cost per scale, VII.3.4a, VII.3.4b), so it is not DMP-complete, and blowup is the expected consequence; the negative result is the expected one and makes the framework falsifiable (global regularity would refute it); the step from "not DMP-complete" to blowup is the reading, since without a floor the settling machine is undecidable (II.3) | reading | NS 4(6); `PREP.md`, 2026-11-24, "Five answers", 4, and "The lower edge at the end of the ODP", 2 | a proof of blowup or of regularity (VII.5.1) decides it |
| VII.7f | "Settle" means the carried quantity dies out: regular on the regularity card, blowup on the route I card | reading | NS 5.2 | none |
| VII.7g | With the energy-only transfer bound against the viscous cost as gate factor and the claim "regular" at every dyadic scale, the gate reads R136a1 at some scale for every nu, K > 0 and every margin below 1: the Navier-Stokes box is not DMP-complete | Lean (model, as VII.3.4b) | `ProofPhase/ETM/RotationInstances.lean`, `nsBox`, `ns_gate_outside`, `ns_wrong_marker`, `ns_not_complete` | none |
| VII.7h | VII.7g covers the energy-only ledger only; an actual solution with a better transfer bound is not covered, so "not DMP-complete, hence blowup" stays the reading VII.7e | reading | `docs/unified/ROTATION-API.md` 3(5) | a proof of blowup or of regularity (VII.5.1) |

## Part VIII. Birch and Swinnerton-Dyer (`draft/08-part-VIII-bsd.md`)

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VIII.0a | Clay's statement (Wiles): for an elliptic curve over Q, the Taylor expansion of L(E, s) at s = 1 is c (s - 1)^r + higher terms with c not zero and r the rank of E(Q); so L(E, 1) = 0 exactly when E(Q) is infinite | classical | Wiles' official description; BSD 1.1 | none |
| VIII.0b | The Clay text also states the refined formula for c: real period, regulator, order of Sha, Tamagawa numbers, torsion order | classical | Wiles' official description; BSD 1.1 | none |
| VIII.0e | This part proves no case of the conjecture that was not already known; the notes record no claimed proof of the general statement | (statement of scope) | BSD header, 5 | none |
| VIII.1.1a | E(K) is finitely generated over a number field (Mordell 1922, Weil 1929); the proof is weak Mordell-Weil plus descent with a height | classical | Mordell; Weil; BSD 1.2 | none |
| VIII.1.1b | Hasse's bound abs(a_p) <= 2 sqrt p (Hasse 1933-36, Weil 1948): the Riemann hypothesis of the curve over F_p | classical | BSD 1.2 | none |
| VIII.1.1c | For CM curves L(E, s) is a Hecke L-function, entire with a functional equation (Deuring) | classical | Deuring 1953-56; BSD 1.2 | none |
| VIII.1.1d | Every E/Q is modular; so L(E, s) is entire and the completed function has a functional equation with sign w = +1 or -1 | external | Wiles; Taylor-Wiles; Breuil-Conrad-Diamond-Taylor; Hecke; BSD 1.2 | rebuild |
| VIII.1.1e | CM curves: L(E, 1) not zero gives E(Q) finite (Coates-Wiles 1977) and Sha finite (Rubin 1987) | external | BSD 1.2 | none needed for this paper |
| VIII.1.1f | Gross-Zagier 1986: L'(E, 1) is a nonzero multiple of the height of a Heegner point; a simple zero gives a point of infinite order | external | BSD 1.2 | none needed for this paper |
| VIII.1.1g | Kolyvagin 1988-90 with modularity: analytic rank 0 or 1 gives rank = analytic rank and Sha finite | external | BSD 1.2 | none needed for this paper |
| VIII.1.1h | Buhler-Gross-Zagier 1985: the curve 5077a has a zero of order exactly 3 and rank 3 | external (recalled) | BSD 1.2 | re-reading of the paper |
| VIII.1.1i | Kato 2004, Skinner-Urban 2014 and later: the p-part of the refined formula for many curves of rank 0 or 1 and many p | external (recalled) | BSD 1.2 | re-reading |
| VIII.1.1j | p-parity: Monsky 1996, Nekovar, Dokchitser-Dokchitser 2010; so finiteness of Sha would give (-1)^rank = w | external | BSD 1.2 | none needed for this paper |
| VIII.1.2a | No construction of two or more independent points from a higher zero (no higher Heegner points); no bound "rank <= order" beyond order 1 | open | BSD 1.3, 4 | a construction and a bound |
| VIII.1.2b | Finiteness of Sha in general (known for analytic rank at most 1) | open | BSD 1.3 | a proof |
| VIII.1.2e | No curve of proved analytic rank 4 or more is known; a zero is certified only up to order 3; numerics cannot certify a zero | classical (recalled) | BSD 1.3 | re-reading |
| VIII.2a | The BSD card: input a curve, a function and a sign; one open step `BSDStatement W`; conclusion the existence line and the parity of the rank; external inputs modularity and weak Mordell-Weil | Lean | `ProofPhase/Unified/BSDAPI.lean`, `Input`, `problem` | none (the open step is VIII.5.1) |
| VIII.2b | The ledger card: open step the growth form `C (log p)^r` of the partial Euler products, conclusion BSD, external input Goldfeld | Lean (plumbing; external content) | `ProofPhase/Unified/BSDAPI.lean`, `LedgerInput`, `ledgerCard` | none (the open step is VIII.5.2) |
| VIII.2d | IM states BSD over any number field and uses the true rank in the extended naturals (no junk value) | Lean | `Arsenal.BSD.Algebraic`, `algRank`; `Arsenal.BSD`, `BSDStatement` | none |
| VIII.3.0 | The adapted API instance `BSDAPI` is on standard axioms (log regenerated 2026-11-24, 46 declarations); IM's own audit of the native `Arsenal.BSD` modules (`arsenal/tools/check.sh`) is not run for this draft | paper | `docs/unified/bsd-axioms.log` (2026-11-24 04:50, after `BSDAPI.lean` 03:52; read, not rebuilt) | run IM's audit |
| VIII.3.1a | E(K) is finitely generated if E(K)/2E(K) is finite (Mordell-Weil from weak Mordell-Weil, through Mathlib's descent and naive height) | Lean (from the named part `WeakMordellWeil`) | `Arsenal.BSD.Algebraic`, `mordellWeil_of_weak`, `WeakMordellWeil` | a Lean proof of weak Mordell-Weil |
| VIII.3.1b | The torsion of E(K) is finite, unconditionally | Lean | `Arsenal.BSD.Algebraic`, `torsion_finite` (Mathlib `finite_torsion`) | none |
| VIII.3.1c | The rank `algRank` is the Z-module rank in the extended naturals; it equals `finrank` and is finite once E(K) is finitely generated | Lean | `Arsenal.BSD.Algebraic`, `algRank`, `algRank_eq_finrank`, `algRank_ne_top` | none |
| VIII.3.1d | Rank zero is: every point has finite order; and, unconditionally, E(K) finite; E(K) is infinite exactly when the rank is positive | Lean | `Arsenal.BSD.Algebraic`, `algRank_eq_zero_iff_torsion`, `algRank_eq_zero_iff`, `infinite_iff_algRank_pos` | none |
| VIII.3.2a | A continuation is analytic on `re s > a` with `a < 1` and equals Mathlib's L-series on a right half-plane; an entire function equal to the series for `re s > 3/2` is one; a continuation is analytic at 1 | Lean | `Arsenal.BSD.Analytic`, `IsContinuation`, `IsContinuation.of_entire`, `IsContinuation.analyticAt_one` | none |
| VIII.3.2b | Two continuations agree near s = 1, so the order of the zero there is well defined; a zero exists exactly when the order is positive | Lean | `Arsenal.BSD.Analytic`, `continuation_unique`, `order_welldefined`, `zero_iff_order_ne_zero` | none |
| VIII.3.2c | The gamma factor (over Q `N^{s/2} (2 pi)^{-s} Gamma(s)`) is analytic and not zero at s = 1; the completed function has the same order as the L-function | Lean | `Arsenal.BSD.Analytic`, `gammaFactor`, `gammaFactor_degree_one`, `gammaFactor_analyticAt`, `gammaFactor_one_ne_zero`, `completed_order` | none |
| VIII.3.2d | From the local functional equation `xi(2 - s) = w xi(s)` and a natural-number order n, `w = (-1)^n`; the strip form over Q implies the local one | Lean (from the functional equation) | `Arsenal.BSD.Analytic`, `order_parity`, `order_parity_of_factor`, `FunctionalEquation`, `analytic_parity`, `FunctionalEquation.of_strip` | none |
| VIII.3.3a | `count` is the number of solutions plus the point at infinity over a finite ring; `frobTrace = q + 1 - count`; the decidable Hasse check is the real inequality; over a finite field the local form is the same check (`hasseCheck_iff_card`) | Lean | `Arsenal.BSD.Count`, `count`, `frobTrace`, `hasseCheck`, `hasseCheck_iff`, `hasseCheck_iff_card` | none |
| VIII.3.3b | Over a finite field the count is Mathlib's `Nat.card` of the group of points; at every prime of good reduction the count of the curve read mod p is Mathlib's | Lean | `Arsenal.BSD.Count`, `count_correct`, `reduceMod`, `count_reduceMod` | none |
| VIII.3.3c | For y^2 = x^3 - x mod 5 the trace is -2 and the Hasse check passes, both by the kernel | Lean | `Arsenal/BSD/Count.lean`, the two `example`s at lines 84 and 86 (`by decide`) | none |
| VIII.3.4a | If `a^2 <= 4q`, the coefficients of `1/(1 - aT + qT^2)` satisfy abs(c_k) <= (k + 1) q^{k/2}; at bad places, for abs(a) <= 1, abs(c_k) <= 1 | Lean | `Arsenal.BSD.Hasse`, `invQuad`, `invQuad_coeff`, `quad_bound`, `lin_bound`, `invQuad_bound`, `invQuad_bound_lin` | none |
| VIII.3.4b | Under Hasse at one place, the coefficients of Mathlib's local power series are bounded by max 1 ((k + 1) q^{k/2}); the first coefficient of `W.LFunction` is 1 | Lean (from `LocalHasse`) | `Arsenal.BSD.Hasse`, `LocalHasse`, `localPowerSeries_coeff_zero`, `localPowerSeries_coeff_bound`, `eulerProduct_apply_one`, `LFunction_one` | none |
| VIII.3.4c | An L-series with first coefficient 1 that converges absolutely somewhere is not zero for all large real arguments; so every continuation has a finite order at s = 1 once the series converges somewhere | Lean | `Arsenal.BSD.Hasse`, `LSeries_not_eventually_zero`, `order_ne_top_of_LSeries`, `order_ne_top_of_summable` | none |
| VIII.3.4d | From the named part Hasse (and, beyond Q, the Euler product bound): absolute convergence for `re s > 3/2`, a finite order at s = 1, and parity with no order given separately | Lean (from the named parts) | `Arsenal.BSD.Hasse`; over Q `Arsenal.BSD.EulerRat`, `LSeriesSummable_of_hasse_rat`, `order_ne_top_rat`, `analytic_parity_of_hasse_rat` | a Lean proof of Hasse |
| VIII.3.5a | `BSDStatement W`: a continuation exists and the rank equals the order of its zero; with a continuation in hand it is the equation rank = order | Lean | `Arsenal.BSD`, `BSDStatement`, `bsdStatement_iff` | none |
| VIII.3.5b | Under BSD, E(K) is infinite exactly when `Lam 1 = 0` (no finite generation assumed) | Lean (from BSD) | `Arsenal.BSD`, `existence_line` | none |
| VIII.3.5c | Under BSD and the functional equation, a rank equal to n gives `w = (-1)^n`; also with `finrank` under finite generation | Lean (from BSD and the functional equation) | `Arsenal.BSD`, `rank_parity`, `rank_parity_of_fg` | none |
| VIII.3.5d | Under BSD, Hasse and the Euler product bound, the rank is finite and `w = (-1)^rank` with no rank given separately | Lean (from BSD, the named parts and the functional equation) | `Arsenal.BSD`, `algRank_ne_top_of_hasse`, `rank_parity_of_hasse` | Lean proofs of the two parts |
| VIII.3.5e | `RefinedBSD` states the refined formula with the rank, torsion order and discriminant derived and the period, regulator, Sha order and Tamagawa product as free numbers; it gives `BSDStatement` when its leading coefficient is not zero | Lean | `Arsenal.BSD`, `RefinedBSD`, `bsd_of_refined` | Lean definitions of the four free quantities |
| VIII.3.6a | The Frobenius eigenvalue `alpha` has norm `sqrt q` when `a^2 <= 4q`, and the point count is `norm(1 - alpha)^2` | Lean | `ProofPhase/Unified/BSDAPI.lean`, `frobAlpha`, `frobAlpha_normSq`, `norm_frobAlpha`, `count_normSq` | none |
| VIII.3.6b | Hasse's bound is an encoder: reflection coefficient `a/(2 sqrt q)` (cos theta), Szego factor `1 - a^2/(4q)` (sin^2 theta) in the unit interval | Lean (Hasse as input) | `ProofPhase/Unified/BSDAPI.lean`, `frob`, `frob_refl`, `frob_szego` | none (Hasse is an input) |
| VIII.3.6c | Each step factor `N_p/p` lies between `(1 - p^{-1/2})^2` and `(1 + p^{-1/2})^2`; the partial product keeps a margin and has a chain bound; no finite stage is zero | Lean (Hasse as input) | `ProofPhase/Unified/BSDAPI.lean`, `factor_bounds`, `EulerData`, `EulerData.fac_bounds`, `EulerData.lower`, `EulerData.upper`, `EulerData.no_finite_zero`, `EulerData.P_le` | none (Hasse is an input) |
| VIII.3.6d | The Euler ledger of one given integral curve W (by construction: the ledger is built from the curve, so its counts are the curve's point counts by `rfl`; natural because the step factor N_p/p is defined from these counts): its counts are Mathlib's point counts of W mod p by construction (Hasse for them stays the named input); at every prime of good reduction they are the computed counts of `Arsenal.BSD`, and the step factor is count/p; instance y^2 = x^3 - x at every odd prime | Lean (Hasse as input) | `ProofPhase/Closures/EulerCurve.lean`, `curveCount`, `ofCurve`, `ofCurve_N`, `ofCurve_N_good`, `ofCurve_fac_good`, `E32Euler_N` | none |
| VIII.3.6e | That these counts give the linear coefficient of Mathlib's local factor (`WeierstrassCurve.localPolynomial`: minimal model over the completion, its reduction, residue field Z/p) at a good prime is the classical definition of a_p; not linked in Lean | classical (not linked in Lean) | Silverman, AEC, App. C.16 (recalled); Mathlib `WeierstrassCurve.LFunction`; `Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv`, `PadicInt.residueField` | the link, stated and proved |
| VIII.3.7a | From modularity and weak Mordell-Weil as inputs: E(Q) finitely generated, torsion finite, the order independent of the continuation, its parity the sign | Lean (from modularity and weak Mordell-Weil) | `ProofPhase/Unified/BSDAPI.lean`, `unconditional` | none |
| VIII.3.7b | Gross-Zagier-Kolyvagin in its slot fills the card's open step whenever the order is at most 1; the content is external | Lean (plumbing) | `ProofPhase/Unified/BSDAPI.lean`, `LowRank`, `open_of_lowRank` | none |
| VIII.3.8a | The curve y^2 = x^3 - x over Q and Z has discriminant 64 and is elliptic; the three points of order two are on it | Lean | `ProofPhase/Unified/BSDAPI.lean`, `E32`, `E32_Δ`, `E32Z`, `E32Z_Δ`, `E32_points`, `instance : E32.IsElliptic` | none |
| VIII.3.8b | For this curve the computed count mod p is Mathlib's at every odd prime and the Hasse check at p = 5 is proved by the kernel; the trace of Frobenius at the odd primes to 37 and the Hasse check at the odd primes to 59 are computed in the build (`#eval`, `#guard`), not kernel proofs (the notes say "below 100"; the source checks to 59) | Lean (`count_E32`, `hasse_E32_five`) + numerical (`#eval`, `#guard`) | `ProofPhase/Unified/BSDAPI.lean`, `count_E32`, `hasse_E32_five` | extend the guard, or drop the note's claim |
| VIII.3.8c | The known values of this curve (continuation and functional equation by Deuring, `L(E, 1)` not zero, E(Q) the four points by Fermat's descent) are external inputs | external | `ProofPhase/Unified/BSDAPI.lean`, `Data32`; Deuring; Fermat; BSD 3.3 | rebuild |
| VIII.3.8d | From those values: rank 0 equals order 0, BSD holds for this curve, the card's open step is filled and the root number is +1 | Lean (from the external values) | `ProofPhase/Unified/BSDAPI.lean`, `input32`, `bsd_E32`, `card_E32` | none |
| VIII.3.8e | Hasse holds for 32a2 and 37a1 at all 2262 primes below 20000 (largest ratio 0.99989 and 0.99648) | numerical | `bsd_check.py`, `bsd_check.log` | none (never proves for all primes) |
| VIII.3.8f | 32a2: `L(E, 1) = 0.655514388573`, `L(E, 1)/Omega = 0.1250000000`, equal to the refined right-hand side 2 * 1/16 with recalled `c_2 = 2`, `Sha = 1`, `T = 4` | numerical | `bsd_check.log` | none |
| VIII.3.8g | 37a1: `L'(E, 1) = 0.305999773834`, `L'(E, 1)/Omega = 0.0511114083` against the recalled regulator 0.0511114082; (0, 0) has infinite order (5P not integral, Nagell-Lutz) | numerical | `bsd_check.log` | none |
| VIII.3.8h | The Euler ledger over `(log x)^r` at x = 100, 1000, 5000, 20000 is 1.65, 2.24, 2.12, 2.25 (32a2, target 2.157) and 6.82, 6.79, 7.96, 7.19 (37a1, target 8.23); the targets use Goldfeld's recalled constant `sqrt 2` | numerical | `bsd_check.log`; BSD 3.3 | none |
| VIII.3.8i | The recalled constants (the Tamagawa number of 32a2, the regulator of 37a1, `sqrt 2`) | classical (recalled) | BSD 3.3 | re-reading |
| VIII.4b | Weak Mordell-Weil: E(K)/2E(K) is finite (a named part in IM, an `External` in the API) | classical | Mordell 1922; Weil 1929; `Arsenal.BSD.Algebraic`, `WeakMordellWeil` | a Lean proof on Mathlib |
| VIII.4c | Hasse's bound at every good prime (a named part in IM, an `External` in `EulerData`); its textbook proof is the positive definite degree form on End(E) | classical | Hasse; Silverman VI.1.1 (recalled); `Arsenal.BSD.Hasse`, `Hasse`; `ProofPhase/Unified/BSDAPI.lean`, `EulerData` | a Lean proof (isogeny degrees or intersection theory on E x E) |
| VIII.4d | Euler products with Hasse-type coefficient bounds converge absolutely for `re s > 3/2`, dominated by `zeta_K(s - 1/2)^2`: proved over Q (the factor at p_v has q_v = p_v and v -> p_v is a bijection onto the primes); for a number field of degree > 1 a named part | Lean over Q (IM); classical (recalled) beyond | `Arsenal.BSD.EulerRat`, `eulerProductBound_rat`, `abs_eulerProduct_le`, `lseriesSummable_eulerProduct_primes`, `card_residueField_rat`; `Arsenal.BSD.Hasse`, `EulerProductBound` | a Lean proof over number fields (q_v = p^f, several v over one p) |
| VIII.4e | Gross-Zagier and Kolyvagin with modularity: analytic rank 0 or 1 gives BSD (`LowRank`) | external | `ProofPhase/Unified/BSDAPI.lean`, `LowRank` | none needed for this paper |
| VIII.4f | Goldfeld 1982: the 1965 growth form of the Euler products implies BSD and the Riemann hypothesis for L(E, s) (`LedgerInput.goldfeld`) | external | Goldfeld; K. Conrad 2005 (recalled); `ProofPhase/Unified/BSDAPI.lean`, `LedgerInput` | re-reading of the exact hypothesis at bad primes |
| VIII.4h | Weak Mordell-Weil is within reach on Mathlib; Hasse needs isogeny degrees or intersection theory on E x E; modularity is a very large formalisation | paper (estimate) | PREP (2026-11-24, BSD is IM; Hasse entries); BSD 2 | the formalisations |
| VIII.5.1 | **Open step of the card:** `BSDStatement W`, the order of the zero of L(E, s) at s = 1 equals the rank of E(Q); proved for order 0 and 1 by others, open from order 2 | open | `ProofPhase/Unified/BSDAPI.lean`, `problem`; `Arsenal.BSD`, `BSDStatement`; BSD 4 | a construction of r points from a zero of order r and a bound rank <= order |
| VIII.5.2 | **Stronger slot:** the ledger form, `product of N_p/p` grows like `C (log p)^rank`; by Goldfeld it also gives the Riemann hypothesis for L(E, s) | open | `ProofPhase/Unified/BSDAPI.lean`, `ledgerCard`, `EulerData.Balance`; BSD 4 | a proof |
| VIII.5.3 | The refined formula for all curves, with all five invariants, is open in general; it gives the rank part | open | `Arsenal.BSD`, `RefinedBSD`, `bsd_of_refined`; BSD 1.3 | a proof |
| VIII.6a | BSD is IM: both sides are derived from one Weierstrass equation and the card takes no content input; a statement about form, not about settling | reading | PREP (owner, 2026-11-24, "BSD is IM"); BSD 3 | none (a reading stays a reading) |
| VIII.6b | "The zeros follow existence": the order of the zero counts the independent rational points; exact counterpart in three levels (existence line, rank equation, ledger form) | reading | PREP (2026-11-24 entries on primes on a curve); BSD 0, 4 | none |
| VIII.6c | Hasse is rotation at a DB: Frobenius at p acts as a rotation with `cos theta_p = a_p/(2 sqrt p)` the encoder's reflection coefficient; the piece left open in Lean is one rotation per DB confined by one positivity | reading (Lean for the encoder: `frob`, `frob_refl`) | PREP (owner, 2026-11-24, "rotation at DB shaped"); `ProofPhase/Unified/BSDAPI.lean` | none |
| VIII.6d | Hasse's bound for one curve reads as `weil_bound_abs` at genus 1 (Lean proves it for every genus g from the Hodge index property and the intersection numbers; the genus-1 specialisation and the link of N to Mathlib's count are not made in Lean) | reading | `ProofPhase/Unified/HodgeLinear.lean`, `weil_bound_abs`; `ProofPhase/Unified/HodgeAPI.lean`, `curveCard`, `curve_open` | state the genus-1 instance and tie N to `count` |
| VIII.6e | What is left of BSD is the `.cmb` record: the refined formula's counts and measures balance to a dimensionless 1 (logarithm 0); the functional equation carries both sides through the rotation with sign `(-1)^rank`; dividing by `(s - 1)^r` removes the zero | reading | PREP (owner, 2026-11-24, "what is left of BSD is the .cmb file"); BSD 4 | none |
| VIII.6g | BSD in the triad: an equation between an existence count (independent points) and a zero count (the vanishing rate of the Euler ledger) | reading | BSD 4; PREP (the triad entries) | none |

## Part IX. Hodge (`draft/09-part-IX-hodge.md`)

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| IX.0a | Clay's statement (Deligne): on a projective non-singular variety over C every Hodge class (rational, type `(p, p)`) is a rational linear combination of classes of algebraic subvarieties | classical | Deligne's official description; HODGE 1.1 | none |
| IX.0b | The conjecture holds for p = 1 (Lefschetz), for curves (hard Lefschetz), and so for dimension at most 3 | classical | HODGE 1.2 | none |
| IX.0d | This part proves no case of the conjecture that was not already known; the geometry enters as `External` slots and the conjecture is the card's one `OpenStep` | (statement of scope) | HODGE header | none |
| IX.1.1a | Lefschetz (1,1): an integral class in `H^2(X, Z)` is `(1,1)` exactly when it is `c1` of a line bundle; on a projective X every line bundle is `O(D)`; so p = 1 holds, even integrally | classical | Lefschetz 1924; Kodaira-Spencer 1953; HODGE 1.2 | none |
| IX.1.1b | Hard Lefschetz is an isomorphism of Hodge structures that sends divisor classes to curve classes; so the rational conjecture holds in degree 2n - 2 | classical | HODGE 1.2 | none |
| IX.1.1c | Abelian varieties whose Hodge ring is generated by divisor classes satisfy the conjecture (very general, Mattuck; simple of prime dimension, Tankeev); Mumford's example and Weil's classes show not all abelian varieties are of this kind | classical / external (recalled) | HODGE 1.2 | re-reading |
| IX.1.1d | Weil classes on abelian fourfolds: discriminant 1 (Markman 2022; Floccari-Fu; van Geemen-Rapagnetta); every abelian fourfold of Weil type (Markman, arXiv 2509.23403, 2025), whose abstract reports the conjecture for abelian varieties of dimension at most 5 then follows (with Moonen-Zarhin) | external (abstracts only, not checked) | HODGE 1.2 | reading the papers |
| IX.1.1e | Other families: cubic fourfolds (Zucker), uniruled fourfolds (Conte-Murre), some Fermat hypersurfaces (Shioda) | external (recalled) | HODGE 1.2 | re-reading |
| IX.1.2a | The integral version fails: Atiyah-Hirzebruch 1962 found non-algebraic torsion classes in `H^4(X, Z)` (cobordism reading, Totaro 1997); Kollar 1992 found non-torsion failures | external (recalled) | HODGE 1.3 | re-reading |
| IX.1.2b | The statement fails on non-projective Kaehler manifolds: Zucker 1977 (complex tori), Voisin 2002 (even with Chern classes of coherent sheaves) | external (recalled) | HODGE 1.3 | re-reading |
| IX.1.3a | Grothendieck's standard conjectures B (Lefschetz type), C (Kunneth), D (numerical = homological), and the Hodge type (positivity of `(-1)^p <x, L^{n-2p} x>` on primitive algebraic classes) | classical | Grothendieck 1969; Kleiman; HODGE 1.4 | none |
| IX.1.3b | The Hodge-type conjecture is a theorem over C (Hodge-Riemann on primitive Hodge classes; algebraic classes are Hodge classes) | classical | HODGE 1.4 | none |
| IX.1.3c | In characteristic p the Hodge type is open except for surfaces (Hodge index theorem: Hodge 1937, Segre, Grothendieck 1958) and a few cases (Ancona 2021 for abelian fourfolds) | open (the exceptions external, recalled) | HODGE 1.4 | a proof |
| IX.1.3d | Grothendieck's standard conjecture C (Kuenneth type) holds over finite fields, from the Weil conjectures | classical | Katz-Messing 1974 | none |
| IX.1.3e | Weil 1948: for curves the Riemann hypothesis is the Castelnuovo-Severi inequality, the Hodge index theorem on `C x C` (Mattuck-Tate 1958; Grothendieck 1958) | classical | HODGE 1.4 | none |
| IX.1.3f | Deligne 1974 proved the Riemann hypothesis over finite fields for all smooth projective varieties by Lefschetz pencils, monodromy and Rankin's squaring trick, without the standard conjectures, which remain open | classical | HODGE 1.4 | none |
| IX.1.3g | The standard conjectures B (Lefschetz type) and D (numerical equals homological) are open in general (known in special cases, e.g. B for abelian varieties, Lieberman 1968) | open | HODGE 1.4; Lieberman 1968 (recalled) | a proof (class d of the closures round) |
| IX.2a | The Hodge card: input rational cohomology with its Hodge classes (described) and algebraic classes (exists); one open step; conclusion `hodge = alg`; the cycle class is a Hodge class as an `External`; `problem.proved` is antisymmetry of inclusion (`le_antisymm h i.alg_le`), so the card adds no mathematics (IX.2b, IX.3.2a) | Lean | `ProofPhase/Unified/HodgeAPI.lean`, `Input`, `HodgeConjecture`, `problem` | none (the open step is IX.5.1) |
| IX.2d | `Unified/All.lean` imports only `Unified` and `TransportBridges`; `HodgeAPI`, `BSDAPI`, `NavierStokesAPI`, `GRHToO1`, `GRH/ContourShiftTie` and `ElectricSUNRunning` have no importer and `BlowupSUN` only `ETM/Instances`; there is no `ProofPhase.lean` root, so these modules build by explicit target | paper | a grep of the `import` lines over `docs/mass-gap/formal/`; `lakefile.toml` | an aggregate import module |
| IX.3.1a | Cauchy-Schwarz for a symmetric form nonnegative on a subspace, over any ordered field | Lean | `ProofPhase/Unified/HodgeLinear.lean`, `sq_add_smul`, `cs_of_nonneg` | none |
| IX.3.1b | `PolHS` is a polarised real Hodge structure of weight 0 in circle form (representation of the circle, invariant symmetric form, positivity `Q(C x, x) > 0`); the Hodge classes are the vectors fixed by the circle | Lean | `ProofPhase/Unified/HodgeLinear.lean`, `PolHS`, `PolHS.hodge`, `PolHS.mem_hodge` | none |
| IX.3.1c | `Q` is positive definite on the Hodge classes of a `PolHS`, satisfies Cauchy-Schwarz there, and, in finite dimension, the Hodge classes split off orthogonally | Lean | `ProofPhase/Unified/HodgeLinear.lean`, `PolHS.hodge_pos`, `PolHS.hodge_nonneg`, `PolHS.hodge_cs`, `PolHS.hodge_isCompl` | none |
| IX.3.1d | The cohomology of a smooth projective variety, with `Q` from the cup product, an ample class and the Lefschetz signs, is such a structure (the Hodge-Riemann theorem); not in Mathlib, not proved here | classical | Hodge theory; HODGE 3.2 | Lean Hodge theory |
| IX.3.2b | From the Hodge-Riemann relations on rational Hodge classes (an `External`): `Q` is positive definite on algebraic classes (the Hodge standard conjecture in characteristic 0); an algebraic class orthogonal to all algebraic classes is zero (D in this piece); Cauchy-Schwarz on algebraic classes (the encoder bound) | Lean (from the Hodge-Riemann `External`) | `ProofPhase/Unified/HodgeAPI.lean`, `PosInput`, `PosInput.alg_pos`, `PosInput.alg_nonneg`, `PosInput.num_eq_hom`, `PosInput.alg_cs` | none (the input is IX.3.1d) |
| IX.3.2c | A `PolHS` whose rational points carry `Q` and whose Hodge classes contain the rational Hodge classes gives exactly the Hodge-Riemann slot | Lean | `ProofPhase/Unified/HodgeAPI.lean`, `hr_of_polHS` | none |
| IX.3.3a | Signature `(1, *)` and a positive class `H` give the Hodge index property: every class orthogonal to `H` has nonpositive square | Lean | `ProofPhase/Unified/HodgeLinear.lean`, `HodgeIndex`, `hodgeIndex_of_sigPos` | none |
| IX.3.3b | Under the index property, the reversed Cauchy-Schwarz inequality `B(D,D) B(H,H) <= B(D,H)^2` | Lean | `ProofPhase/Unified/HodgeLinear.lean`, `reverse_cs` | none |
| IX.3.3c | The Hodge index theorem on a surface: the intersection form has one positive direction | classical | Hodge 1937; Segre; Grothendieck 1958; HODGE 1.4 | Lean intersection theory |
| IX.3.4a | Castelnuovo-Severi: with `f1^2 = f2^2 = 0`, `f1 f2 = 1` and the index property at `f1 + f2`, `D^2 <= 2 (D f1)(D f2)` | Lean | `ProofPhase/Unified/HodgeLinear.lean`, `castelnuovo_severi` | none |
| IX.3.4b | With the intersection numbers on `C x C`: `g q a^2 - a b (N - q - 1) + g b^2 >= 0`; and Weil's bound `(N - q - 1)^2 <= 4 g^2 q`, `abs(N - (q + 1)) <= 2 g sqrt q` | Lean | `ProofPhase/Unified/HodgeLinear.lean`, `weil_form`, `weil_bound`, `weil_bound_abs` | none (the intersection numbers are IX.4d) |
| IX.3.4c | The curve card: open step the index property at `f1 + f2`, conclusion Weil's bound; with the Hodge index theorem in signature form as an `External` the open step holds | Lean (from the Hodge index `External`) | `ProofPhase/Unified/HodgeAPI.lean`, `CurveInput`, `curveCard`, `curve_open` | none |
| IX.3.4d | The full Riemann hypothesis for a curve also needs the bound for every extension `F_{q^n}` and the rationality of the zeta function; not in the Lean | classical | HODGE 1.4 | Lean statement |
| IX.3.5a | If Frobenius scales a positive-definite norm (or a positive Hermitian form) by c, every eigenvalue has `abs(mu)^2 = c` | Lean | `ProofPhase/Unified/HodgeLinear.lean`, `eigen_on_circle`, `eigen_on_circle_form` | none |
| IX.3.5b | The Weil card: from `StandardHodge` (a positive form on which Frobenius is a similitude of ratio `q^w`) every eigenvalue has `abs(mu)^2 = q^w` | Lean | `ProofPhase/Unified/HodgeAPI.lean`, `WeilInput`, `StandardHodge`, `weilCard` | none (the open step is IX.5.2) |
| IX.3.6a | The Lefschetz (1,1) chase: exactness at `H^2` and zero `(0,2)` part give a line bundle with that Chern class | Lean | `ProofPhase/Unified/HodgeLinear.lean`, `lefschetz11` | none |
| IX.3.6b | Rational descent: a rational class with a positive multiple in the image of a set lies in the rational span of the image | Lean | `ProofPhase/Unified/HodgeLinear.lean`, `rational_descent` | none |
| IX.3.6c | The open step of the Hodge card holds for p = 1, from the exponential sequence, the Hodge decomposition and the divisor interpretation as three `External` slots | Lean (from three `External` slots) | `ProofPhase/Unified/HodgeAPI.lean`, `DivisorInput`, `DivisorInput.toInput`, `DivisorInput.holds`, `DivisorInput.card`; `DivisorInput.exact`, `.hodge_int`, `.div_hodge` | none (the inputs are IX.4b) |
| IX.3.6d | Transfer along an isomorphism of Hodge structures; with hard Lefschetz as an `External`, the open step holds for curve classes | Lean (from the hard Lefschetz `External`s) | `ProofPhase/Unified/HodgeLinear.lean`, `transfer`; `ProofPhase/Unified/HodgeAPI.lean`, `CurveClassInput`, `CurveClassInput.toInput`, `CurveClassInput.holds`; `CurveClassInput.hl_hodge`, `.hl_alg` | none (the input is IX.4c) |
| IX.3.7a | A torsion class maps to 0 in rational cohomology, and 0 is a Hodge class; so the integral statement makes every torsion class algebraic | Lean | `ProofPhase/Unified/HodgeLinear.lean`, `integral_needs_torsion` | none |
| IX.3.7b | With a non-algebraic torsion class (Atiyah-Hirzebruch) as an `External`, the integral statement is false | Lean (from the Atiyah-Hirzebruch `External`) | `ProofPhase/Unified/HodgeAPI.lean`, `IntegralInput`, `IntegralHodge`, `integral_fails` | none (the input is IX.1.2a) |
| IX.3.7c | The non-projective failure is text only; Mathlib has no complex manifolds beyond holomorphic functions | paper | HODGE 1.3, 2 | none |
| IX.3.8 | Mathlib v4.34.0 has no Kaehler metric, de Rham theorem, Hodge decomposition, Chow ring, cycle class map or Lefschetz theorem; it has algebraic cycles on a scheme, the signature of a quadratic form, eigenvalues and the circle | paper | HODGE 2 (a search of the library) | none |
| IX.4a | The cycle class of a subvariety is a rational `(p, p)` class (`Input.alg_le`) | classical | HODGE 1.1 | none |
| IX.4d | The intersection numbers on `C x C`: `f1^2 = f2^2 = 0`, `f1 f2 = 1`, `Gamma f1 = 1`, `Gamma f2 = q`, `Delta f1 = Delta f2 = 1`, `Gamma^2 = q(2 - 2g)`, `Delta^2 = 2 - 2g`, `Gamma Delta = N` | classical | `ProofPhase/Unified/HodgeAPI.lean`, `CurveInput.geometry`; HODGE 3.5 | Lean intersection theory |
| IX.5.1 | **Open step of the card:** every rational `(p, p)` class is a rational combination of classes of algebraic cycles of codimension p; proved for p = 1 and p = n - 1, open for p >= 2 in general | open | `ProofPhase/Unified/HodgeAPI.lean`, `HodgeConjecture`, `problem`; HODGE 1.5, 3.1 | a proof for p >= 2 |
| IX.5.2 | **Second slot, a different problem:** the Hodge standard conjecture over `F_q`, a positive form on which Frobenius is a similitude of ratio `q^w`; open in general except for surfaces and special cases; the Riemann hypothesis over `F_q` is nevertheless a theorem by another route | open (the theorem classical, Deligne) | `ProofPhase/Unified/HodgeAPI.lean`, `StandardHodge`, `weilCard`; HODGE 1.4, 3.5 | a proof of the positivity |
| IX.6a | Describable implies exists: described = the rational `(p, p)` classes, exists = algebraic cycles; in the API `OpenStep (hodge <= alg)` with `alg <= hodge` external | reading | PREP (owner, "Describable => exists => positive"); HODGE 4 | none (a reading stays a reading) |
| IX.6b | Hodge is the geometric counterpart of the owner's Goedel completeness anchor; no completeness theorem bridges a Hodge-type description and a cycle, which is why it is open | reading | PREP (same entry); HODGE 4 | none |
| IX.6d | Describable must mean rational on a projective variety: torsion classes are Hodge but need not be cycles; on non-projective Kaehler manifolds descriptions outrun existence | reading (Lean for the torsion half: `integral_fails`) | HODGE 4; `ProofPhase/Unified/HodgeAPI.lean` | none |
| IX.6e | Hodge types are charges on the circle (the circle acts on `H^{p,q}` by `z^{p-q}`); the Hodge classes are the neutral vectors; the identification with DMP's G0 circle is the reading | reading (Lean for the model: `PolHS`, `PolHS.mem_hodge`) | HODGE 4; `ProofPhase/Unified/HodgeLinear.lean` | none |
| IX.6f | The Hodge index route is more efficiently correct than Deligne's: both are complete proofs; the positivity route has one moving part (Cauchy-Schwarz on a positive form, the shape of the encoder bound), so it transfers between problems | reading | PREP (owner, 2026-11-24, "more efficiently correct"); `ProofPhase/Unified/HodgeLinear.lean`, `cs_of_nonneg` | none |
| IX.6g | Reach of the positivity route: proved for curves, and for the index theorem on surfaces in every characteristic; in higher dimension it needs the Hodge type in characteristic p, open, where Deligne's route covers everything | open (the proved part classical) | PREP (same entry, care point 2); HODGE 1.4 | a proof of the Hodge type in characteristic p |
| IX.6h | Choosing the route names the open step for GRH over number fields (an arithmetic Hodge index on `Spec Z`); it does not close it | reading | PREP (same entry, care point 3) | none |
| IX.6i | The shared positivity of Hodge and the GRH column: described classes positive, so existing classes positive; the same form puts Frobenius eigenvalues on the circle; the two columns share "a positive form, a dynamics that is a similitude of it, and the line as the consequence" | reading (Lean for the steps: `PolHS.hodge_pos`, `PosInput.alg_pos`, `eigen_on_circle_form`, `curve_open`, `weil_bound`) | HODGE 4; PREP (Hodge-index-route entry) | none |
| IX.7.1 | The hard-Lefschetz `sl_2` decomposition, the Hodge-Riemann signature formula, Hodge structures of any weight with the Hodge filtration, and finiteness of lattice Hodge classes of bounded norm are reachable on Mathlib and not built | paper (estimate) | HODGE 2 | building them |
| IX.7.2 | Kaehler manifolds, harmonic forms, the Hodge decomposition itself, the cycle class map and the exponential sequence on a complex manifold need geometry Mathlib lacks | paper (estimate) | HODGE 2 | Mathlib geometry |

## Part X. GU, the Grand Unified reading (`draft/10-part-X-gu.md`)

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| X.0a | The Grand Unified reading of GUID: the framework containing SU(3) x SU(2) x U(1) in one structure with at least one checkable consequence; the release criterion is the owner's | (statement of scope) | `docs/paper/OUTLINE.md`, release criterion; `PREP.md`, naming entry | none |
| X.0d | This part derives no hypercharge, predicts no new particle or number and contains no new physics; the hypercharges are input | (statement of scope) | GU 1, header | none |
| X.1.1a | Grand unification embeds the Standard Model group in one simple group (SU(5): Georgi-Glashow 1974; SO(10): Georgi 1975, Fritzsch-Minkowski 1975) with one coupling at the unification scale | classical | GU 2.3 | none |
| X.1.1b | Not every SU(N) is a viable grand unified group; a GUT must contain SU(3) x SU(2) x U(1), cancel the anomalies with the observed matter and survive proton-decay limits | classical | `PREP.md`, "Every SU(N) as a valid unified theory" entry; GU 2.3 | none |
| X.1.2a | All Standard Model fields are invariant under a Z_6 in the centre of SU(3) x SU(2) x U(1); the gauge group may be the quotient by Z_1, Z_2, Z_3 or Z_6 with the same local physics; present experiments do not decide | classical | Tong, JHEP 07 (2017) 104, arXiv 1705.01853; GU 2.2 | a measurement (X.4.3, X.5) |
| X.2.1 | GU is not a `Problem` card in the Lean API; its Lean pieces are group-level statements in `General/` plus the API's G0-link statement | paper (observation) | `ProofPhase/API.lean`, `ProofPhase/API/Phase.lean`; GU 4 | a GU `Problem` card |
| X.2.2 | The one-generation field data (triality, duality, hypercharge in sixths) listed in the draft's table is the Standard Model's; it is the card's input | classical | GU 2.1; `ProofPhase/General/GUCentre.lean`, `SMField`, `smFields` | none |
| X.3.1a | A centre element (u, v, z) acts trivially on all Standard Model fields iff z^6 = 1, u = z^2, v = z^3 | Lean | `ProofPhase/General/GUCentre.lean`, `centrePhase`, `SMTrivial`, `sm_kernel` | none |
| X.3.1b | The kernel is cyclic of order 6, generated by (zeta^2, zeta^3, zeta) with zeta a primitive sixth root; the generator splits into a primitive cube root and -1 | Lean | `ProofPhase/General/GUCentre.lean`, `sm_kernel_cyclic`, `zeta6_prim`, `gen_order`, `gen_parts` | none |
| X.3.1c | CRT split: the order-2 part (1, -1, -1) and the order-3 part (zeta^4, 1, zeta^2) each act trivially; at the level of Z/6, ZMod 6 = ZMod 2 x ZMod 3 | Lean | `ProofPhase/General/GUCentre.lean`, `sm_kernel_two`, `sm_kernel_three`; `ProofPhase/General/SUNTwistPrimes.lean`, `centre6` | none |
| X.3.1d | The generator is trivial on a field iff 6 divides 2t + 3d + q; true for every field of the table | Lean | `ProofPhase/General/GUCentre.lean`, `gen_trivial_iff`, `gen_trivial_sm` | none |
| X.3.1e | Charge in thirds: if 6 divides 2t + 3d + q, every component has Q + t/3 an integer (integer charge for colour singlets, -1/3 + Z for triplets) | Lean | `ProofPhase/General/GUCentre.lean`, `charge_thirds`, `charge_thirds_sm` | none |
| X.3.1f | A colour singlet with a component of non-integer charge is not invariant under the generator | Lean | `ProofPhase/General/GUCentre.lean`, `fractional_singlet_breaks` | none |
| X.3.1g | The scalar matrices omega I for omega^N = 1 form a copy of Z_N in SU(N), with N elements, central, acting as omega on the fundamental | Lean | `ProofPhase/General/Centre.lean`, `centreHom`, `centreHom_injective`, `centreHom_central`, `card_centre`, `centreHom_rep` | none |
| X.3.1h | The SU(5) block embedding (A, B, z) -> diag(z^{-2} A, z^3 B) has determinant 1 and kernel exactly {(z^2 1, z^3 1, z) : z^6 = 1}; so an SU(5) unification through this block embedding forces Gamma = Z_6 (X.0b) | Lean | `ProofPhase/General/GUCentre.lean`, `su5Embed`, `su5_embed_det`, `su5_embed_kernel` | none |
| X.3.1i | Not formalised: a gauge field theory with this U(1); that the image of the SU(5) map is all of S(U(3) x U(2)); the anomaly equations; twist sectors of the product group; chiral matter | paper (observation) | GU 4 | formalisation, X.7 |
| X.3.2a | The Fourier coefficients of a character of the circle shift by its value; every continuous character of AddCircle T is x -> toCircle(n x) for an integer n, and n is unique | Lean | `ProofPhase/General/GUCharge.lean`, `fourierCoeff_char_shift`, `addCircle_char`, `addCircle_char_unique` | none |
| X.3.2b | Every continuous homomorphism from the circle to the circle is z -> z^n with n a unique integer | Lean | `ProofPhase/General/GUCharge.lean`, `circle_char`, `circle_char_unique` | none |
| X.3.2c | On a line every real a gives a character t -> e^{iat}; it factors through the circle exactly when a is an integer; quantisation comes from compactness alone | Lean | `ProofPhase/General/GUCharge.lean`, `line_char`, `line_char_periodic_iff` | none |
| X.3.2d | An N-th root of unity on the circle (an SU(N) centre element) sees z^n as omega^(n mod N) | Lean | `ProofPhase/General/GUCharge.lean`, `centre_char_mod` | none |
| X.3.2e | The chain: hypercharge acting by a continuous character of the circle on a field invariant under the Z_6 generator gives an integer q (derived from compactness), 6 divides 2t + 3d + q, and Q + t/3 is an integer for every component | Lean | `ProofPhase/General/GUCharge.lean`, `g0_charge_thirds` | none (the input is X.4.1) |
| X.4.1a | Anomaly cancellation (with the mixed gauge-gravitational anomaly) fixes the hypercharge ratios for the Standard Model representations; with a right-handed neutrino a B - L direction opens unless a Majorana mass is assumed | classical | Geng-Marshak 1989; Minahan-Ramond-Warner 1990; Babu-Mohapatra 1989; GU 2.1 | none |
| X.4.2a | What Gamma allows: colour singlets of charge 1/3 and 1/2 are allowed or forbidden according to Z_1, Z_2, Z_3, Z_6 (the draft's table) | classical | elementary arithmetic with the generators of X.3.1; Tong 2017; GU 2.2 | none |
| X.4.2b | Gamma also changes the allowed line operators, the minimal monopole charge and the theta periodicities; for Z_6 the fractional part of the axion-photon coupling is tied to the axion-gluon coupling | classical | Tong 2017; Reece, JHEP 10 (2023) 116, arXiv 2309.03939; Choi-Forslund-Lam-Shao, arXiv 2309.03937; GU 2.2, 2.4 | an axion discovery |
| X.4.3a | Neutrality of matter: electron-proton charge difference below about 1 part in 10^21 | external | Bressi et al. 2011, arXiv 1102.2766; GU 8.4 | none |
| X.4.3b | No free fractional charges found in bulk matter or at accelerators | external | Perl-Lee-Loomba, Annu. Rev. Nucl. Part. Sci. 59 (2009) 47; GU 2.4 | a discovery |
| X.4.3c | Proton decay not seen; the Super-Kamiokande bound is above 10^34 years for p -> e+ pi0; minimal non-supersymmetric SU(5) is excluded | external | arXiv 1610.03597, 2010.16098; GU 2.4 | a discovery |
| X.4.3d | The three Standard Model couplings do not meet at one point; with supersymmetric running they nearly do | external | Amaldi-de Boer-Fuerstenau 1991; GU 2.4 | none |
| X.4.3e | No magnetic monopole found (flux limits; production limits) | external | MACRO, IceCube, MoEDAL (Nature 602 (2022) 63; arXiv 2311.06509); GU 8.4 | a discovery |
| X.5a | Candidate (a): the U(1) of G0 glued to the SU(2) and SU(3) centres as fully as the matter allows selects Z_6; checkable through fractional charges, a monopole's charge, axion couplings; a falsifiable reading, coinciding with what SU(5) gives | reading | GU 3.3, 6 | a DMP theorem stating the selection before the hypercharges |
| X.5b | Candidate (b): integer charge from the compact G0 circle (derived, X.3.2), thirds from the input, measured (X.4.3a); it is also the standard expectation of any compact U(1) | paper | GU 8.1, 8.5 | the owner's decision (X.5f) |
| X.5c | The project's twist-sector results are for pure gauge theory with one group; there the whole centre is a symmetry, so they cannot single out Z_6 | paper | GU 3.2 | X.7 item 3 |
| X.5d | "2 first, then 3" does not give Z_6 as a consequence: the centre of SU(2) x SU(3) is Z_6 once the factors are chosen, which Z_6 part is divided out is set by the matter, and Z_2 x Z_3 has no order | paper | GU 1, 3.2 | none |
| X.5e | A DMP theorem that selects Z_6 or the hypercharges does not exist | open | GU 3.2, 5 | X.7 item 1 |
| X.5f | The owner's decision on the gate's "at least one checkable consequence" (also X.0c): uniform charge quantisation, one unit for all matter (candidate (b)), with the unit guaranteed as the ODP's dimensionless 1, the same construction as Yang-Mills' lower edge (III.64a); it coincides with the standard expectation of any compact U(1), and no consequence beyond it is claimed (X.5e) | reading | GU 8.1, 8.5; `PREP.md`, 2026-11-24, "Five answers", 3 | none for the decision; X.5e for a consequence beyond the standard one |
| X.5g | The owner's position: GU comes down to well-defined inputs, which DMP can guarantee; the checkable consequence comes from the link to G0 | reading | `PREP.md`, "GU is pretty much done" and "The checkable consequence for GU" entries | none |
| X.6a | "G0's U(1) possibility field": every centre phase is a point on one circle (centres on one circle: Lean, X.3.1g) | reading | `PREP.md`; GU 3.3 | none |
| X.6b | "The universal quantum running" reads as charge quantisation (the step from the circle to integer charges is X.3.2) | reading | `PREP.md`, 2026-11-24 entry; GU 8 | none |
| X.6c | Electroweak symmetry breaking leaves (SU(3) x U(1)_em)/Z_3: the Z_2 part is absorbed, the Z_3 part survives as the charge-colour correlation | classical | GU 3.3 | none |
| X.6d | "2 then 3" reads as electroweak breaking, then confinement; it predicts nothing beyond the standard picture | reading | GU 3.3 | none |
| X.6e | "SU(5) with a single coupling is G0 at GRH, with a forward arrow independent of scale"; the single coupling holds at one scale only, and the programme lies beyond Yang-Mills, GRH and NP vs coNP | reading | `PREP.md`, naming entry; GU 3.3 | none |
| X.6f | On s > 1 zeta decreases continuously from infinity to 1, so it takes every integer N >= 2 exactly once; it indexes every SU(N) one to one | classical | continuity and monotonicity; `PREP.md`, "Every SU(N) as a valid unified theory" entry | none |
| X.6g | Every SU(N) "describes existence"; descending from 2 and 3 | reading | `PREP.md`, same entry | none |
| X.6h | SU(2) as the stable Ricci-flow profile (Appendix A) has no found link to the global form Z_6 | paper (observation; under X.6's readings) | GU 3.3 | a link |
| X.7a | Route 1: a DMP principle, stated before the hypercharges and proved as a theorem about running existence spaces, whose consequence is that the surviving centre twists are glued maximally to the U(1) | open | GU 6, item 1 | the theorem |
| X.7b | Route 2, done classically in Lean: for one generation with the Standard Model representations the four anomaly conditions (SU(3)^2 U(1), SU(2)^2 U(1), gravitational, U(1)^3) have exactly the solutions q = q_Q (1, 4, -2, -3, -6), up to u <-> d, and the degenerate family q_Q = 0; with q_Q > 0 and coprime charges the charges are those of `smFields`, and the centre acting trivially is the Z_6 (composing with `sm_kernel`, `gen_trivial_iff`). The input is a classical theorem, not a DMP one | Lean | `ProofPhase/Closures/Anomaly.lean`, `anomalyFree_iff`, `anomaly_fixes_sm`, `fermion_kernel`, `anomaly_fixes_Z6`; Geng-Marshak 1989; Minahan-Ramond-Warner 1990 | none (the degenerate family is excluded by q_Q > 0, the Yukawa input, stated in the file) |
| X.7c | Route 3: twist sectors of a lattice SU(3) x SU(2) x U(1) theory with Z_6-invariant vector-like matter; chiral matter stays out of reach | open | GU 6, item 3 | the extension of the `SUNTwist` chain |
| X.7d | Route 4: a statement about running couplings needs the continuum theory with matter | (statement of scope) | GU 6, item 4 | beyond the paper's scope |
| X.7e | Until one lands, the paper can say: SU(3) x SU(2) x U(1)/Z_6 as one structure (classical, Lean-stated); readings that select Z_6 and are falsifiable; charge quantisation proved and measured but standard; no consequence derived from DMP beyond that | paper | GU 6 (closing paragraph); X.5f | X.5e (a consequence beyond the standard expectation) |

## Part XI. Outlook: a settling machine (`draft/11-outlook-settling-machine.md`)

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| XI.1 | The first author's concept of a DMP-native general intelligence (CMOS in IM tokens, one Milky Way gate, an externally set tick, total freedom inside) | reading | `PREP.md` (2026-11-23); the first author | none (outlook) |
| XI.1b | The system works directly on the vectors embedding existence, its meta layer for arbitrary logic, as long as a correct answer comes out | reading | the first author (2026-11-23) | none (outlook) |
| XI.1c | Fast weights and hypernetworks as the DMP-native form: an existence embedding with a meta layer, changed through IM (and GG) while existence stays guaranteed | reading | the first author (2026-11-23) | none (outlook) |
| XI.3 | The gate certifies integrity and freshness, not meaning; it must check acts, not self-reports | paper | XI.3 | none |

---

## Appendix A. Validation: Poincare, SU(N) and the rigid groups (`draft/12-appendix-a-validation.md`)

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| A.1a | Ricci flow on a closed 3-manifold with positive scalar curvature has a singularity by T <= 3/(2 R_min(0)) | classical | Hamilton; BL 6.1 | none |
| A.1b | The W-entropy is non-decreasing and gives kappa-noncollapsing at every scale | classical | Perelman, arXiv math/0211159; BL 6.2 | none |
| A.1c | Each surgery removes a definite volume and volume is bounded, so finitely many surgeries on a finite interval | classical | Perelman, arXiv math/0303109; BL 6.2 | none |
| A.1d | Blowup limits are kappa-solutions, classified in 3D; the canonical neighbourhood theorem; surgery along necks | classical | Perelman, arXiv math/0303109; BL 6.2, 6.3 | none |
| A.1e | Finite extinction for simply connected closed 3-manifolds, which certifies the 3-sphere | classical | Perelman, arXiv math/0307245; Colding-Minicozzi 2005; BL 6.4 | none |
| A.1f | Singular Ricci flows through singularities exist without choices and are unique and stable | classical | Kleiner-Lott; Bamler-Kleiner, arXiv 1709.04122; BL 6.3 | none |
| A.1g | The ledger fit of Perelman's proof: steps, monotone quantity (no uniform positive cost), one estimate at all scales, quantum per step, boundary, act, end | reading | BL 6.2 | none (a reading stays a reading) |
| A.2 | Verdict: the restatement matches Perelman's proof as a description, not as a mechanism; nothing new is claimed | reading | BL 6.5 | none |
| A.3a | The unit sphere of C^2 is in bijection with SU(2) | Lean | `ProofPhase/Unified/BlowupSUN.lean`, `su2Mat_mem`, `su2_form`, `sphereEquivSU2` | none |
| A.3b | That bijection is a diffeomorphism, so SU(2) is the 3-sphere | classical | BL 7.1 | Lean topology statement |
| A.3c | The bi-invariant metric on SU(N) shrinks as g(t) = (1 - N t) g(0), extinct at 1/N, with the Einstein constant growing as lambda' = 2 lambda^2 | Lean (model: the scalar factor with lambda = N/2 supplied; no metric or Ricci flow object) | `ProofPhase/Unified/BlowupSUN.lean`, `shrink_hasDerivAt`, `shrink_unique`, `shrink_pos`, `shrink_extinct`, `einstein_hasDerivAt`, `einstein_unbounded`, `sun_extinction` | none |
| A.3d | Ric = (N/2) g for the metric -tr(XY) on SU(N) | classical | Killing form; BL 7.2 | none |
| A.3e | The constants of A.3d checked for N = 2, 3, 5, 11 (error below 5e-15) | numerical | `blowup_sun_check.py`, `blowup_sun_check.log` | none |
| A.3f | The extinction of A.3c holds for every positive Einstein manifold, so it carries no topological information about SU(N) | classical | BL 7.2 | none |
| A.3g | Positive-Ricci metrics on a closed 3-manifold flow to constant curvature, so SU(2) attracts | classical | Hamilton 1982; BL 7.3 | none |
| A.3h | For N >= 3 the first Laplace eigenvalue N - 1/N lies strictly inside the Cao-He window; for N = 2 it sits exactly on the lower edge | Lean (the number N - 1/N; that it is the first Laplace eigenvalue is classical, BL 7.3) | `ProofPhase/Unified/BlowupSUN.lean`, `sun_window`, `su2_window_edge` | none |
| A.3i | Cao-He's criterion and verdict (SU(N), N >= 3, linearly unstable) and Kroencke's dynamical instability | external | Cao-He, arXiv 1304.2697 (Crelle 2015); Kroencke (recalled); BL 7.3 | none |
| A.3j | "Poincare for SU(N)" (homotopy equivalent to SU(N) implies homeomorphic or diffeomorphic). N = 2: true (Poincare; TOP = DIFF in dimension 3). N = 3: true in both categories; every closed smooth manifold homotopy equivalent to SU(3) is diffeomorphic to it (in particular `SU(3) # Sigma^8` is diffeomorphic to SU(3)). N >= 4: false in both categories (`H^8(SU(N); Q) != 0` below the top degree gives closed smooth manifolds homotopy equivalent to SU(N) with `p_2 != 0`, hence not homeomorphic to the parallelisable SU(N)) | external (N = 3); paper (N >= 4, a surgery computation from classical theorems) | X. Wang, arXiv 1810.08478, Theorem 1.1, Corollary 1.2 (read in v1; the journal version, Acta Math. Sinica 37 (2021), as cited in the note, not checked); Browder 1972; Wall 1970; Kirby-Siebenmann 1977; Novikov 1965; `docs/unified/PERELMAN-DMP.md` 2 | none for N <= 3; for N >= 4 a published reference (optional) |
| A.3k | With the point SU(1), the SU(N) determined by their homotopy type are exactly N = 1, 2, 3; the circle U(1) is rigid as well | paper (from A.3j; S^1 classical) | A.3j; `docs/unified/PERELMAN-DMP.md` 2 | none |
| A.4 | The side-by-side table of Perelman, Chen-Hou and the claimed route I | reading | BL 6.5; NS 2.3 | none |
| A.5i | Among U(1) and the SU(N), the groups determined by their homotopy type are exactly U(1), SU(2), SU(3), the Standard Model's factors; that rigidity selects them is the owner's reading | paper (the selection: reading) | A.3j, A.3k; `PREP.md`, 2026-11-24, "The rigid start" | A.5j | Sp(2) = Spin(5) is strongly topologically rigid: its structure set is a point, so every homotopy equivalence from a closed topological manifold to Sp(2) is homotopic to a homeomorphism (cells 0, 3, 7, 10; `[Sp(2), G/TOP] = H^10(Sp(2); Z/2) = Z/2`; the surgery obstruction is the Kervaire invariant, an isomorphism onto L_10; L_11 = 0). Smooth: every smooth homotopy Sp(2) is `Sp(2) # Sigma`, Sigma in Theta_10 = Z/6; the order-3 Sigma are not in the homotopy inertia group | paper (a surgery computation from classical theorems; the coordinator's sketch, confirmed by an independent read; no published statement found) | Kirby-Siebenmann 1977; Rourke-Sullivan, Ann. of Math. 94 (1971); Madsen-Milgram 1979; Kervaire-Milnor 1963; Maruyama-Oshima, J. Math. Soc. Japan 60 (2008); Kreck-Lueck, arXiv math/0509238; `docs/unified/G2-SP2-RIGIDITY.md` 1 | smooth only: the inertia group of Sp(2) |
| A.5j | Sp(2) = Spin(5) is topologically rigid: cells in dimensions 0, 3, 7, 10; the normal invariants see them through pi_3, pi_7, pi_10 of G/TOP (0, 0, Z/2); the top class is detected by the Kervaire invariant in L_10 = Z/2, and L_11 = 0, so the structure set is a point. (Sp(2) and G2 pass the rational test that excludes SU(N), N >= 4; the witness reading A.5o needs both rigid) | paper (coordinator's sketch; needs an independent read) | `PREP.md`, 2026-11-24, "The two hidden witnesses", 4; Wall, Surgery on compact manifolds; Kirby-Siebenmann | an independent read; the smooth case (exotic 10-spheres) |
| A.5k | Among compact simple groups, representations that are not their own conjugate exist exactly for SU(N), N >= 3, Spin(4k+2) and E6 (-1 not in the Weyl group); G2, Sp(n), Spin(2n+1) and SU(2) have only self-conjugate ones; U(1) has the charges e^{iq theta} | classical | Lie theory (e.g. Slansky, Phys. Rep. 79 (1981)); `PREP.md`, 2026-11-24, "Only U(1) carries content" | none |
| A.5l | Among the groups of A.5k with complex representations, only SU(3) is rigid: SU(N), N >= 4, is not (A.3j); Spin(4k+2), k >= 2, and E6 have rational cohomology in a degree 4i below the top (Spin(10) and E6: degree 12), the room that breaks rigidity for SU(N) | paper (rational test; the surgery step not written out for Spin and E6) | A.3j; `docs/unified/PERELMAN-DMP.md` 2.3 | the surgery step for Spin(4k+2) and E6 |
| A.5m | Only U(1) carries content across the gate; a non-abelian factor certifies only through its centre on the U(1) circle (Z_2, Z_3, glued as Z_6); "carries content" read as "has a complex representation" | reading | `PREP.md`, 2026-11-24, "Only U(1) carries content"; X.3 (Z_6, Lean) | none |
| A.5n | The compact simple Lie groups of rank 2 are exactly SU(3), Sp(2) = Spin(5) and G2; only SU(3) has complex representations; their centres are Z_3, {+1, -1} and trivial | classical | Lie theory (Cartan classification) | none |
| A.5o | The owner's witness reading: Sp(2) and G2, dimensionless to the encoder (self-conjugate, centres on the real points of the circle), are the two hidden witnesses the U(1) gate needs; the gate checks that the constants resolve to 1 (the encoder's root, Lean `Encoder.root`), certifies and transports the content | reading | `PREP.md`, 2026-11-24, "The two hidden witnesses"; `ProofPhase/Unified/Encoder.lean`, `root` | A.5r (Sp(2) passes, strongly, A.5j; G2 is not strongly rigid, A.5p, and its rigidity is one open test) |
| A.5p | G2 is not strongly rigid: its structure set has exactly two elements (`[G2, G/TOP]` has four: `H^6(G2; Z/2)` from pi_6(G/TOP) and the top cell; `H^8(G2; Z) = 0`; the surgery obstruction is the top coordinate; L_15 = 0). The second structure `h: X -> G2` has normal invariant x_3^2, pulled back from S^6 = G2/SU(3); h is tangential, X is stably parallelisable and can be taken smooth, and no characteristic class separates X from G2 | paper (a surgery computation from classical theorems; the count checked two ways) | Borel 1954; Mimura 1967 via Maruyama-Oshima 2008; Kirby-Siebenmann 1977; Rourke-Sullivan 1971; Kreck-Lueck, arXiv math/0509238; `docs/unified/G2-SP2-RIGIDITY.md` 2 | none for the count; A.5r for rigidity |
| A.5r | G2 is rigid, i.e. the fake X of A.5p is homeomorphic to G2: this holds exactly when G2 has a self-homotopy equivalence not homotopic to a homeomorphism (Kreck-Lueck); the standard construction needs an 8-sphere dual to x_3^2, and none exists; the test: does some element of pi_14(G2) carry nu^2 on the 8-cell stably? | open | `docs/unified/G2-SP2-RIGIDITY.md` 2.5; Kreck-Lueck, Thm 1.1, 2.2 | the test, now reduced (`docs/unified/G2-SP2-RIGIDITY.md` 5): the stable top-cell component of the lift `[nu_5^2]` in `pi_11(S^8)` (odd multiple of nu: G2 rigid, given two formulas still to verify); or an invariant separating X from G2; the smooth case (Theta_14 = Z/2) |
| A.5s | The owner's reading: the live G2 candidate (through SU(3), the confined fibre, whose top cell opens onto G2's 8-cell) is a confined CMOS's open interface channel, and the square nu . nu = nu^2 it needs folds in through reflection positivity; it predicts that the channel's top-cell component is an odd multiple of nu; nu . nu is a composition, not a reflection form | reading (the channel's odd degree: classical; the square: sketch) | `PREP.md`, 2026-11-24, "The live G2 candidate"; `docs/unified/G2-SP2-RIGIDITY.md` 5 | A.5r |
| A.5t | The owner's reading: since the DB can be drawn freely, every setting that can be placed through the gate can be certified, so the G2 channel goes back into the one assumption (the scale certificate, III.68a, Lean from it); G2's rigidity is a finite computation that the assumption cannot decide, so the reading predicts its answer (rigid) and the computation tests the prediction and the reach of "placed, hence certified" | reading | `PREP.md`, 2026-11-24, "The G2 channel goes back into O1"; III.68a; A.5r | A.5r |
| A.5u | G2 is rigid if its box shares the gate with the certified one box (the one assumption, III.64, as a named OpenStep); the owner's "certified as a DMP-complete state, equivalent to O1 as constructability"; the DMP corollary is the next layer's named hypothesis, never a Lean axiom; G2's unconditional rigidity (A.5r) is not proved | Lean (from External: the surgery input; from OpenStep: III.64) | `ProofPhase/ETM/G2Rigidity.lean`, `g2_rigid_of_one_assumption`, `g2_rigid_of_one_assumption'`; `PREP.md`, 2026-11-24, "The one assumption certifies the G2 state", "A corollary becomes an axiom one layer down" | III.64; the External slot (surgery theory, not in Mathlib) |
| A.5v | G2 is rigid exactly when its rigidity box is DMP-complete (two presentations, A.5p; the normal invariant of the self-equivalences to Z/2); a computation showing G2 not rigid refutes the sharing for G2 | Lean (from External: the surgery input) | `ProofPhase/ETM/G2Rigidity.lean`, `g2_rigid_iff_complete`, `g2_not_shared_of_not_rigid` | the External slot |
| A.5q | The owner's reading: the fake G2 is cancelled by the reflection positivity of the start; the room is x_3^2 in H^6(G2; Z/2), whose square x_3^4 vanishes (classical), read as a null state of a reflection-positive form; a Z/2 class has no sign and the cup square is not the reflection form; the exact counterpart of "cancelled" is "absorbed by a self-equivalence of G2", which the reading predicts and A.5r tests | reading (the square vanishing: classical) | `PREP.md`, 2026-11-24, "The fake G2 is cancelled", "The G2 and Sp(2) round"; IV.9.5a | A.5r |

## Draft 3 labels (relabelled 2026-11-24, draft 4)

Draft 4 is machine-first; every row kept its content and got the label of its new place. A draft-3 label, as used in older notes (`PREP.md`, `OPEN-CLAIMS-CLOSURES.md`, `CLAIMS-AUDIT.md`, `docs/unified/`), maps as follows:

| Draft 3 | Draft 4 |
|---|---|
| I.8i, I.8j, I.8k (the one-box test) | II.4a, II.4b, II.4c |
| II.9, II.10, II.11, II.12, II.13, II.14 (the machine) | II.1, II.2, II.3, II.5, II.6, II.7 |
| II.0, II.1, II.2, II.3, II.4, II.5, II.6, II.7, II.8 (the tools) | II.8, II.9, II.10, II.11, II.12, II.13, II.14, II.15, II.16 |
| II.15 (where Part II ends) | II.17 |
| X.n (the generalisation) | III.n |
| III.n (Yang-Mills), IV.n (GRH), V.n (P vs NP) | IV.n, V.n, VI.n |
| VI.n (Navier-Stokes), except VI.6 | VII.n |
| VI.6, VI.6.n (Perelman, Poincare for SU(N)) | A.0, A.n |
| VII.n (BSD), VIII.n (Hodge) | VIII.n, IX.n |
| IX.n (GU), except IX.6i to IX.6r | X.n |
| IX.6i to IX.6r (the rigid groups) | A.5i to A.5r |
| 0.n, I.n, XI.n | unchanged |

## Folded labels (audit of 2026-11-24)

These labels were rows of draft 3. Each was a duplicate of, or folded into, the row named; chapters may still cite the old label. A row marked "dropped" has no chapter text.

| Old label | Now |
|---|---|
| 0.2 | IV.3.6, IV.5.6 |
| 0.3 | V.0a |
| 0.4 | V.0c |
| 0.6 | III.64, III.67 |
| 0.7 | II.3.2, II.3.3 |
| 0.8 | III.58 |
| I.4a | VI.3.1 |
| I.6a | II.15.1 |
| I.9b | II.6.2 |
| I.11a | II.6.1, II.6.4 |
| II.11.5 | V.2.5a, V.2.5c |
| II.12.3b | IV.2.1 |
| II.5.2b | III.27 |
| IV.1.2 | II.9.2 |
| IV.3.2 | II.14.3 |
| IV.3.8 | II.14.4 |
| IV.4.1 | II.13.2 |
| IV.6.10 | (dropped: the coarse test is in no chapter) |
| IV.7.3 | I.6c |
| V.1.1 | II.9.3 |
| V.1.4 | II.9.4 |
| VI.1.2 | II.12.3, II.9.5 |
| VI.1.3 | II.10.1 |
| VI.1.4 | II.12.1, II.12.2, II.12.5 |
| VI.1.10 | (dropped: in no chapter) |
| VI.3.6 | II.14.2 |
| VI.3.7 | II.14.5 |
| VI.3.12 | (dropped: in no chapter) |
| VI.4.3 | II.14.5 |
| VI.5.1 | II.15.1, II.15.2 |
| VI.6.N2 | VI.4.10 |
| VII.0c | VII.4.2a |
| VII.0d | VII.4.1a, VII.4.1d |
| VII.8 | 0.1 |
| VIII.0c | VIII.1.1d |
| VIII.0d | VIII.3.5a |
| VIII.0f | VIII.5.1 |
| VIII.1.1k | (dropped: context only, unreferenced) |
| VIII.1.2c | VIII.5.3 |
| VIII.1.2d | V.0c |
| VIII.2c | II.5.1, II.6.2 |
| VIII.3.4e | VIII.3.3a |
| VIII.3.7c | VIII.2b |
| VIII.4a | VIII.1.1d |
| VIII.4g | VIII.4b, VIII.4c, VIII.4d |
| VIII.5.4 | VIII.1.1g |
| VIII.5.5 | VIII.1.1f, VIII.1.1g, VIII.1.2a |
| VIII.5.6 | VIII.3.6c |
| VIII.5.7 | VIII.3.2d |
| VIII.5.8 | VIII.1.1b, V.0c |
| VIII.6f | VIII.5.3 |
| VIII.7.1 | VIII.3.0 |
| VIII.7.2 | 0.1 |
| IX.0c | IX.5.1 |
| IX.1.4b | V.2.5c |
| IX.2b | IX.2a |
| IX.2c | II.5.1 |
| IX.3.2a | IX.2a |
| IX.4b | IX.1.1a, IX.3.6c |
| IX.4c | IX.1.1b, IX.3.6d |
| IX.4e | IX.1.3f |
| IX.5.3 | V.2.5c |
| IX.6c | VII.4.4a |
| IX.7.3 | 0.1 |
| X.0b | X.3.1h |
| X.0c | X.5f |
| X.3.2f | (dropped: in no chapter) |
| X.3.3 | II.5.4 |
| X.4.1b | X.7b |
| III.2b | IV.8.1, V.5.2 |
| III.8 | II.2.3 |
| III.30 | II.3.2, II.3.3 |
| III.33 | III.7g |
| III.35 | II.6.2 |
| III.44 | II.1.0 |
| III.45 | V.3.6b |
| III.49b | III.7g |
| III.50 | I.8d |
| III.56 | IV.1.6, IV.1.7, IV.3.1 |
| III.60 | XI.1, XI.3 |
| XI.2a | II.3.2 |
| XI.2b | II.3.3 |
| XI.2c | II.3.1 |
| IX.1.4a | IX.1.3c, IX.1.3g |

Part X row X.0b was a cross-reference and is folded; the scope rows that stay (not counted) are 0.1, IV.0, VII.0e, VIII.0e, IX.0d, X.0a, X.0d.

## Counts by primary status

Counted on the rows above (each row once, by its first mark; scope rows not counted: 0.1, IV.0, VII.0e, VIII.0e, IX.0d, X.0a, X.0d). The draft 3 column is the count of the committed draft; the next column is after the audit of 2026-11-24 (rows removed and added, status changes, `certified` as its own mark, II.3.2 and II.3.3 counted as Lean):

| Status | Current (2026-11-24) | After the decidable start (2026-11-24) | After the fake G2 reading (2026-11-24) | After the witnesses (2026-11-24) | After the U(1) reading (2026-11-24) | After the rigid start (2026-11-24) | After the one-box test (2026-11-24) | After A.3j (2026-11-24) | After the second answers (2026-11-24) | After the owner's answers (2026-11-24) | After closures (draft 3) | Draft 3 as committed | Draft 2 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Lean | 245 | 232 | 232 | 232 | 232 | 232 | 231 | 221 | 221 | 221 | 221 | 239 | 114 |
| classical | 125 | 125 | 124 | 124 | 123 | 122 | 121 | 121 | 121 | 121 | 121 | 120 | 42 |
| external | 42 | 41 | 41 | 41 | 41 | 41 | 41 | 41 | 40 | 40 | 40 | 48 | 7 |
| conditional | 7 | 7 | 7 | 7 | 7 | 7 | 6 | 5 | 5 | 4 | 4 | 4 | 3 |
| paper | 62 | 60 | 60 | 60 | 59 | 58 | 56 | 56 | 56 | 56 | 56 | 63 | 27 |
| numerical | 22 | 22 | 22 | 22 | 22 | 22 | 22 | 22 | 22 | 22 | 22 | 24 | 17 |
| certified | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 0 | 0 |
| reading | 100 | 93 | 92 | 91 | 90 | 89 | 88 | 87 | 87 | 86 | 83 | 83 | 25 |
| open | 46 | 46 | 46 | 46 | 46 | 46 | 45 | 44 | 45 | 47 | 48 | 70 | 28 |
| **Total** | **651** | **628** | **626** | **625** | **622** | **619** | **612** | **599** | **599** | **599** | **597** | **651** | **263** |

The owner's answers of 2026-11-24 moved X.5f from open to reading and added III.64a and III.64b (reading); IV.9.5b stays open as the lower edge of the one assumption. The second answers of the same day moved IV.9.5b to conditional on III.64 (placed at the ODP's end, as III.66) and VII.7e to reading (Navier-Stokes not DMP-complete, blowup the expected and falsifiable consequence). The Perelman round settled A.3j (open to external: N = 3 rigid in both categories, Wang; N >= 4 not, paper). The one-box test (the rotation API) added 13 rows: II.4a to II.4c, IV.10c to IV.10e, VII.7g, VII.7h, III.68 to III.68d (10 Lean, 1 open, 1 reading, 1 conditional). The rigid start added 7 rows: A.3k, A.5i, A.5j, III.69 to III.69c (1 Lean, 1 classical, 2 paper, 1 reading, 1 conditional, 1 open: the rigidity of Sp(2) and G2). The U(1) reading added A.5k (classical), A.5l (paper) and A.5m (reading). The witness reading added A.5n (classical), A.5o (reading) and A.5p (open: G2), and A.5j became a paper sketch (Sp(2) topologically rigid). The fake G2 reading added A.5q (reading). The decidable start added III.70 (reading) and III.70a (classical). The G2 round confirmed A.5j (Sp(2) strongly rigid), moved A.5p from open to paper (G2's structure set has exactly two elements) and added A.5r (open: is G2 rigid). After the relabel, A.5s (reading: the live G2 candidate as an open interface channel) A.5t (reading: the G2 channel goes back into O1) and A.5u (the G2 channel as a certified DMP-complete state; now Lean from the one assumption, with A.5v and II.4d) III.71 (reading: the one assumption as a leak axiom) the draft-4 abstract rows 0.21 to 0.25 the ETM translation II.0a to II.0e I.11b (IM read as Identity Multiplication), I.11c (IM as a step up the DAG) II.0f (only rotation keeps identity), II.0g and I.11d (ordinary multiplication as IM) and II.0h (the 100 declarations, a reading) were added; the first column is kept current. The committed draft counted 651 rows; the file then held 655 counted rows (the abstract rows 0.6 to 0.9 had been added after the count: 0.6 paper, 0.7 Lean, 0.8 certified, 0.9 Lean), so the table column is the count as committed and the audit column is recounted by script on this file.

Counted by script on this file (first word of the status column; "project rule" counts as paper). Mixed rows count once, under their
first mark; for example "Lean (implication); premises open" counts as Lean, so the open count understates how many rows carry an open
part. Most of the growth since draft 2 is new results of the crossover, GRH and cutting-planes rounds, not re-labelling; no draft-1 row lost a mark, and one was upgraded (DAG-like
size-width, VI.3.4, classical to Lean). In the audit one row was upgraded (V.1.5, the explicit formula for zeta, to Lean) and one downgraded (VII.3.5e, to reading).

The open statements that decide each problem, one card each:

* **Yang-Mills:** IV.5.6 (O1) with IV.5.7 to IV.5.9 and IV.9.5 to IV.9.7; III.7g restates the cutoff-uniform form in the transport form.
* **GRH:** V.0c (beyond Dirichlet L-functions), V.4.1 to V.4.8, and V.1.5b (the explicit formula and Weil's criterion beyond zeta); III.7i restates the remainder bound.
* **P vs NP:** VI.4.10 (interface hardness at width 3), VI.6.N1, VI.6.N3, VI.6.N4; III.7k restates the constant-gadget lifting step.
* **Navier-Stokes:** VII.5.1 (the route I period contraction, in the tie the Alpoge-Buckmaster certificate), VII.5.2 (the regularity slot), VII.5.3 (continuation past T*), with VII.0f; VII.7e reads Navier-Stokes as not DMP-complete, blowup the expected consequence.
* **Birch and Swinnerton-Dyer:** VIII.5.1 (`BSDStatement`, from analytic rank 2), VIII.5.2 (the ledger form), VIII.5.3 (the refined formula), and VIII.3.6d (the link of the Euler data to the curve).
* **Hodge:** IX.5.1 (codimension p >= 2), IX.5.2 (the Hodge standard conjecture over F_q, a different problem); the arithmetic Hodge index is V.2.5c.
* **GU:** X.5e (a DMP consequence beyond the standard expectation; for the gate's wording the owner takes uniform charge quantisation, X.5f) with X.7a to X.7d; X.6h.

The one assumption behind all seven is III.64 (O1, the running state, stated once in Part III 4.4), with two edges for Yang-Mills (III.64a: O1 and the lower edge IV.9.5b); it is not proved.

Lean names (draft 2): every backticked identifier in this file and in Parts II to VII was checked by script against a declaration
(`theorem`, `lemma`, `def`, ...) under `docs/mass-gap/formal/`; all resolve except `H1LocalLip` (discrepancy 5). The new modules
(`Crossover/Containment.lean`, `Neighbours.lean`, `RDoeblin.lean`, `Runs.lean`, `Saturation.lean`, `GRH/Mirror.lean`, `Tate.lean`,
`Induction.lean`, `Variational.lean`, `Transfer.lean`, `Proof/Dag.lean`, `Edge.lean`, `CPDuality.lean`, `CPPairs.lean`) are tracked and
contain no `sorry`, `admit`, `native_decide` or `axiom` declaration. Axiom logs were read in the notes, not regenerated.
The transport modules of III.7 (`Unified/Transport.lean`, `TransportBridges.lean`, `TransportInstances.lean`, `All.lean`) were
checked the same way, and their identifiers resolve; their axiom log, `docs/unified/axioms-transport.log` (70 declarations, standard
axioms only), was regenerated for this section.

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
   needs O2-O4 (IV.0). The paper states the narrower claim.
7. The notes do not yet say which Lean input form (`FineOneBox`, `FineOneBoxSplit`, `BlockGapBddW`) is exactly the one-box
   statement of `OPEN-QUESTIONS-DMP.md` 0.
8. `docs/OPEN-QUESTIONS-DMP.md` 0 still states the one-box statement as F_e(L) > 2c(L) (the chain criterion); `CONTAINMENT.md`
   sharpens it to F_e(L) > log mu_4 for a grid. The relation between the two in the cubic geometry is not written down (IV.5.8).
9. `docs/OPEN-QUESTIONS-DMP.md` G3 says "the same piece in five forms"; `grh/TRANSFER.md` 5 now counts eight faces.
10. `CONTAINMENT.md` 3 uses the per-box product structure along paths (annealed to quenched, `RATE.md` 5') as an assumption; the
    paper lists it as an open input (IV.5.7), not as part of the Lean chain.
11. `grh/TATE.md` cites `ZMod.completedLFunction_one_sub_even` / `_odd` in Mathlib. Both exist in Mathlib v4.34.0, `Mathlib/NumberTheory/LSeries/ZMod.lean`, as `completedLFunction_one_sub_even` (line 461) and `completedLFunction_one_sub_odd` (line 509) (V.2.2b; checked by the owner's coordinator, 2026-11-24).
