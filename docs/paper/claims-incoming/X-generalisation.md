# Incoming claims: Part X, the generalisation (`draft/10-part-X-generalisation.md`, draft 3, 2026-11-24)

For the coordinator to merge into `../CLAIMS.md`. Rows are in the format of `CLAIMS.md`: ID, claim, status (first word is the one primary
mark), source, upgrade. Lean paths are relative to `docs/mass-gap/formal/` unless they start with `docs/`; a path in the `im`
repository is marked. Nothing in the repository outside the three chapters and this folder was edited.

## Labels kept (content stays; rows in `CLAIMS.md` unchanged)

`X.1`, `X.2a`, `X.2b`, `X.2c`, `X.3`, `X.3b`, `X.5`, `X.7f` to `X.7o`.

Where they now sit: X.1, X.2a, X.2b, X.2c and X.5 in section 4.1 (table and the observation on II.1); X.3 and X.3b in section 6
("What the act carrier settled"); X.7f to X.7o in section 7; X.7n is also used in section 4.2. The side-by-side table (X.2a) is
unchanged except that it is now introduced as the three cards of Parts III to V; the cards of Parts VI to IX are not in it.

## Labels retired

| Label | Why |
|---|---|
| X.5b | "Yang-Mills is likely to close first" was an expectation with no source in the notes of 2026-11-24 (the owner's later entries make O1 the open step of every card, not Yang-Mills the first to close). Dropped. |
| X.7a | Moved: the transport theorem is described once, in Part II. Now II.9.1. Same Lean names. |
| X.7b | Moved to II.9.2. |
| X.7c | Moved to II.9.3. |
| X.7d | Moved to II.9.4. |
| X.7e | Moved to II.9.5. |

The old Part X sections "X.4 What would close each step, and what cannot" (a table without a claim label) and "X.6 The paper as it
will close" (no label) are now the last paragraph of section 8 and the proved-obstructions row of section 4.1. The "what cannot help"
column of the old X.4 table is not carried over: it restated the proved obstructions of Parts III to V that the X.2a table already
summarises.

## New rows

### Section 1. The container (new section, added 2026-11-24 at the owner's request)

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| X.54 | The one box is the confined inside: binary and free to assert itself; it exists only as an assertion against an outside (the inside cannot exist without an outside) | reading | `PREP.md`, 2026-11-22, "Inside and outside are one system"; 2026-11-24, last entry | none |
| X.55 | The outside must leave the possibility space free (0 < p < 1: might happen, need not; causality and the gap are one condition) and complete (every configuration has positive weight: compact group, finite action, "every possibility exists"); the two together are the container | reading | `PREP.md`, 2026-11-22, "The possibility space, binary existence, and the reflected assertion" and "Why the possibility space saturates at a definite size"; 2026-11-24, last entry | none |
| X.56 | Yang-Mills, proved halves of the container: every configuration has positive weight at fixed cross-section; Z_tw < Z for beta != 0, so p = Z_tw/(Z_tw + Z_0) < 1/2; 0 < p needs 0 < Z_tw, carried as a hypothesis (cross-reference to III.1.6, III.1.7, III.3.1, not counted twice) | (cross-reference) | `ProofPhase/Flip/Bound.lean`, `stepK_pos`; `ProofPhase/Flip/Strict.lean`, `su2_Ztw_lt_Z`; `ProofPhase/Crossover/HandOver.lean`, `su2_handover` | formalise 0 < Z_tw |
| X.57 | Yang-Mills quantifier: `HandoverSide` (every cutoff, nontrivial sector and end-face outside: electric side at most sqrt 2 - 1 of the neutral) is O1 at mu = 1 + sqrt 2 at the single length L_h; it implies `HandoverSideRunning` (running outsides only) | Lean (the equivalence and the implication); both statements themselves open | `ProofPhase/Unified/ElectricSUNPress.lean`, `HandoverSide`, `handoverSide_iff`; `ProofPhase/Unified/ElectricSUNRunning.lean`, `HandoverSideRunning`, `handoverSideRunning_of_handoverSide`, `O1_slab_running`, `O1_box_running` | a proof of `HandoverSide` or `HandoverSideRunning`, uniformly in the cutoff (O1; III.5.6) |
| X.57b | Frozen outsides are not running outsides and are not quantified over; they count as remnants, entering only through their exponentially small weight epsilon, a fresh uncertainty r = epsilon in the transport theorem | reading (identification); transport Lean | `PREP.md`, 2026-11-24, "Frozen faces aren't running outsides"; `ProofPhase/Unified/ElectricSUNRunning.lean`, `runningTransport`, `runningTransport_slab`; `docs/unified/ELECTRIC-SUN.md` 6 | a large-deviation bound on epsilon, uniform in the cutoff (open per `ElectricSUNRunning.lean`) |
| X.58 | GRH quantifier: Weil's form is positive for every test function of L2(-a, a) at the certified supports a = 0.60, 0.65, 0.69 (the universal start {infinity, 2, 3}), from enclosures computed in ball arithmetic | numerical | `docs/unified/GRH-ONEBOX-CERT.md`; `docs/unified/grh_onebox_cert.py` | certify beyond a = 0.69 (IV.4) |
| X.58b | The abstract step: a certified finite part, a cross-term bound and a tail bound give W f f >= c norm(f)^2 for every f (the enclosures are named hypotheses) | Lean | `ProofPhase/GRH/OneBoxCert.lean`, `schur_scalar`, `onebox_positive`, `onebox_cert_69_100` | none |
| X.59 | NP vs coNP quantifier: a refutation certifies that every assignment falsifies a clause; "every assignment" is the container's quantifier | reading (on Lean refutation completeness, cross-reference to I.4a, V.3.1) | `ProofPhase/Proof/Complete.lean`, `refutable_iff`; `docs/pnp/DICTIONARY.md` | none |
| X.60 | Settling machine quantifier: total freedom inside one verified gate (cross-reference to XI.1, XI.3, not counted twice) | (cross-reference) | Part XI; `PREP.md`, 2026-11-23 | none |
| X.61 | The container is also where the open step sits: O1 is exactly the requirement that the one box holds for every outside, uniformly in the scale; the container is the precondition the cards share, not a result | reading (on Lean X.57) | `PREP.md`, 2026-11-24, last entry (care point) | O1 |
| X.62 | The container asks two things of each tick: from the inside a margin is carried, from the outside the twisted sector is refuted; these are the two edges of section 2 | reading | `PREP.md`, 2026-11-24, last entry; X.15 | none |
| X.63 | The care point of the container is answered by construction: the process from G0 to the hand-over (the ODP) is one established process, and once that is accepted every start gets a direction through {infinity, 2, 3} | reading | `PREP.md`, 2026-11-24, last entry ("The owner on the care point") | none |
| X.64 | The paper's one assumption: the process from G0 to the hand-over is established, i.e. the one box is a running, DMP-complete system (the MP-type existence assumption; O1 as the corollary of running, slotted as the named hypothesis R); stated once (Part X section 4.4), not proved | open | `PREP.md`, 2026-11-24, "O1 ... must always be the open step", "DMP being O1", last entry; X.7n, X.28, X.61 | a proof of the running state for each object (O1; IV.4; V.4.10) |
| X.65 | At the start {infinity, 2, 3} the first tick is certified positive with a margin (Weil's form on supports up to a = 0.69: c = 1.5e-9, 3.4e-11, 6.4e-13 at a = 0.60, 0.65, 0.69), so the sign is fixed there | numerical (certified in ball arithmetic); abstract step Lean (X.58b) | `docs/unified/GRH-ONEBOX-CERT.md`; `ProofPhase/GRH/OneBoxCert.lean` | certify beyond a = 0.69 |
| X.66 | Under the acceptance of X.64, the sign at the start, and with it the direction of every later tick, is fixed; for every tick past the start this is conditional on X.64 and is not a theorem that the margin survives (it collapses to about 3.6e-15 at a = 0.75) | conditional (on X.64) | `PREP.md`, 2026-11-24, last entry; `docs/unified/GRH-ONEBOX-CERT.md` | X.64 |
| X.67 | Reading rule for "conditional on the established process": a result so marked holds if X.64 holds; the Lean theorems of section 2, the transport theorem (II.9) and the certified start do not use X.64 | paper (editorial rule) | Part X section 4.4 | none |

### Section 2. One geometry, two edges

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| X.8 | The per-tick distance d of an encoder from the lossless point: the electric factor is e^{-d}, the Szego factor 4 e^{-d}/(1 + e^{-d})^2 = 1/cosh^2(d/2) (cross-reference to II.10.3, not counted twice) | (cross-reference) | `ProofPhase/Unified/GRHLens.lean`, `elec_cost`, `szego_of_elec` | none |
| X.9 | GRH asks of the tick distance: finite at every tick (sign); uniformly bounded, d_N <= D (multiplicative transport, enough for the sign, not needed by it) | open | `docs/unified/GRH-TO-O1.md` 3a; `ProofPhase/GRH/Transfer.lean`, `margin_pos_of_factors` (the finite part, Lean) | GRH beyond the finite model |
| X.10 | O1 holds exactly when some mu' > mu has mu' p1 <= p0 for every outside (uniform ratio bound), and exactly when p0 - mu p1 >= delta p1 uniformly (a strict margin); the electric cost is log(p0/p1); encoder form of the one-box step | Lean | `ProofPhase/Unified/GRHToO1.lean`, `ymOneBox_iff_ratio`, `ymOneBox_iff_margin`, `cost_eq_log_ratio`; `ProofPhase/Unified/Encoder.lean`, `oneBox_iff_refl` | none (O1 itself is III.5.6) |
| X.11 | On one tick sequence with encoders at least theta > 0 from the lossless point, the carried Szego margin falls below every m > 0: a uniform margin and O1 at every tick exclude each other | Lean | `ProofPhase/Unified/GRHToO1.lean`, `o1_ticks_kill_margin`, `uniform_margin_excludes_o1` | none |
| X.12 | Multiplicative transport (a lower bound on the factors) and O1 in factor form (an upper bound below 1/mu) are independent: lossless ticks transport and fail O1; factors 2^{-n}/(2 mu) satisfy O1 and transport nothing | Lean | `ProofPhase/Unified/GRHToO1.lean`, `transport_not_decay`, `decay_not_transport` | none |
| X.13 | On the two-sector cone, bounded Birkhoff spread and O1 are independent (all ratios 1: spread 0, O1 false; ratios e^{-n}/(2 mu): O1, unbounded spread) | Lean | `ProofPhase/Unified/GRHToO1.lean`, `spread_without_o1`, `o1_without_spread` | none |
| X.14 | One tick sequence with factors in a band e^{-D} <= f <= e^{-kappa}, kappa > log mu, uniformly would give both edges; no known object has both the zero measure's Verblunsky steps and the box's sector ratios as ticks, and no known result supplies either edge | open | `docs/unified/GRH-TO-O1.md` 3a, "Named exactly" | a proof of either edge |
| X.15 | GRH prescribes the existence side, O1 the non-existence side, of the same distance (the two edges of one band) | reading | `PREP.md`, 2026-11-24, "What GRH and O1 share"; X.8 to X.14 | none |
| X.16 | For any statement H and any card with an input that fails the open step, "H implies every input meets the open step" is equivalent to "not H"; so "RH implies O1 on every input", the same for Dirichlet GRH and for the GRH card's open step, is equivalent to the statement being false | Lean | `ProofPhase/Unified/GRHToO1.lean`, `imp_all_iff_not`, `badInput`, `badInput_not_open`, `rh_imp_card_iff`, `dirichlet_imp_card_iff`, `grhCard_imp_card_iff`, `pair_model` | none |
| X.17 | In the finite model, under the card's open step the Toeplitz form at scale k is positive with margin exactly 0 (a null vector exists); no positive margin is certified at the closure | Lean | `ProofPhase/Unified/GRHToO1.lean`, `exists_null`, `toepForm_atoms_null`, `no_margin_at_closure`, `grh_margin_exactly_zero` | none |
| X.18 | Positive sector weights (encoder strictly inside the disk) with O1 false exist for every mu >= 1 | Lean | `ProofPhase/Unified/GRHToO1.lean`, `positivity_without_o1` | none |
| X.19 | `ZetaCoupling`: a bound on the sector ratio, valid for every outside and controlled by RH; the coupling and RH give O1, and O1 alone gives the coupling. Its content for 4D SU(N) is not known | Lean (definition and the two implications); content open | `ProofPhase/Unified/GRHToO1.lean`, `ZetaCoupling`, `o1_of_coupling`, `coupling_of_o1` | the coupling itself (no easier than O1) |
| X.20 | 2D SU(2) zero-area sectors: Z_{e=1} = 2^{-s} Z, Z_{e=0} = (1 - 2^{-s}) Z, Z = re zeta(s), sector domination iff mu + 1 <= 2^s, twist ratio 1 - 2^{1-s} (s = 2g - 2 > 1); zeta cancels from every sector ratio | Lean | `ProofPhase/Unified/GRHToO1.lean`, `Ze1_eq`, `Ze0_eq`, `zeta_re_eq`, `sector_dom_iff`, `twist_ratio` | none |
| X.21 | The SU(2) zero-area partition function on a closed surface of genus g >= 2 is zeta(2g - 2) | external | Witten, CMP 141 (1991); `docs/unified/GRH-TO-O1.md` 4, 7 | a re-read of the source |
| X.22 | A margin of Weil's form at scale k + 1 is one at scale k: growing the support is restriction to nested sections, not iteration | Lean | `ProofPhase/Unified/GRHToO1.lean`, `sec_restrict` | none |
| X.22b | Szego recursion steps are SU(1,1) isometries of the cone, whose image is the whole cone: Delta = infinity, Birkhoff-Hopf gives factor 1 (also at the start {infinity, 2, 3}) | classical | `docs/unified/GRH-TO-O1.md` 3a; `GRH-LENS.md` 6.5 | none |
| X.22c | Prime powers enter Weil's form additively as indefinite symmetrised translations; adding one consumes margin | classical | `docs/unified/GRH-TO-O1.md` 3a; `docs/rh-guide/grh/INDUCTION.md` 1; `ProofPhase/GRH/Transfer.lean`, `two_term_bound` (two-term bounds only add, Lean) | none |

### Section 3. Existence and falsifiability

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| X.23 | GRH asks that something exists (a margin stays at every tick); O1 asks that something is falsifiable (every twisted state is refuted at every box): the duality inherent in the construction of DMP-complete systems | reading | `PREP.md`, 2026-11-24, same entry, the owner's sharpening | none |
| X.24 | RH is a Pi-0-1 statement: one computable counterexample refutes it (Lagarias' criterion; Davis-Matiyasevich-Robinson); the notes say the same of GRH for Dirichlet L-functions | classical | `PREP.md`, 2026-11-24, same entry; references as the notes cite them, not re-read here | check the references |
| X.25 | The Yang-Mills problem asks for an existence (a continuum theory with a gap) | classical | the Clay statement; Part III.0 | none |
| X.26 | Stated whole, each problem has the logical form of the other's role in the band: the duality appears twice (roles; statements, mirrored) | reading | `PREP.md`, 2026-11-24, same entry, care point; X.23 to X.25 | none |

### Section 4. Why O1 is always the open step

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| X.27 | Each of the three cards of Parts III to V is a `Problem` with one `OpenStep` slot, proved "open step gives conclusion"; slots are hypotheses, never axioms | Lean | `ProofPhase/API.lean`, `Problem`, `Problem.holds`, `OpenStep`, `External`; `ProofPhase/API/YangMills.lean`, `API/GRH.lean`, `API/NP.lean`; `docs/unified/API.md` 2 to 4 | none |
| X.28 | The structural sense of "O1 is always the open step": every card's open step is the running-state hypothesis R, "this object runs"; the form layer proves everything else | reading | `PREP.md`, 2026-11-24, "O1 ... must always be the open step"; `ProofPhase/Unified/All.lean`, `three_bridges` (Lean, see X.7m, X.7n) | none |
| X.29 | The logical sense: a system cannot certify its own running from inside (Goedel II; the settling machine cannot decide balance for all content); "open from inside" is not "unprovable"; DMP's own running assertion is its O1 | reading (on classical Goedel II and Lean II.11.3) | `PREP.md`, 2026-11-24, "O1 ... always the open step" and "DMP being O1" | none |
| X.30 | With a floor (cost above the floor) settling is decidable within an explicit bound; at cost = floor it is undecidable for all content (cross-reference to II.11.2, II.11.3 and XI.2a, XI.2b, not counted twice) | (cross-reference) | `ProofPhase/ETM/Machine.lean`, `reaches_of_contracting`, `balanceBound_ge`, `contracting_iff_costAboveFloor`, `etm_balance_undecidable`, `etm_edge` | none |
| X.31 | At G0 a gap and an arrow must be established: the gap makes each tick's answer binary (passes, or outside); the arrow orders the ticks, so a later excision is a later tick, never a revision | reading (on Lean II.11.2, II.11.3) | `PREP.md`, 2026-11-24, "The residue is why G0 must establish a gap and an arrow" | O1 (the floor in the continuum) |
| X.32 | The floor is at least the existence tied to the error bars; with the floor as hypothesis, a run settles to within the error bar in an explicit number of steps | reading (identification); Lean for the implication | `PREP.md`, 2026-11-24, "The floor is always at least ..."; `ProofPhase/ETM/Machine.lean`, `reaches_of_contracting` | none |
| X.33 | Keeping the floor positive as the error bar goes to zero (the continuum limit) is O1 | open | `docs/unified/GRH-TO-O1.md` 3; III.5.6 | a worst-case argument for one box |
| X.34 | It would be circular to justify O1 by "the floor is at least the error bar" and then the error bar by O1's rate; the settle theorem takes the floor as a hypothesis, which keeps it honest | paper | `docs/unified/GRH-TO-O1.md` 6 | none |

### Section 5. Excision and incompleteness

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| X.35 | `R136a1 "name" P` is `P` as a named hypothesis, never an axiom; a part answered R136a1 stays a hypothesis of the theorems that name it (cross-reference to II.13.2, not counted twice) | (cross-reference) | `im` repository, `arsenal/Arsenal/R136a1.lean`, `R136a1`, `R136a1.out` | none |
| X.36 | Goedel's theorems apply to a whole consistent, effectively axiomatised theory containing arithmetic; Presburger arithmetic and Tarski's real closed fields are complete decidable fragments | classical | Goedel 1931; Presburger 1929; Tarski; `PREP.md`, 2026-11-24, "Point 3 is how DMP passes the incompleteness argument" | none |
| X.37 | DMP's excision is decision per tick, with R136a1 as the answer for "outside"; at tick n everything not yet decided is outside | reading (on Lean II.11.2, II.11.3; classical for "provable within n steps" being decidable) | `PREP.md`, 2026-11-24, same entry | none |
| X.38 | "Outside at tick n" can become "inside at a later tick": a new act, never a revision of the earlier tick; the set of all sentences ever decided is not decidable in general | reading | `PREP.md`, 2026-11-24, same entry, care point 1 | none |
| X.39 | The Clay statements, being arithmetic and analysis, cannot be excised as a class: an independent one would be answered R136a1, "outside", which is not settling; the owner: the assertion states that an O1 of that behaviour exists and lints everything that cannot survive it | reading | `PREP.md`, 2026-11-24, same entry, care point 2 and the owner's answer | none |
| X.40 | `sorry` (reported as `sorryAx`) and R136a1 (a named hypothesis the lint lists) are independent channels; a result passing both is certified twice, for form only | reading (mechanisms: Lean, X.35, and the pin and lint scripts, paper) | `PREP.md`, 2026-11-24, same entry; `INDEPENDENT-CHECK.md` | none |
| X.41 | A missing expected tick is an answer too: the part is outside (the time-to-live of every act; the cutoff of the settling machine) | reading | `PREP.md`, 2026-11-24, same entry, the owner's answer to point 1; Outlook | none |
| X.42 | The finite loss excised at the beginning is the floor at the error bars: a fixed finite cost paid once; every act is then constructible inside or R136a1 | reading | `PREP.md`, 2026-11-24, same entry, the owner's answer to point 3 | none |
| X.43 | Nothing in this construction makes a theory with arithmetic complete; the completeness is that of the generalisation over what is inside at each tick | classical (for the incompleteness side) | `PREP.md`, 2026-11-24, same entry, care point 3; X.36 | none |

### Section 6. The tick operator

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| X.44 | Reaching composes: from a certified start every finite scale is reached by finitely many ticks; composed paying steps form a ledger | Lean | `ProofPhase/Unified/Encoder.lean`, `pays_of_factors`; `ProofPhase/Unified/Ledger.lean`, `carry`; `ProofPhase/ETM/RunSys.lean`, `RunSys.carry`, `RunSys.contract` | none |
| X.45 | A uniform lower bound on the tick factors keeps the carried margin positive at every finite scale, decaying at most exponentially | Lean | `ProofPhase/Unified/Ledger.lean`, `survive`, `survive_pos`; `ProofPhase/GRH/Transfer.lean`, `margin_pos_of_factors` | none |
| X.45b | A uniform margin (infimum above zero over all scales) is false for zeta's zero measure: the zero side is purely atomic, the product of Szego factors is exp(integral of log w) = 0 | classical | Szego-Kolmogorov-Krein; `docs/unified/GRH-TO-O1.md` 3a; `INDUCTION.md` 1 | none |
| X.46 | The continuum needs a uniform bound on the tick factors; which bound (lower edge for GRH, upper edge for O1) is the open step of each card | open | X.9, X.10; `PREP.md`, 2026-11-24, "Base existence as SU(p + (p+1))", the owner's refinement | the bounds of X.14 |
| X.47 | The tick operator is an act at a DB, rotating; the encoder's half-turn is its rotation | reading | `PREP.md`, 2026-11-24, "The multiplicative transport is the tick operator" | none |
| X.48 | A positive map whose image cone has finite Hilbert projective diameter Delta contracts the projective distance by tanh(Delta/4) | classical | Birkhoff 1957; Hopf 1963 (recalled, not re-read) | none |
| X.49 | Yang-Mills slab chain: the single-layer floor e^{-2s} gives abs(Z_{e=1}) <= tanh(s)^{n+1} Z_{e=0} for every end-face outside (SU(2) Wilson: s = beta N), with no join loss | Lean | `ProofPhase/Unified/JoinLossSlab.lean`, `kchain_tanh`, `kchain_elec`, `elec_exp_neg_two_mul` | none |
| X.49b | The cutoff-uniform form of the slab bound (a cost above the floor at fixed physical length, uniform as the lattice spacing goes to zero) | open | `PREP.md`, 2026-11-24, same entry; `docs/unified/TRANSPORT.md` 3.1; III.5.6 | O1 |
| X.50 | The root chain pins by hash: a `PIN` records the sha256 of the pinned copy of DMP, and the pin check fails on any change; the circle between DMP and Gravity closes through time (each side pins an earlier commit of the other) | paper (Gravity's side read from the script; DMP's side stated by the notes, not re-read) | `tools/check-pin.sh`; `vendor/dmp/PIN`; `PREP.md`, 2026-11-24, "DMP as a recipe" | read DMP's check |
| X.51 | A file containing its own hash, or two files containing each other's current hashes, is a fixed point of sha256, which no one can compute; the hash itself is one-way | classical | design of the hash; `PREP.md`, 2026-11-24, "DMP as a recipe", "Rotatable, not negatable" | none |
| X.52 | "Rotatable hash": across versions the pin passes from one node to the other, one turn per tick, the same half-turn shape as the encoder's; no hash function is rotated, the roles of pinner and pinned are | reading | `PREP.md`, 2026-11-24, "Rotatable, not negatable" | none |
| X.53 | Inside the system the time-to-live of a certification is not a separate mechanism: every certification is re-made at each tick against the same shared root, so any hash's validity window is bounded by the interval between two ticks; what leaves the inside is the boundary's matter | reading | `PREP.md`, 2026-11-24, "Correction: the post-quantum world is the inside of CMOS" | none |

## Counts for this file

Counted by script on the rows above (first word of the status column); see the report for the figures.

## Notes for the coordinator

1. **Cross-reference rows** X.8 and X.30 repeat statements whose home is now Part II (II.10.3; II.11.2 and II.11.3, which are the
   same statements as XI.2a and XI.2b). Count them once, in Part II (as with V.6.N2).
2. **Looser wording in the notes.** `PREP.md` says the margin carried by ticks "keeps a floor in the limit only if the factors are
   bounded uniformly". Strictly, a uniform lower bound q < 1 on the factors gives a margin of at least c_0 q^n: positive at every
   finite scale, but not bounded below in the limit. The paper states exactly that (X.45, X.45b) and leaves "which bound" as the open
   step (X.46).
3. **Not in the draft, by choice.** The Parts VI to IX cards are not described: their writers own them. Section 4.1 says so.
4. **The `Unified/GRHToO1.lean` module is new and uncommitted** (verified by the coordinator, per the brief). X.10 to X.22 cite it.
   If the coordinator's check changes any name, X.10 to X.20 and X.22 are the rows to adjust.
5. **The one assumption (X.64) and the abstract.** The owner's framing (via the coordinator) asks that the paper state the acceptance
   once, as its one assumption, and mark every result that uses it as conditional on it. Part X section 4.4 does that and refers to it
   from the container (section 1). The abstract and introduction are not mine to edit; the coordinator's reading is that they should
   say "conditional on the established process (O1)" until the assumption is proved. In Part X the results that use X.64 are X.66 and
   the statement in section 6 that every tick past the start pays (marked conditional in the text, no separate row). The margin
   numbers of X.65 also appear in section 6; they are one claim (X.65), not two.
