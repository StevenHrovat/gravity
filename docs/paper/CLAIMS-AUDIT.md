# Audit of the claims ledger (draft 3)

Proposal only. Nothing in `CLAIMS.md` or `draft/` was changed. Written 2026-11-24 for the coordinator, who verifies and applies it.
Ledger audited: `docs/paper/CLAIMS.md`, 673 table rows (the file's own count table says 651, see 1.2). Lean and IM trees read: `docs/mass-gap/formal/` (356 `.lean` files) and `C:\claude\im\{arsenal,proof}` (14 files).

**How to read the evidence column.** `[V]` = the auditor read the declaration, chapter line or log named. `[S]` = reported by a haiku sweep of the chapter against the ledger (line numbers as reported, not re-read). The two haiku jobs were: (a) each ledger row against its chapter, (b) each Lean row against the signatures it cites. Job (b) over-flagged (of the flags I re-read, roughly half held up: it saw truncated signatures and missed structure fields). Every flag that appears below as `[V]` was re-checked; unverified flags are not used. The raw sweep and flag files are in the shared notes folder, `audit-working/` (sweep_*.md, leancheck_*.md).

## 1. Summary

### 1.1 Actions

Every row has one action. Rows not listed in section 2 are `keep`.

| Action | Rows |
|---|---|
| keep | 509 |
| fix | 77 |
| combine | 78 |
| upgrade | 3 |
| drop | 5 |
| resolve | 1 |
| **Total** | **673** |

`combine` and `drop` rows leave the ledger (83 rows); the row they fold into stays. `upgrade` here includes one downgrade (VI.3.5e).

### 1.2 Ledger counts by status, before and after

"Before" is recounted on the rows of the file (first word of the status column, as the ledger's own script does; scope and cross-reference rows not counted: 18). "After" applies every proposal in section 2 and adds the 10 new rows of section 3.1; it counts II.11.2 and II.11.3 as Lean (they become the home of the settle theorem), drops the cross-reference rows that are deleted, and keeps 7 scope rows (0.1, III.0, VI.0e, VII.0e, VIII.0d, IX.0a, IX.0d) outside the count.

| Status | File says (draft 3) | Recounted before | After |
|---|---|---|---|
| Lean | 239 | 241 | 212 |
| classical | 120 | 120 | 115 |
| external | 48 | 48 | 40 |
| conditional | 4 | 4 | 4 |
| paper | 63 | 64 | 56 |
| numerical | 24 | 24 | 22 |
| certified | (not in table) | 1 | 2 |
| reading | 83 | 83 | 82 |
| open | 70 | 70 | 60 |
| **Total** | **651** | **655** | **593** |

The difference between the file's 651 and the recount is exactly the four abstract rows 0.6 to 0.9 (0.6 paper, 0.7 Lean, 0.8 certified, 0.9 Lean), which were added after the count table was made. [V]

### 1.3 Conventions the proposal assumes

* **C1. One home per claim.** Part II ("the tools") is the home of any statement that a card re-uses with the same declaration; the cards (Parts III to V) point to it. Part X is the home of the card API (X.27) and of what the three bridges say; Part XI (outlook) points to Part II for the settle theorem. This reverses the present counting of the settle theorem (XI.2a, XI.2b counted, II.11.2, II.11.3 cross-references), which disagrees with the writers' notes for Parts I-II and X ("count them once, in Part II").
* **C2. "Lean (from X)" in the ledger.** The chapters already write "[Lean, from BSD]", "[Lean, from Hodge-Riemann]" and similar (sweeps: 20 rows in Part VII, 5 in Part VIII, e.g. VII.3.5b to VII.3.5d, VIII.3.2b, VIII.3.4c, VIII.3.6c, VIII.3.6d, VIII.3.7b); the ledger says bare Lean. The Lean theorems are proved, the hypotheses are `External`/`OpenStep`/`R136a1` slots. Use the chapter's form in the ledger, with the same first word, so the counts do not change.
* **C3. Add `certified` to the ledger legend.** The abstract defines `[certified]` (enclosed in ball arithmetic, with its log); the ledger legend lacks it and uses it once (0.8) while X.58 and X.65 say `numerical`. Use `certified` for X.58 and X.65; row 0.8 folds into X.58.
* **C4. Rows that cite files and no declaration** (Lean status with no resolvable name): 0.2, II.1.2, II.12.1, III.1.1, III.1.3, III.2.8, V.3.8, V.5.2, VII.3.3c (found by script; each has a proposal in section 2). Every other Lean row names were matched by script to a declaration; the only unmatched tokens are Mathlib names (`finite_torsion`), structure fields (`CurveClassInput.hl_hodge`, `CurveInput.geometry`) and file words.

### 1.4 The five most important findings

1. **"Neither implies the other" is over-claimed (0.9, abstract L74-76, Part X L146).** Lean proves independence of two bounds on tick sequences. For the statements themselves, "O1 implies GRH" is trivially true for Dirichlet GRH (proved by others) and unknown for general GRH, and X.16/X.17 do not give what Part X L146 cites them for. Reword as a model statement.
2. **The explicit formula for zeta is a Lean theorem now, and the ledger says the opposite.** `CS.contourShift` and `explicit_formula_of_smooth` (log: 122 declarations, standard axioms) make IV.1.5 ("Mathlib has neither", paper) out of date; the abstract states the Lean result three times and no row carries it. Upgrade IV.1.5, add rows 0.10, IV.1.5b, IV.1.11.
3. **Abstract claims with no row and one dead cross-reference.** "Re-checked by independent kernels (Part II)": Part II never mentions it, and 29 of 356 Lean files were modified after the independent check's last log line (all the new GRH, BSD, Hodge, NS, API modules). Also no row for the equivalence `liftCPConst_iff_extract` (abstract L64-65), and the "strict twist bound for every SU(N)" has Lean (`sunZtw_lt`) that III.1.6 does not cite (row says SU(2) only).
4. **78 rows fold into other rows, 5 are dropped.** The biggest clusters: the settle theorem (6 rows: 0.7, II.11.2, II.11.3, X.30, XI.2a, XI.2b), "nothing is an axiom" (II.12.1, VII.2c, VIII.2c), the dichotomy tools stated in Part II and again in Parts III and V with the same declarations (II.6.2 to II.6.6 vs III.3.2, III.3.8, V.3.6, V.3.7, V.4.3), and the BSD section VII.5 which restates VII.1.1 and VII.3 five times. Dropped (no chapter states them): III.6.10, V.1.10, V.3.12, IX.3.2f, and VII.1.1k (context only, unreferenced).
5. **Three Lean rows say more than the Lean.** VI.3.5e (`boundary_quantum` is an arithmetic identity, the Beale-Kato-Majda count is not in Lean: reading), III.4.3a (0.134 is Lean, "about 0.22" needs the recalled percolation threshold 0.197), III.3.4 (superadditivity is an inequality, the "iff" is not proved). Also VII.3.8b: the `#eval`/`#guard` ranges to 37 and 59 are build-time computations, not kernel proofs; only the general `count_E32` and `hasse_E32_five` are.

Other notable: VII.3.0/VII.7.1 are half-resolved (axiom log of the adapted `BSDAPI` regenerated 2026-11-24 04:50); X.58b cites one of three certified Lean instances; the count table is stale by four rows.

## 2. Rows that change, by part

Action key: **fix** wording, source, status or home; **combine** fold into the named row (the row leaves); **upgrade** stronger (or weaker, for VI.3.5e) status justified; **drop** no chapter states it; **resolve** newer result settles it.

### Abstract and introduction (Part 0) (9 rows, 7 change)

| ID | Action | Evidence | Proposed new text or status |
|---|---|---|---|
| 0.6 | combine | Same claim as X.64 (the one assumption, stated once in Part X 4.4) plus the reading rule X.67. Keep X.64 (open) and X.67 (editorial rule). The abstract row can say "see X.64, X.67". [V] |  |
| 0.7 | combine | Restates II.11.2 (settle bound) and II.11.3 (undecidable edge), same declarations (`reaches_of_contracting`, `balanceBound_ge`, `etm_balance_undecidable`). Also fix wording: "without one, undecidable" is not what `etm_balance_undecidable` says. It says no computable predicate decides `etm.Reaches` over all codes, for the one lossless machine `etm`, for `0 <= eps < 1`. Proposed text: "at cost = floor there is a running system (the lossless machine that runs every partial recursive content) whose settling is undecidable". [V: `Machine.lean:274`] | At cost above the floor settling is decidable within an explicit bound (II.11.2); at cost = floor the universal lossless machine has undecidable settling (II.11.3). |
| 0.8 | combine | Same claim as X.58 (Weil form positive on the first box, certified supports a = 0.60, 0.65, 0.69), whose status is "numerical", while 0.8 says "certified" and X.65 says "numerical (certified in ball arithmetic)". Keep X.58, relabel it `certified` (convention C3, section 1.3), and make 0.8 a pointer. |  |
| 0.9 | fix | Overclaims. Lean proves, on tick sequences and on a two-sector cone, that a uniform margin and O1 at every tick exclude each other (X.11) and that the two bounds are independent (X.12, X.13). It does not prove "neither implies the other" for the statements GRH and O1: for a statement already proved (Dirichlet GRH, by others, 0.3) "O1 implies GRH" is trivially true, and for general GRH it is unknown (X.14 says no known object carries both edges). The same sentence is in the abstract (L74-76) and in Part X L146 ("GRH does not imply O1, and O1 does not imply GRH (claims X.16, X.17)"): X.16 gives only the card-form equivalence "H implies every input meets the open step iff not H", X.17 is the finite-model margin. [V: `GRHToO1.lean:446-470`; Part X L118-160] | In the model of tick sequences, GRH-type margin carrying and O1-type refutation are independent bounds of one distance: a uniform margin excludes O1 at every tick (X.11) and each holds without the other (X.12, X.13). This is a statement about the model, not about the implication between GRH and O1. (status: Lean, model) |
| 0.2 | combine | Summary row, cites no declaration ("III.3 to III.5"). Fold into III.3.6 (Lean) and III.5.6 (the one number, open); the Lean+classical status mixes both. [V] |  |
| 0.3 | combine | Same statement as IV.0a (RH and Dirichlet GRH proved in Lean by others), same sources (`SOURCES.md` S1-S4, `GUIDE.md`). Keep IV.0a. [V] Chapter drops the release and certification dates (abstract L82-84). [S] |  |
| 0.4 | combine | Same statement as IV.0c (GRH beyond Dirichlet open). Keep IV.0c. [V] |  |

### Part I (33 rows, 12 change)

| ID | Action | Evidence | Proposed new text or status |
|---|---|---|---|
| I.1 | fix | Row says Z > 0 in all three problems; chapter (L49-51) gives GRH as a non-negative pairing. Say: Z > 0 for YM and SAT, the Weil pairing is non-negative for GRH. [S] |  |
| I.1a | fix | Chapter L51 states "SAT iff #SAT > 0" with no mark; row says classical. Add the mark in the chapter. [S] |  |
| I.4a | combine | Same declaration as V.3.1 (`refutable_iff`, `Proof/Complete.lean`). The excision wording is a reading (X.59 already carries it). Fold into V.3.1; keep the "excised leaves a refutation" sentence as part of X.59. [V] |  |
| I.4b | fix | Lean pointers V.3.6, III.3.2 are rows that are themselves duplicates of II.6.2 and II.6.3 (see V.3.6, III.3.2). Point to II.6.2 (`gauss`, `unsat_of_odd`) and II.6.3. Chapter cites `Proof/Crossing.lean` and `Crossover/FluxRate.lean` (L124). [S] |  |
| I.6a | combine | Same declarations as II.7.1 (`fixed_after`, `real_never_arrives`/`reaches_floor`) and V.5.1. Keep II.7.1. [V] |  |
| I.6b | fix | Two statuses in one row (Lean abstract kernel + paper lattice instantiation). The Lean half is II.4.2 (`contracts_of_doeblin`); fold it there and keep only "A finite box has a Doeblin rate for every outside: paper (lattice instantiation)". [V] | A finite Wilson box has a Doeblin floor for every outside (paper; the abstract implication is II.4.2). |
| I.8c | fix | Wording: row "open parts only as named R136a1 hypotheses", chapter L233-234 "an open part only as a named R136a1 hypothesis". [S] |  |
| I.8f | fix | Row has "(the MP-type existence assumption)"; chapter L243-246 omits it. Align. [S] |  |
| I.9b | combine | Cross-reference to II.13.2 (`R136a1`, `R136a1.out`), same declarations, same wording. Chapter L268 marks it [Lean]. Delete the row, cite II.13.2 in Part I. [V] |  |
| I.10c | fix | Row: "every sentence keeps the decidable laws"; chapter L292-293: "keeps every law". Proved: `Im.closure` : every `s.shape.lawfulB = true`, `space_size = 72` by `decide +kernel` (`im/proof/Im/Closure.lean:27-34`). Align the wording to "lawfulB". [V] |  |
| I.10g | fix | Chapter L283-284 marks [classical] without the Gross-Wilczek / Politzer attribution the row has. [S] |  |
| I.11a | combine | Same claim as II.13.1 plus II.13.4 (the arsenal is the one place for Mathlib-needing transferable results; used from `im` as a dependency, never vendored). Keep II.13.1 and II.13.4. [V] |  |

### Part II (60 rows, 17 change)

| ID | Action | Evidence | Proposed new text or status |
|---|---|---|---|
| II.0 | fix | Status "classical; finite forms Lean" but no declaration cited. Name them: `T_symm`, `T_pos` (II.1.1), `weil_criterion_finite` (II.1.3), `spectral_gap_iff` (II.2.1). Chapter L20 carries no mark. [V, S] |  |
| II.1.2 | fix | Cites three files and no declaration. Take the names from III.1.2 (`wilson_rp`, `wilson_rp_SU2`) and fold III.1.2 into this row. [V] | Reflection positivity of the Wilson action, site and link. `Positivity/Wilson.lean` (`wilson_rp`), `Positivity/LinkWilson.lean`, `Positivity/Concrete.lean` (`wilson_rp_SU2`). |
| II.1.4 | fix | Upgrade column is stale: "Lean with the explicit formula (IV.1.5)". The explicit formula for zeta is now a Lean theorem (see IV.1.5), so the remaining gap is the proof of Weil's criterion itself and the extension to Dirichlet L-functions. Also absorbs IV.1.4 (same statement). Chapter L44-45 states only the zeta case. [V, S] | upgrade: Weil's criterion in Lean (the explicit formula for zeta is available; Dirichlet L-functions are not) |
| II.2.2 | fix | Status should name the hypothesis: `gap_of_RP` takes the splitting bound `hsplit : Q(F - f k) <= bB k + 2 bA k` with `bA`, `bB -> 0` (Lemma UV-TV) as hypotheses. "Lean (hypothesis: UV-TV block bounds)". [V: `M1/UVTVOS.lean`, as read from the digest] |  |
| II.3.5 | combine | Both halves are duplicates: the function-field half is IV.2.5a (Weil 1948, `BRIDGE.md` 2.3), the open half is IV.2.5c (arithmetic positivity / arithmetic Hodge index). Fold into IV.2.5a and IV.2.5c. [V] |  |
| II.4.3b | combine | Same declaration as III.2.1 (`theoremA_w`). III.2.1 carries the hypotheses (`GDSw`, `LocalConvergenceW`, `LimitFlatW`). Fold into III.2.1; the chapter (L124-125) has no label for it anyway. [V, S] |  |
| II.4.5r | fix | Chapter has the claim but no label. [S] |  |
| II.5.2 | fix | Absorb III.4.1 (same `handover_column_sum_iff`) and the `path_entropy_beats_handover` clause of III.5.4a. Chapter L163 states the chain half without a mark, the [Lean] at L165 covers only the path-entropy half. [V, S] |  |
| II.6.5 | fix | Chapter L190-192 drops "two graph hypotheses stated" from the Lean mark. Absorb V.3.7 and V.4.3 (same `cross_any_system`). The theorem is for an abstract system with at most two premises per rule; V.4.3 adds no CP-specific declaration. [V, S] |  |
| II.7.3 | fix | Row says "linear in building blocks"; chapter L216-218 says only "finite, bounded by the size of the finite building blocks". Weaker in the chapter; drop "linear" or add its source. [S] |  |
| II.8 | fix | Chapter L228-229 gives no status mark; row says paper (observation). [S] |  |
| II.10.2 | fix | "both lie in [0, 1]" holds for the Szego factor (`szego_mem`, every encoder). For the electric factor `elec_mem` needs `0 < c < 1` and gives the open interval. Say so. [V: `Encoder.lean:163-195`] | The Szego factor lies in [0, 1] for every encoder; the electric factor (1 - c)/(1 + c) lies in (0, 1) for 0 < c < 1 ... |
| II.10.6 | fix | Chapter L318-321: the [paper] mark sits on the NP sentence only; YM and GRH sentences are unmarked. [S] |  |
| II.11.2 | fix | Home of the settle theorem. Change status from "(cross-reference)" to Lean and count it here; XI.2a, 0.7 and X.30 become pointers. Declarations checked: `reaches_of_contracting` (`ETM/Machine.lean:138`, for every n >= `balanceBound M eps q`, any rational q with e^delta theta <= q < 1), `balanceBound_ge` (121). [V] | status: Lean (home; was cross-reference) |
| II.11.3 | fix | Home of the edge. Change status from "(cross-reference)" to Lean and count it here; XI.2b, 0.7 and X.30 become pointers. `etm_balance_undecidable` (`Machine.lean:274`): no computable predicate decides `etm.Reaches eps (start c n)` over all codes c, for `0 <= eps < 1`. [V] | status: Lean (home; was cross-reference) |
| II.12.1 | fix | Cites a file, no declaration. Name `Problem`, `Problem.holds`, `OpenStep`, `External` (all in `ProofPhase/API.lean`, cited by X.27). Absorb VII.2c and VIII.2c ("nothing in the card is an axiom"), the same sentence three times. [V] |  |
| II.12.2b | combine | Cross-reference to X.27. Chapter has no X.27 reference (L383-386). Delete the row; X.27 is the home. [S] |  |

### Part III (77 rows, 18 change)

| ID | Action | Evidence | Proposed new text or status |
|---|---|---|---|
| III.1.1 | fix | Lean row with no declaration: `AreaLaw/ConcreteSUn.lean`, `OneScale/`. Needs the declaration names from the writer. [V: auditor script] |  |
| III.1.2 | combine | Same statement as II.1.2 (RP of the Wilson action, site and link), same declarations. Keep II.1.2, which takes the names. [V] |  |
| III.1.3 | fix | Lean row with no declaration (`LayerKernel.lean`, `LayerSector.lean`; both exist in `Attempts/R4/`). Name the declarations; "identity definitional" is not a theorem. [V] |  |
| III.1.6 | upgrade | SU(N) is now in Lean. `ProofPhase/General/SUNTwistWilson.lean`: `sunZtw_lt` (for every N, beta != 0, every k != 0 in Z/N, every L >= 1, every even T, every background twist P, every plane c: `Z_tw,k < Z`), `sunTwistRatio_mem` (0 < ratio < 1), `sunZtw_pos` (0 < Z_tw,k, every beta); axiom log `docs/unified/sunprimes-axioms.log` lines 152-153, standard axioms; instances `su3_Ztw_lt`, `su5_Ztw_lt`, `su11_Ztw_lt` in `SUNTwistInstances.lean`. The abstract (L58-59) already says "for every SU(N)" but the row names `su2_Ztw_lt_Z` only. SU(2) is the case N = 2 (`su2N_Ztw_lt`). Also X.56 should cite these. [V: read the statement] | Z_tw,k < Z and 0 < Z_tw,k for beta != 0, every SU(N), every nontrivial centre element, every even time extent and background (`General/SUNTwistWilson.lean`, `sunZtw_lt`, `sunTwistRatio_mem`, `sunZtw_pos`); SU(2): `su2_Ztw_lt_Z`. |
| III.2.5 | fix | Status should name the hypotheses. `yang_mills_assembly_torus` needs `OnLCP T`, `NonTrivial T`, `BlockedTorusRoute T` and gives `MassGapLoc` and `MassGapMFLoc` (local-observable forms); `bothOrders_of_torusDecay` (`Existence/Bridge.lean:301`) needs `Tendsto T.a atTop (nhds 0)` and `TorusDecay T.toV` and gives `MassGap T` and `MassGapMF`. "Lean (hypotheses: OnLCP, NonTrivial, BlockedTorusRoute; TorusDecay)". [V: `Torus/Top.lean:53-54`] |  |
| III.2.6 | fix | Source cites `not_trivial`, which is the case beta_k = 0 only. Bounded couplings is `not_onLCP_of_bounded` (`Assembly.lean:492`, `\|beta_k\| <= B` gives `not OnLCP`). Add it. [V] |  |
| III.2.7 | fix | Status "paper (spectral bridge Lean)" cites two files and no theorem. Name `spectral_gap_iff` / `gap_of_RP_spectral`. [V: names in II.2.1, II.2.2] |  |
| III.2.8 | fix | Status "Lean / paper" and the upgrade column says "split Lean/paper parts": do it. One row Lean (`OneScale/SingleLink.lean` declaration names needed), one row paper. [V] |  |
| III.3.2 | combine | Same statement and declarations as II.6.3 (`exists_sheet_of_flux`, `even_card_fluxCells`). Keep II.6.3. Note: `even_card_fluxCells` needs every plaquette in an even number of cells (`hev`), which the claim should say. [V] |  |
| III.3.4 | fix | Row says "rate multiplies iff F_e(L) > 2c(L)". Lean (`flux_superadd`, `flux_superadd_iter`) gives the inequality direction only: superadditivity up to excess terms. Say "if". [V: `CompositeHTF.lean:91-110`] |  |
| III.3.8 | combine | Same statement and declaration as II.6.4 (`measure_uncontained`). Keep II.6.4. [V] |  |
| III.4.1 | combine | Same `handover_column_sum_iff` as II.5.2 (hand-over covers at most two channels). `column_requirement` moves to II.5.2. [V] |  |
| III.4.3a | fix | The row mixes two forms. Lean (`floor_column_requirement`, general k, `C < log(k/(k-1))`): for 2d = 8 channels C < log(8/7) = 0.134. The figure "about 0.22" is `-log(1 - p_c)` with the site-percolation threshold p_c(Z^4) = 0.197, a recalled classical number that no declaration contains (`floor_disagreement_requirement` is `1 - e^{-C} < p iff C < -log(1-p)` for any p). Split: Lean for the two requirement lemmas; the 0.22 as classical (recalled). [V: `RDoeblin.lean:20-28, 68-90`; RDOEBLIN.md 78-81] |  |
| III.5.4a | fix | Drop `path_entropy_beats_handover` from this row (home: II.5.2, where it states the d >= 3 loss to the 0.881 hand-over). Keep `path_sum_summable_iff`, `tube_threshold`. [V: `1 <= mu (sqrt 2 - 1)` is the same 0.881, e^{-0.881} = sqrt 2 - 1] |  |
| III.5.9 | fix | Chapter L213-215 has no [open] mark and does not say which Lean input form is O1. [S] |  |
| III.6.7 | fix | Lean half is `window_gap`, the same as II.6.6. Keep II.6.6 for the Lean disjointness; III.6.7 becomes "the numbers 0.18 and 1.79 nats per plaquette: paper". [V] |  |
| III.6.10 | drop | The coarse test (`COARSE-TEST.md`) is in no chapter: search of `draft/*.md` for "coarse", "isolated", "spanning", "near-cut" finds nothing for it. Nothing else cites III.6.10. Drop, or add a sentence to Part III 6. [V: grep] |  |
| III.7.3 | combine | Same rule as I.6c (error bars max(statistical floor, 1/T), project rule, `attempts/RULES.md`). Keep I.6c; chapter L293 drops the [paper] mark. [V, S] |  |

### Part IV (58 rows, 9 change)

| ID | Action | Evidence | Proposed new text or status |
|---|---|---|---|
| IV.1.1 | combine | Same declaration as II.1.3 (`weil_criterion_finite`). Keep II.1.3. [V] |  |
| IV.1.3 | fix | Lean statement needs finite multiplicities (`hfin : forall z, {j \| gamma j = z}.Finite`) besides the approximation property; the status names only the latter. [V: digest signature] |  |
| IV.1.4 | combine | Same statement as II.1.4 (Weil 1952; Bombieri 2000). Keep II.1.4. [V] |  |
| IV.1.5 | upgrade | Out of date, and contradicted by the abstract (L61, L115, L144: "the explicit formula for all nontrivial zeros of zeta, by the contour shift, in Lean"). Lean: `ProofPhase/GRH/ContourShift.lean` `CS.contourShift` (line 442; for c > 1, g smooth with compact support, for every `ZeroFamily`: the zero sum converges absolutely and the two line integrals differ by the residues); `ContourShiftTie.lean` `explicit_formula_smooth` (143), `explicit_formula_of_smooth` (155), `zeta_tie_in_smooth` (164); the zero count `zero_count_ball` (383), `zero_count_window` (612: at most `B (1 + abs y)^2` zeros per unit window, weaker than the classical O(T log T) count). Axiom log `docs/unified/contourshift-axioms.log`: 122 declarations, standard axioms, imports of the core are Mathlib only (lines 111, 119, 120). Notes: `docs/unified/CONTOUR-SHIFT.md`, `EXPLICIT-FORMULA.md`. Still not in Lean: Dirichlet and real L-functions, test functions of class C^2 only, and Weil's criterion itself (II.1.4). Chapter L33 still says "Mathlib has neither". [V: read the three statements, the log lines] | IV.1.5 (Lean): Weil's explicit formula for zeta holds for every smooth compactly supported test function (`CSTie.explicit_formula_of_smooth`), with a polynomial zero count per unit window (`zero_count_window`). IV.1.5b (open): the same for Dirichlet and other L-functions. |
| IV.2.2a | fix | Wording. The Lean statement is `norm(1 - x^(-s)) = norm(1 - x^(s-1))` at s = 1/2 + it: the local factors at s and at 1 - s have the same modulus, so their ratio is a pure phase (docstring: "a phase on the critical line"). The row says "local factors are pure phases", which is not what is proved. [V: `GRH/Tate.lean:47-50`] | The ratio of the local factor at s and at 1 - s has modulus 1 on the line (unramified primes). |
| IV.2.6 | fix | Chapter table L87 says "[numerical] + [Lean] (via IV.2.1)", chapter prose L72-73 only [numerical], row "numerical (with IV.2.1)". Make the three agree. [S] |  |
| IV.3.6a | fix | Chapter table L160 merges IV.3.6a (numerical + classical) and IV.3.6b (Lean) into one row marked [numerical] + [Lean]; the prose matches the ledger. Split the table row. [S] |  |
| IV.3.6b | fix | Absorb X.45 (same `margin_pos_of_factors`; add `survive`, `survive_pos` from `Unified/Ledger.lean:129-141`, which give `M n >= (prod f) M 0` and `exp(-sum c) M 0 > 0`). [V] |  |
| IV.5.4 | fix | Chapter L180 marks the claim [open]; row says classical (recalled). [S] |  |

### Part V (49 rows, 15 change)

| ID | Action | Evidence | Proposed new text or status |
|---|---|---|---|
| V.1.2 | combine | Both parts are II.4.3 (`spectral_gap_dobrushin`) and II.1.5 (`timeCorr_spectral`); `exists_spectral_measure` goes to II.1.5. [V] |  |
| V.1.3 | combine | Same declaration as II.2.1 (`time_gap_iff`). Chapter L31 states "no spectral mass above e^{-m}", the row "spectral support": check the wording against `TimeGap.lean`. [V, S] |  |
| V.1.4 | combine | Declarations are II.4.2 (`contracts_of_doeblin`, `doeblin_sharp`) and II.4.1 (`contracts_kpow`); `box_bound` moves to II.4.2. [V] |  |
| V.1.8 | fix | Status "classical (assembled; mixing step Lean)" cites no declaration for the Lean step. Name `tv_sweep_dobrushin` / `mixing_sweep_dobrushin` (V.1.1). [V] |  |
| V.1.9 | fix | Status "open (Lean)"; chapter L37 says "[open] in Lean; [classical] on paper". Write the classical part as its own row or drop it. [S] |  |
| V.1.10 | drop | "Certified class = DMP-complete inputs" (reading) is in no chapter: grep of `05-part-V-pnp.md` for "DMP-complete", "complete input" finds nothing, and no other row cites V.1.10. [V: grep] |  |
| V.3.6 | combine | Same declarations as II.6.2 (`gauss`, `unsat_of_odd`, `Proof/Crossing.lean`). Keep II.6.2. [V] |  |
| V.3.7 | combine | Same declaration as II.6.5 (`cross_any_system`). Keep II.6.5. [V] |  |
| V.3.8 | fix | Status "Lean (`summary`) + classical" cites no declaration; name the Lean `summary` theorem and its file. [V: auditor script] |  |
| V.3.12 | drop | "Flux-loss principle reproduces Urquhart; for Frege as hard as formula bounds" (reading) is in no chapter: `05-part-V-pnp.md` mentions Urquhart only as an attribution in V.3.9 (L75). No other row cites it. [V: grep] |  |
| V.4.3 | combine | Same declaration as II.6.5 (`cross_any_system`); the CP specialisation has no declaration of its own (the abstract system `SD` is not tied to cutting-planes derivations in the cited names). Keep II.6.5. [V] |  |
| V.4.7b | fix | Row: "fail at width 3"; chapter L110: "fails at constant width". V.4.10 (open) is width-3 interface hardness; the row mixes "the interface bound fails" with "hardness". Align. [S] |  |
| V.5.1 | combine | Same declarations as II.7.1, II.7.2 (`fixed_after`, `reaches_floor`, `iterate_clog_pairUp`) and I.6a (`real_never_arrives`); `sum_pairUp` goes to II.7.2. [V] |  |
| V.5.2 | fix | Lean + numerical row with no declaration (`Native/RouteBChain.lean`; counts 16 to 12 theorems, 5 to 4 layers in `NATIVE-METHOD.md`). Name the declarations or call it numerical. [V] |  |
| V.6.N2 | combine | Cross-reference to V.4.10 (same open step). Delete; V.4.10 is the home. [V] |  |

### Part VI (87 rows, 10 change)

| ID | Action | Evidence | Proposed new text or status |
|---|---|---|---|
| VI.0c | combine | Same claim as VI.4.2a (OpenAI 2026-09-08: smooth compactly supported force, zero initial data; external). Keep VI.4.2a. [V] |  |
| VI.0d | combine | Same claim as VI.4.1a (Theorem 1.1) and VI.4.1d (certificate unreleased, hash only). Keep those. [V] |  |
| VI.0e | fix | Two things in one row: scope ("proves no statement about the real Navier-Stokes equations") and a checkable fact ("the Lean modules contain no Navier-Stokes object"), which is VI.2.1 (paper, observation; `ABInterface` doc: "this library has no Navier-Stokes object"). Keep the scope half as the scope row, fold the fact into VI.2.1. [V: `NavierStokesAPI.lean:323-326`] |  |
| VI.3.1c | fix | Status: the Lean `ns_energy_window` is `(forall tau in (0,1], tau^(5a-2) <= 1) iff 2/5 <= a`: pure exponent arithmetic. The exponent 5a - 2 is supplied by the classical scaling computation (VI.3.1a); no energy object exists in the library (VI.2.1). Same for VI.3.1d (`ns_window`). Mark "Lean (model: the exponents of VI.3.1a)". [V: `NavierStokes.lean`, digest] |  |
| VI.3.1d | fix | As VI.3.1c: Lean (model: exponents). [V] |  |
| VI.3.5c | fix | Row says the one-step certificate "is" `CostAboveFloor` of 1 - q over 2 sqrt(C r). `gap_of_costAboveFloor` proves one direction: CostAboveFloor (strict, cost > floor) implies `4 C r <= (1 - q)^2` (non-strict). The converse and the boundary case are not in Lean. Say "implies". [V: `Blowup.lean:83-94`] |  |
| VI.3.5e | upgrade | Downgrade. `boundary_quantum` is the identity `sum_{i<n} (durations a i)^(-1) * durations a i = n`. The Beale-Kato-Majda count is not defined in Lean; the physical statement ("each rescaled step adds one fixed quantum to the BKM count") is a reading of an arithmetic identity. Status: reading (Lean identity as model). [V: `Blowup.lean:196`, digest] | reading (Lean: the identity `boundary_quantum`) |
| VI.5.2 | fix | Chapter L249 widens "false if VI.0d holds" to "If the 2026 claims hold" (both OpenAI and Alpoge-Buckmaster); OpenAI's claim has a force and addresses (C), (D), not the unforced regularity slot. Align chapter or row. [S] |  |
| VI.6.3g | fix | Chapter L323 says "Only SU(2) is stable" with no mark; the row says SU(2) attracts (classical, Hamilton) and the "only" part rests on VI.6.3i (external, Cao-He). [S] |  |
| VI.8 | combine | The same closing rule is in VII.7.2, VIII.7.3 and the abstract (L92-93): "if an independent proof appears, one row, one verdict line, one abstract item change". Keep one row (0.1 or X.67). Chapter L362 says "either way the paper changes", the row says only on verification; fix the chapter. [S] |  |

### Part VII (89 rows, 27 change)

| ID | Action | Evidence | Proposed new text or status |
|---|---|---|---|
| VII.0c | combine | Modularity as the source of the continuation is VII.1.1d and VII.4a; keep VII.1.1d. [V] |  |
| VII.0d | combine | `BSDStatement W` and `bsdStatement_iff` are VII.3.5a (Lean); the claim that it is the rank part of the Clay statement is the paper-status remainder. Fold into VII.3.5a. [V] |  |
| VII.0f | combine | Open from analytic rank 2 is VII.5.1 (open step) and VII.1.2a. Keep VII.5.1. [V] |  |
| VII.1.1j | fix | Chapter L45 calls p-parity "a conjecture for E/Q"; the row records it as a theorem (Monsky 1996, Nekovar, Dokchitser-Dokchitser 2010). The chapter wording should follow the row. [S] |  |
| VII.1.1k | drop | Row and chapter both say "context only, not used". No row cites VII.1.1k (grep of the ledger). Drop from the ledger and from the chapter table, or keep as context outside the count. [V: grep] |  |
| VII.1.2c | combine | Refined formula for all curves is VII.5.3. Keep VII.5.3. [V] |  |
| VII.1.2d | combine | RH for L(E, s) beyond Dirichlet is part of IV.0c (GRH beyond Dirichlet open); VII.5.8 says the same again. Keep IV.0c with a pointer. [V] |  |
| VII.2c | combine | R136a1 half is II.13.2; "OpenStep or External slot is an ordinary hypothesis" is II.12.1 (and VIII.2c). Keep II.12.1 and II.13.2. [V] |  |
| VII.3.0 | resolve | Half resolved. `docs/unified/bsd-axioms.log` was regenerated after the adapted `BSDAPI.lean`: log 2026-11-24 04:50, source 03:52; it records "build ProofPhase.Unified.BSDAPI: Build completed successfully", 46 declarations, 45 axiom lines all standard (three subsets: `E32` on [propext, Quot.sound], `E32Z_Δ` on [propext], `E32Z` none), no sorry/admit/native_decide, imports of the core `Arsenal.BSD.*` only. So the standard-axioms claim can be made for the API instance. Not re-run by the auditor (no build). Remains: IM's own audit of the native `Arsenal.BSD.*` modules (`arsenal/tools/check.sh`) was not run for this draft. [V: log and mtimes read] | The adapted API instance `BSDAPI` is on standard axioms (log regenerated 2026-11-24). IM's audit of the native `Arsenal.BSD` modules (`arsenal/tools/check.sh`) is not yet run for this draft (paper). |
| VII.3.3c | fix | Lean row with no declaration. The two examples are `Arsenal/BSD/Count.lean:84` (`example : frobTrace (reduceMod <0,0,0,-1,0> 5) = -2 := by decide`) and `:86` (`hasseCheck ... = true := by decide`), both kernel `decide`. Cite them by line. [V] |  |
| VII.3.4e | combine | `hasseCheck_iff_card` is the finite-field form of the decidable check of VII.3.3a (`hasseCheck_iff`); the chapter (L135) states only the latter. Fold into VII.3.3a. [V, S] |  |
| VII.3.5b | fix | Convention C2 (section 1.3): the chapter writes "[Lean, from BSD]" (L166), the ledger bare Lean. The same holds for VII.3.5c (L168), VII.3.5d (L170), VII.3.1a (L105), VII.3.2d (L128), VII.3.4b (L150), VII.3.4d (L157), VII.3.6b/c (L182, L186), VII.3.7a (L195), VII.3.8d (L215), VII.5.6 (L186). Use "Lean (from X)" in the ledger. [S] |  |
| VII.3.7c | combine | Same `ledgerCard`, `LedgerInput` as VII.2b (and VII.4f for the Goldfeld input). Keep VII.2b. [V] |  |
| VII.3.8a | fix | Add `instance : E32.IsElliptic` (`BSDAPI.lean:288`); the row cites `E32_Δ` only, which gives the discriminant 64, not ellipticity. [V] |  |
| VII.3.8b | fix | Split. Lean (kernel): `count_E32` (every odd prime), `hasse_E32_five` (`by decide`). Not kernel proofs: the `#eval` trace list to 37 and the `#guard` Hasse list to 59 (`BSDAPI.lean:313-324`) are build-time computations. Label the second part "numerical (computed in the build)". The note's "below 100" is not in the source: confirmed, the guard stops at 59, so the chapter is right and `BSD.md` should be changed. [V] |  |
| VII.4a | combine | Same as VII.1.1d and VII.0c (modularity). Keep VII.1.1d. [V] |  |
| VII.4g | combine | Summary of VII.4b, VII.4c, VII.4d (the three named parts are classical theorems missing from Mathlib). Fold. [V] |  |
| VII.5.4 | combine | Restates VII.1.1g (Kolyvagin with modularity) as its contrapositive. Fold. [V] |  |
| VII.5.5 | combine | Restates VII.1.1f, VII.1.1g (Gross-Zagier, Kolyvagin) and VII.1.2a (nothing from order 2). Fold. Chapter L271-274 states only the first direction. [V, S] |  |
| VII.5.6 | combine | Same declaration as VII.3.6c (`EulerData.no_finite_zero`). Keep VII.3.6c. [V] |  |
| VII.5.7 | combine | Same declaration as VII.3.2d (`analytic_parity`). Keep VII.3.2d. [V] |  |
| VII.5.8 | combine | Restates VII.1.1b (Hasse) and VII.1.2d / IV.0c (RH for L(E, s) open). Fold. [V] |  |
| VII.6d | fix | Chapter L302-304 marks it "[Lean for the linear algebra, from the intersection numbers and the Hodge index property, both external]"; ledger says reading. Say which part is which. [S] |  |
| VII.6e | fix | Chapter L308-311 carries [classical statement, open], [Lean for the shape] and [numerical] inside one bullet; ledger says reading. [S] |  |
| VII.6f | combine | Same as VII.5.3 (refined formula open; the five quantities free numbers in Lean). Fold. [V] |  |
| VII.7.1 | combine | Same item as VII.3.0 (regenerate the axiom log, run IM's audit). Fold into VII.3.0. [V] |  |
| VII.7.2 | combine | Closing rule, same as VI.8 and VIII.7.3. Fold into one row. [V] |  |

### Part VIII (67 rows, 15 change)

| ID | Action | Evidence | Proposed new text or status |
|---|---|---|---|
| VIII.0c | combine | Open for p >= 2 is VIII.5.1 (the card's open step) and VIII.1.4a. Keep VIII.5.1. [V] |  |
| VIII.1.4a | fix | The first clause (p >= 2 in general) is VIII.5.1; keep only B in general, D, the Hodge type in characteristic p (VIII.1.3c, VIII.1.3d say it as well). [V] |  |
| VIII.1.4b | combine | Positivity route over Z is IV.2.5c (arithmetic Hodge index) and VIII.5.3. Keep IV.2.5c. [V] |  |
| VIII.2b | combine | `problem.proved` as antisymmetry (`HodgeAPI.lean:76`, `proved i h := le_antisymm h i.alg_le`) is VIII.2a/VIII.3.2a. Keep VIII.2a. [V] |  |
| VIII.2c | combine | Same sentence as II.12.1 and VII.2c. Keep II.12.1. [V] |  |
| VIII.2d | fix | True and wider than the row. `Unified/All.lean` imports only `Unified` and `TransportBridges`. A grep of the `import` lines over `docs/mass-gap/formal/` finds no importer for `HodgeAPI` (it imports `HodgeLinear`), `BSDAPI`, `NavierStokesAPI`, `GRHToO1`, `GRH/ContourShiftTie` (a leaf), `ElectricSUNRunning` (a leaf), and `BlowupSUN` only from `ETM/Instances`. There is no `ProofPhase.lean` root file in `formal/` (the `ProofPhase` lean_lib in `lakefile.toml` has no explicit roots), so these modules build only by explicit target, as in each `*-axioms.sh`. The check that covers them is `tools/independent-check.sh` (new row 0.11). Rewrite as one row listing the leaf modules, or add one aggregate module. [V: grep of imports] |  |
| VIII.3.2a | combine | Same as VIII.2a (`problem`, open step to conclusion). [V] |  |
| VIII.3.2b | fix | Chapter L132-135 marks "[Lean, from Hodge-Riemann]" (the input is an `External`); convention C2. [S] |  |
| VIII.4b | combine | Same claims as VIII.1.1a (Lefschetz (1,1), line bundles are O(D)); VIII.4b names the Lean slots `DivisorInput.exact`, `.hodge_int`, `.div_hodge`, which belong in VIII.3.6c. Fold. [V] |  |
| VIII.4c | combine | Identical wording to VIII.1.1b (hard Lefschetz sends divisor classes to curve classes). The slots `CurveClassInput.hl_hodge`, `.hl_alg` belong in VIII.3.6d. Fold. [V] |  |
| VIII.4d | fix | The row lists the intersection numbers (f1^2 = f2^2 = 0, f1 f2 = 1, Gamma Delta = N, ...); the chapter (L152-153, table L216) names the slot `CurveInput.geometry` and gives none of the values. Add the values to the chapter or shorten the row. [S] |  |
| VIII.4e | combine | Same as VIII.1.3f (Deligne 1974). Keep VIII.1.3f. [V] |  |
| VIII.5.3 | combine | Arithmetic Hodge index as the GRH sign slot is IV.2.5c (and II.3.5, VIII.1.4b). Keep IV.2.5c. [V] |  |
| VIII.6c | combine | Goedel completeness is VI.4.4a (same sentence, classical). Keep VI.4.4a. [V] |  |
| VIII.7.3 | combine | Closing rule, same as VI.8, VII.7.2. [V] |  |

### Part IX (54 rows, 11 change)

| ID | Action | Evidence | Proposed new text or status |
|---|---|---|---|
| IX.0b | combine | Cross-reference. The claim is IX.3.1h (kernel of the SU(5) block embedding, Lean) with IX.1.1a. Delete the row. [V] |  |
| IX.0c | combine | Same as IX.5f (whether any candidate meets the gate's "checkable consequence"; the owner's decision). Keep IX.5f. [V] |  |
| IX.3.2f | drop | Pontryagin duality is in no chapter: `09-part-IX-gu.md` has no "Pontryagin" (the chapter states the character classification without attribution, L108-109). Nothing cites IX.3.2f. Drop, or add the attribution to the chapter. [V: grep] |  |
| IX.3.3 | combine | Same declarations as II.12.4 (`chargeQuantisation`, `PhaseLabel.integer_charge`). Keep II.12.4 (a fact of the API); IX.3.2e is the use. [V] |  |
| IX.4.1b | combine | Anomaly cancellation is not in Lean: same as the open row IX.7b (Route 2) and one item of IX.3.1i. Keep IX.7b. [V] |  |
| IX.5b | fix | Row status paper; chapter L168-176 marks the derivations [Lean] (L172) and leaves the "standard expectation" cell unmarked. [S] |  |
| IX.5d | fix | Row status paper; chapter L182 marks "[classical] + [Lean]". [S] |  |
| IX.5g | fix | Row status reading; chapter L189 tags the owner's position "[open]". [S] |  |
| IX.6d | fix | Row says "electroweak breaking, then confinement"; chapter L200-203 says "the 2-part acts first and the 3-part remains", no "confinement". [S] |  |
| IX.6g | fix | Row includes "descending from 2 and 3"; chapter L211 states only that every SU(N) "describes existence" is the owner's reading. [S] |  |
| IX.6h | fix | Row status open; chapter L212-213 sits under the all-[reading] header of IX.6 and says "No link to Z_6 was found". [S] |  |

### Part X (83 rows, 20 change)

| ID | Action | Evidence | Proposed new text or status |
|---|---|---|---|
| X.2b | combine | Same declarations as III.8.1 (`runs_two_targets`) and IV.5.2 (`runs_and_mirror_on_line`). Keep those. [V] |  |
| X.7f | fix | Chapter L443-445 drops the seam condition mu (theta^n u_0 + sigma/(1 - theta)) <= 1 from the sentence "any positive twist ratio clears O1 with enough layers". [S] |  |
| X.7l | fix | Row says "recalled; to be checked against the sources"; chapter L458-459 marks it [reading] and drops the caveat, so it reads as checked. [S] |  |
| X.7o | fix | Chapter L463-464 drops the law interval [3/10, 7/10]. [S] (The Lean `ident_margin_lost` concludes `1 - q n < eps`; the docstring speaks of "the probability of state 0", the statement of q approaching 1: harmless but confusing. [V]) |  |
| X.56 | combine | Cross-reference to III.1.6, III.1.7, III.3.1. Delete; point III.1.6 to the SU(N) result. [V] |  |
| X.58 | fix | Relabel `certified` (convention C3, section 1.3; `numerical` is wrong for ball-arithmetic enclosures with a named-hypothesis Lean step, and 0.8 says certified). Absorbs 0.8. The abstract step has three Lean instances, not one: `onebox_cert_3_5` (a = 0.60), `onebox_cert_13_20` (0.65), `onebox_cert_69_100` (0.69) in `GRH/OneBoxCert.lean:160-174`; X.58b cites only the last. [V] |  |
| X.58b | fix | Add `onebox_cert_3_5`, `onebox_cert_13_20` (`OneBoxCert.lean:160, 167`) to the cited names. Lean, conditional on the numerical enclosures `OneBoxEnclosures`. [V] |  |
| X.60 | combine | Cross-reference to XI.1, XI.3. Delete. [S] |  |
| X.65 | fix | Relabel `certified` (numerical enclosures; abstract step Lean X.58b). The values at a = 0.60, 0.65, 0.69 each have a Lean instance (see X.58b). [V] |  |
| X.8 | combine | Cross-reference to II.10.3 (`elec_cost`, `szego_of_elec`). Delete the row. Chapter L112-113 marks it [Lean] with no pointer to II.10.3. [S] |  |
| X.16 | fix | Keep the row (Lean, card form). Fix Part X L146: "GRH does not imply O1, and O1 does not imply GRH (claims X.16, X.17)" is not what X.16 and X.17 give (see 0.9). [V] |  |
| X.30 | combine | Cross-reference to II.11.2, II.11.3. Delete the row. [S] |  |
| X.33 | combine | Same statement as X.7g and X.49b: positive floor as the error bar goes to zero (cost above floor at fixed physical length, uniform in the cutoff) is O1 in the form III.5.6. Keep X.7g as the one transport-form restatement; III.5.6 stays the home. [V] |  |
| X.35 | combine | Cross-reference to II.13.2. Delete. [S] |  |
| X.36 | fix | Two classical claims: Goedel's theorems for a whole effectively axiomatised theory with arithmetic (= I.8h) and Presburger/Tarski completeness. Move the first to I.8h, keep the second. [V] |  |
| X.44 | combine | Same declarations as II.9.0 (`pays_of_factors`, `carry`, `RunSys.carry`, `RunSys.contract`). Keep II.9.0. The cited theorems bound M n at a fixed n; none states "every finite scale is reached", which is the reading. [V] |  |
| X.45 | combine | Same `margin_pos_of_factors` as IV.3.6b and X.9 (finite part). Fold into IV.3.6b. [V] |  |
| X.49 | fix | Chapter L383-384 states "tanh(beta N) per layer" without the bound abs(Z_{e=1}) <= tanh(s)^{n+1} Z_{e=0}, the e^{-2s} floor or "every end-face outside". The Lean `kchain_tanh` takes the floor as hypothesis `hc`; "s = beta N" for the SU(2) Wilson action is the instance (`JoinLossSlab.lean`). [S] |  |
| X.49b | combine | Same as X.7g and X.33. [V] |  |
| X.50 | combine | Same claim, sources and status as I.8d (root chain pins by hash; Gravity's side read, DMP's side not re-read). Keep I.8d. [V] |  |

### Part XI (7 rows, 3 change)

| ID | Action | Evidence | Proposed new text or status |
|---|---|---|---|
| XI.2c | combine | `Hom`, `RunSys.contract` are II.11.1; `Hom.iterate_comm` and `reaches_of_contracting` are II.11.1 and II.11.2. Fold into II.11.1. [V] |  |
| XI.2a | combine | Same statement and declarations as II.11.2. Make Part II the home (II.11.2 counted Lean, XI.2a pointer), as the writers' notes for X and for I-II say ("count them once, in Part II"). Currently the ledger counts XI.2a/XI.2b and marks II.11.2/II.11.3 as cross-references; the two notes disagree. [V] |  |
| XI.2b | combine | Same as II.11.3. Chapter L41-42 and abstract L51-52 restrict it correctly ("without a contraction ... in general"); the row says "no procedure decides settling for all content" unconditionally. Fix with 0.7. [V, S] |  |

## 2b. The known cross-reference and scope rows: where each lives

| Row | Proposed home (once) | Action |
|---|---|---|
| 0.1 | Part 0 as the paper-level scope row (not counted). It also absorbs the closing rule now repeated in VI.8, VII.7.2, VIII.7.3 and the abstract (L92-93). | keep |
| I.9b | II.13.2 (same declarations `R136a1`, `R136a1.out`). Delete I.9b; Part I cites II.13.2. | combine |
| II.11.2 | II.11.2 itself, counted Lean (home of the settle theorem). XI.2a, 0.7, X.30 point to it. | fix |
| II.11.3 | II.11.3 itself, counted Lean (home of the edge). XI.2b, 0.7, X.30 point to it. | fix |
| II.12.2b | X.27 (the three cards are `Problem`s). Delete II.12.2b; add the X.27 pointer in the chapter (L383-386 has none). | combine |
| III.0 | Stay, as the Part III scope row (not counted). | keep |
| V.6.N2 | V.4.10. Delete. | combine |
| VI.0e | Keep the scope half ("proves no statement about the real Navier-Stokes equations", not counted). Fold the checkable half ("no Navier-Stokes object in the Lean") into VI.2.1. | fix |
| VII.0e | Stay, as the Part VII scope row (not counted). | keep |
| VIII.0d | Stay, as the Part VIII scope row (not counted). | keep |
| IX.0a | Stay: a definition of the gate, not a claim (not counted). | keep |
| IX.0b | IX.3.1h (kernel of the SU(5) block embedding, Lean) with IX.1.1a. Delete. | combine |
| IX.0d | Stay, as the Part IX scope row (not counted). | keep |
| X.8 | II.10.3 (`elec_cost`, `szego_of_elec`). Delete. | combine |
| X.30 | II.11.2 and II.11.3. Delete. | combine |
| X.35 | II.13.2. Delete. | combine |
| X.56 | III.1.6 (now SU(N)), III.1.7, III.3.1. Delete. | combine |
| X.60 | XI.1 and XI.3. Delete. | combine |

Net effect on counts: 9 rows leave, 2 move into the counted Lean total, 7 scope rows stay outside the count.

## 3. Chapter claims that have no row

### 3.1 Proposed new rows (10)

Selected because each is a Lean result, a stated status or a number that a reader will rely on. Statuses are the auditor's proposal.

| New ID | Status | Claim | Source | Why it is missing |
|---|---|---|---|---|
| 0.10 | Lean | Weil's explicit formula for zeta, for every smooth compactly supported test function, by the contour shift, on a Mathlib-only core, no named step | `ProofPhase/GRH/ContourShift.lean` `CS.contourShift`; `ContourShiftTie.lean` `explicit_formula_of_smooth`; log `docs/unified/contourshift-axioms.log` | abstract L61, L115, L144 state it; IV.1.5 (upgraded) is the Part IV row |
| 0.11 | paper | The Lean layer was re-checked by `leanchecker`, `nanoda_lib` (independent kernel in Rust) and `lean4lean` on 2026-11-23: 317 modules at the run start (323 in the last incremental line); 356 `.lean` files exist in `docs/mass-gap/formal/` now, 29 of them with a modification time after the log's last write (2026-11-23 22:26): `API.lean` and `API/*`, `GRH/ContourShift*` (7), `GRH/ExplicitFormula*` (3), `GRH/OneBoxCert`, `General/GUCentre`, `General/GUCharge`, `Proof/SoundAPI`, `Unified/BSDAPI`, `ElectricSUN*` (3), `GRHToO1`, `HodgeAPI`, `HodgeLinear`, `NavierStokes`, `NavierStokesAPI` (by modification time, not by content); the 14 Lean files of the `im` repository are outside that run | `docs/unified/INDEPENDENT-CHECK.md`, `independent-check.log`, `independent-check.stamp` | abstract L43-44 and L158 say "re-checked by independent kernels (Part II)"; Part II never mentions it. Re-run `tools/independent-check.sh` before submission |
| IV.1.5b | open | The explicit formula for Dirichlet and other L-functions, the C^2 test class, and Weil's criterion for L-functions are not in Lean | `docs/unified/CONTOUR-SHIFT.md` 5 | replaces the surviving half of IV.1.5 |
| IV.1.11 | Lean | From the named hypothesis `ExtRH` and the kernel bookkeeping, `ScaleSign` and the non-negativity of Weil's pairing hold for smooth compactly supported kernels (the zeta column of the ledger) | `ProofPhase/GRH/ContourShiftTie.lean` `zeta_tie_in_smooth`; `GRH-TIE-IN.md` | Lean results of `GRH/TieIn*.lean` are not in Part IV at all |
| V.4.11 | Lean | `ExtractAPI G c` (every cutting-planes refutation of F o G of size below exp(c (w+1)) admits a narrow-clause labelling) is equivalent to `LiftCPConst G c` | `ProofPhase/Proof/SoundAPI.lean` `liftCPConst_iff_extract` (log `soundapi-axioms.log:15`) | abstract L64-65 states it; no row, no chapter text in Part V |
| III.4.3c | classical | The site-percolation threshold of Z^4 is about 0.197, so -log(1 - p_c) = 0.22 | `RDOEBLIN.md` 78-81 (recalled) | split from III.4.3a |
| III.5.4c | classical | The connective constant of self-avoiding walks on Z^d is at least d (so the 0.881 hand-over loses to path entropy in every d >= 3) | Part III L188; elementary counting | unmarked in the chapter, used for the bold "every d >= 3" claim |
| IV.3.7c | numerical | The place-by-place condition fails by 9.7 t_0 at support 1.225 while the whole form is positive | Part IV L141 (source note not identified) | IV.3.7b says "fails by 7.9 t_0 at support 1.225" for the Weyl two-term bound; two figures at one support, no row for 9.7 |
| 0.12 | classical | Tuning: the fifth is a rotation of pitch mod the octave; twelve pure fifths overshoot seven octaves by 3^12/2^19 = 1.01364; equal temperament gives 2^(7/12); 19/12 is a convergent of log2(3); each zero 1/2 + i gamma sounds at frequency gamma in log x | abstract L129-140 | four [classical] marks with no row (one grouped row) |
| 0.13 | classical | Attributions of the introduction: Osterwalder-Schrader (reflection positivity), Weil (RH as one positivity), Hodge and Riemann (positivity on cohomology) and Weil (RH for curves), Dobrushin (contraction gives a unique equilibrium) | abstract L101-105, L171-172 | one grouped row for the attributions |

### 3.2 Lean results in the repository that the paper does not name

Found by counting, for each module, how often its name occurs in `CLAIMS.md` and `draft/*.md`: (all in `docs/mass-gap/formal/ProofPhase/`) `GRH/ContourShift*` (7 files, see IV.1.5), `GRH/ExplicitFormula*` (3), `GRH/TieIn.lean`, `GRH/TieInFF.lean` (easy direction: `ScaleSign` iff all zeros on the line in the finite model; function-field instance; 43 declarations, `grhtiein-axioms.log`), `General/SUNTwist*.lean` (6 modules, 169 declarations: strict twist bound and positive electric sectors for every SU(N); only `SUNTwistPrimes` is named, in IX), `Proof/SoundAPI.lean`, `Proof/Lifting*.lean`, `Unified/EncoderInstances.lean`, `Unified/ProofSize.lean`, `ETM/Instances.lean`. The paper may leave them out; if so, the abstract should not claim the results they prove (the explicit formula, the SU(N) twist bound, the lifting equivalence).

### 3.3 Chapter statements with a mark or number but no row, by chapter (counts from the sweeps)

| Chapter | Count | Typical content | File with line numbers |
|---|---|---|---|
| Abstract / Part XI | about 40 | per-problem "what is proved" bullets (mostly restatements of rows, see finding 4 in 1.4), attributions, the 4 [classical] tuning marks and 1 [reading]; Part XI design claims ("the core network has to be trained from the ground up", "linear-attention transformers are such programmers") | `audit-working/sweep_0XI.md` |
| Part I | 21 | 9 unmarked; "Z_tw < Z at every beta != 0" and "at least log(1+sqrt 2)" restated with [Lean]; "unlintable assumption is the open step of each card" | `sweep_I.md` |
| Part II | 35 | unmarked statements, pointers, a few [Lean]/[classical] marks | `sweep_II.md` |
| Part III | about 60 | numbers 0.42, 0.91, 1.26, 1.45, "15 cells", "91 pieces"; "in every d >= 3" (needs mu_d >= d, row III.5.4c); "rigorously log mu_4 between log 4 and log 7" unmarked | `sweep_III.md` |
| Parts IV, V | about 70 | numbers near rows: IV.3.9 onset 0.425 vs row 0.40 to 0.43; 9.7 t_0 vs 7.9 t_0 (row IV.3.7c); many table cells with marks | `sweep_IVV.md` |
| Part VI | about 45 | see file | `sweep_VI.md` |
| Part VII | 24 | see file | `sweep_VII.md` |
| Parts VIII, IX | 41 | the SO(10) "forces Z_6" sentence (IX L41-42) is untraced; Lean declaration and axiom counts | `sweep_VIIIIX.md` |
| Part X | about 45 | the table cells (L221-226), "II.9.1 to II.9.5" restated (L436-439; the rows exist as II.9.1 to II.9.5, the sweep missed them), "GRH does not imply O1, O1 does not imply GRH" (L146, see 0.9) | `sweep_X.md` |

Most of these are narration or restatements of existing rows. They are listed in the sweep files with chapter line numbers and 15-word quotes; the sweep is mechanical and was not individually verified except where a row above says `[V]`.

## 4. What the auditor could not decide, and why

1. **IV.2.2b (the Mathlib name `ZMod.completedLFunction_one_sub_even`/`_odd`).** Mathlib is not in this checkout (no `.lake`), so the name could not be checked. Status stays "classical (Mathlib name not checked)". To settle: open Mathlib v4.34.0 and grep the two names.
2. **No Lean build was run.** Every "declaration exists" is by reading source and by matching names with a script (all names in Lean-status rows resolve); that a declaration compiles on the current Mathlib pin is the job of the axiom scripts and of `tools/independent-check.sh`. VII.3.0 relies on the log's timestamp (log 04:50, source 03:52), not on a rebuild.
3. **Whether the semantic Lean flags that the haiku job raised and I did not read are real.** About 100 flagged rows were not re-read (kinds a/c/d on Parts II to IX). Judged from the pattern of the ones I did read, most are "claim names the hypothesis in its text, status does not" (convention C2) or truncated signatures. They are in `audit-working/leancheck_*.md`; none is used above unless marked `[V]`.
4. **Which rows the owner wants as "context" even if unused.** VII.1.1a to VII.1.1k, VI.1.1a to VI.1.1g, VI.6.1a to VI.6.1f are classical/external rows with no other row depending on them. They are all stated in their chapters, so none is proposed for dropping except VII.1.1k, which says of itself "context only, not used". If the owner wants a smaller ledger, these 24 are the next candidates, one row per citation being the only reason to keep them apart.
5. **V.1.3 wording** ("gap in time iff spectral support" vs the chapter's "no spectral mass above e^{-m}"): `time_gap_iff` in `Mixing/TimeGap.lean` decides which; not read.
6. **III.2.1, III.2.4, III.9.3 status wording** (conditional on named hypotheses `GDSw`, `OpenPieces`, `M1Hypotheses`): the claims already say "from OpenPieces" etc.; whether to add C2 qualifiers is the coordinator's call.
7. **The 7 "scope" rows as claims.** VII.0e, VIII.0d, IX.0d ("proves no case not already known", "derives no hypercharge") are promises about the paper, not about mathematics; they are counted by no status. Kept as is.

## 5. Method, in short

* Parsed the 673 table rows; matched every backticked identifier in each Lean-status row to a declaration in `docs/mass-gap/formal/`, `im/arsenal`, `im/proof` (12908 names indexed): no unresolved name except file/word tokens.
* Read the newer notes and Lean (`CONTOUR-SHIFT.md`, `EXPLICIT-FORMULA.md`, `GRH-TIE-IN.md`, `SUN-PRIMES.md`, `NP-SOUND-APIS.md`, `NP-LIFTING.md`, `INDEPENDENT-CHECK.md`) and the logs `contourshift-axioms.log`, `sunprimes-axioms.log`, `bsd-axioms.log`, `soundapi-axioms.log`.
* Nine haiku sweeps (row by row against chapter text, plus chapter claims without a row) and seven haiku checks of statement against signature. Sibling notes read: `parts-VII-VIII-handover.md`, `paper-vi-ix-handover.md` and the claims-incoming "Notes for the coordinator".
* Row IDs in the chapters are coarser than the ledger's (the chapter says III.4.3, the ledger III.4.3a/b; VI.3.1 for VI.3.1a to f), so "label used" was judged by statement, not by exact label. No ledger row has its statement absent from its chapter except the four drops III.6.10, V.1.10, V.3.12, IX.3.2f and the fold VII.3.4e (section 2); VII.1.1k is present but self-declared unused.
