# Incoming claims: Parts I and II (`draft/01-part-I-dmp.md`, `draft/02-part-II-tools.md`, draft 2, 2026-11-24)

For the coordinator to merge into `../CLAIMS.md`. Same format as `CLAIMS.md`. Lean paths are relative to
`docs/mass-gap/formal/` unless they start with `docs/`; a path in the `im` repository is marked. Nothing in the repository outside the
chapters and this folder was edited.

## Labels kept (content stays; rows in `CLAIMS.md` unchanged)

Part I: `I.1`, `I.1a`, `I.2`, `I.3`, `I.4a`, `I.4b`, `I.5a`, `I.5b`, `I.6a`, `I.6b`, `I.6c`, `I.7a`, `I.7b`, `I.7c`.
Part II: `II.0`, `II.1.1` to `II.1.5`, `II.2.1` to `II.2.3`, `II.3.1` to `II.3.5`, `II.4.1` to `II.4.5r`, `II.5.1`, `II.5.2`, `II.6.1` to
`II.6.6`, `II.7.1` to `II.7.3`, `II.8`.

Changes of place or wording that touch a kept label, none of which changes a claim: Part I's vocabulary table moved from section I.8 to
section I.12 and gained four rows; I.4 got one pointer sentence to I.9; II.8 now says that it holds for II.9 to II.13 too and points to
Part X section 4 (it used to say "Part X states this once").

## Labels retired

None in Part I or Part II. (The transport statements that were X.7a to X.7e in Part X are now II.9.1 to II.9.5 here; see
`X-generalisation.md`.)

## New rows: Part I

New sections: I.8 (linter), I.9 (excision at transmission), I.10 (rights tied to identity), I.11 (the arsenal), I.12 (the table).
No quotes of the owner are added: the sources are paraphrased and marked.

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| I.8a | DMP reads as an existence linter: Gravity is the linter, DMP the universally readable rule set that is its passing condition; existence is what the linter passes | reading | `docs/mass-gap/weak-coupling/PREP.md`, 2026-11-24, "DMP is a very well defined existence linter" | none |
| I.8b | Gravity's check passes only when the pinned DMP matches its hash, the setup file is complete, no source file uses an escape hatch, the build succeeds and every theorem rests on the three standard axioms | paper | `evidence/tools/check.sh`; `tools/check-pin.sh` (read; not run for this draft) | run the check |
| I.8c | The arsenal has the same shape at small size: its lint is the linter, "Mathlib v4.34.0 only, no escape hatch, open parts only as named R136a1 hypotheses" the passing condition | paper | `im` repository, `arsenal/README.md`, `arsenal/tools/lint.sh` | none |
| I.8d | The root chain pins in both directions: Gravity holds a pinned copy of DMP; that DMP pins Gravity in turn is stated by the owner and the notes, not re-read | paper (Gravity's side read; DMP's side not re-read) | `vendor/dmp/PIN`; `tools/check-pin.sh`; `PREP.md`, 2026-11-24 | read DMP's check |
| I.8e | A linter certifies form, not content: passing does not say that DMP's sentences describe the world | paper | `PREP.md`, 2026-11-24, care point 1 | none |
| I.8f | The unlintable assumption is that the system runs (the MP-type existence assumption), which is O1 in each card's terms | reading | `PREP.md`, 2026-11-24, care point 2, and "O1 ... must always be the open step" | none |
| I.8g | "Universally readable" holds for the form (plain text and Lean, checkable with the pinned toolchain); "universal superset" is a reading | reading | `PREP.md`, 2026-11-24, care point 3 | none |
| I.8h | A consistent, effectively axiomatised theory containing arithmetic cannot prove its own consistency (Goedel II) | classical | Goedel 1931 | none |
| I.9a | Excision at transmission: a wrong act is answered R136a1 at the gate and never crosses; only its remnant tail stays, the record that an excision happened; IM's verifier counts refusals without content | reading | `PREP.md`, 2026-11-24, "Correction to care point (2): 'transmitted' is the operative word"; DMP chapters 01 (C-infinity) and 06 as the notes cite them | none |
| I.9b | `R136a1 "name" P` is `P` as a named hypothesis, never an axiom (cross-reference to II.13.2, not counted twice) | (cross-reference) | `im` repository, `arsenal/Arsenal/R136a1.lean`, `R136a1`, `R136a1.out` | none |
| I.9c | The gate excises what its checks recognise as wrong at that tick; a later recognition is a later tick, with its tail recorded then, never a revision | reading | `PREP.md`, 2026-11-24, same entry, care point | none |
| I.10a | Rights tied to identity give total freedom inside and security at the gate; asymptotic freedom (free at short distance, bound at long) reads the same way: free inside the box, bound at the boundary | reading | `PREP.md`, 2026-11-24, "Security in CMOS: rights tied to identity" | none |
| I.10b | A sentence passes IM's door only when both the security and the operational grant carry its kind; one grant alone never passes | Lean | `im` repository, `proof/Im/Laws.lean`, `Im.pass_needs_both_grants`, `Im.one_grant_never_passes` | none |
| I.10c | IM's grammar is closed: the space has exactly 72 shapes, and every sentence keeps the decidable laws | Lean | `im` repository, `proof/Im/Closure.lean`, `Im.closure`, `Im.all_shapes_lawful`, `Im.space_size` | none |
| I.10d | A network of nodes that keep the guarantee on what their door lets in keeps it on any input | Lean | `im` repository, `proof/Im/Compose.lean`, `Im.sound`, `Im.galaxy_robust`, `Im.galaxy_is_a_node` | none |
| I.10e | Tokens only attenuate (kept by the grammar's construction; the theorem is not yet written) | open | `im` repository, `proof/Im/Closure.lean` (header: "the attenuation theorem is still to be written"); `docs/findings.md` IF9 as cited there | write the theorem |
| I.10f | "Permissible" is as good as its specification; the gate certifies integrity and authority, not the truth of content; the binding is as strong as the custody of the key | reading | `PREP.md`, 2026-11-24, same entry, care points | none |
| I.10g | Asymptotic freedom: the Yang-Mills coupling vanishes in the ultraviolet | classical | Gross-Wilczek 1973; Politzer 1973 (recalled, not re-read) | none |
| I.11a | The arsenal is the one place for content-free Lean results that need Mathlib and are used by more than one project; they are imported from the `im` repository and never copied | paper | `im` repository, `arsenal/README.md`; `docs/unified/API.md` 7 | none |

## New rows: Part II

New sections: II.9 (ledger and transport), II.10 (encoder and half-turn), II.11 (settle theorem and edge), II.12 (API), II.13 (arsenal and
lint), II.14 (closing paragraph, no claims).

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| II.9.0 | The ledger: if M_{i+1} <= e^{delta - c_i} M_i then M_n <= e^{n delta - sum c} M_0; costs at least kappa > delta give decay at rate kappa - delta and a summable M; a lower bound on M_n bounds the total cost | Lean | `ProofPhase/Unified/Ledger.lean`, `Pays`, `ledger`, `decay`, `summable_of_gap`, `size`, `CostAboveFloor`, `rate_of_costAboveFloor`; `ProofPhase/ETM/RunSys.lean`, `RunSys.carry`, `RunSys.contract`, `RunSys.decay_cost` | none |
| II.9.1 | Bounded transport (was X.7a): an uncertainty crossing contracting steps with fresh uncertainty at most R stays at most q^n e_0 + R/(1 - q) | Lean | `ProofPhase/Unified/Transport.lean`, `bounded_transport`, `transport_geom`, `acc_eq` | none |
| II.9.2 | Critical transport (was X.7b): at cost = floor e_n <= e_0 + sum r_j; sharp; bounded exactly when the r_j are summable; a constant fresh uncertainty grows without limit | Lean | `ProofPhase/Unified/Transport.lean`, `critical_transport`, `critical_sharp`, `critical_bounded_iff`, `critical_unbounded` | none |
| II.9.3 | Sign preserved (was X.7c): an uncertainty below the sign margin certifies the sign at every step | Lean | `ProofPhase/Unified/Transport.lean`, `sign_transport`, `sign_of_bounded`, `sign_of_critical` | none |
| II.9.4 | The ledger is the case of no fresh uncertainty (was X.7d) | Lean | `ProofPhase/Unified/Transport.lean`, `pays_iff_transports`, `carry_of_transport`, `ETM.Ledger.transports`, `contract_of_transport` | none |
| II.9.5 | Zero slack, exactly (was X.7e): an uncertainty and a margin paying the same cost have their ratio carried at cost = floor | Lean | `ProofPhase/Unified/Transport.lean`, `relative_transport`, `relative_critical` | none |
| II.10.1 | An encoder (state psi, rotated image psi' of the same norm) has one number, the reflection coefficient c = <psi, psi'>/norm(psi)^2, with abs(c) <= 1 from positivity; read from the other side c is conjugated | Lean | `ProofPhase/Unified/Encoder.lean`, `Encoder`, `Encoder.ofRot`, `refl`, `norm_refl_le`, `refl_swap` | none |
| II.10.2 | The Szego factor 1 - abs(c)^2 (the share of psi left after removing its projection on the mirror image) and the electric factor (1 - c)/(1 + c) (odd over even part) are fixed by c; both lie in [0, 1]; the cost is -log of the factor; a uniform factor bound below e^{-delta} is exactly a cost above the floor | Lean | `ProofPhase/Unified/Encoder.lean`, `szego`, `szego_mem`, `szego_pos_iff`, `szego_eq_one_iff`, `szego_remainder`, `elec`, `elec_mem`, `encoder_elec`, `pays_of_factors`, `costAboveFloor_of_factor_le`, `factor_le_of_costAboveFloor`, `oneBox_iff_refl` | none |
| II.10.3 | One distance, two functions: -log elec(c) = log((1 + c)/(1 - c)) = d, and szego(c) = 4 elec(c)/(1 + elec(c))^2 = 1/cosh^2(d/2) | Lean | `ProofPhase/Unified/GRHLens.lean`, `elec_cost`, `szego_of_elec` | none |
| II.10.4 | The half-turn: the electric factor is the Moebius map of (1/sqrt 2)[[-1, 1], [1, 1]], a symmetric matrix that squares to the identity; elec is an involution with antipodal fixed points sqrt 2 - 1 and -(1 + sqrt 2); it swaps product of reflection coefficients and hyperbolic addition of electric factors; its self-dual cost is log(1 + sqrt 2) | Lean | `ProofPhase/Unified/GRHLens.lean`, `halfTurn_mobius`, `halfTurn_transpose`, `halfTurn_mul_self`, `elec_elec`, `elec_selfdual`, `elec_fixed_neg`, `fixed_antipodal`, `elec_mul`, `elec_oplus`; `ProofPhase/Unified/Encoder.lean`, `selfdual_cost` | none |
| II.10.4b | As a Moebius map of the Riemann sphere that matrix is a rotation by 180 degrees | classical | `docs/unified/GRH-LENS.md` 6.1 | none |
| II.10.5 | The half-turn is a symmetry of the description: it exchanges the pictures, fixes its axis, and does not turn an upper bound on one encoder into a lower bound on another | paper | `docs/unified/GRH-LENS.md` 6.3 | none |
| II.10.6 | Applications of the encoder: Yang-Mills (twist ratio is c; O1 is c above (mu - 1)/(mu + 1) for every outside); GRH (the Verblunsky step at each scale is c); NP vs coNP (the crossing label passes at factor 1 with a cutting-planes line, so the encoder explains resolution's cost but supplies none for strong systems) | paper | `docs/unified/ENCODER.md` 1, 2 | none |
| II.11.1 | Running systems (states, step, factor in [0, 1], mass, ledger law) form a category whose terminal object is the space of ledgers; every running system has exactly one map into it; the ledger theorems hold on every one | Lean | `ProofPhase/ETM/RunSys.lean`, `RunSys`, `Hom`, `exists_unique_hom`, `univIsTerminal`, `RunSys.carry`, `RunSys.contract` | none |
| II.11.2 | The settle theorem: in the contraction class (every factor at most theta, e^delta theta < 1, equivalently a cost above the floor) the run reaches balance within epsilon by the explicit computable step bound ceil(M q/(eps (1 - q))) + 1 (cross-reference to XI.2a, not counted twice) | (cross-reference) | `ProofPhase/ETM/Machine.lean`, `Contracting`, `contracting_iff_costAboveFloor`, `balanceBound`, `balanceBound_ge`, `reaches_of_contracting`, `reaches_iff_bounded`, `reaches_of_contracting'` | none |
| II.11.3 | The edge: the lossless machine that runs every partial recursive content lies outside the contraction class and its balance problem is undecidable; its truth value exists classically but is not computable (cross-reference to XI.2b, not counted twice) | (cross-reference) | `ProofPhase/ETM/Machine.lean`, `etm`, `etm_universal`, `etm_not_contracting`, `etm_balance_undecidable`, `etm_truth_edge`, `etm_edge` | none |
| II.12.1 | The API (`ProofPhase.API`) is a facade with one structure per concept (running system, settle bound, edge, chain, margin, encoder, uncertainty, problem card, `OpenStep`, `External`); slots are transparent hypotheses, never axioms | Lean | `ProofPhase/API.lean`; `docs/unified/API.md` 2 | none |
| II.12.2 | Adding a problem takes seven steps (copy the template, write the input, fill a running system or chain and check the ledger inequality, write the open step, call the free theorems, add an uncertainty, state the card) | paper | `docs/unified/API.md` 3 | none |
| II.12.2b | The three cards of Parts III to V are `Problem`s, each proved "open step gives conclusion" (cross-reference to X.27, not counted twice) | (cross-reference) | `ProofPhase/API/YangMills.lean`, `API/GRH.lean`, `API/NP.lean` | none |
| II.12.2c | The template's toy settles in 101 steps to 1/100 | Lean | `ProofPhase/API/Template.lean`, `toy_settle_101`, `ticksNeeded_correct` | none |
| II.12.3 | What runs: the settle count, the encoder factors on rational data and the ledger law on rational data are computable and decidable and proved right for the real system; the machine's step and balance test are primitive recursive; the real-valued structures and the undecidability are truth only | Lean | `ProofPhase/API.lean`, `szegoQ`, `elecQ`, `szegoQ_cast`, `elecQ_cast`, `PaysQ`, `PaysQ.pays`, `settle0`; `ProofPhase/ETM/Machine.lean`, `balanceBound`, `estep_primrec`, `halted_primrec` | none |
| II.12.4 | Every continuous character of G0's phase circle is z -> z^n for an integer n, so every label carried on it has integer charge | Lean | `ProofPhase/API/Phase.lean`, `chargeQuantisation`, `PhaseLabel.integer_charge`; `ProofPhase/General/GUCharge.lean`, `circle_char` | none |
| II.12.5 | The API proves no open step and adds no mathematics; it does not build a running system for you; interface-only arguments cannot settle P vs NP | paper | `docs/unified/API.md` 5 | none |
| II.13.1 | The arsenal is the set of transferable Lean results that need Mathlib, in `arsenal/` of the `im` repository, pinned to Lean and Mathlib v4.34.0; first modules `Arsenal.R136a1` and `Arsenal.BSD` | paper | `im` repository, `arsenal/README.md`, `arsenal/lean-toolchain`, `arsenal/lakefile.toml` | none |
| II.13.2 | `R136a1 "name" P` is `P` as a named hypothesis, never an axiom; a theorem that needs it takes it as a hypothesis | Lean | `im` repository, `arsenal/Arsenal/R136a1.lean`, `R136a1`, `R136a1.out` | none |
| II.13.3 | `arsenal/tools/lint.sh` (static, no network, no build) fails unless the toolchain is Lean v4.34.0 with Mathlib v4.34.0 the one requirement, every module imports only Mathlib or the arsenal, no module uses an escape hatch (code only), and every module is reached from `Arsenal.lean`; it lists every R136a1 part by name | paper | `im` repository, `arsenal/tools/lint.sh` (read; run for this draft: "lint: OK (3 modules; Mathlib v4.34.0 only; no escape hatch)") | run `tools/lint-selftest.sh` and `tools/check.sh` |
| II.13.4 | What can be transferred moves to the `im` repository and is used from there as a dependency (by repository, subdirectory and commit), never vendored | paper | `im` repository, `arsenal/README.md`, "Using it"; `docs/unified/API.md` 7 | none |

## Notes for the coordinator

1. **Cross-reference rows** (I.9b, II.11.2, II.11.3, II.12.2b) repeat statements whose home is elsewhere (II.13.2; XI.2a and XI.2b;
   X.27). XI.2a and XI.2b still describe the same theorems in the Outlook, so the settle theorem is stated twice in prose
   (Part II and the Outlook) but is one claim; if the Outlook is later shortened to point at II.11, move XI.2a and XI.2b here.
2. **Not run for this draft:** Gravity's own check (`evidence/tools/check.sh`), the arsenal's `lint-selftest.sh` and `check.sh`. Only
   `lint.sh` was run (static, a few seconds).
3. **`docs/findings.md` IF9** is cited as IM's own note cites it; the file was not read here.
4. **IM's attenuation theorem (I.10e)** is stated as open only because IM's source says it is not yet written; the notes of
   2026-11-24 describe grants as attenuating without that caveat.
5. **Vocabulary.** Part II sections II.9 to II.13 call the machinery "the form layer", as `docs/unified/API.md` does.
