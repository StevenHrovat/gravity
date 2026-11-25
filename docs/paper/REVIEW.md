# Review process for GUID v8 and its related work

Set up 2026-11-24 on the owner's go ("Yes, please do"), adapted from the GUID v7 process (`docs/guid/final-verification-prompt.md`,
`docs/guid/consolidation.md`). The goal: every sentence of the paper is true, backed and no stronger than its evidence, and every
reading is marked as one, before the paper leaves the draft stage.

**Scope.** The paper (`docs/paper/draft/`, `CLAIMS.md`, `OUTLINE.md`); the Lean in this repository (`docs/mass-gap/formal/`, the
`ProofPhase` library, standard axioms only) and in IM's arsenal (`StevenHrovat/im`, `arsenal/`, pinned in
`docs/mass-gap/formal/lakefile.toml`); the notes the paper cites (`docs/unified/`, `docs/mass-gap/weak-coupling/PREP.md` for the
owner's readings). DMP itself (`vendor/dmp`) is the owner's and is never reviewed for change, only quoted.

## Stage 1. Mechanical, on every change (the coordinator)

Nothing is pushed unless all of these pass. `tools/paper-gate.sh` runs the local ones in one go.

| Check | Command | Pass |
|---|---|---|
| Evidence gate | the gate script (`evidence/tools/check.sh` on the pushed branch) | `OK 285 theorems, none resting on more than propext, Quot.sound, Classical.choice` |
| Scrub | `LC_ALL=C.UTF-8 bash tools/scrub-scan.sh` (stage new files first: it reads tracked files only) | `scrub-scan: clean` |
| Ledger | `python tools/claims-check.py` | no duplicate IDs, every label in the paper resolves, counts printed match the counts table |
| Machine and test modules | `bash docs/unified/rotation-axioms.sh` in WSL (`ym-replay`) | every declaration of `ETM/Rotation*.lean` and `ETM/G2Rigidity.lean` on the standard axioms; no escape hatch |
| IM | the `verify` workflow on every IM pull request; `arsenal/tools/check.sh` before opening it | CI green; `OK n declarations` |
| Independent re-check | `bash tools/independent-check.sh quick` in WSL | replay and nanoda pass; `NONSTD_AXIOMS []`; stamp matches |

The evidence gate does not build `docs/mass-gap/formal`; the machine and test modules, and every other module the paper cites,
are covered by the independent re-check and the axiom logs next to the notes.

## Stage 2. Part reviews (fresh threads, adversarial)

One thread per group of parts, each started fresh with `review/part-review-prompt.md` and its group filled in. Groups:

| Group | Parts |
|---|---|
| R1 | Front matter, Part I (DMP), Part XI (Outlook) |
| R2 | Part II (the machine and the tools) |
| R3 | Part III (the one assumption and the rigid start) |
| R4 | Part IV (Yang-Mills) |
| R5 | Parts V and VI (GRH, P vs NP) |
| R6 | Parts VII to X (Navier-Stokes, BSD, Hodge, GU) |
| R7 | Appendix A (validation) and the notes it rests on |

Each thread checks every ledger row of its group: the Lean names exist and state what the text says; classical and external
citations match their sources; readings are not presented as mathematics; nothing is stronger than its evidence; the status mark is
right. Output: `docs/paper/review/part-RN.md` in a draft pull request titled `[review RN] ...`, a findings table (id, severity,
location, sentence, evidence, proposed fix) and a section per checked item so that absence of findings is visible. Threads never
edit the paper. Model: Sonnet by default (the owner's usage rule); a group may go to Opus where the mathematics is hard (R4, R7), on
the coordinator's judgment.

When: after the boxes for GRH, P vs NP, BSD, Hodge and GU are written, so the reviews see the final content.

## Stage 3. Final fault verification (two independent verifiers, then one consolidation)

On the release candidate: the LaTeX build with one bibliography. Two threads receive `review/final-verification-prompt.md`
unchanged, each filling in its own name; neither reads the other's findings until both are in. Models: as the owner decides at the
time (v7 used Fable High and Opus High; **Fable needs the owner's approval in advance, every time**). Then one consolidation pass
(`review/consolidation.md`) merges both with the part reviews and corrects the paper once.

**Stage 3b. Review of the assembled paper (the owner's request, 2026-11-24).** After the consolidation, the assembled paper (the
LaTeX build of the consolidation commit) is reviewed once more, by fresh reviewers who have not seen it: an attack on every claim,
and an evaluation of readability, precision and efficiency of delivery in the actual content. Their findings are fixed in one pass,
then stage 4 follows; the owner reads his personal note last, on the fixed paper.

## Stage 4. The owner's gate

The owner reads the consolidation and approves. Any sentence about the reviews in the personal note is made true before release.
The paper leaves the draft stage only under the release criterion (`OUTLINE.md`): every open step closed, so that "General" and
"Grand Unified" both hold. Nothing is sent or posted on the owner's behalf.

## Record

| Stage | Date | What | Result |
|---|---|---|---|
| Claims audit (stage 2, early) | 2026-11-24 | `CLAIMS-AUDIT.md`, one pass over every row | 83 rows folded, overclaims narrowed, applied |
| Independent re-check | 2026-11-23, 2026-11-24 | `docs/unified/INDEPENDENT-CHECK.md` | passed |
| Independent re-check, quick, draft 4 | 2026-11-24 | at `1d71a05`: stamp matches; replay of changed modules fail=0 (incl. `Arsenal.Rotation`, `Arsenal.Rigidity`); axiom audit `NONSTD_AXIOMS []`; nanoda 105,150 declarations, no typechecker errors (one pretty-printer error, not a check failure) | passed |
| Bibliography | 2026-11-24 | `docs/paper/references.md`: 92 works, each looked up on its Crossref, arXiv, dblp or publisher record by five verification agents (haiku), merged strictly by the coordinator | 73 checked, 14 partly checked, 5 not yet identified (Grothendieck 1969, Lovasz 1975, Mordell 1922, Weil 1948, Weil 1952); task R of stage 3 re-checks every entry |
| Stage 2, part reviews R1-R7 | 2026-11-24 | seven fresh Sonnet threads; reports `review/part-R1.md` to `part-R7.md` (gravity #39-#45); 14 blocking, about 40 major findings | all blockers and majors fixed by the same threads (#46-#52) and merged; the root-chain blocker on the owner's decision (one-way pin, mutual honesty his reading); open after the fixes: the references for gap-to-mixing and the heat-bath gap (II.10.3), 63 partly checked and 2 unidentified bibliography rows, and the personal note's factual sentences (the owner's) |
| Stage 3, final verification | 2026-11-24 | Opus and Fable on the release candidate `f4592e3`, independently; `review/final-opus.md` (gravity #53), `review/final-fable.md` (#54) | 7 blockers (3 Opus, 4 Fable, overlapping), about 55 other findings |
| Stage 3, consolidation | 2026-11-24 | `review/consolidation.md`: every finding with its action, the owner's decisions and readings of the day | all blockers and findings acted on; open by design: the personal note's sentences (the owner's) |
| Independent re-check, quick, release | 2026-11-24 | at `897ef5c`: stamp matches; 15 changed modules replayed, fail=0; axiom audit `NONSTD_AXIOMS []`; nanoda 74,295 declarations, no typechecker errors (one pretty-printer error, not a check failure) | passed |
| Independent re-check, quick, after the essence | 2026-11-24 | at `db9fbc7`: stamp matches; 2 changed modules (`ETM.ETM`, `ETM.Essence`) replayed, fail=0; `NONSTD_AXIOMS []`; nanoda 15,257 declarations, no typechecker errors | passed |
| Stage 3b, review of the assembled paper | 2026-11-24 | Opus and Fable on `68f5c48`, independently; `review/assembled-opus.md` (gravity #55), `review/assembled-fable.md` (#56) | 4 blockers (1 Opus, 3 Fable), 68 other findings |
| Stage 3b, fixes | 2026-11-24 | `review/consolidation-3b.md`: every finding with its action; the author line by the owner | all blockers fixed (one in Lean); restructured on the owner's decision (problems III to IX, the one assumption X, Appendix R for readings and neighbours); F40 work plans and m1 not done |
| Independent re-check, quick, after stage 3b | 2026-11-24 | at `d0257ab`: 18 changed modules replayed, fail=0; `NONSTD_AXIOMS []`; nanoda 75,100 declarations, no typechecker errors; evidence gate with pin check OK 285 | passed |
| Independent re-check, quick, after the reorder | 2026-11-24 | 3 changed modules (label strings only) replayed, fail=0; `NONSTD_AXIOMS []`; nanoda 72,355 declarations, no typechecker errors; rotation axiom log 125 declarations | passed |
| Independent re-check, quick, after the SU(N) hand-over | 2026-11-24 | the new module `General/SUNHandOver.lean` replayed, fail=0; `NONSTD_AXIOMS []`; nanoda 39,911 declarations, no typechecker errors | passed |
| Clean-clone reproduction | 2026-11-24 | a fresh clone at `7beae40` in a fresh WSL folder, a fresh Mathlib cache: `tools/reproduce.sh all`. Paper and evidence (OK 285) passed; all 26 axiom scripts rebuilt and matched their committed logs line by line (1,775 axiom lines, standard axioms only; the comparison was then fixed to read both log formats and rerun on the outputs); 27 minutes. The certificate stage needs `python3-venv` on Ubuntu (now in REPRODUCE.md) and passed on Windows | passed, one guide fix |
| Certificates rerun | 2026-11-24 | `tools/reproduce.sh certs`: the three RESULT lines equal the committed logs (1.500e-9, 3.398e-11, 6.417e-13) | passed |
| Release review | 2026-11-24 | Opus at medium effort on `f8e81f6`: attack, delivery and reproduction as a new reader (`review/release-opus.md`, gravity #57); its own runs of `paper`, `evidence`, `lean` (26 scripts) and `certs` passed | 27 findings (1 blocker: no repository or commit in the PDF), all acted on: the title page names the repository and the source commit; claim labels link to the ledger; Part II's map, the box list and the pointers after the reorder; A.3 for odd N; II.7 in one paragraph; dates and review names out of the body; IM, CMOS, Milky Way, GG and TTL in I.8; the vocabulary table renumbered I.8; Part VI ends at its box (VI.8); one Lean path base; the guide per stage with measured times |
| IM arsenal, full check | 2026-11-24 | `arsenal/tools/check.sh` at the pin `b01adbd`: lint, build against Mathlib, kernel axiom report | passed, 223 declarations, standard axioms only |
| Bibliography, stage 3 | 2026-11-24 | `references.md` corrected and completed from three lookup rounds (haiku), merged by the coordinator | 195 works: 123 checked, 72 partly checked, none unidentified; DOIs for 26 rows |
| Bibliography, completed | 2026-11-24 | after the first author's approval: the 67 rows still partly checked re-read by the coordinator on registry records (Crossref, the arXiv API, zbMATH Open), by script, no agents; corrections from the records (Weil 1948 is series 1041; Weil 1952 found in its Lund volume; the Dobrushin-Shlosman book title; the five Clay descriptions with their printed pages in the 2006 volume; full names, journal versions and DOIs where the records give them) | 210 works, all checked; remarks on content not read stay in the last column |
| Windows reproduction | 2026-11-24 | `vendor/** -text` in `.gitattributes`: the vendored DMP keeps its exact bytes on a Windows checkout | `tools/check-pin.sh` passes in a Windows checkout (it failed before on converted line endings) |
| Draft 5, the full turn | 2026-11-25 | the first author's reading of n! as a full turn (dmp#25, 2026-11-25) generalised into one tool: IM `Arsenal/FullTurn.lean` (im#15; `arsenal/tools/check.sh` OK, 278 declarations, standard axioms only), the SU(N) hand-over over all N sectors (`General/SUNFullTurn.lean`, `sunprimes-axioms.log` 176 declarations; all 26 axiom scripts rerun from a fresh clone of `ca43521`, every log the same), the hash collision theorems (`ETM/Essence.lean`); the draft in its own folder `docs/paper/D5` (Draft 4 unchanged in `docs/paper`; the tools take the draft name), text in II.2.7, II.13.3, II.13.4, III.3.1c, III.5.4d, IV.1.5c, VII.3.5f, R.5c, R.6a, R.7; six new references read on Crossref (Grover 1996, Shor 1997, Brassard-Hoyer-Tapp 1998, FIPS 180-4, Bryant 1987, Harvey-Lawson 1982) and the duplicate Georgi-Glashow row merged | ledger 681 rows; paper gate OK for D4 and D5 |
| Draft 5 review | 2026-11-25 | Opus subagent at medium effort on `d66ff2a` (IM `e84f78c`), fresh clones; `review/draft5-opus.md`; its runs of `paper D5` and `paper` passed; Draft 4 found untouched | 0 blockers, 3 major, 11 minor; all fixed (IM pinned to `f7661fc`; `sunprimes-axioms.log` 176 and `rotation-axioms.log` 127 declarations rerun) |
| Draft 5, the headline | 2026-11-25 | the first author's headline: every observable system has a one-box description, DMP-complete exactly when its claim holds, with a route to the proof certified universally once shown; IM `Arsenal/Observable.lean` and `full_turn_slope` (im `c8707b4`; `arsenal/tools/check.sh` OK, 309 declarations); D5 abstract, introduction and II.4.1 rebuilt around it; R.8 (derivations as slopes; what a turn can undo); references 217 (Kitaev 1995, arXiv record) and 218 (Lee 2012, Crossref) | ledger 684 rows; paper gate OK |

## Citation items for the part reviews (from the bibliography round, 2026-11-24)

Found while reading the sources; each is for the part review of its group to settle, not a silent fix.

* Year differs from the notes: Novikov (1964 on the page, cited 1965); Seregin, Comm. Math. Phys. 312 (2011 on the Crossref record,
  cited 2012); Presburger (published 1930, cited 1929); the Super-Kamiokande and MoEDAL arXiv years against their journal years.
* Source may not carry the row's claim: Grothendieck 1958 ("Sur une note de Mattuck-Tate") cited for the Hodge index theorem;
  Hastad 1998 (shrinkage exponent) cited for an AC0[p]-Frege statement; Minahan-Ramond-Warner 1990 for the B-L content of its row;
  the monopole row cites MACRO and IceCube but the source read is a MoEDAL search.
* Which work is meant: Martinelli-Olivieri 1994 (parts I and II); Dyer-Goldberg-Jerrum (2008 CPC) against Hayes (2006); Wall (1970
  original or the 1999 second edition).
* Not yet identified: Grothendieck 1969, Lovasz 1975 (likely Erdos-Lovasz, the local lemma), Mordell 1922, Weil 1948, Weil 1952.
