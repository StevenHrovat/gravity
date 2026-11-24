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

## Stage 4. The owner's gate

The owner reads the consolidation and approves. Any sentence about the reviews in the personal note is made true before release.
The paper leaves the draft stage only under the release criterion (`OUTLINE.md`): every open step closed, so that "General" and
"Grand Unified" both hold. Nothing is sent or posted on the owner's behalf.

## Record

| Stage | Date | What | Result |
|---|---|---|---|
| Claims audit (stage 2, early) | 2026-11-24 | `CLAIMS-AUDIT.md`, one pass over every row | 83 rows folded, overclaims narrowed, applied |
| Independent re-check | 2026-11-23, 2026-11-24 | `docs/unified/INDEPENDENT-CHECK.md` | passed |
