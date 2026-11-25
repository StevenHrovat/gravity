# Release review of GUID v8: opus

Reviewer: opus-release. Commit reviewed: `f8e81f6` (branch `ccr-be614210-u4r7na`, pull request 37). Brief: the block of
`assembled-review-prompt.md`, used unchanged, with two additions: reproduction is part of the review (findings of kind
"reproduction"), and the new order of the parts (problems III to IX, the one assumption X, Appendix R) is checked for how it reads and
for references that point to the wrong place.

Read in this order: the PDF built from the commit (104 pages), then `draft/`, `CLAIMS.md`, `REPRODUCE.md`, spot-checked Lean, and
only then the earlier records (`final-opus.md`, `final-fable.md`, `consolidation.md`, and the stage-3b `consolidation-3b.md`). A
finding that an earlier record lists as fixed is reported only where the fix is incomplete, and says so.

## Findings

Severity: blocker / major / minor / typo. Kind: attack / readability / precision / efficiency / format / reproduction. Locations are
in `docs/paper/draft/` unless a path says otherwise.

| id | kind | sev. | location | the sentence | evidence or reason | fix in one sentence |
|---|---|---|---|---|---|---|
| R1 | format, reproduction | **blocker** | title page (`tools/paper-latex.py`, `\date`); `01-part-I-dmp.md:22`; `00-abstract-introduction.md:244` | "other repository files are named relative to `docs/`, at the commit printed on the title page"; "can be rerun from a clone of the repository" | The title page prints only "Draft 4, 2026-11-24": no commit (`guid-v8.tex` line 27, `\date{Draft 4, 2026-11-24}`). The PDF never names this repository: `grep -o "github.com/StevenHrovat/[a-z]*" guid-v8.tex` finds nothing; the only GitHub links are to others' repositories. A reader of the released PDF cannot find the code, the ledger or the guide that every [Lean], [certified] and [numerical] mark points to. | Print the repository URL and the commit on the title page and in "Reproducing it" (and the `im` repository URL beside "IM's arsenal"). |
| R2 | format (restructure) | major | `02-part-II-machine.md:5-14` | table header "IV Yang-Mills, V GRH, VI P vs NP, VII Navier-Stokes, VIII BSD, IX Hodge, X GU"; "the one-box test and the cards (II.4, II.5) by every part from IV to X" | Pre-reorder numbers (the table was added at stage 3b before the reorder, `consolidation-3b.md`, F22). After the reorder Yang-Mills is III and GU is IX; X has no card. Every column label in the PDF's first map of the paper is off by one. | Relabel the columns III to IX and write "every part from III to IX". |
| R3 | format (restructure) | major | `02-part-II-machine.md:215-216` | "What the test gives for each card is in III.12 (Yang-Mills), VI.6 (the model Navier-Stokes box), the box sections of Parts IV, V, VII, IX and X" | The box sections are IV.8, V.10, VII.8, VIII.8 and IX.8; Hodge (VIII) is missing and Part X has none. | List them by section: IV.8, V.10, VII.8, VIII.8, IX.8. |
| R4 | readability, format | major | throughout; e.g. `10-…:116` "(claim X.8)", `03-…:271` "(III.10e)", `03-…:47` "X.64a", `10-…:201` "(0.5; III.7)", `07-…:342` "(VII.5.1)", `08-…:299` "(VIII.5.1)", `06-…:312` "(VI.5.1)", `10-…:378` "(A.3j)", `04-…:188` "IV.0a" | claim labels used as cross-references | The PDF prints no claim labels and does not include the ledger, so a reader looking for "X.64" or "0.5" finds nothing; several labels collide with section numbers: claim X.8 sits in section X.2 while section X.8 is "What this part adds up to"; claims III.10c-e are in III.12 while III.10 is the readings section; "0.5" refers to the introduction, which has no numbered sections. The one assumption itself is cited as "X.64" in at least ten places. | Either print each claim's label where it is stated (a margin tag) or replace label references in the text with section references, keeping labels for the ledger. |
| R5 | readability | major | `00-…:82, 96, 111`; `03-…:417`; `07-…:295`; `11-outlook-settling-machine.md:8-60`; `13-appendix-r-readings.md:117` | "IM's `Arsenal.Rotation.Box`"; "IM is both sides"; "BSD is IM: a full subset of only derivations"; "a CMOS system that runs entirely in IM tokens"; "sends it out as GG"; "One interface to the outside: Milky Way" | "IM" is used from the introduction on, both as a repository and as a DMP concept, and is first defined in Appendix R.4 ("IM is the Interstellar Medium"); CMOS, GG, Milky Way and TTL are never defined; none is in the vocabulary table I.12, which the introduction names as the place for DMP words. A physicist or number theorist meets "IM is both sides" in III.10 with no way to read it. | Add IM (repository and DMP sense), GG, CMOS and Milky Way to I.12 with one plain meaning each, or keep them out of the body. |
| R6 | precision, attack | major | `12-appendix-a-validation.md:58-62` | "it is a surgery-theory question, and it is answered: published for `N = 3`, and for `N >= 4` by a surgery computation in this paper … For `N >= 4` it fails in both categories" | The same bullet then says the odd case is open ("**[open]** for odd N >= 5"), as do the introduction, X.4.4 and A.3k; the consolidation fixed the four other places (Fable F10) but not this sentence. As written the appendix claims a result for odd N >= 5 that the paper does not have. | Write "answered for N = 3 (published) and for even N >= 4 (a surgery computation here); odd N >= 5 is open". |
| R7 | efficiency, format | major | `02-…:317-338` (II.7); `07-…:92-94, 214-215`; `08-…:108`; `01-…:81, 131, 138`; `02-…:488`; `09-…:194` | "Seven runs of 2026-11-24 are recorded … The last quick run, at the release commit of this draft (`897ef5c` …) … a further quick run at `db9fbc7` … a last quick run at `d0257ab` … The last, after `General/SUNHandOver.lean` was added"; "the stage-2 part review R6 ran `#print axioms`"; "(The notes say "below 100"; the source checks up to 59, and this part follows the source.)"; "(the author, 2026-11-23)"; "The first author's decision (2026-11-24)" | Process history the reader does not need, left after the stage-3b fix that reports it done (Fable F39). II.7 is a run log of about 350 words, and its "release commit of this draft" is not the last run it lists, so the reader cannot tell which commit the re-check covers. The VII.3.8 parenthesis is a note to the authors. | Cut II.7 to one paragraph naming the last run's commit and its numbers with a pointer to `REVIEW.md`; delete the notes-versus-source remark, the review-round names and the dates of quotes. |
| R8 | reproduction | minor | `docs/paper/REPRODUCE.md`, "What you need" and the venv paragraph | "Python 3.10 or later, with `pip install -r docs/paper/requirements.txt` … for the ledger check, the LaTeX source, the certificates, the numerics"; "the clean-clone test of this guide stopped there" | `tools/reproduce.sh paper` ran to "reproduce: OK" on a fresh clone in WSL Ubuntu 24.04 with the system Python 3.12 and no pip and no packages (1.5 s; `wrote guid-v8.tex: 14 chapters, 210 references`). The packages are needed for `certs` and the numerics only; the venv hurdle the guide describes blocks nothing for `paper`, `evidence` or `lean`. | Say per stage what it needs: `paper` plain Python 3, `certs` python-flint (and the venv steps there). |
| R9 | reproduction | minor | `REPRODUCE.md`, "If something fails"; `docs/mass-gap/formal/sync-build.sh:16` | "`lake update` must not be run" | `sync-build.sh` runs `lake update && lake exe cache get` itself on the first build, because no `lake-manifest.json` is committed (`git ls-files docs/mass-gap/formal` lists none). A careful reader sees the script do what the guide forbids. | Commit the manifest the logs were made with, or say that the first build runs `lake update` once and later runs must not. |
| R10 | reproduction | minor | `REPRODUCE.md`, "Checking one claim" | "look it up in the axiom log of its module … The modules each axiom log covers are named at the top of its script" | A reader must open up to 26 scripts to find the log. The example also works only after the `lean` stage has built `~/gravity-formal`, which the section does not say. | Give `grep -l '<declaration>' docs/unified/*axioms*.log` and say the example needs the `lean` stage first. |
| R11 | reproduction | minor | `REPRODUCE.md`, "What you need" and the stage table | "Linux, macOS, or Windows with WSL 2 … (the scripts are bash)" | Verified here: `paper` (with MiKTeX: PDF, 104 pages, no warnings beyond three sub-point overfull boxes) and `certs` (the three RESULT lines equal the logs, 71 s in all) run from Git Bash on Windows. Running `paper` rewrites the tracked `guid-v8.tex` and `guid-v8.pdf`, so a clone shows modified files afterwards (on Windows the `.tex` differs only in line endings). Timings: `evidence` took 7 s with the toolchain present (guide: "a few minutes"), `certs` 71 s for all three supports (guide: "about a minute per support"). | Add one line that Git Bash suffices for `paper` and `certs`, one that `paper` rewrites the tracked PDF, and the measured times. |
| R12 | format (restructure) | minor | `docs/paper/OUTLINE.md`; cited at `09-part-IX-gu.md:9` and `10-…:315` | "release criterion (`OUTLINE.md`)" | OUTLINE.md still has the old order (Part III the one assumption, Parts IV to X the problems, Part XI the Outlook). The paper sends the reader there for the release criterion. | Update OUTLINE.md to the new order, or state the criterion in IX.0 and drop the pointer. |
| R13 | format (restructure) | minor | `04-part-IV-grh.md:128-132` | "As in Part X, the support a is the half-width … They are not comparable with the certified lower bounds of Part X (X.65)" | The certificate and the definition of a are now stated in IV.1 ("The certified first box, as stated"); the sentence sends the reader forward six parts for what is two pages back. | "As in IV.1 … the certified lower bounds of IV.1". |
| R14 | format (restructure) | minor | `10-…:230`; `10-…:46` | "1.5e-9 at 0.60, 6.4e-13 at 0.69; IV.3"; "(`General/SUNTwistWilson.lean`, `sunZtw_pos`; III.1.6)" | The certified margins are in IV.1, not IV.3; III.1.6 is the SU(2) strict flip, the SU(N) positivity is III.3 (claim III.3.1b). | Point to IV.1 and to III.3. |
| R15 | readability (restructure) | minor | `01-part-I-dmp.md:215`; `10-…:59`; `11-…:3` | "I.12 The vocabulary in one table" after I.7; "(Part XI)"; "This appendix records a concept" | I.8 to I.11 moved to Appendix R, leaving a numbering gap the table of contents shows; the Outlook is called "Part XI" in X.1 and "this appendix" in its own header, and is neither. | Renumber I.12 as I.8; call the Outlook "the Outlook" everywhere. |
| R16 | readability | minor | `06-part-VI-navier-stokes.md` | section order VI.5 open step, VI.6 box, VI.7 readings, VI.8 close | Every other problem part ends at its box (III.12, IV.8, V.10, VII.8, VIII.8, IX.8), as the introduction's Plan says ("each ends at its card and its box"); Part VI puts the box in the middle. | Move VI.6 to the end of Part VI. |
| R17 | precision | minor | `00-…:48-49` (abstract) | "Proved in Lean without it: … the classical explicit formula for all nontrivial zeros of zeta" | IV.1.5 and the introduction add that the real-place term is a line integral at Re s = c > 1 whose identification with Weil's closed form is not in Lean; the abstract, the one place many readers stop, drops this. | Add "(its real-place term as a line integral, not yet identified with Weil's)". |
| R18 | precision | minor | `04-part-IV-grh.md:19` | "Tao's post … reports that the same author has also generated a Lean-only proof of a Generalized Riemann Hypothesis" | "The same author" has no antecedent: the preceding bullets name a library, the Lean FRO and the Mathlib Initiative, not an author. | Name the author of the library once. |
| R19 | precision | minor | `04-part-IV-grh.md:215`, heading of IV.4 | "Each face would close the others' consequences; they are not shown to be equivalent"; "eight equivalent-looking faces" | A referee cannot tell what is claimed between the faces. The proved relations are the two lines under the table (faces 2, 3 imply 1; 5, 6, 8 are one quantity). | Replace with "Each face, if built, would give the open step; the relations proved among them are the two below." |
| R20 | precision, attack | minor | `13-appendix-r-readings.md:166-167` | "a fixed point of sha256, which no one can compute **[classical]** (by the hash's design)" | II.3 states that one-wayness is "a well-tested assumption rather than a theorem" and that the existence of one-way functions is open; R.6 marks the same kind of hardness [classical] as if proved. | Mark it as the standard assumption on sha256, not as a classical fact. |
| R21 | precision | minor | `00-…:115`; `03-…:126` | "unconditionally for the SU(N) twisted Wilson partition functions"; "the rate holds with no further hypothesis" | `sun_handover` (`General/SUNHandOver.lean:29-30`) still takes `hβ : β ≠ 0`, `hT : Even T` and a nontrivial sector `hk : k ≠ 0`; what is removed is only the hypothesis 0 < Z_tw. | Say "with no hypothesis on Z_tw (beta != 0, even time extent, a nontrivial sector)". |
| R22 | precision | minor | `10-…:362-364, 386` | "**[Lean, conditional]** on X.64" | Not one of the eleven marks or qualifiers the introduction defines; the defined form of a Lean theorem with a named hypothesis is "[Lean] (from X)", and [conditional] marks the use. | Write "**[Lean]** (from `SharedGate`)", and [conditional] where the conclusion is used. |
| R23 | precision | minor | `10-…:7`; `10-…:590-591`; `03-…:361` | "Parts III to IX each end at a **card**: an input, a proved structure, and exactly one named open step"; "the abstract's list of what remains shrinks by one item"; status "project rule" | GU has no card (IX.2), Navier-Stokes has three, BSD three, Hodge five (II.5.2); the list of what remains is in the introduction, not the abstract; "project rule" is not one of the eleven marks. | "each ends at its cards and its box"; "the introduction's list"; mark III.7.3 [paper] (a design rule), as claim 0.5 is. |
| R24 | readability | minor | headers of `01`, `02`, `04` to `10` vs `03-…:3` and `CLAIMS.md` legend | "Lean paths relative to `docs/mass-gap/formal/ProofPhase/`" vs "Lean paths relative to `docs/mass-gap/formal/`" | Part III and the ledger use one base, the other parts another, so `Flip/Strict.lean` and `ProofPhase/Flip/Strict.lean` name the same file. | One base for the whole paper and the ledger. |
| R25 | efficiency | minor | `00-…:176-178`; `06-…:324-325`; `07-…:324-325`; `08-…:280`; `10-…:590-592` | "the change to this paper would be one row of the ledger, one verdict line of this part and one item of the introduction's list of open steps" | The same sentence five times. | Keep it once, in X.8. |
| R26 | readability | minor | `11-…:42` | "the decidable half of the Existence Turing Machine (Part II and `docs/unified/ETM.md`)" | The name appears nowhere else in the paper; Part II calls the object the machine, the settling machine and the universal machine. | Use Part II's name. |
| R27 | format | typo | `12-appendix-a-validation.md:3`; `00-…:3-4`; `01-…:168-169` | "Gathered from draft 3's Part V, section 6 …"; "the results that need the one assumption (Part III)" ; stray indent "   with its own mark" | Leftovers in the draft headers (stripped from the PDF, visible on GitHub): the old Part number of the one assumption and the history of Appendix A. | Update the header to Part X; drop the draft-3 provenance. |

## A. Attack: what was checked and found to hold

Lean declarations the abstract and the introduction's list rest on exist at `f8e81f6` and say what the sentence says (read in the
source): `onebox_certificate` (`ETM/Rotation.lean:125`, wrapping IM's `Arsenal/Rotation.lean:99`: correct at the start and kept by
the step gives `DMPComplete`); `cardBox_complete_iff` (`ETM/CardBox.lean:90`: the card box is DMP-complete iff `Pr.Open i`, a
restatement, as the paper says); `fineOneBox_iff_complete`, `o1_iff_complete`, `ns_not_complete` (`ETM/RotationInstances.lean`);
`sun_handover` (with the hypotheses of R21); `explicit_formula_of_smooth`; `cross_any_system_of_falsify`; `etm_edge`;
`onebox_positive`; `su2_Ztw_lt_Z`; `liftCPConst_iff_extract`; `constGadget_crossingCost`; `yang_mills_assembly_onebox`;
`grh_box_iff`; `weil_bound`; `scale_certificate`; `g2_rigid_of_one_assumption`; `two_add_two_ne_five`; `mordellWeil_of_weak` (IM,
`Arsenal/BSD/Algebraic.lean:71`, at the pinned commit `b01adbd`).

Reproduced (commands and outputs in the reproduction section below): the evidence gate prints `OK 285 theorems`; the three
certified margins rerun to the committed RESULT lines; all 26 axiom scripts of the `lean` stage rerun to the committed axiom
lines, standard axioms only, no `sorryAx`; the ledger gate passes (669 claims, every label resolves).

Arithmetic checked by hand, all correct: log(8/7) = 0.134 and -log(1 - 0.197) = 0.22 (III.4); (mu - 1)/(mu + 1) = 0.743 at
mu_4 = 6.77 and the twist ratio 0.742 at F_e = 1.91 (III.5.4, III.0); the saturation thresholds 0.42, 0.44, 0.15 (III.6); F_e from
r at L = 4, 6 and beta = 3.5 (III.7.1: 0.91, 2.59, 0.036); 8 pi^2 = -4 zeta(2)/zeta(-1) (III.7.4); the one-loop slope
4 pi^2/g^2 = (11/3) log(1/(a Lambda)) and 11/(6 pi^2) in the Lean beta (III.5.5, III.0); the window exponents 1 - 2 alpha and
5 alpha - 2 (VI.3.1); the 2t + 3d + q column and Q = (3s + q)/6 (IX.3.1); the BSD numerics for 32a2 and 37a1 against the known
values, including 5P = (1/4, -5/8) (VII.3.8); Weil's bound from the quadratic form (VIII.3.4); the four ring links of R.5; the
surgery dimension count N^2 - 1 odd for even N, divisible by 8 for odd N (A.3).

Contradictions found between parts: R6 (A.3 against the introduction and X.4.4), R20 (R.6 against II.3). Between the paper and
`CLAIMS.md`: none found beyond R24 (path bases); the gate's label check passes.

External claims dated after this reviewer's knowledge (the Lean RH library of November 2026, the VP != VNP posting, the two
Navier-Stokes blowup claims, the Yang-Mills submission, arXiv numbers 26xx.xxxxx): unknown to this reviewer; each is marked
[external] or [external, unverified] with its scope, and none is used as a step of a proof here.

## B. Readability

The reorder works. Reading III to IX first and X after them is easier than the earlier order: each problem part is
self-contained, and Part X now compares cards the reader has seen. The introduction's "The test in one page" gives the reader the
words before Part II. What still loses a reader: the undefined IM/GG/CMOS vocabulary (R5), claim labels that cannot be followed in
the PDF (R4), and the Part II map with the old numbers (R2). A number theorist can find the GRH status in IV.0 and IV.4; a
complexity theorist in V.0 and V.6; a geometer in VII.0, VIII.0 and VIII.5; a topologist in A.3 and A.5 (after R6); a logician in
II.3 and X.4.3. The physicist has to get through III.0's O2 bullet, which mixes the open lower edge with the reading that places it
in the one assumption; it holds, but it is the densest paragraph of the part.

## C. Precision

Status marks are used as the introduction defines them, with the exceptions R22 ("Lean, conditional") and R23 ("project rule").
The [conditional] mark now appears where the one assumption is used (X.4.4, X.6, X.69c; the stage-3b fix of the earlier blocker
holds). Vague sentences: R18, R19, R23.

## D. Efficiency

Candidates, with an estimate of what can go: II.7 to one paragraph (about two thirds of a page); the repeated "one row of the
ledger" sentence (R25, four sentences); process remarks (R7, about half a page); the readings bullets of VI.7 that repeat X.4.4's
"expected negative" nearly word for word (about a third of a page). Together about two pages of 104. Nothing essential is too short,
except the Outlook's vocabulary (R5), which is too short to be read at all.

## E. Abstract and introduction

The abstract says plainly that no problem is solved, names the one assumption and its five cards, and lists what is proved without
it; R17 is the one dropped qualifier. "Results and open steps" matches the parts, including the validation bullet (rigid for N <= 3,
even N >= 4 not rigid, odd N >= 5 open), which A.3 contradicts once (R6). The Plan matches the new order except that Part VI does not
end at its box (R16).

## F. Format

The PDF builds cleanly from the commit with MiKTeX: 104 pages, no undefined reference, three overfull boxes below 1.2 pt. The
regenerated `guid-v8.tex` equals the committed one (WSL: byte-equal; Windows: line endings only). The cross-reference check: every
section reference in `draft/` resolves either to a heading or to an inline result label or a ledger label (script over all 14
files; 152 headings, 757 ledger rows, 788 folded labels). What does not resolve for a reader is R1 (no repository, no commit) and
R4 (ledger labels). The bibliography is a numbered standard list with author-year links; not re-audited beyond its use here.

## Reproduction, step by step as a new reader

On a fresh clone of the branch in WSL (Ubuntu 24.04, Python 3.12 without pip, elan installed, Lean v4.34.0 toolchain present), and
on Windows with Git Bash, Python 3.14 with python-flint 0.9.0, and MiKTeX:

1. `python3 -m venv .venv`: fails without `python3-venv`, as the guide warns; no sudo used. Not needed for step 2 (R8).
2. `tools/reproduce.sh paper` (WSL): `scrub-scan: clean`, `counts: … total 669`, `claims-check: OK`, `paper-gate: OK`,
   `wrote guid-v8.tex: 14 chapters, 210 references`, "pdflatex not installed …", `reproduce: OK`, 1.5 s; the clone stays clean.
3. `tools/reproduce.sh paper` (Git Bash with MiKTeX): `Output written on guid-v8.pdf (104 pages, 1288492 bytes)`, `reproduce: OK`,
   18 s; the tracked PDF and `.tex` are rewritten (R11).
4. `tools/reproduce.sh evidence` (WSL): `OK 285 theorems, none resting on more than propext, Quot.sound, Classical.choice`,
   `reproduce: OK`, 7 s.
5. `tools/reproduce.sh certs` (Git Bash): `ok a = 3/5 … [1.500e-9 +/- 2.01e-13]`, `ok a = 13/20 … [3.398e-11 +/- 2.01e-15]`,
   `ok a = 69/100 … [6.417e-13 +/- 3.01e-17]`, `reproduce: OK`, 71 s.
6. `tools/reproduce.sh lean` (WSL, `FORMAL_DST` a copy of an existing build folder at the same pins): 26 `ok` lines, each "standard axioms only, same as the committed log",
   `reproduce: OK`, 16 min 46 s on the seeded build folder (a cold first build was not timed here).
7. `tools/reproduce.sh kernels`: not run (hours, by the guide).

## The five changes that would most improve the paper for a reader

1. Put the repository URL and the commit on the title page and in "Reproducing it" (R1).
2. Fix the restructure leftovers in Part II's map and box list, and the forward and stale pointers (R2, R3, R12 to R15).
3. Make claim references followable in the PDF, or replace them with section references (R4).
4. Define IM, GG, CMOS and Milky Way where they are first used, or keep them out of the body (R5).
5. Correct A.3's "for N >= 4" (R6) and cut the process history out of II.7 and Part VII (R7).

Findings: 27 (blocker 1, major 6, minor 19, typo 1). By kind (a finding with two kinds counts under its first): format 7,
precision 8, readability 6, reproduction 4, efficiency 2. The attack findings, R6 and R20, are counted under precision; of the
format findings, R2, R3 and R12 to R14 come from the restructure (with R15 and R16 under readability).

Release-blocking findings: 1
