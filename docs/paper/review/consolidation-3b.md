# Stage 3b: fixes after the review of the assembled paper

Two independent reviews of the assembled paper at `68f5c48`: `assembled-opus.md` (gravity #55: 26 findings, 1 blocker) and
`assembled-fable.md` (gravity #56: 46 findings, 3 blockers). Brief: `assembled-review-prompt.md`. The coordinator verified the
blockers before fixing (F03 by reading `Proof/Crossing.lean`: the hypothesis asked for both directions of a toggle that no clause of
width 2 or more has, while the proof used one). Fixed in one pass on 2026-11-24, in the commits after `68f5c48`.

The section and claim labels in the tables below are those of the assembled paper (draft 4, before the reorder); the ledger table
"Draft 4 labels" maps them to the present ones.

## The first author's decisions

* Author line: "Steven Hrovat with Claude (Anthropic) during pressing" (title page); PDF metadata names the first author.
* Structure (decided by the first author, "Yes, restructure"): the problems come before the part that compares them. New order:
  I vocabulary, II machine, III to IX the seven problems (Yang-Mills, GRH, P vs NP, Navier-Stokes, BSD, Hodge, GU), X the one
  assumption, the Outlook, Appendix A validation, and a new Appendix R "DMP readings and neighbours" holding what no card uses:
  the old I.8 to I.11 (linter, excision, rights, IM's arsenal, now R.1 to R.4), the essence line (R.5) and the rotatable hash (R.6)
  (Opus M11; Fable F21, F26, F41). Every label was relabelled by one script, in the drafts, the ledger and the current Lean strings
  (`X.64`); the ledger's table "Draft 4 labels" maps the old labels. Nothing was deleted. "Appendix R", not B: "Appendix B" already
  names appendices of cited papers.
* Personal note: the first author's new sentence ("... turned into three, which revealed the MP-type, and let me generalize while
  sharing the credit with those that phrased the correct problem :D").

## Blockers

| Finding | Action |
|---|---|
| Fable F03 (crossing theorem on 3-CNF) | Lean: `cross_any_system_of_falsify` takes the direction the proof uses; `fixes_of_single` and `invisible_of_not_mem` prove both conditions for clause blocks; `cross_any_system` is now its corollary. II.14, VI.4 and ledger row II.14.5 cite the new form; the 3-CNF step is Lean |
| Opus B1, Fable F02 (the [conditional] mark never used) | **[conditional]** on every result that uses the one assumption (III.66, III.68a, III.68d, III.69b, III.69c, the tick paragraph of III.6, IV.0); IV.9.5b stays **[open]** (part of the assumption by a reading); the ledger legend now says what the introduction says |
| Fable F01 (a definition broken into a table) | the line no longer starts with a bar (`abs(c) <= 1`, typeset as the modulus) |

## Attack and precision

| Finding | Action |
|---|---|
| Opus M2, M4, M12; Fable F04 to F07, F09, F17 (abstract) | rewritten: six Clay problems, two in a neighbouring form, GU not a Clay problem; for most cards the box is the open statement itself; "certifiable" defined (the one-box certificate); the Yang-Mills reduction to one named criterion, uniform in spacing and volume; the explicit formula called classical; the first box enclosed in ball arithmetic given estimates argued in a note; the model Navier-Stokes box; 1,916 characters |
| Opus M1, Fable F11 (GRH and O1 "proved independent") | "What is new" and III.4.4: two abstract bounds on one sequence are independent; reading them as GRH's edge and O1 is the paper's identification |
| Opus M3 (GRH state) | V.0 cites Tao's post on the further GRH claim (scope unstated, not examined), marks the traced route "preliminary"; the bibliography entry has the source's own title |
| Opus M5, Fable F16 (DMP-complete with three meanings) | "DMP-complete" is the box property only; the first author's reading is "running" (III.4.4, III.70, VII.7, the introduction) |
| Opus M6, Fable F19, F30 (terms before definitions) | new section "The test in one page" in the introduction (running system, box, gate, marker, tick, DMP-complete, the one-box certificate, card, open parts, O1, the one assumption); I.12 gains the same words |
| Opus M7 (assumption before its content) | III.4.4 leads with the schema: seven instances, each named in Lean, then the reading |
| Opus M10, Fable F33 (runs and commits) | II.7: four runs, the last naming its commit; REVIEW Record adds the evidence gate with the pin check |
| Fable F08 (the Yang-Mills card's slot) | the card's slot is `YMOneBox` (chain model); `FineOneBox` is the assembly's hypothesis; their relation is prose (introduction, III.4.4) |
| Fable F10 (rigid "exactly" for N <= 3) | rigid for N <= 3, not rigid for even N >= 4, odd N >= 5 open, in all four places and in ledger rows A.3k, A.5i |
| Fable F12 (NP open step) | `CrossingCost` in II.5, the III.4.1 table and row III.64, VI.4.10 as the nearest target |
| Fable F13 (GRH instance) | III.4.4 says what the assumption asserts on the GRH card and that for zeta's model it is discharged by an external result |
| Fable F14 (O1 names four statements) | O1 is `FineOneBox`; the chain form, the path-counting number and the hand-over side are named as such in II and III |
| Fable F15 (beta of the simulations) | read from the code: standard beta = 4/g^2 (`w2/smalltorus.py`) |
| Fable F18 (two kinds of margin) | V.3 says what "support a" is and that its grid eigenvalues lie above the true margin, not comparable with the certified bounds |
| Fable F20 (the two boxes with content) | new IV.12 and VII.6 "The box in the one-box test", with `ymFac`, `nsFac`, the theorem names and the module |
| Fable F31 (explicit formula, real-place term) | V.1.5 and the introduction say the term is a line integral at Re s = c > 1, its identification with Weil's closed form not in Lean |
| Fable F35, F38 (draft, gates, MP-type) | one sentence on the draft and the release criterion; "release criterion" and "the existence assumption of the Millennium-Prize type" |
| Opus m1 to m13, Fable F32, F34, F36, F37, F42, F44, F46 | done (marks, labels, "simply connected", "Appendix A", one legend with "A + B" and "A / B", floor wording, P vs NP naming, docstrings relabelled, Tate sentence), except m1 (an unconditional SU(N) hand-over line in Lean: not added) and m4 (Part V rows keep their claim labels II.9.3, II.9.4) |
| Fable F45 | the certificate note is no longer headed "private" and says who read it |

## Readability, efficiency, format

| Finding | Action |
|---|---|
| Opus M8, Fable F27 (no typeset mathematics) | the converter sets formulas in math mode (exponents, subscripts, Greek letters, relations, square roots, moduli) |
| Opus M9, Fable F28, F29 (bibliography) | working remarks and revision notes stay out of the typeset entries; duplicates merged; wrong links removed; 15 works added (Clay descriptions of Fefferman, Deligne and Cook, Chen-Hou I, Garg-Goos-Kamath-Sokolov, Georgi-Glashow, Bradshaw-Tsai, Koch-Nadirashvili-Seregin-Sverak, Lee-Yang, Landau, Pringsheim, Stepanov, Shioda, Tankeev, Lieberman); author-year citations in the text link to their numbered entry |
| Fable F22 (tools for three problems) | a table at the head of Part II: which part uses which tool |
| Fable F24 (A.5 results buried) | A.5 opens with its four results, numbered, each with its status |
| Fable F25, Opus M11 (repetition) | the box boilerplate of V.8, VI.10 and VIII.8 cut to one sentence; the legends of I.0 and III.0 replaced by a pointer. The repeated margins remain |
| Fable F39 (history in the body) | "now", "earlier rounds", "this round" and dated entries removed from the body |
| Fable F40 (work plans) | not done: the lists stay in "What would close it" |
| Fable F23 (file names in the PDF) | I.0 says how paths resolve, at the commit printed on the title page; no sources appendix yet |
| Fable F43 (PDF properties) | title and author set |

## Checks

Recorded in `REVIEW.md` (Record) and II.7.
