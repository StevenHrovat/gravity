# Review of Draft 6: the reader's slope (Fable, high effort), and its check

**Fable at high effort, 2026-11-25, on gravity main `6f8d566`, read only,** asked to judge the paper's readability across its fields
and to propose a gentle slope: the core first, a few examples, the rest inferred. Verdict: the Draft 5 skeleton was close to a gentle
slope; Draft 6 had put its additions at the two steepest points, the head of the introduction and between II.0.1 and II.1, so a
newcomer from any field was lost by page 6 and again at page 19. Its ranked edits and what was done (PR StevenHrovat/gravity#73):

| # | Edit | Done |
|---|---|---|
| 1 | move II.0.2 to II.0.5 behind what they cite | E.0.1, E.0.2 at the head of Appendix E; R.11, R.12 closing Appendix R; relabelled; a pointer at II.0.2 |
| 2 | reorder the introduction | the core page first, the marks next, "What Draft 6 adds" last |
| 3 | a one-page core with Figure 1 and the toy | "The core in one page", Figure 1 moved from II.4.1 |
| 4 | II.0.5 as numbered clauses | R.12a, b, e, f, g, h as numbered clauses, each followed by its exact parts and care |
| 5 | the abstract opens with the problems and "no problem is solved" | done, every hedge kept |
| 6 | split II.4 | reading, definition with the toy, outside, care point, a table of boxes, certificates, rigidity, cards |
| 7 | vocabulary | I.8 rows added; ETM, ODP, IM, Gravity glossed at first use; the operators defined on the core page |
| 8 | Appendix E | opens with its table and the optimizer's output; DMP's cell in its final form; E.8 its own section; version aliases |
| 9 | III.13 | toys first; "the counting ledger"; A.1's row inlined |
| 10 | labels | not done: renaming established claim labels would break citations in earlier drafts and reviews |
| 11 | part openers and card boxes | IV.8 and V.10 now say the Lean box is the card box (checked in `ETM/CardBox.lean`) |
| 12 | housekeeping | reproduce paths to D6, Plan, the mark qualifiers, the E = mc^2 reading kept in III.5 only |
| - | the `·` glyph | kept (the matrix tool prints it); a sentence now separates it from `.` |

**Check review, Opus at medium effort, on `48669c5`.** Nothing lost in the moves, relabelling or counts. Two blockers in the abstract
("each problem is a card" and "the work is in Lean"), fixed: "each problem has cards ... (GU a box, no card)" and "the restatements are
in Lean"; should-fix items fixed: the neighbouring forms named, the hand-over row's conditions, the `·` reading moved to its column,
the CMB bullet in R.12i marked a reading, the stale "ends with" and the README; nits applied (marks on the toy and Appendix E
sentences, "interpretation" in IV.8, the figure note, a comma, claim numbers for the toy).

R.12j (the first author's reading of ordinality as the orbit of the atoms) was added with the fixes.
