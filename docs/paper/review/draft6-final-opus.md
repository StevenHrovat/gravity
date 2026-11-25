# Draft 6, final review (Opus at medium effort)

2026-11-26, on main after the contraction and the second throughline (PR 86). An Opus subagent at medium effort as a professional
referee, read-only, asked for the final review before the draft is declared complete. Verdict: no blockers; publishable as a final
draft once about eight should-fix items are corrected. Checked by the reviewer: the printed contents against four pages, the reading
counts and ledger totals by script, six Lean names in IM at the pinned commit, the arithmetic of the core page, both figures.

| # | Severity | Finding | Done |
|---|---|---|---|
| 1 | should-fix | "no test function is negative up to 0.69" marked [certified] alone where IV.1 needs [paper] analytic estimates | Marked [certified] for the enclosures, [paper] for the analytic estimates, in the introduction (three places), the plug-in notes of IV and X, and ledger rows X.58, X.65 |
| 2 | should-fix | II.4h: n bits as "the corner points of a space of dimension 2^n" | Fixed: the 2^n corners of the n-cube, as basis vectors spanning dimension 2^n; a reversible computation a permutation matrix (II.4, ledger II.4h) |
| 3 | should-fix | "0.69 read as a rapidity gives 5 : 3 : 4" exact only at log 2 | Fixed: "a rapidity of log 2, 0.69 to two digits" |
| 4 | should-fix | I.1 cited as [paper]; the ledger has it as a reading | Marked [reading] (introduction, READINGS.md R.12q, ledger R.12q) |
| 5 | should-fix | Counts: 751 rows (753 counted), 56 pages, the scope-row list | Fixed; the list lacked IX.7d (III.0 was listed) |
| 6 | should-fix | Kept passages pointing at removed text (X.8, VII "example above", A's Chen-Hou T*, the Outlook's +dimensions, II's XI.2a-c) | Each now says "in the full text" or names what it meant |
| 7 | should-fix | Bibliography uncontracted (267 entries, 26 cited); von Neumann 1923 twice and unlinked | `tools/paper-latex.py` gains options a draft switches on (`<!-- typeset: ... -->`): Draft 6 prints only the cited entries, with their numbers, and links names with a particle; the duplicate row removed. Drafts 4 and 5 convert as before (checked) |
| 8 | should-fix | The one assumption as each card's base case against X.4.4's `FineOneBox` for Yang-Mills | Part X's opening now names Yang-Mills as the exception in form |
| 9 | nit | IX.2 "The card" while GU has no card | Retitled "The card in prose"; X says "GU's open step" |
| 10 | nit | Full stops inside superscripts | Fixed in the generator (option strict-periods) |
| 11 | nit | The title page names the commit the PDF was built from, one behind the commit that carries it | Kept: inherent in committing a built PDF |
| 12 | nit | The empty set and foundation; Goedel's second theorem needs "effectively axiomatised" | Both fixed |
| 13 | nit | Abstract: "stated once, as a reading" against ledger X.64 [open] | Kept: the abstract is at 1,917 of 1,920 characters |
| 14 | nit | I.8 calls Moin the label of O1 | The cell now says: the state of every named open step; read as the label of O1 |
| 15 | nit | Part III's header names R2 under Attempts/ | Fixed: R3 and R4 where a claim uses them; R2 and the rest at the tag |
| 16 | nit | "1001 steps at most" for halving to 1/1000 | Says now that the bound is general and loose here |
| 17 | readability | unprinted-section markers, the CLAIMS path in the PDF, `assignment_does_not_decide` as a negative result | The last presented as the simplest illustration; the others kept (each part's "Contracted" note says it) |

After the fixes the PDF has 47 pages (from 58), the page check passes, the paper gate is clean.
