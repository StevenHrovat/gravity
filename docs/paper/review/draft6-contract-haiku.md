# Draft 6 contracted: closed-book route readers

2026-11-25, on the contraction branch (`paper-d6-contract`, PR 85). Two Haiku subagents at low effort, each reading only one route of
the contracted paper (Route 2 without `READINGS.md`), then the same closed-book test as `draft6-routes-haiku.md` (Q1 to Q4, keys
written before the first run). Neither used a tool during the test (tool counts unchanged, 7 and 5).

| Reader | Q1 (4) | Q2 (5) | Q3 (5) | Q4 (5) |
|---|---|---|---|---|
| Route 1, exact | 0 (not recalled; not on route 1's stops) | 5 | 3.5 (the token's iff only; no pigeonhole) | 4.5 |
| Route 2, readings | 1 (the three notations recalled, not their mapping) | 5 | 3.5 (the iff and "every hash collides", no pigeonhole) | 5 |

Before the contraction route 2 scored 4, 5, 5, 4: the operator notation and the pigeonhole argument now live in `READINGS.md`, which
the reader was told not to open, so route 2's Q1 and Q3 dropped as expected. Q2 and Q4, the core and the throughline, hold.

Findings, and what was done:

| # | Reader | Finding | Done |
|---|---|---|---|
| 1 | route 1 | Parts name sections that the contraction no longer prints (III.3, II.1, II.12, X's sections 1 to 6, E.9 to E.11) | Each part now says at its start, after the plug-in note, that named but unprinted sections are in the full text (`d6-full`) and every label is a ledger row; Part II's and Appendix E's headers and X.8 say so where they name them |
| 2 | both | "the headline holds as a theorem" reads stronger than a restatement; "none is proved" beside Lean results | Both route endings now say the headline is a restatement that proves nothing by itself, and that no open part is proved |
| 3 | route 2 | Part I's note said "stop 2"; the vocabulary is stop 3 | Fixed |
| 4 | route 2 | Figures exist only as LaTeX comments in the Markdown | Kept: the PDF has them |
| 5 | route 1 | Seven instances of the one assumption against five cards | Kept: X.4.4 states the schema and its instances; the abstract names the five base cases |
