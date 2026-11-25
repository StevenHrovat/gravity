# Review of Draft 6: the ETM as the ODP running DMP (II.0.5, III.13, A.2b, R.5b)

Two Opus subagents at medium effort, 2026-11-25, read only.

**First, on the interface as first built for a Draft 7** (gravity `aa4b2de`, StevenHrovat/gravity#68, closed when the first author
decided there would be no Draft 7). Confirmed: `BoxAt` is literally the inner statement of `FineOneBox`, `Interface` carries exactly
its outer existentials, so `interface_iff` is an equivalence with O1; the axiom log is clean. Findings, all carried into the Draft 6
text and the Lean docstrings before the port was committed:

| # | Severity | Finding | Fixed by |
|---|---|---|---|
| B1 | blocker | the a-theorem stated as a quantity monotone along the flow; Komargodski-Schwimmer show only a_UV > a_IR | III.13c and its ledger row: it compares the endpoints and is not shown monotone along the flow |
| B2 | blocker | "an instance is a mechanism that gives O1"; W can be a counter, so the type adds no mechanism | A.2b: an instance gives O1 and O1 gives an instance, W a counter; no mechanism beyond O1 |
| S3 | should-fix | "the open content in one field": the choice of geometry and constants is part of the open step | III.13b, the ledger and the module docstring: the ledger together with the geometry and constants |
| S4 | should-fix | "the interface is not vacuous" is about the ledger type on toys | scoped to the ledger type; the toys named as illustrations |
| S5 | should-fix | "the interface makes 'all else constructable' a theorem", already true of O1 (III.9.5) | "as for O1 itself, an instance gives the gap" |
| S6 | should-fix | Perelman's count runs on volume, not on the W-entropy | stated in III.13a, III.13c and the docstring; W plays the cumulative volume removed |
| S7, S8 | should-fix | Draft 7 headings and a garbled II.0.4e row | moot after the port; II.0.4e now says the interface is built in III.13, equivalent to O1, no instance |
| nits | nit | the gapped toy's bound; [0, T]; A.2b under a reading heading | "at most the bound"; [0, T] stated; A.2b is its own section |

**Second, on the Draft 6 port** (gravity `1fd6a4d`, StevenHrovat/gravity#69). Result: no blockers, 2 should-fix, 7 nits. Confirmed:
the three reasons of II.0.5c (zero ring; 0 = 1 in the naturals proves everything; P = NP implies NP = coNP), every claim of II.0.5
attributed and marked, the Lean names (`r_four`, `exists_unique_hom`, `univIsTerminal`), the VIBE coefficient as `balance.tex` names
it, the VII.6e cross-reference, the earlier fixes, the counts (739 rows; index 159, 134 first-mark), the abstract (1,905), the subtitle
everywhere.

| # | Severity | Finding | Fixed by |
|---|---|---|---|
| S1 | should-fix | ledger row II.0.4b still called the Possibility Space "the subtitle" | "the first subtitle" |
| S2 | should-fix | R.5b: the `.cmb` / VIBE coefficient read as supplying O1 without saying it does not follow | R.5b text and R.0 row: a measured coupling gives no bound on the Wilson measure, does not supply O1; ledger row too |
| N3 | nit | "the exact side of" under a classical mark | "the nearest exact statement to" |
| N4 | nit | the crossing theorem's Lean scope | "in Lean, with two graph hypotheses stated, II.14.5" (the ledger row II.14.5 marks it Lean for two-premise systems) |
| N5 | nit | "it lines up" ambiguous after two subtitles | "the Possibility Space lines up" |
| N6 | nit | "There is no Draft 7" in the README | "the interface first planned for a later draft is built here" |
| N7 | nit | A.2b's source cites itself | removed |
| N8 | nit | one long line in R.0 | kept: rewrapping the file would have changed list indentation |
| N9 | nit | the `?` of the essence chain | kept: `?` is the first author's operator (R.10a), not a lost symbol |
