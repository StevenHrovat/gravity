# Review of Draft 6: the explanation mechanism (II.0.2, Appendix E)

Opus subagent at medium effort, 2026-11-25, on gravity `bb69b82` (branch draft-6) and IM `69004d7`. Read only. Result: 2 blockers, 7
should-fix, 6 nits. Confirmed: `Matrix.lean` correct and on Lean's core alone; the 5 by 5 table of E.1 matches `versionUses` and
`versionProofs` cell for cell; the commits; the ledger recount (717 rows, 142 reading marks, 120 first-mark readings).

| # | Severity | Finding | Fixed by |
|---|---|---|---|
| B1 | blocker | E.6 marked Lean, but `step_sound` lets derivation make cells + along chains; that no chain reaches O1 is a paper fact | E.6 rewritten: derivation makes a cell + only along a chain (`derive_sound`, Lean), no such chain to O1 among what Draft 5 establishes (paper), a derived cell explains (reading); introduction softened |
| B2 | blocker | "derivation explains, never proves" tagged Lean, but in Lean a derived cell is a `true` like any other | marked as the first author's reading in the abstract, the introduction, II.0.2, the README and IM's docstrings |
| S1 | should-fix | the diagonal: no use in E.1, a use in E.2 and E.3 | one convention in II.0.2: a current part's own cell is a use, a frozen earlier version's is `·`; stated in E.1 |
| S2 | should-fix | E.5's chain mixes three relations and is not one table | the T.12 part marked a reading, its links named as of different kinds |
| S3 | should-fix | E.4 not Draft 5's table; the core count predates the Lean of II.0.2 | the core re-measured at IM `c441ed5` (3,673 declarations, 2 modules), a commit per column, T.14 cited, the evidence chain and module counts named new in Draft 6 |
| S4 | should-fix | the older cells are proved by a tool version not in the table | E.1 names who runs each proof; a cell means the use is proven; "today's Gravity" replaced by `db03d05` |
| S5 | should-fix | soundness proved for one step only; the closure not proved | `derive_sound` added (IM `c441ed5`); II.0.2 says the closure being reached is classical, not proved in Lean |
| S6 | should-fix | "never exist at the same time" stated as fact | marked a reading in E.1 and in IM's docstrings |
| S7 | should-fix | E.2 has no stated run | date, commits and command given |
| N1 to N6 | nit | `new_cells` is arithmetic; three symbols over one Boolean; "after any number of steps"; Warshall's algorithm vs repeated composition; `.` defined; the counts prose | all taken |
