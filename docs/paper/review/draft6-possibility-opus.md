# Review of Draft 6: the optimizer and the possibility space (II.0.3, II.0.4, E.9 to E.11)

Opus subagent at medium effort, 2026-11-25, on gravity `2ef71c2` (branch d6-possibility) and IM `e9a4057`. Read only. Result: 2
blockers, 7 should-fix, 5 nits. Confirmed: every Lean name cited exists in `Optimizer.lean` or `Possibility.lean` and the statements
match apart from S3 and S9; `versionUses` and `versionsSettled` match E.9; `repos_reduce_loses_dmp` is correct; the optimizer tool
merges duplicate edges, its memoised reachability has no false negatives after the DAG check, its redundancy test matches
`redundant`, and it cannot hang; E.11 matches the tool's rule; the counts (730 rows, Lean 282, reading 129, index 154); the abstract
(1,912 characters); the cross-references; the commit ids; the classical attributions other than B1 and N12.

| # | Severity | Finding | Fixed by |
|---|---|---|---|
| B1 | blocker | II.0.4d: "the smallest space with exactly that symmetry is CP^2 x S^2 x S^1" misstates Witten 1981, which finds seven as the minimum dimension, reached by a family of circle bundles over CP^2 x S^2, and the obstacle of chiral fermions; the hypercharges were not confirmed | rewritten in II.0.4d, its ledger row and the R.0 row |
| B2 | blocker | II.0.4c: confinement stated as **[classical]** | "where it is expected to confine: lattice evidence, not a proof, and close to the open problem of Part III"; ledger and R.0 rows |
| S3 | should-fix | II.0.3c: "fewest uses" marked Lean; the Lean proves minimality and uniqueness, not the count | marked classical (Aho-Garey-Ullman 1972), with what the Lean proves stated |
| S4 | should-fix | II.0.4b: "only the + side carries a state" is false as physics; "a refusal is not a state" is in R.9, not R.10a | marked a reading with R.9a; the physics stated (the answer-0 side holds states too) |
| S5 | should-fix | II.0.4d contradicts R.7b, which records a second fact at N = 3 (SU(3) inside G2 inside SO(7)) | both facts named, neither continuing (R.7b) |
| S6 | should-fix | "a base dimensionality of 6" has no exact counterpart stated | "no exact counterpart is given"; the six-sphere G2/SU(3) of R.7b named, a relation not claimed |
| S7 | should-fix | the Draft 7 interface stated as fact | stated as a plan for Draft 7, not part of Draft 6 |
| S8 | should-fix | the matrix stage passed a settled result, though E.9 states one redundant use | the stage now requires exactly that redundant use; a settled result or another use fails it; E.9 says so |
| S9 | should-fix | "optimizing once settles" lacks "on a DAG", here and in `Optimizer.lean` | added in II.0.3 and in IM's docstring (StevenHrovat/im#28) |
| N10 | nit | what "DAG" means in the Lean | stated once in II.0.3 and in `Optimizer.lean`: `Earlier`, every DAG up to renumbering |
| N11 | nit | the Bloch sphere is the pure states | "pure states (the mixed states fill the ball)" |
| N12 | nit | the endpoint speed is not Goto's result | the string credited to Nambu and Goto (Goto 1971), the endpoint speed stated as a property of its rotating solution |
| N13 | nit | a non-DAG made the tool exit 1, read as a failing cell; a nested PIN with an empty parent shifted fields; a newline in the stage's title | exit 4 for a non-DAG and the nested PIN skipped (StevenHrovat/im#28); the stage handles 4; the title on one line |
| N14 | nit | E.10's title: the reduction runs but loses reach | "cannot be optimized without losing DMP" |

After the fixes the IM pin moved to `966a016` (StevenHrovat/im#28, docstring and tool only), and E.9 was measured again on a clean
clone from gravity `3841987`: one redundant use, `im@966a016 -> dmp@1370dc0`, through `gravity@4ec1131`; the stage and the evidence
gate (OK 285) pass.
