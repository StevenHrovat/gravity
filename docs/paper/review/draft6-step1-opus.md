# Review of Draft 6: II.0.5h (from step 1 to the encoder, packed into O1)

Opus subagent at medium effort, 2026-11-25, on gravity `431c127` (branch d6-step1, StevenHrovat/gravity#72). Read only. Result: no
blockers, 6 should-fix, 9 nits. Confirmed: Peano from 1; the inclusions and NP in coNP equivalent to NP = coNP; Cook-Reckhow; Elitzur;
5-bar + 10 as fifteen Weyl fermions; the references 257 to 262; RH recorded as external; the Lean names; the counts (743 rows, 138
first-mark readings, index 163); every cross-reference. The care points keep both `?`, O1 open, and RH's status from changing anything
proved.

| # | Severity | Finding | Fixed by |
|---|---|---|---|
| S1 | should-fix | "SU(5) holds the Standard Model group as its quotient by Z_6 [Lean]": the Lean proves the embedding's kernel is Z_6; the image is a paper observation | the kernel (IX.3.1h, Lean) and the image (IX.3.1i, paper) stated separately |
| S2 | should-fix | "every conditional result of the paper has this form [Lean]" | "the conditional results of III.9.5 and III.13 are of this form" |
| S3 | should-fix | Lagarias' criterion is Pi-1 only after a further step | X.24 cited: rational approximations, Davis-Matiyasevich-Robinson |
| S4 | should-fix | Landauer listed under Lean in the ledger row | moved to classical |
| S5 | should-fix | the README sentence lacked the reading mark and the care | "(all the first author's reading, with their care points ...)" |
| S6 | should-fix | P != NP's reason incomplete | "P != NP is Pi-2: a counterexample is an algorithm with a proof of correctness and polynomial time, not a finite object" |
| nits | nit | `ActAdm` in Criterion.lean; Mathlib's `PNat`; the Euler product for Re s > 1; II.3.2; IV.1.5 for zeta; von Koch's statement and the amplitude as a reading; Super-Kamiokande 2017; Amaldi-de Boer-Fuerstenau 1991 for the couplings; "[Lean] for the form" | all applied |
