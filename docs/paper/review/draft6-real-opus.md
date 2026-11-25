# Review of Draft 6: II.0.5g (elastic spheres, real induction as +N!, the kernel)

Opus subagent at medium effort, 2026-11-25, on gravity `0b440f8` (branch d6-real, StevenHrovat/gravity#71). Read only. Result: no
blockers, 6 should-fix, 5 nits. Confirmed: elastic collisions and binding; real induction equivalent to completeness (Clark 2019);
Tarski for ordered fields; Mathlib's reals as Cauchy sequences; Turing's countably many computable reals; every cross-reference; the
counts (742 rows, 137 first-mark readings, index 162); references 247 to 255; the care points keep O1 open, the sets apart and the
kernel certification relative.

| # | Severity | Finding | Fixed by |
|---|---|---|---|
| S1 | should-fix | Loewenheim alone, and without the countable-language scope | "in a countable language ... a countably infinite one (Loewenheim 1915; Skolem 1920)"; Skolem 1920 added as row 256 |
| S2 | should-fix | the countable model is a field, not the naturals; the theories differ (decidable against undecidable) | a care line: the reals' first-order theory decidable (Tarski), arithmetic's not (Goedel 1931; Turing 1937); equality holds for certificates |
| S3 | should-fix | "no countable certificate settles completeness" is false: Mathlib proves it | "no countable ordered field is complete; completeness separates them" |
| S4 | should-fix | lean4lean does not prove Lean's kernel correct | "parts of the metatheory behind its own typechecker, work in progress; not Lean's own kernel" |
| S5 | should-fix | Landauer is about erasure; the link to the binary question is a reading (measurement can cost nothing, Bennett) | the bound kept classical, the link marked a reading, Bennett 1973 cited |
| S6 | should-fix | DoE has no source in the draft | pointed to `docs/guid/preface.tex` and IX.8; not spelled out in the paper |
| N7 | nit | Bohr-Mollerup: positive on x > 0; the original | added; "the theorem of Bohr and Mollerup, 1922, as in Artin 1931" (the 1922 volume not found on zbMATH) |
| N8 | nit | "every certificate ... is one" reads as "equals 1" | "any two certificates of one statement are identified" |
| N9 | nit | Carneiro 2019 is for Lean 3 | "Lean 3" added |
| N10 | nit | Cantor 1891 is the diagonal argument | "the diagonal argument, Cantor 1891" |
| N11 | nit | the references header named only Crossref and zbMATH | "Crossref, zbMATH, arXiv or GitHub release record" |
