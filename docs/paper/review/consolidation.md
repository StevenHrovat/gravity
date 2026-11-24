# Stage-3 consolidation of GUID v8 (draft 4)

One pass over both final verification reports (`final-opus.md`, Opus; `final-fable.md`, Fable; release candidate `f4592e3`),
the part reviews R1 to R7, and the first author's decisions and readings of 2026-11-24. Done 2026-11-24 by the coordinator, in the
commits after `12e96a1` on branch `ccr-be614210-u4r7na`. Stage 4, the first author's gate, follows.

## The first author's decisions applied

* Blocker F-04: the abstract's sentence is now "One certifiable step is the same on every card" (his wording). The abstract and the
  introduction say what the step is (the step of the box at its gate), that the one assumption reads the open step the same way on
  five cards and is a different statement on each, that Navier-Stokes is the expected negative and that GU's open step lies outside
  its box.
* Personal note: his paragraph "My logical deduction chain: ..." added ("its" for "it's"); the other sentences unchanged. The
  editorial note under it removed. Its three points: the Riemann sentence is phrased as his reading (done in stage 2); the umlaut is
  restored in the typeset text (below); "One thing led to three" and "after GRH got proven and certified" (F7, F-18) stay his to
  change.
* "Goettingen" with the umlaut in the typeset text: `tools/paper-latex.py` restores umlauts and accents of a fixed list of words
  (Goettingen, Lueck, Goedel, Kaehler, Poincare, Szego, Necas-Ruzicka-Sverak, ...) as TeX escapes; the sources stay transliterated
  (repository rule, scrub).

## Findings and what was done

Blockers (Opus F1 to F3, Fable F-01 to F-04): all fixed.

| Finding | Action |
|---|---|
| F1, F-01, F-02 editorial notes, "coordinator" sentences, "DOI to be added" | removed from every draft; III.4.4 now says what the abstract says; IX.2 states that `HodgeAPI` is built and audited through `ETM/CardBox.lean`; IX.7 item 3 dropped; VII.4.2 says the Zenodo record was not found again (lookup B), no DOI promised |
| F2, F-03 Bogomolny 1976, Ito | identified (INSPIRE 101280; Phys. Rev. Lett. 55 (1985) 558); IV.6 cites Ito 1985 as **[classical, recalled]**: the record was read, not the bounds |
| F3, F-16 wrong links (Weil 1948, Hopf, Cantor) | replaced by the works' records (zbMATH, BnF) or dropped; titles and years corrected |
| F-04 "one step is the same on every card" | the first author's sentence, see above |
| F4, F-05 G2 | abstract list, III.4.4, claim 0.24: G2's rigidity is restated as a one-box test; the sharing it assumes is at least as strong as the rigidity, so the one assumption does not decide it |
| F5, F-06 the assumption as a schema | III.4.4 "A schema, not one proposition" with its Lean instances; IV.9.5b and IV.0 O2 marked **[open]**, part of the assumption by a reading (ledger: conditional 7 to 6, open 46 to 47) |
| F6, F-07 one open step per card | introduction: one named open step per card in Lean, further items in each part; Yang-Mills O1 to O4 spelled out; GU a box, not a card; NP: VI.6 says how `CrossingCost`, `LiftCPConst` and N1 to N4 relate |
| F8, F-09 restatement by construction; `FineOneBox` | introduction, IV.5.6, claim 0.22; III.4.1 table names `FineOneBox`, the number a sufficient heuristic route |
| F9 "the owner" in the typeset text | "the first author" in every draft (82 places); CLAIMS, PREP and the notes keep the workflow word |
| F10, F-14, F-21 re-checks at the release commit | the independent re-check (quick), IM's arsenal check, the Hodge axiom log and the rotation axiom log were run at the consolidation commit; II.7 and the record below give the results; I.8b, II.6.3, VIII.3, VIII.7, IX.3 now point to them |
| F11, F-25 the undecidable edge, the certificate's hypothesis | "for the universal machine, over all content"; "a marker correct at the start and kept by the step at every state" |
| F12, F-23 certification wording | "the Riemann hypothesis certified by the Lean FRO and the Mathlib Initiative; the Dirichlet theorems checked on the verification page" (introduction, V.0) |
| F13, F-16 typeset bibliography | standard entries: authors, title, venue, a DOI or record link; no status tags, no working remarks, no search links (`tools/paper-latex.py`, `clean_bib`, `bib_link`) |
| F14 Voisin's title | the journal page's title (OUP), "extended to Kaehler varieties" |
| F15, F-29 the marks | one legend: the nine marks plus the qualifiers and [sketch], [unchecked] (introduction); I.0 adds [conditional], [certified] and points there |
| F16, F-17 the abstract | plain text, two paragraphs, 1,912 characters; the lists moved to the introduction ("Results and open steps") |
| F17, F-13 Hodge | "from named classical inputs": Hodge-Riemann and the Hodge index property as inputs |
| F18 NP crossing | "on expanding, minimally unsatisfiable formulas" |
| F19 BSD | "over Q, from order 2 on (over other number fields, in general)" |
| F20 Yang-Mills assembly | "to exponential decay of slab correlations (a lattice mass gap) ...; the step to a gap of the Hamiltonian is argued in prose (IV.2.7)" |
| F21 III.4.1 | the open statement is `FineOneBox`; the number its sufficient, heuristic route |
| F22 small-support literature | Connes-Consani 2021 and Yoshida 1992 cited (introduction, V.8) as **[external, recalled]**; what the first box adds: the primes 2 and 3 and explicit margins |
| F23, F-27 `sync-build.sh` | `src` derived from the script's own folder; `.gitattributes` keeps `*.sh` LF |
| F24, F-32 draft history | removed from the body (IV.0, IV.5.6, III.2, III.4.4, III.7, VI.6) and the header notes; Lean strings "X.64" renamed "III.64" in `ETM/Rotation.lean`; II.16 "six sections" |
| F25 the modulus and the cost | "the negative logarithm of the modulus is the cost" (abstract, claim 0.25) |
| F26, F-31 layout | `xurl`, breakable code spans, `\sloppy` in the bibliography: 42 overfull boxes down to 5 (worst 26 pt) |
| F27 A.3 | "answered: published for N = 3, and for N >= 4 by a surgery computation"; the odd-N step (the obstruction in L = Z) marked open (A.3, claim A.3j) |
| F28 R136a1 | "in IM's arsenal ...; this repository's cards use the same transparent form under the names `OpenStep` and `External`" |
| F-08 VI.4.11 | new paragraph and table row in Part VI; "for cutting planes on lifted formulas" |
| F-10 the external route | "as far as this project traced it, does not go through Weil's positivity criterion"; V.0 no longer contradicts itself |
| F-11 GRH open step | "a proof of Weil positivity from the primes and the real place alone ...; GRH beyond Dirichlet, no card yet"; V.4 adds that no uniform margin is asked |
| F-12 certified and paper | "[certified] for the enclosures, [paper] for the analytic estimates" in III.1, III.4.4, III.6, V.8 and the introduction |
| F-15 missing works | 19 rows added (Buhler-Gross-Zagier, Dokchitser-Dokchitser, Goldfeld, Kato, the Trento examples, Kolyvagin twice, Monsky, Necas-Ruzicka-Sverak, Rubin, Skinner-Urban, the Lean RH library, Connes-Consani, Yoshida, Levin-Peres-Wilmer, Wu, Simon, Pisarenko, Makhoul) |
| F-18 "three problems" | "the first three problems" (I.0, I.1, II.8, IV.1) |
| F-19 Sp(2) | one wording: strongly rigid, a surgery computation, independently read |
| F-20 anomaly | "with q_Q > 0 and coprime charges", and the second solution without q_Q != 0 (X.4.1, X.7) |
| F-22 pointers | I.8 to II.4 (II.6.1, III.4.4, IV.5.6); the BSD triad sentence aligned with III.3 |
| F-24 IV.6 threshold | the twist ratio 3/7, beta L^2 <= (1/2) log(7/3) = 0.42; with 0.414 the bound is 0.44, with 0.74 it is 0.15 |
| F-26 `LiftCPConst` | docstring and ledger rows VI.4.11, III.7k: open for suitable gadgets (indexing), false for XOR (Tseitin, Dadush-Tiwari 2020; not machine-checked) |
| F-28 Part VII | retitled "three cards and the claimed certificates"; section numbers kept, so the claim labels VII.7a to VII.7h stay valid |
| F-30 rows | Dobrushin titles (Crossref), Cantor 1890/91 printed 1892, OpenAI page title, Super-Kamiokande 215 authors, Bombieri merged |
| F-33 placeholders | references supplied: Levin-Peres-Wilmer (II.10.3), Hayes and Wu (II.12.3), Simon (III.45b), Pisarenko and Makhoul (V.3.3); the recalled items say "recalled, not traced" instead of a to-do |
| F-34 Navier-Stokes | "three cards on the form layer; no Navier-Stokes object in Lean; (A) and (B) named, not defined" |
| F7 the personal note | left to the first author |
| also | III.6 corrected to the one-way pin decided in stage 2 (the spiral through time is now the first author's reading); "one item of the abstract" now "one item of the introduction's list of open steps" |

## The first author's readings of 2026-11-24, applied

All as readings, each with its exact part beside it (claims I.7d, I.7e, II.4f, III.32a, III.32b, III.65a, XI.1d):

* I.7: 2 + 2 = 5 through DMP, and the essence line 2 + 2 ? 5 ? 4 ? 0 ? 1 ? SU(5) = 1.5, only 1.5 assumed. New Lean,
  `ETM/Essence.lean`: `two_add_two_ne_five` (by `decide`, no axioms), `essence_zmod_one` (by `decide`), `essence_iff_subsingleton`
  (the chain holds in a ring exactly when it has one element), `essence_decided` (once 2 is a unit, every link is equivalent to
  0 = 1), `four_eq_zero_without_half` (without it, Z/2 separates 4 = 0 from 0 = 1).
* II.3: a DMP-complete proof is lintable in one step, relying only on `decide`, with the care points (correctness theorems are
  ordinary proofs; the open steps are not of that form; `native_decide` excluded).
* III.4.3: the error bars as the possibility space; "to be correct is to have the correct error, when read through DMP", with the
  hard line that it does not discharge O1.
* III.4.4: the certificate read as 1.5 = 3/2, with the normalisation care point.
* XI: +AI, the name for a DMP-complete general intelligence.

## Ledger

666 counted rows: Lean 252, classical 124, external 42, conditional 6, paper 63, numerical 22, certified 2, reading 108, open 47. `tools/claims-check.py`: OK.

## Checks at the consolidation commit

Recorded in `REVIEW.md` (Record) and II.7.
