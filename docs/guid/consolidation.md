# Consolidation of the final fault verifications

One pass over both final verifications, gravity#26 (Opus, `review-final-opus.md`, 35 findings, 6 release-blocking) and gravity#27
(Fable, `review-final-fable.md`, 24 findings, 6 release-blocking), applied to `guid.tex` once. Both reviewed `0b20f2b`. The GLM-5.3
verification is not in the repository yet; it is folded in when its pull request exists (gate G1).

Both passes reproduced every number (assembly 18 of 18 and 25 of 25, Lean 243 and 246 with Lean 4.34.0), found all 35 references correct,
and found Claim 1 holds. Where they overlap the Opus id is given first.

## Fixed in the paper

| Ids (Opus / Fable) | What changed |
|---|---|
| A3 / – | "public" becomes "released with this paper" (abstract, What we claim); publishing stays gate G4 |
| H1 / H3 | Contributions: every theorem on `main` is checked by two kernels; `blind_record_same` by Lean's kernel only, second-kernel run pending; Section 8 says the same |
| S1 / F3 | Dropped "the independent verification he reports agrees" until the GLM-5.3 record exists |
| F2-2 / F2-1 (rows) | The final-verification row is filled from #26 and #27; the editors' instruction sentence under the table is removed. The GLM-5.3 row stays pending (G1) |
| F1 / – | Agreed fact (v): no coherent superposition of backgrounds while records exist; "within one area sector" |
| E4 / E4 | **2+1 verdict corrected to CAN NOT model, CAN host**, on the owner's ruling (18:19Z, "It is correct!"), with his two reasons (18:19Z, 18:21Z) quoted as his reasoning and the holonomy and particle-scattering arguments cited (Nelson and Regge 1989; 't Hooft 1988). Abstract and Result paragraph follow |
| E5 / – | Chern-Simons "perturbatively"; Brown-Henneaux for negative cosmological constant |
| G2 / – | "as far as the published code models go" becomes "the kinematic content of the HaPPY model, on a tree of one layer" (also in the conclusion) |
| B1 / B1 | "obeys all three axioms as written" becomes "encodes the eight sentences of the table", with what it does not encode and "not shown DMP-complete" |
| B2 / B3 | The majority row is marked as the first author's reading; DMP's T5 named |
| – / B2 | The no-cloning row is "cited, not checked" |
| B3, H2 / B4, H2 | Check [7]: "acted on jointly under a grant"; the construction choice (existence = field register) and the alternative that breaks it; negativity for the plus-plus contents only; `blind_record_same` assumes the clause and says nothing about coherence |
| E1 / E2 | Definition 1 and Proposition 2 no longer claim DMP-completeness; Proposition 2 is labelled "argued, not proven"; content moved by grant is stated not to be a DMP structure |
| E2 / E1 | Deutsch as a principle we assume, to finite precision |
| E3 / – | "Hosting is cheap; the content of the result is the cannot-model half" in the Result paragraph |
| D1 / – | "Together" says the geometry, as a local classical mediator, cannot by itself entangle |
| C1 / C1 | Claim 1 restated as "depends on the parts only through classical records, so it acts as a classical mediator"; the deterministic-preparation case and the erasure escape added to the argument |
| D2 / D2 | Debate extended: the size of the Aziz-Howl effect; Schneider, Huggett and Linnemann (arXiv:2511.19242); Gundhi, Infantino and Bassi (arXiv:2604.19696). **Correction to #27's D2:** it attributes 2511.19242 to Gundhi, Infantino and Bassi and 2604.19696 to Aziz and Howl; search shows the reverse pairing above (2604.19696 is a rebuttal, not Aziz and Howl's reply). Marletto and Vedral arXiv:2510.19969 is not added: its title could not be confirmed |
| F3 / F2 | Harlow: "with complementary recovery" |
| G1 / G2 | X5 hedged: no discrete model established; CDT's de Sitter phase cited (arXiv:0712.2485; the PRL reference could not be confirmed, so the arXiv number is cited) |
| G4 / – | "Fixed before the assembly was built" becomes "stated before the run; the record holds both in one commit" |
| C2 / – | "(Axioms 2 and 3)" |
| B4 / – | Check [4] "by construction" |
| – / B6 | Check [4]'s 0.50 named as the refusal of the full-reach-as-content reading; listed in Section 10 |
| H3 / – | "We model every layout as a term of one recipe type (a modelling assumption)" |
| S2, S3 / S2 | Cold-read row: 13 requirements (7 conflicts), 8 divergences; "did not arrange" |
| S4 / S3 | Availability lists #18, #19, #21-#24, #26, #27, #24 at `60a1616`, #17 for the CHSH theorem |
| A4 / – | "counts always, content only by a grant" (abstract) |
| A5 / H5 | "theorems numbered T0 to T40 (with gaps)" |
| – / H4 | "the recipe's digest is not injective" |
| – / X1 | "gravity#21, row A7, says how" |

## Open: the owner's words (release gate G2 and the preface)

| Ids | Sentence | State |
|---|---|---|
| P1 / P1 | "The final result was proven correct by four separate adverserial reviews (Fable, Fable, GLM-5.3, Fable)" | Both: false today and cannot become true as worded (the three Fable passes on record predate the final result; a fault verification does not "prove correct"). Asked the owner |
| P2 / P2 | "pinned to at least v1.0.0" | Kept as aspirational (17:40Z); both say false today. Asked the owner whether "will be pinned" |
| P3 / – | "mapped 1:1 to actual Hawking radiation" | Opus: the record does not back "1:1" (cold read Q5). The owner's words; flagged only |
| P4 / P3 | "Showing provability for the effects of quantum gravity" | Both: the body proves no effect; covered by the preface note. Flagged only |

## Open: release gates

| Ids | What | Gate |
|---|---|---|
| A3 / – | Repositories private; drafts #18, #19, #22, #24 unmerged | G4 |
| H1 / H3 | Second-kernel run for `Blind.lean` (#24 targets #23's merged branch, so `lean-evidence` never fired) | G4 |
| F2-1 / F2-1 | Contact address on the title page | closed: the owner's mailbox, his choice 18:34Z |
| – | GLM-5.3 row | G1 |
| F2-3 / – | Source comments with timestamps in `guid.tex` and `preface.tex` | trim at release |
| – / F2-4 | "Draft of 27 October 2026" | set at release |
