# Final fault verification of GUID (#25): opus

VERIFIER = opus (Claude Opus 5.5, high effort), 2026-10-27. Independent: the Fable verifier's pull request and thread were not opened.
Reviewed: `docs/guid/guid.tex` and `docs/guid/preface.tex` on `claude/project-thread-x1aw4m` at `0b20f2b` (gravity#25), against gravity
`main` `06231b8`, gravity#24 head `60a1616`, DMP `45d3822` (0.9.8, read from `vendor/dmp`, PIN verified by `check.sh`), and the review
passes #18, #19, #21, #22, #23, #24. Nothing in the paper, the preface or DMP was edited.

**Environment.** Python 3 with numpy 2.5.3; Lean 4.34.0 (the pinned `leanprover/lean4:v4.34.0`, official Linux release); TeX Live
(pdflatex). The second kernel (lean4export + nanoda) was not run here; its record is the CI run named in task A. arXiv and publisher pages
could not be fetched from this environment (DNS refused for arxiv.org, quantum-journal.org); every reference was checked through web search
results that quote the arXiv listing, the DOI record or the publisher's page, named per row in task R.

**Bottom line.** Every number the paper gives reproduces. The 3+1 verdict holds as argued under Definition 1, and the dissent's split is a
choice of definition, but the paper leaves out one physical fact both passes agree on (F1). Six sentences are false or unbacked today:
the preface's four-reviews sentence (P1, gate G2), "public" (A3), the claim that every formal claim was checked by two kernels (H1), the
GLM-5.3 verification cited as agreeing (S1), and two leftover placeholders (F2-1, F2-2). The 2+1 section (E4) and the overstatement
"as far as the published code models go" (G2) are the weakest physics.

## Findings

| Id | Severity | Location (guid.tex line unless named) | The sentence | Evidence | Proposed fix |
|---|---|---|---|---|---|
| P1 | blocker | preface.tex 15 | "The final result was proven correct by four separate adverserial reviews (Fable, Fable, GLM-5.3, Fable)" | The final result (CAN NOT model, CAN host) first appears in gravity#23 (Opus 5.5, opened 13:46Z, section 10 at 14:41Z). The three Fable passes predate it and reviewed earlier claims: #19 (opened 06:43Z, "does not hold"), #21 (merged 09:26Z, refuted the earlier claims, row B4a "refuted (not implied)" on the earlier Claim 1), #22 (last commit 13:22Z, seven conflicts). The only review of the final result in any repository, #24 (Opus 5.5), dissents (CAN). No GLM-5.3 record exists in any repository. "Proven correct" also contradicts the body, line 88: "We do not claim the result is correct". | Make the sentence true before release (gate G2) or change it to what the record holds once G1 is complete, e.g. "reviewed adversarially by N passes, one dissenting". |
| A3 | blocker | 50; also 87-88, 417-420 | "Checks, Lean 4 proofs and every review are public under Apache 2.0"; "reproduce from the public repositories" | GitHub API, 2026-10-27: `StevenHrovat/gravity` and `StevenHrovat/dmp` both `"private": true`. #18, #19, #22, #24 are open drafts, #24 head is not on `main`. | Publish the repositories and merge or pin the cited drafts before release (gate G4), or say "will be public". |
| H1 | blocker | 414 | "every formal claim a theorem checked by two kernels" | `blind_record_same` (used by Proposition 2 and the dissent) lives only on #24; `get_check_runs` for #24 returns 0 runs, so no `lean-evidence` (nanoda) run exists for it. This pass checked it with Lean's own kernel only (246 theorems, see A). | Run `lean-evidence` on #24's head (or merge Blind.lean) and cite the run; until then say "checked by Lean's kernel; the second kernel pending". |
| S1 | blocker | 324-325 | "this is the verdict the first author accepted, and the independent verification he reports (Section 9) agrees" | Section 9's GLM-5.3 row reads "to be added"; no VERDICT.md or PR from that verification exists in gravity, dmp or im. A sentence citing it as agreeing is unbacked today. | Cite the GLM-5.3 record once it is a pull request (gate G1), or drop the clause. |
| F2-1 | blocker (release format) | 29 | `\thanks{Independent. Contact: to be set before release (a forwarding address, see README).}` | Placeholder and a pointer to an internal README on the title page. | Put the forwarding address in; drop "see README". |
| F2-2 | blocker (release format) | 374-375, 380-382 | Rows "to be added"; "Before release, the rows marked 'to be added' are filled ..." | Placeholder rows and an instruction to the editors inside the paper. | Fill both rows from their records and delete the instruction sentence. |
| F1 | major | 323-328 (and 312-316) | "Where they part. Only on Definition 1 ... the choice is a definition, not a calculation" | Harlow's area operator is central in each wedge algebra, but the global code state may be a coherent superposition of area sectors; a DMP structure is read in full by two witnesses, which decoheres across sectors. The paper's own Remark (236, fixed-area states [dhm]) says this, and #24 section 10.5 concedes it: "Two geometries that differ in a record ... cannot interfere until the record is gone". So both passes agree on a physical fact the paper omits: the dissent's construction is linearised gravity on one classical background, never a superposition of backgrounds. With that fact stated, "definition, not calculation" holds. | Add agreed fact (v): DMP forbids coherent superpositions of backgrounds (area sectors); the dissent models linearised gravity on one background. Replace "exactly like a DMP structure" by "like a DMP structure within one sector". |
| E4 | major | 274-275 | "With no local field there is no mediator for Claim 2 to forbid, and no local experiment to run. What remains is that DMP forbids superpositions of different global geometries, a superselection rule. So in 2+1 the verdict is CAN, up to that rule." | Point particles in 2+1 gravity interact topologically and scatter non-trivially ('t Hooft, Commun. Math. Phys. 117, 685 (1988), DOI 10.1007/BF01218392), and an interaction generically entangles. With matter, the global geometry is the configuration of the conical defects, so forbidding superpositions of global geometries forbids superpositions of the particles' relative positions: not a mild superselection rule. The 2+1 verdict has no check and no theorem behind it; its only source is prose (qg-verdict.md section 8, 14:00Z reply). | Restrict the 2+1 CAN to pure gravity without matter (moduli and boundary gravitons), or state that with massive particles the rule decoheres their relative configuration and the verdict there is open. |
| G2 | major | 209-210 | "this is as far as the published holographic code models go~\cite{happy}" | Published code models go further: bulk/boundary maps between local Hamiltonians, i.e. dynamics (Kohler and Cubitt, "Toy models of holographic duality between local Hamiltonians", JHEP 08 (2019) 017, DOI 10.1007/JHEP08(2019)017); the assembly is one root and five children. | "this is the kinematic content of the HaPPY model, on a tree of one layer". |
| B1 | major | 209 (and 45-46, 403-404) | "X1, X2 (on a tree) and X3 hold in an assembly that obeys all three axioms as written" | `assembly.py` encodes the eight sentences of the table (lines 174-194). It encodes nothing of the minting, the failure classes, the decay of freshness, retention, records that outlive the act, or DMP-completeness (Definition 1 asks for a DMP-complete assembly). | "in an assembly that encodes the eight sentences of the table"; say the assembly is not shown DMP-complete. |
| B2 | major | 184 | Row "Majority within a type" under the column "DMP, as written" | The phrase is absent from DMP 0.9.8 (`grep -i "within a type" vendor/dmp/*.md`: no hit); qg-verdict.md line 61 labels it "the owner, 06:53Z, gravity#19 level 0c". DMP's majority is T5: M1 and M2 over the pinned White Key seats of both sides, not erasure recovery of 3 of 5 children. | Label the row as the owner's reading (not DMP text), or map it to T5 and say the 3-of-5 encoding is a reading, not T5. |
| B3 | major | 288-292; 310-311 | "Content moved between parts by grant keeps its entanglement ... check [7] ... finds the record and the counts identical for all 16 pairs of mass contents" | In #24's `assembly.py` [7]: (a) no content is moved; a "grant" is a joint logical CNOT or CZ on two blocks (`ACTS`, `two_block_gate`); (b) the act list is hard-coded and every syndrome is trivial on code-space inputs, so "record and counts identical" holds by construction; (c) the result rests on one construction choice #24 section 10.2 states and the paper does not: "existence is the field register of each part ... the particle is its content". The faithful alternative, existence read per mass position, is in the same script and gives negativity 0. | State the construction choice and the alternative encoding that breaks [7] (task B asks for exactly this); say "acted on jointly under a grant", not "moved". |
| H2 | major | 291-292; 311 | "the Lean theorem blind_record_same proves the record-blindness from Axiom 3's existence clause"; "so the fluctuation stays coherent" | `evidence/Dmp/Blind.lean` on #24: the clause is the hypothesis, built into `blindRequest` (each witness's evidence is a function of `ex a.c` and `t` only); the theorem is the congruence that `run` then depends on existence only. It is about classical Boolean records and says nothing about coherence. | "assumes the clause in the form ... and proves the record is then a function of existence and time only; coherence is check [7]'s numerics". |
| E1 | major | 281-282 | "there is a DMP-complete configuration whose content runs H" | DMP-complete (the words, DMP 0.9.8): every axiom and theorem hold "and both chains prove it", every dependency pinned inside the repository. Nothing proves that for any configuration that runs a quantum theory; the argument shows only that DMP's text does not obstruct content. | "there is a configuration, not obstructed by DMP's text, whose content runs H"; or prove DMP-completeness. |
| D1 | major | 249-250 | "Any dictionary in which a DMP structure is the geometry predicts that gravity never entangles two masses" | Claim 2 (GGS) needs the field to be the only, local mediator. In DMP matter is content and content can be acted on across parts while records stay blind (check [7]); if Aziz and Howl are right (Nature 646, 813 (2025)), quantum matter content with a classical geometry can entangle. The live-debate paragraph (253-256) says only the refuter weakens; this sentence would fail too. | "... predicts that the geometry, as a local classical mediator, cannot by itself entangle two masses". |
| C1 | major | 216-219 | Claim 1: "... is held in full by at least two independent witnesses, and is therefore described by a commuting family of states: it cannot be in a superposition of two of its values" | Counter-model to the wording: each half prepares the same quantum state of the layout, a superposition, deterministically from the classical counts (both "recompute" it, Axiom 3); no-broadcasting is not violated because what is broadcast is the counts. What the argument establishes, and all Claim 2 needs, is weaker: the structure depends on the parts only through classical records, an entanglement-breaking (measure-and-prepare) channel. The verdict survives; the sentence as worded does not. | "... its dependence on the parts factors through classical records, so as a mediator it acts as a classical one". |
| P3 | major | preface.tex 27 | "my proposed Information-Hawking radiation actually mapped 1:1 to actual Hawking radiation" | The record contradicts it: cold read (#22) row Q5, "Hawking's radiation is a number, a temperature ... derived from quantum fields"; qg-verdict.md section 9 row Q5, "no temperature follows, so the absence stays". The body makes no such claim. | The owner's words, his call; flag that the record does not back "1:1". |
| P2 | major | preface.tex 10 | "version pinned to at least v1.0.0" | `vendor/dmp/VERSION` = 0.9.8; DMP `main` `45d3822` is 0.9.8. The owner kept it as aspirational (README, answer 4). | His call; if kept, "will be pinned". |
| D2 | minor | 253-256 | The live debate in one paragraph | Incomplete in one point that matters to Section 10 item 3: Howl says the classical-gravity effect is far smaller and unlikely to be seen soon, so a positive result at the BMV rate would still point to quantised gravity (physicsworld.com, "Classical gravity may entangle matter, new study claims"). Also missing: Marletto and Vedral, arXiv:2510.19969, "Classical Gravity Cannot Mediate Entanglement by Local Means". | Add one sentence on the size and scaling of the Aziz-Howl effect and cite 2510.19969. |
| E2 | minor | 287-288 | "A universal quantum computer simulates any finitely realisable physical system (Deutsch)" | Deutsch 1985 states this as a physical principle (the Church-Turing principle) and shows the universal quantum computer is compatible with it; it is not a theorem, and a continuum theory is simulated only to finite precision. | "by Deutsch's Church-Turing principle, to any finite precision". |
| E3 | minor | 81-85 | Result paragraph | "Host" is satisfied by any substrate that allows universal quantum computation as content; the paper says so only at line 297 ("Hosting is cheap"). The introduction and abstract present "can host" as half of the result without that sentence. | Carry "hosting is cheap; the content of the result is the cannot-model half" into the Result paragraph. |
| E5 | minor | 273, 276 | "It is an exactly soluble quantum theory, a Chern-Simons theory" ... "whether pure 3D quantum gravity exists as a consistent theory is open" | Internal tension; Witten 1988 says "exactly soluble classically and quantum mechanically", Witten 2007 (arXiv:0706.3359) and Maloney-Witten 2010 revisit it. Brown-Henneaux holds for Λ < 0 only. | "perturbatively exactly soluble as a Chern-Simons theory (Witten 1988), with a holographic boundary algebra for Λ < 0". |
| F3 | minor | 312-313 | "In any quantum error-correcting code the quantum Ryu-Takayanagi formula reads ..." | Harlow's abstract says "any code"; the theorem is stated for codes with complementary recovery (operator-algebra QEC), arXiv:1607.03901. | "In any code with complementary recovery". |
| G1 | minor | 156 | "No published discrete model reaches X5" | Causal dynamical triangulations report a 4D de Sitter universe from a Lorentzian sum over geometries (Ambjørn, Goerlich, Jurkiewicz, Loll, "Planckian birth of the quantum de Sitter universe", arXiv:0712.2485); not a derivation of Einstein's equations, but evidence in that direction. | "No discrete model has derived X5; causal dynamical triangulations report evidence of a de Sitter phase". |
| G4 | minor | 140; abstract 42 | "Fixed before the assembly was built"; "fix five expectations before building" | The record cannot show the order: the table X1-X5 and `assembly.py` arrive in the same commit `2cb3d62` (13:46Z). | "fixed before the run; the record holds both in one commit", or cite where they were fixed first. |
| C2 | minor | 225-226 | "every standing of the trust field is such a record (Axiom 2)" | Axiom 2 says "A standing is evidence with a validity"; that grants leave records is Axiom 3 ("Every grant, every use and every loss of trust leaves a record"). | "(Axioms 2 and 3)". |
| B4 | minor | 202, 205 | Checks [4] and [5] on the halves' readings | Both pass by construction: code-space inputs give trivial, deterministic syndromes. The paper says so for [5] (line 211) but not for [4]. | Add "by construction" to [4] as the paper does for [5]. |
| H3 | minor | 100, 338 | "a Lean 4 model of DMP whose recipe type contains every layout the system admits"; "Every layout the system admits is a term of one closed inductive type" | Not a theorem: that the type contains every admissible layout is a modelling assumption (DMP's assumption register lists "the mapping of code to acts"). `Recipe` is a structure (a count and a line function). | "we model every layout as a term of ...". |
| S2 | minor | 370 | "13 conflicts, 8 divergences" | Cold read (#22) section 7 tally: thirteen requirements, of which seven conflicts, three matches in flavour, three absences; eight divergences. (qg-verdict.md section 9 repeats "thirteen conflicts".) | "13 requirements (7 conflicts), 8 divergences". |
| S3 | minor | 370 | "refused to arrange the parts as quantum gravity" | The record: section 6 "every dictionary entry offered so far fails" and no reply integrated; "refused" is the owner's word (qg-verdict.md section 9, 14:30Z). | "found every offered dictionary entry failing and integrated none of the replies". |
| S4 | minor | 419 | "the review passes as pull requests #18-#24" | #20 is the earlier paper draft, not a review pass; #24's head `60a1616` is not on the commit named (06231b8). | "#18, #19, #21-#24; #24 at 60a1616". |
| A4 | minor | 38-41, 70-71 | "every act leaves a record that its witnesses read in full while anyone else sees only counts" | Axiom 3: "Any other reader sees the counts always and the content only by a grant". | "... sees the counts always, the content only by a grant". |
| A5 | minor | 105-106 | "theorems T1-T40" | DMP 0.9.8 chapter 01 holds T0 to T6, T19 to T40, T24b, T24c, T-P; T7 to T18 do not exist (`grep '^## T' vendor/dmp/*.md`). | "theorems T0-T40 (T7-T18 vacant)" or "37 theorems". |
| P4 | minor | preface.tex 7 | "Showing provability for the effects of quantum gravity as a subet within DMP" | The body proves no effect of quantum gravity; it reproduces a toy entanglement (check [7]) and argues hosting. The owner's words; flagged only. | His call. |
| F2-3 | minor | guid.tex 1-3; preface.tex 1-4 | Source comments with the owner's timestamps and editorial notes | Meta-comments in the published source; harmless in the PDF. | Trim to licence and build lines before release. |

## A. Reproduce

| What | Paper says | Got | Command |
|---|---|---|---|
| assembly, `main` 06231b8 | 18 of 18 | **18 of 18**, 45.7 s wall (2 min 50 s CPU) | `python3 docs/qg-verdict/assembly.py` |
| assembly, #24 `60a1616` | 25 of 25 | **25 of 25**, 45.0 s | `git show pr24:docs/qg-verdict/assembly.py > a.py; python3 a.py` |
| Lean, `main` | 243 theorems | **"OK 243 theorems, none resting on more than propext, Quot.sound, Classical.choice"**, exit 0 | `evidence/tools/check.sh`, Lean 4.34.0 (commit 293d5d0c), pin check passed |
| Lean, #24 | 246 theorems | **"OK 246 theorems ..."**, exit 0 | same, on a worktree of `60a1616` |
| Lean unchanged since 6d09660 | yes | `git diff --stat 6d09660 origin/main -- evidence` is empty; #24 adds only `Blind.lean` (+73) and one README line | |
| run 53 at 6d09660 | green, both kernels | `lean-evidence` run 53, head `6d09660`, conclusion `success` (Actions API) | |
| check values | [3] 0 and 2 bits; [4] 15 syndromes, fidelity 1, 0.50; [5] 2.828 and 2; [6] 0.5 and 0; [7] 16 pairs, 0.5 | all as stated; [4] read-content fidelity 0.497452 (Haar mean, tolerance passes); [2] tests 70 contiguous regions (lengths 1-10, 7 starts) | |
| "about a minute", "numpy only" | | 45 s; imports numpy, itertools only | |

No number in the paper differs from what this pass got.

## B. Each check

- [1] computes the minimum entropy over all 20 three-leg cuts of the six-leg state: 3 bits, a perfect tensor. As stated.
- [2] checks both tile maps are isometries and S(A) = min cut for 70 contiguous regions with the bulk legs fixed to |0>. As stated; the
  encoding of "the fewest hops in total" as the minimal cut is a reading of a routing sentence, not a quotation.
- [3] computes I(R:pair) and I(R:triple) for the root's logical qubit. As stated; the DMP side is B2.
- [4] two independent full stabilizer reads per block; fidelity 1; 15 distinct syndromes; correction restores; reading logical Z then X
  gives ~0.5. As stated; passes by construction (B4).
- [5] CHSH 2√2 on a logical Bell pair, 2 on deterministic verdicts, commutator 0. As stated; the paper already notes the verdict value is
  trivial.
- [6] CNOT A→M, CZ M-B, CNOT A→M: negativity 0.5 coherent, 0 with M dephased after the first coupling. As stated. Dephasing M there equals
  measuring A in Z, so the check is the LOCC theorem on its smallest case, which is what the paper claims.
- [7] see B3: correct numerics, but a construction choice the paper does not state, and a faithful alternative encoding (existence per
  position) that breaks it, run in the same script.

## C. Claim 1

Searched for a structure DMP defines between parts that can be in superposition without breaking Axiom 3: the layout, the trust field,
the order of acts, the counts, admissions (grants), independence and the failure-class list, the tree. Each is either a record "every
witness of that act can read in full", a count "any other reader sees ... always", or recomputed by both halves from such records. None
escapes. The one counter-model found (C1) breaks the wording, not the conclusion: a deterministic quantum function of classical records
is still an entanglement-breaking mediator. The paper's remark that the claim is close to definitional is fair: it is the cost of
Axiom 3's "absolute Observability" under the no-broadcasting theorem (Barnum et al. 1996, verified). It holds.

## D. Claim 2 and the 2025 debate

Claim 2 is the LOCC theorem plus Galley, Giacomini and Selby (Quantum 6, 779 (2022), arXiv:2012.01441): entanglement generation,
mediation by the field, and classicality cannot all hold. Stated correctly. Its use overreaches once (D1). The paper's account of the
debate is accurate as far as it goes: Aziz and Howl argue classical gravity entangles through virtual matter processes (Nature 646,
813-817 (2025)); Marletto, Oppenheim, Vedral and Wilson (arXiv:2511.07348, "Classical gravity cannot mediate entanglement") and Diósi
(arXiv:2511.00852, "No, classical gravity does not entangle quantized matter fields") dispute it. It is not sufficient on the size of
the effect (D2).

## E. Proposition 2 and 2+1

"Host" is not empty but it is weak: it holds for any substrate that allows universal quantum computation as content (E3); the paper
says so once. The proposition overclaims "DMP-complete" (E1) and treats Deutsch's principle as a theorem (E2). The 2+1 verdict is the
weakest physics sentence of the paper (E4, E5).

## F. The dissent

The paper's account of #24 is accurate: #24 section 10.1 (background field split, DeWitt 1967; Christodoulou et al., PRL 130, 100202
(2023), verified), 10.2 (existence clause, Blind.lean, check [7]) and 10.3 (Harlow's area operator) are summarised faithfully. Check [7]
itself places the mediator inside part M as its content, which is the first pass's "gravity inside the content" horn: on the evidence
both passes ran, the split is a choice of definition, as the paper says. The account omits one agreed fact (F1). Harlow is stated
correctly up to the complementary-recovery condition (F3).

## G. Proposition 3 and the physics sentences

Rabinovich and Raz (Discrete Comput. Geom. 19, 79-94 (1998)): an n-cycle needs distortion at least n/3 − 1 in any tree; holds. The
boundary of the Bruhat-Tits tree is the p-adic projective line, totally disconnected (Heydeman et al. 2018; Gubser et al. 2017); holds.
2+1: no local degrees of freedom, conical deficits (Deser, Jackiw, 't Hooft 1984); holds. LIGO measured local degrees of freedom; holds.
Fixed-area states are special (Dong, Harlow, Marolf 2019); holds. Findings: G1, G2, G4, E4, E5.

## H. Lean

Names checked on the commits named: `empty_recipe_proven` (`Dmp/Cmb.lean:341`, `main`), `digest_not_injective` (`Dmp/Cmb.lean:237`,
`main`), `Recipe.verdict_proven_iff` (`Dmp/Complete.lean:33`, `main`; `agree` is an input, as the paper discloses), `gate_obeys_chsh`
(only on #17, `Dmp/NoGo.lean:159`, unmerged, as stated), `blind_record_same` (`Dmp/Blind.lean:34`, #24 only). The verdict order
`refuse < hold < pass` (`Dmp/Gate.lean:10`), Denning, the frame rule, Goguen-Meseguer (`Dmp/Theory.lean:17-32`) and Malkhi-Reiter
fail-prone systems (`Dmp/Layer.lean:16-24`) are named in the files as the paper says. "Independence is relative to a declared class
list": `empty_list_makes_everything_independent`, `one_person_is_no_duality` (`Dmp/Layer.lean:89,117`); holds. The hatch list of
`check.sh` covers sorry, admit, axiom, native_decide, unsafe, implemented_by and extern; holds. Findings: H1, H2, H3.

## R. References (35)

| # | Key | Result | Checked against |
|---|---|---|---|
| 1 | cirelson | OK (pp. 93-100) | DOI 10.1007/BF00417500 |
| 2 | chsh | OK | PRL 23, 880, first page |
| 3 | rt | OK | arXiv hep-th/0603001 journal-ref |
| 4 | adh | OK | arXiv:1411.7041, DOI 10.1007/JHEP04(2015)163 |
| 5 | happy | OK (arXiv:1503.06237 confirmed; JHEP 06 (2015) 149 not shown in the result, matches the DOI 10.1007/JHEP06(2015)149) | arXiv listing |
| 6 | bose | OK | DOI 10.1103/PhysRevLett.119.240401 |
| 7 | mv | OK | DOI 10.1103/PhysRevLett.119.240402 |
| 8 | ggs | OK | quantum-journal.org/papers/q-2022-08-17-779 |
| 9 | laflamme | OK (pp. 198-201) | journal record |
| 10 | wz | OK | Nature 299, 802-803 |
| 11 | dieks | OK | Phys. Lett. A 92, 271 |
| 12 | barnum | OK | arXiv quant-ph/9511010 journal-ref |
| 13 | bph | OK | DOI 10.1038/ncomms8908 |
| 14 | dhm | OK | arXiv:1811.05382, JHEP 10 (2019) 240 |
| 15 | vw | OK | DOI 10.1103/PhysRevA.65.032314 |
| 16 | azizhowl | OK (pp. 813-817) | search record of the Nature article |
| 17 | movw | OK (title, authors) | arXiv:2511.07348 listing |
| 18 | diosi | OK (title) | arXiv:2511.00852 listing |
| 19 | hmss | OK (pp. 93-176) | DOI 10.4310/ATMP.2018.v22.n1.a4 |
| 20 | gubser | OK (pp. 1019-1059) | DOI 10.1007/s00220-016-2813-6 |
| 21 | rr | OK (pp. 79-94) | DOI 10.1007/PL00009336 |
| 22 | djt | OK | DOI 10.1016/0003-4916(84)90085-X |
| 23 | witten88 | OK (pp. 46-78) | DOI 10.1016/0550-3213(88)90143-5 |
| 24 | bh | OK (pp. 207-226) | DOI 10.1007/BF01211590 |
| 25 | mw | OK | DOI 10.1007/JHEP02(2010)029 |
| 26 | ligo | OK | PRL 116, 061102 records |
| 27 | deutsch | OK (pp. 97-117) | DOI 10.1098/rspa.1985.0070 |
| 28 | dewitt | OK | Phys. Rev. 162, 1195, scanned front matter |
| 29 | christodoulou | OK | DOI 10.1103/PhysRevLett.130.100202 |
| 30 | harlow | OK (arXiv:1607.03901 confirmed; CMP 354, 865 not shown in the search result) | arXiv listing |
| 31 | lean4 | OK (pp. 625-635; the volume prints as LNAI 12699, a subseries of LNCS) | DOI 10.1007/978-3-030-79876-5_37 |
| 32 | denning | OK (pp. 236-243) | DOI 10.1145/360051.360056 |
| 33 | mr | OK (pp. 203-213) | Distributed Computing 11(4), Duke record |
| 34 | ohearn | OK (pp. 1-19) | DOI 10.1007/3-540-44802-0_1 |
| 35 | gm | OK (pp. 11-20) | IEEE Xplore document 6234468 |

No fabricated or wrong citation found. Two journal references (5, 30) were confirmed by their arXiv record only, because the search did
not show the journal page; check those two on the publisher's page before release.

## P. The preface

Not judged: the owner's conjectures and opinions (QG as a subset of DMP, the primordial DoE, the AGI note, the two impossible things,
the note on AI). Checked: the four-reviews sentence is **false today** (P1, gate G2). "G0 is not minted, it's full Authority is held by the
owner" matches DMP G0 ("Until the first LHC is minted, the owner's own words stand for both halves"). "Pinned to at least v1.0.0" does not
match 0.9.8 (P2). The Hawking-radiation sentence is contradicted by the record (P3). "Fable 5.1 ... refused to make it fit" matches the
record in substance (#22 integrated none of the replies; Fable 5.1 per its commit trailers). "Opus 5.5 was finally able ... to assemble
the parts" matches #23 (Opus 5.5 per its commit trailer), whose result is CAN NOT model. "No other approach for hardened security got
through their classifiers": unknown, no record.

## S. Section 9

| Row | Accurate? |
|---|---|
| Physics pass, Fable, #19 draft | Yes: "It does not hold as an approach to quantum gravity, and the failure is ... a fork" (`docs/physics.md`); commit trailer Fable 5.1. |
| Second witness, Opus 5.5, #18 draft | Yes: "the axioms force the trust half to be classical" (`docs/physics-opus.md`); trailer Opus 5.5. |
| Refutation, Fable (Team), #21 merged | Yes: B4a "refuted (not implied)", A7 (the strong ETM) "refuted" (`docs/refutation.md`). |
| Cold read, Fable (Team), #22 draft | Counts and wording: S2, S3. |
| Verdict, first pass, Opus 5.5, #23 merged | Yes. |
| Verdict, second pass, Opus 5.5, #24 draft | Yes: CAN, 25 of 25. |
| GLM-5.3, Final fault verification | Placeholders (F2-2); cited as agreeing before its record exists (S1). |

## F2. Format

Abstract: 1,753 characters of plain text with whitespace collapsed (1,763 counting the raw LaTeX), under 1,920. Build: `pdflatex` twice
in a clean folder, exit 0, 12 pages, no warning, no overfull box, no undefined reference; every cross-reference resolves. Leftovers:
F2-1, F2-2, F2-3.

Release-blocking findings: 6
