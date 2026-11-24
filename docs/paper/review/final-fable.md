# Final fault verification of GUID v8: fable

Stage 3 of `../REVIEW.md`, prompt `final-verification-prompt.md`, VERIFIER = fable. Release candidate `f4592e3`
(branch `ccr-be614210-u4r7na`, pull request StevenHrovat/gravity#37). Date of the run: 2026-11-24.

**How this was done.** A fresh clone of the release candidate inside a Linux environment (WSL, Lean v4.34.0, Mathlib
v4.34.0), a fresh `lake update` and Mathlib cache, and a build folder of its own. The paper was read in full from
`docs/paper/draft/*.md` and built to LaTeX. Every sentence of a finding carries its source: a command with its output, a Lean
declaration, or a page that was fetched. The other verifier's work was not opened. The part reviews `part-R*.md` were consulted
only where a finding touches them (R3); nothing here relies on them. Hand derivations (the surgery steps of task E, the
algebra of tasks D and E) are given as arguments a reader can follow, not as citations. Not done, and said where it matters: the ball-arithmetic
certificate of the first box was not re-run; IM's `proof/` package was read, not built; the external Lean libraries of others
were not rebuilt (as the paper also says).

## Findings

Severity: **blocker** (must change before release), **major** (a sentence stronger than, or different from, its evidence),
**minor**, **typo**. Line numbers are those of the Markdown source at `f4592e3`; "tex" is `docs/paper/latex/guid-v8.tex`.

| Id | Severity | Location | Sentence | Evidence | Fix |
|---|---|---|---|---|---|
| F-01 | blocker | `00-abstract-introduction.md` 32-35; tex 43; PDF p. 1-2 | "Editorial notes for the owner (to remove before publication): (1) the Riemann sentence is phrased as your reading; ..." | `python tools/paper-latex.py` then `grep -n "to remove before publication" docs/paper/latex/guid-v8.tex` gives line 43: the note is typeset in the paper. | Remove the paragraph from the typeset source (decide its three points first: the Riemann sentence, the umlaut, "One thing led to three"). |
| F-02 | blocker | III.4.4 (`03` 396-397, tex 993); IX.2 (`09` 101-102, tex 2334); IX.7 item 3 (`09` 290, tex 2476); VII.4.2 (`07` 224-225, tex 1931) | "Until it is, the abstract and the introduction should say ... That wording is the coordinator's to place; this part does not edit them."; "`Unified/HodgeAPI.lean` is not yet part of the aggregate import `Unified/All.lean`; that is left to the coordinator."; "its DOI is to be added to the bibliography" | `grep -n -i "coordinator\|to be added" docs/paper/latex/guid-v8.tex`: lines 993, 1931, 2334, 2476, 2657. These are instructions to an editor and one placeholder, typeset as body text. `grep -n HodgeAPI docs/mass-gap/formal/ProofPhase/Unified/All.lean` is empty, so the IX sentence is still true as a fact, but it is a to-do. | Delete the instruction sentences; add the Zenodo record to the bibliography or drop the clause; either import `HodgeAPI` in `All.lean` or state the fact without the to-do. |
| F-03 | blocker | Bibliography (tex 2838, 2905; `references.md` rows 114, 115); cited at IV.5.5 (`04` 234-236) and IV.6 (`04` 296) | "Bogomolny 1976 *(not yet identified)*"; "Ito *(not yet identified)*", both cited as **[classical]** | `grep -n "not yet identified" docs/paper/latex/guid-v8.tex`. A lookup (Crossref, web search; haiku subagent, 2026-11-24) found no record for either row; the likely Bogomolny work is "Stability of classical solutions", Sov. J. Nucl. Phys. 24 (1976) 449, not confirmed on a record; for Ito no candidate could be confirmed. | Identify both works on a record and cite them, or remove the two claims that rest on them (the Bogomolny bound has textbook sources; the "upper decimation flows to strong coupling" sentence needs its source or goes). |
| F-04 | blocker | Abstract (`00` 50-51); Introduction (`00` 118-120); verification prompt, claim 1 | "**The one assumption.** One step is the same on every card: that the one box is a running, DMP-complete system, its gate shared at every scale."; "the open step is the same on every card: that the box is a running system whose gate is shared at every scale" | False for two of the seven cards by the paper's own text and Lean. Navier-Stokes: VII.7 (`07` 291-303) "it is not DMP-complete, and blowup is the expected consequence", Lean `ns_not_complete` (`ETM/RotationInstances.lean`); the card's open step is `PeriodContraction` (VII.5). GU: X.8 (`10` 257-258) "The GU card's open step ... is not a statement about this box", and the GU box passes, proved (`gu_box`, `ETM/CardBox.lean`). For the other five the identification is marked **[reading]** in III.4.4 ("**[reading]** for the identification", `03` 305-306) but is unmarked in the abstract and the introduction. | Say it as it is: "On five cards (Yang-Mills, GRH, NP vs coNP, BSD, Hodge) the open step can be read as one statement, that the card's box is DMP-complete (a reading; each is a different mathematical statement). Navier-Stokes is the expected negative, and GU's open step lies outside its box." |
| F-05 | major | Abstract (`00` 82-83); A.5 (`12` 116-121); III.4.4 (`03` 326-327) | "G2 is rigid under the one assumption (in Lean, from that assumption and a named surgery input)." | `ETM/G2Rigidity.lean`, `g2_rigid_of_one_assumption`: `G2Rigid : Prop`, `E : Type` and `η : E → ZMod 2` are free variables; there is no G2 in Lean. Hypotheses: `hsurg : G2Rigid ↔ Function.Surjective η` (External), `hB : B.DMPComplete x₀`, and `hX64 : OpenStep "III.64: ..." (SharedGate B x₀ (G2 box))`. `SharedGate` (`Arsenal/Rotation.lean`) demands a map that keeps step, gate factor and marker, so `dmpComplete_hom` transfers completeness at once: the hypothesis labelled III.64 is "the G2 box is a marker-preserving copy of a complete box", which is at least the conclusion. It is not the assumption of III.4.4 ("the one box is a running, DMP-complete system"); that one is the plain hypothesis `hB`. The same schema applied to the Navier-Stokes box would contradict `ns_not_complete`, so it cannot be an assumption made of every box. A.5 says "a reformulation of the question, not evidence for its answer"; the abstract does not. | Abstract: "G2 is rigid if its rigidity box shares the gate with a certified box (in Lean; the sharing is a named hypothesis at least as strong as the rigidity, and the surgery input is a named slot)". |
| F-06 | major | III.4.4 (`03` 298-306); abstract (`00` 50-52); IV.0 O2 (`04` 39-48), IV.9.5b (`04` 379) | "This is the one place where the paper states what it assumes."; "The paper states it once (Part III) and marks every result that uses it as conditional on it."; IV.9.5b "**[conditional]** on the one assumption (III.64, III.66)" | The assumption is stated once in prose, as a reading ("**[reading]** for the identification; **[open]** as a statement about each object"). It has no single formal statement. In Lean it appears as three different hypotheses: each card's own `OpenStep` (`FineOneBox`, `ScaleSign`, `CrossingCost`, `BSDStatement`, `HodgeConjecture`, `PeriodContraction`); `R136a1 "the gate is shared across scales" (SharedGate B x₀ C x)`, a schema over `B` and `C` (`scale_certificate`); and the G2 instance (F-05). For Yang-Mills it bundles two statements that the paper proves independent in its model (`gap_not_lower`, `gap_and_lower_compatible`, `Closures/NonTrivialSplit.lean`): O1 and the scale-uniform lower bound. No implication from O1 or from III.64 to the lower bound exists in Lean or in prose; III.64a places it there as a **[reading]**. So "[conditional]" on IV.9.5b marks a definition ("the assumption includes the lower edge"), not a derived consequence. | State the assumption as a schema ("for each card: its box is DMP-complete; across scales: the marker travels with the gate") and list its instances; mark IV.9.5b "[open]; part of the one assumption by the owner's reading (III.64a)". |
| F-07 | major | Abstract (`00` 85, 101-102); prompt claim 2; IV.0 (`04` 27); VI.6 (`06` 156-167); VII.2 (`07` 79-85); VIII.2 (`08` 73-79); IX.2 (`09` 90-98); X.2 (`10` 49) | "One open step per card"; "one card per problem are machine-checked"; "each open step is stated in the exact form that would close it" | Per part: Yang-Mills "leaves four things open" (O1 to O4). P vs NP lists four open steps N1 to N4. Navier-Stokes has three cards (`routeI`, `regularity`, `abProblem`), each with its own open step. BSD has two cards and a slot. Hodge has five cards, two with an open step. GU "is **not a `Problem` card in the Lean API**" (X.2), so "one card per problem ... machine-checked" fails there. The NP open step has three names: abstract "lifting with constant-size gadgets" (`LiftCPConst`, III.7k); Part VI "interface hardness at width 3" (VI.4.10); the Lean card `CrossingCost` (`API/NP.lean`). No statement relates VI.4.10 to `LiftCPConst`. | In the abstract say "one card per problem with one named open step in Lean (GU: a box, no card), and the further open items of each part listed there"; pick one NP open step and state how the others relate to it. |
| F-08 | major | Abstract (`00` 67-68, 92); Part VI | "*NP vs coNP.* ... the equivalence of the lifting interface with lifting by constant-size gadgets."; open: "lifting with constant-size gadgets, and with it super-polynomial lower bounds for strong proof systems" | The equivalence is real Lean (`Proof/SoundAPI.lean`, `liftCPConst_iff_extract`; ledger row VI.4.11) but Part VI never states it: `grep -n -i lifting docs/paper/draft/06-part-VI-pnp.md` finds only the last line of VI.10. So an abstract item under "What is proved" has no section in the paper. "Strong proof systems": `LiftCPConst` is a statement about cutting planes on lifted formulas; it gives nothing for Frege or extended Frege, and VI.6 itself says "CP is not the strongest system". | Add VI.4.11 to Part VI (one paragraph, with `LiftCPConst` and `ExtractAPI`), and replace "for strong proof systems" by "for cutting planes on lifted formulas". |
| F-09 | major | IV.0 (`04` 29-38), IV.5.6 (`04` 245-265); abstract (`00` 63, 87-88); III.1 (`03` 61-63) | "(O1) The one-box statement"; abstract: "O1, the hand-over inequality for every outside, uniformly in the scale"; "O1 is exactly DMP-completeness of the Yang-Mills box" | "O1" names four statements that are not identified with each other in Lean: (i) the number `F_e(L) - 2C > log mu_4` for the torus free energy, where IV.0 says "for the number it is a heuristic" and a "sufficient route"; (ii) `FineOneBox T` (`OneBox/Fine.lean`), the form `yang_mills_assembly_onebox` uses; (iii) `YMOneBox Fe μ` for an arbitrary `Fe : Ω → ℝ` (`Unified/YangMills.lean`), the form of `o1_iff_complete` and of III.2; (iv) `HandoverSide` (O1 at mu = 1 + sqrt 2). `o1_iff_complete` is the equivalence "a uniform lower bound on `Fe` iff a uniform upper bound on `min 1 e^{-Fe}`", with no Wilson measure; `fineOneBox_iff_complete` holds because the gate factor `ymFac` is defined as the infimum of the ratios for which the criterion holds. Both are true and both are restatements. Only (ii) feeds the assembly. | Name `FineOneBox` as the open step in the abstract and say that the number is a heuristic route to it; say in the abstract that the equivalence with the box is a restatement (as II.4e says of the card boxes). |
| F-10 | major | Abstract (`00` 89-91); V.0 (`05` 14-16) | "RH and GRH for Dirichlet L-functions were proved in Lean by others in November 2026, by a route that does not use positivity" | The paper contradicts itself: V.0 says "Its sign is the non-negative coefficients of Landau's theorem", II.11 says "Positivity enters in the instances", and the project's own source note (`docs/rh-guide/SOURCES.md`, S3) records that the author's note credits "Guinand-Weil ... with the sign". What the project traced is that the route does not use *Weil's positivity criterion*. The route description ("Landau's theorem applied to a one-sided square-root bound ... from a Stepanov-type size balance") rests on the author's 4-page note and on reading about ten files of a library of 175,187 modules (SOURCES.md, S4; module count: https://math.mit.edu/~drew/grh/). | Abstract: "by a route that, as far as this project traced it, does not go through Weil's positivity criterion". Keep "[external, traced]" on every sentence about the route. |
| F-11 | major | Abstract (`00` 89); V.4 (`05` 176-190); II.5.2 (`02` 223-225) | "*GRH:* Weil positivity beyond the first boxes, a margin that survives the growth of the support." (under "What is not proved") | For zeta and for Dirichlet L-functions the truth of Weil's positivity now follows from the external theorem and Weil's criterion (classical, II.9, V.1 row II.9.4). What is open is a proof from arithmetic alone, and GRH beyond Dirichlet. The Lean card (`API/GRH.lean`: `ScaleSign` for a finite model; `tie_in` and `grh_box_of_RH` with Mathlib's `RiemannHypothesis` as `External`) is about zeta; for L-functions beyond Dirichlet the paper has no card (V.1.5b: explicit formula and criterion "not yet in Lean"). Also "a margin that survives" sits next to III.45b, which says a uniform margin is false for zeta's zero measure. | Abstract: "*GRH:* a direct proof of Weil positivity from the primes and the real place (for zeta and Dirichlet it holds through the external proof), and GRH beyond Dirichlet L-functions, for which no card is written yet." |
| F-12 | major | Abstract (`00` 64-65, 53-54); III.1 (`03` 72-76); III.4.4 (`03` 381-384) | "Weil's form positive with an explicit margin on the first box ... (certified in ball arithmetic)"; "The three inputs are numbers computed in ball arithmetic" | `docs/unified/GRH-ONEBOX-CERT.md` (headed "Private working note") marks ten steps "[proved here]": the tail bound, the cross-term bounds and the identification of the abstract form with Weil's form are analytic estimates proved in that note, not numbers and not in Lean; `onebox_positive` (`GRH/OneBoxCert.lean`) takes them as hypotheses `hfin`, `hcross`, `htail` for an arbitrary inner product space. The logs exist and carry the three margins (`grh_onebox_cert-a0.69.log`: "RESULT a = 69/100: [6.417e-13 +/- 3.01e-17]"). The run was not repeated here and the note's analytic section was not re-derived here. | Mark it "[certified] for the enclosures, [paper] for the analytic estimates of the note (not independently read)" in III.1, III.4.4, III.6 and the abstract. |
| F-13 | major | Abstract (`00` 74-75) | "*Hodge.* Hodge-Riemann positivity, the Hodge index as linear algebra, Weil's bound for curves, eigenvalues on the circle, and Lefschetz (1,1) as a diagram chase." (under "What is proved") | In Lean the Hodge-Riemann positivity is a field of the structure, an input: `PolHS.pos : ∀ x, x ≠ 0 → 0 < Q (h weil x) x` (`Unified/HodgeLinear.lean`); what is proved is that `Q` is positive on the circle-fixed vectors. Weil's bound is proved from two `External` slots (intersection numbers; the Hodge index property). Part IX says this exactly ("The geometry ... enters as named `External` slots"); the abstract's first and third items read as theorems. | "*Hodge.* The linear algebra of the positivity: from the Hodge-Riemann relations (an input), positivity on Hodge and algebraic classes; from the Hodge index property (an input), Weil's bound for curves; ..." |
| F-14 | major | Abstract (`00` 44-46); II.7 (`02` 292-295) | "The test, the machine under it ... and one card per problem are machine-checked in Lean 4 with Mathlib, standard axioms only, and re-checked by independent kernels" | II.7 itself: "**No independent-kernel run has yet covered** `ETM/CardBox.lean` (claim II.4e) ... nor the last two theorems of `ETM/Complex.lean` ... A run at the final commit is still to be made." `git diff --stat 1d71a05 f4592e3 -- docs/mass-gap/formal`: `CardBox.lean` (+136), `Complex.lean` (+16), `ETM.lean` (+1) are newer than the last independent run. So the card boxes are not re-checked by an independent kernel at the release candidate. | Run `tools/independent-check.sh` at the release commit and record it, or say in the abstract "re-checked by independent kernels up to commit `1d71a05`". |
| F-15 | major | Bibliography and text | Works cited by author and year with no bibliography entry | `python` scan of author-year pairs in `draft/*.md` against `references.md`: Buhler-Gross-Zagier 1985, Dokchitser-Dokchitser 2010, Goldfeld 1982, Kato 2004, Kollar 1992, Kolyvagin 1988-90, Monsky 1996, Necas-Ruzicka-Sverak 1996, Rubin 1987, Skinner-Urban 2014 have no row. The Lean library of the Riemann hypothesis and Dirichlet GRH, cited in the abstract and V.0, has no row (`grep -n -i "riemann" docs/paper/references.md` shows no such entry); its sources exist: https://leanprover-community.github.io/blog/posts/riemann-hypothesis/ , https://math.mit.edu/~drew/grh/ , https://github.com/leanprover-community/riemann-hypothesis (fetched 2026-11-24). The Zenodo record of VII.4.2 has none (F-02). | Add the rows. |
| F-16 | major | Bibliography (tex 2983 and the next Weil entry; tex 2902; tex 2848) | "Andre Weil, *Sur les courbes algebriques ...*, ... `https://arxiv.org/abs/1109.5230`"; "E. Hopf, ... `https://portal.mardi4nfdi.de/wiki/Item:Q2524936`"; "Georg Cantor, ... `https://en.wikipedia.org/wiki/Cantor%27s_theorem`" | arXiv 1109.5230 is M. Audin, "La guerre des recensions", a different work (https://arxiv.org/abs/1109.5230); it is attached to both Weil 1948 entries (rows 82, 83). The Hopf link is the record of a 1965 paper by Bauer (https://portal.mardi4nfdi.de/wiki/Item:Q2524936). The bibliographic data of the three works themselves are right (zbMATH 0036.16001, 0037.16202 for Weil). The typeset entries also carry working remarks ("not settled without the journal page", "from a Cambridge reference list in a search snippet"). | Replace the three links by the works' own records; strip working remarks and the status tags from the typeset bibliography. |
| F-17 | major | Abstract as a whole (`00` 37-102) | (format) | `python`: 1026 words, 6155 characters, 16 bullet items, bold run-in headings. It is not plain text. For scale: arXiv's abstract field is limited to 1,920 characters (https://info.arxiv.org/help/prep.html; recalled, not fetched for this report). | Write a plain-text abstract of one or two paragraphs; move the lists to the introduction. |
| F-18 | minor | I.0 (`01` 10-11), I.1 (`01` 45), II.8 (`02` 300-302), IV.1 (`04` 75); personal note (`00` 14-15) | "the three problems of Parts IV to VI"; "In all three problems"; "All three problems run along the same four links"; "the one problem of the three"; "one Millennium Problem attempt turned into three" | The paper covers seven problems (abstract, first sentence). The personal note is the first author's (the editorial note of F-01 already raises it). | Say "the first three problems (Parts IV to VI)" where three is meant. |
| F-19 | minor | Abstract (`00` 81), Introduction (`00` 131-132); A.5 (`12` 107); III.4.4 (`03` 350-351) | "Sp(2) is rigid (a sketch that awaits an independent read)"; "**[paper]** (A.5j, independently read)"; "their rigidity was not checked (claim A.5j)" | Three states of one claim. Ledger row A.5j: "confirmed by an independent read". My own check agrees with the computation (see task E). | Use one wording in all three places. |
| F-20 | minor | X.4.1 (`10` 136-137), X.7 item 2 | "for one generation the four anomaly conditions fix the charges up to u <-> d" | `Closures/Anomaly.lean`, `anomaly_fixes_sm (g) (hA : AnomalyFree g) (hQ : 0 < g.Q) (hP : Primitive g)`: the hypotheses `0 < q_Q` and coprime charges are not named in the text. Without `q_Q != 0` there is a second solution (`q_Q = q_L = q_e = 0`, `q_u = -q_d`; the other branch of `anomalyFree_iff`). | Add "with q_Q > 0 and coprime charges". |
| F-21 | minor | I.8 (`01` 239-241); II.6.3 (`02` 264-265); VIII.3 (`08` 93-94), VIII.7 item 1; IX.3 (`09` 106-108) | "the evidence build was not run for this draft"; "Both were not run for this draft."; "IM's own audit script ... has not been run for this draft"; "The log was read, not regenerated." | All were run here and pass (task A). VIII.7 item 1 ("Regenerate the axiom log ... none done") contradicts VIII.3 ("regenerated 2026-11-24"). | Replace by the result of a run at the release commit. |
| F-22 | minor | II.6.1 (`02` 252), III.4.4 (`03` 324), IV.5.6 (`04` 261); VIII.6 (`08` 318) | "`Arsenal.Rotation` (the one-box test, I.8)"; "In the one-box test (I.8)"; "In the test of Part I (I.8, the rotation API)"; "Yang-Mills is existence, GRH is non-existence, NP vs coNP is their interaction (Part I)" | The one-box test is II.4 (I.8 itself points there). The triad sentence is not in Part I, and III.3 reads it the other way ("GRH asks that something *exists*. O1 asks that something is *falsifiable*."). | Point to II.4; drop or align the triad sentence. |
| F-23 | minor | V.0 (`05` 10-12) | "a library released 2026-11-20 and certified by the Lean and Mathlib communities on 2026-11-21" | The statement of 2026-11-21 is by "Lean FRO and Mathlib Initiative" and certifies the Riemann hypothesis only ("We hereby certify that both the statement and the proof of the Riemann Hypothesis are correct"; https://leanprover-community.github.io/blog/posts/riemann-hypothesis/). The Dirichlet theorems are on the verification page (five theorems, three standard axioms; https://math.mit.edu/~drew/grh/), which on 2026-11-24 still listed one comparator run as in progress. | "certified for the Riemann hypothesis by the Lean FRO and the Mathlib Initiative on 2026-11-21; the Dirichlet theorems are checked on the verification page". |
| F-24 | minor | IV.6 (`04` 289-292), IV.6.1 | "That saturates the twist only for beta L^2 <= 0.42" | The threshold behind 0.42 is a twist ratio of 3/7 (`SATURATION.md` line 19: "beta L^2 <= 1/2 log(7/3)"), which the paper never states; its own thresholds are 0.414 (self-dual) and 0.74 (tube). With 0.414 the bound is 0.44, with 0.74 it is 0.15. | State the threshold used. |
| F-25 | minor | Abstract (`00` 52-53); Introduction (`00` 116-117) | "one step certified on one box certifies every tick"; "without a floor no procedure decides it" | `onebox_certificate` needs `∀ x, B.Correct x → B.Correct (B.step x)`: the step at every state, an induction. Undecidability is proved for the universal machine (`etm_balance_undecidable`); II.3 says "a lossless system as such need not be undecidable". | "a marker correct at the start and kept by the step at every state"; "at the floor there are systems for which no procedure decides it". |
| F-26 | minor | `Proof/LiftingNP.lean` docstring of `LiftCPConst`; ledger VI.4.11, III.7k | "**Open for every constant-size gadget**"; "neither is proved for any constant gadget" | `Gadget` is any `g : (Fin a → Bool) → (Fin b → Bool) → Bool`, and `LiftCPConst G c` quantifies over every CNF. For the XOR gadget and Tseitin formulas on expanders the lifted formula is again a Tseitin formula, which has quasi-polynomial cutting-planes refutations (Dadush-Tiwari 2020, cited in VI.4), while the resolution width is linear: `LiftCPConst XOR c` is false for every `c > 0`. Not machine-checked here. | "open for suitable gadgets (for example indexing); false for XOR". |
| F-27 | minor | `docs/mass-gap/formal/sync-build.sh` line 6 | `src=/mnt/c/claude/gravity-ym/docs/mass-gap/formal` | The build script and all 26 axiom scripts copy from one fixed checkout path, whatever tree they are run from. Reproduced here with a copy of the script whose `src` points at the clone. | Derive `src` from the script's own location. |
| F-28 | minor | VII (`07` title, 247, 282) | "Part VII. Navier-Stokes: the card, the claimed certificate, and Poincare as validation"; sections VII.5 then VII.7 | Poincare is Appendix A now; there is no VII.6. | Retitle; renumber. |
| F-29 | minor | Part I.0 legend (`01` 22-30); IV (`04` 71) | Marks used but not in the legend of Part I | `[conditional]`, `[certified]` are missing from the table in I.0 (the introduction has them); `[unchecked]`, `[sketch]`, `[external, traced]`, `[external, unverified]`, `[Lean, re-checked]` are used and defined nowhere. | One legend, complete. |
| F-30 | minor | Bibliography rows 63, 64, 87, 140, 3, 18/19 | Dobrushin 1968 and 1970 titles; Cantor "(1891)"; OpenAI "Finite time blowup for Navier-Stokes"; Super-Kamiokande "213 other authors"; Bombieri twice | Crossref: the English titles are "The Description of a Random Field by Means of Conditional Probabilities and Conditions of Its Regularity" (10.1137/1113026) and "Prescribing a System of Random Variables by Conditional Distributions" (10.1137/1115049). zbMATH 24.0066.02 gives 1892 for Cantor's volume. The OpenAI page is titled "On the Navier-Stokes Millennium Prize Problem" (https://openai.com/index/navier-stokes-solution/; the PDF's own title was not read). Crossref lists 215 authors (10.1103/PhysRevD.102.112011). Rows 18 and 19 are one work. | Correct the rows. |
| F-31 | minor | LaTeX build | Overfull boxes | `pdflatex guid-v8.tex` (second run): about 40 "Overfull \hbox", the worst 152 pt, 146 pt, 101 pt and 91 pt in the bibliography (URLs, tex 2876-2973) and 60 pt in the table at tex 1346. Text runs off the page there. | Break URLs (`\usepackage{xurl}`), narrow the table. |
| F-34 | minor | Abstract (`00` 69) | "*Navier-Stokes.* The card, with Fefferman's four forms" (under "What is proved") | `Unified/NavierStokesAPI.lean` 327-344: `ABInterface` has `ClayA : Prop` and `ClayB : Prop` as fields with no definition, and nothing for (C) and (D); VII.2 says the statements are "**named, not defined**: this library has no Navier-Stokes object". There are three cards, not one (F-07). | "*Navier-Stokes.* Three cards on the form layer (no Navier-Stokes object in Lean; Fefferman's (A) and (B) are named, not defined); in the energy-only model ...". |
| F-32 | typo | II.16 (`02` 545); XI header (`11` 3); headers of every part | "The five sections that follow, II.1 to II.6"; "This appendix records a concept"; "Draft 2 ... (V.n; IV.n in draft 3)" | II.1 to II.6 are six sections and precede II.16. Part XI is the Outlook. The italic header notes are not typeset, but body sentences with draft history are: "What changed since draft 1." (IV.0), "Care points, settled in draft 3." (IV.5.6), "new in this draft" (III.2, VI.6), "X.7a to X.7e in draft 2 (those labels are no longer valid)" (III.7), "(the Lean strings still use its draft-3 label)" (III.4.4). | Fix; remove draft history from the body. |
| F-33 | typo | V.3.3 (`05` 114-115), V.4 faces 4 and 7, II.10 (`02` 371), II.12.3 (`02` 432), III.6 (`03` 454), III.7 (`03` 541) | "recalled, no reference yet"; "theorem not yet checked"; "the reference is still to be pinned"; "its exact source is not yet pinned"; "the specific works are not yet in `../references.md`"; "to be checked against Mertz-Pitassi and Lovett-Meka-Mertz-Pitassi-Zhang" | Open reference items stated in the body (known to `REVIEW.md` for II.10.3). They are honest, and they are placeholders. | Supply the references or cut the sentences that need them. |

## A. Reproduce

All commands ran on 2026-11-24 in a fresh clone of the release candidate (`git checkout f4592e3`, clean `git status`) inside
WSL, with a build folder of its own (`FORMAL_DST`), `lake update` and `lake exe cache get` from scratch.

| What | Command | Result |
|---|---|---|
| Evidence gate | `bash evidence/tools/check.sh` (from `evidence/`) | exit 0; pin `OK vendor/dmp ... @ 4400cce... (version 0.9.9)`; `setup: OK`; 27 modules built; "OK 285 theorems, none resting on more than propext, Quot.sound, Classical.choice" (70 on no axiom, 81 on `propext`, 108 on `propext, Quot.sound`, 26 on all three). As expected. |
| Formal, the required target | `bash sync-build.sh ProofPhase.ETM.ETM` | "Build completed successfully (9106 jobs)"; the arsenal resolved at `b01adbdd7dc34f7565acb062f090681bae88612d`, the pin of `lakefile.toml`. |
| Formal, everything | `lake build AreaLaw Influence Positivity OneScale` and every one of the 362 modules under `AreaLaw`, `Influence`, `Positivity`, `OneScale`, `Attempts`, `ProofPhase` | "Build completed successfully (9302 jobs)", exit 0, no error (311 warning lines: deprecations and style linters). |
| Axiom scripts | all 26 of `docs/unified/*-axioms.sh` and `axioms*.sh` | every script exit 0; 1,673 declarations reported; none on an axiom beyond `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`; every "source grep" line reads "no sorry / admit / native_decide / axiom". Compared name by name with the 26 committed logs: **0 differences**. |
| IM arsenal, lint | `bash tools/lint.sh` at the pinned commit | "lint: OK (10 modules; Mathlib v4.34.0 only; no escape hatch; 4 part(s) answered R136a1)", the four being `Euler product bound`, `Hasse`, `the gate is shared across scales`, `weak Mordell-Weil`. As II.6.3 prints it. |
| IM arsenal, full check | `bash tools/check.sh` at the pinned commit, fresh build against Mathlib | exit 0; "OK 223 declarations, none resting on more than propext, Quot.sound, Classical.choice" (182 on all three, 35 on none, 4 on `propext`, 2 on `propext, Quot.sound`). |
| Paper | `python tools/paper-latex.py`; `pdflatex guid-v8.tex` twice | task F. |
| Ledger, scrub | `python tools/claims-check.py`; `LC_ALL=C.UTF-8 bash tools/scrub-scan.sh` | "claims-check: OK" (659 rows); "scrub-scan: clean" (with this report staged). |

**Numbers of the paper against the runs.** They match: 285 (I.8, REVIEW); the lint line (II.6.3); Navier-Stokes 52 + 4 (VII.3);
Hodge 47, two of them on two axioms (IX.3); GU 18 + 1 + 2 and 12 (X.3); BSD 46 (VIII.3); rotation 115, ETM 154 (logs). II.7's
358 modules and 103,282 declarations, 369 modules and 105,150 declarations agree with `docs/unified/INDEPENDENT-CHECK.md`
(lines 155-158, 190-195); the independent re-check itself was not repeated here. VIII.3's "85 declarations" of the native BSD
core is a count by the stage-2 review and was not recounted; the arsenal as a whole reports 223. **No number was found that
does not match.** What the paper says was "not run for this draft" has now been run (F-21).

**Notes.** (1) `sync-build.sh` copies from a fixed path (F-27); the runs above used a copy of it with `src` set to the clone,
nothing else changed. (2) The first attempt at the arsenal check failed on this verifier's own setup (a package link that
pointed at a folder that no longer exists); it was re-run against the fresh Mathlib of the build above and passed. (3) Not
re-run: `tools/independent-check.sh`, the ball-arithmetic certificate (`grh_onebox_cert.py`), `bsd_check`, and any numerical
script. (4) The 14 blockers of the stage-2 part reviews were spot-checked against the release candidate: for 13 the quoted
sentence is gone or corrected (R1 S1, R2 L1 and S1, R3 S1, R4 S1, S3 and C1, R5 C1, R6 L1, C1, C2 and N1, R7 C1); R6 X4 is a
ledger row and was not checked.

## B. Lean statements

Checked by reading the sources at `f4592e3` and at the arsenal's pinned commit, and by the build above.

* **Every name resolves.** A script took every back-quoted identifier of `docs/paper/draft/*.md` and looked for a declaration
  or structure field of that name in `docs/mass-gap/formal`, `evidence/Dmp`, the arsenal and IM's `proof/` at the pinned commit
  (407 files, 7,238 names). The only misses are words that are not declarations (`sorry`, `axiom`, module names, Mathlib names,
  variables). `settle`, `settle_everywhere`, `settle_iff_bounded`, `edge` are aliases in `API.lean` (lines 81 to 91).
* **The machine.** `balanceBound M ε q = ⌈M q / (ε (1 - q))⌉₊ + 1` (`ETM/Machine.lean` 116), as II.3.2 prints it;
  `reaches_of_contracting`, `etm_universal`, `etm_balance_undecidable`, `etm_truth_edge`, `etm_edge`, `etm_not_contracting` say
  what II.3 says. `toy_settle_101` is real (`API/Template.lean` 99).
* **The one-box test.** `Arsenal/Rotation.lean`: `Box`, `gate`, `Correct`, `DMPComplete`, `onebox_certificate`,
  `dmpComplete_iff_orbit`, `SharedGate`, `scale_certificate`, `not_shared_of_wrong`, `selfMarked_complete`,
  `exists_not_complete`: as described in II.4 and III.4.4, including the care points. See F-05, F-06, F-25 for what the
  abstract makes of them.
* **Card boxes.** `ETM/CardBox.lean`: `tickBox P` has factor `if P n then 0 else 1`, so `cardBox_complete_iff` is "complete
  iff the open step". `grh_box_iff`, `grh_box_of_RH`, `np_box_concl`, `bsd_box_iff`, `hodge_box_iff`, `hodge_box_divisor`,
  `gu_box` are real and are what V.8, VI.10, VIII.8, IX.8, X.8 say, each with "restates the step and proves no new bound".
* **Yang-Mills.** `su2_Ztw_lt_Z` (`Flip/Strict.lean` 1187): every `β ≠ 0`, `L ≥ 1`, even `T`, background `P`, position `c`.
  `sunZtw_lt` (`General/SUNTwistWilson.lean` 404, `[Fact (1 < N)]`, `k ≠ 0`): the abstract's "for every SU(N)" holds, though
  Part IV's table cites only the SU(2) theorem (the ledger row IV.1.6 cites both). `su2_handover` carries `0 < su2Ztw` as
  a hypothesis, as stated. `yang_mills_assembly_onebox_of_resolution` needs `Tendsto T.ℓ atTop atTop`, `NonTrivial T`,
  `O1Form T`, and returns `NonTrivial` unchanged, as IV.2.4 and IV.9.5 say. `kchain_tanh` is for abstract kernels with a
  pointwise floor as hypothesis; IV.6.1 says the Wilson bound is an input.
* **GRH.** `explicit_formula_of_smooth` (`GRH/ContourShiftTie.lean` 155): for every smooth compactly supported `g` and every
  enumeration of the nontrivial zeros with multiplicity (`NontrivialZeroFamily`, by `analyticOrderAt`), the sum over zeros is
  summable and equals `efRHS c g` (poles, primes, real place). This is the abstract's sentence. `onebox_positive`: abstract, as
  III.1 says (F-12).
* **NP.** `cross_any_system` (`Proof/Crossing.lean` 243) has the two hypotheses the text names. `liftCPConst_iff_extract` is
  real (F-08).
* **Hodge, GU, BSD.** `PolHS` (F-13); `anomaly_fixes_sm` (F-20); `g2_rigid_of_one_assumption` (F-05). The arsenal's BSD
  declarations were covered by the axiom report of task A; their statements were read for `mordellWeil_of_weak`,
  `existence_line`, `bsdStatement_iff` only.
* **"Lean (from X)" hypotheses.** Named in the text wherever checked, except F-20.

## C. The one assumption

* Stated once: yes, III.4.4, in prose. Exactly: no, see F-06. It is a reading attached to different formal statements.
* Marked conditional where used: III.64a, III.66, III.68a, III.68d, III.69c, IV.9.5b, A.5u carry "conditional" or "Lean from
  III.64 as a named hypothesis". No Lean theorem assumes it silently: every use is a hypothesis in the statement (`hshared`,
  `hX64`, the cards' `Open`), and the axiom reports of task A show no axiom beyond the three standard ones.
* Written as if proved: the abstract's "One step is the same on every card" (F-04) and "G2 is rigid under the one assumption"
  (F-05); A.5 "This is now a theorem one layer down" is accurate only with the sentence that follows it.
* **The scale certificate** is exactly `scale_certificate`: if every scale's box maps into the one box keeping step, gate
  factor and marker, completeness of the one box gives completeness of each. III.4.4's care point ("Sharing the gate alone is
  free; the content of III.64 is that the marker travels with it") is right and is the whole content.
* **The rigid start.** "{infinity, 2, 3}" as the start is a reading (III.69, III.70, marked). What is certified is F-12.
  "Among SU(N) the homotopy type determines the manifold exactly for N = 1, 2, 3" rests on task E.
* **G2 rigid from the one assumption**: F-05.

## D. The cards

* **Yang-Mills.** Proved core as stated (task B). Open step: F-09. The external construction is described accurately: the
  repository https://github.com/yang-mills-group/YM states a submission of 28 October 2026, an assessment dated 10 November
  2026, the Wightman sentence as the assessors' opinion, "It does not prove that the infinite-volume limit is unique or that
  there is a mass gap", and "Posting a submission does not constitute endorsement or certification" (fetched 2026-11-24). The
  assessment PDF and the Lean sources were not read here.
* **GRH.** The external result exists and is described accurately except F-10 and F-23: release 2026-11-20, 17 million
  lines, Mathlib's `RiemannHypothesis`, five theorems including every Dirichlet L-function, Dedekind, Hecke and automorphic
  L-functions excluded (pages cited in F-15). Open step: F-11.
* **P vs NP.** F-07, F-08, F-26. The crossing theorem is as stated.
* **Navier-Stokes.** Accurate against the sources fetched: OpenAI, 8 September 2026, a smooth force, statement (C) "and also
  (D)" (https://openai.com/index/navier-stokes-solution/; the page does not say "compactly supported", the paper was not
  read); Alpoge and Buckmaster, 79 pages, version of 20 November 2026, about 2,270 files and 600,000 lines, Lean v4.33.1, a
  patch of 20 November not rebuilt, the certificate "not in this repository"
  (https://github.com/tristanbuckmaster/navier-stokes/). The SHA-256 value is in their paper, which was not read here:
  unknown. Tao's post says "technically human-readable", strategy "broadly clear", and that a "professionally written proof"
  still needs work (the URL of bibliography row 141). arXiv 2610.08144, 2609.23868, 2609.26790, 2607.09619 exist with the
  authors and titles given; that 2610.08144 "expressly claims nothing about the written proof's correctness" could not be
  confirmed from its abstract: unknown. `ns_not_complete` is a statement about the energy-only model, as VII.7 says.
* **BSD.** The numbers of VIII.3.8 are consistent with each other: 0.655514388573 / 5.2441151066 = 0.12500 = 2 * 1 / 16;
  `sqrt 2 / 0.6555 = 2.157` and `sqrt 2 e^gamma / 0.3060 = 8.23` (the two targets); the trace -2 at p = 5 for y^2 = x^3 - x
  (seven affine points and one at infinity); the discriminant 64. The L-values, the period and the regulator themselves were
  not looked up and `bsd_check.log` was not re-run: unknown beyond the arithmetic. Open step stated exactly.
* **Hodge.** Open step stated exactly; F-13 for the abstract. The algebra of `weil_form` and `weil_bound` was re-derived by
  hand from the intersection numbers and agrees.
* **GU.** The table of X.3.1, the kernel of the SU(5) map and the split of Z_6 were re-derived by hand and agree. The open
  step is stated honestly ("no consequence is derived from DMP beyond what the standard expectation contains"); F-04, F-07,
  F-20.

## E. Validation

* **SU(3).** Read in the source: X. Wang, arXiv 1810.08478v1, page 2. Theorem 1.1(3): the diffeomorphism classes of smooth
  manifolds of the type are `{S^3 x S^5, S^3 x S^5 # Sigma^8, SU(3), M_{1,0}}`; Corollary 1.2: "Two topological 8-manifolds of
  type (*) are homeomorphic if and only if they are homotopy equivalent" and "A closed smooth 8-manifold M is diffeomorphic to
  M_{1,0} or SU(3) if and only if they are homotopy equivalent." This is what A.3 cites (`SU(3) # Sigma^8` included). Journal:
  Acta Math. Sinica (Engl. Ser.) 37 (2021) 941-956 (Crossref 10.1007/s10114-021-0194-z).
* **Kreck-Lueck.** Read in the source: arXiv math/0509238, pages 2 to 3. Definition 0.2 (Borel, strong Borel); "A manifold M
  is strongly Borel if and only if S^top(M) consists of one element. A manifold M is Borel if and only if ho-aut_pi(M) acts
  transitively on S^top(M)." This is the criterion A.5 and `G2Surgery` use.
* **Sp(2), step by step.** Cells in dimensions 0, 3, 7, 10; simply connected, dimension 10. Normal invariants
  `[Sp(2), G/TOP]`: `pi_3 = pi_7 = 0` and `pi_10 = Z/2` for G/TOP, so only the top cell contributes, at most `Z/2`. The
  surgery obstruction to `L_10 = Z/2` is the Kervaire invariant and is onto on the top cell, so the kernel is trivial;
  `L_11 = 0` acts trivially. The structure set is a point. Holds.
* **G2, step by step.** Mod 2 cohomology `Z/2[x_3]/(x_3^4) ⊗ Λ(x_5)`, with `Sq^1 x_5 = x_3^2`; so `H^4`, `H^8`, `H^12` with
  integer coefficients vanish, and the cohomology has only 2-torsion (no odd part of `[G2, G/TOP]`). At 2, G/TOP is a product
  of Eilenberg-MacLane spaces: `[G2, G/TOP] = H^6(G2; Z/2) ⊕ H^14(G2; Z/2) = Z/2 ⊕ Z/2`. G2 is parallelisable, so in
  Sullivan's formula the obstruction to `L_14 = Z/2` is the top coordinate; `L_15 = 0`. The structure set has exactly two
  elements, the second carried by `x_3^2`. Holds, as A.5p.
* **SU(N), N >= 4.** `H^8(SU(N); Q)` contains `x_3 x_5`; a normal invariant with that rational class has zero surgery
  obstruction (odd dimension, or the top L-class vanishes because all products of the class vanish), so it is realised by a
  homotopy equivalence from a manifold with a non-zero rational Pontryagin class; rational Pontryagin classes are topological
  invariants (Novikov) and SU(N) is parallelisable. Holds as a sketch; the step for `Spin(4k+2)` and `E_6` is not written out,
  as A.5l says.
* **Ricci flow facts.** `Ric = (N/2) g` for `<X, Y> = -tr(XY)`, extinction at `1/N`, first eigenvalue `N - 1/N`, and the
  window (`N - 1/N` strictly inside for `N >= 3`, on the Obata edge for `N = 2`): re-derived by hand, agree.

## R. References

All 177 rows of `references.md` were looked up on Crossref, arXiv, zbMATH, DataCite, publisher pages or the repository's own
page by six haiku subagents (2026-11-24); their mismatches were then checked by me against memory or the record. Result:

* **No fabricated work was found.** Every row with data points to a work that exists with those authors and that title,
  including the recent ones: arXiv 2502.03415, 2509.23403, 2504.13607, 2607.18341, 2607.09619, 2609.23868, 2609.26790,
  2610.08144, and the three repositories and two web pages of 2026.
* Two rows have no data (F-03). Three typeset links point to other works or to an encyclopedia page (F-16). Small errors:
  F-30. Works cited without a row: F-15.
* Could not be verified on a primary record (unknown, not wrong): the year "2000" of the Clay description by Bombieri (rows
  18, 19) and the Jaffe-Witten description (row 98), no year is printed on the pages; Grothendieck 1969 (row 29);
  Erdos-Lovasz 1975 (row 45), Presburger (row 48, no venue in the row; the record gives 1930), Mordell 1922 (row 58), only
  through secondary lists; Silverman's theorem number V.1.1 (row 164); which Chae-Wolf paper Alpoge and Buckmaster cite (row
  165); the journal year of Chen-Liu-Vigoda (row 171).
* Fields the lookups can supply: Ajtai, Combinatorica 14 (1994) 417-433; Pitassi-Beame-Impagliazzo, Comput. Complexity 3
  (1993) 97-140; Krajicek-Pudlak-Woods, Random Structures Algorithms 7 (1995) 15-39; Galanis-Stefankovic-Vigoda, Combin.
  Probab. Comput. 25 (2016) 500-559; Sokolov, CSR 2017, 294-307; Maruyama-Oshima, J. Math. Soc. Japan 60 (2008) 767-792;
  Ancona, Invent. Math. 223 (2021) 149-212; Reece, JHEP 2023 (10) 116; Hou, Found. Comput. Math. 23 (2023) 2251-2299;
  Babu-Mohapatra, pages 938-941; Perl, Lee, Loomba are Martin L., Eric R., Dinesh; Martinelli, Olivieri are Fabio, Enzo.

## P. The personal note

The opinions are the first author's and are not judged. Factual sentences against the record:

* "after GRH got proven and certified, I decided to take a look if Yang-Mills ...": the library was released 2026-11-20 and
  the certification statement is dated 2026-11-21 (F-23: it certifies the Riemann hypothesis; "GRH" in the library means
  Dirichlet L-functions). The first commit of `docs/mass-gap` is dated 2026-11-21
  (`git log --reverse --format=%ad --date=short -- docs/mass-gap | head -1`). Consistent.
* "everything needed is public under Apache 2.0": `LICENSE` of this repository, `vendor/dmp/LICENSE` and the `LICENSE` of the
  `im` repository at the pinned commit are Apache 2.0. Holds. One note the paper rests on calls itself a "Private working
  note" (`docs/unified/GRH-ONEBOX-CERT.md`, line 3) while being public.
* "One thing led to three ... turned into three": the paper covers seven problems (F-18; the first author's to decide).
* "In v1 I invited everyone ...", the sentences about Goettingen: not checkable from the record. Unknown.

## F. Format

* Build: `python tools/paper-latex.py` prints "wrote guid-v8.tex: 13 chapters, 177 references"; the generated file equals the
  committed one up to line endings (`git diff` shows no content change). `pdflatex guid-v8.tex` twice: exit 0, 99 pages, no
  LaTeX warning, no undefined reference or citation. Overfull boxes: F-31.
* `python tools/claims-check.py`: "claims-check: OK", 659 rows (certified 2, classical 124, conditional 7, external 42, lean
  251, numerical 22, open 46, paper 63, reading 102). Every label used in the paper resolves. The check does not test the
  converse; F-08 is a ledger row that the paper does not carry.
* Leftover editorial, instruction and placeholder text: F-01, F-02, F-03, F-32, F-33. Abstract: F-17.
* Cross-references that resolve to the wrong place: F-22. Numbering: F-28.

Release-blocking findings: 4
