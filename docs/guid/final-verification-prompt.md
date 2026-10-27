# Final fault verification of the GUID paper: the prompt

The owner, 2026-10-27 17:47Z: "TF wont be able to for a while, let's do it here when the time comes with a Fable High. More effort does
not help it. Please also, to verify, an Opus High." So the block below is given, unchanged, to two independent threads of the project:
one on Fable at high effort, one on Opus at high effort. Each fills in VERIFIER below with its own name (fable or opus). Neither reads the
other's findings until both are in; the consolidation pass then merges them with every other review.

```text
You are one of two independent final adversarial fault verifiers of a paper before its public release. VERIFIER = your model family in lower case (fable or opus). Your only job is to find every fault in it, prove each one or show it holds, and report. You do not rewrite the paper; a later pass consolidates every verifier's findings and corrects it once.

WHAT TO READ (GitHub, public or shared with you)
- The paper: StevenHrovat/gravity, pull request #25, branch claude/project-thread-x1aw4m, folder docs/guid/: guid.tex (the paper), preface.tex (the first author's own preface), README.md (what backs each claim, the release gates). Build: cd docs/guid && pdflatex guid.tex && pdflatex guid.tex.
- Its evidence: docs/qg-verdict.md and docs/qg-verdict/assembly.py on gravity main (06231b8); pull request #24 (head 60a1616: docs/qg-verdict.md section 10, assembly.py check [7], evidence/Dmp/Blind.lean); evidence/ (Lean 4, toolchain in evidence/lean-toolchain, check with evidence/tools/check.sh); the review passes #18, #19, #21, #22, #23, #24.
- The axiom system: StevenHrovat/dmp main 45d3822 (DMP 0.9.8), 01-constitution.md (the words, Axioms 1 to 3, G0, T38 to T40); a byte copy is at gravity vendor/dmp.

WHAT THE PAPER CLAIMS (attack exactly this, not a stronger or weaker version)
- DMP cannot model quantum gravity in 3+1 dimensions but can host it as content; in 2+1 it can, up to one superselection rule. "Model" and "host" are Definition 1 of the paper.
- It claims the construction EXISTS and its checks REPRODUCE, not that it is correct. A fault is anything that makes a sentence of the paper false, unbacked, misquoted, or stronger than its evidence.

TASKS (do all; number every finding)
A. Reproduce. Run docs/qg-verdict/assembly.py on main (expect 18 of 18) and on #24's head (expect 25 of 25). Run evidence/tools/check.sh if your environment can install the pinned Lean toolchain (expect 243 theorems on main, 246 on #24, nothing beyond propext, Quot.sound, Classical.choice); if it cannot, say so, and check instead that evidence/ is unchanged between 6d09660 (lean-evidence run 53, green) and the commits named, and count the theorem declarations. Report every number in the paper that does not match what you got.
B. Check each check. For [1] to [7], say whether the code computes what the paper says it computes, and whether the encoding of each DMP sentence is faithful to the quoted DMP text. Name any faithful alternative encoding that breaks a check.
C. Attack Claim 1 (shared structures are classical). Find a structure DMP defines between parts that can be in superposition without breaking Axiom 3 as written, or show none exists. Judge the paper's own remark that the claim is close to definitional.
D. Attack Claim 2 and its use (a classical mediator cannot entangle; Galley-Giacomini-Selby 2022). Include the 2025 debate (Aziz and Howl, Nature 646, 813; Marletto, Oppenheim, Vedral and Wilson, arXiv:2511.07348; Diosi, arXiv:2511.00852): is the paper's one-paragraph treatment accurate and sufficient?
E. Attack Proposition 2 (DMP hosts any finitely specified quantum theory of gravity) and the 2+1 section. Is "host" so weak it is empty? Is the 2+1 verdict right?
F. Adjudicate the dissent (paper section 7, gravity #24). Is the paper's account of where the passes part accurate, and is "the choice is a definition, not a calculation" true? Is the area-operator correspondence (Harlow 2017) stated correctly?
G. Proposition 3 (the tree is not our space) and every physics sentence: check against the cited source.
H. Lean (paper section 8): is every theorem name real, on the stated commit, and does it say what the paper says? Is any theorem weaker than its name?
R. References: check every one of the 35 entries against the publisher's or arXiv's own page (authors, title, journal, volume, page or article number, year). Mark each OK or wrong with the correct data. A fabricated or wrong citation is a blocker.
P. The preface is the first author's own words and personal conjectures; do not judge his opinions. Do check its factual sentences against the record, and say plainly whether this one is true today: "The final result was proven correct by four separate adverserial reviews (Fable, Fable, GLM-5.3, Fable)". Its truth is a release gate.
S. Section 9 (the record of review passes): is every row an accurate summary of that pull request?
F2. Format: abstract at most 1,920 characters of plain text; compiles cleanly; no leftover AI meta-comment, placeholder or instruction text anywhere in the paper; every cross-reference resolves.

OUTPUT
One file, docs/guid/review-final-VERIFIER.md, opened as a DRAFT pull request on StevenHrovat/gravity against the branch claude/project-thread-x1aw4m, titled "Final fault verification of GUID (#25): VERIFIER". Do not open, read or cite the other verifier's pull request. Never merge it, never edit guid.tex or preface.tex, never change DMP.
The file has a table with one row per finding: id (task letter plus number, e.g. C3), severity (blocker: a sentence is false, fabricated or unbacked; major: stronger than its evidence or misleading; minor: imprecise; typo), location (section and line of guid.tex), the sentence, the evidence (a run, a theorem, a counter-model, or a source with URL), and the fix you propose in one sentence. Then a section per task with what you checked and found to hold, so absence of findings is visible. End with one line: "Release-blocking findings: N".

RULES
- Every claim you make has a source: a command you ran with its output, a Lean theorem, or a cited page with its URL. "Unknown" is a valid answer; a guess is not.
- Attack the strongest reading of each sentence, then the weakest. If you think the verdict is wrong, say so and why, as a finding, and do not reframe the paper to make it right.
- No company or personal facts in anything you write; the repository is public, Apache 2.0.
```
