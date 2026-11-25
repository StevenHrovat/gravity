# Review of the assembled GUID v8: the prompt (stage 3b of `../REVIEW.md`)

Requested by the first author after the stage-3 consolidation (2026-11-24): the fully assembled paper is reviewed once more, for
attack and for the delivery of its actual content. The block below is given unchanged to independent fresh threads, each filling
in REVIEWER with its own name; none reads another's findings until all are in. Models: the first author's choice at the time
(Fable needs his approval in advance). Fill in COMMIT and PR before use.

```text
You are one of the independent reviewers of a paper that has just been assembled after a final fault verification and one consolidation pass. REVIEWER = your model family in lower case. You have not seen this paper before. Your job has two halves of equal weight: attack every claim, and judge how well the actual content is delivered. You do not rewrite the paper; a later pass fixes every reviewer's findings once.

WHAT TO READ
- The paper: StevenHrovat/gravity at COMMIT (pull request PR). Read it as a reader would: the PDF docs/paper/latex/guid-v8.pdf (or build it: python tools/paper-latex.py, then pdflatex twice in docs/paper/latex), front to back, before anything else.
- Then the sources for checking: docs/paper/draft/ (the Markdown the PDF is built from; fix locations are given there), docs/paper/CLAIMS.md (every claim with its status), docs/paper/references.md (the bibliography with the page each entry was read from), the Lean in docs/mass-gap/formal/ and IM's arsenal (StevenHrovat/im, arsenal/, at the commit pinned in docs/mass-gap/formal/lakefile.toml), and the axiom logs in docs/unified/.
- Read the earlier review records only after your own reading: docs/paper/review/final-opus.md, final-fable.md and consolidation.md. A finding they already list and the consolidation fixed is not a new finding; say if a fix is wrong or incomplete.

WHAT THE PAPER CLAIMS (attack exactly this)
- No Millennium Prize problem is solved. Each problem is one box under one test (one command at one shared gate, a marker per step, DMP-complete when every marker agrees with the gate). One certifiable step is the same on every card. One assumption, stated once in Part III as a reading and a schema, reads the open step the same way on five cards; every result that uses it is marked conditional on it.
- The machine and each box's proved core are machine-checked in Lean on the standard axioms; each card has one named open step in Lean, stated in the form that would close it.
- Readings (DMP interpretations, many of them the first author's) are marked as readings and carry no proof. Do not judge whether a reading is true; judge whether it is marked, kept apart from the mathematics, and placed where it helps or hinders the reader.

TASKS (do all; number every finding)
A. Attack. For every claim marked Lean, classical, external, certified, paper or conditional: is it true, is it what the source proves, is its mark right, is anything stated more strongly than its evidence? Spot-check the Lean declarations the abstract and the introduction's list rest on (real, on the commit, saying what the sentence says). Look for contradictions between parts, and between the paper and CLAIMS.md.
B. Readability. Can a mathematician from each field (mathematical physics, number theory, complexity, geometry, topology, logic) find what is proved for their problem, what is open, and why, in a first reading? Where does the reader get lost: undefined terms (the DMP vocabulary, "box", "gate", "marker", "tick", "card"), forward references, sections in the wrong order, notation introduced twice or never?
C. Precision. Every sentence that a referee would mark "vague", "ambiguous" or "unclear what is claimed": quote it and give the precise form. Check that the status marks are used consistently and that each mark's meaning is the one the introduction defines.
D. Efficiency of delivery. Where does the paper say the same thing twice, carry history or process the reader does not need, bury a result under readings, or spend pages on what one paragraph would carry? Name the passages and estimate what could go. Where is something essential too short?
E. The abstract and the introduction: does the abstract say, in plain text, exactly what the paper does and does not do? Does the introduction's "Results and open steps" match the parts?
F. Format: clean build, no leftover meta-comment or instruction text, every cross-reference and claim label resolves, the bibliography is a standard one.
The personal note is the first author's own words and is out of scope, except for plain factual errors.

OUTPUT
One file, docs/paper/review/assembled-REVIEWER.md, in a DRAFT pull request against the paper's branch, titled "Assembled review of GUID v8: REVIEWER". Do not open, read or cite another reviewer's pull request. Never merge it, never edit the paper, never change DMP. First a findings table (id, kind: attack / readability / precision / efficiency / format, severity: blocker / major / minor / typo, location in docs/paper/draft/, the sentence, evidence or reason, fix in one sentence); then a section per task with what was checked and found to hold; then the five changes that would most improve the paper for a reader, in order. End with one line: "Release-blocking findings: N".

RULES
- Every attack finding has a source: a command with its output, a Lean theorem, or a page with its URL. "Unknown" is a valid answer; a guess is not.
- Delivery findings quote the passage and say what a reader loses, not what you would prefer.
- No company or personal facts in anything you write.
```
