# The paper: submission spec

The owner, 2026-10-27 08:09Z, after agreeing on the sentence "an information-theoretic axiom system for trust, tested level by level
against quantum gravity": "Please prepare an appropriately specced article in both English in German for the categories it is going to be
submitted in." This folder holds the two drafts and this spec. Nothing here is submitted; the owner decides every item marked **decision**.

## Files

| File | What |
|---|---|
| `article.en.md` | the article, English, the version that is submitted (about 5,100 words) |
| `article.de.md` | the same article in German, for German readers and venues (about 4,600 words) |
| `README.md` | this spec |

The drafts are Markdown so that they can be read and steered in the repository; the submitted form is LaTeX built from them (section
"Build" below). Everything stated as proven in the text is a theorem on `main` of this repository at the commit the paper names, and every
theorem is cited by its Lean name so a reader can find it.

## Venue and categories

**Venue: arXiv**, as the owner's stated aspiration (a preprint when DMP, Gravity, IM and CM are finished). arXiv needs no peer review and
gives a citable, timestamped record before any journal or conference.

**Primary category: `cs.LO` (Logic in Computer Science).** The paper's contribution is a formally verified axiom system and its
metatheory (a closed inductive type, induction over it, two kernels). That is cs.LO's scope ("finite model theory, logics of programs, ...
mechanised theorem proving").

**Cross-lists (decision: keep both or one):**

- `cs.CR` (Cryptography and Security): trust, witnesses, containment, a gate with no other way through.
- `cs.DC` (Distributed, Parallel, and Cluster Computing): two independent witnesses, fail-prone systems, self-stabilisation, the layout as
  a spanning tree.

**Not** `gr-qc`, `quant-ph` or `physics.gen-ph`: section 8 is a test against quantum gravity and its result is negative at the quantum
level; it contributes nothing to physics and says so. Listing a physics category would be read as a claim the paper refuses to make, and
arXiv moderators reclassify such submissions. The physics stays in the title as "tested against", which is what the paper does.

**Classification codes** (go in the abstract page and the LaTeX front matter):

- ACM CCS 2012: Theory of computation → Logic → Logic and verification; Security and privacy → Formal methods and theory of security;
  Computer systems organization → Dependability and fault-tolerance → Dependable and fault-tolerant systems and networks.
- MSC 2020: 68Q60 (specification and verification), 68V15 (theorem proving), 68M14 (distributed systems), 03B70 (logic in computer science).

## arXiv requirements the drafts meet

| Requirement | How the draft meets it |
|---|---|
| Title, plain text | "The Duality of Trust: a formally verified, information-theoretic axiom system for trust, tested against quantum gravity" (**decision:** keep, or shorten to the part before the colon plus "tested against quantum gravity") |
| Abstract at most 1,920 characters, no LaTeX markup, no line breaks | the abstract in `article.en.md` is about 1,900 characters; recount after any edit (`wc -m` on the paragraph) |
| Submission in English; other languages allowed with an English abstract | `article.en.md` is the submission; `article.de.md` is for German readers and a German venue, or an ancillary file if the owner wants both on arXiv |
| Source files (LaTeX) preferred over PDF | build from the Markdown with pandoc to a `article` class, two columns optional, bibliography from the reference list; `.tex` and `.bib` are uploaded |
| Licence (**decision**) | arXiv offers several; CC BY 4.0 is the one that lets anyone reuse the text with attribution, matching the owner's Apache 2.0 intent for the code (Apache 2.0 itself is not offered for the text; the code the paper describes stays Apache 2.0 in the repositories) |
| Author block (**decision**) | the owner's name; contact address a forwarding alias, never the private mailbox (the self-audit of 2026-10-26 names the mail addresses as the main publish-time exposure); affiliation "independent" unless the owner wants another; an ORCID is optional and recommended |
| Authorship policy | arXiv and most venues do not accept an AI system as an author; the drafts put the agents in the acknowledgements and the owner as the author who takes responsibility for every claim |
| Endorsement | a first submission to a cs category may need an endorser; arXiv tells the submitter at upload |
| Length | no limit on arXiv; the drafts are about 12 pages single-column, within the 10 to 15 pages a cs.LO reader expects |

## What the text claims, and what backs it

- **Proven** means: a theorem in `evidence/Dmp/*.lean` on `main`, checked by `evidence/tools/check.sh` and re-checked by nanoda in CI. The
  count stated (232) is `main` at the paper's commit; recount on the day of submission.
- **Candidate** means: a finding in `docs/findings.md` or a sharpened definition from the physics pass, not DMP text, awaiting the owner's
  "approved".
- **Section 8** summarises the companion document of the physics pass (`docs/physics.md`, gravity#19, draft at the time of writing). It
  must be merged, or the paper must cite the pull request's commit, before submission (**decision:** merge order of gravity#17 and #19).
- **DMP text** is quoted from the vendored copy at `vendor/dmp` (version 0.9.8 at the time of writing). A re-pin before submission needs a
  re-read of section 2.

## Before submission (in order)

1. The owner's decisions above: title, cross-lists, licence, author block and contact alias, merge order of the physics drafts.
2. The repositories are public, scrubbed (`tools/scrub-scan.sh` clean), with the commit author identity rewritten as the self-audit says
   and the owner's words on it; the paper names the exact commits.
3. Recount the theorems and re-read section 2 against the pinned DMP of that day.
4. Build the LaTeX, check the abstract length, run the reference list against the sources (every entry was written from memory of the
   publication data and must be checked against the publisher's page before submission).
5. Upload the English version; attach the German version as an ancillary file if the owner wants it on arXiv.

## Build

```sh
pandoc docs/paper/article.en.md -o article.tex --standalone -V documentclass=article -V geometry:margin=2.5cm
```

The reference list is a numbered list in the Markdown; for a `.bib` file, convert the fifteen entries by hand (they are short) or keep the
list as a `thebibliography` environment, which arXiv accepts.
