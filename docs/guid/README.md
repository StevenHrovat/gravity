# GUID: the paper

"GUID: The General Unified Information Duality. An information-theoretic axiom system for trust, tested against quantum gravity."
Authors: Steven Hrovat, Sirius (Claude Opus 5.5). Licence: Apache License 2.0 (the owner, 2026-10-27 17:37Z).

The owner, 2026-10-27 17:22Z: "spawn Opus 5.5 thread to write the paper in accordance to cs.IT specifications. And then give me a prompt
for final fault verification run on TF. When the paper is written and all the verifications are in, they all get consolidated, fixed at
once, integrated into the paper, and then I think we can be satisfied." 17:37Z: the release goes to Twitter/X first, not arXiv; Apache 2.0.

This folder supersedes the earlier drafts of gravity#20 (`docs/paper/`, "The Duality of Trust", cs.LO): the title, the verdict
(gravity#23) and the release route changed since. Nothing here is released; nothing here changes DMP.

## Files

| File | What |
|---|---|
| `guid.tex` | the paper (LaTeX, `article` class, inline bibliography, about 12 pages) |
| `preface.tex` | the owner's preface, verbatim as posted 17:23Z, LaTeX-escaped only; one change, his (the subtitle, 17:40Z) |
| `README.md` | this spec: format, what backs each claim, the release gates |
| `fault-verification-prompt.md` | the prompt for Team Fable's final fault verification (the owner pastes it; its findings come back as a draft PR) |

## Build

```sh
cd docs/guid && pdflatex guid.tex && pdflatex guid.tex     # twice for cross-references; no BibTeX
```

Packages: `lmodern`, `geometry`, `amsmath`, `amssymb`, `amsthm`, `booktabs`, `tabularx`, `enumitem`, `hyperref`, `url`; all in TeX
Live's `latex-extra`, so arXiv's TeX Live compiles it unchanged. Built clean (no overfull box, no undefined reference) on 2026-10-27.

## Format (arXiv cs.IT conventions, kept so the paper can go to arXiv later without rework)

| Requirement | State |
|---|---|
| Category | primary cs.IT (the owner, 17:23Z, "*cs.it"); related cs.LO, cs.CR named on the title page |
| Abstract at most 1,920 characters, plain text | 1,753 characters (count the `abstract` environment with whitespace collapsed) |
| LaTeX source, compiles with pdflatex | yes |
| Authorship | **for arXiv only:** arXiv does not accept an AI system as an author; on an arXiv upload Sirius moves into "Contributions and use of AI". On Twitter/X the author block stays as the owner set it. |
| Disclosure of AI use | section "Contributions and use of AI" |
| Endorsement | a first cs submission may need an endorser (arXiv only) |
| Licence | Apache 2.0, stated in the paper (arXiv does not offer Apache 2.0 for the text; on an arXiv upload pick the closest, CC BY 4.0, and keep Apache 2.0 in the repositories) |
| Contact | **open:** a forwarding address, never the private mailbox (self-audit of 2026-10-26) |

## What backs each claim

| Claim in the paper | Backing | Reproduce |
|---|---|---|
| Sections 4 and 5, checks [1] to [6] | `docs/qg-verdict/assembly.py` on `main` `06231b8` | `python3 docs/qg-verdict/assembly.py` (18 of 18, re-run 2026-10-27) |
| Section 6 and 7, check [7] and `blind_record_same` | gravity#24 head `60a1616` (draft) | its `assembly.py` (25 of 25, re-run 2026-10-27); `evidence/Dmp/Blind.lean` |
| Section 8, 243 theorems, two kernels | `evidence/` on `main` `06231b8`; Lean unchanged since `6d09660`, whose `lean-evidence` run 53 was green on both kernels | `evidence/tools/check.sh` |
| Section 2, DMP quotes | DMP `45d3822` (0.9.8), vendored at `vendor/dmp` | `tools/check-pin.sh` |
| Section 9, the record | gravity#18, #19, #21, #22, #23, #24; the GLM-5.3 and final Team Fable rows are filled when their records arrive | the pull requests |
| References | 35 entries; each to be checked against the publisher's or arXiv's page before release | final fault verification, task R |

## Preface: the owner's answers (2026-10-27 17:40Z)

1. Title "General Unified" (not "Grand Unified"): accepted.
2. Subtitle end "can host a theory of QG whose run reproduces its predicted effects" (was "proves the observed effects of QG"): accepted.
3. "The final result was proven correct by four separate adverserial reviews (Fable, Fable, GLM-5.3, Fable)": stays; "it being true is a
   gate for the papers release" (release gate G2 below).
4. "DMP pinned to at least v1.0.0": stays, aspirational ("We will see where it ends up"). DMP `main` is 0.9.8.

Typos in the preface stay as written until the owner says otherwise ("subet", "adverserial", "graps", "natievety", "then" for "than",
"EMT" for "ETM", "WHKs" for "WKHs").

## Release gates (Twitter/X first)

- **G1.** Every reviewer is back: the GLM-5.3 verification (Z code, `out\qg-verify\VERDICT.md`, to be collected as a draft gravity PR) and
  the final Team Fable fault verification.
- **G2.** The preface's sentence on four adversarial reviews is true when the paper goes out (the owner, 17:40Z).
- **G3.** Every finding that can be closed is closed; the paper is corrected once, against all of them.
- **G4.** The repositories hold at least everything needed to verify the paper (the owner, 17:40Z): the drafts this paper cites (#24's
  check [7] and `Blind.lean`, the review records) are merged or pinned by commit, and the repositories are public.
- **G5.** The project's release gate (the owner, 2026-10-27 17:30Z): the owner and Sirius agree on the form; every repository is in a state
  we are proud to show; the commit author identity and a contributor's publish consent are settled.
