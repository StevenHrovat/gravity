# Final fault verification of GUID v8: opus

Stage 3 of `../REVIEW.md`, one of two independent verifiers, run with `final-verification-prompt.md` unchanged.
VERIFIER = opus. RC = `f4592e3` (branch `ccr-be614210-u4r7na`, pull request StevenHrovat/gravity#37). Date 2026-11-24.
The other verifier's work was not opened, read or cited. Nothing in the paper, the Lean or DMP was changed.

**How it was checked.** The worktree was checked out at `f4592e3` (the branch had not moved). The LaTeX was regenerated with
`python tools/paper-latex.py` (output identical to the committed `guid-v8.tex` except line endings) and built with `pdflatex` twice.
The Lean ran in the WSL replay distro from a fresh Linux-side clone of the repository at `f4592e3` (see A.1 for why a clone):
the evidence gate, a build of `ProofPhase.ETM.ETM`, every `docs/unified/*axioms*.sh`, and IM's `arsenal/tools/check.sh` at the pinned
commit. Bibliography rows were looked up by six haiku agents (29 rows each) against arXiv, Crossref, dblp and publisher pages;
every row they flagged, and every row used for a finding below, was re-read by this verifier (`curl` on the arXiv page or the
Crossref record). The ball-arithmetic certificate of the GRH first box was re-run at `a = 3/5`. Severity follows the prompt:
blocker (must change before release), major, minor, typo.

## Findings

| id | severity | location | sentence | evidence | fix |
|---|---|---|---|---|---|
| F1 | blocker | typeset paper: front matter (tex l. 43); III.4.4 (tex l. 993); IX.2 and IX.7 (tex l. 2334, 2476); X.6 (tex l. 2657) | "Editorial notes for the owner (to remove before publication): ..."; "That wording is the coordinator's to place; this part does not edit them."; "...; that is left to the coordinator."; "3. A Hodge row ... left to the coordinator."; "The owner's entry, in the coordinator's reading" | `grep -n "Editorial notes\|coordinator" docs/paper/latex/guid-v8.tex` after `python tools/paper-latex.py`: all five lines are in the typeset text (the README says editors' notes under chapter headings are dropped; these are not under headings) | Delete the editorial note and the two "left to the coordinator" sentences; replace the III.4.4 paragraph "Why it is stated plainly" by the wording it asks for, or drop it; drop "in the coordinator's reading" in X. |
| F2 | blocker | bibliography (tex l. 2838, 2905); IV.5.5; IV.6 | "Bogomolny 1976 *(not yet identified)*"; "Ito *(not yet identified)*"; IV.6: "(Ito; source not yet identified, recalled)" | `grep -n "not yet identified" docs/paper/latex/guid-v8.tex` (3 hits); `references.md` rows 114, 115 have no author list, title or venue | Give the full reference for each (authors, title, venue, year), read on the record, or remove the citation and the sentence that rests on it. |
| F3 | blocker | bibliography (tex l. 2983, 2984), rows 82, 83 of `references.md` | Weil 1948, *Sur les courbes algebriques...* and *Varietes abeliennes et courbes algebriques*, each with the link `https://arxiv.org/abs/1109.5230` | `curl -s https://arxiv.org/abs/1109.5230`: citation_title "La guerre des recensions (autour d'une note d'Andre Weil en 1940)", author Michele Audin: a different work. The link of both entries points to the wrong document | Replace the link by a record of each book (or drop the link); keep the bibliographic data, which is right. |
| F4 | major | abstract ("Argued in prose", last sentence); intro "What is new" ("rigidity as a one-box test [Lean]"); claim 0.24, A.5u | "Rigidity is a one-box test too, and G2 is rigid under the one assumption (in Lean, from that assumption and a named surgery input)." | The instance of the one assumption that `g2_rigid_of_one_assumption` (`ETM/G2Rigidity.lean`) takes is *equivalent* to its conclusion. Proved here in Lean (A.3, `G2Check.lean`): `(∃ B x₀, B.DMPComplete x₀ ∧ SharedGate B x₀ (G2 box) 0) ↔ G2Rigid`, from IM's `sharedGate_self` and `box_complete_iff` (take B := the G2 box itself). A.5 already concedes "at least as strong ... a reformulation of the question, not evidence for its answer"; the abstract and claim 0.24 do not | Abstract: "G2's rigidity is restated as a one-box test; in Lean the sharing for G2 is equivalent to its rigidity, so the one assumption does not decide it (A.5r open)". Claim 0.24: same. |
| F5 | major | abstract ("The one assumption"); intro ("What is new", "the open step is the same on every card"); III.8 item 2 | "One step is the same on every card: that the one box is a running, DMP-complete system, its gate shared at every scale." | In Lean the assumption is not one proposition but a schema, instantiated per object with different content: `SharedGate B x₀ C x` for a given family (`ETM/Rotation.lean`, string "X.64 ..."), the G2 sharing (`ETM/G2Rigidity.lean`, string "III.64 ..."), `HandoverSide`/`FineOneBox` for Yang-Mills, `ScaleSign` for GRH, `LiftCPConst` for NP. The paper's own Lean shows two of them are independent: `transport_not_decay`, `decay_not_transport` (`Unified/GRHToO1.lean`), and III.2 says "no single statement proves them all". III.4.4 marks the identification **[reading]**; the abstract states it unmarked as fact | Abstract: "One step has the same form on every card (a reading, Part III): ... In each card's own terms it is a different open statement (O1; Weil positivity beyond the first box; constant-gadget lifting; ...), and these are not reducible to one another." |
| F6 | major | abstract ("Each card names exactly one open step" in the claims under test; "One open step per card"); IV.0 | "What is not proved. ... One open step per card: Yang-Mills: O1, ..., with the lower edge ... in the same assumption; for the Clay statement also the continuum construction and every compact simple group." | IV.0 lists four open items O1 to O4; the lower edge (O2) is independent of O1 in the paper's own spectral model (`gap_not_lower`, `gap_and_lower_compatible`, `Closures/NonTrivialSplit.lean`), and is folded into "one assumption" only by the reading III.64a | Say "one open step for the box (O1); the lower edge (O2) is a second, independent statement, put in the one assumption by a reading; O3 and O4 remain for the Clay statement". |
| F7 | major | personal note, first paragraph | "after GRH got proven and certified, I decided to take a look if Yang-Mills ..." | The paper itself (abstract; V.0) says GRH beyond Dirichlet L-functions is open. The certification post (https://leanprover-community.github.io/blog/posts/riemann-hypothesis/, 2026-11-21, "Joint statement by the Lean FRO and the Mathlib Initiative") certifies the Riemann hypothesis; GRH for Dirichlet L-functions is stated in the library's README (https://github.com/leanprover-community/riemann-hypothesis) | For the author to decide: "after RH (and GRH for Dirichlet L-functions) got proven and certified". Also "One thing led to three" against seven problems (already flagged in the editorial note, F1). |
| F8 | major | abstract "What is proved", Yang-Mills; intro "What is new"; IV.5.6 care point; claims 0.22, IV.10c, IV.10d | "O1 is exactly DMP-completeness of the Yang-Mills box, in both directions" | `o1_iff_complete` (`ETM/RotationInstances.lean`): the box is a chain whose marker is constantly `inside` and whose gate factor is `min 1 (exp (-Fe))`, so DMP-completeness *is* "every factor ≤ θ", i.e. O1 with θ = e^-κ; `fineOneBox_iff_complete` likewise rewrites `FineOneBox` through `ym_complete_iff`. True, and a restatement by construction. V.8 says this for GRH ("it restates the step and proves no new bound"); the abstract lists the Yang-Mills one among the proved results without it | Add "(a restatement by construction; no new bound)" in the abstract and at IV.5.6. |
| F9 | major | whole typeset paper (61 occurrences in `guid-v8.tex`) | "The owner's reading ...", "The owner agrees", "The owner's correction", "the owner's definition" | `grep -c owner docs/paper/latex/guid-v8.tex` = 61 | Replace "the owner" by "the first author" (or the authors) throughout the typeset text; keep the workflow word in the notes. |
| F10 | minor | abstract; intro ("re-checked by independent kernels"); II (independent check) | "... machine-checked in Lean 4 with Mathlib, standard axioms only, and re-checked by independent kernels" | Last recorded independent re-check: `1d71a05` (`REVIEW.md`, `docs/unified/INDEPENDENT-CHECK.md`, "Run of 2026-11-24 (quick, draft 4, at 1d71a05)"). `ETM/CardBox.lean` (the boxes V.8, VI.10, VIII.8, IX.8, X.8) came after it: `git log -1 --format=%ci 958d756` = 2026-11-24 15:36 against 15:17 for `1d71a05`. The Lean kernel's axiom report for it passes (A.2); the second kernels have not seen it | Run `bash tools/independent-check.sh quick` at the RC and record it, or say which modules the re-check covers. |
| F11 | minor | abstract ("The one assumption" paragraph) | "With a floor, settling is decidable within an explicit bound; without a floor no procedure decides it." | `etm_balance_undecidable` (`ETM/Machine.lean`) is about one system, the lossless universal ETM, over all content; many floorless systems are decidable (a constant run). III.4.3 has the qualifier ("for all content") | "... without a floor, for the universal machine, no procedure decides it for all content." |
| F12 | minor | V.0, first bullet; abstract | "... a library released 2026-11-20 and certified by the Lean and Mathlib communities on 2026-11-21" | The post (URL in F7) is "Joint statement by the Lean FRO and the Mathlib Initiative" and certifies the Riemann hypothesis (statement `RiemannHypothesis`, four checks); its body does not mention Dirichlet L-functions. The README of the library states RH and GRH for Dirichlet L-functions, checked by comparator, on `propext`, `Quot.sound`, `Classical.choice` | "certified by the Lean FRO and the Mathlib Initiative (for RH); GRH for Dirichlet L-functions is in the same library, checked by its comparator". |
| F13 | minor | bibliography (typeset) | entries end in "(checked)", "(partly checked)" (64), and 28 links are Crossref search queries (`api.crossref.org/works?query...`) | `grep -c "partly checked" ...guid-v8.tex` = 64; `grep -c "api.crossref.org/works?query" ...guid-v8.tex` = 28 | Typeset standard entries (DOI or arXiv id); keep the verification status and the page read in `references.md`. |
| F14 | minor | bibliography row 149 | "A counterexample to the Hodge conjecture extended to Kaehler varieties" | arXiv record (`curl` arXiv math/0112247): "A counterexample to the Hodge conjecture for Kaehler varieties"; the Crossref record of the IMRN article (DOI 10.1155/S1073792802111135) has an empty title field, so the journal title was not read | Read the journal's page; use its title, or the arXiv title with the arXiv id. |
| F15 | minor | intro "How to read the status marks" ("Every statement carries one mark") | nine marks are defined | The typeset text also uses [sketch], [unchecked], [external, traced], [external, unverified], [external, unverified, certificate unreleased], [classical, recalled], [paper, an estimate], [open in general], [external, recalled] and others (count by `grep -oE "\\textbf\{\[[a-z][^]]*\]\}"`) | Define the extra marks (or map each to one of the nine plus a qualifier) in the intro. |
| F16 | minor | abstract, length and form | the abstract | 1,025 words with bold headings and bullet lists (`python` word count of the `## Abstract` section); not a plain-text abstract, and over the usual archive limit (1,920 characters on arXiv) | A plain-text abstract of one paragraph; move the lists to the introduction. |
| F17 | minor | abstract, Hodge bullet | "Hodge. Hodge-Riemann positivity, the Hodge index as linear algebra, Weil's bound for curves, ..." | IX.3.4: Weil's bound is "[Lean from the external index theorem]", with the intersection numbers an `External` slot (`CurveInput.geometry`); the BSD bullet says "with the classical theorems Mathlib lacks carried as named parts", the Hodge bullet does not | Add "from named classical inputs" to the Hodge bullet. |
| F18 | minor | abstract, NP bullet | "The crossing theorem for every sound two-premise proof system" | `cross_any_system` (`Proof/Crossing.lean`) needs the formula expanding (`hexp`) and every proper sub-system satisfiable (`hsat`) | "... for every sound two-premise proof system, on expanding, minimally unsatisfiable formulas". |
| F19 | minor | abstract, BSD open step | "BSD: the rank equals the order of the zero at s = 1, from order 2 on." | The proved core is stated over any number field; "proved for order 0 and 1" (VIII.5) holds over Q (Gross-Zagier, Kolyvagin, with modularity) | "over Q, from order 2 on (over other number fields, in general)". |
| F20 | minor | abstract, Yang-Mills | "the assembly from a one-box gap certificate to a lattice mass gap in both orders of limits" | IV.0 item 1: "The Lean gap is a decay statement for slab correlations ...; the step to a gap of the Hamiltonian ... is IV.2.7 ([paper])" | "... to exponential decay of slab correlations (a lattice mass gap) in both orders of limits; the Hamiltonian gap step is in prose". |
| F21 | minor | III.4.1 table, row "The open statement", Yang-Mills cell | "F_e(L) - 2c(L) > log mu_4 = 1.91, the excess act included, uniformly over every well-defined outside (IV.5.6)" | IV.0 and IV.5.6: the number is "a sufficient route ..., not a necessary one", stated for the torus free energy, and "uniformly over every well-defined outside" is the content of the Lean form `FineOneBox`, "for the number ... a heuristic" | State the open statement as `FineOneBox` and the number as its sufficient route, as IV.5.6 does. |
| F22 | minor | intro "What is new"; V.3, III.4.4 | "the first box of Weil's positivity with an explicit margin [certified]" listed as new | No prior work on Weil positivity at small support is cited (`grep -i "yoshida\|connes\|consani" docs/paper/references.md docs/paper/draft/*.md` finds only an unrelated mention). Connes-Consani, "Weil positivity and Trace formula, the archimedean place" (arXiv 2006.13771) treats Weil positivity at the archimedean place; which supports it covers was not read here | Check the small-support literature (Connes-Consani; Yoshida) and cite it, saying what the certificate adds (the primes 2 and 3, explicit margins). |
| F23 | minor | `docs/mass-gap/formal/sync-build.sh` (the build the paper cites) | `src=/mnt/c/claude/gravity-ym/docs/mass-gap/formal` | The script copies from one fixed checkout, not from the tree it is run in, so the axiom scripts (which call it) can build another commit than the one checked out; and in a Windows checkout with CRLF the scripts fail (`set: pipefail: invalid option name`). Here the fixed checkout was at `f4592e3` too, and the run used a clone with that line pointed at itself (A.1) | Derive `src` from the script's own folder; add a `.gitattributes` rule `*.sh text eol=lf`. |
| F27 | minor | A.3, fourth bullet; abstract ("Validation") | "A genuine 'Poincare for SU(N)' ... is a surgery-theory question, and it is settled." | Settled in the literature only for N = 2 (Poincare) and N = 3 (Wang, arXiv 1810.08478); for N >= 4 it rests on this paper's own computation, marked **[paper]** in the same bullet. The sketch (a normal invariant on x_3 x_5 in degree 8 changes p_2) is complete when N^2 - 1 is odd (N even, L_odd(1) = 0); for N odd the dimension N^2 - 1 is divisible by 8, L(1) = Z, and the sketch does not show that the surgery obstruction of the chosen normal invariant vanishes (or is killed by another class) | "... and it is answered: published for N = 3, and for N >= 4 by a surgery computation in this paper ([paper]; for odd N the obstruction in L = Z still has to be shown to vanish)". |
| F28 | minor | abstract, "The machine" bullet; intro "What is new" ("R136a1 as the named answer 'outside'") | "R136a1, the one way to leave a statement open, as a named hypothesis that never becomes an axiom" | True of IM's arsenal (`Arsenal/R136a1.lean`, `def R136a1 (_name : String) (P : Prop) : Prop := P`), as III.5 says. In this repository's Lean the open steps are `API.OpenStep` and `API.External` (`ProofPhase/API.lean` l. 59, 64: `abbrev OpenStep (_name : String) (P : Prop) : Prop := P`, likewise `External`), separate wrappers, not defined through `R136a1`; e.g. `scale_certificate` and `g2_rigid_of_one_assumption` take `OpenStep` | "in IM's arsenal, R136a1 is the one way ...; this repository's cards use the same transparent form under the names `OpenStep` and `External`". |
| F24 | typo | draft-history remarks in the typeset text, III.4.4 and III.7; Lean strings | "(the Lean strings still use its draft-3 label; claim III.68a)"; "The five statements were X.7a to X.7e in draft 2 (those labels are no longer valid)." | `grep -n "draft-3 label\|those labels are no longer valid" guid-v8.tex`; `ETM/Rotation.lean` OpenStep string "X.64: ..." against III.64 in the paper | Drop the draft history from the typeset text; rename the Lean strings at the next Lean change. |
| F25 | typo | abstract; claim 0.25 | "each step multiplies by one number of modulus at most one, whose modulus is the cost and whose phase the rotation" | The paper's cost is -log of the factor (II, `elec_cost`: "The cost -log of the electric factor is the distance d") | "whose modulus gives the cost (its negative logarithm)". |
| F26 | typo | layout | 42 overfull and 44 underfull boxes; largest 152 pt (bibliography URL, tex l. 2955) | `grep -c Overfull guid-v8.log`; `grep -c Underfull guid-v8.log` | Allow breaks in long URLs and `\texttt` names (`\usepackage{xurl}` or `\sloppy` in the bibliography). |

## A. Reproduce

A.1. **Setup.** `git -C ... worktree add ... origin/ccr-be614210-u4r7na`: HEAD `f4592e3413046bc2956de177d4eead28e44adf4f` (the RC; the
branch had not moved). A first run from the Windows worktree failed at once: the worktree's scripts have CRLF line endings
(`tools/check.sh: line 9: set: pipefail: invalid option name`), and `sync-build.sh` reads a fixed checkout (F23). The reported run
therefore used `git clone https://github.com/StevenHrovat/gravity` in WSL, `git checkout f4592e3`, with the one `src=` line of
`sync-build.sh` pointed at the clone; build folder `~/formal-final-opus` (seeded with a copy of a built package folder, so Mathlib
was not rebuilt), never `~/formal`.

A.2. **Results.**

| Check | Command | Result |
|---|---|---|
| Evidence gate | `bash evidence/tools/check.sh` (from `evidence/`) | `OK 285 theorems, none resting on more than propext, Quot.sound, Classical.choice` (as the prompt expects) |
| Formal build | `bash docs/mass-gap/formal/sync-build.sh ProofPhase.ETM.ETM`, `FORMAL_DST=~/formal-final-opus` | `Build completed successfully (9106 jobs)`; IM's arsenal fetched at `b01adbdd7dc34f7565acb062f090681bae88612d`, the commit `lakefile.toml` pins |
| Axiom scripts | every `docs/unified/*axioms*.sh` (26 scripts), same build folder | all exit 0; 1,673 declarations in all; every one on `propext`, `Quot.sound`, `Classical.choice` or a subset (some on none); every source grep "no sorry / admit / native_decide / axiom"; **each of the 26 logs is identical to the committed log** apart from build-progress lines (`diff` after dropping `Build completed`/warning lines: 0 differing lines in every file) |
| IM arsenal | `arsenal/tools/check.sh` in a copy of the arsenal at `b01adbd` (Mathlib `5ed2965`, v4.34.0) | `lint: OK (10 modules; Mathlib v4.34.0 only; no escape hatch; 4 part(s) answered R136a1)` (Euler product bound, Hasse, the gate is shared across scales, weak Mordell-Weil); `OK 223 declarations, none resting on more than propext, Quot.sound, Classical.choice` |
| Ledger | `python tools/claims-check.py` | `claims-check: OK`, 659 claims |
| LaTeX | `python tools/paper-latex.py`; `pdflatex guid-v8.tex` twice | 13 chapters, 177 references; 99 pages, exit 0 |

No number in the paper was found that the runs contradict. The paper does not state the arsenal's declaration count; the
independent re-check numbers it quotes (II: 105,150 declarations for `nanoda_lib`) are from the recorded run at `1d71a05` and were
not re-run here (F10).

A.4. **The GRH first-box certificate.** `python docs/unified/grh_onebox_cert.py 3/5` (python-flint 0.9.0) reproduces the committed log
line for line: `RESULT a = 3/5: [1.500e-9 +/- 2.01e-13] * ||f||^2 <= W(f) for every f in L^2(-3/5, 3/5)`, with upper bound
`[1.6077e-9 +/- 1.83e-14]`. The margins quoted in the paper (1.5e-9, 3.4e-11, 6.4e-13 at a = 0.60, 0.65, 0.69; about 3.6e-15 at 0.75 as
an upper bound only) agree with `docs/unified/GRH-ONEBOX-CERT.md` and its logs. The cut a = 0.69 < (1/2) log 4 = 0.6931 is right: only
n = 2, 3 enter.

A.5. **Numbers checked and found to hold.** log(1 + sqrt 2) = 0.881; log 8 = 2.08; log(8/7) = 0.134; -log(1 - 0.197) = 0.22;
mu_4 = 6.77, log mu_4 = 1.91, (mu - 1)/(mu + 1) = 0.74; log 4 = 1.39, log 7 = 1.95; 3^12/2^19 = 1.01364; one-loop slope 11/(6 pi^2) for
beta = 2/g^2 and pi^2 beta = (11/3) log(1/(a Lambda)) for SU(2) with beta = 4/g^2; Bogomolny floor 4 pi^2/g^2 = pi^2 beta for half-integer
charge; Ric = (N/2) g for -tr(XY), extinction at t = 1/N, first eigenvalue N - 1/N, Obata edge 3/2 for N = 2; the Weil-bound algebra of
IX.3.4 (a = N - q - 1, b = 2 g q gives (N - q - 1)^2 <= 4 g^2 q); the page count (99) and the reference count (177). Evidence gate count:
285, as stated.

## B. Lean statements

Every backticked Lean name in `docs/paper/draft/*.md` (751 names) was looked up in the sources: the repository's Lean, IM's
`arsenal/` and `proof/` at the pinned commit `b01adbd` (read with `gh api repos/StevenHrovat/im/contents/...?ref=b01adbd...`), and
`evidence/`. Every name resolves, apart from Mathlib names (checked by `#check`, A.3) and words in backticks that are not declarations
(`sorry`, `axiom`, file names). Read in full against their sentences:

* `scale_certificate`, `onebox_everywhere`, `not_shared_of_wrong` (`ETM/Rotation.lean`) and IM's versions: as stated. The
  "one step certified" of the abstract is the hypothesis `∀ x, Correct x → Correct (step x)` for every state of the box, a for-all,
  and the scale step is a pull-back along a morphism of running systems that the hypothesis `SharedGate` supplies. The paper's
  wording ("Sharing the gate alone is free; the content of III.64 is that the marker travels with it") is accurate.
* `g2_rigid_of_one_assumption`, `g2_rigid_iff_complete` (`ETM/G2Rigidity.lean`): as stated, and the hypothesis is equivalent to the
  conclusion (F4).
* `o1_iff_complete`, `ym_complete_iff`, `fineOneBox_iff_complete`, `ym_assembly_of_complete` (`ETM/RotationInstances.lean`): as
  stated; a restatement by construction (F8).
* `ns_not_complete`: the "Navier-Stokes box" has the gate factor `K 2^{5k/2} / (ν 4^k)` clipped to [0, 1], the energy-only scaling;
  "in the energy-only model" in the abstract is the right qualifier, and VII.0 says the modules contain no Navier-Stokes object.
* `etm_balance_undecidable`, `etm_edge`, `reaches_of_contracting`, `balanceBound` (`ETM/Machine.lean`): a real reduction from
  Mathlib's `ComputablePred.halting_problem`; scope as in F11.
* `explicit_formula_of_smooth` (`GRH/ContourShiftTie.lean`): for every smooth compactly supported test function and every
  enumeration of the nontrivial zeros with multiplicity (`NontrivialZeroFamily`: real part in (0, 1), a zero of `riemannZeta`, and
  `encard` of each fibre equal to `analyticOrderAt`), with no named hypothesis: as stated in V.1.5.
* `cross_any_system` (`Proof/Crossing.lean`): as stated in VI, with the two hypotheses (F18 for the abstract).
* `LiftCPConst`, `ExtractAPI`, `liftCPConst_iff_extract` (`Proof/LiftingNP.lean`, `Proof/SoundAPI.lean`): an equivalence of two
  forms of the same open statement, as the file says ("Nothing here is a lower bound"); the abstract's "the equivalence of the
  lifting interface with lifting by constant-size gadgets" is accurate.
* `su2_handover` with `0 < Z_tw` as hypothesis, and `sunZtw_pos` not linked to it: stated as such in the abstract, III.1, IV.3.
* GU (`General/GUCentre.lean`): kernel of the SU(5) block embedding is the cyclic group of order 6, charge in thirds; the axiom log
  matches X.3 (21 declarations; `gen_trivial_sm` on `propext` only; two definitions on none).
* Every "Lean (from X)" in the abstract names X: the hand-over (positivity of Z_tw), G2 (the surgery input and the assumption),
  BSD (the named classical parts), the scale certificate (the one assumption). The Hodge bullet does not (F17).

A.3 / B. **Verifier's Lean check** (`G2Check.lean`, run with `lake env lean` in the build folder, not committed):

```lean
import ProofPhase.ETM.ETM
open Arsenal.Rotation

theorem shared_iff_rigid (R : RigidityData.{0, 0}) :
    (∃ (B : Box.{0}) (x₀ : B.X), B.DMPComplete x₀ ∧
        Box.SharedGate B x₀ (fun _ : Unit => R.box) (fun _ => (0 : ℕ))) ↔ R.Rigid := by
  constructor
  · rintro ⟨B, x₀, hB, hs⟩
    exact R.rigid_of_shared B hB hs
  · intro h
    exact ⟨R.box, (0 : ℕ), R.box_complete_iff.2 h, Box.sharedGate_self R.box (0 : ℕ) Unit⟩

theorem g2_shared_iff_rigid (E : Type) (η : E → ZMod 2) {G2Rigid : Prop}
    (hsurg : ProofPhase.ETM.G2Surgery E η G2Rigid) :
    (∃ (B : Box.{0}) (x₀ : B.X), B.DMPComplete x₀ ∧
        Box.SharedGate B x₀ (fun _ : Unit => (ProofPhase.ETM.g2Data E η).box) (fun _ => (0 : ℕ))) ↔ G2Rigid := by
  rw [shared_iff_rigid, twoPoint_rigid_iff]
  exact (show G2Rigid ↔ Function.Surjective η from hsurg).symm
```

Output: `'shared_iff_rigid' depends on axioms: [propext, Classical.choice, Quot.sound]`, the same for `g2_shared_iff_rigid`; no
errors. So the hypothesis pair of `g2_rigid_of_one_assumption` (a certified box and the sharing), closed over the certified box,
is equivalent to G2's rigidity given the surgery input: F4. The same file checked the Mathlib names V.2.2 cites:
`ZMod.completedLFunction_one_sub_even` and `ZMod.completedLFunction_one_sub_odd` exist in Mathlib v4.34.0
(`Mathlib/NumberTheory/LSeries/ZMod.lean`, l. 461 and 509) and state the functional equation for even and odd functions on Z/N, as
V.2.2 says.

## C. The one assumption

* **Stated once.** III.4.4 is the one place; III.64 in `CLAIMS.md` points there. It is stated in prose as an identification (the ODP
  is established, so the one box is a running, DMP-complete system), marked **[reading]** for the identification and **[open]** per
  object. It is not stated *exactly* as one mathematical statement: in Lean it is a family of hypotheses, one per object and per
  use (F5). Within each card the instance is exact (`SharedGate`, `HandoverSide`, `FineOneBox`, `ScaleSign`, `LiftCPConst`).
* **Conditional marks.** Checked every use I could find: the scale certificate (III.68a, abstract "Under it"), the direction of
  every later tick (III.66), the lower edge (III.64a, IV.9.5b), "certified on the box, hence everywhere" (III.68d), III.69c, IV.10e,
  G2 (A.5u): each is marked conditional or carries the assumption as a named hypothesis. No sentence was found that states a
  consequence of III.64 as proved.
* **The scale certificate is exactly what the Lean proves**: yes (B). The content sits in the hypothesis, as III.68b says.
* **The rigid start.** "{infinity, 2, 3}" is certified only as the GRH first box (A.4); its identification with the rigid SU(N)
  (N <= 3) and with "the start where the floor is forced" is **[reading]** (III.69, III.70) and marked so in the body. The abstract's
  "The start is fixed where the floor is forced, at the places {infinity, 2, 3}, certified with explicit margins" joins the
  certified part (margins) and the reading (where the floor is forced) in one unmarked sentence; it is covered by F5's fix.
* **"G2 rigid from the one assumption"**: the Lean proves it, and its hypothesis is equivalent to the conclusion (F4).

## D. Each card

* **Yang-Mills.** O1 is the real gap of the mechanism and is stated exactly in its Lean form `FineOneBox`; the number form is a
  sufficient route (F21). The Clay statement's other needs are named (O2 to O4), so "one open step" holds for the box only (F6). The
  external construction (IV.9): the submission repository exists as described (bibliography row 97, checked by an agent: repository,
  dates, authorship); its scope as stated (no uniqueness of the limit, no mass gap) matches the row's reading.
* **GRH.** The open step (Weil positivity at every support, from arithmetic, beyond the certified first box) is the real gap for the
  positivity route; V.0 states that RH and Dirichlet GRH are proved by others by another route. That external claim is accurate as to
  existence, date, author, size (17 million lines) and kernel checks (F7, F12 for the wording).
* **P vs NP.** The open step `LiftCPConst` with c > 0 for a constant gadget is stated exactly and is the real gap of the route; the
  Cook-Reckhow equivalence and "NP != coNP implies P != NP" are right.
* **Navier-Stokes.** Fefferman's four forms (A) to (D) are stated correctly, including that an unforced blowup proves (C)/(D) with
  f = 0. The two posted claims: Alpoge-Buckmaster, version of 20 November 2026, 79 pages, repository README: the certificate
  "whose hash the paper gives is not in this repository; the paper says that it will be released" (agent read of
  https://github.com/tristanbuckmaster/navier-stokes/; matches "announced, not released"). OpenAI, 8 September 2026: the page says a
  smooth external force is applied and links a Lean repository; "compactly supported" is not on the page (the PDF was not read here:
  unknown). The related arXiv items 2610.08144 and 2609.26790 exist with the stated authors and titles (`curl` of the arXiv pages).
* **BSD.** The open step (rank = order, from order 2 on) is right over Q (F19); Goldfeld's theorem is described correctly; Kolyvagin's
  contrapositive is right. "A finite order at s = 1 from Hasse's bound" is for every continuation, which the text says exists over Q
  by modularity (external): accurate in the body.
* **Hodge.** The open step (codimension >= 2) and the external inputs of the curve card are stated in the body (F17 for the abstract).
* **GU.** The open step and the reading that selects Z_6 are marked; "any compact U(1) also gives" uniform charge quantisation is
  stated honestly.

## E. Validation

* **SU(N) Ricci flow (A.3):** Ric = (N/2) g for the metric -tr(XY) (Killing form 2N tr(XY)), so g(t) = (1 - N t) g(0); first eigenvalue
  N - 1/N (Casimir of the fundamental representation); for N = 2 it equals the Lichnerowicz bound 3/2, Obata's case: all right.
* **Poincare for SU(3):** X. Wang, arXiv 1810.08478, "On 1-connected 8-manifolds with the same homology as S^3 x S^5" exists
  (`curl` of the arXiv page); SU(3) has that homology, so the source is the right kind. Theorem 1.1 and Corollary 1.2 were not read
  here: unknown whether they state the SU(3) case exactly as A.3 does.
* **N >= 4 fails:** the argument (a normal invariant in H^8(SU(N); Q), x_3 x_5, changes p_2; L_odd(1) = 0 for N even, and Novikov's
  topological invariance of rational Pontryagin classes) is sound as sketched for N even; for N odd (dimension N^2 - 1 divisible by 8
  when N is odd, L = Z) the surgery obstruction must be killed by another normal invariant, which the sketch does not say. Marked
  **[paper]**; acceptable as a sketch, recorded here as a gap in the prose.
* **Sp(2) rigid:** cells in dimensions 0, 3, 7, 10; pi_3(G/TOP) = pi_7(G/TOP) = 0, the top cell's pi_10(G/TOP) = Z/2 maps isomorphically
  to L_10(1) = Z/2 (Arf), L_11(1) = 0: the structure set is a point. Sound.
* **G2's two structures:** plausible from the cells (3, 5, 6, 8, 9, 11, 14) and the Z/2 in H^6 (x_3^2); the count needs the full
  normal-invariant computation, which `docs/unified/` carries; not re-derived here (unknown).
* **Kreck-Lueck:** arXiv math/0509238, "Topological rigidity for non-aspherical manifolds", Kreck and Lueck (`curl`); the row's
  description of Theorem 1.1 (Borel manifold iff the self-equivalences act transitively on the structure set) is what the G2
  `External` string uses. The theorem text was not read here.
* **Perelman (A.1):** the comparison T <= 3/(2 R_min(0)) from dR/dt >= Delta R + (2/3) R^2 is right; the account of surgery and finite
  extinction is the standard one.

## R. References

177 rows. Six haiku agents read each row on arXiv, Crossref, dblp or the publisher (results kept with this verifier; summary):
158 rows matched their record. 4 were flagged as mismatches: rows 82 and 83 (wrong link, F3), row 149 (title, F14), row 48
(Presburger 1929 against 1930 on the record: a convention the text already explains in III.5, "1929 congress, proceedings 1930"; not
a finding). Row 29 (Grothendieck 1969, Bombay colloquium) has no Crossref record and its Stacks page refused the fetch. 14 rows could
not be read on an authoritative page in this run: rows 114 and 115 have no data to look up (F2); the others are Bombieri 2000 (the
Clay PDF and its year, rows 18 and 19), Hopf 1963, Erdos-Lovasz 1975, the journal reference of Reece 2023, the Lund original of
Weil 1952, Cantor 1891, the title variant of the 1923 Szeged paper (row 88), Georgii, the OpenAI Navier-Stokes PDF (row 140), the
author of the Clay BSD description (row 158), and the 1970 first edition of Wall. None of these is shown wrong; they are "unknown". No arXiv identifier of 2026 (`26xx.xxxxx`) was
found fabricated: 2610.08144, 2609.26790, 2607.18341 resolve with the stated authors and titles.

## P. The personal note

Factual sentences checked against the record: "everything needed is public under Apache 2.0" holds (`gh api repos/StevenHrovat/{gravity,im,dmp}`:
public, `Apache-2.0`). "after GRH got proven and certified": see F7. The first mass-gap commit (`f0ff10f`, 2026-11-21 00:10 UTC) is
after the library's release on 2026-11-20, consistent with the sequence the note tells. The sentence about v1 refers to a document
not in this repository (unknown). The sentences about the author's own history are not checkable here and are not judged.

## F. Format

Clean build: `pdflatex` exits 0 twice, 99 pages, no `!` errors, no undefined references or citations in the log. Leftover
meta-text: F1, F24. Placeholders: F2. Abstract: F16. Status marks: F15. Layout: F26. Every cross-reference resolves:
`python tools/claims-check.py` prints `claims-check: OK` (659 claims; every label in the paper resolves).

Release-blocking findings: 3
