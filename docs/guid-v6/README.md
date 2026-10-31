# GUID v6: Our proposed view of the universe, with its predictions tested against current experimental data

A complete, standalone paper in four parts. Part I states GUID's account of gravity and of what gravity contains, with every hypothesis
listed and a test plan at its end; it quotes only the measured bounds its statements rest on. Part II simulates the account, Part III confronts every prediction that existing
data can reach, and Part IV says what the tests show, gives the ledger of verdicts and names where we expect the account to break. Ten short
primers introduce each field where it first enters, so a reader from any one field can follow the whole.

**It replaces version 5.1** (`docs/quantum-gravity/`), which stays in the repository as the record. Nobody needs to read v5.1 or any
other document to follow this one.

- English: `guid-v6.pdf` (built from `guid-v6.tex`).
- German: `de/guid-v6-de.pdf`. Its LaTeX source is not tracked, as with v5.

## Layout

| file | what it holds |
|---|---|
| `guid-v6.tex` | title, abstract, introduction (the problem, the proposal, the eight steps, what is new, results in brief, how to read); includes everything else in reading order |
| `preamble.tex` | packages, theorem and primer environments, the marks (D), (H), (P), (S) and `\chk{}` |
| `part1.tex` | Part I, the proposal: DMP, the hypotheses and names, what the axioms fix (with the start and hosting), classical-quantum dynamics and the bridges, the experiments and the dissent, black holes, holography, 2+1, cosmology, dark matter, the information scalar and matter (with H8 and H9), readings, the approaches, the test plan |
| `primers/p1-dmp.tex` ... `p10-hadron.tex` | the ten background boxes (DMP, general relativity, quantum information, classical-quantum dynamics, holography, cosmology, particle physics, hadron spectroscopy, statistics, galaxy dynamics) |
| `figures/fig-map.tex`, `fig-steps.tex`, `fig-act.tex`, `fig-timeline.tex` | the four TikZ figures of Part I |
| `sections/gravsim.tex` | Part II: the recorded frame against the coherent field (`docs/simulation/gravity_simulated.py`, G1, G3, G4) |
| `sections/bmv.tex` | Part II: the decisive experiment under Bridge B and the corrected spin witness (`gravity_simulated.py` G2, `bmv_witness.py`) |
| `sections/holocode.tex` | Part II: the holographic assembly at thousands of qubits (`holographic_code.py`) |
| `sections/hosted.tex` | Part II: known quantum configurations hosted (`hosted_benchmarks.py`) |
| `sections/scoring.tex` | Part III: the scoring rules and classes, fixed once for every section |
| `sections/data.tex` | Part III: laboratory, solar-system and cosmological data (`predictions_vs_data.py`) |
| `sections/sparc.tex` | Part III: dark matter I, rotation curves (`sparc_rotation.py`) |
| `sections/remnant.tex` | Part III: dark matter II, accumulation, halos, cosmic time, primordial black holes; the one home of the dark-matter verdict (`remnant_history.py`) |
| `sections/standard_model.tex` | Part III: the Standard Model statements, pre-registered in `docs/simulation/sm_preregistration.md` (`standard_model.py`) |
| `sections/exotics.tex` | Part III: hadrons as trees of dualities (H8) and the minting in hadrons (H9) (`exotic_hadrons.py`) |
| `sections/tally.tex` | Part III: every scored confrontation counted in one table (`tally.py`) |
| `part4.tex` | Part IV: what the tests show, the ledger, where it breaks, conclusion, acknowledgements, contributions, licence |
| `appendix.tex` | Appendices A and B: reproducibility (scripts, checks, runtimes, data digests) and the checks of Part I |
| `appendix-changes.tex` | Appendix C: the changes from version 5.1, each with its evidence |
| `sections/hosted-appendix.tex`, `holocode-appendix.tex`, `exotics-appendix.tex` | Appendices D to F: the detail of the hosting benchmarks, the holographic code and the hadron model |
| `appendix-readings.tex` | Appendix G: the readings that add no prediction, in full |
| `bib-core.tex`, `bib-extra.tex`, `sections/*-bib.tex` | the reference pools; `build_bib.py` writes `bibliography.tex` from them |
| `checks.py` | every number of Part I (125 of 125) |
| `reproduce.py` | runs every script behind the paper and prints the check counts |
| `testwrap.tex` | compiles one section on its own |

## Build

```
cd docs/guid-v6
python3 build_bib.py            # bibliography.tex: every cited key, in order of first citation; fails on a missing key
pdflatex guid-v6.tex
pdflatex guid-v6.tex
pdflatex guid-v6.tex            # three passes, for the references and the long tables
```

Requirements: a TeX Live with `longtable`, `tabularx`, `booktabs`, `multirow`, `caption`, `enumitem`, `hyperref`, `tcolorbox` and
`tikz`. The data figures are read from `docs/simulation/figures/`; the four figures of Part I are TikZ sources in `figures/`.

## Reproduce every number

```
python3 docs/guid-v6/reproduce.py --data <folder with the two SPARC .mrt files>
```

| script | checks |
|---|---|
| `docs/guid-v6/checks.py` | 125 of 125 |
| `docs/qg-verdict/assembly.py` | 18 of 18 |
| `docs/simulation/hosted_benchmarks.py` | 53 of 53 |
| `docs/simulation/holographic_code.py` | 77 of 77 |
| `docs/simulation/gravity_simulated.py` | 110 of 110 |
| `docs/simulation/bmv_witness.py` | 34 of 34 |
| `docs/simulation/sparc_rotation.py` | 39 of 39 |
| `docs/simulation/remnant_history.py` | 39 of 39 |
| `docs/simulation/predictions_vs_data.py` | 6 of 6 numerical checks; 28 of 31 scored confrontations consistent at 95% (exits 1 by design) |
| `docs/simulation/standard_model.py` | 32 of 32 |
| `docs/simulation/exotic_hadrons.py` | 80 of 80 |
| `docs/simulation/tally.py` | 6 of 6 (72 scored confrontations across the paper, 58 hold) |

- **SPARC data.** The tables (Lelli, McGaugh and Schombert 2016) are not redistributed. Their SHA-256 digests are in Appendix A, and
  the scripts check them before use.
- **Determinism.** Every script fixes its seeds and pins BLAS to one thread. Two runs give identical output apart from the runtime
  field.

## What changed from v5.1

Appendix C of the paper lists twenty-three corrections and sharpenings, each with its evidence. Beyond them, version 6 adds:
- **Structure:** one standalone paper in four parts (state, simulate, test, judge), ten primers, four figures, one scoring section and one
  tally, so that every number has one home.
- **Simulation (Part II):** the recorded frame against the coherent field at 4000 masses; the decisive experiment under Bridge B (no
  two-sphere geometry entangles at the Diosi-Penrose rate) and a corrected spin witness; the holographic code at 5120 qubits; four
  hosted quantum systems.
- **Tests (Part III):** 72 scored confrontations, 58 hold. The 14 FAILs are 11 inherited tensions of LambdaCDM, the Standard Model and
  a borrowed hadron model, and all 3 GUID-specific statements that a datum or a derivation can already reach; 22 GUID-specific rows hold
  but are not yet sensitive.
- **Dark matter:** Bridge A and the stochastic remnant are refuted by rotation curves in every form computed; primordial black holes from
  the start remain, untested here.
- **Standard Model:** pre-registered statements SM1 to SM5; the Higgs couplings follow mass; Dirac neutrinos with B-L read as a count
  (an added reading) predict no neutrinoless double-beta decay; the pre-registered window for R = dln mu/dln alpha failed.
- **Hadrons:** H8, hadrons as trees of dualities (a reading QCD allows; a standard colour-spin model fails for 5 of 9 measured masses),
  and H9, a pentaquark as a minting (no open-flavour pentaquark, hidden-bottom pentaquarks near 11.1 GeV live; the general one-flavour
  rule and the alpha M/2 splitting refuted).

## References

Every reference was checked against a publisher, arXiv or collaboration record. The numbers taken from each, and how they were read,
are listed in the results notes of the scripts: `docs/simulation/results/*.md`, "Citations". The core references of Part I carry over
from v5.1 (`docs/quantum-gravity/README.md`). A reference that could not be re-checked is marked as such in the text.

One reference was read only in part: the published version of Bose et al., PRL 119, 240401. Its arXiv text (v1, the only version) was
read, and the publisher's page was outside this session's network allowlist. Section "bmv" says so.

## Licence

Apache License 2.0.
