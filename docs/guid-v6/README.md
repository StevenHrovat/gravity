# GUID v6: Our proposed view of the universe, with its predictions tested against current experimental data

A complete, standalone paper. It states GUID's account of gravity and of what gravity contains (Part I). It hosts that account in
simulation (Part II) and confronts every prediction that existing data can reach (Part III). It ends with the predictions, the ledger of
verdicts, the corrections to version 5.1 and where we expect it to break (Part IV).

**It replaces version 5.1** (`docs/quantum-gravity/`), which stays in the repository as the record. Nobody needs to read v5.1 or any
other document to follow this one.

- English: `guid-v6.pdf` (built from `guid-v6.tex`).
- German: `de/guid-v6-de.pdf`. Its LaTeX source is not tracked, as with v5.

## Layout

| file | what it holds |
|---|---|
| `guid-v6.tex` | title, abstract, introduction; includes everything else in reading order |
| `preamble.tex` | packages, theorem environments, the marks (D), (H), (P), (S) and `\chk{}` |
| `part1.tex` | Part I, the proposal: axioms, the two fields, what the axioms fix, classical-quantum dynamics and the bridges, the experiments, thermodynamics, black holes, holography, 2+1, cosmology and dark matter, matter, hosting, the landscape |
| `sections/hosted.tex` | Part II: known quantum configurations hosted (`docs/simulation/hosted_benchmarks.py`) |
| `sections/holocode.tex` | Part II: the holographic assembly at thousands of qubits (`holographic_code.py`) |
| `sections/gravsim.tex` | Part II: the recorded frame against the coherent field (`gravity_simulated.py`, G1, G3, G4) |
| `sections/bmv.tex` | Part II: the decisive experiment under Bridge B and the corrected spin witness (`gravity_simulated.py` G2, `bmv_witness.py`) |
| `sections/sparc.tex` | Part III: rotation curves (`sparc_rotation.py`) |
| `sections/remnant.tex` | Part III: the accumulated remnant, halos and the joint fit (`remnant_history.py`) |
| `sections/data.tex` | Part III: every other prediction against data (`predictions_vs_data.py`) |
| `part4.tex` | Part IV: predictions, ledger, corrections from v5.1, where it breaks, conclusion, contributions, licence |
| `appendix.tex` | reproducibility (scripts, checks, runtimes, data digests) and the checks of Part I |
| `bib-core.tex`, `bib-extra.tex`, `sections/*-bib.tex` | the reference pools; `build_bib.py` writes `bibliography.tex` from them |
| `checks.py` | every number of Part I (125 of 125) |
| `reproduce.py` | runs every script behind the paper and prints the check counts |
| `testwrap.tex` | compiles one section on its own |

## Build

```
cd docs/guid-v6
python3 build_bib.py            # bibliography.tex: every cited key, in order of first citation; fails on a missing key
pdflatex guid-v6.tex
pdflatex guid-v6.tex            # twice, for the references
```

Requirements: a TeX Live with `longtable`, `tabularx`, `booktabs`, `multirow`, `caption`, `enumitem` and `hyperref`. The figures are
read from `docs/simulation/figures/`.

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
| `docs/simulation/bmv_witness.py` | 32 of 32 |
| `docs/simulation/sparc_rotation.py` | 36 of 36 |
| `docs/simulation/remnant_history.py` | 39 of 39 |
| `docs/simulation/predictions_vs_data.py` | 6 of 6 numerical checks; 30 of 33 scored confrontations consistent at 95% (exits 1 by design) |

- **SPARC data.** The tables (Lelli, McGaugh and Schombert 2016) are not redistributed. Their SHA-256 digests are in Appendix A, and
  the scripts check them before use.
- **Determinism.** Every script fixes its seeds and pins BLAS to one thread. Two runs give identical output apart from the runtime
  field.

## What changed from v5.1

Section "What changed from version 5.1" of the paper lists twenty-three corrections and sharpenings, each with its evidence. In short:
- **Corrected bounds and data:**
  - the 95% bound on the information scalar (3.1e-5);
  - the newest clock bound, with the negative drift derived but unobservably small;
  - the Bridge B smearing length (R0 >= 4e-10 m);
  - Starobinsky inflation against ACT DR6 (needs N >= 63);
  - the DESI DR2 neutrino bound, the DES recalibration and the inherited H0 and curvature tensions;
  - the graviton-mass bound.
- **Experiments:**
  - a null BMV result does not discriminate if Diosi-Penrose decoherence is real; decoherence does;
  - the spin witness of Bose et al. as printed is reached by product states, and a corrected witness is given.
- **Dark matter:**
  - Bridge A is refuted by rotation curves too;
  - the stochastic remnant is refuted as the dark matter in every form computed;
  - primordial black holes from the start are the consistent reading.

## References

Every reference was checked against a publisher, arXiv or collaboration record. The numbers taken from each, and how they were read,
are listed in the results notes of the scripts: `docs/simulation/results/*.md`, "Citations". The core references of Part I carry over
from v5.1 (`docs/quantum-gravity/README.md`). A reference that could not be re-checked is marked as such in the text.

One reference was read only in part: the published version of Bose et al., PRL 119, 240401. Its arXiv text (v1, the only version) was
read, and the publisher's page was outside this session's network allowlist. Section "bmv" says so.

## Licence

Apache License 2.0.
