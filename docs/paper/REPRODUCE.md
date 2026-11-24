# Reproducing GUID v8

Everything the paper claims as **[Lean]**, **[certified]** or **[numerical]** can be rerun from a clone of this repository. One
script drives it: `tools/reproduce.sh`, one stage at a time or all at once. This page says what each stage needs, how long it
takes, and what it prints when it passes.

## What you need

| Tool | Version | For |
|---|---|---|
| Linux, macOS, or Windows with WSL 2 | any recent | everything (the scripts are bash) |
| git, bash, coreutils | any recent | everything |
| Python | 3.10 or later, with `pip install -r docs/paper/requirements.txt` (python-flint 0.9.0, numpy, scipy, mpmath, sympy) | the ledger check, the LaTeX source, the certificates, the numerics |
| elan (the Lean installer) | any; it installs the pinned toolchain itself | the Lean stages |
| Lean 4 and Mathlib | v4.34.0 and v4.34.0, pinned in `docs/mass-gap/formal/lean-toolchain` and `lakefile.toml` | the paper's Lean |
| IM's arsenal | the commit pinned in `docs/mass-gap/formal/lakefile.toml` (fetched by Lake) | the rotation API, the rigidity box, the BSD core |
| pdflatex (TeX Live or MiKTeX) | any recent, with `lmodern`, `geometry`, `booktabs`, `longtable`, `enumitem`, `newunicodechar`, `hyperref`, `xurl`, `doi` | the PDF (optional) |
| Disk | about 10 GB free | the Mathlib cache (about 5 GB) and one build folder |

A clean Python environment for the packages: `python3 -m venv .venv`, `. .venv/bin/activate`, `pip install -r
docs/paper/requirements.txt`. On Debian and Ubuntu, `python3 -m venv` needs the system package `python3-venv` (`sudo apt install
python3-venv python3-pip`); the clean-clone test of this guide stopped there on a fresh WSL Ubuntu without it.

Install elan with its own script (https://github.com/leanprover/elan, "Installation"); the Lean stages then fetch the pinned
toolchain and the Mathlib build cache by themselves (`lake exe cache get`).

## The stages

Run from the repository root. Each stage ends with `ok` lines or `FAIL` lines; the last line is `reproduce: OK` or
`reproduce: FAILED`. Outputs go to `.reproduce/` (or `$REPRO_OUT`).

| Command | What it checks | Time | Passes when |
|---|---|---|---|
| `tools/reproduce.sh paper` | the claims ledger (every label resolves, the counts match), the privacy scan, the LaTeX source, the PDF | under a minute | `paper-gate: OK`, and pdflatex writes `docs/paper/latex/guid-v8.pdf` |
| `tools/reproduce.sh evidence` | the DMP evidence chain: the pinned copy of DMP, the setup file, the Lean build of `evidence/`, the kernel's axiom report | a few minutes | `OK 285 theorems, none resting on more than propext, Quot.sound, Classical.choice` |
| `tools/reproduce.sh lean` | the paper's Lean in `docs/mass-gap/formal`, against Mathlib: all 26 axiom scripts in `docs/unified/` are rerun and every declaration's axiom line is compared with the committed log | the first time about an hour (Mathlib cache and build), later minutes | one `ok` line per script: the same declarations, standard axioms only, no `sorryAx` |
| `tools/reproduce.sh certs` | the certified first box of Part IV (Weil's form at supports a = 3/5, 13/20, 69/100, in ball arithmetic) | about a minute per support | the three `RESULT` lines equal the committed logs: margins 1.500e-9, 3.398e-11, 6.417e-13 |
| `tools/reproduce.sh kernels` | the second kernels: Lean's `leanchecker` and the independent Rust kernel `nanoda_lib` over the whole environment | hours, once; then `tools/independent-check.sh quick` takes minutes | the stages of `tools/independent-check.sh` pass (see `docs/unified/INDEPENDENT-CHECK.md`) |
| `tools/reproduce.sh all` | paper, evidence, lean and certs | about an hour the first time | `reproduce: OK` |

The build folder of the Lean stage is `$FORMAL_DST` (default `~/gravity-formal`): the sources are copied there and built on the
Linux file system, which is much faster than building on a Windows drive.

## Checking one claim

Every claim of the paper has a row in `docs/paper/CLAIMS.md`: its label, its status, its source (the Lean module and declaration,
the log, or the reference), and what would upgrade it. To check one **[Lean]** claim, find its declaration in the source column and
look it up in the axiom log of its module (`docs/unified/*-axioms.log`), or print it yourself in the build folder:

```sh
cd ~/gravity-formal
printf 'import ProofPhase.ETM.ETM\n#print axioms ProofPhase.ETM.essence_decided\n' > /tmp/One.lean
lake env lean /tmp/One.lean
```

The modules each axiom log covers are named at the top of its script. A **[certified]** claim names its log in
`docs/unified/`; a **[numerical]** claim names the script and the note that report it.

## What reproduction does not cover

* **[paper]** claims are arguments in prose; they are checked by reading, not by a script. The surgery computations of Appendix A
  and the analytic estimates of the certificate note (`docs/unified/GRH-ONEBOX-CERT.md`) are of this kind.
* **[external]** claims are results by others, read but not rebuilt here (the Lean proof of the Riemann hypothesis by others, the
  posted Navier-Stokes claims, the Yang-Mills submission). Their sources are in the bibliography.
* The simulations behind **[numerical]** entries of Part III section 7 take hours on a CPU; their scripts and run records are in
  `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/w2/`.

## If something fails

Open the stage's output in `.reproduce/` and compare it with the committed log of the same name in `docs/unified/`. A different
number of declarations usually means a different Mathlib or IM commit than the pinned ones; `lake update` must not be run. A
failure that persists at the pinned commits is a finding: please report it with the output.
