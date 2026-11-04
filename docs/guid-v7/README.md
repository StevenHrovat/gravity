# GUID v7: From Inflation to the Standard Model, read through the axioms of DMP

One timeline from the end of inflation to today's accelerating expansion, with its black holes, its matter surplus, its particles and its
dark energy, tested on data and on the lattice. It is a complete, standalone stage: nobody needs to read v6 or any other document to
follow it. **Version 6** (`docs/guid-v6/`) stays as it is.

- English: `guid-v7.pdf` (19 pages, built from `guid-v7.tex`). There is no German version yet.
- Draft of 4 November 2026, reviewed once by an independent Claude session before it was merged. Every review finding is applied:
  the lensing value, the net result with lensing included, the order of fitting, the trial count, and seven verdicts. Nothing here has
  been reviewed by a physicist.

## What it claims

The timeline is coherent where the paper says it holds and it breaks where the paper says it breaks; the paper does not claim it is
correct. The ledger (Section 12) has 54 items: 13 hold, 15 are readings, 15 are refuted or dropped, 11 are open. The dark-energy law
fits the expansion history about as well as DESI's w0-wa form (1-2 sigma over a constant after trials). Its S8 of about 0.85 is
3.7-5 sigma above DES six-year lensing, and with lensing included it is level with or behind the cosmological constant.

## Layout

| file | what it holds |
|---|---|
| `guid-v7.tex` | the whole paper, bibliography inline |
| `fig-de.png` | Figure 1, the leftover law against DESI's w0-wa form (from `runs/de/leftover_predict.py des`) |
| `checks.py` | 60 checks: 37 re-derive analytic numbers from standard inputs (A1-A15), 23 re-read fitted numbers from `runs/` (F) |
| `runs/de/` | the dark-energy scripts and their outputs (62 forms, 3 controls, growth with CAMB, held-out tests, predictions) |
| `runs/pt/` | the switch, the late patches, cogenesis, the one-event table, the LVK check and the whole-timeline pass |
| `runs/bh/REPORT.md` | the black-hole work package (WP1-WP5): collapse thresholds, the gauge objection, the slow-decay rescue, the window and the hum |

The scripts in `runs/` are the record of the runs, kept as they ran: their absolute paths are those of the session that ran them. The
survey data are public and not redistributed: DESI DR2 BAO (CobayaSampler `bao_data`), Pantheon+, DES-SN5YR with the Dovekie
recalibration, and the LVK O3 isotropic background spectrum. The lattice code and outputs and the balance fuzzing are kept with the first
author; the paper quotes their results and their run counts (Appendix A).

## Build and check

```
cd docs/guid-v7
pdflatex guid-v7.tex
pdflatex guid-v7.tex      # two passes, for the references and the long ledger table
python3 checks.py         # needs Python 3 with numpy and scipy; exit 0 when all 60 pass
```

Requirements: a TeX Live with `longtable`, `tabularx`, `booktabs`, `enumitem`, `graphicx` and `hyperref`.

Licensed under the Apache License 2.0, as is the whole repository.
