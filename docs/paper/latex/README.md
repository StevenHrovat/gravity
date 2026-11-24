# The paper as LaTeX (draft 4)

`guid-v8.tex` is generated from `../draft/*.md` by `tools/paper-latex.py`; do not edit it by hand. `guid-v8.pdf` is its build.

Build, from the repository root:

```
python tools/paper-latex.py
cd docs/paper/latex && pdflatex guid-v8.tex && pdflatex guid-v8.tex
```

Needs a TeX distribution with `lmodern`, `geometry`, `booktabs`, `longtable`, `enumitem`, `newunicodechar`, `hyperref` (MiKTeX and
TeX Live have them). The editors' notes under each chapter heading stay in the Markdown and are left out of the typeset paper.

The last section is the bibliography, typeset from `../references.md` (one row per work, with the page each entry was read from and
its status: checked, partly checked, or not yet identified). Task R of the final verification re-checks every entry (`../REVIEW.md`).
