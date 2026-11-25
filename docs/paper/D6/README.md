# Draft 6 of GUID v8 (`D6`)

Draft 6 grew from Draft 5 and adds to it. Draft 4 is the merged state and is never edited: it stays whole in `docs/paper`. Every
later draft lives whole in its own folder, `docs/paper/DN`, grown from the draft before it:

| Draft | Folder | Grown from | PDF |
|---|---|---|---|
| 4 (merged, G0) | `docs/paper` | 3 | `docs/paper/latex/guid-v8.pdf` |
| 5 (G0 + 1) | `docs/paper/D5` | 4 | `docs/paper/D5/latex/guid-v8-D5.pdf` |
| 6 (G0 + 2) | `docs/paper/D6` | 5 | `docs/paper/D6/latex/guid-v8-D6.pdf` |

A draft names only its number ("Draft 6"); its merged identity is implied by the draft it grew from. A draft is reproduced exactly at
the commit its title page names.

**What Draft 6 adds.** DMP's explanation mechanism, from the first author's readings of 2026-11-25: a k by k table of which part
proves which (II.0.2), in Lean on the kernel alone (IM, `arsenal/core/ArsenalCore/Matrix.lean`): extensibility (2k + 1 cells per new
part), derivation with its chain and its bound (it explains, it never proves), the `·` cells and the DAG. Appendix E applies it to what
Draft 5 measured: the versions of DMP, Gravity and IM (a DAG, every use proven), the repositories (`tools/rebuild matrix`), what a new
part costs, the two kernels and their targets, a result of Draft 5 explained by its chain, and where the mechanism stops (O1). Draft 6
explains what Draft 5 establishes and claims nothing beyond it; the one assumption O1 is untouched.

Everything Draft 5 adds is described in `../D5/README.md`.
