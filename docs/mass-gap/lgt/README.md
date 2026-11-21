# Draft contributions to `mrdouglasny/lgt` (2026-11-21)

Lean files written against `lgt` at commit `b8793cc` (Lean 4.30.0, its pinned Mathlib), filling stubs there. They are kept here because
the gravity evidence chain is core Lean only; nothing is offered upstream without the owner's decision.

| file | replaces in `lgt` | status |
|---|---|---|
| `WilsonLoop.lean` | `LGT/WilsonAction/WilsonLoop.lean` (a one-line stub) | builds, no `sorry`, standard axioms only |

Build: clone `lgt` at `b8793cc`, `lake exe cache get`, copy the file over the stub, `lake build LGT.WilsonAction.WilsonLoop`.

What `WilsonLoop.lean` proves: lattice paths and their holonomy; gauge covariance of open paths (`pathHol_gauge_covariant`, the
transformation telescopes to the two ends); gauge invariance of Wilson loops (`wilsonLoop_gauge`, and `wilsonLoop_gauge_invariant` in
`lgt`'s `IsGaugeInvariant` form); the plaquette as the smallest Wilson loop (`plaquettePath_hol`, `plaquettePath_isLoop`); the R × T
rectangle in any plane is a closed path and its Wilson loop is gauge-invariant (`rectPath_isLoop`, `rectWilsonLoop_gauge`).
