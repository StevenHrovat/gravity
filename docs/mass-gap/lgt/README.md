# Draft contributions to `mrdouglasny/lgt` (2026-11-21)

Lean files written against `lgt` at commit `b8793cc` (Lean 4.30.0, its pinned Mathlib), filling stubs there. They are kept here because
the gravity evidence chain is core Lean only; nothing is offered upstream without the owner's decision.

| file | replaces in `lgt` | status |
|---|---|---|
| `WilsonLoop.lean` | `LGT/WilsonAction/WilsonLoop.lean` (a one-line stub) | builds, no `sorry`, standard axioms only |
| `CentreSymmetry.lean` | new file `LGT/WilsonAction/CentreSymmetry.lean` | builds, no `sorry`, standard axioms only |

Build: clone `lgt` at `b8793cc`, `lake exe cache get`, copy the file over the stub, `lake build LGT.WilsonAction.WilsonLoop`.

What `WilsonLoop.lean` proves: lattice paths and their holonomy; gauge covariance of open paths (`pathHol_gauge_covariant`, the
transformation telescopes to the two ends); gauge invariance of Wilson loops (`wilsonLoop_gauge`, and `wilsonLoop_gauge_invariant` in
`lgt`'s `IsGaugeInvariant` form); the plaquette as the smallest Wilson loop (`plaquettePath_hol`, `plaquettePath_isLoop`); the R × T
rectangle in any plane is a closed path and its Wilson loop is gauge-invariant (`rectPath_isLoop`, `rectWilsonLoop_gauge`).

What `CentreSymmetry.lean` proves, for a central `z` with `z·z = 1` acting as `−1` in the gauge representation (for U(n) and SU(2):
`z = −1`), with left multiplication by `z` preserving the single-link Haar measure (stated as a hypothesis, since `lgt`'s
`HasHaarProbability` does not assert invariance): flipping one link multiplies every path's holonomy by `z` once per visit
(`pathHol_flipAt`) and Re Tr by `(−1)^visits` (`gaugeReTr_zpow_mul`); the flip preserves the product Haar measure
(`measurePreserving_flipAt`); an integrand odd under the flip integrates to zero (`integral_eq_zero_of_flip_odd`); and the **selection rule**
`integral_parity_eq_zero`: a Wilson loop times odd functions of the plaquettes in `O` times even functions of any plaquettes integrates
to zero unless every link is visited an even number of times by the loop and the boundaries of `O` together, i.e. only closed surfaces
mod 2 survive. This is the step of the strong-coupling area law that forces the minimal spanning area.
