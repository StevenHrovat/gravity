# Pushing the proven lattice gap outward: quick shots (2026-11-21)

The idea (owner-approved step 1): `lgt` proves the lattice mass gap with Dobrushin's method (a blast-radius contraction: each link
passes on at most a fraction of any disturbance) for β < 1/96 in four dimensions. Sharper influence estimates, and then blocks
(Dobrushin–Shlosman), could push the proven region outward. Before spending a day on rigour, two quick shots, pre-registered in
[`PREREG.md`](PREREG.md). All β below are the standard Wilson β (SU(2): β Σ ½ Re Tr U_p; U(1): β Σ cos θ_p).

## Shot 1: the exact single-link influence (`single_link.py`, 56 s)

| | `lgt` (proven, Lean) | Shen–Zhu–Zhu (proven, Bakry–Émery) | exact single-link total-variation Dobrushin (this, floating point) |
|---|---|---|---|
| SU(2) | 0.0104 | 0.0833 | **0.1310** (π/24 = 0.1309 to linear order) |
| U(1) | 0.0104 | | **0.0874** (π/36) |

Sanity checks passed: at β = 10⁻³ the computed influence equals the linearisation to 4 digits; a direct Monte Carlo on S³ at β = 0.1
gives 0.04245 ± 0.00004 against 0.04242. The worst case is the obvious one: the other five staples cancel and the changed staple flips
sign. Pre-registered criterion "worth step 2" (β\* > 0.0833) met, **but the literature check that the criterion named came out
against it:**

## What others already claim (searched 2026-11-21; none of it refereed)

- `creelie/4Y-M` (an AI-assisted research repository, pull request #9, 2026): single-link **Wasserstein** Dobrushin for SU(2) up to
  β < 2/9 ≈ 0.222, with a proof that W₁ between von Mises–Fisher laws on S³ is at most |b − b′|/4, called "the ceiling of every
  single-link Wasserstein–Dobrushin argument"; parts checked in Lean. https://github.com/creelie/4Y-M/pull/9
- "Explicit strong-coupling mass gap and a robust landing interface for four-dimensional SU(2) lattice Yang-Mills theory" (preprint):
  computer-assisted Wasserstein row sums ≤ 0.9953 for β ≤ 0.419, with a decimated (block) specification, and a ceiling near 0.43 for
  that method.

So the single-link total-variation computation is **not new and not competitive**: it is the textbook version, and others claim up to
1.7× (single link) and 3.2× (blocks) more. Step 2 as planned (make 0.131 rigorous, formalise in `lgt`) is dropped. These claims are
unrefereed; checking them independently would be audit work, which the owner has set aside.

## Shot 2: does a box forget its boundary, across the whole range? (`wall.py`, `analyse_wall.py`)

(results below when the runs finish)
