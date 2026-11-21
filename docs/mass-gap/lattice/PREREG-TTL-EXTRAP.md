# Pre-registration: is the TTL scan's failure a coarse-grid artefact? (2026-11-21, after the scan's verdict, before this fit)

**Why.** The TTL scan (`PREREG-TTL.md`) **failed** its constancy criterion at the coarsest grid (β = 2.3). Lattice discretisation errors
of the Wilson action shrink like (lattice spacing)², i.e. like (a√σ)² in string-tension units; the standard check for "the same at every
layer up to discretisation errors" is a continuum extrapolation. This is a **follow-up hypothesis formed after seeing the data**; it
cannot change the scan's recorded verdict, and it is labelled as such wherever it is reported.

**Data.** The five points of `results/ttl_summary.json` (unchanged): x = (a√σ)², y = TTL · √σ = 1/(m₀₊₊/√σ), errors as computed.

**Fit.** Weighted least squares y = c + k·x, with errors on y only (the x errors are small by comparison; reported, not propagated).

**Criteria.**
1. **Fit quality:** p > 0.05 for χ² with 3 degrees of freedom. **Fail** otherwise (then the a² form does not describe the data).
2. **Continuum value:** c agrees with 1/3.74 = 0.267 ± 0.009 (Teper's continuum m₀₊₊/√σ) within 2 combined errors.
3. **The coarse-grid term:** k > 0 (TTL larger on coarser grids), at least 2 errors from 0; otherwise the artefact hypothesis is not
   supported by these data even if 1 and 2 pass.

**Verdict.** 1 to 3 hold: the failure is consistent with an a² discretisation effect and the continuum TTL agrees with the known value.
Any failing: reported as such. Either way the scan's own verdict (fail) stands.

## Result (2026-11-21)

Fit y = c + k·x with x = (a√σ)²: c = 0.2470 ± 0.0061, k = 0.30 ± 0.11, χ²/dof = 5.4/3, p = 0.15.

1. Fit quality: p = 0.15 > 0.05: pass.
2. Continuum value: c against 1/3.74 = 0.267 ± 0.009: 1.9 errors: pass (narrowly).
3. Coarse-grid term: k > 0 at 2.7 errors: pass.

**Verdict:** the TTL scan's failure is consistent with an a² discretisation effect, and the extrapolated continuum TTL agrees with the
known value within 2 errors (at the margin). This is a post-hoc hypothesis tested after a pre-registration of its own; the scan's verdict
(fail on constancy across raw lattice spacings) stands. Stored: `results/ttl_extrapolation.json`.
