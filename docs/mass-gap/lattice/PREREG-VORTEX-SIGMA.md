# Pre-registration: vortex follow-up against the measured string tension (2026-11-21)

**Status.** A **follow-up hypothesis formed after seeing the β = 2.3 data** of `PREREG-VORTEX.md` (which failed there). Written and
committed before any β = 2.4 vortex data existed (the run was thermalising). It cannot change the original verdict, and it is labelled
as post-hoc wherever reported. For β = 2.3 it is not blind; for β = 2.4 it is.

**Why.** The original criteria compare χ_proj with the full Creutz ratio χ_full at R = 3 and 4. At β = 2.3, χ_full still falls with R
(0.214 at R = 3, 0.184 at R = 4) while χ_proj is flat (0.145, 0.149): small full Wilson loops carry short-distance (Coulomb-like) terms
on top of the string tension, so χ_full at small R overstates σa². The string tension is a large-distance quantity; the standard
comparison in the literature is with the asymptotic σa², which this project measured independently from torelons in the TTL scan
(`results/ttl_summary.json`, same code base, different configurations).

**Reference values** (own torelon measurement, σa² = (a√σ)²): β = 2.3: 0.1227 ± 0.0043; β = 2.4: 0.0666 ± 0.0015. Teper's values are
reported beside them, not used for the verdict.

**Criteria**, at the two largest loops measured, R = 4 and R = 5 (both β; a value with relative error above 50 % is reported as "too noisy"
and does not count as a pass):

1. **Twists carry the string tension:** χ_proj(R) within 30 % of σa² (the tolerance of the original pre-registration, carried over
   unchanged).
2. **Removing the twists removes it:** χ_removed(R) below 20 % of σa², or consistent with zero within 2 errors.

The original control criterion is not repeated; its outcome (fail) stands, and its size is reported beside it.

**Verdict.** 1 and 2 at R = 4 and 5 for β = 2.4 (the blind case): **pass** of the follow-up. β = 2.3 is reported with the same rule but
marked "not blind". Errors: jackknife as in `analyse_vortex.py` (largest of bin sizes 1, 5, 10), combined in quadrature with the error
of σa² for the ratios.
