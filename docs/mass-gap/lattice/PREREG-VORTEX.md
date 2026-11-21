# Pre-registration: do the MG3 twists carry the string tension? (2026-11-21, before any production run)

**Why.** Finding MG7: inside DMP the mass gap follows from Axiom 1's reach; in physics words, from confinement. Finding MG3 (`Gauge.lean`,
`twisted_balanced`): a network can pass every local check and still be off by one around a big loop. In SU(2) exactly such twists are
centre vortices. The question in DMP terms: **are the MG3 twists what keeps IM within reach?** In physics terms: do centre vortices
carry the string tension? This reproduces a known lattice result (Del Debbio, Faber, Greensite and Olejnik 1997; de Forcrand and
D'Elia 1999); what it adds is the link to DMP's own theorem, checked with this project's code.

**Method.** `vortex.py` (self-test: gauge fixing leaves every Wilson loop unchanged to 2 × 10⁻¹⁶, the gauge functional rises
monotonically). SU(2), configurations from the GPU heat bath; maximal centre gauge by checkerboard site updates (300 sweeps); centre
projection Z = sign(½ tr U); vortex removal U′ = Z·U. Wilson loops W(R, T), R, T ≤ 5, averaged over all six planes; Creutz ratios
χ(R) = −ln[W(R,R) W(R−1,R−1) / (W(R,R−1) W(R−1,R))]; errors by jackknife over configurations.

**Runs.** β = 2.3 on 12⁴ and β = 2.4 on 16⁴ (boxes of at least four times 1/√σ), 4 chains, configurations 20 sweeps apart, at least
100 configurations per β.

**Criteria, for R = 3 and 4 at each β (χ_full, χ_proj, χ_removed, χ_control):**

1. **The twists carry the string tension:** χ_proj agrees with χ_full within 30 % (centre dominance; the known result is agreement
   within roughly 10 to 20 % at these β).
2. **Removing the twists removes it:** χ_removed is below 20 % of χ_full, or consistent with zero within 2 errors.
3. **Control:** projecting without the gauge fixing (χ_control) gives no string tension: the projected loops W(R, T) for R, T ≥ 2 are
   consistent with zero within 2 errors (the Creutz ratio is then undefined), so the result is not an artefact of projecting.

**Verdict.** All three at both β: **pass**, the MG3 twists carry the string tension in SU(2) at these couplings. Criterion 1 or 2 failing at
either β: **fail**, reported as such. Nothing here explains *why* the twists stay randomly spread at every scale; that is again the open
problem. The photon test does not apply directly (U(1) has no discrete centre twists of this kind; its analogues are magnetic monopoles).
