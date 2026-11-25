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

## Result (2026-11-21, after both runs; nothing above changed)

β = 2.3 on 12⁴ (100 configurations) and β = 2.4 on 16⁴ (100 configurations; the first attempt stopped at 87 with GPU out of memory from
outside the job and was rerun with the identical command and seed after a laptop restart). Analysis `analyse_vortex.py` (jackknife,
largest error of bin sizes 1, 5, 10); stored `results/vortex_summary.json`.

| β | R | χ_full | χ_proj | χ_removed | proj/full (crit. 1) | removed/full (crit. 2) |
|---|---|---|---|---|---|---|
| 2.3 | 3 | 0.214 ± 0.002 | 0.145 ± 0.001 | 0.074 ± 0.002 | 0.68: fail | 0.34: fail |
| 2.3 | 4 | 0.184 ± 0.014 | 0.149 ± 0.002 | 0.013 ± 0.008 | 0.81: pass | 0.07: pass |
| 2.4 | 3 | 0.150 ± 0.001 | 0.082 ± 0.000 | 0.101 ± 0.001 | 0.55: fail | 0.67: fail |
| 2.4 | 4 | 0.110 ± 0.003 | 0.085 ± 0.001 | 0.041 ± 0.004 | 0.78: pass | 0.37: fail |

Control (criterion 3): projected loops without gauge fixing are about 600 times smaller than with it, but at this precision not zero
within 2 errors (max |W|/error 4.2 and 12.1): fail.

**Verdict: fail** at both β (criteria 1 and 2 at R = 3, criterion 2 at R = 4 for β = 2.4, criterion 3 at both).

Diagnosis, beside the verdict and not changing it: (i) at R = 3 the full Creutz ratio still carries short-distance terms (it falls with R
while the projected one is flat), so comparing at R = 3 was a poor design (follow-up in `PREREG-VORTEX-SIGMA.md`); (ii) the control
criterion was too strict for this statistical precision; (iii) the projected string tension depends on how well the maximal centre gauge is
fixed: plain iterative maximisation finds local maxima (Gribov copies), and with better maximisation (simulated annealing) the literature
finds the projected string tension falling to about two thirds of the physical one (Bornyakov, Komarov, Polikarpov, hep-lat/0009035;
hep-lat/0103030). Our projected values lie 20-30 % *above* the measured string tension, so this result depends on the gauge-fixing
procedure and cannot settle centre dominance either way. Not pre-registered, reported only: the vortex density in physical units,
density / σa², is 0.77 and 0.91 at β = 2.3 and 2.4, roughly constant, as expected for vortices that are physical objects.
