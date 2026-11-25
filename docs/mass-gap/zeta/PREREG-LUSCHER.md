# Pre-registration: ζ(−1) in the flux tube (2026-11-21, before any run)

**Why (an exploration, not a test of DMP).** `helicity.py` shows that the screening part of the strong force's one-loop coefficient is
ζ(−1) = −1/12 per spin state (11/3 = 4·(1 + ζ(−1)) for the gluon field). The same ζ(−1) is expected in the energy of a confining flux
tube: a closed tube of length L around a periodic box vibrates in d − 2 transverse directions, and the zero-point sum of its modes,
regularised, is (d − 2)·(2π/L)·ζ(−1). In d = 4 its energy is

  E(L) = σL − π/(3L) + O(1/L³),   the coefficient π/3 = −4π·ζ(−1)

(the Luescher term for a closed string; Nambu–Goto resums it as σL·√(1 − 2π/(3σL²))). Measuring the coefficient with this project's code
is a measurement of ζ(−1) in an IM flux tube. Known physics (Luescher 1981; lattice confirmations by Luescher and Weisz 2002, Athenodorou
and Teper): this reproduces, it does not discover.

**Runs** (`run_su2_gpu.py`, after the TTL and vortex queue): SU(2), β = 2.3, boxes L³ × 16 for L = 6, 8, 10, 12, 14 (even only: the checkerboard update needs an even
number of sites per side); 10 chains × 2000
measurements each; smearing levels 2, 6, 12, 20; 500 thermalisation sweeps.

**Analysis** (`luscher.py`, fixed with this file): torelon mass at each L from `analyse_plateau.py` (variational, first plateau); a
weighted fit E(L) = σL − c/L with σ and c free, over every L with a plateau.

**Criteria.** **Pass** if c agrees with π/3 = 1.047 within 2 errors and the fit has p > 0.05 (equivalently, ζ(−1) measured as −c/(4π)
agrees with −1/12). **Tension** between 2 and 3 errors. **Fail** beyond 3 errors. Reported alongside, not part of the verdict: the
Nambu–Goto form with σ the only free parameter, and σ against Teper's a√σ = 0.3687 at β = 2.3. If the small boxes (L√σ ≈ 2.2 at L = 6)
show corrections beyond 1/L, that is reported, and the fit restricted to L ≥ 8 is shown next to it without replacing it.

## Result (2026-11-21, after all five runs; nothing above changed)

Runs: L = 8, 10, 12 completed in the first queue; L = 6 and 14 failed on GPU out of memory (cause outside these jobs) and were rerun with
identical commands and seeds after a laptop restart. All five: β = 2.3, L³ × 16, 10 chains × 2000 measurements.

**1. The pre-registered code (`luscher.py`) as written: inconclusive.** It finds plateaus only at L = 6 and 10: two points, two
parameters, no p-value, so the criteria cannot be applied. Cause found after the run: `luscher.py` takes the torelon mass from
`analyse_plateau.analyse`, which reports it only when the **glueball** channel also has a plateau. The text above asks only for the torelon
("torelon mass at each L ... first plateau"); in these small boxes the glueball is noisy, which dropped L = 8 (torelon plateau at t = 2).

**2. The analysis the text specifies (`luscher_torelon_only.py`, a code fix written after seeing the data; labelled post hoc).**
Torelon plateaus at L = 6, 8, 10 (E = 0.5986 ± 0.0046, 0.980 ± 0.031, 1.223 ± 0.025); none at L = 12, 14 (the signal is gone by t = 2).
Fit E(L) = σL − c/L: σ = 0.1376 ± 0.0036 (a√σ = 0.371, Teper 0.3687), **c = 1.36 ± 0.14 against π/3 = 1.047: 2.3 errors, p = 0.085:
tension** by the criteria above (ζ(−1) measured as −c/(4π) = −0.108 ± 0.011 against −1/12 = −0.0833). Reported alongside: the Nambu–Goto
form with σ only fits well (σ = 0.1333 ± 0.0007, a√σ = 0.365, χ² = 3.1 for 2 dof, p = 0.21). The fit restricted to L ≥ 8 has two points and
is not shown. Stored: `results/luscher_summary.json`.

Reading: the flux-tube energies are consistent with a string (the Nambu–Goto form, which contains the π/(3L) term, fits); the free
coefficient is 2.3 errors above π/3 with three box sizes, the smallest at L√σ ≈ 2.2 where higher corrections are expected. Lattice work
with larger boxes and more statistics confirms π/3 (Luescher and Weisz 2002); this run is too small to add to that.

**Classification (the owner, 2026-11-21).** A measurement limit, not a statement about theory: three usable box sizes, the smallest at
L√σ ≈ 2.2 where the O(1/L³) corrections pull the free coefficient upward, plus a code defect in the analysis. The run shows that this
project's tooling is consistent with the established results (string tension against Teper, the Nambu–Goto form); it was an exploration,
not a test of DMP. Settling π/3 needs larger boxes and more statistics, which the literature has done.
