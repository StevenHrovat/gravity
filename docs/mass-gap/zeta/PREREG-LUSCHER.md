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
