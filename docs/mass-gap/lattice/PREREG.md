# Pre-registration: thread C lattice runs (2026-11-21, before any of these runs started)

Written before the runs below were started on the owner's laptop, as HANDOVER §4 asks. The analysis is `analyse.py` as committed at
the time of writing, unchanged: effective mass from t = a to 2a for β ≤ 2.5 and from 2a to 3a above (Teper's choice), jackknife errors
over 20 bins, U(1) energies from the cosh fit at t = a.

## Runs

| run | lattice | measurements | seed |
|---|---|---|---|
| SU(2) β = 2.4 | 14⁴ | 2000 | 24 |
| SU(2) β = 2.5 | 16⁴ | 1500 | 25 |
| SU(2) β = 2.6 | 20⁴ | 1000 | 26 |
| U(1) β = 1.2 (Coulomb phase) | 8³ × 16, 12³ × 24, 16³ × 32 | 1500, 1200, 800 | 31, 32, 35 |
| U(1) β = 0.8 (confined phase) | 8³ × 16, 12³ × 24 | 1500, 1200 | 33, 34 |

## What counts as agreement, tension and failure

**SU(2), against Teper (hep-th/9812187, Table 10).** For a√σ and a·m₀₊₊ at each β, with d the difference to Teper's value divided by
the two errors combined in quadrature: **agree** if d ≤ 2, **tension** if 2 < d ≤ 3 (reported as such, no retuning), **fail** if d > 3
(the code or the analysis is wrong at that β until shown otherwise; the number is not used in README §6). The headline test is the
pattern: a·m₀₊₊ falls with β while m₀₊₊/√σ stays within 2 errors of 3.74 ± 0.12 (Teper Table 1).

| β | Teper a√σ | Teper a·m₀₊₊ |
|---|---|---|
| 2.4 | 0.2686 ± 0.0021 | 0.959 ± 0.020 |
| 2.5 | 0.1834 ± 0.0026 | 0.660 ± 0.022 |
| 2.6 | 0.1326 ± 0.0030 | 0.51 ± 0.03 |

**U(1), the photon test on the lattice.** Observable: the energy E₁ of the lightest state at the smallest momentum 2π/L.

- Coulomb phase (β = 1.2): **pass** if at each of L = 8, 12, 16 E₁ agrees with the free massless value 2·asinh(sin(π/L)) within 2
  errors, and a fit of E₁² = m² + E_free² over the three boxes gives m consistent with 0 within 2 errors. **Fail** if m is more than 3
  errors above 0.
- Confined phase (β = 0.8): **pass** if E₁ stays large: E₁(L = 12) / E₁(L = 8) > 0.85 (a massless particle would give 0.67). If the
  correlator is lost in noise before t = 2a (no cosh solution), that is reported as "E₁ above about 2", which also passes.

Nothing here tests the continuum limit or proves anything; it reproduces published lattice physics with our own code.
