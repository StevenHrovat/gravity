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

## Addendum (2026-11-21, after the β = 2.5 result, before the diagnostic runs)

Result by the rule above: β = 2.3 and 2.4 agree on all numbers; at β = 2.5 a√σ = 0.1990 ± 0.0030 against Teper's 0.1834 ± 0.0026
(3.9 errors): **fail**, so that number is not used in README §6. (This addendum first said the torelon effective mass was flat from
t = a to 3a, so excited states were not the cause; with the diagnostic's statistics that turned out wrong, see the result below.) Diagnostic runs on the GPU (`run_su2_gpu.py`), fixed before running:

1. **Statistics.** β = 2.5, 16⁴, ten independent chains of 1500 measurements (500 thermalisation sweeps each), same analysis. If a√σ
   agrees with Teper within 2 errors, the CPU run's error was underestimated or it fluctuated, and the GPU value is reported next to it.
2. **Box size.** β = 2.5, 20⁴, ten chains of 1000 measurements. If a√σ at 20⁴ is lower than at 16⁴ by more than 2 errors, the 16⁴ box is
   too small for our torelon analysis at this β.

If neither explains it, the cause stays open and is reported as such; the analysis rule is not changed to make the number agree.

**Result of the diagnostics (2026-11-21).** (1) Statistics: 16⁴, 15 000 measurements: a√σ = 0.1936 ± 0.0012 (3.6 errors from Teper),
a·m₀₊₊ = 0.771 ± 0.012 (Teper 0.660 ± 0.022): not explained. (2) Box size: 20⁴, 10 000 measurements: a√σ = 0.1983 ± 0.0015, higher than on
16⁴, not lower: not explained. Both show effective masses that keep falling with t (torelon on 16⁴: 0.534, 0.526, 0.507, 0.478), so the
cause is the analysis window t = a → 2a with two smearing levels, contaminated by heavier states on this finer grid. The verdict stays
**fail** for β = 2.5 under this pre-registration; the corrected method is a separate pre-registration (`PREREG-TTL.md`).
