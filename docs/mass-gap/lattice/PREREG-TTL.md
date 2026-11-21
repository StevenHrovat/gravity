# Pre-registration: is the existence TTL the same at every layer? (2026-11-21, before any scan run)

**Why.** Finding MG7 with the owner's existence TTL: a node's existence is a certificate renewed within a bounded reach, so its time to
live (TTL = 1 / mass) is finite and, "at every layer", the same in real units however fine the grid. In physics terms: m₀₊₊/√σ stays
constant as the lattice spacing shrinks (scaling), while the TTL counted in grid ticks grows like 1/(a√σ). Decades of lattice work say it
does (Teper's continuum value m₀₊₊/√σ = 3.74 ± 0.12); this scan checks it with this project's GPU code over a range of grid finenesses
the CPU code could not reach.

**What was learned before this file (thread C addendum, `PREREG.md`).** At β = 2.5 the fixed analysis window t = a → 2a with two
smearing levels is contaminated by heavier states (with ten times the statistics the effective masses keep falling). The scan therefore
uses a larger operator basis and a plateau rule, both fixed here for every β, before any scan data exist.

**Runs** (`run_su2_gpu.py`, smearing levels 2, 6, 12, 20, 32 with α = 0.5: 10 glueball and 5 torelon operators; 500 thermalisation
sweeps; 2 sweeps of 1 heat bath + 3 overrelaxation between measurements; boxes of at least 3.2/√σ):

| β | lattice | chains × measurements |
|---|---|---|
| 2.3 | 12⁴ | 10 × 1000 |
| 2.4 | 16⁴ | 10 × 1000 |
| 2.5 | 20⁴ | 10 × 1000 |
| 2.6 | 28⁴ | 4 × 800 |
| 2.7 | 32⁴ | 4 × 600 |

**Analysis** (`analyse_plateau.py`, unchanged after this commit): variational step at t = 0, 1; effective mass at the first plateau
(m(t) agrees with m(t+1) and m(t+2) within combined errors, relative error at most 25 %); string tension from the torelon by Teper's
eqn 6; jackknife errors over 20 bins (one chain spans whole bins).

**Criteria.**

1. **Same at every layer (the test):** a constant fit to TTL·√σ = 1/(m₀₊₊/√σ) over all β with a plateau has χ²/dof with p > 0.05, and
   every point lies within 2 errors of the fitted constant.
2. **Agreement with the continuum value:** the fitted constant agrees with 1/3.74 = 0.267 ± 0.009 within 2 combined errors.
3. **Ticks grow:** the TTL in grid ticks grows from β = 2.3 to 2.7 by a factor within 2 errors of the ratio of a√σ measured at the two
   ends (Teper: about 3.7).
4. Reported per β, not part of the verdict: a√σ and a·m₀₊₊ against Teper's Table 10 (agree / tension / fail as in `PREREG.md`).

**Verdict.** 1 to 3 hold: **pass**. Any of them fails: **fail**, with the failing β named. A β without a plateau in either channel is
reported as "no plateau" and left out of the fit; if fewer than three β remain, the verdict is "not enough data", not a pass.

## Result (2026-11-21, after all five runs; nothing above changed)

| β | lattice | t* (glueball, torelon) | a√σ (vs Teper) | a·m₀₊₊ (vs Teper) | TTL in ticks | TTL · √σ |
|---|---|---|---|---|---|---|
| 2.3 | 12⁴ | 1, 1 | 0.350 ± 0.006 (tension, 2.9) | 1.20 ± 0.04 (agree) | 0.83 ± 0.03 | 0.291 ± 0.010 |
| 2.4 | 16⁴ | 2, 1 | 0.258 ± 0.003 (tension, 3.0) | 1.01 ± 0.05 (agree) | 0.99 ± 0.04 | 0.256 ± 0.012 |
| 2.5 | 20⁴ | 1, 2 | 0.182 ± 0.002 (agree) | 0.720 ± 0.009 (tension, 2.5) | 1.39 ± 0.02 | 0.253 ± 0.004 |
| 2.6 | 28⁴ | 2, 1 | 0.140 ± 0.002 (tension, 2.1) | 0.52 ± 0.02 (agree) | 1.92 ± 0.08 | 0.268 ± 0.012 |
| 2.7 | 32⁴ | 3, 1 | 0.106 ± 0.002 (agree) | 0.39 ± 0.02 (agree) | 2.54 ± 0.12 | 0.268 ± 0.014 |

1. Same at every layer: constant 0.2603 ± 0.0036, χ²/dof = 12.5/4, p = 0.014; β = 2.3 lies 3.0 errors above: **fail** (at β = 2.3).
2. Against the continuum value 1/3.74 = 0.267 ± 0.009: 0.8 errors: pass.
3. Ticks grow from β = 2.3 to 2.7 by 3.05 ± 0.17 against the a√σ ratio 3.31 ± 0.08: 1.4 errors: pass.

**Verdict: fail**, by criterion 1 at the coarsest grid. Likely cause, stated beside the verdict and not used to change it: scaling
violations at coarse lattice spacing; Teper's own β = 2.3 entry has m₀₊₊/√σ = 3.30 (TTL · √σ = 0.303), also above the continuum value. The
four finer grids (β = 2.4 to 2.7) are mutually consistent, but excluding β = 2.3 after seeing the data would not be a pre-registered result.
Stored: `results/ttl_summary.json`.
