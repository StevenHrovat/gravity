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
