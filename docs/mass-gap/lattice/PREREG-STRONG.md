# Pre-registration: where does the proven strong-coupling regime hand over? (2026-11-21, before any run)

**Why.** The Lean theorems in `../formal/` prove confinement (area law) and, in progress, the mass gap (clustering) for SU(2) at strong
coupling, in a window of β far below the physical region. Their mechanism is the leading strong-coupling picture: a disturbance travels
only by tiling plaquettes, each costing a factor u = ⟨½ tr U_p⟩ of a single plaquette. For the scalar glueball the cheapest tube in the time
direction is four plaquettes per time step, so at leading order a·m₀₊₊ = −4 ln u(β), with u(β) = I₂(β)/I₁(β) (standard normalisation
(β/2) Re tr). This scan measures the gap between β = 1.7 and 2.2 and the plaquette, and puts three things side by side: the rigorous
bound (where it exists), the leading strong-coupling value, and the measurement. It locates where the strong-coupling picture stops
describing the data, i.e. the start of the middle range that a proof of the mass gap has to bridge. It is a measurement with stated
expectations, not a test of DMP.

**Runs** (`run_su2_gpu.py`, queued after the Luescher runs by `queue_strong.ps1`): SU(2), lattice 8⁴, β = 1.7, 1.9, 2.1, 2.2; 10 chains ×
3000 measurements, 300 thermalisation sweeps, 3 over-relaxation per heat bath, a measurement every 2 sweeps; smearing levels 0, 1, 2, 4.

**Analysis** (`analyse_plateau.py`, unchanged; and `ttl.py` conventions): glueball effective mass with the plateau rule of
`PREREG-TTL.md`; plaquette with jackknife errors. If the correlator at t = 1 is not significant (relative error above 50 %), the mass is
reported as a lower bound from t = 0 → 1 only, and labelled so.

**Expectations stated before the runs** (reported, no pass/fail verdict): (1) the measured a·m₀₊₊ falls monotonically with β; (2) at
β = 1.7 it lies within 25 % of −4 ln u; (3) the ratio measured / leading falls with β, reaching about 0.5 at β = 2.2 (leading values: 3.85, 3.50, 3.20, 3.07 at β = 1.7, 1.9, 2.1, 2.2) (Teper's β = 2.2 entry
is a·m₀₊₊ = 1.44 against −4 ln u = 3.07); (4) the measured plaquette agrees with the strong-coupling series' leading term u(β) only at the
smallest β, within 5 %. Each expectation is reported as met or not met.

## Result (2026-11-21, after the four runs; nothing above changed)

Runs: first attempt failed on GPU out of memory (10:46-10:52, cause outside these jobs); rerun with identical commands and seeds after a
laptop restart (13:43-13:51). Analysis `analyse_plateau.py` (unchanged); stored `results/strong_summary.json`.

| β | plaquette | u(β) = I₂/I₁ | a·m(t=0→1) | a·m(t=1→2) | −4 ln u | m(0→1) / (−4 ln u) |
|---|---|---|---|---|---|---|
| 1.7 | 0.41363 ± 0.00003 | 0.3816 | 3.21 ± 0.04 | 2.8 ± 0.8 | 3.85 | 0.83 |
| 1.9 | 0.47009 ± 0.00003 | 0.4166 | 2.53 ± 0.03 | 2.5 ± 0.4 | 3.50 | 0.72 |
| 2.1 | 0.53459 ± 0.00004 | 0.4491 | 1.88 ± 0.01 | 1.82 ± 0.08 | 3.20 | 0.59 |
| 2.2 | 0.56923 ± 0.00003 | 0.4645 | 1.53 ± 0.01 | 1.49 ± 0.05 | 3.07 | 0.50 |

**No plateau** by the rule at any β (at β = 1.7 and 1.9 the correlator at t = 1 has 30 and 15 % errors and later times are noise; at
β = 2.1 and 2.2 m(3) drops below m(1) by more than the errors). As fixed above, the masses are reported from t = 0 → 1. **Correction to the
text above:** it calls that value a "lower bound"; it is an **upper bound** (with reflection positivity, effective masses approach the
lightest mass from above). The β = 2.2 value at t = 1 → 2, 1.49 ± 0.05, agrees with Teper's 1.44.

Expectations: (1) a·m falls monotonically with β: **met**. (2) at β = 1.7 within 25 % of −4 ln u: **met** (17 % below). (3) the ratio
falls with β, about 0.5 at β = 2.2: **met** (0.83 → 0.50). (4) the plaquette agrees with u(β) within 5 % only at the smallest β: **not
met**: already at β = 1.7 it is 8 % above u (13, 19, 23 % at the larger β); the leading strong-coupling term describes the plaquette less
well than the gap.

Reading: the leading strong-coupling mechanism (four plaquettes per time step) describes the gap at β = 1.7 to within about 20 % and
loses half of it by β = 2.2, where the TTL scan's region begins. The proven windows (standard β below 0.09 for the area law, far below
for clustering) lie much further out. The hand-over from the strong-coupling picture to the physical region happens between β ≈ 1.7 and
2.2, on this lattice; that interval is the middle range a proof has to bridge.
