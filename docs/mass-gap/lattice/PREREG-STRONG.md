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
