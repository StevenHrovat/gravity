# Pre-registration: does a box forget its boundary at one physical scale? (Leg B, 2026-11-21)

**Status: pre-registered 2026-11-21 (reviewed by the coordinating session, to which the owner delegated the prioritisation), before
any production run.** Three changes made after the small feasibility runs and before production are marked where they occur (the
photon-test wording, the gate at ℓ = 12, the second box size); no production data existed when they were made. Review decisions:
(1) the photon gate stays at ℓ = 12 with the confined control at β = 0.9; U(1) β = 0.8 at ℓ = 12 is added to phase 1 as a reported
extra, not as an alternative way to pass the gate; (2) the phase-2 GPU budget of about 7.5 h is accepted; (3) Q3 stays exploratory;
(4) two physical box sizes as planned; (5) the typical BC is cut from a periodic lattice only slightly larger than the box (ℓ + 2 or
ℓ + 3): its boundary is less independent of its own periodic images than an ideal typical BC; reported as a caveat.

**Why.** The Bridge (README §4.C, `../weak-coupling/PREP.md` routes 1 and 6) needs a contraction at one physical scale L₀ that holds as
the lattice is refined. `../weak-coupling/BLUEPRINT-REDUCTION.md` turns this into one hypothesis on one box, GDS: the summed influence of
the shell links on the box, Σ_{y∈∂V} k_V(y), is at most γ|V| with γ < 1, measured with relatively gauge-invariant Lipschitz observables;
`../weak-coupling/PROOF-NOTE.md` proves the reduction (Theorem A) and corrects the blueprint. This instrument measures, numerically and
non-rigorously, (a) how far into a box of fixed physical size a boundary condition reaches, as the grid is refined, and (b) upper
estimates of k_V(y) itself. The earlier wall probe (`../dobrushin/README.md`, shot 2) was inconclusive because it failed the photon
test: it read local energy, which couples to photon pairs. This instrument reads flux, and the photon test is built in as a gate.

## The instrument (`boundary.py`, `analyse_boundary.py`)

- **Box.** Sites {0..ℓ}⁴; all links that lie in a face of the box are frozen (the boundary condition, BC); all other links of the box
  are dynamic. The dynamic links are exactly the links with at least one end in the interior cube {1..ℓ−1}⁴: the **thick cube** V⁺ of
  PROOF-NOTE §3.8 (side ℓ−2 in its convention), so there are **no dangling shell links** and the pure-gauge surface term of PROOF-NOTE
  §3.6 (C3) is absent. |V| = 4ℓ(ℓ−1)³; the shell ∂V is the set of face links. The box is embedded in a periodic lattice of even side N
  (ℓ+2 or ℓ+3) so that the GPU checkerboard kernels (`gpu/gauge.py`, unchanged) can be used; frozen links are restored after every
  checkerboard pass, which is exact (a pass never reads the links it writes).
- **BCs.** calm (all 1); typical (cut from an equilibrium periodic configuration at the same β, one per chain); hot (Haar random);
  flux (the face links of a uniform abelian field in the (x, y) plane with flux Φ through every cross-section: SU(2) exp(iAσ₃) with
  Φ = π, whose cross-section holonomy is the centre element −1; U(1) Φ = 2π and Φ = π/2); twist (the same flux on a k×k patch at the
  centre of the z and t faces: SU(2) k = 1, one thin centre vortex threading the box; U(1) k = 2; Z₂ k = 1).
- **Observables** (all invariant under gauge transformations of the interior sites; self-tested to 10⁻¹⁵):
  - plaquettes by depth d (distance of the plaquette's nearest corner from the boundary), per plane, and the admissibility counts
    (shortfall 1 − ½ tr U_p, U(1) 1 − cos θ_p, above ε = 0.5, 1, 1.5);
  - centred R×R Wilson loops in the flux plane at every slice (z, t), R = 1..ℓ, by slice depth, unsmeared and APE-smeared in the plane
    (dynamic links only, α = 0.5); the same loops in the (z, t) plane as a control;
  - straight lines across the box from face to face (relatively invariant: their ends are boundary sites);
  - U(1): sin θ_p of the flux plane by depth (the field itself, odd in the flux).
- **Coupled chains** (`boundary.py couple`, BLUEPRINT §5.1). Pairs of chains whose BCs differ only at one shell link y (SU(2):
  y → y·exp(iθσ₃), U(1): y + θ, θ = 0.5; Z₂: flipped), with shared random numbers. The coupled sweep is a pure heat bath drawn by inverse
  CDF (one uniform per link: exact, and continuous in the staple), followed by a relative Landau alignment of the odd chain to the even
  one on the running state. Recorded: k̂(y) = Σ_e ρ(U_e, U′_e)/ρ(τ_y, τ′_y) over the dynamic links after alignment (ρ the bi-invariant
  distance), an upper estimate of k^W_V(y) for the coupling used, and paired differences of the observables above (lower bounds).
  Why these choices: with rejection samplers (Kennedy–Pendleton, Best–Fisher) a pair desynchronises at every unequal accept/reject;
  overrelaxation is an isometry and never forgets a difference; and the shared-random-number update is not gauge covariant in SU(2),
  so without the running re-alignment the pair's relative gauge drifts and turns into physical differences. Each of the three made
  the estimate vacuous in tests (below).

**Self-tests** (`python boundary.py selftest [--gpu]`, all pass on CPU and on the GPU, 2026-11-21): staples identical to `su2.py`,
`u1.py`; frozen links bit-for-bit unchanged and dynamic links moving (SU(2), U(1), Z₂; CPU and GPU; hot, twist, flux BCs); heat bath
exact for one dynamic link in a frozen random environment (KS test against the exact density: SU(2) at βk = 0.15 and 3.5, U(1) at
βk = 0.76 and 3.0, both samplers including the inverse CDF; Z₂ exact probabilities); overrelaxation keeps the local action to 10⁻¹⁵;
gauge invariance of every observable under a random interior gauge transformation to 3·10⁻¹⁵ (SU(2), U(1), Z₂; ℓ = 5, 6; smeared loops
included); prefix-product loops equal direct products; the cross-section holonomy of each BC (+1, −1, +1 as constructed); paired chains
stay bit-for-bit identical from identical starts; the alignment recovers a random gauge copy (SU(2), U(1): summed distance 9·10³ →
10⁻⁹); GPU quaternion/matrix conversion exact and plaquette equal to the kernel's to 2·10⁻¹⁵; box centre with typical BC agrees with the
periodic plaquette at β = 2.3 (indicative).

## Runs (`queue_boundary.ps1`, waits for "AFTER RESTART DONE" in `runs-gpu/queue.log`)

Phase 1, controls on the CPU (8 in parallel, GPU free), all with 4 chains, 300 thermalisation sweeps, 2 sweeps (1 heat bath + 3
overrelaxation) between measurements, loops smeared 4 steps:

| group | β | ℓ | BCs | measurements | role |
|---|---|---|---|---|---|
| U(1) | 1.1 (Coulomb), 0.9 (confined) | 6, 8, 12 | calm, flux Φ = 2π, flux Φ = π/2 | 1500, 1200, 800 | photon test (gate) |
| U(1) | 0.8 (confined, further from β_c) | 12 | calm, flux Φ = 2π, flux Φ = π/2 | 800 | reported only (review addition) |
| Z₂ | 0.6 (deconfined, gapped), 0.3 (confined) | 6, 8, 12 | calm, twist | 1000 | Ising-gauge test (reported, not a gate) |
| U(1), Z₂ coupled | as above | 4, 6, 8, 10 | calm (U(1)), twist (Z₂); y = face centre; 4 pairs, pure heat bath | 300 | R(ℓ) for the controls |

Estimated wall time of phase 1: about 3 to 4 hours (from the feasibility runs: U(1) ℓ = 12 about 2.3 s per sweep with 10 jobs sharing
the CPU). Then the **photon gate**: `analyse_boundary.py --photon-gate`; if criterion P fails at any ℓ, the queue stops before any SU(2)
run.

Phase 2, SU(2) on the GPU, boxes of fixed physical size ℓ·a√σ ≈ 2.8 (a√σ from `../results/ttl_summary.json`), 500 thermalisation
sweeps, loops smeared 8 steps:

| β | a√σ | ℓ | ℓ·a√σ | lattice N⁴ | chains × measurements | BCs | est. GPU minutes |
|---|---|---|---|---|---|---|---|
| 2.3 | 0.350 | 8 | 2.80 | 10⁴ | 16 × 1000 | calm, typical, twist, flux, hot | 25 |
| 2.4 | 0.258 | 11 | 2.84 | 14⁴ | 8 × 1000 | calm, typical, twist, flux | 32 |
| 2.5 | 0.182 | 15 | 2.73 | 18⁴ | 8 × 1000 | calm, typical, twist, flux, hot | 95 |
| 2.6 | 0.140 | 20 | 2.79 | 22⁴ | 4 × 800 | calm, typical, twist, flux | 73 |
| 2.7 | 0.106 | 26 | 2.75 | 28⁴ | 4 × 600 | calm, typical, twist, flux | 145 |
| 2.3 | 0.350 | 12 | 4.20 | 14⁴ | 8 × 1000 | calm, twist, flux | 24 |
| 2.4 | 0.258 | 16 | 4.13 | 18⁴ | 8 × 1000 | calm, twist, flux | 57 |

The last two rows are a second physical size: the feasibility runs showed the twist still seen deep inside the box at ℓ·a√σ = 2.8
(see below), so the box-size dependence of Q2 needs a larger box.

Phase 3, coupled chains for SU(2), β = 2.3 at ℓ = 4, 6, 8 and β = 2.5 at ℓ = 6, 8, 10, calm BC, y = face centre, 4 pairs, 200 + 300
sweeps, **on the CPU** (6 at a time, alongside phase 2): the coupled path is launch-bound array code, about 4 s per sweep on the GPU in a
tiny test, no faster than one core.

**GPU time, total: about 7.5 h for phase 2, ±50 %** (phase 3 uses no GPU). Basis: the heat-bath kernel costs about 0.35 µs per site
and sweep (`gpu/README.md`: 124 ms per measurement of 2 sweeps on 20⁴ with 10 chains), plus the measurement (launch-bound, about 0.15 s
at 10⁴ up to about 1.2 s at 28⁴ with 4 chains). The frozen-link restores cost under 5 %. Tiny GPU benchmarks today ran while the
production queue held the GPU at 80 to 99 %, so they are upper bounds. Peak GPU memory: about 2 to 3 GB (β = 2.7, 4 chains of 28⁴).
Cheapest cuts if needed: drop 'flux' at β = 2.4 and 2.6 (−25 min), 'hot' everywhere (−24 min), or β = 2.7 to 400 measurements (−45 min).

## Analysis, fixed in advance (`analyse_boundary.py`, its docstring is the reference)

- Errors: blocked standard errors, at least 20 blocks per run, blocks inside chains; different BCs are independent runs.
- **Δ_P(d)** = plaquette(bc) − plaquette(calm) at depth d, flux plane and the other five planes separately.
- **Decay length** ξ: weighted exponential fit of |Δ_P(d)| over the tail window: from d₀ = max(1, ⌈0.3/(a√σ)⌉) (skipping the first
  0.3/√σ, where lattice artefacts set the shape; the wall probe's 0.5-site decay lengths came from there) over the consecutive points
  with |Δ| > 3σ and one sign, at least 2 points; physical ξ√σ = ξ·a√σ, its error including that of a√σ. Also reported: the window d ≥ 1
  and the step-wise ξ_eff(d).
- **Flux deficit** D(R, d₂) = 1 − W_bc/W_calm of the centred smeared loops; D_deep(R) with W averaged over slice depths d₂ ≥ ⌈ℓ/4⌉;
  R_ph = ⌊ℓ/2⌋. Predictions: free field D_C = 1 − cos(ΦR²/ℓ²); random vortices with the string tension D_V (formula in the script).
- **Flux witness** (U(1)): F̄ = mean sin θ_p over the flux-plane plaquettes of the inner half-box (depth ≥ ℓ/4), flux minus calm,
  divided by its free-field value sin(Φ/ℓ²)·⟨cos θ_p⟩. Evaluated at Φ = π/2 (PROOF-NOTE C9: at Φ = π the two interior sectors ±π are
  degenerate on the torus and the odd witness is blind; in this box the faces pin the flux, but π/2 removes the question).
- **Coupled chains**: k̂(y) averaged over the measurements after the first third; R_face(ℓ) = |∂V|·k̂(face)/|V| (every shell link given
  the face-centre value: an upper-side proxy of Σ_y k(y)/|V|).
- **Typical-vs-typical spread** σ_b(d): the boundary-induced spread of the per-chain means (each chain has its own equilibrium boundary).
- **Admissibility** (route 6b): the fraction of plaquettes with shortfall above ε, on the periodic stage of each typical run (bulk),
  and at the box centre for every BC.

## Criteria and questions

**P. Photon test (control, gate).** At ℓ = 12 (the gate), with U(1) flux BCs against calm:
1. Coulomb (β = 1.1): D_deep(R_ph) ≥ 0.5·D_C(R_ph) at Φ = 2π, and the flux witness ratio F̄/F̄_free ≥ 0.5 at Φ = π/2;
2. Coulomb: no decay into the box, D(R_ph, d₂ max)/D(R_ph, 1) ≥ 0.5;
3. confined (β = 0.9): F̄/F̄_free ≤ 0.2 or within 2σ of 0;
4. Coulomb and confined F̄/F̄_free differ by more than 3 combined errors.
In the confined phase large loops are unmeasurable (area law: W(6×6) is consistent with 0), so their deficit cannot be judged; it is
reported at the largest R whose calm loop exceeds 5 errors. (Changed after the first feasibility look, before any production run: the
first draft also required the confined loop deficit, which failed on noise, not physics.)
**The instrument passes only if 1–4 hold at ℓ = 12.** If not, the SU(2) results are not evidence about the gap, and the queue stops.
ℓ = 6 and 8 are reported as a trend: β = 0.9 lies close to the transition (β_c ≈ 1.01), its flux screening length is a few lattice
units, and at ℓ = 8 the confined witness still keeps about a fifth of the free-field flux (feasibility below). Expected trend: the
confined ratio falls with ℓ, the Coulomb ratio stays near 1.

**Z. Ising-gauge test (control, reported, not a gate).** Z₂ at β = 0.6 has a gap but does not confine; a criterion of the GDS kind must
fail there (BLUEPRINT §4.2; heuristic, PROOF-NOTE C6). Expectation: with the twist BC, D_deep(R_ph) at β = 0.6 stays large at every ℓ
(the vortex sheet is rigid and pinned, D near 2 for loops around it) and does not decay into the box; at β = 0.3 it is small. Reported
as "behaves as expected" or not; it says whether the instrument separates *confinement* from a mere gap.

**Q1. Is the SU(2) influence decay length constant in physical units across β = 2.3–2.7?** Test: a constant fit to ξ√σ (tail window,
other five planes, typical BC against calm) over the β with a fit has p > 0.05 and every point within 2σ of the constant (the TTL scan's
rule). Expectation: yes, with ξ√σ near 1/(m₀₊₊/√σ) ≈ 0.27 if the slowest mode is the scalar glueball. Fewer than three β with a fit:
"not enough data".

**Q2. Does the twisted boundary's influence stay short-range for SU(2)?** (a) Δ_P^{twist}(d) has a tail fit at every β, with ξ√σ within a
factor 2 of Q1's constant; (b) at the box centre the twist is seen as a randomly placed vortex, not as a spread field:
|D_deep(R_ph) − D_V| < |D_deep(R_ph) − D_C| and D_deep(R_ph) < 0.5·D_C, for twist and for flux. Judged separately for the two physical
sizes. Expectation: at ℓ·a√σ ≈ 2.8, no (the feasibility look at β = 2.3 already shows a plateau ten times D_V); at 4.2, closer to D_V,
because the twist free energy vanishes in a confining theory only once the box is large compared with 1/√σ. If (b) fails at both sizes
and every β, the twist is long-range on every box we can afford, and the instrument cannot show GDS for twisted BCs. Note: the Z₂ flux of the twist is topologically conserved in SU(2) (the cross-section
holonomy is frozen at −1), so loops that enclose a fixed fraction of the cross-section always see it a little; "short range" here
means the vortex prediction D_V, which falls like e^{−σ(ℓ² − 2R²)} in the box size, not zero.

**Q3. Coupled-chain upper estimates (exploratory).** R_face(ℓ) for U(1) at both β, Z₂ at both β and SU(2) at β = 2.3, 2.5. Expectation
(BLUEPRINT §3.6, §5.3): Coulomb U(1) flat or rising in ℓ, confined theories falling like ξ/ℓ. Stated beforehand: at these ℓ, R_face is
expected to stay above 1 everywhere (it is an upper estimate with a crude coupling), so Q3 reports only the trend in ℓ and its sign,
not GDS.

**A. Admissibility (route 6b).** Per β and ε, the bulk fraction with errors. Expectation: it falls steeply as β grows (ε = 1.5 at most a
few 10⁻⁵ at β ≥ 2.3). This measures what a *soft* admissibility weight (PROOF-NOTE §9, C8) would cost; a hard cut makes k infinite
across topological sectors and is not what is measured here.

**What none of this can show.** The supremum over all BCs (only the listed classes); GDS^∂ for truncated blocks near the boundary of a
larger box (PROOF-NOTE C2: only the full thick cube is measured, which is what the torus version needs); anything rigorous.

## Feasibility (2026-11-21, small CPU runs; indications only, not part of the pre-registration)

CPU only, 4 chains, 10 to 17 jobs sharing the CPU; many runs were analysed from checkpoints (number of measurements given). Raw files:
`runs/boundary-feas/` (gitignored). These numbers informed the design changes marked above; they are not results.

**Photon test.** U(1), ℓ = 12, Φ = 2π, 600 measurements (complete): Coulomb (β = 1.1) loop deficit D_deep(R = 6) = 1.025 ± 0.020 against
the free-field value 1.000; the whole curve D_deep(R), R = 1..11, follows 1 − cos(ΦR²/ℓ²) within errors; the profile in depth is flat
(last/first 1.02); odd witness F̄/F̄_free = 0.94 ± 0.02. Confined (β = 0.9): F̄/F̄_free = −0.01 ± 0.03 (screened); loops of side 4 and more
are consistent with zero (area law). Criterion P as now worded: **pass**. ℓ = 8, Φ = π/2, 800 flux and 500 to 700 calm
measurements: Coulomb F̄/F̄_free = 0.93 ± 0.05, D_deep(R) again on the free-field curve; confined 0.22 ± 0.07, partly screened (hence the
gate at ℓ = 12). In this box the faces pin the non-compact flux, so even Φ = 2π stays in its sector in the Coulomb phase; Φ = π/2 is kept
anyway (PROOF-NOTE C9).

**Ising-gauge test.** Z₂, ℓ = 8, twist BC, 400 measurements. β = 0.6 (gapped, deconfined): every centred loop sees the pinned vortex
sheet, D_deep(R) = 1.89 to 2.00 at all R and the same at every depth; the plaquette deficit grows towards the centre (−0.035, −0.089,
−0.48 by depth), so no decay length exists: the instrument reports long range, as a criterion of the GDS kind must for this theory.
β = 0.3 (confined): plaquette differences within 2σ of zero, loops beyond R = 1 unmeasurable (area law).

**SU(2), β = 2.3, ℓ = 8 (ℓ·a√σ = 2.8)**, 300 measurements (typical 200):
- typical against calm: Δ_P(d) = −0.100, −0.036, −0.013, −0.010 (d = 0..3); tail fit ξ = 1.04 ± 0.04 lattice units, **ξ√σ = 0.365 ± 0.015**
  (compare 1/(m₀₊₊/√σ) ≈ 0.27–0.29); the boundary-to-boundary spread of typical BCs falls from 1.1·10⁻³ to 3.6·10⁻⁴ by d = 2.
- flux (smooth, Φ = π): no significant local energy change; D_deep(R = 4) = 0.19 ± 0.01, between the free-field value 0.29 and the
  random-vortex value 0.04, and the profile in depth falls only slowly (0.23, 0.20, 0.16, 0.30 ± 0.05).
- twist (thin, Φ = π): the loop around the pinned entry point sees −1 at the face (D = 2), relaxes within two slices (0.88, 0.50) and
  then stays at a plateau D ≈ 0.36–0.39, ten times the random-vortex value; the flux-plane plaquette deficit is about −0.006 at every
  depth (the vortex sheet costs action through the whole box). **At this box size the twist is not short-range** in the sense of Q2(b);
  this is why a second physical size (ℓ·a√σ ≈ 4.2) is in the plan. Whether it becomes short-range in larger boxes is the question.
- admissibility on the periodic stage (bulk, β = 2.3): fraction of plaquettes with shortfall above ε = 0.5, 1, 1.5: 0.295, 0.051,
  0.0053 (errors below 3·10⁻⁴). Not small at this β; the β dependence is what production measures.

**Coupled chains** (k̂ for y = face centre, calm BC, θ = 0.5; ℓ = 4 and 6; R_face = |∂V|k̂/|V|):

| theory | β | k̂ (ℓ = 4) | k̂ (ℓ = 6) | R_face (4, 6) | reading |
|---|---|---|---|---|---|
| U(1) Coulomb | 1.1 | 1.63 ± 0.05 | 3.06 ± 0.15 | 3.3, 3.7 | k̂ grows about like ℓ, R flat: as BLUEPRINT §3.6 predicts for the photon |
| U(1) confined | 0.9 | 3.6 ± 0.8 | 457 ± 29 | 7, 548 | vacuous at ℓ = 6: the pair decorrelates |
| SU(2) | 2.3 | 3.33 ± 0.08 | 7.8 ± 0.3 | 6.7, 9.4 | stationary, independent of θ (0.05 gives the same); rising with ℓ at these sizes |
| Z₂ | 0.6, twist | | 0.01 | 0.02 | one flip is absorbed; the worst case needs a "pivot" BC (BLUEPRINT §4.2) |
| Z₂ | 0.3, twist | | 663 ± 2 | 795 | vacuous: the pair decorrelates |

Reading: the synchronous coupling is informative where the dynamics is close to Gaussian (Coulomb U(1), SU(2) at β = 2.3 in small
boxes) and **vacuous in rough, confining regimes**, exactly where GDS should hold. As an upper estimate it cannot confirm GDS anywhere we
tested; Q3 is therefore marked exploratory, and a better coupling is an open design question. Getting here required three fixes, each
found by a failing trial: rejection samplers desynchronise the pair (SU(2) k̂ ≈ 3200 at ℓ = 6); overrelaxation never forgets a
difference (k̂ ≈ 490 at ℓ = 4); without running re-alignment the SU(2) pair's relative gauge drifts (k̂ growing without limit).

## Change of run order (2026-11-21, 16:48, before any SU(2) data existed)

By the owner's decision the SU(2) GPU phase was started before the photon gate, in parallel with the CPU controls, to save about 3
hours (`queue_boundary.ps1` split into `queue_boundary_cpu.ps1` (controls, then the gate) and `queue_boundary_gpu.ps1` (SU(2) and the SU(2)
coupled chains, then the final analysis after the gate); identical commands and seeds; control jobs already started kept running). The gate's
role is unchanged: if it fails, the SU(2) results are not used as evidence about the gap.

## Second change of run order (2026-11-21, 19:41, before any of the reordered runs had data)

By the owner's decision (long runs saved for low load): the remaining SU(2) GPU runs reordered (`queue_boundary_gpu2.ps1`): the larger
boxes (ℓ·a√σ ≈ 4.2 at β = 2.3 and 2.4, question Q2) first, then the rest of β = 2.5, then β = 2.6, then β = 2.7 last (overnight). Identical
commands and seeds. The exploratory SU(2) coupled-chain runs on the CPU (Q3) were paused (`cpl_su2_b2.3_l4` and `_l6`, `cpl_su2_b2.5_l6`
completed; the others stopped and not used), to free the CPU for the controls and the photon gate; the attempt round and the curvature
study (`../weak-coupling/H2-CURVATURE.md`) had found that this estimator measures curvature at one configuration only. The run
`su2_b2.5_l15_flux`, already started at the swap, continued; its completion is logged by `watch_orphan_flux25.ps1`.
