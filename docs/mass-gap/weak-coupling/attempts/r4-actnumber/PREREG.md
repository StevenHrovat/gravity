# Pre-registration: the act number z(L) = E_e(L)·L of SU(2) in a twisted box (round 4, r4-actnumber, 2026-11-21)

**Status: pre-registered 2026-11-21 by round 4, attempt r4-actnumber, before any GPU run.** Only the CPU self-test, a CPU pipeline test
and a CPU feasibility check of the photon control (tiny lattices, marked as such below) have been run. Runs: `queue_actnumber_gpu.ps1`,
to be started by the coordinating session after Leg C (r3-blocked, main queue and addendum); never by an attempt. Any change after the
first GPU data must be marked as such, as in `../../../lattice/PREREG-BOUNDARY.md`. The coordinator's addition from r4-minting (received
during preparation, before any data) is part of the readings: reading (vi), the collapse test, and the Banks–Zaks point under "What z
measures".

**Why.** The round-4 scout (`../../round4-prep/DMP-SCOUT.md` §2) reads the DMP act identity (existence × extent = one quantum) in
Yang–Mills as the act number of a twisted box, z(L) = E_e(L)·L: the energy of the cheapest state that carries one unit of centre
flux around a periodic box of side L, times L. For the photon it is frozen at 2πα (classical); for SU(2) it should run, cross 1 near the
deconfinement length and grow like σL². No one in this project has measured it. This measurement turns the scout's candidate 1 into
numbers: where z crosses 1 (target T1a, "the act fits its own box", 3s1t), whether it keeps growing by a margin at every doubling (T1b,
the δ of `act_reach`), and, with r4-minting's addition, whether z(2L) is a function of z(L) alone (one flow).

## What z measures, and what it cannot show (claim discipline, `../RULES.md` round 4)

- **What it is.** E_e is the gap of the transfer matrix in the **centre-charged** sector (electric flux e_f = 1) of a finite twisted box,
  above that box's vacuum. It is not the vacuum-sector (glueball) gap. z is a finite-volume, finite-lattice-spacing number; two lattice
  spacings (and a third at the ends) give a scaling check, not a controlled continuum limit.
- **Targets it can inform.** "z crosses 1" (T1a: a tuning step; **weaker** than the mass gap). "z keeps growing, by a margin per
  doubling" (T1b: flux-sector confinement on the measured stretch; **incomparable** with the gap, implied by an area law, not implying a
  vacuum gap). "z(2L) = σ(z(L)) for one σ" (r4-minting's assumption (U) in this scheme; **weaker**, an existence-plus-universality
  statement).
- **What it cannot show.** (1) The sector transfer: a large flux-sector energy does not imply a glueball gap; no reading below says or
  implies anything about the vacuum sector. (2) Anything rigorous: these are Monte Carlo estimates with statistical and systematic
  errors. (3) Anything beyond the measured stretch L√σ ≈ 0.56–3.6: "keeps growing" is a statement about that stretch only.
  (4) Uniqueness of the scheme: z is one coupling among many (the twisted-Polyakov-loop amplitude scheme of de Divitiis et al. is another).
- **Banks–Zaks (from r4-minting, `../r4-minting/NOTE.md` §2.5, §4).** Growth of z in pure SU(2) is **not** implied by asymptotic freedom:
  conformal-window theories (Banks and Zaks 1982; e.g. SU(2) with two adjoint Dirac flavours as a lattice candidate) are asymptotically
  free, conserve their Λ, and are gapless, so their act number would stall at an infrared fixed point. A measured growth is therefore
  evidence about **pure SU(2) specifically** (no matter fields), not a consequence of b₀ > 0 alone.
- **Deconfinement test (RULES round 4).** A box thinner than 1/T_c ≈ 1.41/√σ (T_c/√σ = 0.709, Lucini, Teper and Wenger 2004, recalled) is
  deconfined in the flux direction. The expectation is z < 1 there; the readings never claim z ≥ 1 at a prescribed small L.

## The instrument (`actnumber.py`, `analyse_actnumber.py`; self-test and pipeline test below)

- **Lattice and action.** L³ × T sites, periodic, Wilson action S = −β Σ_p c_p ½tr U_p. **'t Hooft twist** ('t Hooft 1979) in the spatial
  plane (a, b): the plaquettes P_ab at (x_a, x_b) = (L−1, L−1), for every (x_f, t), have c_p = −1 (all others +1). This is the lattice
  form used by García Pérez, González-Arroyo and Martínez (Phys. Lett. B 305 (1993) 366, hep-lat/9302007; González-Arroyo and Martínez,
  Nucl. Phys. B 459 (1996) 337, hep-lat/9507001, read: "flipping the sign of ... plaquettes sitting at the corner"). Primary plane
  (a, b) = (x, y), flux direction f = z. The twist is purely spatial, so time reflection keeps reflection positivity and the transfer
  matrix (r3-monotone B1) applies: E_e is a true energy.
- **Sector.** Electric flux e_f = 1 **parallel** to the magnetic twist m_f, so e × m = 0: no fractional momentum (in the m = (1,1,1) box of
  González-Arroyo and Martínez the sectors with e × m ≠ 0 carry momentum π√2/L, which is why they read the |e|² = 3 sector for the
  tunnelling physics; here e ∥ m by construction). The classical vacua are the two twist eaters with P_f = ±1 (`su2_twist_eater`,
  r3-monotone §4.1); the e_f = 1 state is their odd combination, split by tunnelling through Q = ½ fractional instantons at small L
  (hep-lat/9302007, read via its HTML version: dilute-gas fits at L√σ ≈ 0.76–1.14) and by a flux string at large L.
- **Observable.** p_k(t) = L⁻² Σ_{x_a,x_b} ½tr Π_{x_f} V^(k)_f(x, t), the Polyakov loop along f summed over the transverse plane (zero
  transverse momentum), V^(k) the f-links after k smearing steps with the four transverse staples of the planes (f, a) and (f, b) only
  (APE weight α = 0.5, projection to SU(2); Albanese et al. 1987, credited). These planes contain no twisted plaquette, so the operator
  needs no sign and is gauge invariant (self-test). Levels: L ≤ 6: k ∈ {0, 2, 6}; medium: {0, 3, 8, 16}; L ≥ 12 (β ≥ 2.4) or L = 10 at β
  2.3: {0, 4, 12, 24}. Second operator: s(t) = sign p_top(t) (the sign-flip count of hep-lat/9302007 in correlator form).
- **Estimator (why this one).** Under the centre transformation along f, p → −p, so ⟨p⟩ = 0 exactly; the correlator is used **without**
  vacuum subtraction (subtracting a sample mean would turn slow Monte Carlo tunnelling into a fake signal). Its spectral decomposition in
  periodic time with the e = 0 vacuum and the e = 1 ground state is A cosh(E(T/2 − t)) + excited states, valid for every E·T, which
  covers the small-L regime where E·T is of order 1. Effective masses solve c(t)/c(t+1) = cosh(E(T/2−t))/cosh(E(T/2−t−1)) (our
  `analyse.cosh_mass`), after a variational step over the smearing levels (generalised eigenvalues at t = 0, 1; our
  `analyse.best_projection`). **U(1) only:** the flux sectors form a tower E_n = n²·e²/(2L) (the photon's zero mode is a free quantum
  rotor, classical electrostatics), so a two-state cosh is biased when E·T is of order one; the U(1) effective masses solve the same
  ratio for the exact rotor correlator Σ_n exp(−E₁[n²(T−t) + (n+1)²t]) (`rotor_mass`), which reduces to the cosh form for E₁T ≫ 1.
  SU(2), Z₂ and 2I have a Z₂ centre: two flux sectors, the cosh form is the exact low-energy form. Alternatives considered and not chosen: (a) the twisted/periodic partition-function ratio with a temporal
  twist ('t Hooft's electric flux free energy, de Forcrand and von Smekal, Phys. Rev. D 66 (2002) 011504, hep-lat/0107018, abstract
  read): it needs a 20-node coupling integration or a snake algorithm per point, an order of magnitude more GPU time, and gives the free
  energy at one T, not the energy; (b) the twisted-Polyakov-loop scheme (de Divitiis, Frezzotti, Guagnelli, Petronzio, hep-lat/9312085,
  Nucl. Phys. B 422 (1994) 382, abstract read): a coupling from a correlator **amplitude** at fixed separation, ∝ g² at tree level, not
  an energy, so it is not existence × extent. Both are fine running couplings; only the energy matches the act identity term by term.
- **Updates.** SU(2): Kennedy–Pendleton heat bath + 3 overrelaxation steps per sweep, checkerboard per direction. GPU production uses the
  fused kernels of `../../../lattice/gpu/gauge.py` (imported, unchanged; they know no twist) plus an **exact sheet fix-up**: after every
  checkerboard pass of a twist-plane direction, the only links whose staple contains a twisted plaquette (4·L·T per configuration) are
  re-updated with the correct staple (heat bath: a fresh draw, which does not depend on the old value; overrelaxation: reflection of the
  value saved before the pass). Exact because a pass never reads the links it writes. Fallback: the same algorithm in array code
  (cupy). U(1): von Mises heat bath + overrelaxation (`boundary.vonmises`); Z₂: heat bath; 2I: Metropolis, 4 hits per link and pass,
  proposals r·U with r one of the 12 elements next to 1, then a snap to the group (roundoff only). Starts per chain (i mod 4): twist eater
  P_f = +1, twist eater P_f = −1, hot, hot (U(1), Z₂: cold, hot).
- **Errors.** Jackknife over bins inside chains (chains × k bins, at least 20 in all). For readings that combine points, Gaussian
  sampling of the point errors; the a√σ error is common to one β.
- **Lattice spacing.** a√σ from our TTL scan (`../../../results/ttl_summary.json`): β 2.3: 0.3503(61); 2.4: 0.2579(29); 2.5: 0.1822(22);
  2.6: 0.1396(16); 2.7: 0.1057(18). z itself needs no lattice spacing; only the L axis does.

## Runs (`queue_actnumber_gpu.ps1` = `actnumber.PLAN`, in this order)

Sweeps = 1 heat bath + 3 overrelaxation. "meas" per chain; "every" sweeps between measurements.

| # | run | β | L | T | L√σ | chains × meas, every | therm | role |
|---|---|---|---|---|---|---|---|---|
| 0 | `selftest --gpu`, `bench` | | | | | | | gate: fused path = array path (overrelaxation to 10⁻¹⁰), sheet = bulk; timings |
| 1–4 | U(1) | 1.1 | 4, 6, 8, 10 | 32, 32, 48, 48 | — | 4 × 500, 4 | 300 | **photon gate** |
| 5–10 | SU(2) | 2.4 | 4, 6, 8, 10, 12, 14 | 96, 64, 48, 32, 32, 32 | 1.03, 1.55, 2.06, 2.58, 3.10, 3.61 | 8 × 500 (L ≤ 8), 4 × 1000 (10), 4 × 800 | 1000 | coarse spacing |
| 11–17 | SU(2) | 2.5 | 4, 6, 8, 10, 12, 14, 16 | 128, 96, 64, 48, 32, 32, 32 | 0.73, 1.09, 1.46, 1.82, 2.19, 2.55, 2.92 | 8 × 500 (L ≤ 8), 4 × 1000 (10), 4 × 800 | 1500 (L 4), 1000 | fine spacing |
| 18 | SU(2), twist in yz, flux along x | 2.4 | 6 | 64 | 1.55 | 8 × 500, 8 | 1000 | symmetry control |
| 19–21 | Z₂ | 0.5 | 2, 4, 6 | 32 | — | 8, 8, 4 × 500, 4 | 300 | deconfined control |
| 22–24 | 2I | 8.0 | 2, 4, 6 | 32 | — | 8, 8, 4 × 500, 4 | 300 | frozen finite-subgroup control |
| 25–29 | SU(2) | 2.6; 2.7 | 4, 6, 8, 12; 6 | 128, 128, 96, 48; 128 | 0.56, 0.84, 1.12, 1.68; 0.63 | 8 × 500 (L 4, 6; 2.7), 4 × 750 (8), 4 × 800 (12) | 1500, 1000 | small-L end, third doubling curve |
| 30–33 | SU(2) | 2.3 | 4, 6, 8, 10 | 64, 32, 32, 32 | 1.40, 2.10, 2.80, 3.50 | 8 × 500, 8 × 500, 4 × 1000, 4 × 800 | 1000 | reported: large end at a second spacing |
| 34–35 | U(1) | 1.3 | 4, 8 | 32, 48 | — | 4 × 500, 4 | 300 | reported: collapse control at a second u |
| 36–37 | SU(2), periodic (no twist) | 2.5 | 6, 12 | 64, 32 | 1.09, 2.19 | 8 × 500, 4 × 500 | 1000 | reported: does the twist matter? |
| 38 | 2I | 2.4 | 6 | 32 | (1.55) | 4 × 300, 4 | 500 | reported: 2I below its freezing mimics SU(2) |

Time extents: chosen so that the expected E·T is at least about 3 (small L: z ≈ 0.1–0.5 expected) and T ≥ 2L at large L.
Exact arguments and seeds: `actnumber.PLAN`.

**GPU time: about 4.8 h (±50 %), the core runs 1–29 about 4.2 h.** Basis: the fused heat-bath kernel at 0.45 µs per site and sweep
(Leg B's and Leg C's figure, `../r3-blocked/PREREG.md`), plus a floor of 25 ms per sweep for small lattices (kernel launches and the
sheet fix-up, about 100 small launches per twist-plane pass); cupy array code for U(1)/Z₂ at 1.5 µs and 2I at 4 µs per site and sweep
(estimates, not measured on this GPU); measurements about 5 % per smearing step. The queue's `bench` step measures the real numbers first
and logs the projection. CPU numpy reference: 17 µs per site and sweep for SU(2) (one core). Peak GPU memory well below 1 GB.
**Cheapest cuts, in order:** runs 30–38, the reported extras (about 38 min); run 29, β = 2.7 (15 min, loses the second small-L
spacing); runs 27–28, β = 2.6 L = 8, 12 (35 min, loses the third doubling curve of the collapse test). If the bench projects more than
7 h, the coordinator decides on these cuts before continuing (the queue logs the projection; it does not stop by itself).

The queue stops before any SU(2) run if the GPU self-test fails on both paths, or if the photon gate fails.

## Counted points

A run's E (and z = L·E) **counts** for the readings if all of:
1. **plateau**: the TTL scan's rule on the cosh effective masses (smallest t ≥ 1 with m(t) agreeing with m(t+1) and m(t+2) within
   combined errors and e(t) ≤ 0.25·m(t)); E = m(t*);
2. **sheet check**: the mean signed sheet plaquette equals the mean of the other plaquettes of the twisted plane within 3σ + 0.005
   (translation invariance of the twisted theory: the sheet can be moved by a change of variables; it fails grossly, −1.26, if the twist
   is mishandled, self-test);
3. **drift**: E from the first and the second half of every chain agree within 2 combined errors (thermalisation and slow tunnelling);
4. **autocorrelation**: the jackknife bin length is at least 4 τ_int of the per-configuration C(T/4) estimate (Sokal window).

Reported for every run, counted or not: the sign-operator energy E_sign (its plateau) and whether it agrees with E within 2σ (a
disagreement at a counted point is flagged in the report as an operator systematic), the upper estimate z_up = L·(m(2) + 2e(2)) (the
effective masses of a positive-weight correlator approach E from above), the plaquette, τ_int and the bin length. A run with no plateau
is reported with its effective masses and z_up only.

## Readings (SU(2), twist in xy, counted points)

**(i) z(L) against L√σ**, per β, with the scaling check: every counted β = 2.5 point inside the β = 2.4 range is compared with the β = 2.4
curve (log z interpolated linearly in log L√σ, a√σ errors included), and the other pairs are reported. **SCALING HOLDS** if no pull
exceeds 2, or one pull is between 2 and 3 among at least four. Otherwise **SCALING VIOLATED**, and every reading below is reported as
indicative only (lattice artefacts at least as large as the errors).

**(ii) The crossing z = 1** (T1a, 3s1t: the box side equals the flux state's time to live 1/E). L*√σ per β by log-log interpolation
between the bracketing counted points (Gaussian sampling of the point errors and of a√σ); the β = 2.4 and 2.5 values and their spread
are the result. Compared with 1/T_c = 1.41 (deconfinement length) and the Nambu–Goto value 1.58. Not bracketed: reported as "below the
smallest" or "above the largest" counted point.

**(iii) Growth per doubling** (T1b; the δ of `act_reach`; Conjecture W summed over one doubling). Per β, g(L) = z(2L)/z(L) from the
interpolated curve on the grid L√σ = 0.5, 0.625, ..., 1.75 inside the counted range (2L ≤ the largest counted L), and the √2-step
ratio on the whole range. Reported: g_min, where it sits, δ = (2.3 % quantile of g at g_min) − 1. Verdicts:
- **GROWS WITH MARGIN**: the 2.3 % quantile of g exceeds 1 at every grid point, at both main β;
- **NEAR FIXED POINT**: some grid point has g consistent with 1 within 2σ (the crossover has a near fixed point there; any analytic
  argument must work hardest there);
- **FALLS SOMEWHERE**: g + 2σ < 1 somewhere (z decreases with L on a stretch; the act-number scheme then has no monotone crossover).

**(iv) The large end.** For counted points at L√σ ≥ 2.5: R = z/(σL² − π/3) (string with Luescher term) and the Nambu–Goto ratio.
Consistent with a string if R ∈ [0.85, 1.15] within 2σ. **Caveat, stated now:** our a√σ values were obtained from periodic-box torelons
at L√σ ≈ 3.6–4.2 with exactly this formula, so near that L reading (iv) checks twisted against periodic (that the twist stops mattering),
not an independent string tension.

**(v) The small-L exponent.** d log z / d log L between the two smallest counted L per β, compared qualitatively with the semiclassical
11/3 (scout §2.2, heuristic, with log² prefactors) and with the effective exponent of about 2 that González-Arroyo and Martínez fitted in
their dilute region (hep-lat/9507001 eq. 16, read: l_s E = 2 e^{−F} ~ (l_s/l̄)^α, α ≈ 2, l̄ ≈ 0.6–0.7 fm, i.e. l̄√σ ≈ 1.3–1.6 in their
σ = 5 fm⁻² units). Reported, no criterion: lattice artefacts at L = 4 are large (their Q = ½ lattice action is 37.5 at N_s = 4 against
4π² = 39.5).

**(vi) The collapse test** (added at r4-minting's request, before data; its assumption (U): one autonomous flow). At fixed β, the lattice
step-scaling points (u, σ) = (z(L), z(2L)) for every counted L with 2L ≤ the largest counted L (z(2L) measured or log-log interpolated in
the lattice L; no lattice spacing enters): β = 2.3: L = 4; 2.4: L = 4, 6; 2.5: L = 4, 6, 8; 2.6: L = 4, 6. These are the three
resolutions a/L = 1/4, 1/6, 1/8 of the same flow at different u.
- **Collapse**: every point of one β against the other β's curve (log-log interpolation in u). **COLLAPSE HOLDS** if no pull exceeds 2,
  or one between 2 and 3 among at least five. Otherwise **COLLAPSE FAILS**: in this scheme, at these spacings, z(2L) is not a function
  of z(L) alone within errors. Meaning: either the one-flow reading (U) fails for the act-number scheme, or cutoff effects exceed the
  errors; the report says which pattern it is (pulls shrinking towards the finest β point to cutoff effects).
- **Continuum σ(u)**: on a common u grid, σ_β(u) = σ(u) + c(u)·(a/L)² fitted across the β that cover u (two or three; with two the fit is
  exactly determined and reported as such). Reported: σ(u), min σ(u)/u on the measured stretch and where it sits (the growth margin per
  doubling in the u variable; equal in content to (iii) but free of a√σ), and the lattice min σ/u.
- **Controls.** U(1) (β = 1.1: L = 4 → 8; β = 1.3: 4 → 8): σ = identity, |z(2L)/z(L) − 1| ≤ 0.15 + 2σ (the photon's frozen flow at
  u = 2πα_R). Deconfined Z₂ and frozen 2I (L = 2 → 4; 3 → 6 is not available): **PASSED** if σ is below the diagonal (z_up(2L) < z(L), or
  z(2L) + 2σ < z(L) − 2σ); **FAILED** if σ is above it (z(2L) − 2σ > z(L) + 2σ: growth in a deconfined theory, the instrument cannot tell
  confinement from its absence); otherwise **NOT RESOLVED** (reported; no growth, but not resolved below the diagonal). Changed during the
  pipeline test, before any GPU data: the first draft had only PASSED/FAILED and called an unresolved z(2L) a failure.
- **What a failed collapse means**: the one-parameter description (U) of r4-minting does not hold in the act-number scheme at the
  resolution of these data, so "the running is the conservation of Λ" cannot be read off this scheme, and the minting picture's
  "everything else follows" does not hold in it. It says nothing about other schemes, and nothing about SU(2)'s gap.

**(vii) The inversion box, two-state form** (r4-conjw §6, request 2; free, same data). On a symmetric L⁴ box with the twist m_z, 't
Hooft's duality F_e = −log tanh(F_m/2) (round 3, Lean) has the self-dual point F* = log(1 + √2) = 0.8814. With the transfer matrix and
two states per sector, F_e = z (the time extent equals L) and F_m = −log tanh(z/2), so the inversion box is where **z = F* = 0.881**.
Reported per β: L_inv√σ by the same interpolation as (ii), compared with r4-conjw's heuristic bracket [0.94, 1.6], best guess 1.4 ± 0.15.
Stated now: on the symmetric box F_e = z + log[(1 + R₀)/(1 + R₁)] with excited-state sums R that are not small near the crossover, so
this is the two-state value, not the exact F_e = F_m point (see "Optional: exact F_e and F_m" below).

**Line of constant physics (r4-conjw request 4).** No reading compares runs at a fixed L/a across β. Readings (i)–(v) and (vii) compare
at matched L√σ; the collapse test (vi) compares at matched u = z(L), and its (a/L)² extrapolation is at fixed u; the four-move ratios
below are formed at one β and compared across β only at matched L√σ. At fixed L/a and growing β the per-move ratios are lattice
artefacts (r4-conjw §5.3: the widening ratio at fixed N is driven by the Wilson action's a² term), so such a comparison is never made.

**Deconfinement test.** **CONSISTENT** if no counted point at L√σ ≤ 1.2 has z − 2σ > 1. Otherwise **ANOMALY**: the instrument claims a
fitted act at a size where the box is deconfined; the readings are suspended until the cause is found.

## Optional addendum W: the four moves of one doubling (r4-conjw's request 1 and 3; not in the main queue)

**Runs** (`actnumber.PLAN_W`, started only with `queue_actnumber_gpu.ps1 -AddendumW`, after the main plan; the coordinator decides).
Twist in xy, flux along z, the cubes L and 2L from the main plan.

| β | boxes (Lx, Ly, Lz) | T | L√σ of the cube L | role |
|---|---|---|---|---|
| 2.4 | (4, 4, 8), (8, 4, 8); (6, 6, 12), (12, 6, 12); (6, 12, 12) | 48; 32 | 1.03; 1.55 | coarse; (6, 12, 12) = symmetry check of the widened box |
| 2.5 | (4, 4, 8), (8, 4, 8); (6, 6, 12), (12, 6, 12) | 64; 48 | 0.73; 1.09 | fine |
| U(1) 1.1 | (4, 4, 8), (8, 4, 8) | 32 | — | control: l = 2, w = ½ (light) |
| 2I 8.0 | (2, 2, 4), (4, 2, 4) | 32 | — | control: widening far below ½ |

**Cost: about 1.3 GPU hours (±50 %)**, same rate model as the main plan.

**Reading (viii), per (β, L).** At one β, from aE (no lattice spacing): lengthening l = E(L,L,2L)/E(L,L,L), widenings
w_x = E(2L,L,2L)/E(L,L,2L), w_y = E(2L,2L,2L)/E(2L,L,2L); the exact identity z(2L)/z(L) = 2·l·w_x·w_y (r4-conjw, Lean
`four_move_identity`) is a consistency check of the bookkeeping. Margin δ = min(2w_x − 1, 2w_y − 1) and its 2σ-lower value; reported
with where it is smallest along L√σ (β = 2.5 at 0.73, 1.09; β = 2.4 at 1.03, 1.55: compared across β only at matched L√σ).
Verdicts: **W HOLDS** if l + 2σ ≥ 2 and both widenings − 2σ > ½; **W FAILS** if l + 2σ < 2 or a widening + 2σ < ½; otherwise
**NOT RESOLVED**. Symmetry: E(6, 12, 12) = E(12, 6, 12) within 2σ at β = 2.4. Controls: U(1): |l − 2| ≤ 2σ + 0.2 and |w − ½| ≤ 2σ + 0.05
(the photon is exactly marginal, r4-conjw Theorem A; the 10 % allowance covers the box dependence of e_R² with the Wilson action);
2I frozen: w + 2σ < ½ or E unresolved
(r4-conjw: E ∝ e^{−0.955 β N²}). Expectations (r4-conjw §9, heuristic): l ≈ 2, w well above ½ (≈ 1.8 × a shape factor ≥ 1) at small L.
Limits: two L per β at the small end only (L√σ ≤ 1.55); the large-L regime of W (w → 1) is not covered.

## Optional, not prepared: exact F_e and F_m (r4-conjw request 2, exact form)

The exact inversion box needs the zt-twist free energy F_m = −log(W₁/W₀) on symmetric L⁴ boxes with the twist m_z (then F_e =
−log tanh(F_m/2) exactly, by B1 of r3-monotone, and the inversion box is F_m = F*). That is a partition-function ratio, measured by the
Kovacs–Tomboulis coupling integration of r3-monotone §7 (20 Gauss–Legendre nodes in the zt-sheet coupling, about 10⁴ sweeps per node).
**Not prepared here.** Code needed: per-chain sheet couplings and a second sheet in `SheetFix` (the 20 nodes run as 20 chains of one
launch), plus tests: about 2–3 hours of work. **GPU cost**: β = 2.4 and 2.5, L = 6, 8, 10 (L√σ ≈ 1.1–2.6): about 50 min in all. It would
also deliver r3-monotone's twist step-scaling at those points. Recommended only if the two-state reading (vii) lands near the crossover
and the excited-state question matters for the next round.

## Expectations (stated before the data; not criteria)

- z(L√σ) rises from about 0.05–0.3 at L√σ ≈ 0.56 to about 10–12 at 3.6 (σL² − π/3 = 11.9 at 3.61); the crossing at L*√σ ∈ [1.2, 1.8],
  most likely 1.4–1.6; growth per doubling g ≥ 3 everywhere on the grid (power 2 to 11/3 at small L gives 4 to 13; the string gives
  more than 4; the crossover region is where it is smallest); SCALING HOLDS between β = 2.4 and 2.5 within the larger small-L errors;
  R ∈ [0.9, 1.1]; small-L exponent 2–4; COLLAPSE HOLDS with min σ(u)/u ≥ 3.
- The periodic box (reported): z_periodic > z_twisted at L√σ ≈ 1.1 (no tunnelling suppression without twist; Luescher's toron valley),
  equal within errors at 2.2.
- 2I at β = 2.4 (reported): z equal to SU(2) at β = 2.4, L = 6 within errors (2I below its freezing transition mimics SU(2); the
  finite-subgroup test is about β → ∞, not about one β).
- If z falls anywhere on the stretch, or the collapse fails badly, the act-number scheme is not a monotone coupling and the scout's
  candidate 1 loses its numerical support; the report says so plainly.

## Controls and gates

- **Photon gate (U(1), β = 1.1, Coulomb phase), stops the queue.** Every point counted, and all of: **flat**, |z(L) − mean| ≤ 0.15·mean
  + 2σ for L = 4, 6, 8, 10; **no growth**, z(10)/z(4) < 1.5; **photon level**, mean·2β ∈ [0.3, 3] (z = 2πα_R with α_R within a factor of
  3 of the bare 1/(4πβ)). Reported: α_R = z/2π against α_bare = 1/(4πβ) = 0.0723: **the owner's α pointer, checked as z = 2πα on the
  data.** Expectation from the feasibility check below: z ≈ 0.7, α_R ≈ 0.11, about 1.5 times the bare value (the Coulomb phase at
  β = 1.1 is close to the transition at 1.01; a free Villain-type matching of the single-plaquette weight, β_V = 1/(2 ln(I₀(β)/I₁(β)))
  = 0.651, already gives z = 1/(2β_V) = 0.77 instead of 0.45).
- **Z₂ deconfined (β = 0.5 > β_c = 0.4407).** CONTROL PASSED if z does not grow (z(6) − 2σ ≤ z(2) + 2σ, or no plateau at 6) and
  z_up(6) < 1. Expectation: z falls like L·e^{−2βL²}, unmeasurably small at L = 4, 6. Stated now: in this regime the Monte Carlo itself
  rarely tunnels between flux sectors (the barrier is the same 2βL² that suppresses E), so the control tests that the readout reports
  "no growth" when the flux sectors are degenerate, not the exact rate.
- **2I frozen (β = 8.0, above the freezing transition near β ≈ 6, recalled, not re-read).** The same criterion as Z₂. The plaquette is
  reported; frozen means 1 − plaquette far below SU(2)'s at the same β (the snap to the group keeps links exact group elements).
- **Symmetry control (twist in yz, flux along x, β = 2.4, L = 6).** PASSED if |z₁₂ − z₀₁| ≤ 2 combined errors; otherwise the instrument
  is suspected of a direction-dependent bug and the SU(2) readings are marked "instrument asymmetry" until it is found.
- **Every run:** the sheet check (counted points), and the GPU self-test at the start.

## Self-tests, pipeline test and feasibility check (CPU, 2026-11-21; part of the instrument, not results)

`python actnumber.py selftest` (one process, `CUDA_VISIBLE_DEVICES=-1`, about 1 min, **28/28 pass**, `cpu-test/selftest.log`; the three
anisotropic-box checks were added with the addendum): 2I has 120
elements, is closed (10⁻¹³) and has 12 nearest neighbours of 1; the twist eater has zero twisted action and p_f = ±1 in all three planes;
the twisted staple is the exact derivative of the twisted action for one-link changes, sheet links included (SU(2) 10⁻¹⁴, U(1) 10⁻¹⁴);
gauge invariance of the action and the flux operators (10⁻¹⁴); the centre transformation along f flips every flux operator and leaves
the action unchanged (exact); the heat-bath x₀ sampler passes a KS test against √(1−x²)e^{αx} at α = 0.15, 2, 9; the sheet fix-up after an
untwisted pass (numpy emulation of the kernel pass) gives exactly the twisted overrelaxation; the signed sheet plaquette equals the bulk
plaquette for the array path, the emulated fused path, U(1), Z₂ and 2I (β = 2.4: plaquette 0.6283, SU(2) 0.6283), and **fails** by −1.26
without the fix-up (the test has power). `selftest --gpu` adds: fused + fix-up overrelaxation equals array overrelaxation from one
configuration; cupy array = numpy; sheet = bulk on the fused and cupy paths; U(1), Z₂, 2I run on the GPU.

**Pipeline test** (`pipeline_test.py`, one process, numpy, 390 s, `cpu-test/pipeline.log`, `cpu-test/summary.json`; pre-registered as
a **pipeline test only**: L = 2–6, T = 16–32, 4 chains, 100–200 measurements; the numbers are not physics). Every run type of the plan
and of the addendum (U(1), SU(2) in both planes, untwisted and in anisotropic boxes, Z₂, 2I frozen and below freezing) runs, and the
analysis produces every per-run quantity and verdict. For the record only: SU(2) β = 2.4, L = 4 (L√σ = 1.03): z = 0.43 ± 0.04 (sign
operator 0.40 ± 0.04); yz-plane twist 0.53 ± 0.05 (symmetry pull 1.6, passed); periodic box 0.87 ± 0.05 (larger, as expected); 2I at
β = 2.4: 0.32 ± 0.07; Z₂ and frozen 2I (plaquette 0.993 at β = 8): "z falls"; U(1) β = 1.1: z = 0.96, 0.71, 0.73 at L = 2, 4, 6, toy
photon gate passed. Two-site boxes are lattice artefacts: the toy U(1) four-move control at L = 2 → 4 gives l = 2.03 ± 0.14 but
w = 0.45, 0.40 (not ½), and the toy U(1) collapse control (L = 2 → 4) fails for the same reason; production uses L = 4 → 8. (A first
version with U(1) at T = 16 failed the toy gate at L = 6; see the feasibility check.)

**Synthetic check of the combining readings** (`pipeline_test.synthetic_readings`, `cpu-test/synthetic.log`; added after the logged
pipeline run and run on its own; the pipeline test now calls it at the end): counted points generated
from z = x³/(x + 1.6) with 3 % errors at the plan's (β, L), and exact light boxes. Recovered: crossing L*√σ = 1.49 ± 0.02, 1.46 ± 0.02,
1.45 ± 0.02 at β = 2.4, 2.5, 2.6 (true 1.45: the log-linear interpolation is biased by up to 3 % at the coarsest spacing, a stated
method bias); inversion box 1.41, 1.39, 1.38 (true 1.38); GROWS WITH MARGIN with g_min ≈ 5.4–6.3 (true 5.2–6); SCALING HOLDS;
COLLAPSE HOLDS with min σ(u)/u = 5.6 ± 0.4 at u = 0.78 (true 5.5); light four moves l = 2, w = ½ "PASSED".

**Feasibility check of the photon gate** (CPU, one process at a time, `cpu-test/u1-feasibility/`, about 6 min; pre-registered as a
feasibility check only). The toy failure above came from T = 16. With T = 32, 4 chains × 600 (L = 4) and × 400 (L = 6) measurements
and the rotor estimator: z = 0.694 ± 0.020 (L = 4) and 0.729 ± 0.036 (L = 6), both counted, flat within 5 %: the photon's act number is
frozen at 2πα_R with α_R ≈ 0.11. As a consequence U(1) L = 4 uses T = 32 in the plan (was 24). τ_int of C(T/4) at L = 4 was 14
measurements (bin length 120): the plan's every = 4 halves it.

## Changes before data

Both made during preparation, before any GPU data, on relayed requests of finished round-4 attempts:
1. r4-minting: reading (vi), the collapse test with its controls, and the Banks–Zaks point under "What z measures".
2. r4-conjw: reading (vii), the two-state inversion box; the line-of-constant-physics statement; the optional addendum W (reading (viii),
   `PLAN_W`, `-AddendumW`) with anisotropic boxes in the code (self-test 28/28 with three new anisotropic checks; one more in
   `selftest --gpu`); the exact F_e/F_m measurement written up as optional, not prepared.
