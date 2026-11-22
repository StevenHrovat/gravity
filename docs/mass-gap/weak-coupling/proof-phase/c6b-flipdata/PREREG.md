# Pre-registration: the flip probability p(L) read off existing twist and flux data (c6b-flipdata, cycle 6, 2026-11-22)

Written **before any p value, z value or verdict was computed**. Disclosure: while searching for the data (inventory below) the summary
files of the torelon runs were opened, so the torelon energies E_e of the primary points were seen, and it was clear from them that the
measured range will sit near p = 1/2. The rules below were therefore fixed with that knowledge, and they are NOT blind in that sense;
what is fixed is the arithmetic, the thresholds and the wording of each verdict. Nothing is changed after the numbers are computed. Any
later change is listed in a section "Changes after data", at the end of RESULT.md, never here. No new simulation; CPU only; no existing
file is modified; the only input files are the stored summaries listed below, opened read-only.

## 1. What exists (inventory, written first)

A direct measurement of the SU(2) ratio Z_tw / Z_0 (twisted over periodic partition function) **does not exist in this repository.**
Checked: `lattice/` (vortex runs, boundary runs, torelon runs), `weak-coupling/attempts/r3-monotone` (its SU(2) twist free-energy grid
was requested, never run; what exists is `frozen_twist.json`, exact counts at beta = infinity for finite subgroups), `r3-blocked`
(blocked couplings, no twist), `r4-layer` (Lean only: `freeTwist`, the duality), `r4-actnumber` (the twisted-box act number: **no SU(2)
run exists**, the queue stopped at the U(1) photon gate; only four U(1) runs), `c3b-refit` (blocked refit, no twist), `r4-conjw` (its
exact F_e/F_m measurement is "written up as optional, not prepared"), `ROUND-1..4`. What does exist, and what is used:

| id | file | what it is | status here |
|---|---|---|---|
| A | `results/ttl_summary.json` (`lattice/runs-gpu/ttl_*`) | periodic-box torelon (flux-odd) ground-state energy, SU(2), beta = 2.3, 2.4, 2.5, 2.6, 2.7 at L = 12, 16, 20, 28, 32 (T = L), plateau rule | **primary** |
| B | `results/luscher_summary.json`, `zeta/PREREG-LUSCHER.md` | the same at beta = 2.3, L = 6, 8, 10 (T = 16), plateau rule (L = 12, 14: no plateau) | **primary** |
| C | `results/lattice_summary.json` | the same at beta = 2.3 L = 10, 2.4 L = 14, 2.5 L = 16 (T = L), fixed rule (effective mass t = 1 to 2), no plateau test | secondary (reported, no vote) |
| D | `results/strong_summary.json` | 8^4, beta = 1.7 to 2.2, effective masses only, no scale | not used (no plateau, no sigma) |
| E | `results/vortex_summary.json`, `lattice/PREREG-VORTEX*.md` | centre-projected P-vortex density per plaquette, beta = 2.3 (12^4), 2.4 (16^4); gauge-fixing dependent (Gribov copies, `PREREG-VORTEX-SIGMA.md`) | **model input only** (curve V) |
| F | `weak-coupling/attempts/r3-monotone/frozen_twist.json` | **exact** Z_tw / Z_0 counts at beta = infinity: Q8, 2T, 2O, 2I (and Z2, Z4: twist never flat) | exact control (not SU(2)) |
| G | `weak-coupling/attempts/r4-actnumber/runs-gpu/photon_gate.log` | U(1), beta = 1.1, twisted box (flux along twist) act number z: L = 4, 6 counted; L = 8, 10 not counted (cold/hot split) | photon control |

Not twist data, listed so nobody looks for them again: `lattice/runs-gpu/boundary/` (twisted **boundary condition** on a box with frozen
faces: a response of the interior, not a partition-function ratio), `r3-blocked`, `c3b-refit`.

## 2. The quantity

Flip probability of a box of side L: p(L) = Z_tw / (Z_tw + Z_0) = 1 / (1 + e^{F_tw}), F_tw = -ln(Z_tw / Z_0), twist in one plane of the
periodic symmetric box (L^4).

**Exact bridge to the existing data** (the duality `tHooft_rotation`, `freeFlux_eq_dual`, `twist_centre_transform`, Lean, in this repo;
r3-monotone B1): on the symmetric box, Z_0 = Z_e0 + Z_e1 and Z_tw = Z_e0 - Z_e1, with Z_e1 / Z_e0 = rho = e^{-F_e} the weight of the flux-odd
sector (one direction) over the flux-even sector. Hence, exactly,

    p = (1 - rho) / 2 = (1 - e^{-F_e}) / 2,        F_tw = -ln tanh(F_e / 2).

So p = 1/2 means rho = 0; the floor p >= p_min is the statement rho <= 1 - 2 p_min, i.e. F_e >= -ln(1 - 2 p_min) > 0: **the flux-odd sector
stays strictly lighter than the vacuum sector in weight by a margin.** (p <= 1/2 is Z_e1 >= 0; p >= 0 is Z_e1 <= Z_e0, the nontrivial side,
`Z1_le_Z0` in `LayerSector.lean`.)

**Estimator** (one-state proxy, the r4 convention): F_e ~ z := L * E_e, E_e the ground-state energy of the flux-odd sector read from the
torelon correlator (the periodic-box torelon energy does not depend on T; it is independent of whether the box is cubic). Then
rho_c = e^{-z}, p_c = (1 - e^{-z}) / 2, F_tw,c = -ln tanh(z / 2).

**Is the measured quantity exactly Z_tw/Z_0?** No. It is a proxy for it with three stated systematics:
- (S1) excited states: rho = g e^{-z} with g = (1 + flux-odd excitations)/(1 + flux-even excitations) at T = L. Assumed g in [1/2, 2] (a stated
  assumption, not derived); a band is reported, never used for a pass.
- (S2) the effective mass at t* is an **upper** bound on E_e (reflection positivity: effective masses approach the ground state from above).
  So z_meas >= z_true, rho_meas <= rho_true, **p_meas >= p_true**. The data bound p from above, not from below, strictly; the floor
  direction is covered only by the plateau (agreement t* vs t* + 1) and by the agreement with the string formula (reported).
- (S3) the torelon ground state at weak spatial transverse momentum is taken to be the lowest flux-odd state; tower multiplicity in the
  flux-odd sector is inside g.
  Twist conventions: the box is periodic, T = L is required by the duality, the torelon winds the direction whose twist is dualised;
  by the lattice symmetry (Lean `twistZ_perm`) the plane is immaterial. The **twisted-box** act number of r4-actnumber (flux parallel to
  a spatial twist) is a different object; it is used only for the U(1) control (G), flagged.

## 3. Units and errors

- Physical length: x = L sqrt(sigma) = L * (a sqrt(sigma))_beta, with (a sqrt(sigma))_beta from the TTL scan row of the same beta (A):
  0.3503(61), 0.2579(29), 0.1822(22), 0.1396(16), 0.1057(18) at beta = 2.3 ... 2.7; the same value is used for B and C at that beta.
  Scale error and the alternative scales (the project's other torelon values 0.363, 0.273, 0.199; B's own 0.371) are a horizontal error bar and a
  systematic of x only; they cannot move any verdict below (checked in the result).
- Vertical errors, independent per point: dz = L dE; drho = rho dz; dp = rho dz / 2; dF_tw = (dz / sinh z) (exact derivative of -ln tanh(z/2)).
  Statistical errors are those stored (jackknife, bins as in the source analyses); no new resampling.
- Combined conservative value for each verdict test: z_lo = z - 2 dz (so rho_hi = e^{-z_lo}), p_lo = (1 - rho_hi) / 2.
  Also reported: the systematic band for S1 (g = 1/2 and 2), and E at t* + 1 where stored (S2 check).

## 4. Fixed thresholds and verdicts

x = L sqrt(sigma). Counted points: primary (A, B) only; C is shown and must agree with the primary points within 2 combined errors where
they overlap (beta, L), else it is flagged; it has no vote. Thresholds are fixed as follows.

- **NEAR HALF (a point):** p_lo >= 0.45 (equivalently z_lo >= 2.30, rho <= 0.10).
- **FALLS (a pair):** two counted points at the same beta, L1 < L2, with p(L2) < p(L1) - max(2 sigma_comb, 0.02).
- **TREND test:** fit z against x^2 (the area-law form z = s x^2 - c) with the counted points, weighted; **GROWS** if s > 0 at more than 2
  sigma (then rho -> 0 exponentially in the measured form, and p -> 1/2); **STALLS** if s <= 0 within 2 sigma. The extrapolation to x -> infinity
  that follows from s > 0 is **the area law itself**, i.e. confinement of the flux sector; it is reported as circular for the purpose of a
  floor, not as evidence for it.
- **FLOOR ON THE MEASURED RANGE:** every counted point has p_lo >= 0.25 (rho <= 0.5, z_lo >= 0.69) and no pair FALLS. Stated as "floor on
  [x_min, x_max]", never as a floor at all L. The reported p_min is the smallest p_lo over the counted points.
- **AGAINST THE FLOOR:** any counted point with x >= 2 and p_lo < 0.25, or any FALLS pair, or STALLS.
- **p <= 1/2:** holds point by point if rho_c > 0 (it does by construction of the proxy); reported as "not independent of the
  duality", not as a test of reflection positivity. The test that carries content is p >= 0 (z > 0), reported.
- **THE TRANSITION REGION:** counted points with x < 2: if there are none, every statement about p near the deconfinement length
  (1/T_c, x ~ 1.4) and near the round-4 self-dual point is **NO DATA**, whatever the extrapolation says.
  Marks drawn: x = 1.41 (1/T_c from T_c/sqrt(sigma) = 0.71, recalled value), x = 1.39 to 1.55 (the round-4 "self-dual point": a
  **prediction** of r4-conjw from the Luescher and Nambu-Goto formulas, not a measurement; no SU(2) twisted-box run exists), and the level
  p = 0.293 = 1/(1 + e^{F*}), F* = ln(1 + sqrt 2), where F_e = F_tw.

## 5. Controls and comparison curves (no vote on the SU(2) verdicts)

- **Photon (G):** p_gamma = (1 - e^{-z}) / 2 from the counted U(1) points; verdict-style statement only: does the photon also have a floor
  (z frozen)? Reported both for the one-state form and for the free-rotor tower E_n = n^2 E_1 (Z_e1/Z_e0 = sum over odd n / sum over even n).
- **Finite subgroups (F):** p_inf = 1 / (1 + e^{F_inf}) from the exact counts, the same for every box size; Z2, Z4: Z_tw = 0, p = 0.
- **Curve S:** z = x^2 - pi/3 (Luescher) and z = x sqrt(x^2 - pi/3) (Nambu-Goto), extrapolated into the unmeasured x < 2, flagged as not data.
- **Curve V:** independent-vortex model: n = (density / sigma a^2) x^2, the parity of the number of P-vortex piercings of an L x L cross-section
  is odd with probability p_V = (1 - e^{-2 n}) / 2. Density per plaquette from E (0.0943 at beta = 2.3); gauge-fixing dependent (the
  projected string tension is 18 to 32 % too high there), independence is an assumption; **it has p -> 1/2 built in** and so cannot test a
  floor. Comparison only.
- **Published values** are quoted only as already recorded in the repository notes (r3-monotone, r4-actnumber: Kovacs and Tomboulis, hep-lat/0002004,
  vortex free energy at beta = 2.3, 2.4, 2.5 decays with L; de Forcrand and von Smekal, Phys. Rev. D 66 (2002) 011504, electric flux free energies
  vanish with L below T_c; Gonzalez-Arroyo and Martinez, Nucl. Phys. B 459 (1996) 337, hep-lat/9507001, diagonal flux l E ~ 2 near x ~ 1.3 to 1.6);
  not re-read in this workstream, no numbers beyond these are cited.

## 6. What the data cannot show (stated before looking)

Finite x range (the primary points start at x ~ 2.1); finite beta (2.3 to 2.7, scale errors of a few %); no continuum limit; S1 and S2 above;
the proxy is not Z_tw/Z_0; **a floor for all L is not a finite-data statement.** A measurement of the transition region x in [0.7, 2]
(Z_tw/Z_0 itself, by snake or coupling integration, or the flux energy on twisted and periodic boxes) is what would add information; it is
specified in RESULT.md after the verdicts.
