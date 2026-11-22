# Result: the flip probability p(L) from existing data (c6b-flipdata, 2026-11-22)

Rules: `PREREG.md` (unchanged). Code: `extract_p.py` (read-only inputs, CPU, a few seconds). Output: `extract_p.log`, `p_table.csv`,
`p_plot.svg`. No existing file was modified. Claim level: analysis of stored summaries; a proxy, not a measurement of Z_tw / Z_0.

## 1. What the data are, in one paragraph

**No SU(2) measurement of Z_tw / Z_0 (or of a twist free energy at any box size) exists in this repository.** The r3-monotone grid was
requested and never run; r4-actnumber's twisted-box act number has no SU(2) run (the queue stopped at the U(1) photon gate); r4-conjw's exact
F_e/F_m was written up as optional and not prepared; the boundary runs are a twisted boundary condition on a frozen-face box, not a
partition-function ratio. What exists are **periodic-box torelon (flux-odd) energies E_e**, 11 points, beta = 2.3 to 2.7, x = L sqrt(sigma) from
2.1 to 4.2. On a symmetric box these are linked to p exactly by the duality already in Lean (p = (1 - e^{-F_e})/2, F_tw = -ln tanh(F_e/2)),
and with the one-state proxy F_e ~ L E_e that gives p(L). The vortex runs (centre-projected P-vortex density, two beta) and the exact
beta = infinity twist counts for finite subgroups are the only other twist-type data; they enter as a model curve and as exact controls.

## 2. The p(L) table (primary = plateau-rule points; secondary has no vote)

x = L sqrt(sigma) with a sqrt(sigma) from the TTL scan row of the same beta; z = L E_e; p = (1 - e^{-z})/2; errors propagated as in PREREG 3.
p_lo uses z - 2 dz. "band" is the excited-state systematic S1 (rho multiplied by 2 or 1/2), an assumption, not an error.

| src | beta | L | x | z = L E_e | p | F_tw = -ln tanh(z/2) | p_lo | band (g = 2 .. 1/2) |
|---|---|---|---|---|---|---|---|---|
| B | 2.3 | 6 | 2.10(4) | 3.59(3) | 0.4862(4) | 5.5e-2 (1.5e-3) | 0.4854 | 0.472 .. 0.493 |
| B | 2.3 | 8 | 2.80(5) | 7.84(25) | 0.49980(5) | 7.9e-4 (2.0e-4) | 0.4997 | 0.4996 .. 0.4999 |
| A | 2.7 | 32 | 3.38(6) | 10.39(40) | 0.49998 | 6.1e-5 | 0.5000 | - |
| B | 2.3 | 10 | 3.50(6) | 12.23(25) | 0.500000 | 9.8e-6 | 0.5000 | - |
| A | 2.5 | 20 | 3.64(4) | 12.24(33) | 0.500000 | 9.7e-6 | 0.5000 | - |
| A | 2.6 | 28 | 3.91(5) | 14.24(36) | 0.500000 | 1.3e-6 | 0.5000 | - |
| A | 2.4 | 16 | 4.13(5) | 15.99(38) | 0.500000 | 2.3e-7 | 0.5000 | - |
| A | 2.3 | 12 | 4.20(7) | 16.62(61) | 0.500000 | 1.2e-7 | 0.5000 | - |
| C | 2.5 | 16 | 2.92(4) | 9.09(31) | 0.49994 | 2.3e-4 | 0.4999 | - |
| C | 2.3 | 10 | 3.50(6) | 12.12(81) | 0.500000 | 1.1e-5 | 0.5000 | - |
| C | 2.4 | 14 | 3.61(4) | 13.54(45) | 0.500000 | 2.6e-6 | 0.5000 | - |

Plot: `p_plot.svg` (p against x; 1/T_c at x = 1.41, the round-4 band 1.39 to 1.55, the self-dual level p = 0.293; the Luescher and
Nambu-Goto extrapolations, the independent-vortex model, and the U(1) photon marked). Only the right-hand part (x >= 2.1) carries data.

Reading of the table: p is within 0.014 of 1/2 at the smallest measured box (x = 2.10, p = 0.486, F_tw = 0.055) and within 1e-3 from x = 2.8 on.
The deficit 1/2 - p = rho/2 falls by about a factor e per unit of z, i.e. like e^{-(x^2 - c)}. At the same beta (2.3), L = 6, 8, 10, 12 give a
monotonically rising p. The secondary points agree with the primary one where they overlap (beta 2.3, L = 10: 0.13 sigma). The stored effective
mass at t* + 1 agrees with that at t* within 1 sigma at all five TTL points (S2 check), so the one-sided bias of S2 is not visible at this precision.

## 3. Verdicts (pre-registered rules, PREREG 4)

| statement | verdict |
|---|---|
| NEAR HALF (p_lo >= 0.45) at every primary point | **yes**, 8 of 8 (smallest p_lo = 0.4854) |
| FALLS (same-beta pair, drop > max(2 sigma, 0.02)) | **none** (only beta = 2.3 has more than one primary point: four sizes, rising) |
| TREND, z = s x^2 - c over the primary points | s = 1.014 +- 0.015, c = 0.88 +- 0.08, chi2/dof = 21/6 (errors too small for the scatter between betas); unweighted s = 0.95: **GROWS** (the Luescher values s = 1, c = pi/3 = 1.05 lie within about 2 sigma of the weighted fit for c) |
| FLOOR ON THE MEASURED RANGE x in [2.10, 4.20] | **holds**, p_min = 0.485 (the smallest p_lo); no counted point at x >= 2 has p_lo < 0.25 |
| AGAINST THE FLOOR (any point with x >= 2 and p_lo < 0.25, a FALLS pair, or STALLS) | **no** |
| transition region x < 2 (deconfinement length, round-4 self-dual point) | **NO DATA**: no counted SU(2) point below x = 2.10 |
| p >= 0 (z > 0) | holds at every point (z >= 3.6); p <= 1/2 holds by construction of the proxy, so it is not a test |

Stated as plainly as the data allow: **on x in [2.1, 4.2], SU(2) has p within 1.4 percent of 1/2 and rising; no sign of the flip probability
fading. Below x = 2.1 the data say nothing at all, and that is exactly the region where p would have to leave 1/2 (deconfinement length,
self-dual level p = 0.293).**

## 4. Controls and the one thing they change

- **Photon (U(1), beta = 1.1; twisted-box act number, a different object, flagged):** the counted points L = 4, 6 give z = 0.686(18), 0.540(13);
  L = 8, 10 (not counted, cold/hot split) 0.72, 0.78. One-state p = 0.25, 0.21 (0.26, 0.27 uncounted). With the free-rotor tower E_n = n^2 E_1 (flux sums
  over all odd/even n) rho is 0.85 to 0.96 and p drops to 0.02 to 0.08. **Either way the photon's p is a constant bounded away from 0 at every
  box size: the photon passes the floor test.** So "p(L) >= p_min > 0" does not separate a gapless Coulomb phase from SU(2). What does separate
  them in these data is the **growth of z with x** (z frozen near 0.7 for the photon, z = x^2 - c for SU(2)), i.e. p -> 1/2 versus p frozen
  below 1/2. A floor with p_min, without p -> 1/2 (or at least p - p_frozen > 0 growing), proves too much (photon test).
- **Finite subgroups at beta = infinity (exact counts, every l):** p = 0.115 (Q8), 0.016 (2T), 0.020 (2O), 0.0063 (2I); Z2 and Z4: p = 0
  (twist never flat). These are exact Z_tw/Z_0 ratios, the same at every box size: a floor that is literally independent of L and carries
  no gap (frozen configurations). So a floor alone also does not imply dynamics.
- **Independent-vortex model V** (P-vortex density per plaquette / sigma a^2 = 0.77 at beta = 2.3, 0.91 at 2.4, gauge-fixing dependent; piercing
  parity of an L x L cross-section odd with probability (1 - e^{-2n})/2, n = 0.84 x^2): p_V = 0.28, 0.41, 0.48, 0.499 at x = 0.7, 1.0, 1.4, 2.0. It
  has p -> 1/2 built in and cannot test a floor; it is shown only to say that vortex density alone predicts p near 1/2 already at x = 1.4,
  while the Luescher extrapolation of the torelon data gives p = 0.30 there. The two disagree in the unmeasured region by about 0.2: that is
  the open range.
- **Published values (as recorded in the repository notes, not re-read here):** Kovacs and Tomboulis, hep-lat/0002004 (SU(2) vortex free energy
  at beta = 2.3, 2.4, 2.5 decays with L); de Forcrand and von Smekal, Phys. Rev. D 66 (2002) 011504 (electric flux free energies vanish
  with L below T_c); Gonzalez-Arroyo and Martinez, Nucl. Phys. B 459 (1996) 337 (diagonal flux, l E ~ 2 near x ~ 1.3 to 1.6, which would read p ~ 0.43
  if the convention matched; it does not: diagonal flux, twisted box). Our measured range is qualitatively the same statement as those (F_tw falls with
  L); it is a different observable at larger x than their small-volume work. No quantitative comparison is claimed.

## 5. Caveats (what the data cannot show)

1. **It is a proxy.** p = Z_tw/(Z_tw + Z_0) was not measured; F_e ~ L E_e is the ground-state (one-state) form. The excited-state factor g (S1) is an assumed
   band [1/2, 2]; at x >= 2.1 it moves p by at most 0.014. At the smallest box it is irrelevant for the verdicts; it would matter at z ~ 1 (x ~ 1.4).
2. **One-sided bias (S2).** Effective masses are upper bounds on E_e (reflection positivity), so p_meas >= p_true: the data bound p from above. The
   t* versus t* + 1 agreement and the agreement with the string law (s = 1.0, c = 0.9 to 1.0) say the bias is small, but strictly the floor direction is
   not a rigorous lower bound.
3. **Range and scale.** x from 2.10 to 4.20 (the L = 6 point at 1.98 if an alternative scale is used; no verdict depends on x there since p_lo = 0.485);
   beta = 2.3 to 2.7; scale errors 2 to 6 %; the beta = 2.3 box carries the known scaling violation of the TTL scan (`PREREG-TTL.md`).
4. **Conventions.** Periodic box, T = L (the duality needs the symmetric box); the primary B points have T = 16 (the torelon energy does not depend on T,
   so only the proxy's use of L is affected, not the energy). The twist plane is immaterial by the lattice symmetry (Lean `twistZ_perm`).
5. **Circularity of the extrapolation.** That z = s x^2 - c keeps growing, and so p -> 1/2, is the area law of the flux sector, i.e. the confinement
   one wants to prove; the data support it on [2.1, 4.2] and cannot support more.
6. **Not twisted-box data.** No SU(2) twisted-box (e parallel to m) flux energy exists; the r4 "self-dual point at x ~ 1.4 to 1.55" is a prediction from the
   Luescher / Nambu-Goto formulas, not a measurement (my Nambu-Goto form z = x sqrt(x^2 - pi/3) crosses F* at x = 1.26, the Luescher one at 1.39; r4-conjw
   quotes 1.39 to 1.55). The data neither confirm nor refute it.

## 6. What new measurement would settle the floor

The floor needs p at **x between 0.7 and 2**, where p must leave 1/2 and the question is whether it stays above some p_min or fades. One measurement
does it, and it is already scoped in r4-conjw / r4-actnumber (2 to 3 h of code, about 50 GPU minutes): **Z_tw / Z_0 itself on symmetric L^4 boxes** (snake or
coupling integration, de Forcrand and von Smekal style), SU(2), beta = 2.4 at L = 4, 5, 6, 8, 10 (x = 1.03 to 2.58) and beta = 2.5 at L = 6, 8, 10 (x = 1.09 to 1.82),
with p = Z_tw/(Z_tw + Z_0) read directly (no proxy, no excited-state factor), plus the periodic-box torelon energy at the same boxes as a cross-check of
the duality. Pre-registered criteria to carry over: NEAR HALF p >= 0.45; the floor on [x_min, x_max] if p >= 0.25 throughout x >= 1.4; the fall below 0.293 at x
below 1.4 is expected and is not against the floor. Also needed, for the photon test, **the U(1) counterpart with a sector-resolved control** (the photon gate failed at L >= 8
on cold/hot sectors). A floor-with-growth (p - p(x_small) increasing and approaching 1/2) is the discriminating reading; a bare floor is not.
Cheaper partial step (already pre-registered, not run): `c5e-dmp/PREREG-JOINT.md` runs periodic boxes at x = 1.03 to 4.2 (2.5 GPU h) and would extend the torelon
proxy down to x ~ 1, but there S1 matters and only the direct ratio is clean.

## Changes after data

None to the rules. Two remarks added to the text: the alternative-scale check (L = 6 may sit at x = 1.98, no verdict affected), and the Nambu-Goto
crossing computed here (1.26) against the value quoted in r4-conjw.
