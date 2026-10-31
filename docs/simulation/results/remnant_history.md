# Remnants with a history: the stochastic and the contained remnant against SPARC and high-redshift kinematics

Workstream of *GUID v6: Our theory as simulated*. Written by `docs/simulation/remnant_history.py` from one run (seed 20161101, 1000 galaxy-bootstrap resamples, 500 mock universes per null model); every number is also in `remnant_history.json`. Figures: `docs/simulation/figures/remnant_forms.pdf`, `remnant_scales.pdf`, `remnant_history.pdf`, `remnant_halos.pdf`, `remnant_redshift.pdf`. Checks: **39 of 39 passed** (pipeline reproduction and internal consistency; every model comparison below is a result, not a check). The data, cuts, error model and likelihoods are those of `sparc_rotation.py`, imported or copied from it, and its universal fits are reproduced to 1e-4.

The question: `sparc_rotation.py` rejected a static, constant extra acceleration |γ1|/2 (the residual slope d log(g_obs - g_bar) / d log g_bar is 0.44, a constant gives 0). The theory proposes a long cosmic evolution in which remnants accumulate. What does it allow once history is included, and does a cohesive whole emerge?

## Verdict

- **R1, accumulated stochastic remnant.** As a hypothesis, a random walk of the field's kicks gives g_obs = g_bar + √(g_bar a_acc) (form B) or, if the excess is sourced by the total field, g_obs = g_bar/2 + √(g_bar²/4 + g_bar a_acc) (form S). Form S fits SPARC as well as the RAR (ΔBIC -5.5 with the stated errors, -2.6 with a fitted floor), with a_acc = 1.10e-10 m/s² (bootstrap 16-84%: 1.02e-10 to 1.19e-10). Form B is worse (ΔBIC +209; a_acc = 7.72e-11) because it overshoots at high acceleration (median residual -0.079 dex at g_bar > 1e-9). Both beat the constant (by ΔBIC 4857 and 5071). Both forms are MOND's phenomenology under a new name: S is Milgrom's "simple" interpolating function. And the sqrt form was proposed after the slope 0.44 was measured, so matching it is not a prediction.
- **R1, the solar system excludes both forms as written.** Applied pointwise in the Sun's field, form B adds a perihelion precession of -6.0e+04 mas/yr at Mars, 2e+08 times the ephemeris bound; form S adds -74 mas/yr at Saturn, 2e+04 times its bound (Pitjeva and Pitjev 2013). A version that survives needs an extra rule that switches the term off at high acceleration (the RAR's exponential does), which the accumulation picture does not supply.
- **R1, natural scales.** Of nine candidate scales, the nearest to form S's a_acc is c H0 / 2π (H0 = 73) (0.012 dex away; a_acc/cH0/2π = 0.99 with distances rescaled to H0 = 67.4 and 0.97 at 73). This is Milgrom's known coincidence a0 ≈ cH0/2π, not a test: the total uncertainty on a_acc is 0.11 dex (mostly the stellar M/L), 4 of the 9 candidates lie within 2σ of it, and a scale drawn at random within ±1 dex would land as close to one of them with probability 0.10. The scales without 2π (cH0, cH_inf, c/t0, 5.4e-10 to 7.1e-10) are excluded by ΔBIC ≥ 25096, as Bridge A was.
- **R1c and R2, history.** Per galaxy, a_acc (form B) has a spread of 0.40 dex and, against the per-galaxy error estimates, an intrinsic scatter of 0.23 dex (form S 0.20; the RAR's g† 0.20, so form S's a_acc is exactly as universal as g†). Mock universes with a universal RAR, passed through the SPARC error model and the same analysis, give 0.11 and 0.04 dex: with this error model the data scatter more than a universal law would, g† as much as a_acc, so the excess is not specific to the stochastic remnant (an M/L that varies between galaxies by more than the 0.1 dex assumed would do it). Of 15 rank correlations with history proxies (Hubble type, gas fraction, surface brightness, disk scale length, orbits per Hubble time), 0 survive the Holm correction, and 0 of the 15 partial correlations at fixed mass. Measured against the correlations that a universal RAR already produces through the error model and shape mismatch (mock universes), 0 of 30 differ after Holm. The signs a galaxy-specific accumulation predicts for log a_acc are met in 2 of 5, and the slope of log a_acc on log N_orb is +0.12 [-0.17, +0.46] where a per-orbit random walk predicts +1. No history dependence beyond the global cosmic time is detected.
- **R3, contained remnant.** Baryons + a halo per galaxy fit better than any universal law in total BIC (NFW with the Dutton-Macciò prior: -1360 against the universal RAR; Burkert -1780), but they spend 2 parameters per galaxy (264) against 1 in all. Under the point-wise likelihood any per-galaxy parameter absorbs galaxy-wide distance, inclination and M/L offsets: one free RAR scale per galaxy already reaches -1883. Against that yardstick NFW is worse (ΔBIC +523), Burkert worse (+103), and NFW halos held to the Moster et al. stellar-to-halo mass relation worse (+775). Per galaxy, NFW beats the universal RAR in 88 of 132, Burkert in 98, cosmological NFW in 82.
- **R4, the whole.** With NFW halos the best amplitude of the sqrt term is zero, and zero with cosmological halos; its 95% upper bound is 2.07e-15 m/s² (2.28e-15; galaxy-bootstrap 84th percentile of the bound 2.96e-14), 3e+03 times smaller than the a_acc that form B needs alone. A constant term has best amplitude zero with NFW and 6.62e-13 m/s² (ΔBIC of adding it +3.5) with cosmological halos, bounded at 8.42e-13 and 1.18e-12: 0.05 of the constant that fits alone. With cored (Burkert) halos a small constant is preferred: 4.20e-12 m/s² (ΔBIC of adding it -50.1); since the same constant is not wanted with NFW halos, it reads as a correction to the halo's outer shape rather than a universal term (an interpretation). If primordial black holes are all of Ω_c h² = 0.120, halos exist, and the stochastic term has almost no room: at the bootstrap-84% bound it supplies a median 2.1% (sqrt) or 9% (constant) of the dark acceleration at the outermost measured radius.
- **R5, cosmic time.** Accumulation makes a_acc grow with time; random-walk accumulation gives a_acc ∝ t, so at fixed rotation speed galaxies at z ≈ 1 would need +0.37 dex more baryons (deep regime). The published high-redshift kinematics point the other way: the baryonic Tully-Fisher zero point is offset by -0.44 ± 0.04 dex at z ≈ 0.9 and -0.27 ± 0.05 at z ≈ 2.3 (Ubler et al. 2017), and MUSE-DARK III finds the RAR's scale at z ≈ 1 a factor 2.0 ± 0.4 above the local value. A scale ∝ H(z) (1.79 at z = 1) or ∝ 1/t (2.36) has the right sign; 1/t gives 4.2 at z = 2, where Milgrom (2017) finds ~4 a0 all but excluded. These measurements carry systematics (gas masses, pressure support, model-dependent baryonic accelerations) of the size of the effect, and ΛCDM galaxy evolution produces such offsets too, so they are not a clean test; read literally, they disfavour accumulation.
- **R6.** The acoustic peaks, weak lensing, cluster masses and the Bullet Cluster need a relativistic theory of the stochastic remnant, which does not exist; nothing was fitted there. The contained remnant (primordial black holes as cold dark matter) covers them by construction.

**Does a cohesive whole emerge?** Not as a combination. The two remnants compete for the same job. A universal stochastic term of form S reproduces the rotation curves as well as the RAR, but it is MOND with a new motivation: its scale matches cH0/2π only in the way Milgrom's a0 always has, it fails the solar system as written, its accumulation version has the wrong sign in time, and it has no relativistic form for the microwave background, lensing or clusters. The contained remnant covers the cosmology, and once its halos are present the data leave the stochastic term almost no room. The consistent reading is the contained remnant (cold dark matter, here primordial black holes) with a stochastic term too small to matter in galaxies, which inherits ΛCDM's galaxy-scale questions (cored inner profiles, the tightness of the RAR) rather than answering them.

## Fixed before fitting, and chosen after seeing data

Fixed in the script's header before any fit ran: the two forms B and S; the nine natural scales (the task's list); the five history proxies and the sign each should have under galaxy-specific accumulation; the halo models, their priors and bounds; the four evolution laws of R5 and the two acceleration regimes (deep, and g_obs = 3 and 10 g†) used to read the high-redshift data.

Chosen or changed after seeing results, stated here:

1. The R4 amplitude grid first started at 10⁻¹³ m/s². The first run showed that the sqrt term's bound lies below that, and that 10⁻¹³ is not negligible for the sqrt form (√(10⁻¹² · 10⁻¹³) is 30% of g_bar at the lowest points). The grid now starts at 10⁻¹⁶, and the joint fitter's consistency check uses 10⁻³⁰ instead of 10⁻¹³. A resolution change, not a model change.
2. Two checks failed on the first run because the checks themselves were wrong (a log base in the finite-difference slope test; angle unwrapping in the orbit integration). Both were fixed; no tolerance was loosened.
3. The number of mock universes was raised from 200 to 500 after a test run, to steady the 2.5-97.5% null bands.
4. The mocks' extra per-point scatter (non-circular motions) is calibrated on the data: σ_x = 0.044 dex makes the median per-galaxy reduced χ² of a free RAR fit match the data's 3.01.
5. Using one free RAR scale per galaxy as the calibration for what per-galaxy freedom buys under the point-wise likelihood (R3) was decided after seeing that every per-galaxy model beats every universal one in total BIC.
6. The reading of the Burkert + constant improvement in R4 as a halo-shape correction is an interpretation made after seeing it.
7. The shift test of R2 (observed ρ minus the mock-null mean, against the data's bootstrap spread) and the mock calibration of the intrinsic scatter τ in R1c were added after test runs with 4 to 20 mocks, whose 95% bands looked much narrower than the bootstrap intervals. With 500 mocks the raw bands are about as wide as the bootstrap intervals and the partial ones narrower, because the mocks lack the data's extra scatter (R1c). Bands, shift test and the τ calibration are all reported.

## Data and method

- SPARC (Lelli, McGaugh and Schombert 2016), checked by SHA256 and not copied into the repository:
  `MassModels_Lelli2016c.mrt`: `9108994b12cc401b94a1768beca61c53ec354779385c9c9cc571049f3043244c`
  `SPARC_Lelli2016c.mrt`: `5aa0501f6b0d881fa579030e315e7b5b6ef561a5bd3a07472f9929c7e5728243`
- Sample of `sparc_rotation.py`: Q < 3, i ≥ 30°, δV/V < 0.1: 153 galaxies, 2696 points, 147 galaxies with points; Υ_disk = 0.5, Υ_bulge = 0.7. Per-galaxy work uses the 132 galaxies with at least 5 points (2652 points).
- Likelihood L1 (primary, from `sparc_rotation.py`): Gaussian in log g_obs; the variance is the full error model of Lelli et al. (2017), with the g_bar error carried through each model's slope. L2: velocity errors plus a fitted intrinsic floor. Robust: soft-L1 loss. BIC = -2 ln L + k ln N over points. Galaxies are resampled for every uncertainty, because points within a galaxy share distance, inclination and M/L errors and the point-wise BIC overstates the evidence.
- Per-galaxy scales (R1c, R2) are fitted as in `sparc_rotation.py` S2c: velocity errors per point, with distance, inclination, Υ (±25%) and HI (±10%) applied as whole-galaxy shifts and added in quadrature.
- Halos (R3, R4): NFW in (M200, c200) with ρ_crit for H0 = 67.4 and the Dutton and Macciò (2014) relation log c200 = 0.905 - 0.101 log(M200/10¹² h⁻¹ Msun), 0.11 dex scatter, as a prior; "cosmological" NFW halos also carry the Moster, Naab and White (2013) stellar-to-halo mass relation (0.15 dex) with M* = 0.5 L[3.6]; Burkert halos in (ρ0, r0) without prior. Each galaxy is fitted on a grid and refined by Nelder-Mead (MAP); BIC uses -2 ln L at the MAP and k = 2 per galaxy.
- R4 adds one universal term, A (constant) or √(g_bar A), to baryons + halo, refits every halo at each of 66 amplitudes from 10⁻¹⁶ to 10^-9.5 m/s², and sums -2 ln (L × prior) over galaxies (profile likelihood). The one-sided 95% bound is where the sum rises by 2.71; galaxies are resampled for its spread.

## R1a: one universal a_acc

| model | free | best value [m/s²] (bootstrap 16-84%) | χ²/dof | ΔBIC vs RAR (L1) | σ_int (L2) [dex] | ΔBIC vs RAR (L2) | robust MAD [dex] |
|---|---|---|---|---|---|---|---|
| Newton (g_bar only) | 0 | - | 20.766 | +52645.0 | 0.512 | +7383.8 | 0.310 |
| RAR (McGaugh et al. 2016 function) | 1 | 1.12e-10 (1.04e-10 to 1.21e-10) | 1.552 | +0.0 | 0.123 | +0.0 | 0.116 |
| constant |γ1|/2 (sparc_rotation.py) | 1 | 2.27e-11 (2.07e-11 to 2.50e-11) | 3.471 | +5065.8 | 0.169 | +1541.8 | 0.144 |
| form B: g_bar + √(g_bar a_acc) | 1 | 7.72e-11 (7.08e-11 to 8.39e-11) | 1.579 | +209.0 | 0.129 | +225.6 | 0.118 |
| form S: g_bar/2 + √(g_bar²/4 + g_bar a_acc) | 1 | 1.10e-10 (1.02e-10 to 1.19e-10) | 1.542 | -5.5 | 0.123 | -2.6 | 0.118 |

Median residual log(g_obs/g_model) in dex, by acceleration range:

| model | g_bar < 1e-11 | 1e-11 to 1e-10 | 1e-10 to 1e-9 | > 1e-9 |
|---|---|---|---|---|
| rar | -0.007 | +0.013 | +0.012 | -0.001 |
| const | -0.020 | +0.141 | +0.085 | +0.003 |
| brown | +0.020 | -0.012 | -0.070 | -0.079 |
| simple | -0.004 | +0.011 | -0.003 | -0.019 |

- Galaxy by galaxy (lower -2 ln L under the universal fits, 147 galaxies): RAR over B in 84, RAR over S in 73, S over B in 83, B over the constant in 101, S over the constant in 109.
- Low-acceleration slope of log(g_obs - g_bar) in the bins of `sparc_rotation.py` S2d: data 0.436; RAR 0.448; form B 0.500 (exactly 1/2 by construction); form S 0.449; constant 0.

**Solar system.** Both forms are pointwise laws in g_bar. In the Sun's field the extra force of form B is √(GM a_acc)/r (an extra log potential), and that of form S tends to the constant a_acc. A small radial force k rⁿ advances the perihelion by -π(n+2)ε per orbit, ε being its ratio to GM/r² (checked here by integrating an orbit). Against the extra perihelion precessions allowed by the EPM2011 ephemerides (Pitjeva and Pitjev 2013, Table 4; their uncertainties taken as bounds):

| planet | g_sun [m/s²] | form B [mas/yr] | × bound | form S [mas/yr] | × bound | bound [mas/yr] |
|---|---|---|---|---|---|---|
| Mercury | 3.96e-02 | -1.19e+05 | 4e+06 | -1.49e+01 | 5e+02 | 0.03 |
| Venus | 1.13e-02 | -8.69e+04 | 5e+06 | -2.04e+01 | 1e+03 | 0.016 |
| Earth | 5.93e-03 | -7.39e+04 | 4e+07 | -2.40e+01 | 1e+04 | 0.0019 |
| Mars | 2.55e-03 | -5.99e+04 | 2e+08 | -2.96e+01 | 8e+04 | 0.00037 |
| Jupiter | 2.19e-04 | -3.24e+04 | 1e+05 | -5.48e+01 | 2e+02 | 0.283 |
| Saturn | 6.52e-05 | -2.39e+04 | 5e+06 | -7.41e+01 | 2e+04 | 0.0047 |

The RAR function switches off exponentially (its excess at Saturn is of order 10^-331 of g), so the RAR itself is untouched; MOND's external-field effect is a separate issue not treated here.

## R1b: parameter-free scales

Systematics on log a_acc: galaxy bootstrap 0.037 (B) and 0.034 (S) dex; stellar M/L shifted by ±0.1 dex: 0.126 and 0.105; likelihood choice (L1, L2, robust): 0.004 and 0.008; total 0.131 and 0.110 dex. SPARC's 97 Hubble-flow distances assume H0 = 73; rescaled to 67.4 they give a_acc = 7.18e-11 (B) and 1.03e-10 (S). Each H0 = 67.4 candidate is compared with the rescaled data, each H0 = 73 candidate and c/t0 with SPARC's own distances. ΔBIC is against the form's own best fit on the same data (a fixed scale has k = 0).

| candidate | value [m/s²] | B: a_acc / candidate | B: ΔBIC | S: a_acc / candidate | S: ΔBIC | RAR g† / candidate |
|---|---|---|---|---|---|---|
| c H0 (H0 = 67.4) | 6.55e-10 | 0.110 | +36759.1 | 0.158 | +31774.4 | 0.161 |
| c H0 / 2π (H0 = 67.4) | 1.04e-10 | 0.689 | +777.5 | 0.990 | -7.2 | 1.009 |
| c H_inf (H0 = 67.4) | 5.42e-10 | 0.132 | +29978.9 | 0.190 | +25096.2 | 0.194 |
| c H_inf / 2π (H0 = 67.4) | 8.63e-11 | 0.832 | +176.1 | 1.196 | +218.7 | 1.219 |
| c H0 (H0 = 73) | 7.09e-10 | 0.109 | +37609.6 | 0.155 | +32702.7 | 0.158 |
| c H0 / 2π (H0 = 73) | 1.13e-10 | 0.684 | +826.8 | 0.973 | -2.5 | 0.992 |
| c H_inf (H0 = 73) | 5.87e-10 | 0.131 | +30709.2 | 0.187 | +25896.4 | 0.191 |
| c H_inf / 2π (H0 = 73) | 9.34e-11 | 0.826 | +195.5 | 1.176 | +181.1 | 1.198 |
| c / t0 (t0 = 13.8 Gyr) | 6.88e-10 | 0.112 | +36466.6 | 0.160 | +31570.1 | 0.163 |

**Look-elsewhere.** The 9 candidates span 0.91 dex with a median spacing of 0.035 dex; they form two clusters (with and without 2π) a factor 2π apart. For form S the nearest is c H0 / 2π (H0 = 73) at 0.012 dex (0.11 σ_tot); 4 candidates lie within 2σ_tot. A log-uniform scale within ±1 dex of the fitted value lands within 0.012 dex of some candidate with probability 0.10, and within 1σ_tot with probability 0.34. For form B: nearest c H_inf / 2π (H0 = 67.4) at 0.048 dex, probability 0.21, 4 candidates within 2σ. The measurement cannot pick one of the 2π-scales over another, and picking the closest after the fit is not a test. The match a0 ≈ cH0/2π is Milgrom's (1983) observation, not a consequence of the accumulation hypothesis, which gives no factor 2π. The scales without 2π, which a horizon argument would give (cH0, cH_inf = Bridge A, c/t0), are excluded.

## R1c: a_acc per galaxy

| per-galaxy scale | median [m/s²] | spread [dex] | median error [dex] | intrinsic scatter τ [dex] (68%) | Δ(-2 ln L) of τ = 0 | Spearman vs log M_bar | slope vs log M_bar (16-84%) |
|---|---|---|---|---|---|---|---|
| a_acc, form B | 6.42e-11 | 0.399 | 0.369 | 0.226 (0.196 to 0.258) | 52.9 | -0.23 (p = 6.9e-03) | -0.110 (-0.159 to -0.065) |
| a_acc, form S | 1.02e-10 | 0.300 | 0.317 | 0.203 (0.177 to 0.229) | 61.6 | -0.05 (p = 5.5e-01) | -0.008 (-0.044 to +0.027) |
| g†, RAR | 1.06e-10 | 0.293 | 0.312 | 0.201 (0.176 to 0.227) | 62.7 | -0.02 (p = 8.0e-01) | +0.003 (-0.031 to +0.037) |

- Against the per-galaxy error estimates (stat ⊕ whole-galaxy shifts) none of the three scales is consistent with a single value without extra scatter; the RAR's g† (τ = 0.20 dex) scatters as much as form S's a_acc (τ = 0.20). But the same estimator applied to mock universes with a universal RAR gives τ = 0.11 (0.02 to 0.20) for a_acc and 0.04 (0.00 to 0.10) for g†. The data's τ is above what a universal law produces through this error model (Υ varying by 0.1 dex between galaxies, the catalogue's distance and inclination errors, HI at 10%), for g† as much as for a_acc of form S: either the error model misses a galaxy-level term, such as a larger spread of M/L, or neither scale is universal. Li, Lelli, McGaugh and Schombert (2018), who marginalise each galaxy over M/L, distance and inclination, find no credible variation of g†; Rodrigues et al. (2018) argue the opposite with a different treatment. On this question form S and the RAR stand or fall together. Mass trends (Spearman): form B -0.23, form S -0.05, RAR -0.02; a falling a_acc of form B with mass is what its overshoot at high acceleration would produce in massive, high-acceleration galaxies.
- Shape within galaxies (one free scale per galaxy, velocity errors, 2652 points): χ² = 26790 (RAR), 28002 (S), 41734 (B); the RAR shape is better than B in 70 and than S in 65 of 132 galaxies.

## R2: history dependence

A universal a_acc carries no history beyond the global cosmic time. A galaxy-specific accumulation would make older, more evolved, dynamically older systems carry a larger a_acc: negative correlations with Hubble type, gas fraction and disk scale length, positive ones with surface brightness and with N_orb, the orbits completed at the outermost radius in 13.8 Gyr (median 17, 16-84%: 10 to 27); a fixed variance per orbit gives a_acc ∝ N_orb. Spearman ρ with the galaxy-bootstrap 95% interval, Holm-adjusted p over all 30 tests (15 raw, 15 partial at fixed log M_bar), and the 95% band of ρ in mock universes in which the true law is the universal RAR (null R) or the universal form B (null B), observed through the SPARC error model. The last column tests the shift of the observed ρ (raw / partial) from the null-R mean against the data's own bootstrap spread, Holm-adjusted over all 30:

| quantity | proxy | ρ (95%) | p (Holm) | null R | null B | partial ρ (95%) | p (Holm) | null R | shift from null R: p (Holm), raw / partial |
|---|---|---|---|---|---|---|---|---|---|
| log a_acc (B, per galaxy) | Hubble type T | +0.12 (-0.06, +0.30) | 1 | +0.05 to +0.37 | -0.18 to +0.17 | -0.14 (-0.30, +0.03) | 1 | -0.10 to +0.22 | 1 / 0.54 |
| log a_acc (B, per galaxy) | gas fraction | +0.21 (+0.03, +0.38) | 0.45 | +0.09 to +0.42 | -0.17 to +0.18 | +0.04 (-0.12, +0.21) | 1 | -0.02 to +0.30 | 1 / 1 |
| log a_acc (B, per galaxy) | log SB_eff | -0.16 (-0.33, +0.01) | 1 | -0.40 to -0.06 | -0.18 to +0.19 | +0.03 (-0.15, +0.21) | 1 | -0.27 to +0.05 | 1 / 1 |
| log a_acc (B, per galaxy) | log R_disk | -0.20 (-0.37, -0.02) | 0.56 | -0.31 to +0.00 | -0.15 to +0.16 | -0.01 (-0.19, +0.17) | 1 | -0.09 to +0.21 | 1 / 1 |
| log a_acc (B, per galaxy) | log N_orb | +0.12 (-0.06, +0.28) | 1 | -0.17 to +0.15 | -0.17 to +0.15 | -0.00 (-0.18, +0.18) | 1 | -0.30 to +0.01 | 1 / 1 |
| mean residual from universal B [dex] | Hubble type T | +0.10 (-0.09, +0.29) | 1 | +0.05 to +0.38 | -0.17 to +0.17 | -0.10 (-0.27, +0.09) | 1 | -0.09 to +0.24 | 1 / 1 |
| mean residual from universal B [dex] | gas fraction | +0.18 (+0.00, +0.36) | 1 | +0.08 to +0.41 | -0.18 to +0.18 | +0.05 (-0.11, +0.22) | 1 | -0.04 to +0.29 | 1 / 1 |
| mean residual from universal B [dex] | log SB_eff | -0.15 (-0.31, +0.02) | 1 | -0.40 to -0.06 | -0.18 to +0.18 | +0.01 (-0.17, +0.18) | 1 | -0.27 to +0.06 | 1 / 1 |
| mean residual from universal B [dex] | log R_disk | -0.16 (-0.33, +0.03) | 1 | -0.31 to +0.01 | -0.16 to +0.16 | -0.01 (-0.19, +0.17) | 1 | -0.08 to +0.22 | 1 / 1 |
| mean residual from universal B [dex] | log N_orb | +0.13 (-0.05, +0.29) | 1 | -0.16 to +0.16 | -0.17 to +0.16 | +0.03 (-0.14, +0.20) | 1 | -0.29 to +0.02 | 1 / 1 |
| log g+ (RAR, per galaxy) | Hubble type T | -0.11 (-0.29, +0.09) | 1 | -0.18 to +0.17 | -0.38 to -0.06 | -0.22 (-0.39, -0.05) | 0.33 | -0.18 to +0.16 | 1 / 0.35 |
| log g+ (RAR, per galaxy) | gas fraction | -0.06 (-0.23, +0.12) | 1 | -0.18 to +0.18 | -0.42 to -0.08 | -0.13 (-0.28, +0.04) | 1 | -0.16 to +0.17 | 1 / 1 |
| log g+ (RAR, per galaxy) | log SB_eff | +0.09 (-0.08, +0.26) | 1 | -0.18 to +0.19 | +0.06 to +0.39 | +0.17 (-0.00, +0.34) | 1 | -0.18 to +0.17 | 1 / 1 |
| log g+ (RAR, per galaxy) | log R_disk | -0.06 (-0.23, +0.13) | 1 | -0.17 to +0.17 | +0.00 to +0.30 | -0.07 (-0.25, +0.11) | 1 | -0.15 to +0.15 | 1 / 1 |
| log g+ (RAR, per galaxy) | log N_orb | +0.16 (+0.00, +0.32) | 1 | -0.17 to +0.17 | -0.15 to +0.17 | +0.17 (+0.01, +0.33) | 1 | -0.18 to +0.17 | 1 / 0.9 |

- Significant after Holm (p < 0.05): 0 of 15 raw and 0 of 15 partial correlations against zero; 0 raw and 0 partial against the null-R mean. Outside the null-R 95% band: 0 of 15 raw and 6 of 15 partial ρ (about 0.75 of 15 expected by chance). The bands come from mocks that lack the extra galaxy-to-galaxy scatter of R1c (error-weighted τ of g† 0.04 dex in the mocks against 0.20 in the data), so they understate the null spread of the partial correlations; the shift test, which uses the data's own bootstrap spread, is the fair one, and after Holm it finds no departure. The largest, unadjusted: log g+ vs Hubble type T, partial ρ -0.22 (Holm p 0.35); log a_acc vs Hubble type T, partial ρ -0.14 (Holm p 0.54).
- log a_acc (form B) against log N_orb: slope +0.121 (95%: -0.173 to +0.457); a per-orbit random walk predicts +1, a universal scale 0.
- The null means are not zero. A universal law observed through the error model, and fitted per galaxy with a shape that differs from the truth, already correlates with proxies that track where on the g_bar axis a galaxy's points lie (mass, surface brightness, gas fraction). A correlation is evidence for history only if it departs from that baseline; and the mocks contain only the error terms listed (no M/L variation correlated with type, no non-Gaussian outliers), so even a departure would first point to an unmodelled systematic before it pointed to history.

## R3: the contained remnant (halos)

Per-galaxy fits on the 132 galaxies, likelihood L1 for every model. Universal models carry their one global parameter from the fit to all points; per-galaxy BIC counts k = 0 for them, 1 for a free scale, 2 for a halo.

| model | parameters (total) | -2 ln L | ΔBIC (total) vs universal RAR | galaxies better than universal RAR | than universal B |
|---|---|---|---|---|---|
| RAR, universal g† | 1 | -2478.0 | +0.0 | 0 | 78 |
| form S, universal a_acc | 1 | -2482.6 | -4.6 | 64 | 77 |
| form B, universal a_acc | 1 | -2259.9 | +218.1 | 54 | 0 |
| constant, universal | 1 | 2525.2 | +5003.2 | 34 | 43 |
| RAR, g† per galaxy | 132 | -5393.8 | -1883.2 | 85 | 95 |
| form B, a_acc per galaxy | 132 | -5069.6 | -1559.0 | 78 | 90 |
| NFW + c-M prior | 264 | -5911.6 | -1360.4 | 88 | 96 |
| NFW + c-M + stellar-to-halo prior | 264 | -5659.1 | -1107.8 | 82 | 89 |
| Burkert | 264 | -6331.5 | -1780.3 | 98 | 107 |

- Halo parameters (16/50/84%): NFW log M200 10.76 / 11.47 / 12.18, log c200 0.84 / 0.97 / 1.09; median log(M200/M_bar) 1.38 (with the stellar-to-halo prior 1.50). Fits at a parameter bound: NFW 0, cosmological NFW 0, Burkert 1.
- The point-wise likelihood treats the galaxy-wide distance and inclination errors as independent per point, so any per-galaxy parameter gains by absorbing them. One free RAR scale per galaxy is the fair yardstick for what such freedom buys: against it NFW (+c-M) has ΔBIC +523, cosmological NFW +775, Burkert +103. Cored halos fit better than cuspy ones with the same parameter count (Burkert against NFW: ΔBIC -420), the known cusp-core issue. The halos accommodate the RAR's one-parameter regularity with two parameters per galaxy; they do not predict it.

## R4: halos and a universal stochastic term together

| halo + term | best A [m/s²] | Δ(-2 ln L) best - zero | ΔBIC of adding the term | 95% bound on A | bootstrap 50 / 84% of the bound | best at A = 0 in resamples | bound / R1 value | share of dark acceleration at outer radius (at bootstrap-84% bound) |
|---|---|---|---|---|---|---|---|---|
| nfw_cm+const | 0 | +0.0 | +7.9 | 8.42e-13 | 9.26e-13 / 3.53e-12 | 86% | 3.7e-02 | 16.2% |
| nfw_cm+sqrt | 0 | +0.0 | +7.9 | 2.07e-15 | 1.89e-15 / 6.51e-15 | 97% | 2.7e-05 | 1.0% |
| nfw_shmr+const | 6.62e-13 | -4.4 | +3.5 | 1.18e-12 | 1.17e-12 / 1.86e-12 | 23% | 5.2e-02 | 8.5% |
| nfw_shmr+sqrt | 0 | +0.0 | +7.9 | 2.28e-15 | 1.91e-15 / 2.96e-14 | 87% | 2.9e-05 | 2.1% |
| burkert+const | 4.20e-12 | -57.9 | -50.1 | 5.09e-12 | 5.17e-12 / 6.66e-12 | 0% | 2.2e-01 | 30.5% |
| burkert+sqrt | 0 | +0.0 | +7.9 | 1.34e-14 | 1.29e-14 / 1.41e-13 | 86% | 1.7e-04 | 4.5% |

R1 values for comparison: a_acc = 7.72e-11 m/s² for the sqrt form (form B alone) and |γ1|/2 = 2.27e-11 for the constant alone. Where the best amplitude is zero, the summed -2 ln L rises roughly as √A from zero (`dm2lnL_curve` in the JSON): the halos, refitted at each A, cannot absorb the term, so it costs at first order and the bound is far below the value the term needs on its own. With Burkert halos the preferred constant is 0.19 of the value that replaces the halos.

**Consistency requirement.** The microwave background needs Ω_c h² = 0.120 ± 0.001 of collisionless matter at z ≈ 1100 (Planck 2018). If that is the contained remnant, halos of the cosmological masses exist around galaxies, and the stochastic term must not double count the dark acceleration they already supply. The bounds above are that room: with cosmological NFW halos the sqrt term can supply at most a median 2.1% of the dark acceleration at the outermost measured radius (galaxy-bootstrap 84th percentile of the bound), the constant 9%.

## R5: evolution with cosmic time

Flat ΛCDM with Ω_m = 0.315, Ω_Λ = 0.685, H0 = 67.4 (t0 = 13.80 Gyr without radiation). In the deep regime v⁴ = G M a, so at fixed rotation speed log M_bar(z) - log M_bar(0) = -log(a(z)/a(0)). The high-redshift disks are not in the deep regime (Milgrom 2017 puts the z ≈ 1-2.4 galaxies of Genzel et al. at 3-11 a0 at their half-light radii), so the table also gives the shift for a RAR-shaped law at fixed V and R with g_obs = 3 g† and 10 g†, where any change of scale is diluted.

| law for a_acc(z) | a(z)/a(0) at z = 0.9 / 1 / 2 / 2.3 | Δlog M_bar, deep, z = 0.9 / 2.3 | at g_obs = 3 g† | at 10 g† |
|---|---|---|---|---|
| constant | 1.00 / 1.00 / 1.00 / 1.00 | -0.00 / -0.00 | +0.00 / +0.00 | +0.00 / +0.00 |
| H(z) | 1.69 / 1.79 / 3.03 / 3.46 | -0.23 / -0.54 | -0.07 / -0.22 | -0.03 / -0.09 |
| 1/t | 2.20 / 2.36 / 4.21 / 4.85 | -0.34 / -0.69 | -0.12 / -0.31 | -0.04 / -0.14 |
| t (accumulation) | 0.45 / 0.42 / 0.24 / 0.21 | +0.34 / +0.69 | +0.07 / +0.10 | +0.02 / +0.02 |

Published measurements (numbers verified against the papers' text):

- **Ubler et al. (2017), KMOS3D.** Baryonic Tully-Fisher relation with the slope fixed at 3.75 (Lelli et al. 2016), zero-point offsets from the local relation Δb = -0.44 ± 0.04 dex at z ≈ 0.9 (65 galaxies) and -0.27 ± 0.05 at z ≈ 2.3 (46); without their pressure-support correction -0.33 and -0.09. Baryonic masses carry ~0.15 dex each (stellar 0.15, gas 0.20, Chabrier IMF); gas masses come from scaling relations and omit atomic gas; the velocity is the model's peak, assumed comparable to the local Vflat. The errors quoted are statistical only. Read as a change of scale they imply a(z)/a(0) = 2.8 (deep) to 7.6 (3 g†) at z ≈ 0.9 and 1.9 to 4.2 at z ≈ 2.3: non-monotonic, so no single law fits both, and the authors explain the offsets in ΛCDM by evolving gas and dark matter fractions.
- **MUSE-DARK III (Ciocan et al. 2026).** The RAR of 79 star-forming galaxies at 0.33 < z < 1.44: a0(z ≈ 1) = 2.38 (+0.12, -0.10) × 10⁻¹⁰ m/s², a factor 1.98 ± 0.44 above the local 1.2 ± 0.26; their linear fit a0(z) = 1.0 + 1.59 z (10⁻¹⁰ m/s²) gives 2.59 at z = 1. Caveats they state: a_tot and a_bar come from the same 3D model, molecular gas adds ~0.2 dex of systematic uncertainty, and the linear form is phenomenological.
- **Milgrom (2017)**, on the six rotation curves of Genzel et al. (2017) at z ≈ 0.9-2.4: the data "all but exclude" a MOND constant of ~4 a0 at z ≈ 2 and exclude a0 ∝ (1+z)^3/2.
- **RC100 (Nestor Shachar et al. 2023)**: dark-matter fractions within R_e of 0.38 ± 0.23 (z = 0.6-1.2, 33 galaxies) and 0.27 ± 0.18 (z = 1.2-2.5, 67), quoted as median ± scatter; not turned into an a(z) here, because that needs each galaxy's own g_bar. Del Popolo and Chan (2024) use a0 estimates for these galaxies and find, with large uncertainties, an anti-correlation with z within that sample. MIGHTEE-HI (Vărăşteanu et al. 2025) reports tentative evolution with 19 galaxies at z < 0.08, where every law here changes a by less than 10%.

Comparison: at z = 1, MUSE-DARK's 2.0 ± 0.4 sits between H(z) (1.79) and 1/t (2.36); accumulation (0.42) and a constant are below it. At z = 2, 1/t (4.2) meets Milgrom's exclusion of ~4 a0. The Ubler offsets have the sign of a scale that was larger in the past, opposite to accumulation. Read in the deep regime, the offset at z ≈ 0.9 is larger and the one at z ≈ 2.3 smaller than either falling law predicts, and the implied ratio falls between z ≈ 0.9 and 2.3, which no monotonic law does. The two time arrows disagree in principle: an accumulated quantity grows with time, while the cosmological coincidence scales cH and c/t fall. Matching a_acc(t0) to cH0/2π and making it accumulate cannot both hold except as a coincidence of the present epoch.

## R6: what cannot be fitted

- **Microwave background.** The acoustic peaks need Ω_c h² = 0.120 of pressureless matter at z ≈ 1100, with the baryons already at their present share. A stochastic term in the Newtonian limit of a static, spherical calculation has no cosmological perturbation theory: there is no prediction for the peaks to fit. The contained remnant is cold dark matter and fits them as ΛCDM does.
- **Weak and strong lensing.** Light deflection needs the metric, not only the Newtonian potential; Oppenheim and Russo state that lensing is not yet addressed. Nothing to fit. Halos lens as in ΛCDM.
- **Cluster masses.** MOND-like laws reduce the clusters' mass discrepancy but do not remove it (Sanders 2003: the discrepancy becomes three to four times smaller than with Newtonian dynamics). Forms B and S inherit that residual; a cluster test would need the X-ray and lensing profiles and was not run.
- **Bullet Cluster.** The lensing mass of 1E0657-558 follows the galaxies, offset from the X-ray gas at 8σ (Clowe et al. 2006). A term that depends only on the local baryonic field points at the gas; collisionless halos follow the galaxies, as observed.
- **The solar system** (R1a) is the one regime outside galaxies where the forms make a definite prediction, and it fails.

## Caveats

- All fits use Υ_disk = 0.5 and Υ_bulge = 0.7 (as `sparc_rotation.py`), M* = 0.5 L[3.6] for the stellar-to-halo prior (bulge light included at the disk value), and the point-wise likelihood L1, which overstates differences between models; the galaxy bootstrap is the conservative measure.
- Halos are fitted with fixed Υ; letting Υ float with a prior (as published halo catalogues do) improves halo fits, and would also improve the universal laws. The Moster et al. relation was derived with a WMAP7 cosmology; how well it is constrained at the lowest stellar masses of SPARC was not checked here. NFW halos are not adiabatically contracted.
- The high-redshift comparison uses published summary numbers; their systematic uncertainties are comparable to the predicted effects, and their samples are massive, baryon-dominated star-forming disks selected differently from SPARC.
- The accumulation hypothesis is not derived from the classical-quantum dynamics: Oppenheim and Russo's mean metric is static and spherically symmetric, and their linear term is fixed by a boundary condition, not by a history.

## Reproduce

```
python3 docs/simulation/remnant_history.py --data <dir with MassModels_Lelli2016c.mrt and SPARC_Lelli2016c.mrt>
```

Needs numpy, scipy and matplotlib and `docs/simulation/sparc_rotation.py` next to it. `--boot N` and `--mock N` set the resample counts. Deterministic (fixed seeds, one BLAS thread); a few minutes on one core and well under 1 GB of memory.

## References

Marked *verified* where the record and the numbers used were checked on 2026-10-31 against the arXiv text or record, the publisher page or ADS, by web search.

1. F. Lelli, S. S. McGaugh, J. M. Schombert, *SPARC: Mass Models for 175 Disk Galaxies with Spitzer Photometry and Accurate Rotation Curves*, AJ 152, 157 (2016), arXiv:1606.09251. *Verified*: 97 Hubble-flow distances on H0 = 73 km/s/Mpc (the table has 97 with f_D = 1).
2. S. S. McGaugh, F. Lelli, J. M. Schombert, PRL 117, 201101 (2016), arXiv:1609.05917; F. Lelli et al., ApJ 836, 152 (2017), arXiv:1610.08981. Cuts, RAR function and error model, as verified in `sparc_rotation.md`.
3. J. Oppenheim, A. Russo, *Anomalous contribution to galactic rotation curves due to stochastic spacetime*, arXiv:2402.19459 (v3, 22 July 2024; no journal reference). *Verified* (record): static, spherically symmetric, further study needed.
4. Planck Collaboration, *Planck 2018 results. VI. Cosmological parameters*, A&A 641, A6 (2020), arXiv:1807.06209. *Verified*: H0 = 67.4 ± 0.5, Ω_m = 0.315 ± 0.007, Ω_c h² = 0.120 ± 0.001. (Ω_Λ = 0.685 is 1 - Ω_m.)
5. A. A. Dutton, A. V. Macciò, *Cold dark matter haloes in the Planck era*, MNRAS (2014), doi:10.1093/mnras/stu742, arXiv:1402.7073. *Verified*: Eq. 8, log c200 = 0.905 - 0.101 log(M200/10¹² h⁻¹ Msun) at z = 0, scatter 0.11 dex, Planck h = 0.671.
6. B. P. Moster, T. Naab, S. D. M. White, *Galactic star formation and accretion histories from matching galaxies to dark matter haloes*, MNRAS 428, 3121 (2013), arXiv:1205.5807. *Verified*: Eq. 2 and Table 1 (log M1 = 11.590, N = 0.0351, β = 1.376, γ = 0.608), 0.15 dex scatter, M200c, Chabrier IMF, WMAP7.
7. E. V. Pitjeva, N. P. Pitjev, *Relativistic effects and dark matter in the Solar system from observations of planets and spacecraft*, MNRAS 432, 3431 (2013), arXiv:1306.3043. *Verified*: Table 4, extra perihelion precessions (Mars -0.00020 ± 0.00037, Saturn -0.0032 ± 0.0047 mas/yr).
8. H. Ubler et al., *The evolution of the Tully-Fisher relation between z ~ 2.3 and z ~ 0.9 with KMOS3D*, ApJ 842, 121 (2017), arXiv:1703.04321. *Verified*: Table 2, Fig. 5 and Sects. 2.2, 4.2, 4.3 (Δb = -0.44 and -0.27 dex, ±0.04 and ±0.05; -0.33 and -0.09 without pressure support; mass uncertainties).
9. B. I. Ciocan et al., *MUSE-DARK III: The evolution of the radial acceleration relation at intermediate redshifts*, A&A 709, L16 (2026), arXiv:2604.22613. *Verified*: a0(z~1) = 2.38 (+0.12, -0.10) × 10⁻¹⁰ m/s², a0(z) = 1.0 + 1.59 z, local 1.2 ± 0.26, caveats.
10. M. Milgrom, *High-redshift rotation curves and MOND*, arXiv:1703.06110 (v3, 2017). *Verified* (abstract): 3-11 a0 at half-light radii; ~4 a0 at z ~ 2 all but excluded; a0 ∝ (1+z)^3/2 excluded.
11. A. Nestor Shachar et al., *RC100: Rotation Curves of 100 Massive Star-forming Galaxies at z = 0.6-2.5 Reveal Little Dark Matter on Galactic Scales*, ApJ 944, 78 (2023), arXiv:2209.12199. *Verified*: f_DM(R_e) medians 0.38 ± 0.23 and 0.27 ± 0.18, bins and counts.
12. A. Del Popolo, M. H. Chan, *On the time dependency of a0*, Phys. Dark Univ. 43, 101393 (2024), arXiv:2405.01841. *Verified* (abstract).
13. A. A. Vărăşteanu et al., *MIGHTEE-HI: The radial acceleration relation with resolved stellar mass measurements*, MNRAS (2025), doi:10.1093/mnras/staf1079, arXiv:2504.20857. *Verified* (abstract): 19 galaxies to z = 0.08, tentative evolution.
14. P. Li, F. Lelli, S. S. McGaugh, J. M. Schombert, *Fitting the radial acceleration relation to individual SPARC galaxies*, A&A 615, A3 (2018), arXiv:1803.00022. *Verified* (abstract): no credible variation of the acceleration scale.
15. D. C. Rodrigues, V. Marra, A. del Popolo, Z. Davari, *Absence of a fundamental acceleration scale in galaxies*, Nat. Astron. 2, 668 (2018), arXiv:1806.06803. *Verified* (abstract).
16. R. H. Sanders, *Clusters of galaxies with modified Newtonian dynamics*, MNRAS 342, 901 (2003), arXiv:astro-ph/0212293. *Verified* (abstract): discrepancy three to four times smaller, not removed.
17. D. Clowe et al., *A direct empirical proof of the existence of dark matter*, ApJ 648, L109 (2006), arXiv:astro-ph/0608407. *Verified* (abstract): 8σ offset.
18. M. Milgrom, ApJ 270, 365 (1983): a0 ≈ cH0/2π; record verified in `sparc_rotation.md`.

