# SPARC rotation curves against GUID's stochastic remnant

Workstream of *GUID v6: Our theory as simulated*. Written by `docs/simulation/sparc_rotation.py` from one run (seed 20161101, 1000 bootstrap resamples over galaxies); every number is also in `sparc_rotation.json`. Figures: `docs/simulation/figures/sparc_rar.pdf`, `sparc_residuals.pdf`, `sparc_gamma1.pdf`, `sparc_btfr.pdf`. Checks: **39 of 39 passed** (pipeline reproduction and internal consistency; the model comparisons are results, not checks).

The model under test is the paper's stochastic remnant (Section 11.6, after Oppenheim and Russo): v² = GM/r + |γ1| r/2 - γ2 r², so the observed centripetal acceleration should be g_obs = g_bar + |γ1|/2 - γ2 R, a constant extra acceleration on top of the Newtonian one from the baryons.

## Verdict

- **Pipeline (S1).** The radial acceleration relation of McGaugh, Lelli and Schombert (2016) is reproduced: the same 153 galaxies, 2696 points (paper: 2693), rms scatter 0.133 dex (0.13), Gaussian width 0.110 dex (0.11). The acceleration scale comes out g† = 1.10 ± 0.02 (10⁻¹⁰ m/s²) against the published 1.20 ± 0.02 (stat) ± 0.24 (sys): inside the published total uncertainty, but not within three times the quoted random error. The value depends on the fitting choice (1.02 to 1.27 across six choices, see S1).
- **One universal |γ1| (S2a)** fits worse than the RAR's one-parameter function. The best fit is |γ1| = 4.54e-11 m/s² (galaxy bootstrap 16-84%: 4.15e-11 to 4.98e-11). ΔBIC against the RAR = **+5066** with the stated errors and +1542 when each model fits its own intrinsic scatter (RAR 0.123 dex, constant 0.169 dex). The RAR fits better in 109 of 147 galaxies. Newton alone is far worse than both (ΔBIC +52645).
- **Bridge A (S2b) is excluded.** |γ1| = 4.88e-10 to 5.42e-10 m/s² with no free parameter puts the model above the data at 98% of points, by a median 0.59 dex (0.97 dex where g_bar < 1e-11). χ²/N = 96; ΔBIC against the RAR is +254651. It is 11 times the best universal value and 8 times the per-galaxy median. In the turnover relation v*⁴ = 2GM|γ1| its v⁴ at fixed mass is 6.4 to 7.1 times the observed (the paper's crude estimate: 8). At the galaxies' outermost measured radii, where its curve is still rising, the overshoot is a factor 80 to 98 in v⁴.
- **The excess is not constant (S2d).** At low acceleration (g_bar < 1.12e-11 m/s²) the excess Δg = g_obs - g_bar rises with g_bar with logarithmic slope **0.44** [0.39, 0.49]. A constant predicts 0, the RAR 0.45 in the same bins, deep MOND 0.5. Fitting g_obs = g_bar + K (g_bar/1e-10)^p to all points gives p = 0.44 [0.40, 0.46]; p = 0 is rejected by ΔBIC = 4983.
- **Per galaxy (S2c)** |γ1| has median 5.95e-11 m/s² (close to a0/2 = 6e-11) and a spread of 0.25 dex. 131 of 132 galaxies lie below Bridge A beyond their errors. |γ1| rises with baryonic mass (Spearman 0.45, slope 0.14 in log-log) and with Vflat (Spearman 0.61, slope 0.69). That is far slower than Oppenheim and Russo's γ1 ∝ (1 + M/10¹⁰ Msun), which is worse than a constant (ΔBIC +122 on the per-galaxy values; on all points ΔBIC against the RAR is +19789). Within each galaxy, a free constant fits the shape worse than a free RAR scale in 98 of 132 galaxies.
- **BTFR (S3)** is reproduced: slope 3.67 ± 0.10 (paper 3.71 ± 0.08), log A = 2.36 ± 0.21 (2.27 ± 0.18). Read through the idealised turnover relation v*⁴ = 2GM|γ1|, the normalisation would need |γ1| = 7.95e-11 m/s²; Bridge A is 6.1 times that. But v* is the minimum of the model curve, and Vflat is measured further out. Predicted from each galaxy's own baryons at its outermost radius, the best universal constant gives Vflat with median offset +0.006 dex and rms 0.087 dex (RAR: +0.014, 0.061 dex). The constant gets the outer normalisation right on average, but with more scatter than the RAR and a trend with mass (Spearman -0.42 against the RAR's -0.08): it overshoots small galaxies and undershoots large ones. It also fails in the shape of the curves (S2a, S2d).

## Data and cuts

SPARC (Lelli, McGaugh and Schombert 2016): 175 galaxies, 3391 rotation-curve points. Files are checked by SHA256 before use and are not copied into this repository:

- `MassModels_Lelli2016c.mrt`: `9108994b12cc401b94a1768beca61c53ec354779385c9c9cc571049f3043244c`
- `SPARC_Lelli2016c.mrt`: `5aa0501f6b0d881fa579030e315e7b5b6ef561a5bd3a07472f9929c7e5728243`

- RAR sample (S1, S2): quality flag Q < 3 removes 12 galaxies, inclination i ≥ 30° removes 10 more, leaving 153 (paper: 153). Points with δV/V < 0.1: 2696 of 3168 (paper: 2693 of 3149). In this release 6 galaxies have no point that precise (UGC05005, UGC07559, UGC07577, UGC07866, UGC09992, UGCA444), so 147 galaxies contribute points.
- g_obs = V_obs²/R; g_bar = (V_gas|V_gas| + Υ_d V_disk|V_disk| + Υ_b V_bul|V_bul|)/R with Υ_d = 0.5, Υ_b = 0.7 (3.6 µm).
- Errors (Lelli et al. 2017, Eq. 2 and Sect. 2.1.2): δg_obs/g_obs = [(2δV/V)² + (2δi/tan i)² + (δD/D)²]^½; δg_bar from 10% on the HI flux and 25% on Υ. Mean errors 0.104 dex on g_obs and 0.089 dex on g_bar (paper: 0.1 and 0.08).
- Per-galaxy fits (S2c): galaxies with at least 5 points (132).
- BTFR (S3): Vflat > 0, i ≥ 30°, without the 8 starburst dwarfs of Lelli et al. (2014) and Holmberg II (UGC 4305), as in the 2016 letter. That leaves 124 galaxies; the letter had 118, and the public table gives Vflat for more galaxies. M_bar = Υ_d L[3.6] + 1.33 M_HI with Υ_d = 0.5.

## Method

- **S1 fit:** orthogonal-distance regression of log g_obs = log F(g_bar), F = g_bar/(1 - exp(-√(g_bar/g†))), with errors in both variables, on the individual points. The papers used scipy.odr; this script does the same minimisation itself (scipy.odr is deprecated) and is checked against scipy.odr to 1e-3.
- **Likelihood L1 (primary):** Gaussian in log₁₀ g_obs. The variance of each point is the full error model: δg_obs plus δg_bar carried through the model's slope (effective variance). -2 ln L = Σ[r²/σ² + ln 2πσ²]; BIC = -2 ln L + k ln N, with N = 2696.
- **Likelihood L2:** Gaussian in log₁₀ g_obs with the velocity errors only plus a free intrinsic floor σ_int, fitted per model (k + 1 parameters).
- **Robust version:** the L1 residuals with a soft-L1 loss (scipy least_squares); scatter quoted as 1.4826 MAD in dex.
- **Uncertainties:** galaxies are resampled with replacement (bootstrap). Points within a galaxy share distance, inclination and Υ errors, so point-wise χ² differences overstate significance; the bootstrap and the galaxy-by-galaxy counts are the conservative measures.
- **Λ term:** γ2 = Λc²/3 = 3.27e-36 s⁻² (Planck 2018 values as in `checks.py`) is kept in the model. It is at most 7.0e-04 of g_obs at any point (largest at R = 108 kpc), and dropping it moves the best |γ1| by -6.7e-05.

## S1: the radial acceleration relation reproduced

| quantity | published | here |
|---|---|---|
| galaxies after cuts (Q < 3, i ≥ 30°) | 153 | 153 |
| points before / after δV/V < 0.1 | 3149 / 2693 | 3168 / 2696 |
| galaxies with a bulge | 31 | 31 |
| g† [10⁻¹⁰ m/s²] | 1.20 ± 0.02 (stat) ± 0.24 (sys) | 1.102 ± 0.016 (ODR, χ²/dof 1.55) |
| rms scatter [dex] | 0.13 | 0.133 |
| Gaussian width of residuals [dex] | 0.11 | 0.110 (1.4826 MAD: 0.116) |
| expected scatter from errors [dex] | 0.12 | 0.130 |

g† by fitting choice (the papers name scipy.odr with errors in both variables, but not whether the fit is in log or linear space):

| fit | g† [10⁻¹⁰ m/s²] |
|---|---|
| odr log full errors (primary) | 1.102 |
| odr log velocity errors only on gobs | 1.035 |
| least squares log gobs errors | 1.162 |
| least squares log unweighted | 1.161 |
| odr linear full errors | 1.022 |
| odr linear velocity errors only on gobs | 1.266 |

The published 1.20 lies inside this range. The quoted random error (0.02) is smaller than the method dependence (about ±0.12). Tolerances: the first version of the script required 1.20 ± 3 times 0.02 and failed. The check now uses the published total uncertainty (0.24, mostly the Υ normalisation), and the 1% tolerance on the two point counts was set after seeing the counts. Both changes are stated here, and the galaxy counts reproduce exactly.

## S2a: one universal parameter, three models

| model | free | best value [m/s²] | χ² | χ²/dof | ΔBIC vs RAR (L1) | σ_int (L2) [dex] | ΔBIC vs RAR (L2) | robust MAD [dex] |
|---|---|---|---|---|---|---|---|---|
| Newton, g_bar only | 0 | - | 55985 | 20.77 | +52645 | 0.512 | +7384 | 0.310 |
| RAR, one g† | 1 | g† = 1.12e-10 [1.04e-10, 1.22e-10] | 4182 | 1.55 | 0 | 0.123 | 0 | 0.116 |
| GUID, one constant | 1 | \|γ1\| = 4.54e-11 [4.15e-11, 4.98e-11] | 9355 | 3.47 | +5066 | 0.169 | +1542 | 0.144 |
| GUID, \|γ1\| = g0 (1 + M/10¹⁰ Msun) | 1 | g0 = 1.25e-11 | 24198 | 8.98 | +19789 | | | |
| same, Oppenheim-Russo g0 = c² 10⁻²⁸ m⁻¹ | 0 | g0 = 8.99e-12 | 25708 | 9.54 | +21427 | | | |
| GUID, Bridge A (β = 0) | 0 | \|γ1\| = 4.88e-10 | 259715 | 96.3 | +254651 | | | |
| GUID, Bridge A (β → -∞) | 0 | \|γ1\| = 5.42e-10 | 288446 | 107.0 | +283359 | | | |
| g_bar + K (g_bar/10⁻¹⁰)^p | 2 | K = 7.56e-11, p = 0.436 | 4181 | 1.55 | +82 | | | |

Brackets are the galaxy-bootstrap 16-84% range. The best universal constant is set by a compromise: it overshoots the data at the lowest accelerations and falls short at intermediate ones (`sparc_residuals.pdf`, left). Formal (Hessian) errors are much smaller than the bootstrap: ±3.1e-13 on |γ1|.

## S2b: Bridge A

Bridge A fixes |γ1| = 0.9 to 1.0 c H_inf = 4.88e-10 to 5.42e-10 m/s² (paper, Section 5.4). The model lies above the data at 98% of points. The median residual log(g_obs/g_model) is -0.59 dex overall, -0.97 dex at g_bar < 1e-11 m/s², and -0.15 dex at g_bar > 1e-10 m/s²: the misfit grows as the acceleration falls, where the term dominates. χ²/N = 96 to 107. Verdict: refuted by the rotation-curve points themselves, not only by the Tully-Fisher normalisation.

## S2c: one |γ1| per galaxy

- Fit with Υ fixed (0.5/0.7) and the velocity errors per point. The distance, inclination, Υ (±25%) and HI (±10%) errors are applied as whole-galaxy shifts and refits and added in quadrature (median total error 0.18 dex).
- Distribution: median 5.95e-11 m/s², 16-84% 3.69e-11 to 1.04e-10, standard deviation 0.25 dex. Consistent with Bridge A: 1; below it: 131; above it: 0.
- Against baryonic mass: Spearman ρ = 0.45 (p = 4.4e-08), log-log slope 0.143 [0.119, 0.166]. With Υ_d free (log-normal prior of 0.11 dex around 0.5, bounded to 0.1-1.0): ρ = 0.34, slope 0.086. Part of the mass trend trades against Υ.
- Against Vflat (116 galaxies): ρ = 0.61, slope 0.69 [0.60, 0.76].
- Oppenheim and Russo (arXiv:2402.19459v3, p. 6) write, for dwarf galaxies, γ1(M) = γ1 (1 + M/10¹⁰ M_sun) with γ1 ≈ 10⁻²⁸ m⁻¹ (c = 1; times c² this is 8.99e-12 m/s², and 9.89e-11 at 10¹¹ M_sun). They take this scaling over from conformal-gravity fits; it is not derived from their path integral. On the per-galaxy values:

| law for log \|γ1\| | free | rms [dex] | BIC |
|---|---|---|---|
| constant | 1 | 0.249 | 17.2 |
| power law in M_bar | 2 | 0.215 | -16.7 |
| g0 (1 + M/10¹⁰), g0 fitted (2.04e-11) | 1 | 0.395 | 138.8 |
| g0 (1 + M/10¹⁰), their g0 | 0 | 0.531 | 212.5 |

  The (1 + M/10¹⁰) law makes |γ1| ∝ M for massive galaxies, so v*⁴ = 2GM|γ1| ∝ M², a Tully-Fisher slope of 2 where the data give 3.7. The data's |γ1| rises as about M^0.14.
- Shape within galaxies, one free parameter per galaxy for each law (velocity errors only, 2652 points): χ² = 109720 for a constant |γ1| against 26790 for a free g†. The RAR shape wins in 98 of 132 galaxies. Both χ² values are far above the number of points because the velocity errors leave out non-circular motions and the galaxy-wide errors.

## S2d: the residual pattern

A constant extra acceleration predicts Δg = g_obs - g_bar independent of g_bar. Binned medians of Δg in 0.3 dex bins of g_bar, with the galaxy bootstrap (914 points below 1.12e-11 m/s², which is g†/10):

| log g_bar (median) | Δg median [m/s²] | 16-84% (bootstrap) | points |
|---|---|---|---|
| -11.76 | 1.38e-11 | 1.33e-11 to 1.44e-11 | 48 |
| -11.50 | 1.66e-11 | 1.52e-11 to 1.78e-11 | 197 |
| -11.24 | 2.22e-11 | 2.12e-11 to 2.29e-11 | 433 |
| -10.97 | 3.04e-11 | 2.89e-11 to 3.17e-11 | 419 |
| -10.66 | 4.10e-11 | 3.88e-11 to 4.38e-11 | 350 |
| -10.35 | 5.44e-11 | 5.00e-11 to 5.81e-11 | 338 |
| -10.07 | 6.66e-11 | 5.96e-11 to 7.30e-11 | 296 |
| -9.77 | 8.37e-11 | 7.24e-11 to 1.07e-10 | 235 |
| -9.46 | 8.46e-11 | 6.65e-11 to 1.42e-10 | 177 |
| -9.16 | 6.27e-11 | 3.56e-11 to 7.77e-11 | 119 |
| -8.88 | 1.69e-11 | -3.47e-11 to 6.69e-11 | 53 |
| -8.60 | 1.68e-10 | 3.00e-11 to 3.36e-10 | 22 |

- Low-acceleration slope d log Δg / d log g_bar = 0.436 [0.390, 0.490]. The RAR predicts 0.448 in the same bins, a constant predicts 0, and deep MOND (g_obs = √(g_bar a0)) predicts 0.5.
- Point fit g_obs = g_bar + K (g_bar/10⁻¹⁰)^p: p = 0.436 [0.396, 0.464] over all points, p = 0.543 below g†/10. Against the constant (p = 0), ΔBIC = -4983 in favour of the free exponent. The two-parameter law is still worse than the one-parameter RAR (ΔBIC +82).
- At g_bar > 10⁻⁹ m/s², Δg is a small difference of large numbers and its bins are not informative.
- Mock null test of the estimator (400 mocks per truth; the error model of S1 drawn per galaxy and per point, then the same precision cut, bins, low-acceleration cut, slope estimator and galaxy bootstrap). Constant |γ1| = 4.54e-11: slope +0.005 [-0.033, +0.046] over the mocks; one mock analysed like the data gives +0.012 with bootstrap [-0.033, +0.048]; 0.000 of the null mocks reach the data's 0.436. RAR (positive control): +0.469 [+0.424, +0.518], against 0.448 without noise.

## S3: baryonic Tully-Fisher relation

| | slope s | log A [Msun (km/s)^-s] | σ_int [dex] | galaxies |
|---|---|---|---|---|
| Lelli et al. 2016, Υ = 0.5, error-weighted | 3.71 ± 0.08 | 2.27 ± 0.18 | 0.10 ± 0.02 | 118 |
| here, 2.6σ clipping as in LTS_LINEFIT | 3.67 ± 0.10 | 2.36 ± 0.21 | 0.109 | 123 (clipped: UGC07125) |
| here, no clipping | 3.65 | 2.41 | 0.119 | 124 |

Relations with slope 4, compared at the observed Vflat (median of log M_obs - log M_pred; the last column is the relation's v⁴ at fixed mass over the observed Vflat⁴):

| relation | acceleration [m/s²] | log A | median offset [dex] | rms [dex] | v⁴ pred/obs |
|---|---|---|---|---|---|
| MOND v⁴ = G M a0 | 1.20e-10 | 1.798 | -0.106 | 0.279 | 0.78 |
| MOND with the fitted g† | 1.12e-10 | 1.828 | -0.136 | 0.293 | 0.73 |
| GUID v*⁴ = 2GM\|γ1\|, Bridge A β = 0 | 4.88e-10 | 0.888 | +0.804 | 0.836 | 6.37 |
| GUID, Bridge A β → -∞ | 5.42e-10 | 0.842 | +0.850 | 0.880 | 7.08 |
| GUID, best universal \|γ1\| (S2a) | 4.54e-11 | 1.919 | -0.227 | 0.347 | 0.59 |
| GUID, \|γ1\| = 1e-10 (Oppenheim-Russo order) | 1.00e-10 | 1.576 | +0.116 | 0.277 | 1.31 |

With the slope fixed at 4 the data give log A = 1.676 (σ_int 0.120 dex), i.e. v⁴ = G M a with a = 1.59e-10 m/s², or |γ1| = 7.95e-11 m/s² in v*⁴ = 2GM|γ1|. In GUID's model v* is the minimum of the curve v² = GM/r + |γ1| r/2 (for a point mass), and the curve keeps rising beyond r*, so the turnover relation is only a rough guide. The direct test predicts each galaxy's speed at its outermost measured radius from its own baryons (Υ = 0.5/0.7) and compares it with Vflat (124 galaxies):

| model at the outermost radius | median log(V_pred/Vflat) [dex] | rms [dex] | v⁴ pred/obs | trend with log M_bar (Spearman, slope) |
|---|---|---|---|---|
| Newton | -0.319 | 0.336 | 0.05 | +0.34, +0.045 |
| RAR (fitted g†) | +0.014 | 0.061 | 1.14 | -0.08, -0.009 |
| GUID, best universal \|γ1\| | +0.006 | 0.087 | 1.06 | -0.42, -0.044 |
| GUID, \|γ1\| from the turnover relation | +0.109 | 0.146 | 2.72 | -0.46, -0.055 |
| GUID, Bridge A β = 0 | +0.476 | 0.480 | 80.06 | -0.48, -0.074 |
| GUID, Bridge A β → -∞ | +0.498 | 0.501 | 98.12 | -0.48, -0.074 |

## Caveats

- The model is the paper's: a constant |γ1| per galaxy, the same for any mass distribution. Oppenheim and Russo derive it for static, spherically symmetric configurations and call the calculation preliminary. A different spatial structure of the remnant (a γ1 that depends on the mass distribution, as in conformal gravity) is not tested here. Lensing, the microwave background and cluster dynamics are not tested either.
- Points are correlated within a galaxy (distance, inclination, Υ), so the point-wise ΔBIC values are far larger than the independent evidence. The sign of every comparison holds in the galaxy bootstrap and in the galaxy-by-galaxy counts.
- Υ is fixed at 0.5/0.7 for S1, S2a, S2b and S2d. The per-galaxy |γ1| depends on Υ; the mass trend weakens with Υ free.
- Data release: the public SPARC files give 19 more points before the precision cut and 3 more after it than the 2016 paper, and Vflat for more galaxies than the 2016 letter.
- The value of g† depends on the fitting choice at the ±0.12 level, more than its quoted random error (S1).

## Reproduce

```
python3 docs/simulation/sparc_rotation.py --data <dir with MassModels_Lelli2016c.mrt and SPARC_Lelli2016c.mrt>
```

Needs numpy, scipy and matplotlib. It runs in about a minute, and `--boot N` sets the bootstrap size. The script stops with FAIL if a file's SHA256 differs.

## References

Marked *verified* where the bibliographic record and the numbers used were checked against the arXiv text, the arXiv record or ADS by web search on 2026-10-31.

1. F. Lelli, S. S. McGaugh, J. M. Schombert, *SPARC: Mass Models for 175 Disk Galaxies with Spitzer Photometry and Accurate Rotation Curves*, AJ 152, 157 (2016), arXiv:1606.09251, doi:10.3847/0004-6256/152/6/157. Data: http://astroweb.cwru.edu/SPARC/. *Verified.*
2. S. S. McGaugh, F. Lelli, J. M. Schombert, *The Radial Acceleration Relation in Rotationally Supported Galaxies*, Phys. Rev. Lett. 117, 201101 (2016), arXiv:1609.05917. *Verified*: cuts, 2693 of 3149 points, 153 galaxies, Υ = 0.5/0.7, g† = 1.20 ± 0.02 ± 0.24, rms 0.13 dex, Gaussian 0.11 dex, scatter budget (Table I).
3. F. Lelli, S. S. McGaugh, J. M. Schombert, M. S. Pawlowski, *One Law to Rule Them All: The Radial Acceleration Relation of Galaxies*, ApJ 836, 152 (2017), arXiv:1610.08981. *Verified*: error model (Eq. 2, Sect. 2.1.2), scipy.odr on the individual points, δV/V < 0.1.
4. F. Lelli, S. S. McGaugh, J. M. Schombert, *The Small Scatter of the Baryonic Tully-Fisher Relation*, ApJL 816, L14 (2016), arXiv:1512.04543. *Verified*: sample (starburst dwarfs and Holmberg II excluded, i ≥ 30°), Eq. 5, slope 3.71 ± 0.08, log A = 2.27 ± 0.18, σ_int = 0.10 ± 0.02 for Υ = 0.5.
5. J. Oppenheim, A. Russo, *Anomalous contribution to galactic rotation curves due to stochastic spacetime*, arXiv:2402.19459 (v3, 2024; no journal reference on arXiv). *Verified*: metric Eq. 18, conditional mean Eq. 20, γ1 ≈ 10⁻¹⁰ m/s², the dwarf prescription γ1(M) = γ1(1 + M/10¹⁰ M_sun) with γ1 ≈ 10⁻²⁸ m⁻¹.
6. M. P. Hertzberg, A. Loeb, *Critical Analysis of Replacing Dark Matter and Dark Energy with a Model of Stochastic Spacetime*, JCAP 09 (2024) 046, arXiv:2404.13037. A critique of reference 5. *Verified* (record).
7. M. Milgrom, *A modification of the Newtonian dynamics as a possible alternative to the hidden mass hypothesis*, ApJ 270, 365 (1983). *Verified* (record).
8. M. Cappellari et al., *The ATLAS3D project - XV*, MNRAS 432, 1709 (2013), arXiv:1208.3522 (LTS_LINEFIT; default clip 2.6σ, from the ltsfit package documentation). *Verified* (record).
9. Holmberg II = UGC 4305 (catalogue cross-identification). *Verified.*
10. Planck 2018 cosmology (H0 = 67.4 km/s/Mpc, Ω_Λ = 0.685), as used in `docs/quantum-gravity/checks.py`. Not re-verified here.

