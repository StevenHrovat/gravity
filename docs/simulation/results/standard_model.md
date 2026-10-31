# GUID's Standard Model statements SM1 to SM5 against data

Written by `docs/simulation/standard_model.py` (deterministic; numpy, scipy, matplotlib; no network); every number is also in `standard_model.json`. Statements and scoring: `docs/simulation/sm_preregistration.md` (fixed before this script). Figures: `docs/simulation/figures/sm_couplings.pdf`, `docs/simulation/figures/sm_neutrino.pdf`, `docs/simulation/figures/sm_precision.pdf`, `docs/simulation/figures/sm_mu_alpha.pdf`, `docs/simulation/figures/sm_running.pdf`.

**Scored confrontations: 26 of 30 consistent at 95%.** FAIL: SM2d.4 (inherited tension), SM3.1 (refuted as stated (by derivation); corrected value derived), SM3.8 (inherited tension), SM3.9 (inherited tension). Checks of the script's own numerics: 30 of 30.

## Verdicts

| statement | content | verdict | rows |
|---|---|---|---|
| SM1 | spin ladder: no elementary spin-3/2 or spin-2 quantum | holds as a reading | SM1.1-SM1.4; the Standard Model says the same |
| SM2.1 | couplings proportional to mass, kappa = 1 | holds (W, Z, t, b, tau, mu); untested (c, e, u, d, s, nu) | SM2a.1-SM2a.9 |
| SM2.2 | Dirac neutrinos, m_bb = 0, lepton number conserved | live (holds against every 0vbb search) | SM2b.1-SM2b.7 |
| SM2.3 | photon and gluons massless | holds as a reading | SM2c.1 |
| SM2.4 | W and Z masses from the vacuum (rho = 1), with SM loops | holds; CDF 2022 is an inherited tension | SM2d.1-SM2d.6 |
| SM3 | only alpha varies; R of order 1e-3 to 1e-2 | window refuted by derivation (R = -0.045 +- 0.002); live against data | SM3.1-SM3.5 |
| SM3 side | scalar's g-2 contribution negligible | derived; holds (a_mu); a_e limited by the Cs-Rb alpha discrepancy (inherited) | SM3.6-SM3.10 |
| SM4 | no unification within causality | holds (two-loop SM misses by many sigma); proton decay live | SM4.1-SM4.5 |
| SM5 | alpha born near 1/128 at m_Z, runs to 1/137; crossover | holds | SM5.1-SM5.4 |

## Live predictions

- **SM2b:** any neutrinoless double-beta signal refutes GUID's Dirac neutrinos. LEGEND-1000 (3-sigma discovery at 1.3e28 yr, m_bb ~ 9-21 meV) and nEXO (1.35e28 yr) reach the Majorana band of the inverted ordering (>= 18.2 meV) for most nuclear matrix elements.
- **SM3:** if alpha is ever seen to vary, mu must vary 0.045 times as much and with the opposite sign; a detected Delta mu/mu much larger than that (as unification predicts, |R| ~ 20-50) refutes Hypothesis 4.
- **SM4:** proton decay is allowed only from a unification before the start; Hyper-Kamiokande is the test (data:D8.1).

## Failed or refuted

- **SM3.1, the preregistered window for R.** The careful derivation gives R = -0.0451 +- 0.0023, outside 'of order 1e-3 to 1e-2' by a factor 4.5. The estimate behind the window used the proton's electromagnetic mass; the electron's is larger in proportion (its QED self-energy from the electroweak scale down, 4.6% of m_e against 0.09% for the proton). The window is refuted by derivation, not by data; the corrected R is far from unification's and consistent with data.
- **SM2d.4** m_W: Standard Model with loops against CDF 2022: pull = +7.64 sigma (inherited tension).
- **SM3.8** a_e: measurement against the Standard Model with alpha(Rb 2020): pull = +2.15 sigma (inherited tension).
- **SM3.9** a_e: measurement against the Standard Model with alpha(Cs 2018): pull = -3.89 sigma (inherited tension).

## All rows

| ID | statement | GUID | data | sources | test | result | verdict |
|---|---|---|---|---|---|---|---|
| SM1.1 | Supersymmetry, whose gravitino is spin 3/2, through its coloured superpartners | none (SM1 excludes superpartners) | gluino > 2.30 TeV, squarks > 1.85 TeV (95% CL, simplified models, massless LSP) | atlas_susy | null search / spin test: no spin-3/2 or spin-2 quantum seen | **OK** | holds as a reading |
| SM1.2 | Spin-2 Kaluza-Klein graviton (Randall-Sundrum) in diphoton | none (no graviton as a quantum) | RS1 excluded below 4.5 TeV (k/M_Pl = 0.1), 3.9 TeV (0.05), 2.2 TeV (0.01) | atlas_diphoton | null search / spin test: no spin-3/2 or spin-2 quantum seen | **OK** | holds as a reading |
| SM1.3 | Elementary spin-3/2 resonance: excited top quark of spin 3/2 | none | m > 1.2 TeV (95% CL) | cms_tstar | null search / spin test: no spin-3/2 or spin-2 quantum seen | **OK** | holds as a reading |
| SM1.4 | The 125 GeV scalar is spin 0, not spin 2 | spin 0 (the Higgs rung) | all spin-2 alternatives excluded at > 99.9% CL | atlas_spin | null search / spin test: no spin-3/2 or spin-2 quantum seen | **OK** | holds as a reading |
| SM2a.kW | kappa_W = 1 (CMS, effective-loop fit) | 1 | 1.02 +0.08 -0.08 | cms_nature | pull = +0.25 sigma | **INFO** | holds |
| SM2a.kZ | kappa_Z = 1 (CMS, effective-loop fit) | 1 | 1.04 +0.07 -0.07 | cms_nature | pull = +0.57 sigma | **INFO** | holds |
| SM2a.kt | kappa_t = 1 (CMS, effective-loop fit) | 1 | 1.01 +0.11 -0.1 | cms_nature | pull = +0.10 sigma | **INFO** | holds |
| SM2a.kb | kappa_b = 1 (CMS, effective-loop fit) | 1 | 0.99 +0.17 -0.16 | cms_nature | pull = -0.06 sigma | **INFO** | holds |
| SM2a.ktau | kappa_tau = 1 (CMS, effective-loop fit) | 1 | 0.92 +0.08 -0.08 | cms_nature | pull = -1.00 sigma | **INFO** | holds |
| SM2a.kmu | kappa_mu = 1 (CMS, effective-loop fit) | 1 | 1.12 +0.21 -0.22 | cms_nature | pull = +0.55 sigma | **INFO** | holds |
| SM2a.kgamma | kappa_gamma = 1 (CMS, effective-loop fit) | 1 | 1.1 +0.08 -0.08 | cms_nature | pull = +1.25 sigma | **INFO** | holds |
| SM2a.kg | kappa_g = 1 (CMS, effective-loop fit) | 1 | 0.92 +0.08 -0.08 | cms_nature | pull = -1.00 sigma | **INFO** | holds |
| SM2a.kZgamma | kappa_Zgamma = 1 (CMS, effective-loop fit) | 1 | 1.65 +0.34 -0.37 | cms_nature | pull = +1.76 sigma | **INFO** | holds |
| SM2a.1 | All tree-level kappa = 1 (W, Z, t, b, tau, mu), joint | chi2 / dof ~ 1 | CMS 2022 kappas; chi2 = 1.70 for 6 | cms_nature | p = 0.95 (diagonal errors; correlations not published in the text) | **OK** | holds |
| SM2a.2 | All nine kappa = 1, CMS's own likelihood | SM point inside | p = 0.28 (CMS); diagonal approximation p = 0.60 | cms_nature | collaboration p-value | **OK** | holds |
| SM2a.3 | kappa_V = kappa_F = 1 (ATLAS two-parameter fit) | (1, 1) | kappa_V = 1.035 +- 0.031, kappa_F = 0.95 +- 0.05, rho = 0.39 | atlas_nature | chi2 = 3.72 for 2, p = 0.16 (ATLAS: 0.14) | **OK** | holds |
| SM2a.3b | ATLAS seven- and nine-parameter fits | SM point inside | p = 0.56 (kappa_c = kappa_t), 0.65 (kappa_c free), 0.61 (effective couplings) | atlas_nature | collaboration p-values | **INFO** | holds |
| SM2a.4 | Slope of the reduced coupling against mass (prediction 1) | 1 | s = 1.009 +- 0.017 (pole/PDG masses: 1.009 +- 0.017) | cms_nature, antusch | pull = +0.54 sigma | **OK** | holds |
| SM2a.5 | Vacuum value from the couplings (prediction v = (sqrt2 G_F)^-1/2) | 246.22 GeV | v = 244.0 +- 5.7 GeV (at the pivot mass 57 GeV) | cms_nature, gf_mulan | pull = -0.39 sigma | **OK** | holds |
| SM2a.6 | Charm: kappa_c = 1 | 1 | CMS 1.1 < \|kappa_c\| < 5.5 (95%); ATLAS \|kappa_c\| < 4.2 (95%) | cms_nature, atlas_cc | CMS's 95% interval just excludes 1; ATLAS's includes it | **INFO** | untested |
| SM2a.7 | Electron: kappa_e = 1 | 1 | \|kappa_e\| < 240 (95%); SM B(H -> ee) ~ 5e-9 | cms_hee | bound 240 times the prediction | **INFO** | untested |
| SM2a.8 | Light quarks u, d, s: kappa_q = 1 | 1 | no measurement |  | - | **INFO** | untested |
| SM2a.9 | Neutrinos: Dirac Yukawas y_nu = sqrt2 m_nu / v ~ 1e-13 | Higgs coupling to neutrinos | unmeasurable at any collider |  | - | **INFO** | untested |
| SM2b.1 | No neutrinoless double-beta decay (Xe-136) | m_bb = 0: no signal at any exposure | T_1/2 > 3.8e26 yr (90%); m_bb < 28-122 meV | kamland | no signal | **OK** | holds |
| SM2b.2 | No neutrinoless double-beta decay (Ge-76, GERDA + MAJORANA + LEGEND-200) | no signal | T_1/2 > 1.9e26 yr (90%); m_bb < 75-200 meV | legend200 | no signal | **OK** | holds |
| SM2b.3 | What the next generation can do | a signal at any level refutes SM2b | LEGEND-1000 3-sigma discovery at 1.3e28 yr (m_bb ~ 9-21 meV); nEXO 1.35e28 yr; Majorana IO band >= 18.2 meV | legend1000, nexo, nufit6 | if the ordering is inverted and neutrinos were Majorana, a signal is expected inside the reach | **INFO** | live |
| SM2b.4 | N_eff with decoupled right-handed partners (Planck 2018 + BAO) | 3.044 (+ negligible) | 2.99 +- 0.17 | planck18, neff_sm, luo2020 | pull = -0.32 sigma | **OK** | holds |
| SM2b.5 | N_eff with decoupled right-handed partners (ACT DR6 + Planck + lensing + BAO) | 3.044 (+ negligible) | 2.86 +- 0.13 | act_ext, neff_sm | pull = -1.42 sigma | **OK** | holds |
| SM2b.5b | Variant: partners thermalised in the start and decoupled before the split | N_eff = 3.185 | 2.99 +- 0.17 (Planck); 2.86 +- 0.13 (P-ACT-LB) | planck18, act_ext | pulls -1.14 and -2.50 sigma | **INFO** | not GUID's statement |
| SM2b.6 | Sum of neutrino masses: cosmology against the oscillation minimum (inherited; Dirac or Majorana alike) | sum >= 0.0588 eV (NO), >= 0.0989 eV (IO) | DESI DR2 + CMB: < 0.0642 eV (95%, Bayesian) | desi_nu, nufit6 | the NO minimum lies 0.0054 eV below the 95% bound; IO's lies above it | **OK** | holds (NO); inherited tension |
| SM2b.7 | Lepton number conserved | no Majorana mass anywhere | no 0vbb signal (SM2b.1, SM2b.2) | kamland, legend200 | consistent | **INFO** | live |
| SM2c.1 | The photon and the gluons are massless | massless | a reading of the Standard Model (no number scored) |  | - | **INFO** | holds as a reading |
| SM2d.1 | m_W: Standard Model with loops against ATLAS 2024 (7 TeV, reanalysis) | 80.3499 +- 0.0056 GeV (SM fit without M_W) | 80.3665 +- 0.0159 GeV | atlas_mw, deblas | pull = +0.98 sigma | **OK** | holds |
| SM2d.2 | m_W: Standard Model with loops against CMS 2024 | 80.3499 +- 0.0056 GeV (SM fit without M_W) | 80.3602 +- 0.0099 GeV | cms_mw, deblas | pull = +0.91 sigma | **OK** | holds |
| SM2d.3 | m_W: Standard Model with loops against LHCb 2022 | 80.3499 +- 0.0056 GeV (SM fit without M_W) | 80.3540 +- 0.0316 GeV | lhcb_mw, deblas | pull = +0.13 sigma | **OK** | holds |
| SM2d.4 | m_W: Standard Model with loops against CDF 2022 | 80.3499 +- 0.0056 GeV (SM fit without M_W) | 80.4335 +- 0.0094 GeV | cdf_mw, deblas | pull = +7.64 sigma | **FAIL** | inherited tension |
| SM2d.5 | m_W: Standard Model with loops against LHC-TeV combination without CDF (2023; includes ATLAS 2017 and LHCb 2022) | 80.3499 +- 0.0056 GeV (SM fit without M_W) | 80.3692 +- 0.0133 GeV | mw_comb, deblas | pull = +1.34 sigma | **INFO** | holds |
| SM2d.6 | Tree level m_W = g v / 2, m_Z = m_W / cos theta_W (rho = 1) | within 0.5% (Part I) | D8.3: -0.18%; D8.4: +0.34% | mw_comb, mz_pdg | cited from predictions_vs_data.py rows D8.3, D8.4 | **INFO** | holds |
| SM3.1 | R = dln mu / dln alpha when only the Maxwell coefficient varies (preregistered: of order 1e-3 to 1e-2) | \|R\| in [1e-3, 1e-2] | derived R = -0.0451 +- 0.0023 | gasser_leutwyler, glr2021, bmw_sigma, steinhauser, dhmz | \|R\| = 0.045 lies outside the window, a factor 4.5 above its top | **FAIL** | refuted as stated (by derivation); corrected value derived |
| SM3.2 | Molecular mu (methanol, z = 0.89) with quasar alpha (ESPRESSO, z = 1.15) on GUID's line Delta mu/mu = R Delta alpha/alpha | R = -0.045 | \|Delta mu/mu\| <= 1.1e-7 (2 sigma); Delta alpha/alpha = 1.3 +- 1.36 ppm | kanekar, espresso | chi2 = 0.51 (1 dof), p = 0.48; along the line Delta alpha/alpha = +0.58 +- 0.91 ppm | **OK** | live |
| SM3.3 | Same data on a unification line (R = -24.3) | not GUID | as SM3.2 | kanekar, espresso, ferreira | chi2 = 0.91, p = 0.34; along the line \|Delta alpha/alpha\| < 4.4e-09 (95%) | **INFO** | contrast |
| SM3.4 | Clocks: present drifts of mu and alpha on GUID's line | R = -0.045 | alpha-dot/alpha = (1.8 +- 2.5)e-19 /yr; mu-dot/mu = (-8 +- 36)e-18 /yr | filzinger, lange | chi2 = 0.05, p = 0.82 | **OK** | live |
| SM3.5 | High-redshift H2 (z = 2.0-4.2) | \|Delta mu/mu\| = 0.045 \|Delta alpha/alpha\| | \|Delta mu/mu\| < 5e-6 (3 sigma) | ubachs | allows \|Delta alpha/alpha\| < 1.1e-04 on GUID's line, 2.1e-07 on the unification line | **OK** | live |
| SM3.6 | The scalar's contribution to lepton g-2 at \|lambda\| < 3.1e-5 | Delta a ~ C lambda^2 m_l^2 / Mbar_P^2, C <~ 10 | precision: a_e 1.3e-13, a_mu 1.45e-10 | fan2023, fnal_gm2 | Delta a_e <~ 4e-52, Delta a_mu <~ 2e-47: 38 and 36 orders of magnitude below | **OK** | derived; holds |
| SM3.7 | No environment dependence of alpha between laboratories | \|delta alpha/alpha\| <= 1e-20 (scalar; Earth's and the Sun's potential) | alpha^-1: Cs 137.035999046(27), Rb 137.035999206(11): differ by 1.2e-09 (5.5 sigma) | parker2018, morel2020 | the measured difference is 1e+11 times what the scalar allows | **INFO** | derived |
| SM3.8 | a_e: measurement against the Standard Model with alpha(Rb 2020) | Standard Model (scalar negligible, SM3.6) | a_e(exp) - a_e(SM) = +0.34e-12; in alpha^-1: 137.035999206 vs 137.035999166(15) from a_e | morel2020, fan2023 | pull = +2.15 sigma | **FAIL** | inherited tension |
| SM3.9 | a_e: measurement against the Standard Model with alpha(Cs 2018) | Standard Model (scalar negligible, SM3.6) | a_e(exp) - a_e(SM) = -1.02e-12; in alpha^-1: 137.035999046 vs 137.035999166(15) from a_e | parker2018, fan2023 | pull = -3.89 sigma | **FAIL** | inherited tension |
| SM3.10 | a_mu: final Fermilab-based world average against the 2025 Standard Model value | Standard Model (scalar negligible) | 116592071.5(14.5)e-11 vs 116592033(62)e-11 | fnal_gm2, wp25 | pull = +0.60 sigma | **OK** | holds |
| SM4.1 | Standard Model couplings do not meet at one point (two loops) | no single meeting point | smallest spread of 1/alpha_i = 3.20 at 1.7e+14 GeV | alpha_mz, s2w, antusch, buttazzo | 7 sigma from zero (inputs and a theory allowance 0.47) | **OK** | holds |
| SM4.2 | Exact unification would need alpha_s(M_Z) of | not 0.118 (no unification) | SM: 0.0738; measured 0.118 +- 0.0009 | antusch, denterria | 49 sigma (input error only) | **OK** | holds |
| SM4.3 | Contrast: MSSM with M_SUSY = 2 TeV (excluded by SM1) | not GUID | smallest spread 0.003 at 1.1e+16 GeV; needs alpha_s(M_Z) = 0.1181 | martin_vaughn, martin_primer | alpha_s off by +0.1 sigma of the input (+0.1%) | **INFO** | contrast |
| SM4.4 | Proton decay only from a unification before the start | possible, not required | tau/B(p -> e+ pi0) > 2.4e34 yr (90%) | superk | M_X > 4.8e+15 GeV (alpha_G = 1/40), 4.7e+15 GeV (alpha_G = 1/42.2); cited as data:D8.1 | **INFO** | live |
| SM4.5 | A unification at the SM's alpha1 = alpha2 crossing | excluded (no unification within causality) | crossing at 1.1e+13 GeV would give tau ~ 7e+23 yr | superk | 4e+10 times below the bound | **OK** | holds |
| SM5.1 | alpha born near 1/128 at m_Z (on-shell, from alpha(0) and the vacuum polarisation) | 1/alpha(M_Z) ~ 128 (within 1%) | 128.937 +- 0.014 | codata22, steinhauser, dhmz | +0.73% from 128 | **OK** | holds |
| SM5.2 | Same, MS-bar | within 1% | 127.950 +- 0.017 (D8.5) | alpha_mz, erler1999 | -0.04% from 128; recomputed 127.96 | **INFO** | holds |
| SM5.3 | alpha runs down to 1/137 | 1/alpha(0) = 137.036 | 137.035999177(21) | codata22 | the running is the measured vacuum polarisation | **INFO** | holds |
| SM5.4 | The split is a smooth crossover near 160 GeV | crossover | data:D8.6 (m_H = 125.11 GeV above the first-order end point) |  | cited from predictions_vs_data.py | **INFO** | holds |

Notes:

- SM1.1: the Standard Model makes the same statement for its own content; a gravitino-specific limit was not verified and is not used
- SM1.2: the Standard Model makes the same statement for its own content; a gravitino-specific limit was not verified and is not used
- SM1.3: the Standard Model makes the same statement for its own content; a gravitino-specific limit was not verified and is not used
- SM1.4: the Standard Model makes the same statement for its own content; a gravitino-specific limit was not verified and is not used
- SM2a.kW: reported per coupling; scored jointly in SM2a.1 and SM2a.2
- SM2a.kZ: reported per coupling; scored jointly in SM2a.1 and SM2a.2
- SM2a.kt: reported per coupling; scored jointly in SM2a.1 and SM2a.2
- SM2a.kb: reported per coupling; scored jointly in SM2a.1 and SM2a.2
- SM2a.ktau: reported per coupling; scored jointly in SM2a.1 and SM2a.2
- SM2a.kmu: reported per coupling; scored jointly in SM2a.1 and SM2a.2
- SM2a.kgamma: reported per coupling; scored jointly in SM2a.1 and SM2a.2; loop-induced, not a direct mass coupling
- SM2a.kg: reported per coupling; scored jointly in SM2a.1 and SM2a.2; loop-induced, not a direct mass coupling
- SM2a.kZgamma: reported per coupling; scored jointly in SM2a.1 and SM2a.2; loop-induced, not a direct mass coupling
- SM2a.3b: ATLAS gives the per-particle values only graphically; they were not read off and are not used in the fits below
- SM2a.4: six CMS couplings over 3.2 decades of mass; correlations ignored
- SM2a.6: bounded at a few times the prediction; a 2-sigma-level upward fluctuation in one experiment
- SM2b.3: for normal ordering a Majorana m_bb can be far below any planned reach, so a null result does not establish Dirac neutrinos
- SM2b.5b: disfavoured at 2.5 sigma by P-ACT-LB; GUID's partners never thermalise (Yukawa-only interactions)
- SM2b.6: the Feldman-Cousins limit 0.053 eV and the effective-mass analysis (3 sigma) breach the oscillation minimum: a tension of LambdaCDM with oscillations, not of GUID
- SM2d.1: GUID adds no loop of its own: m_W is the Standard Model's
- SM2d.2: GUID adds no loop of its own: m_W is the Standard Model's
- SM2d.3: GUID adds no loop of its own: m_W is the Standard Model's
- SM2d.4: GUID adds no loop of its own: m_W is the Standard Model's
- SM2d.5: GUID adds no loop of its own: m_W is the Standard Model's; overlaps SM2d.1 and SM2d.3
- SM3.1: the electron's electromagnetic share (its QED running from the electroweak scale plus the pole conversion, 4.6% of m_e) dominates; the proton's (0.09%) was the estimate behind the window. The physical claim that \|R\| is far below unification's 20-50 holds.
- SM3.2: under GUID the methanol bound limits alpha at z ~ 0.9 about as tightly as the quasar itself; the two redshifts differ
- SM3.3: a detected alpha change of ppm size with \|Delta mu/mu\| < 1e-7 would exclude this line and agree with GUID's
- SM3.4: the Cs-based mu drift assumes a model for the Cs nuclear g-factor; the alpha and mu values share data
- SM3.5: no constraint on alpha under GUID; a strong one under unification
- SM3.7: the Cs-Rb discrepancy is experimental or in the Standard Model's inputs, not GUID's
- SM3.8: the comparison is made in alpha^-1 with Fan et al.'s alpha from a_e (their QED series); the a_e difference uses d a_e / d alpha^-1 = -alpha^2 / 2pi
- SM3.9: the comparison is made in alpha^-1 with Fan et al.'s alpha from a_e (their QED series); the a_e difference uses d a_e / d alpha^-1 = -alpha^2 / 2pi
- SM4.1: the Standard Model shares this statement
- SM4.3: meets within the input errors at this threshold (no GUT or superpartner threshold corrections, no DR-bar conversion); the SM needs alpha_s 37% below the measured value
- SM5.2: cited from data:D8.5

## Method

**SM2a.** The reduced couplings kappa_f m_f / v (fermions) and sqrt(kappa_V) m_V / v (W, Z) of CMS (Nature 2022, Fig. 4 left) are fitted by ln kappa_eff = a + (s - 1) ln(m / m_pivot), weighted by the symmetrised errors, correlations ignored; v_fit = v exp(-a) at the pivot. Fermion masses at M_Z are y_f(M_Z) v / sqrt2 from the MS-bar Yukawas of Antusch et al.; W and Z pole masses. Result: s = 1.009 +- 0.017, v = 244.0 +- 5.7 GeV at 57 GeV, chi2 = 1.25 for 4; with pole/PDG masses s = 1.009 +- 0.017. The joint test of kappa = 1 uses the error toward 1 for each asymmetric interval.

**SM2b.** Neutrino masses from NuFIT 6.0 (IC24 with SK-atm); the Majorana m_bb band is the closed-form minimum and maximum over both phases (checked against a phase scan). Delta N_eff of thermalised right-handed partners decoupled above all Standard Model thresholds is 3 (10.75/106.75)^(4/3) = 0.141; partners with only Yukawa interactions never thermalise.

**SM3.** Hypothesis 4 changes only the coefficient of F^2. Below the electroweak scale this shifts 1/alpha by a scale-independent constant at one loop, so delta ln alpha(mu) = [alpha(mu)/alpha(0)] delta ln alpha(0). With the Yukawas fixed at the matching scale mu0 = M_Z and Lambda_QCD (three flavours) fixed: d ln M_e / d ln alpha = (3/2pi alpha0) int_{m_e}^{mu0} alpha(mu)^2 dln mu + alpha/pi = 0.0460 (QED anomalous dimension 3 alpha / 2pi of the MS-bar mass; pole mass M = m(m)(1 + alpha/pi)); d ln m_p / d ln alpha = E_em / m_p + sum_q f_q Q_q^2 (3/2pi alpha0) int_{2 GeV}^{mu0} alpha^2 dln mu = 8.94e-04, with E_em = 0.63 +- 0.40 MeV and the BMW sigma-term fractions. alpha(mu) is the one-loop leptonic running scaled to the three-loop Delta alpha_lep and the hadronic Delta alpha_had^(5) spread log-linearly from 0.5 GeV to M_Z. Budget: proton electromagnetic self-energy +-0.40 MeV 4.3e-04; sigma terms (BMW 2020 vs sigma_piN = 59.1 MeV) 7.5e-05; Lambda^(3) fixed vs alpha_s(M_Z) fixed 6.2e-04; matching scale M_W to v (half range) 2.2e-03; hadronic running model, mu_h = 0.3 to 1 GeV (half range) 6.2e-05; two-loop QED anomalous dimension, O(alpha/pi) relative 1.1e-04. Data: Gaussian likelihoods on the lines Delta mu/mu = R Delta alpha/alpha (one parameter); the methanol 2-sigma bound is read as 0 +- 0.55e-7.

**SM4.** Two-loop gauge running with one-loop top Yukawa (Buttazzo et al. Eqs. 96-98, 76; Martin and Vaughn Eqs. 4.4-4.5; Martin Eq. 6.5.22), from 1/alpha-hat(M_Z) = 127.950, sin^2 theta-hat = 0.23129, alpha_s = 0.1180, y_t(M_Z) = 0.967; g1 GUT-normalised. Mismatch measure: the smallest spread of the three 1/alpha_i over 1e12 to 1e19 GeV, with 200 seeded Monte Carlo draws of the inputs and a theory allowance equal to the two-loop minus one-loop difference. Also: alpha_s(M_Z) needed for alpha_3 to meet alpha_1 = alpha_2 at their crossing.

**SM5.** 1/alpha(M_Z) on-shell = 1/alpha(0) (1 - Delta alpha_lep - Delta alpha_had^(5)); MS-bar from the scheme offset implied by Erler's paired values.

## Choices made after seeing the data

- SM2a: the CMS per-particle kappas of Fig. 4 (left) are used for the mass-coupling fit because they are the only published per-particle values in text form; ATLAS enters through its (kappa_V, kappa_F) fit and its p-values.
- SM2a: fermion masses at M_Z from the MS-bar Yukawas (baseline) and pole / PDG masses (variant) were both fixed before the fit; the slope changes by less than its error.
- SM3: the electromagnetic self-energy of the proton is taken as Gasser and Leutwyler's 0.63 MeV with +-0.40 MeV, set before computing R to cover their +-0.2 MeV residual and the spread between Cottingham (0.58 MeV) and lattice (1.0 MeV) values of the proton-neutron difference.
- SM3: the preregistration does not say at which scale the Yukawa couplings are held fixed; M_Z (where alpha is 'born near 1/128') is the baseline, and M_W to v is the stated systematic.
- SM3: the two a_e rows (alpha from Rb and from Cs) are scored separately although they show one tension, the disagreement of the two alpha determinations; this was decided after both were seen to fail.
- SM4: the smallest spread is evaluated at the pairwise crossings rather than on the grid, after the grid minimum was seen to sit at a kink; the change is below 0.02 in 1/alpha.
- SM4: the MSSM contrast uses one common superpartner threshold M_SUSY = 2 TeV (near the gluino limit of SM1.1) and tan beta = 10, fixed before running; the MS-bar to DR-bar conversion and all threshold corrections are omitted.

## Ill-posed points in the preregistration

- SM3's window '1e-3 to 1e-2' is numerically wrong (see above); the preregistration also does not fix the scale at which the Yukawas are held, which moves R by about +-0.002, too little to reach the window.
- SM2.4 tests the W mass 'with the Standard Model's loop corrections': GUID adds nothing to them, so the test is the Standard Model's, inherited.
- SM1's 'holds as a reading' cannot become 'holds': null searches bound masses, they do not exclude a spin.

## Citations (what was read, the value)

- `atlas_susy`: ATLAS Collaboration, JHEP 02 (2021) 143, arXiv:2010.14293. Read: arXiv abstract. Value: gluino excluded below 2.30 TeV (only gluino and massless lightest neutralino); mass-degenerate first- and second-generation squarks excluded below 1.85 TeV (massless neutralino), 95% CL.
- `atlas_diphoton`: ATLAS Collaboration, Phys. Lett. B 822 (2021) 136651, arXiv:2102.13405. Read: arXiv full text, Sect. 8. Value: RS1 graviton excluded for m_G* below 2.2, 3.9 and 4.5 TeV for k/M_Pl = 0.01, 0.05 and 0.1.
- `cms_tstar`: CMS Collaboration, Phys. Lett. B 778 (2018) 349, arXiv:1711.10949. Read: arXiv abstract. Value: spin-3/2 excited top quark: lower mass limit 1.2 TeV (95% CL).
- `atlas_spin`: ATLAS Collaboration, Eur. Phys. J. C 75 (2015) 476, arXiv:1506.05669. Read: arXiv abstract. Value: J^P = 0+ tested against alternatives including spin-2 models: all alternatives excluded at more than 99.9% CL.
- `cms_nature`: CMS Collaboration, Nature 607, 60 (2022), arXiv:2207.00043. Read: arXiv full text: values printed in Fig. 4 (left) and in the captions of Figs. 3 and 4; Sect. on charm. Value: kappa_W = 1.02 +- 0.08, kappa_Z = 1.04 +- 0.07, kappa_gamma = 1.10 +- 0.08, kappa_g = 0.92 +- 0.08, kappa_t = 1.01 +0.11 -0.10, kappa_b = 0.99 +0.17 -0.16, kappa_tau = 0.92 +- 0.08, kappa_mu = 1.12 +0.21 -0.22, kappa_Zgamma = 1.65 +0.34 -0.37 (68%); p = 28% (Fig. 4 left); reduced-coupling fit p = 37.5% (Fig. 3 right); 1.1 < |kappa_c| < 5.5 observed (|kappa_c| < 3.4 expected), 95% CL.
- `atlas_nature`: ATLAS Collaboration, Nature 607, 52 (2022), arXiv:2207.00092. Read: arXiv full text (pp. 8-10 and figure captions); the per-particle kappa values appear only in Figs. 5 and 6 and were not read off. Value: kappa_V = 1.035 +- 0.031, kappa_F = 0.95 +- 0.05, correlation 39%, p = 14%; reduced-coupling fits p = 56% (kappa_c = kappa_t) and 65% (kappa_c free); effective-coupling fit p = 61%; kappa_c < 5.7 (95%); mu = 1.05 +- 0.06.
- `atlas_cc`: ATLAS Collaboration, JHEP 04 (2025) 075, arXiv:2410.19611. Read: arXiv abstract. Value: |kappa_c| < 4.2 (95% CL); VH(cc) below 11.5 (10.6 expected) times the SM.
- `cms_hee`: CMS Collaboration, Phys. Lett. B 846 (2023) 137783, arXiv:2208.00265. Read: arXiv abstract and full text. Value: B(H -> ee) < 3.0e-4 (95% CL), |kappa_e| < 240; SM prediction B ~ 5e-9.
- `antusch`: S. Antusch, K. Hinze, S. Saad, 'Updated running quark and lepton parameters at various scales', arXiv:2510.01312. Read: arXiv HTML (inputs and Eq. 4). Value: PDG 2024 inputs m_b(m_b) = 4.183 +- 0.004 GeV, M_tau = 1776.93 +- 0.09 MeV, M_mu = 105.6583755 MeV, M_e = 0.51099895000 MeV, alpha_s(M_Z) = 0.1180 +- 0.0009; MS-bar Yukawas at M_Z: y_t = 0.967 +- 0.004, y_b = 1.630e-2, y_c = 3.56e-3, y_tau = 0.99378e-2, y_mu = 5.85042e-4, y_e = 2.77713e-6.
- `top_comb`: ATLAS and CMS Collaborations, Phys. Rev. Lett. 132 (2024) 261902, arXiv:2402.08713. Read: arXiv abstract. Value: m_t = 172.52 +- 0.14 (stat) +- 0.30 (syst) GeV, total 0.33 GeV.
- `kamland`: KamLAND-Zen Collaboration, Phys. Rev. Lett. 135, 262501 (2025), arXiv:2406.11438. Read: arXiv abstract. Value: T_1/2(0vbb, Xe-136) > 3.8e26 yr (90% CL); m_bb < 28-122 meV.
- `legend200`: LEGEND Collaboration, arXiv:2505.10440, doi:10.1103/25tk-nctn (2025). Read: arXiv abstract. Value: GERDA + MAJORANA DEMONSTRATOR + LEGEND-200 combined: T_1/2(Ge-76) > 1.9e26 yr (90% CL), sensitivity 2.8e26 yr; m_bb < 75-200 meV.
- `legend1000`: LEGEND Collaboration, 'LEGEND-1000 preconceptual design report', arXiv:2107.11462. Read: arXiv abstract. Value: 99.7%-CL discovery sensitivity T_1/2 = 1.3e28 yr; m_bb upper limit 9-21 meV.
- `nexo`: nEXO Collaboration, J. Phys. G 49, 015104 (2022), arXiv:2106.16243. Read: arXiv abstract. Value: half-life sensitivity 1.35e28 yr (90% CL, 10 yr); covers the inverted ordering.
- `nufit6`: I. Esteban et al., 'NuFit-6.0', arXiv:2410.05380v2. Read: arXiv HTML, Table 1 (IC24 with SK-atm) and Eq. (22). Value: dm21^2 = 7.49 (+0.19 -0.19) e-5 eV^2; dm3l^2 = +2.513 (+0.021 -0.019) e-3 (NO), -2.484 (+-0.020) e-3 (IO); sin^2 th12 = 0.308 (+0.012 -0.011); sin^2 th13 = 0.02215 (NO), 0.02231 (IO); sum m_nu >= 0.058 eV (NO), >= 0.098 eV (IO).
- `desi_nu`: W. Elbers et al. (DESI Collaboration), arXiv:2503.14744 (accepted in Phys. Rev. D). Read: arXiv abstract. Value: sum m_nu < 0.0642 eV (95%, LCDM); Feldman-Cousins 95% upper limit 0.053 eV, 'breaching the lower limit from neutrino oscillations'; the effective-mass analysis is 'in 3 sigma tension with the same oscillation limit'.
- `planck18`: Planck Collaboration, Astron. Astrophys. 641, A6 (2020), arXiv:1807.06209. Read: arXiv abstract. Value: N_eff = 2.99 +- 0.17 (with BAO); sum m_nu < 0.12 eV.
- `act_ext`: E. Calabrese et al. (ACT), JCAP 11 (2025) 063, arXiv:2503.14454. Read: arXiv abstract and HTML Eq. (30). Value: N_eff = 2.86 +- 0.13 (68%, P-ACT-LB), 2.73 +- 0.14 (P-ACT); sum m_nu < 0.082 eV (95%).
- `neff_sm`: J. J. Bennett et al., JCAP 04 (2021) 073, arXiv:2012.02726. Read: arXiv abstract. Value: N_eff^SM = 3.0440 +- 0.0002.
- `luo2020`: X. Luo, W. Rodejohann, X.-J. Xu, JCAP 06 (2020) 058, arXiv:2005.01629. Read: arXiv abstract. Value: Dirac neutrinos: 'With pure standard model interactions, the contribution [to N_eff] is negligibly small'.
- `atlas_mw`: ATLAS Collaboration, Eur. Phys. J. C 84 (2024) 1309, arXiv:2403.15085. Read: arXiv abstract. Value: m_W = 80366.5 +- 9.8 (stat) +- 12.5 (syst) MeV = 80366.5 +- 15.9 MeV.
- `cms_mw`: CMS Collaboration, Nature 652 (2026) 321, arXiv:2412.13872. Read: arXiv abstract. Value: m_W = 80360.2 +- 9.9 MeV.
- `lhcb_mw`: LHCb Collaboration, JHEP 01 (2022) 036, arXiv:2109.01113. Read: arXiv abstract. Value: m_W = 80354 +- 23 (stat) +- 10 (exp) +- 17 (theory) +- 9 (PDF) MeV.
- `cdf_mw`: CDF Collaboration, Science 376, 170 (2022). Read: the value as quoted in de Blas et al. 2022, Eq. (3) (arXiv full text); the journal page was not opened. Value: m_W = 80.4335 +- 0.0094 GeV.
- `mw_comb`: LHC-TeV MW Working Group, Eur. Phys. J. C 84, 451 (2024), arXiv:2308.09417. Read: arXiv abstract. Value: m_W = 80369.2 +- 13.3 MeV without CDF; 80394.6 +- 11.5 MeV with CDF (compatibility 0.5%).
- `deblas`: J. de Blas, M. Pierini, L. Reina, L. Silvestrini, Phys. Rev. Lett. 129, 271801 (2022), arXiv:2204.04204. Read: arXiv full text, Tables I and II. Value: SM prediction (fit without M_W) M_W = 80.3499 +- 0.0056 GeV (standard average), 80.3505 +- 0.0077 GeV (conservative); pull 6.5 sigma against 80.4133 +- 0.0080 GeV.
- `gasser_leutwyler`: J. Gasser, H. Leutwyler, Phys. Rep. 87, 77 (1982). Read: through S. Stern, dissertation, Heidelberg 2008, arXiv:0812.3377, Eqs. (8.8)-(8.10) (arXiv full text). Value: Born-level electromagnetic masses m_p^gamma = 0.63 MeV, m_n^gamma = -0.13 MeV; residual from intermediate states +-0.2 MeV; (m_n - m_p)^gamma = -0.76 +- 0.30 MeV.
- `glr2021`: J. Gasser, H. Leutwyler, A. Rusetsky, Phys. Lett. B 814, 136087 (2021), arXiv:2003.13612. Read: arXiv full text, Eqs. (18), (21) and the discussion. Value: m_QED(p - n) = 0.58 +- 0.16 MeV, elastic part 0.75 +- 0.02 MeV; lattice values quoted there 1.00(7)(14), 1.03(17), 1.53(25)(50) MeV.
- `bmw_sigma`: Sz. Borsanyi et al., arXiv:2007.03319. Read: arXiv HTML, Table 1 and Sect. 3.4. Value: f_u^p = 0.0142(12)(15), f_d^p = 0.0242(22)(30), f_s^N = 0.0577(46)(33) (sigma_q / M_N); sigma_piN = 42.0(1.3)(1.4) MeV (mesonic route).
- `hoferichter`: M. Hoferichter, J. Ruiz de Elvira, B. Kubis, U.-G. Meissner, Phys. Rev. Lett. 115, 092301 (2015), arXiv:1506.04142. Read: arXiv abstract. Value: sigma_piN = 59.1 +- 3.5 MeV.
- `erler1999`: J. Erler, Phys. Rev. D 59, 054008 (1999), arXiv:hep-ph/9803453. Read: arXiv full text. Value: 1/alpha-hat(M_Z) = 127.934 +- 0.027 (MS-bar) for alpha_s = 0.120, corresponding to the on-shell Delta alpha_had^(5)(M_Z) = 0.02779 +- 0.00020; m_c(m_c) = 1.31 +- 0.07 GeV, m_b(m_b) = 4.24 +- 0.11 GeV.
- `kanekar`: N. Kanekar et al., Mon. Not. R. Astron. Soc. 448, L104 (2015), arXiv:1412.7757. Read: arXiv abstract. Value: |Delta mu / mu| <= 1.1e-7 (2 sigma), methanol, z = 0.88582, lookback ~7.5 Gyr.
- `ubachs`: W. Ubachs, J. Bagdonaite, E. J. Salumbides, M. T. Murphy, L. Kaper, Rev. Mod. Phys. 88, 021003 (2016), arXiv:1511.04476. Read: arXiv abstract. Value: |Delta mu / mu| < 5e-6 (3 sigma), H2 in ten quasar systems, z = 2.0-4.2.
- `lange`: R. Lange et al., Phys. Rev. Lett. 126, 011102 (2021), arXiv:2010.06620. Read: arXiv abstract. Value: d ln alpha/dt = 1.0(1.1)e-18 /yr; d ln mu/dt = -8(36)e-18 /yr.
- `filzinger`: M. Filzinger et al., Phys. Rev. Lett. 130, 253001 (2023), arXiv:2301.03433. Read: as verified for predictions_vs_data.py (arXiv full text, Suppl. Eq. 9). Value: d ln alpha/dt = 1.8(2.5)e-19 /yr.
- `espresso`: M. T. Murphy et al., Astron. Astrophys. 658, A123 (2022), arXiv:2112.05819. Read: as verified for predictions_vs_data.py (arXiv abstract). Value: Delta alpha/alpha = 1.3 +- 1.3 (stat) +- 0.4 (sys) ppm at z = 1.15.
- `ferreira`: M. C. Ferreira, M. D. Juliao, C. J. A. P. Martins, A. M. R. V. L. Monteiro, Phys. Rev. D 86, 125025 (2012), arXiv:1212.4164. Read: arXiv full text, Eqs. (2)-(4) and Sect. III. Value: unification class: Delta mu/mu = [0.8 R - 0.3 (1 + S)] Delta alpha/alpha, typical GUT values R ~ 30, S ~ 160.
- `calmet`: X. Calmet, H. Fritzsch, Eur. Phys. J. C 24, 639 (2002), arXiv:hep-ph/0112110. Read: arXiv abstract. Value: 'The relative change of the nucleon mass is about 40 times larger than the relative change of alpha'.
- `fan2023`: X. Fan, T. G. Myers, B. A. D. Sukra, G. Gabrielse, Phys. Rev. Lett. 130, 071801 (2023), arXiv:2209.13084. Read: arXiv abstract. Value: g/2 = 1.001 159 652 180 59 (13); with SM theory alpha^-1 = 137.035 999 166 (15).
- `parker2018`: R. H. Parker, C. Yu, W. Zhong, B. Estey, H. Mueller, Science 360, 191 (2018), arXiv:1812.04130. Read: arXiv abstract. Value: alpha = 1/137.035999046(27).
- `morel2020`: L. Morel, Z. Yao, P. Clade, S. Guellati-Khelifa, Nature 588, 61 (2020). Read: journal abstract through a web search (not on arXiv). Value: alpha^-1 = 137.035999206(11), 81 ppt; differs by more than 5 standard deviations from the Cs value.
- `codata22`: CODATA 2022 recommended values. Read: as verified for predictions_vs_data.py. Value: alpha^-1 = 137.035999177(21).
- `fnal_gm2`: Muon g-2 Collaboration, arXiv:2506.03069 (2025). Read: arXiv abstract. Value: a_mu(FNAL, full) = 116 592 0705(148) e-12 (127 ppb); world average 116 592 0715(145) e-12 (124 ppb).
- `wp25`: R. Aliberti et al., Phys. Rept. 1143 (2025) 1, arXiv:2505.21476. Read: arXiv abstract. Value: a_mu^SM = 116 592 033(62) e-11; a_mu^exp - a_mu^SM = 38(63) e-11, 'no tension'.
- `buttazzo`: D. Buttazzo et al., JHEP 12 (2013) 089, arXiv:1307.3536. Read: arXiv full text, App. B Eqs. (96)-(98) and Eq. (76). Value: two-loop SM gauge beta functions (g1 GUT normalised): one-loop (41/10, -19/6, -7); two-loop matrix [[199/50, 27/10, 44/5], [9/10, 35/6, 12], [11/10, 9/2, -26]]; top-Yukawa terms (17/10, 3/2, 2); (4 pi)^2 d y_t^2 / d ln mu^2 = y_t^2 (9/2 y_t^2 - 8 g3^2 - 9/4 g2^2 - 17/20 g1^2).
- `martin_vaughn`: S. P. Martin, M. T. Vaughn, Phys. Rev. D 50, 2282 (1994), arXiv:hep-ph/9311340. Read: arXiv full text, Eqs. (4.4)-(4.5). Value: MSSM: B^(1) = (33/5, 1, -3); B^(2) = [[199/25, 27/5, 88/5], [9/5, 25, 24], [11/5, 9, 14]]; C^u = (26/5, 6, 4).
- `martin_primer`: S. P. Martin, 'A supersymmetry primer', arXiv:hep-ph/9709356 (v7, 2016). Read: arXiv full text, Eqs. (6.4.7) and (6.5.22). Value: 16 pi^2 d y_t/dt = y_t (6 y_t^2 + y_b^2 - 16/3 g3^2 - 3 g2^2 - 13/15 g1^2) in the MSSM.
- `alpha_mz`: J. Erler, A. Freitas, Electroweak model and constraints on new physics, PDG 2017. Read: as verified for predictions_vs_data.py (web search of the PDG review). Value: 1/alpha-hat(M_Z) = 127.950 +- 0.017 (MS-bar).
- `s2w`: Particle Data Group 2024, quoted in arXiv:2509.18251. Read: arXiv HTML. Value: sin^2 theta-hat_W(M_Z) = 0.23129 +- 0.00004.
- `denterria`: D. d'Enterria et al., J. Phys. G 51, 090501 (2024), arXiv:2203.08271. Read: arXiv abstract. Value: alpha_s(m_Z) = 0.1179 +- 0.0009.
- `dhmz`: M. Davier, A. Hoecker, B. Malaescu, Z. Zhang, Eur. Phys. J. C 80, 241 (2020), arXiv:1908.00921. Read: arXiv abstract. Value: Delta alpha_had^(5)(m_Z^2) = (276.0 +- 1.0) e-4.
- `steinhauser`: M. Steinhauser, Phys. Lett. B 429, 158 (1998), arXiv:hep-ph/9803313. Read: arXiv full text, Table 1. Value: Delta alpha_lep(M_Z^2) = 314.97686 e-4 (three loops; one loop 314.19007 e-4).
- `gf_mulan`: MuLan Collaboration, Phys. Rev. D 87, 052003 (2013), arXiv:1211.0960. Read: as verified for predictions_vs_data.py. Value: G_F = 1.1663787(6) e-5 GeV^-2.
- `mz_pdg`: Particle Data Group, Z boson mass. Read: as verified for predictions_vs_data.py. Value: m_Z = 91.1880 +- 0.0020 GeV.
- `superk`: A. Takenaka et al. (Super-Kamiokande), Phys. Rev. D 102, 112011 (2020), arXiv:2010.16098. Read: arXiv abstract (as for predictions_vs_data.py). Value: tau/B(p -> e+ pi0) > 2.4e34 yr (90% CL).

## Checks of the script's numerics

- OK: v = (sqrt2 G_F)^(-1/2) = 246.22 GeV (246.2197)
- OK: ATLAS (kappa_V, kappa_F) Gaussian chi2 reproduces ATLAS's p = 14% within 0.03 (p = 0.156)
- OK: mass-coupling fit returns slope 1 and v = 246.22 GeV for kappa = 1
- OK: weighted slope: matrix solve equals the closed form (0.009261)
- OK: oscillation minimum sum m_nu (NO) = sqrt(dm21) + sqrt(dm31), and NuFIT's 0.058 eV (0.0588 eV)
- OK: oscillation minimum sum m_nu (IO) agrees with NuFIT's 0.098 eV (0.0989 eV)
- OK: m_bb band: closed-form min/max equal a scan over both Majorana phases
- OK: Delta N_eff of three thermalised Weyl partners decoupled above all SM thresholds = 0.140 (0.1406)
- OK: de Blas et al.'s CDF pull is reproduced: (80.4133 - 80.3499) / sqrt(0.0080^2 + 0.0056^2) = 6.5
- OK: one-loop asymptotic leptonic running reproduces Steinhauser's one-loop 314.19e-4 to 3e-6 (mass terms O(m_tau^2/M_Z^2) neglected) (314.2089e-4)
- OK: running alpha reproduces 1/alpha(M_Z) on-shell = 1/alpha(0) (1 - Delta_lep - Delta_had) (128.937 vs 128.937)
- OK: alpha-squared integral: Simpson converged (n = 4001 against 16001 to 1e-7 relative)
- OK: alpha-squared integral lies between the constant-alpha bounds alpha0 L and alpha(M_Z)^2/alpha0 L
- OK: electron term with alpha frozen at alpha0 equals (3 alpha0 / 2pi) ln(M_Z / m_e) + alpha0/pi
- OK: Coulomb self-energy of a dipole charge distribution: quadrature equals (5/32) alpha Lambda (0.961 MeV)
- OK: the classical Coulomb estimate lies inside E_em +- its error (cross-check of the scale) (0.96 MeV vs 0.63 +- 0.40)
- OK: unification relation of Ferreira et al. with R ~ 30, S ~ 160 gives Delta mu/mu = -24.3 Delta alpha/alpha
- OK: line fit: for R -> 0 the alpha estimate is the alpha datum alone
- OK: Earth's surface potential G M / (R c^2) and the Sun's annual change 2 e G M_sun / (AU c^2) are both below 1e-9
- OK: Cs-Rb disagreement exceeds 5 standard deviations (Morel et al.) (5.49)
- OK: a_e difference and alpha^-1 difference give the same significance (linear map)
- OK: a_mu: world average minus WP25 reproduces 38(63)e-11
- OK: one-loop running: integrator equals the closed form 1/alpha_i(t) = 1/alpha_i(0) - b_i t / 2pi to 1e-8
- OK: two-loop running: tolerances 1e-10 and 1e-12 agree to 1e-7
- OK: inputs reproduce alpha-hat: 1/alpha = (5/3) 1/alpha_1 + 1/alpha_2
- OK: SM: smallest spread at a crossing is not above the grid minimum and within 0.02 of it (3.1964 vs 3.2141)
- OK: MSSM: smallest spread at a crossing is not above the grid minimum and within 0.02 of it (0.0027 vs 0.0197)
- OK: Monte Carlo is reproducible with the fixed seed
- OK: proton lifetime estimate reproduces Part I / D8.1: 4.6e35 yr at M_X = 1e16 GeV and M_X > 4.8e15 GeV
- OK: MS-bar estimate (on-shell minus Erler's scheme offset) agrees with the PDG value 127.950 +- 0.017 used in D8.5 (127.960)
