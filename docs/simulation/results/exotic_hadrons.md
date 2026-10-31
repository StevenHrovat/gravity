# Hadrons as trees of dualities (H8): tetraquarks and pentaquarks against data

Workstream SM6 of *GUID v6*. Written by `docs/simulation/exotic_hadrons.py` (seed 20210901); every number is also in `exotic_hadrons.json`. Figures: `docs/simulation/figures/exotic_fit.pdf`, `exotic_spectrum.pdf`, `exotic_levels.pdf`, `exotic_thresholds.pdf`. Checks: **73 of 73 passed** (engine, hosting check, fit numerics, null distribution); every confrontation with data is a result, not a check. Runtime 66 s.

## Verdict

- **Model.** The colour-spin model of De Rujula, Georgi and Glashow in Karliner and Rosner's form reproduces KR's published numbers to 0.15 MeV (T_cc 3882.2, T_bb 10389.4, T_bc 7133.7, Xi_cc 3627). Refitted to 42 ordinary ground-state hadrons it has sigma_model = 8.1 MeV (24 dof; leave-one-out 11.2 MeV). The held-out Xi_cc++ comes out at 3642.9 +- 12.3 MeV against 3621.55 (pull +1.74).
- **(a) Compact exotics: 4 of 9 scored confrontations hold, 5 are refuted.** T_cc+ holds (3897.5 +- 12.2 against 3874.7, pull +1.86), but the model puts it +22 MeV from the D*+ D0 threshold where it is bound by 0.36 MeV. X0(2900), T_csbar(2900), X(6900) as an S-wave [cc][cbar cbar], P_c(4312) and P_psis(4338) are refuted. The three assignments by proximity (P_c(4440), P_c(4457), P_cs(4459)) hold, with chance probabilities 0.57, 0.24, 0.08.
- **Live predictions.** T_bb- at 10399 +- 12 MeV, -205 MeV below B B* (lattice: 83 to 189 MeV); T_bc 0+ at 7146 (+2 MeV from B0bar D0), T_bc 1+ at 7180 (-9 MeV from D0 B*); P_cc at 4232 MeV, +471 MeV above Xi_cc pi.
- **(b) Threshold proximity.** Of 26 established exotic hadrons, 13 lie within 10 MeV of an allowed S-wave two-hadron threshold where 7.0 are expected for random placement in +-150 MeV windows. Fisher's combined p = 5.4e-05 (W = 150 MeV; 4.1e-06 for W = 300 MeV). Without T_cc+ and X(3872), p = 0.06. Selection and look-elsewhere caveats below.
- **(c) Partners.** The compact (diquark-tree) reading of X(3872) predicts charged partners that BaBar and Belle exclude: a failed prediction. Our model itself places the compact 1++ state 237 MeV above X(3872). Every other predicted partner is untested or live.
- **H8 as such.** Any colour singlet can be written as a binary tree of colour-conjugate pairs (3 x 3 contains 3bar, 3 x 3bar contains 1), so the generic statement holds as a reading and cannot fail; with its either-or (compact or molecular) for every multiquark, it also cannot fail on any single state. Its content is in the model's masses, and there it fails more often than it holds.

## (a) Compact exotics and live predictions

Model P: KR's convention, parameters fitted here. P-in: no binding across the halves. J: universal masses plus junctions. Pull with sigma_pred and the data error on the side of the model; |pull| < 2 holds.

| state | J^P | model P [MeV] | P-in | J | data | pull | verdict | lowest S-wave threshold: M - T |
|---|---|---|---|---|---|---|---|---|
| T_cc+ (cc ubar dbar) | 1+ | 3897.5 +- 12.2 | 3897.5 | 3994.5 | 3874.7 (-0.1 +0.1) | +1.86 | holds | D*+ D0 3875.1: +22.4 |
| T_bb- (bb ubar dbar) | 1+ | 10399.4 +- 12.3 | 10399.4 | 10512.0 | - | - | live | B+~ B*0~ 10604.1: -204.7 |
| T_bc (bc ubar dbar), 0+ | 0+ | 7146.4 +- 11.1 | 7146.4 | 7251.2 | - | - | live | D0 B0~ 7144.5: +1.9 |
| T_bc (bc ubar dbar), 1+ | 1+ | 7180.1 +- 11.5 | 7180.1 | 7285.0 | - | - | live | D0 B*0~ 7189.6: -9.4 |
| X0(2900) (ud cbar sbar) | 0+ | 2754.8 +- 9.5 | 2754.8 | 2860.7 | 2866.0 (-7.3 +7.3) | -9.28 | refuted | K0 D0~ 2362.5: +392.4 |
| T_csbar0(2900) (c sbar u dbar) | 0+ | 2808.5 +- 8.9 | 2825.1 | 2915.9 | 2908.0 (-22.8 +22.8) | -4.06 | refuted | pi+ Ds+ 2107.9: +700.6 |
| cc cbar cbar 2++ vs X(6900) | 2++ | 6424.9 +- 28.7 | 6672.4 | 6514.9 | 6905.0 (-13.0 +13.0) | -15.22 | refuted | J/psi J/psi 6193.8: +231.1 |
| cc cbar cbar 0++ vs X(6900) | 0++ | 6340.3 +- 26.5 | 6587.8 | 6430.3 | 6905.0 (-13.0 +13.0) | -19.14 | info | eta_c eta_c 5968.2: +372.1 |
| cc cbar cbar 1+- | 1+- | 6368.5 +- 26.9 | 6616.0 | 6458.5 | - | - | live | eta_c J/psi 6081.0: +287.5 |
| P_c(4312) (lowest uud c cbar) |  | 4276.8 +- 11.4 | 4338.7 | 4485.1 | 4311.9 (-0.9 +6.8) | -3.06 | refuted | eta_c p 3922.4: +354.4 |
| P_c(4440) (nearest level) |  | 4428.4 +- 11.1 | 4396.3 | 4485.1 | 4440.3 (-4.9 +4.3) | -0.98 | holds | eta_c p 3922.4: +506.0 |
| P_c(4457) (nearest level) |  | 4461.8 +- 11.1 | 4490.3 | 4485.1 | 4457.3 (-1.8 +4.1) | +0.38 | holds | eta_c p 3922.4: +539.4 |
| P_psis(4338) (lowest I=0, J=1/2) | 1/2- | 4392.0 +- 11.1 | 4470.4 | 4601.5 | 4338.2 (-0.8 +0.8) | +4.81 | refuted | eta_c Lambda 4099.8: +292.2 |
| P_cs(4459) (nearest level; evidence only) |  | 4460.3 +- 10.9 | 4470.4 | 4601.5 | 4458.8 (-3.1 +5.5) | +0.13 | holds | eta_c Lambda 4099.8: +360.5 |
| P_cc ([cc][ud] qbar), lowest | 1/2- | 4231.7 +- 12.2 | 4231.7 | 4435.6 | - | - | live | pi+~ Xi_cc++ 3761.1: +470.6 |
| compact X(3872): [cq][cbar qbar] 1++ | 1++ | 4108.2 +- 11.2 | 4170.1 | 4212.1 | 3871.7 (-0.1 +0.1) | +21.03 | info | D0 D*0~ 3871.7: +236.5 |
| compact Z_c(3900): [cq][cbar qbar] 1+- | 1+- | 3985.2 +- 11.3 | 4047.1 | 4087.1 | 3899.0 (-6.1 +6.1) | +6.72 | info | pi+ J/psi 3236.5: +748.7 |
| T_cc partner I=1, J=0 | 0+ | 4041.5 +- 12.1 | 4041.5 | 4143.2 | - | - | live | D0 D0 3729.7: +311.8 |
| T_bb partner I=1, J=0 | 0+ | 10583.2 +- 12.2 | 10583.2 | 10700.3 | - | - | live | B+~ B+~ 10558.7: +24.5 |
| T_cc partner I=1, J=1 | 1+ | 4071.2 +- 12.1 | 4071.2 | 4172.9 | - | - | live | D0 D*0 3871.7: +199.5 |
| T_bb partner I=1, J=1 | 1+ | 10593.0 +- 12.2 | 10593.0 | 10710.2 | - | - | live | B+~ B*+~ 10604.1: -11.1 |
| T_cc partner I=1, J=2 | 2+ | 4130.6 +- 12.2 | 4130.6 | 4232.3 | - | - | live | D*0 D*0 4013.7: +116.9 |
| T_bb partner I=1, J=2 | 2+ | 10612.7 +- 12.2 | 10612.7 | 10730.0 | - | - | live | B*+~ B*+~ 10649.5: -36.8 |
| X0 partner [ud]0[cbar sbar]1, 1+ | 1+ | 2807.3 +- 9.2 | 2807.3 | 2907.7 | - | - | live | K+ D*+~ 2503.9: +303.3 |

- T_bb- (bb ubar dbar): model binding -204.7 +- 12.3 MeV; lattice: Francis2017 -189 (pull -1.0), Leskovec2019 -128 (pull -2.7), Aoki2023 -83 (pull -4.8), Hudspith2023 -112 (pull -5.1), Tripathy2025 -116 (pull -2.3)
- T_bc (bc ubar dbar), 1+: model binding -9.4 +- 11.5 MeV; lattice: Francis2019 -38 (pull +1.1), Padmanath2024 -43 (pull +1.8)
- T_bc (bc ubar dbar), 0+: model binding +1.9 +- 11.1 MeV; lattice: ; Alexandrou2024: shallow bound or virtual states a few MeV or less below the B(*) Dbar thresholds (no number in the abstract)

## Fit to ordinary hadrons

| parameter | value | 1 sigma |
|---|---|---|
| m^m_q | 309.6 | 2.1 |
| m^m_s | 481.8 | 3.1 |
| m^m_c | 1658 | 5.2 |
| m^m_b | 5002 | 5.4 |
| m^b_q | 364 | 1.4 |
| m^b_s | 536 | 1.8 |
| m^b_c | 1716 | 4.4 |
| m^b_b | 5048 | 4.5 |
| b/(310)^2 | 79.32 | 1.5 |
| a/(363)^2 | 51.14 | 1 |
| k_s | 1.789 | 0.12 |
| B1(c sbar) | -66.12 | 6.7 |
| B1(b sbar) | -80.39 | 7 |
| B1(c cbar) | -247.5 | 12 |
| B1(b bbar) | -558.4 | 13 |
| B1(b cbar) | -334.6 | 12 |
| v(c cbar) | 28.2 | 2.9 |
| v(b bbar) | 15.39 | 2.9 |

KR's values: m^m = 310, 483, 1663.3, 5003.8; m^b = 363, 538, 1710.5, 5043.5; b/310^2 = 80; a/363^2 = 50; a_cs/a = 1.646; B1 = -69.9, -83.6, -258.0, -562.8, -341.5. Scheme J: S = 160.6 MeV, sigma_model = 8.25 MeV.

| hadron | input [MeV] | source | model - input |
|---|---|---|---|
| pi | 138.00 | KR2014 Table II | +4.0 |
| rho | 775.00 | KR2014 Table II | +3.2 |
| omega | 782.66 | PDG2024 | -4.4 |
| K | 496.00 | KR2014 Table II | -11.2 |
| K* | 893.71 | PDG2024 (K*+ hadroproduced, K*0) | -0.1 |
| phi | 1019.46 | PDG2024 | +9.9 |
| D | 1867.25 | PDG2024 | +11.3 |
| D* | 2008.55 | PDG2024 | -11.2 |
| Ds | 1968.35 | PDG2024 | +3.0 |
| Ds* | 2112.20 | PDG2024 | -4.3 |
| B | 5279.40 | KR2014 eq.(7) | +2.3 |
| B* | 5324.75 | PDG2024 | -3.7 |
| Bs | 5366.77 | KR2014 eq.(10) | +2.4 |
| Bs* | 5415.40 | KR2014 eq.(10) | -1.0 |
| eta_c | 2984.10 | PDG2024 | +0.0 |
| J/psi | 3096.90 | PDG2024 | -0.0 |
| eta_b | 9398.70 | PDG2024 | +0.0 |
| Upsilon | 9460.28 | KR2014 eqs.(16),(18) | +0.0 |
| Bc | 6274.50 | KR2014 eq.(19) | +0.0 |
| N | 939.00 | KR2014 Table I | +0.3 |
| Delta | 1232.00 | KR2014 Table I | +12.5 |
| Lambda | 1116.00 | KR2014 Table I | -4.6 |
| Sigma | 1193.00 | KR2014 Table I | -16.3 |
| Sigma* | 1385.00 | KR2014 Table I | -1.1 |
| Xi | 1318.00 | KR2014 Table I | +3.3 |
| Xi* | 1530.00 | KR2014 Table I | -1.5 |
| Omega | 1672.00 | KR2014 Table I | +6.4 |
| Lambda_c | 2286.46 | PDG2024 | +4.8 |
| Sigma_c | 2453.40 | KR2014 Table IV | -1.9 |
| Sigma_c* | 2518.10 | KR2014 Table IV | -1.8 |
| Xi_c | 2469.07 | PDG2024 | +10.1 |
| Xi_c' | 2578.70 | PDG2024 (Xi_c'0) | -9.2 |
| Xi_c* | 2645.90 | KR2014 Table IV | -4.7 |
| Omega_c | 2695.20 | PDG2024 | -2.4 |
| Omega_c* | 2765.90 | PDG2024 | +5.5 |
| Lambda_b | 5619.50 | KR2014 Table V | +3.6 |
| Sigma_b | 5814.26 | KR2014 Table V | -2.3 |
| Sigma_b* | 5833.83 | KR2014 Table V | +0.1 |
| Xi_b | 5792.68 | KR2014 Table V | +11.3 |
| Xi_b' | 5935.06 | LHCb_Xibprime + KR2014 Table V (Xi_b0) + m(pi-) | -9.2 |
| Xi_b* | 5952.30 | PDG2024 (Xi_b(5945)0) | -2.1 |
| Omega_b | 6046.38 | KR2014 Table V | -1.4 |

## (b) Threshold proximity

| state | M [MeV] | J^P(C) | nearest allowed S-wave threshold | T [MeV] | M - T | p (W=150) | p (W=300) | source |
|---|---|---|---|---|---|---|---|---|
| chi_c1(3872) | 3871.7 | 1++ | D0 D*0~ | 3871.7 | +0.0 | 0.0001 | 0.0001 | LHCb_X3872_ls |
| Z_c(3900)+ | 3899.0 | 1+ | pi+ psi(3770) (u) | 3913.3 | -14.3 | 0.3852 | 0.1926 | BESIII_Zc3900 |
| Z_c(4020)+ | 4022.9 | ?? | D*0~ D*+ | 4017.1 | +5.8 | 0.1085 | 0.1387 | BESIII_Zc4020 |
| Z_c(4430)+ | 4475.0 | 1+ | D1(2420)0~ D1(2420)+ (u) | 4848.3 | -373.3 | 0.7180 | 0.8590 | LHCb_Z4430 |
| Z_cs(3985)+ | 3982.5 | ?? | D0~ Ds*+ | 3977.0 | +5.5 | 0.3398 | 0.2261 | BESIII_Zcs3985 |
| Z_cs(4000)+ | 4003.0 | 1+ | K*+ J/psi | 3988.8 | +14.2 | 0.3297 | 0.2596 | LHCb_JpsiK |
| Z_cs(4220)+ | 4216.0 | 1? | K+ psi(2S) | 4179.8 | +36.2 | 0.8934 | 0.8905 | LHCb_JpsiK |
| chi_c1(4140) | 4118.0 | 1++ | phi J/psi | 4116.4 | +1.6 | 0.0219 | 0.0225 | LHCb_JpsiK |
| chi_c1(4274) | 4294.0 | 1++ | omega psi(2S) | 4468.8 | -174.8 | 0.9904 | 0.9952 | LHCb_JpsiK |
| chi_c0(4500) | 4474.0 | 0++ | omega psi(2S) | 4468.8 | +5.2 | 0.1049 | 0.1223 | LHCb_JpsiK |
| chi_c0(4700) | 4694.0 | 0++ | phi psi(2S) | 4705.6 | -11.6 | 0.4231 | 0.3983 | LHCb_JpsiK |
| X(4685) | 4684.0 | 1++ | phi psi(2S) | 4705.6 | -21.6 | 0.4935 | 0.5071 | LHCb_JpsiK |
| X(4630) | 4626.0 | 1-+ | Ds*+ Ds1(2536)+~ | 4647.3 | -21.3 | 0.7875 | 0.5861 | LHCb_JpsiK |
| X(3960) | 3956.0 | 0++ | eta' eta_c (u) | 3941.9 | +14.1 | 0.3349 | 0.4126 | LHCb_X3960 |
| psi(4230) | 4222.0 | 1-- | omega chi_c0 | 4197.4 | +24.6 | 0.5876 | 0.5308 | BESIII_Y4230 |
| Z_b(10610)+ | 10607.2 | ?? | B0~ B*+ (u) | 10604.4 | +2.8 | 0.0755 | 0.0729 | Belle_Zb |
| Z_b(10650)+ | 10652.2 | ?? | B*+ B*0~ | 10649.5 | +2.7 | 0.0551 | 0.0708 | Belle_Zb |
| T_cc(3875)+ | 3874.7 | 1+ | D0 D*+ | 3875.1 | -0.4 | 0.0072 | 0.0036 | LHCb_Tcc_NC |
| X0(2900) | 2866.0 | 0+ | K*+ D*+~ | 2902.1 | -36.1 | 0.2418 | 0.1209 | LHCb_X2900 |
| X1(2900) | 2904.0 | 1- | K0 D1(2420)0~ (u) | 2919.7 | -15.7 | 0.1053 | 0.0526 | LHCb_X2900 |
| T_csbar0(2900)++ | 2908.0 | 0+ | K*+ D*+ | 2902.1 | +5.9 | 0.0391 | 0.0195 | LHCb_Tcsbar |
| P_c(4312)+ | 4311.9 | ?? | D0~ Sigma_c+ (u) | 4317.5 | -5.6 | 0.2508 | 0.2603 | LHCb_Pc2019 |
| P_c(4440)+ | 4440.3 | ?? | chi_c1 p (u) | 4448.9 | -8.6 | 0.5527 | 0.4266 | LHCb_Pc2019 |
| P_c(4457)+ | 4457.3 | ?? | D0~ Lambda_c(2595)+ | 4457.1 | +0.2 | 0.0224 | 0.0154 | LHCb_Pc2019 |
| P_psis(4338)0 | 4338.2 | 1/2- | D+~ Xi_c+ | 4337.4 | +0.8 | 0.0631 | 0.0482 | LHCb_Ppsis4338 |
| X(6900) | 6905.0 | ??+ | chi_c0 chi_c1 | 6925.4 | -20.4 | 0.8595 | 0.7267 | LHCb_X6900 |

(u): a threshold hadron mass not re-read. Fisher X2 = 101.1 (52 dof), p = 5.36e-05; W = 300: p = 4.13e-06. Within 5/10/20 MeV: 7/13/18 observed, 3.82/6.99/12.19 expected (Poisson p 0.093/0.027/0.071). Below the nearest threshold: 12 of 26. Mean number of allowed thresholds per window: 5.5. Unverified threshold masses perturbed by 1 MeV: p from 7.0e-06 to 7.5e-05; by 3 MeV: 5.0e-07 to 1.4e-04. States with measured J^P only (17): p = 1.8e-04. Without T_cc+ and X(3872): p = 0.057.

## (c) Partners

- **C1** compact (diquark-tree) X(3872) = [cq][cbar qbar] 1++ has charged isospin partners X+- at about the X(3872) mass, produced in B -> X- K at twice the neutral rate (Maiani et al. 2005; the isovector hypothesis of BaBar). *Search:* BaBar: B(B0 -> X- K+, X- -> J/psi pi- pi0) < 5.4e-6 (90% CL) where 2.56e-5 (75+-25 events) was expected; likelihood ratio 1.1e4 for no signal. Belle: limits well below the isospin-triplet expectation. **refuted (failed prediction of the compact X(3872) reading)**.
- **C2** our model's compact 1++ isomultiplet (I = 0 and 1 degenerate) at 4108 +- 11 MeV, 237 MeV above X(3872): the model does not make X(3872) compact; its charged 1++ partners lie near 4.1 GeV. *Search:* no search for a charged C = + (G = -) hidden-charm state near 4.1 GeV verified. **untested**.
- **C3** T_cc isospin partners [cc]_1[qbar qbar]_1 (I = 1) with J = 0, 1, 2 at 4042, 4071, 4131 MeV, i.e. +312, +200, +117 MeV above their lowest S-wave thresholds (open, so broad); no isoscalar spin partner (a good antidiquark has spin 0). *Search:* LHCb: no narrow signal in D+ D0 pi+ (3.9-4.0 GeV) or D+ D+ (up to 3.87 GeV); the isovector reading of T_cc+ itself is disfavoured. The predicted I = 1 states lie above these windows and would be broad. **consistent (the model's T_cc+ is isoscalar); the I = 1 partners are untested**.
- **C4** T_bb isospin partners (I = 1) with J = 0, 1, 2 at 10583, 10593, 10613 MeV, +25, -11, -37 MeV from their lowest S-wave thresholds. *Search:* none (no doubly bottom hadron observed). **live**.
- **C5** hidden-charm pentaquark multiplet: 10 S-wave levels with I = 1/2 from 4277 to 4584 MeV, and I = 3/2 partners degenerate with the 7 levels that contain a spin-1 light diquark. *Search:* LHCb Lambda_b -> J/psi p K- shows three narrow peaks; no search for I = 3/2 (doubly charged) hidden-charm pentaquarks verified; production in Lambda_b decay favours the spin-0 [ud] diquark (MPR 2015), so absent peaks do not exclude partners. **untested**.
- **C6** fully charmed S-wave triplet 0++, 1+-, 2++ at 6340, 6369, 6425 MeV; the 1+- cannot decay to J/psi J/psi. *Search:* di-J/psi structures of LHCb, CMS, ATLAS (Table of Section A); no 1+- channel searched. **the S-wave triplet is not X(6900) (Section A); untested otherwise**.
- **C7** X0(2900) partner [ud]_0[cbar sbar]_1 with J^P = 1+ at 2807 MeV. *Search:* a 1+ state cannot decay to D- K+ (two pseudoscalars); not visible in the LHCb analysis. **untested**.

## Choices made after seeing the data

1. The rule for binding across the two halves (primary: KR's factorised potential applied to every pair; variant P-in: no binding across the root) was written into the script before any exotic state was computed, but by authors who knew the published masses of the exotic states. Both rules are reported for every state; they differ only where a heavy or strange pair sits in different halves (hidden-charm and fully charmed states, P_c, T_csbar).
2. k_s (KR's heavy-strange hyperfine enhancement a_cs = a_bs) is shared between mesons and baryons. KR apply it in baryons only; the extension was fixed before the fit, motivated by KR's own observation that the D_s* - D_s splitting is enhanced by the same factor, not by any exotic comparison.
3. For each catalogue state one measurement was taken: the most recent one of the cited collaboration that we could read (LHCb 2021 for the J/psi phi states, not the 2016 values; the BESIII discovery values for Z_c(3900) and Z_c(4020), not PDG averages, which we could not read). The catalogue excludes X(3915) (exotic status disputed), P_cs(4459) and P_c(4337) (evidence below 5 sigma).
4. The chance-proximity numbers for the three 'nearest level' assignments (p_chance) were added after seeing that they hold.
5. Tests B5 (states with measured J^P only) and B6 (without the two states within 1 MeV of a threshold) were added after seeing the Fisher result, to show what drives it.
6. The CMS and ATLAS di-J/psi structures are shown with the fully charmed levels but not scored; that the lowest ATLAS structure (6.41 GeV) lies near the model's S-wave levels was noticed after the comparison and is not a test.

## Caveats

- Effective-mass conventions dominate the multiquark predictions. Baryon masses for every constituent (KR) and universal masses with string junctions (variant J) differ by about 100 MeV for every tetraquark and 110-210 MeV for pentaquarks, ten times sigma_model; the fit to ordinary hadrons cannot choose between them (sigma_model 8.1 and 8.3 MeV).
- sigma_model is the spread of ordinary hadrons. It does not include the uncertainty of carrying the model to four and five constituents (colour configurations outside the H8 tree, the spatial size of a diquark pair, binding across the halves).
- The H8 tree keeps one colour configuration (3bar x 3 for tetraquarks). The full colour-spin model also has 6 x 6bar; mixing would lower the lowest levels, mostly for the fully heavy and hidden-charm states.
- Only S-wave ground states are computed. Radial and orbital excitations (X1(2900) is 1-) are outside the model, so a mismatch refutes an S-wave assignment, not every compact reading.
- Threshold test: the catalogue is not a random sample. Many exotic states were found as narrow structures near thresholds, and threshold cusps can mimic peaks, so proximity is partly a selection effect. The threshold list (hadrons narrower than 60 MeV) and the S-wave and C rules set the look-elsewhere count, on average 5.5 thresholds per +-150 MeV window; isospin and G parity are not imposed.
- Threshold proximity is the standard signature of hadronic molecules and of threshold cusps in QCD; it supports the molecular branch of H8 only in the sense that H8 includes that branch.
- Lattice QCD results for T_bb scatter from 83 to 189 MeV binding; the comparison is not a measurement.

## Citations (what was read, the values used)

- **DGG1975**: A. De Rujula, H. Georgi, S. L. Glashow, Phys. Rev. D 12, 147 (1975). Read: cited for the colour-spin (chromomagnetic) hyperfine interaction; not re-read (no arXiv version). Values: none used.
- **KR2014**: M. Karliner, J. L. Rosner, Phys. Rev. D 90, 094007 (2014), arXiv:1408.5877. Read: full text: Tables I, II, IV, VI, VII, IX; eqs. (1)-(20). Values: m^b_q=363, m^b_s=538, a/(m^b_q)^2=50, m^m_q=310, m^m_s=483, b/(m^m_q)^2=80, m^m_c=1663.3, m^b_c=1710.5, m^m_b=5003.8, m^b_b=5043.5, B(cs bar)=-69.9, B(cs)=-35.0, B(bs bar)=-83.6, 6a_cs/(m_s m_c)=70.7, a_bs=(70.7/43.0)a, Mbar(cc bar)=3068.6, M(J/psi)-M(eta_c)=113.2, Mbar(bb bar)=9444.7, M(Upsilon)-M(eta_b)=62.3, M(B_c)=6274.5, B_c* - B_c = 68.0, p=1.46; hadron masses quoted in the tables (PDG 2012 and KR's b-baryon averages); predictions Xi_cc=3627+-12, Xi_cc*=3690, Xi_bb=10162, Xi_bb*=10184.
- **KR2017**: M. Karliner, J. L. Rosner, Phys. Rev. Lett. 119, 202001 (2017), arXiv:1707.07666. Read: full text: Tables I-III, Secs. II, III, VI. Values: T(bb ubar dbar) 1+ = 10389.4+-12 (215 below BB* at 10604; 170 below B- B0bar gamma at 10559); T(cc ubar dbar) 1+ = 3882.2+-12 (7 above D0 D*+ at 3875); T(bc ubar dbar) 0+ = 7133.7+-13 (11 below B0bar D0 at 7144.5); M(D0)+M(D*+)=3875.09+-0.07; string-junction term S=165 MeV.
- **KNR2017**: M. Karliner, S. Nussinov, J. L. Rosner, Phys. Rev. D 95, 034011 (2017), arXiv:1611.00348. Read: Sec. II, eqs. (1)-(8). Values: S=165.1, m_c=1655.6, m_b=4988.6, M(cc,3bar)=3204.1, B=-388.3, Delta M_3=79.3, M(cc cbar cbar, 0++) = 6191.5 (abstract 6192+-25); J/psi J/psi threshold 6193.8.
- **LHCb_Tcc_NP**: LHCb, Nature Phys. 18, 751 (2022), arXiv:2109.01038. Read: abstract. Values: narrow state just below the D*+ D0 threshold, mass about 3875 MeV.
- **LHCb_Tcc_NC**: LHCb, Nature Commun. 13, 3351 (2022), arXiv:2109.01056. Read: full text, eqs. (1), (4), (5), (12), Table 2, Fig. 4 and conclusions. Values: delta m_U = -359+-40 (+9 -6) keV; pole delta m = -360+-40 (+4 -0) keV, Gamma_pole = 48+-2 (+0 -14) keV; delta m_BW = -273+-61 keV; J^P = 1+ favoured; no signal in D+D0pi+ (3.9-4.0 GeV) or D+D+ (to 3.87 GeV): isovector interpretation disfavoured.
- **LHCb_X6900**: LHCb, Sci. Bull. 65, 1983 (2020), arXiv:2006.16957. Read: full text, Sec. 5 and conclusions. Values: model I: m = 6905+-11+-7, Gamma = 80+-19+-33; model II: m = 6886+-11+-11, Gamma = 168+-33+-69; broad structure 6.2-6.8 GeV.
- **CMS_diJpsi**: CMS, Phys. Rev. Lett. 132, 111901 (2024), arXiv:2306.07164. Read: abstract and Table I. Values: no interference: 6552+-10+-12 (Gamma 124), 6927+-9+-4 (122), 7287+20-18+-5 (95); interference: 6638+43+16-38-31, 6847+44+48-28-20, 7134+48+41-25-15.
- **ATLAS_diJpsi**: ATLAS, Phys. Rev. Lett. 131, 151902 (2023), arXiv:2304.08962. Read: Table 2. Values: model A: 6.41+-0.08(+0.08-0.03), 6.63+-0.05(+0.08-0.01), 6.86+-0.03(+0.01-0.02) GeV; model B: 6.65+-0.02(+0.03-0.02), 6.91+-0.01+-0.01 GeV.
- **LHCb_X2900**: LHCb, Phys. Rev. D 102, 112003 (2020), arXiv:2009.00026 (and PRL 125, 242001, arXiv:2009.00025). Read: full text, Table 4 and conclusions. Values: X0(2900): spin 0, M = 2866+-7+-2, Gamma = 57+-12+-4; X1(2900): spin 1, M = 2904+-5+-1, Gamma = 110+-11+-4; D-K+ channel, minimal content cbar d sbar u.
- **LHCb_Tcsbar**: LHCb, Phys. Rev. Lett. 131, 041902 (2023), arXiv:2212.02716. Read: abstract. Values: M = 2908+-11+-20, Gamma = 136+-23+-11, J^P = 0+, isospin triplet (D_s+ pi+ and D_s+ pi-).
- **LHCb_Pc2019**: LHCb, Phys. Rev. Lett. 122, 222001 (2019), arXiv:1904.03947. Read: full text, Table 1 and text. Values: P_c(4312): 4311.9+-0.7(+6.8-0.6), Gamma 9.8+-2.7(+3.7-4.5); P_c(4440): 4440.3+-1.3(+4.1-4.7), Gamma 20.6+-4.9(+8.7-10.1); P_c(4457): 4457.3+-0.6(+4.1-1.7), Gamma 6.4+-2.0(+5.7-1.9); 7.3 sigma and 5.4 sigma; J^P not determined.
- **LHCb_Pcs4459**: LHCb, Sci. Bull. 66, 1278 (2021), arXiv:2012.10380. Read: abstract. Values: evidence: M = 4458.8+-2.9(+4.7-1.1), Gamma = 17.3+-6.5(+8.0-5.7).
- **LHCb_Ppsis4338**: LHCb, Phys. Rev. Lett. 131, 031901 (2023), arXiv:2210.10346. Read: abstract. Values: M = 4338.2+-0.7+-0.4, Gamma = 7.0+-1.2+-1.3, J = 1/2, negative parity preferred.
- **MPR2015**: L. Maiani, A. D. Polosa, V. Riquer, Phys. Lett. B 749, 289 (2015), arXiv:1507.04980. Read: full text. Values: P = epsilon cbar [cq]_{s=0,1} [q'q'']_{s=0,1}, colour-3bar units; S-wave multiplicities J=1/2 (2), 3/2 (1) for s(q'q'')=0 and 1/2 (3), 3/2 (3), 5/2 (1) for s=1.
- **MPPR2005**: L. Maiani, F. Piccinini, A. D. Polosa, V. Riquer, Phys. Rev. D 71, 014028 (2005), hep-ph/0412098. Read: abstract. Values: X(3872) as [cq][cbar qbar] with two neutral components and charged partners X+-.
- **BaBar_Xminus**: BaBar, Phys. Rev. D 71, 031501 (2005), hep-ex/0412051. Read: full text. Values: B(B0 -> X- K+, X- -> J/psi pi- pi0) < 5.4e-6, B(B- -> X- K0bar) < 22e-6 (90% CL); isovector X predicts 75+-25 events, 2.56e-5; null favoured by likelihood ratio 1.1e4.
- **Belle_X3872**: Belle, Phys. Rev. D 84, 052004 (2011), arXiv:1107.0163. Read: abstract. Values: charged-partner limits well below the isospin-triplet expectation; M = 3871.84+-0.27+-0.19.
- **Francis2017**: A. Francis, R. J. Hudspith, R. Lewis, K. Maltman, Phys. Rev. Lett. 118, 142001 (2017), arXiv:1607.05214. Read: abstract. Values: ud bbar bbar 1+ 189(10) MeV below threshold.
- **Leskovec2019**: L. Leskovec, S. Meinel, M. Pflaumer, M. Wagner, Phys. Rev. D 100, 014503 (2019), arXiv:1904.04197. Read: abstract. Values: binding -128+-24+-10 MeV, mass 10476+-24+-10 MeV.
- **Aoki2023**: T. Aoki, S. Aoki, T. Inoue, Phys. Rev. D 108, 054502 (2023), arXiv:2306.03565. Read: abstract. Values: 83(10) MeV below B B* (coupled channel), +-20 MeV systematic; single channel 155(17).
- **Hudspith2023**: R. J. Hudspith, D. Mohler, Phys. Rev. D 107, 114510 (2023), arXiv:2303.17295. Read: abstract. Values: 112.0(13.2) MeV below B B*.
- **Tripathy2025**: B. S. Tripathy, N. Mathur, M. Padmanath, arXiv:2503.09760 (2025). Read: abstract. Values: Delta E = -116 (+30 -36) MeV relative to B B*.
- **Francis2019**: A. Francis, R. J. Hudspith, R. Lewis, K. Maltman, Phys. Rev. D 99, 054505 (2019), arXiv:1810.10550. Read: abstract. Values: ud cbar bbar 0(1+) 15 to 61 MeV below Dbar B*.
- **Padmanath2024**: M. Padmanath, A. Radhakrishnan, N. Mathur, Phys. Rev. Lett. 132, 201902 (2024), arXiv:2307.14128. Read: abstract. Values: 1+: -43(+6-7)(+14-24) MeV with respect to D Bbar*.
- **Alexandrou2024**: C. Alexandrou et al., Phys. Rev. Lett. 132, 151902 (2024), arXiv:2312.02925. Read: abstract. Values: shallow bound or virtual states a few MeV or less below the B(*) Dbar thresholds.
- **LHCb_X3872_ls**: LHCb, Phys. Rev. D 102, 092005 (2020), arXiv:2005.13419. Read: abstract. Values: m(chi_c1(3872)) - m(psi(2S)) = 185.598+-0.067+-0.068; Gamma_BW = 1.39+-0.24+-0.10.
- **LHCb_X3872_JPC**: LHCb, Phys. Rev. Lett. 110, 222001 (2013), arXiv:1302.6269. Read: abstract. Values: J^PC = 1++.
- **BESIII_Zc3900**: BESIII, Phys. Rev. Lett. 110, 252001 (2013), arXiv:1303.5949. Read: abstract. Values: 3899.0+-3.6+-4.9, Gamma 46+-10+-20.
- **BESIII_Zc3900_JP**: BESIII, Phys. Rev. Lett. 119, 072001 (2017), arXiv:1706.04100. Read: abstract. Values: J^P = 1+.
- **BESIII_Zc4020**: BESIII, Phys. Rev. Lett. 111, 242001 (2013), arXiv:1309.1896. Read: abstract. Values: 4022.9+-0.8+-2.7, Gamma 7.9+-2.7+-2.6.
- **LHCb_Z4430**: LHCb, Phys. Rev. Lett. 112, 222002 (2014), arXiv:1404.1903. Read: full text. Values: 4475+-7(+15-25), Gamma 172+-13(+37-34), J^P = 1+.
- **BESIII_Zcs3985**: BESIII, Phys. Rev. Lett. 126, 102001 (2021), arXiv:2011.07855. Read: abstract. Values: pole 3982.5(+1.8-2.6)+-2.1, Gamma 12.8(+5.3-4.4)+-3.0; 5.3 sigma.
- **LHCb_JpsiK**: LHCb, Phys. Rev. Lett. 127, 082001 (2021), arXiv:2103.01803. Read: abstract and Table 1. Values: Zcs(4000) 1+ 4003+-6(+4-14), Gamma 131+-15+-26; Zcs(4220) 1+ or 1- 4216+-24(+43-30), Gamma 233; X(4140) 1+ 4118+-11(+19-36), Gamma 162; X(4274) 1+ 4294+-4(+3-6), Gamma 53; X(4500) 0+ 4474+-3+-3, Gamma 77; X(4700) 0+ 4694+-4(+16-3), Gamma 87; X(4685) 1+ 4684+-7(+13-16), Gamma 126; X(4630) 1- 4626+-16(+18-110), Gamma 174; all above 5 sigma.
- **LHCb_JpsiPhi2016**: LHCb, Phys. Rev. Lett. 118, 022003 (2017), arXiv:1606.07895. Read: full text, Table 2. Values: X(4140) and X(4274) J^PC = 1++, X(4500) and X(4700) 0++.
- **LHCb_X3960**: LHCb, Phys. Rev. Lett. 131, 071901 (2023), arXiv:2210.15153. Read: abstract. Values: 3956+-5+-10, Gamma 43+-13+-8, J^PC = 0++, > 12 sigma.
- **BESIII_Y4230**: BESIII, Phys. Rev. Lett. 118, 092001 (2017), arXiv:1611.01317. Read: abstract. Values: 4222.0+-3.1+-1.4, Gamma 44.1+-4.3+-2.0 (e+e- -> pi+pi- J/psi, J^PC = 1--).
- **Belle_Zb**: Belle, Phys. Rev. Lett. 108, 122001 (2012), arXiv:1110.2251. Read: abstract. Values: 10607.2+-2.0, Gamma 18.4+-2.4; 10652.2+-1.5, Gamma 11.5+-2.2.
- **LHCb_Xicc**: LHCb, JHEP 02 (2020) 049, arXiv:1911.08594. Read: abstract. Values: M(Xi_cc++) = 3621.55+-0.23+-0.30.
- **LHCb_Xibprime**: LHCb, Phys. Rev. Lett. 114, 062004 (2015), arXiv:1411.4849. Read: abstract. Values: m(Xi_b'-) - m(Xi_b0) - m(pi-) = 3.653+-0.018+-0.006.
- **PDG2024**: S. Navas et al. (Particle Data Group), Phys. Rev. D 110, 030001 (2024) and 2025 update. Read: listings returned by web search (pdgLive, the 2024/2025 listings): D0 1864.84, D+ 1869.66, D*0 2006.85, D*+ 2010.26, D_s 1968.35, D_s* 2112.2, D2*(2460)0 2461.1, D_s1(2536) 2535.11, eta_c 2984.1, J/psi 3096.900, chi_c0 3414.71, chi_c1 3510.67, h_c 3525.37, chi_c2 3556.17, eta_c(2S) 3637.7, psi(2S) 3686.097, eta_b 9398.7, h_b(1P) 9899.3, B* 5324.75, omega 782.66, phi 1019.461, K*(892)0 895.55, K*(892)+ 891.88, Lambda_c 2286.46, Xi_c+ 2467.71, Xi_c0 2470.44, Xi_c'0 2578.7, Lambda_c(2595) 2592.25, Lambda_c(2625) 2628.11, Omega_c 2695.2, Omega_c(2770) 2765.9, Sigma(1385)+ 1382.83, Sigma(1385)0 1383.7, Xi_b- 5797.0, Sigma_b*+ 5830.32, Xi_b(5945)0 5952.3; D_s0*(2317) 2317.7 and D_s1(2460) 2459.5 as quoted in arXiv:2409.05337. Values: see THRESH_HADRONS; entries not in this list are PDG 2024 values not re-read (unverified).

## Checks

73 of 73 passed.

- OK E1 meson colour factor <lambda1.lambda2> (singlet)
- OK E2 meson spin singlet <sigma1.sigma2>
- OK E3 meson spin triplet <sigma1.sigma2>
- OK E4 baryon pair colour factor (3bar)
- OK E5 baryon pair colour factor (outer quark)
- OK E6 tetraquark diquark colour factor (3bar)
- OK E7 tetraquark cross colour factor (-4/3)
- OK E8 tetraquark colour sum = -32/3
- OK E9 pentaquark colour sum = -40/3
- OK E10 pentaquark diquark-diquark cross pair (-2/3)
- OK E11 pentaquark antiquark pair (-4/3)
- OK E12 MPR S-wave multiplicities, light diquark spin 0: J=1/2 (2), 3/2 (1)
- OK E13 MPR S-wave multiplicities, light diquark spin 1: J=1/2 (3), 3/2 (3), 5/2 (1)
- OK E14 Delta: sum of <sigma.sigma> = +3
- OK E15 [cq][cbar qbar] J=1: C eigenvalues {-1,-1,+1} (one 1++, two 1+-)
- OK E16 [cc]_1[cbar cbar]_1: C = +, -, + for J = 0, 1, 2
- OK H KR2014 Tables I-II N
- OK H KR2014 Tables I-II Delta
- OK H KR2014 Tables I-II Lambda
- OK H KR2014 Tables I-II Sigma
- OK H KR2014 Tables I-II Sigma*
- OK H KR2014 Tables I-II Xi
- OK H KR2014 Tables I-II Xi*
- OK H KR2014 Tables I-II Omega
- OK H KR2014 Tables I-II pi
- OK H KR2014 Tables I-II rho
- OK H KR2014 Tables I-II K
- OK H KR2014 Tables I-II K*
- OK H KR2014 Tables I-II phi
- OK H KR2014 eq.(1)-(2) D*-D = 8b/(m_q m_c)
- OK H KR2014 Sec.IV B*-B
- OK H KR2014 Sec.IV Bs*-Bs = 8b/(m_b m_s)
- OK H KR2014 Tables IV, VI Sigma_c
- OK H KR2014 Tables IV, VI Sigma_c*
- OK H KR2014 Tables IV, VI Xi_c
- OK H KR2014 Tables IV, VI Xi_c'
- OK H KR2014 Tables IV, VI Xi_c*
- OK H KR2014 Tables IV, VI Omega_c
- OK H KR2014 Tables IV, VI Omega_c*
- OK H KR2014 Tables IV, VI Sigma_b
- OK H KR2014 Tables IV, VI Sigma_b*
- OK H KR2014 Tables IV, VI Xi_b
- OK H KR2014 Tables IV, VI Xi_b'
- OK H KR2014 Tables IV, VI Xi_b*
- OK H KR2014 Tables IV, VI Omega_b
- OK H KR2014 Tables IV, VI Omega_b*
- OK H KR2014 Tables VII, IX Xi_cc
- OK H KR2014 Tables VII, IX Xi_cc*
- OK H KR2014 Tables VII, IX Xi_bb
- OK H KR2014 Tables VII, IX Xi_bb*
- OK H KR2014 Sec.VII power p of |psi(0)|^2 ~ mu^p
- OK H KR2014 Sec.VII Bc*-Bc
- OK H KR2014 eq.(19) spin-averaged bc: M(Bc)+3/4*68.0
- OK H KR2017 Table I T(bb ubar dbar) 1+
- OK H KR2017 Table II T(cc ubar dbar) 1+
- OK H KR2017 Table III T(bc ubar dbar) 0+
- OK H KR2017 T_bb - B B* threshold (10604)
- OK H KR2017 T_cc - D0 D*+ threshold (3875)
- OK H KR2017 T_bc - B0bar D0 threshold (7144.5)
- OK H KNR2017 p (binding power law)
- OK H KNR2017 B((cc)(cbar cbar))
- OK H KNR2017 Delta M_3
- OK H KNR2017 eq.(8) M(cc cbar cbar, 0++)
- OK F1 fit converged (scheme P, status 2)
- OK F3 Jacobian full rank (scheme P)
- OK F5 gradient of RSS at the minimum (scheme P, max |J^T r|)
- OK F2 fit converged (scheme J, status 2)
- OK F4 Jacobian full rank (scheme J)
- OK F6 gradient of RSS at the minimum (scheme J, max |J^T r|)
- OK F7 fit from a start 5% away reaches the same RSS
- OK F8 leave-one-out residuals at least as large as in-sample (RMS)
- OK B1 analytic null p-values agree with 20000 Monte Carlo placements per state (4.5 sigma)
- OK B2 Fisher statistic equals -2 sum ln p (consistency of chi2 tail)
