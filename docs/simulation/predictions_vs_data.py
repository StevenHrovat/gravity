"""GUID v6: every prediction of GUID (Part I of the v6 paper; version 5.1 where noted) that existing measurements reach, confronted
with those measurements.

Run:  python3 docs/simulation/predictions_vs_data.py
Needs numpy, scipy, matplotlib. Deterministic: no random numbers, no clock, no network, no machine name; the PDF figures are written
without a creation date. Runtime a few seconds, memory well under 200 MB.
Writes docs/simulation/results/predictions_vs_data.{json,md} and docs/simulation/figures/data_*.pdf.

Every measured number in this file was checked on 2026-10-31 against the publication: the arXiv abstract or full text where the
paper is on arXiv, otherwise the journal or collaboration record through a web search. CITATIONS below lists, for each source, the
reference, what was read and the value quoted. Numbers that could not be verified are left out, and the Markdown report says which.

Each confrontation prints the GUID prediction, the datum, the pull (in standard deviations) or the bound, and a verdict line. Every row
has one of four kinds (table KIND below):
  scored       a prediction confronted with a datum it was not set from: OK if GUID is consistent with the datum at 95% (|pull| < 1.96, or
               the GUID value inside the allowed region; 90% regions are labelled as such), FAIL otherwise. A FAIL stays a FAIL, also when
               general relativity, LambdaCDM or the Standard Model share it. Only these rows enter the tally.
  conditional  the same test for a prediction of a model Part I names but GUID does not derive (the Starobinsky/Higgs plateau potential);
               OK/FAIL reported and counted separately.
  consistency  the prediction or statement was set from this datum, so it cannot fail; reported as CONS, never counted as a success.
  info         superseded, derived, overlapping a scored row, or without a usable uncertainty; reported as INFO, not scored.
The last line counts the scored confrontations; the exit code is 0 only if all of them pass. Separate METHOD checks (marked [M]) test
the script's own numerics (closed forms against quadrature, ODE against analytic limits); they must all pass.

Not done here, because other workstreams of the paper do it: galaxy rotation curves (sparc_rotation.*), the accumulated remnant
(remnant_history.*), hosted quantum benchmarks, holographic codes, gravity ensembles and the BMV witness. Their result files are cited.

  D1  the information scalar (Hypothesis 4): coupling lambda = d ln alpha / d phi and the present drift of alpha; MICROSCOPE,
      Eot-Wash, optical clocks, Oklo, quasars, CMB, BBN; two cosmological models (A: Part I's action, no potential, the scalar
      driven by the electrostatic energy of baryons, BSBM-like; B: a slowly rolling, thawing scalar with the dark energy); the sign
  D2  PPN gravity: gamma, beta, Nordtvedt eta, strong-field SEP, gravitational redshift, speed of gravity, graviton mass
  D3  the balanced state: transition redshift, de Sitter rate, DESI DR2 evolving dark energy, H0, spatial flatness
  D4  inflation and the start: Starobinsky / Higgs inflation (n_s = 1 - 2/N, r = 12/N^2, N = 50..60) against Planck, ACT, BICEP/Keck;
      the ordering of the strong split and inflation (monopoles)
  D5  black holes: Soltan radiative efficiency against the Kerr ISCO curve, measured spins, the area theorem, Hawking radiation
  D6  Bridge B (Diosi-Penrose rate G M^2 / hbar R): the largest existing superpositions, the bounds on the smearing length R0,
      the Oppenheim et al. window for D2, and what experiment would first see it
  D7  contained remnants: the asteroid-mass primordial-black-hole window and its edges
  D8  the electroweak and strong splits: proton decay, monopoles, W, Z, Higgs masses and alpha(M_Z) against the tree-level relations
  D9  the rest: Bell/CHSH and Tsirelson's bound, neutrinos as the remnant, the radiated remnant, gravity weighing all energy
"""

import json
import math
import sys
from pathlib import Path

import numpy as np
from scipy import integrate, optimize, special, stats

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
FIGURES = HERE / "figures"
Z95 = stats.norm.ppf(0.975)            # 1.959964: two-sided 95%
DATE_VERIFIED = "2026-10-31"

# ---------------------------------------------------------------------------------------------------------------------------------
# Constants (SI 2019 exact values; CODATA 2018 for G, as in docs/quantum-gravity/checks.py)
h = 6.62607015e-34
hbar = h / (2 * math.pi)
c = 299792458.0
G = 6.67430e-11
kB = 1.380649e-23
eV = 1.602176634e-19
GeV = 1e9 * eV
u_kg = 1.66053906660e-27
year = 3.15576e7                       # Julian year, s
pc = 3.0856775814913673e16
Mpc = 1e6 * pc
M_sun = 1.98847e30
L_P = math.sqrt(hbar * G / c**3)
m_P = math.sqrt(hbar * c / G)

# ---------------------------------------------------------------------------------------------------------------------------------
# Sources. "read" says what was read on DATE_VERIFIED; "value" is what the source states.
CITATIONS = {
    "microscope": dict(ref="P. Touboul et al. (MICROSCOPE Collaboration), Phys. Rev. Lett. 129, 121102 (2022), arXiv:2209.15487",
                       read="arXiv abstract", value="eta(Ti,Pt) = [-1.5 +- 2.3 (stat) +- 1.5 (syst)] x 1e-15, 1 sigma in statistical errors"),
    "eotwash": dict(ref="S. Schlamminger et al., Phys. Rev. Lett. 100, 041101 (2008), arXiv:0712.0607",
                    read="arXiv abstract", value="Be-Ti: Delta a = (0.6 +- 3.1) x 1e-15 m/s^2, eta = (0.3 +- 1.8) x 1e-13"),
    "lange": dict(ref="R. Lange et al., Phys. Rev. Lett. 126, 011102 (2021), arXiv:2010.06620",
                  read="arXiv abstract", value="d ln alpha/dt = 1.0(1.1) x 1e-18 /yr"),
    "filzinger": dict(ref="M. Filzinger, S. Doerscher, R. Lange, J. Klose, M. Steinel, E. Benkler, E. Peik, C. Lisdat, N. Huntemann, "
                          "Phys. Rev. Lett. 130, 253001 (2023), arXiv:2301.03433",
                      read="arXiv full text, Supplemental Material Eq. (9) (data combined with those of Lange et al. 2021)",
                      value="(1/alpha) d alpha/dt = 1.8(2.5) x 1e-19 /yr"),
    "oklo_dh": dict(ref="E. D. Davis, L. Hamdan, Phys. Rev. C 92, 014319 (2015), arXiv:1503.06011",
                    read="arXiv abstract", value="|alpha_Oklo - alpha_now| < 1.1e-8 alpha_now (95% CL), given a weak restriction on m_q/Lambda"),
    "oklo_dd": dict(ref="T. Damour, F. Dyson, Nucl. Phys. B 480, 37 (1996), arXiv:hep-ph/9606486",
                    read="arXiv abstract", value="reactors operated about two billion years ago; -0.9e-7 < Delta alpha/alpha < 1.2e-7 and "
                                                 "-6.7e-17 < alpha-dot/alpha < 5.0e-17 /yr (95%), which implies an elapsed time of 1.8 Gyr"),
    "espresso": dict(ref="M. T. Murphy et al., Astron. Astrophys. 658, A123 (2022), arXiv:2112.05819",
                     read="arXiv abstract", value="Delta alpha/alpha = 1.3 +- 1.3 (stat) +- 0.4 (sys) ppm at z = 1.15 (HE 0515-4414)"),
    "wilczynska": dict(ref="M. R. Wilczynska et al., Science Advances (2020), arXiv:2003.07627",
                       read="arXiv abstract (journal volume not shown there)", value="Delta alpha/alpha = (-2.18 +- 7.27) x 1e-5, weighted mean over z = 5.5 to 7.1"),
    "hartchluba": dict(ref="L. Hart, J. Chluba, Mon. Not. R. Astron. Soc., doi:10.1093/mnras/stx2783 (2018), arXiv:1705.03925",
                       read="arXiv abstract", value="alpha_EM/alpha_EM,0 = 0.9993 +- 0.0025 (Planck 2015, CMB only)"),
    "planck_xxiv": dict(ref="Planck Collaboration, Astron. Astrophys. 580, A22 (2015), arXiv:1406.7482",
                        read="arXiv abstract", value="Delta alpha/alpha = (3.6 +- 3.7) x 1e-3 (68% CL) at z ~ 1e3"),
    "avelino": dict(ref="P. P. Avelino et al., Phys. Rev. D 64, 103505 (2001), arXiv:astro-ph/0102144",
                    read="arXiv full text", value="BBN, alpha alone varying, Omega_b h^2 free: Delta alpha/alpha = (-7 +- 5) x 1e-3 (68% CL), (-7 +- 9) x 1e-3 (95%)"),
    "martins21": dict(ref="C. J. A. P. Martins, Astron. Astrophys. 646, A47 (2021), arXiv:2012.10505",
                      read="arXiv abstract and conclusions", value="|Delta alpha/alpha| < 50 ppm (2 sigma, no priors) or < 5 ppm (with priors), lithium "
                                                                  "excluded, in GUT-type models where all couplings vary with alpha (not an alpha-only scalar)"),
    "cassini": dict(ref="B. Bertotti, L. Iess, P. Tortora, Nature 425, 374 (2003)",
                    read="ADS abstract through a web search", value="gamma = 1 + (2.1 +- 2.3) x 1e-5"),
    "fienga": dict(ref="A. Fienga, O. Minazzoli, Living Rev. Relativ. 27, 1 (2024), arXiv:2303.01821",
                   read="arXiv full text, Eq. (102) and Table 5", value="(beta - 1) = (-0.45 +- 1.75) x 1e-5, (gamma - 1) = (0.55 +- 1.35) x 1e-5 "
                                                                       "(common overlap of the recent planetary-ephemeris intervals)"),
    "genova": dict(ref="A. Genova et al., Nat. Commun. 9, 289 (2018)",
                   read="publication text through a web search; beta also in Fienga & Minazzoli Table 5 and Biskupek et al. 2021",
                   value="beta = 1 + (-1.6 +- 1.8) x 1e-5; Nordtvedt eta = (-6.6 +- 7.2) x 1e-5"),
    "biskupek": dict(ref="L. Biskupek, J. Mueller, J.-M. Torre, Universe 7, 34 (2021), arXiv:2012.12032",
                     read="arXiv full text, Table 1 (the sigma level of the errors is not stated; read here as 1 sigma, the stricter reading)",
                     value="Delta(m_g/m_i)_EM = (-2.1 +- 2.4) x 1e-14; gamma - 1 = (1.7 +- 1.6) x 1e-4; beta - 1 = (6.2 +- 7.2) x 1e-5"),
    "voisin": dict(ref="G. Voisin et al., Astron. Astrophys. 638, A24 (2020), arXiv:2005.01388",
                   read="arXiv abstract", value="strong-equivalence-principle violation Delta = (+0.5 +- 1.8) x 1e-6 at 95% CL (PSR J0337+1715)"),
    "gw170817": dict(ref="B. P. Abbott et al. (LIGO, Virgo, Fermi GBM, INTEGRAL), Astrophys. J. Lett. 848, L13 (2017), arXiv:1710.05834",
                     read="arXiv abstract", value="speed of gravity minus speed of light between -3e-15 and +7e-16 of c"),
    "gwtc3tgr": dict(ref="LIGO, Virgo and KAGRA Collaborations, 'Tests of General Relativity with GWTC-3', Phys. Rev. D 112, 084080 (2025), "
                         "arXiv:2112.06861v3", read="arXiv abstract v3 (comment: 'v3: fixed graviton mass bound in abstract'; v1 had 1.27e-23)",
                     value="m_g <= 2.42e-23 eV/c^2 (90% credibility); no evidence of non-GR polarization modes"),
    "delva": dict(ref="P. Delva et al., Phys. Rev. Lett. 121, 231101 (2018), arXiv:1812.03711",
                  read="arXiv abstract", value="gravitational-redshift deviation (+0.19 +- 2.48) x 1e-5 at 1 sigma (Galileo satellites)"),
    "planck18": dict(ref="Planck Collaboration, Planck 2018 results VI, Astron. Astrophys. 641, A6 (2020), arXiv:1807.06209",
                     read="arXiv abstract", value="H0 = 67.4 +- 0.5 km/s/Mpc, Omega_m = 0.315 +- 0.007, Omega_c h^2 = 0.120 +- 0.001, "
                                                  "Omega_b h^2 = 0.0224 +- 0.0001, n_s = 0.965 +- 0.004 (68%)"),
    "planck18x": dict(ref="Planck Collaboration, Planck 2018 results X, Astron. Astrophys. 641, A10 (2020), arXiv:1807.06211",
                      read="arXiv abstract", value="n_s = 0.9649 +- 0.0042 (68% CL); spatial flatness confirmed at 0.4% (95% CL) with BAO"),
    "desi2": dict(ref="DESI Collaboration, 'DESI DR2 results II', Phys. Rev. D 112, 083515 (2025), arXiv:2503.14738",
                  read="arXiv abstract and HTML full text (Eqs. 21, 25-28; Tables 5, 6)",
                  value="LCDM DESI+CMB: Omega_m = 0.3027 +- 0.0036, H0 = 68.17 +- 0.28; 1e3 Omega_K = 2.3 +- 1.1 (DESI+CMB); w0waCDM: DESI+CMB "
                        "w0 = -0.42 +- 0.21, wa = -1.75 +- 0.58 (3.1 sigma); +Pantheon+ -0.838 +- 0.055, -0.62 +0.22-0.19 (2.8 sigma); +Union3 "
                        "-0.667 +- 0.088, -1.09 +0.31-0.27 (3.8 sigma); +DESY5 -0.752 +- 0.057, -0.86 +0.23-0.20 (4.2 sigma); sum m_nu < 0.064 eV (95%)"),
    "dovekie": dict(ref="B. Popovic et al. (DES Collaboration), Mon. Not. R. Astron. Soc. (2026), doi:10.1093/mnras/stag632, arXiv:2511.07517",
                    read="arXiv abstract", value="recalibrated DES supernovae: preference for evolving dark energy 4.2 sigma -> 3.2 sigma; with CMB and "
                                                 "DESI DR2 w0 = -0.803 +- 0.054, wa = -0.72 +- 0.21; Bayesian odds about 5:1"),
    "sh0es": dict(ref="A. G. Riess et al., Astrophys. J. Lett., doi:10.3847/2041-8213/ac5c5b (2022), arXiv:2112.04510",
                  read="arXiv abstract", value="H0 = 73.04 +- 1.04 km/s/Mpc; 5 sigma from Planck + LCDM"),
    "cchp": dict(ref="W. L. Freedman et al., Astrophys. J. 985, 203 (2025), arXiv:2408.06153",
                 read="arXiv abstract (journal reference through a web search)", value="H0 = 70.39 +- 1.22 (stat) +- 1.33 (sys) +- 0.70 (sigma_SN), TRGB"),
    "moresco": dict(ref="M. Moresco et al., JCAP 05 (2016) 014, arXiv:1601.01701",
                    read="arXiv abstract", value="z_t = 0.4 +- 0.1 (cosmic chronometers, cosmology-independent)"),
    "jesus": dict(ref="J. F. Jesus, R. F. L. Holanda, S. H. Pereira, JCAP 05 (2018) 073, arXiv:1712.01075",
                  read="arXiv abstract", value="z_t = 0.806 +- 0.094, 0.870 +- 0.063, 0.973 +- 0.058 (three parametrizations; SNe Ia + H(z); 1 sigma)"),
    "farooq": dict(ref="O. Farooq, F. Madiyar, S. Crandall, B. Ratra, Astrophys. J. 835, 26 (2017), arXiv:1607.03537",
                   read="arXiv abstract", value="weighted-mean deceleration-acceleration redshift z_da = 0.72 +- 0.05 (0.84 +- 0.03) for "
                                                "H0 = 68 +- 2.8 (73.24 +- 1.74) km/s/Mpc; z_da depends mainly on the H0 prior"),
    "dahiya": dict(ref="D. Dahiya, D. Jain, Res. Astron. Astrophys. (2023), arXiv:2212.04751",
                   read="arXiv abstract", value="best-fit z_t between 0.61 and 0.82 for four dark-energy models (Pantheon+ and H(z); no uncertainty given)"),
    "bk18": dict(ref="P. A. R. Ade et al. (BICEP/Keck), Phys. Rev. Lett. 127, 151301 (2021), arXiv:2110.00483",
                 read="arXiv abstract", value="r_0.05 < 0.036 (95%), sigma(r) = 0.009"),
    "act_dr6": dict(ref="T. Louis et al. (ACT), 'DR6 Power Spectra, Likelihoods and LambdaCDM Parameters', JCAP (accepted), arXiv:2503.14452",
                    read="arXiv abstract and HTML full text (Sect. VIII)",
                    value="P-ACT-LB (ACT+Planck, CMB lensing, DESI DR1 BAO): n_s = 0.974 +- 0.003; P-ACT: n_s = 0.9709 +- 0.0038; W-ACT 0.9660 +- 0.0046"),
    "macro": dict(ref="M. Ambrosio et al. (MACRO Collaboration), Eur. Phys. J. C 25, 511 (2002), arXiv:hep-ex/0207020",
                  read="arXiv abstract", value="monopole flux < 1.4e-16 cm^-2 s^-1 sr^-1 (90% CL) for 4e-5 < beta < 1"),
    "superk": dict(ref="A. Takenaka et al. (Super-Kamiokande Collaboration), Phys. Rev. D 102, 112011 (2020), arXiv:2010.16098",
                   read="arXiv abstract", value="tau/B(p -> e+ pi0) > 2.4e34 yr, tau/B(p -> mu+ pi0) > 1.6e34 yr (90% CL)"),
    "mw_comb": dict(ref="LHC-TeV MW Working Group, Eur. Phys. J. C 84, 451 (2024), arXiv:2308.09417",
                    read="arXiv abstract; the PDG 2025 average 80.3692 +- 0.0133 GeV (through a web search) is the same number",
                    value="m_W = 80369.2 +- 13.3 MeV without CDF (compatibility 91%); 80394.6 +- 11.5 MeV with CDF (compatibility 0.5%)"),
    "mz_pdg": dict(ref="Particle Data Group, Z boson mass (pdgLive)", read="through a web search (the PDG pages were not reachable directly)",
                   value="m_Z = 91.1880 +- 0.0020 GeV (LEP-SLC 91.1876 +- 0.0021 combined with CDF 2022)"),
    "atlas_mh": dict(ref="ATLAS Collaboration, Phys. Rev. Lett. 131, 251802 (2023), arXiv:2308.04775",
                     read="arXiv abstract", value="m_H = 125.11 +- 0.11 GeV"),
    "alpha_mz": dict(ref="J. Erler, A. Freitas, 'Electroweak model and constraints on new physics', Review of Particle Physics (PDG 2017 edition)",
                     read="through a web search of the PDG review text", value="alpha-hat(M_Z)^-1 = 127.950 +- 0.017 (MS-bar)"),
    "s2w": dict(ref="Particle Data Group, S. Navas et al., Phys. Rev. D 110, 030001 (2024), world average as quoted in arXiv:2509.18251",
                read="arXiv:2509.18251 HTML", value="sin^2 theta_W-hat (M_Z) = 0.23129 +- 0.00004 (MS-bar)"),
    "gf_mulan": dict(ref="MuLan Collaboration, Phys. Rev. D 87, 052003 (2013), arXiv:1211.0960",
                     read="arXiv abstract", value="G_F = 1.1663787(6) x 1e-5 GeV^-2"),
    "codata22": dict(ref="CODATA 2022 recommended values (P. J. Mohr et al.)", read="NIST tables through a web search",
                     value="alpha^-1 = 137.035999177(21)"),
    "donofrio": dict(ref="M. D'Onofrio, K. Rummukainen, Phys. Rev. D 93, 025003 (2016), arXiv:1508.07161",
                     read="arXiv abstract", value="smooth cross-over at T_c = 159.5 +- 1.5 GeV for the physical Higgs mass"),
    "kajantie": dict(ref="K. Kajantie, M. Laine, K. Rummukainen, M. Shaposhnikov, Phys. Rev. Lett. 77, 2887 (1996), arXiv:hep-ph/9605288",
                     read="arXiv abstract", value="first-order line ends at m_H,c with 70 GeV < m_H,c < 95 GeV (about 80 GeV)"),
    "yu_tremaine": dict(ref="Q. Yu, S. Tremaine, Mon. Not. R. Astron. Soc. 335, 965 (2002), arXiv:astro-ph/0203082",
                        read="arXiv abstract", value="luminous QSOs are Kerr black holes accreting with efficiency > 0.1"),
    "marconi": dict(ref="A. Marconi et al., Mon. Not. R. Astron. Soc. 351, 169 (2004), arXiv:astro-ph/0311619",
                    read="arXiv abstract", value="epsilon = 0.04 to 0.16, Eddington ratio 0.1 to 1.7"),
    "shankar": dict(ref="F. Shankar, D. H. Weinberg, J. Miralda-Escude, Astrophys. J. 690, 20 (2009), arXiv:0710.4488",
                    read="arXiv abstract", value="epsilon = 0.075 from matching the AGN emissivity to the local BH mass density (about 25% higher "
                                                 "for an alternative luminosity function)"),
    "davis_laor": dict(ref="S. W. Davis, A. Laor, Astrophys. J. 728, 98 (2011), arXiv:1012.3213",
                       read="arXiv abstract", value="eta from about 0.03 to about 0.4, rising with mass; mean log eta = -1.05 +- 0.52"),
    "reynolds": dict(ref="C. S. Reynolds, Annu. Rev. Astron. Astrophys. (2021), doi:10.1146/annurev-astro-112420-035022, arXiv:2011.08948",
                     read="arXiv full text, Tables 1 and 2", value="36 SMBH spins (X-ray reflection) and 25 X-ray-binary spins, 90% ranges"),
    "isi": dict(ref="M. Isi, W. M. Farr, M. Giesler, M. A. Scheel, S. A. Teukolsky, Phys. Rev. Lett. 127, 011103 (2021), arXiv:2012.04486",
                read="arXiv abstract", value="GW150914: area increase with 97% (95% without overtones) probability"),
    "gw250114": dict(ref="LIGO, Virgo and KAGRA Collaborations, 'GW250114: testing Hawking's area law and the Kerr nature of black holes', "
                         "doi:10.1103/kw5g-d732 (2025), arXiv:2509.08054", read="arXiv abstract",
                     value="remnant area larger than the sum of the initial areas to high credibility; ringdown modes within +-30% of Kerr"),
    "fein": dict(ref="Y. Y. Fein et al., Nat. Phys. 15, 1242 (2019), doi:10.1038/s41567-019-0663-9",
                 read="through web searches: the journal abstract (beyond 25 kDa, up to 2000 atoms, > 90% of the expected visibility); the "
                      "interferometer (three gratings, period 266 nm, spacing 0.98 m) from arXiv:2203.11866; masses up to 28,000 u from "
                      "arXiv:2301.11095; 'more than 7 ms' from the University of Vienna release; 'delocalized over hundreds of nm' from Donadi et al. 2021",
                 value="M up to 28,000 u, delocalization ~266 nm, about 7 ms"),
    "pedalino": dict(ref="S. Pedalino et al., 'Probing quantum mechanics using nanoparticle Schroedinger cats', arXiv:2507.21211 (2025)",
                     read="arXiv abstract and HTML full text", value="Na clusters of > 7000 atoms, 143 to 197 kDa, cluster diameter ~8 nm (Methods), "
                                                                     "grating period 133 nm, L = 0.983 m, v ~ 160 m/s, delocalization > 10 diameters, mu = 15.5"),
    "kovachy": dict(ref="T. Kovachy et al., Nature 528, 530 (2015), doi:10.1038/nature16155",
                    read="journal abstract through a web search; rubidium from the review arXiv:1706.06173", value="wave packets separated by up to 54 cm "
                                                                                                                 "on a timescale of 1 s"),
    "xu": dict(ref="V. Xu et al., Science 366, 745 (2019), arXiv:1907.03054",
               read="arXiv abstract; Cs and Delta z = 3.9 um through a web search (preprint figure, Physics Today)",
               value="20 s interrogation, microns of vertical separation"),
    "donadi": dict(ref="S. Donadi et al., Nat. Phys. 17, 74 (2021), arXiv:2111.13490",
                   read="arXiv full text, Eq. (6) and Fig. 5", value="R0 > 0.54e-10 m with probability 0.95; earlier bounds R0 >= (40.1 +- 0.5)e-15 m "
                                                                     "(gravitational-wave detectors) and R0 >~ 1e-13 m (neutron stars)"),
    "figurato": dict(ref="L. Figurato et al., New J. Phys. 26, 113004 (2024), arXiv:2406.18494",
                     read="arXiv abstract", value="current experiments set a lower bound R0 >~ 4e-10 m"),
    "osswd": dict(ref="J. Oppenheim, C. Sparaciari, B. Soda, Z. Weller-Davies, Nat. Commun. 14, 7910 (2023), arXiv:2203.01982",
                  read="arXiv full text, Eqs. (46) and (47)", value="1e-1 kg s >= (l_P^3/m_P) D2 >= 1e-25 kg s; 1e-9 kg^2 s/m >= l_P^2 D2 >= 1e-40 kg^2 s/m"),
    "gorton_green": dict(ref="M. Gorton, A. M. Green, SciPost Phys. 17, 032 (2024), arXiv:2403.03839",
                         read="arXiv abstract and HTML full text", value="window ~1e17 to 1e22 g, open for current constraints; f_PBH = 1 excluded for "
                                                                         "m <~ 1e17 g (INTEGRAL/SPI, Voyager 1); Subaru-HSC M31 microlensing above ~1e22 g"),
    "carr21": dict(ref="B. Carr, K. Kohri, Y. Sendouda, J. Yokoyama, Rep. Prog. Phys., doi:10.1088/1361-6633/ac1e31 (2021), arXiv:2002.12778",
                   read="arXiv abstract", value="PBHs smaller than about 1e15 g have evaporated"),
    "poh": dict(ref="H. S. Poh et al., Phys. Rev. Lett. 115, 180408 (2015), arXiv:1506.01865",
                read="arXiv abstract", value="CHSH S = 2.82759 +- 0.00051; distance to Tsirelson's bound 0.00084 +- 0.00051"),
    "hensen": dict(ref="B. Hensen et al., Nature 526, 682 (2015), arXiv:1508.05949",
                   read="arXiv abstract", value="loophole-free S = 2.42 +- 0.20, 245 trials, p = 0.039"),
    "katrin": dict(ref="KATRIN Collaboration, Science 388, 180 (2025), arXiv:2406.13516",
                   read="arXiv abstract", value="m_nu < 0.45 eV (90% CL)"),
    "nanograv": dict(ref="G. Agazie et al. (NANOGrav), Astrophys. J. Lett. 951, L8 (2023), arXiv:2306.16213",
                     read="arXiv abstract", value="characteristic strain 2.4 (+0.7 -0.6) x 1e-15 at f = 1/yr (median, 90% credible)"),
}

# ---------------------------------------------------------------------------------------------------------------------------------
ROWS = []          # every confrontation
METHOD = []        # method checks
COND = "conditional on the Starobinsky/Higgs plateau potential, which Part I names but GUID does not derive"
R0SET = "Bridge B's smearing length R0 >= 4e-10 m was adopted from these bounds"
NUEMP = "that the known neutrinos are not the remnant is an empirical statement set from neutrino-mass bounds, not a prediction"
KIND = {  # rows whose kind is not 'scored' (or 'info' for rows passed with scored=False); reason in the second field
    "D1.12": ("info", "derived from D1.3 and the cosmological alpha data and dominated by D1.3 (both +0.72 sigma)"),
    "D2.2": ("info", "overlaps D2.1: Cassini tracking data enter the planetary ephemerides"),
    "D2.4": ("info", "included in the ephemeris combination D2.3 (Fienga and Minazzoli, Table 5)"),
    "D3.1": ("info", "inconclusive: the published determinations disagree with each other and depend on the H0 prior and the "
                     "parametrisation"),
    "D3.6": ("info", "overlaps D3.7 (both rest on the CMB) and uses older BAO"),
    "D4.1": ("info", "superseded by D4.3, which includes the Planck data"),
    "D4.3": ("conditional", COND),
    "D4.4": ("conditional", COND),
    "D5.1": ("info", "overlaps D5.2: same kind of Soltan inputs (AGN luminosity function, local black-hole mass density), older"),
    "D5.3": ("info", "overlaps D5.2: same kind of Soltan inputs, older"),
    "D5.5": ("consistency", "the spins are measured with Kerr models capped at a = 0.998, so this test cannot fail"),
    "D6.5": ("consistency", R0SET),
    "D6.6": ("consistency", R0SET + "; overlaps D6.5"),
    "D6.7": ("consistency", R0SET),
    "D7.1": ("consistency", "the contained remnant's window 1e14 to 1e19 kg was adopted from the open window"),
    "D7.2": ("info", "the datum ('about 1e15 g') has no stated uncertainty; it passes only through the chosen tolerance of ten"),
    "D8.1": ("consistency", "GUID allows a unification at any M_X; the example M_X = 1e16 GeV was chosen above this bound"),
    "D8.2": ("consistency", "Part I's ordering of the strong split is required by the absence of monopoles"),
    "D8.3": ("info", "tree-level Standard Model value; scheme dependent, it meets 0.5% only in the MS-bar route"),
    "D8.4": ("info", "tree-level Standard Model value; scheme dependent"),
    "D8.5": ("consistency", "Part I's 1/128 is read from the measured alpha(M_Z)"),
    "D8.6": ("consistency", "Part I's crossover statement is read from the measured Higgs mass and the lattice"),
    "D9.3": ("consistency", NUEMP),
    "D9.4": ("consistency", NUEMP),
    "D9.5": ("consistency", "the radiated remnant was refuted from the NANOGrav amplitude itself"),
}
VERDICT_TEXT = {"OK": "GUID consistent with this datum at 95%", "FAIL": "GUID NOT consistent with this datum at 95%",
                "CONS": "consistent by construction (prediction set from this datum): not counted", "INFO": "reported, not scored"}


def fmt(x, digits=3):
    if x == 0:
        return "0"
    if 1e-3 <= abs(x) < 1e4:
        return f"{x:.{digits}g}"
    return f"{x:.{digits - 1}e}"


def method(label, ok):
    print(f"[M] {'OK  ' if ok else 'FAIL'} {label}")
    METHOD.append({"label": label, "ok": bool(ok)})


def record(rid, observable, guid, data, refs, measure, ok, cls, note="", scored=True, pull=None):
    kind, reason = KIND.get(rid, ("scored" if scored else "info", ""))
    if kind in ("scored", "conditional"):
        verdict = "OK" if ok else "FAIL"
    elif kind == "consistency":
        verdict = "CONS" if ok else "FAIL"
    else:
        verdict = "INFO"
    row = dict(id=rid, section=rid.split(".")[0], observable=observable, guid=guid, data=data, refs=refs, measure=measure,
               pull=None if pull is None else float(pull), verdict=verdict, kind=kind, kind_reason=reason, scored=(kind == "scored"),
               cls=cls, note=note)
    ROWS.append(row)
    print(f"\n[{rid}] {observable}")
    print(f"     GUID : {guid}")
    print(f"     data : {data}   [{', '.join(refs)}]")
    print(f"     test : {measure}")
    if note:
        print(f"     note : {note}")
    if reason:
        print(f"     kind : {kind} ({reason})")
    tag = " [conditional: not counted for GUID]" if kind == "conditional" else ""
    print(f"{verdict:<4} {VERDICT_TEXT[verdict]}{tag}")
    return row


def gauss(rid, observable, guid_val, obs, sig, refs, cls, guid_sig=0.0, unit="", note="", scored=True, guid_text=None, data_text=None):
    """Two-sided Gaussian confrontation; the pull is (datum - GUID) / sqrt(sigma_data^2 + sigma_GUID^2)."""
    s = math.hypot(sig, guid_sig)
    pull = (obs - guid_val) / s
    gtxt = guid_text or (f"{fmt(guid_val)}{' +- ' + fmt(guid_sig) if guid_sig else ''} {unit}".strip())
    dtxt = data_text or f"{fmt(obs)} +- {fmt(sig)} {unit} (1 sigma)".strip()
    return record(rid, observable, gtxt, dtxt, refs, f"pull = {pull:+.2f} sigma", abs(pull) < Z95, cls, note, scored, pull)


def inside(rid, observable, guid_val, lo, hi, cl, refs, cls, unit="", note="", scored=True, guid_text=None, data_text=None):
    ok = lo <= guid_val <= hi
    lo_t = "-inf" if lo == -math.inf else fmt(lo)
    hi_t = "+inf" if hi == math.inf else fmt(hi)
    gtxt = guid_text or f"{fmt(guid_val)} {unit}".strip()
    dtxt = data_text or (f"allowed [{lo_t}, {hi_t}]" + (f" {unit}" if unit else "") + f" ({cl})")
    return record(rid, observable, gtxt, dtxt, refs, f"GUID value {'inside' if ok else 'outside'} the allowed region ({cl})", ok, cls, note,
                  scored)


# =================================================================================================================================
print("GUID v6: predictions against existing data. Every datum verified on", DATE_VERIFIED, "(see CITATIONS).")

# Background cosmology used where a model needs one (Planck 2018, abstract values)
H0_kms, H0_err = 67.4, 0.5
Om_P, Om_P_err = 0.315, 0.007
OL_P = 1 - Om_P
H0_si = H0_kms * 1e3 / Mpc
H0_yr = H0_si * year                        # 1/yr
ombh2, omch2 = 0.0224, 0.120
h_little = H0_kms / 100
Ob_P = ombh2 / h_little**2

# =================================================================================================================================
print("\n" + "=" * 100 + "\nD1  The information scalar: coupling lambda = d ln alpha / d phi and the present drift of alpha\n" + "=" * 100)


def f_coulomb(Z, A):
    """Electrostatic share of a nucleus' mass: Bethe-Weizsaecker Coulomb term a_C Z(Z-1)/A^(1/3), a_C = 0.711 MeV (as checks.py [Q6])."""
    return 0.711 * Z * (Z - 1) / A ** (1 / 3) / (A * 931.494)


f_Ti, f_Pt, f_Be = f_coulomb(22, 48), f_coulomb(78, 195), f_coulomb(4, 9)
earth = {(26, 56): 0.32, (8, 16): 0.30, (14, 28): 0.15, (12, 24): 0.14, (20, 40): 0.02, (13, 27): 0.02, (28, 58): 0.05}
f_E = sum(w * f_coulomb(Z, A) for (Z, A), w in earth.items()) / sum(earth.values())
# eta(A,B) = 2 (a_A - a_B)/(a_A + a_B) = 2 lambda^2 f_E (f_A - f_B): the scalar adds 2 Q_E Q_A to each body's fall, Q = lambda f (Eq. fifth)
k_mic = 2 * f_E * (f_Ti - f_Pt)
k_ew = 2 * f_E * (f_Be - f_Ti)
eta_mic, sig_mic = -1.5e-15, math.hypot(2.3e-15, 1.5e-15)
eta_ew, sig_ew = 0.3e-13, 1.8e-13
EP = [(k_mic, eta_mic, sig_mic), (k_ew, eta_ew, sig_ew)]


def chi2_ep(lam, which=None):
    terms = EP if which is None else [EP[which]]
    return sum(((k * lam**2 - e) / s) ** 2 for k, e, s in terms)


def lam_bound(which=None, dchi2=stats.chi2.ppf(0.95, 1)):
    num = sum(k * e / s**2 for k, e, s in (EP if which is None else [EP[which]]))
    den = sum(k * k / s**2 for k, e, s in (EP if which is None else [EP[which]]))
    l2_best = max(0.0, num / den)
    c_min = chi2_ep(math.sqrt(l2_best), which)
    lam_best = math.sqrt(l2_best)
    return lam_best, optimize.brentq(lambda l: chi2_ep(l, which) - c_min - dchi2, lam_best + 1e-12, 1.0)


lam_best, lam95 = lam_bound()
lam_best_mic, lam95_mic = lam_bound(0)
lam_paper = math.sqrt(2.7e-15 / abs(k_mic))      # checks.py [Q6]: |eta| < 2.7e-15
print(f"electrostatic shares: Ti {f_Ti:.3e}, Pt {f_Pt:.3e}, Be {f_Be:.3e}, Earth {f_E:.3e}")
print(f"profile likelihood (MICROSCOPE + Eot-Wash): best |lambda| = {lam_best:.2e}, 95% CL upper limit |lambda| < {lam95:.2e} "
      f"(MICROSCOPE alone {lam95_mic:.2e}); version 5.1's |lambda| < 2e-5 is |eta| < 2.7e-15 -> {lam_paper:.2e}")

gauss("D1.1", "Universality of free fall, Ti/Pt (MICROSCOPE): eta = 2 lambda^2 f_E (f_Ti - f_Pt)", 0.0, eta_mic, sig_mic, ["microscope"],
      "GUID-specific parameter (lambda); WEP shared with GR", guid_text=f"0 for the frame; scalar term {k_mic:.2e} lambda^2 (<= 0)",
      data_text="(-1.5 +- 2.3 stat +- 1.5 syst) e-15, combined 2.75e-15",
      note=f"95% CL profile-likelihood bound |lambda| < {lam95:.1e} (version 5.1 quoted 2e-5, the 1-sigma-level |eta| < 2.7e-15); GUID fixes "
           f"the sign, eta <= 0, so the test can fail")
gauss("D1.2", "Universality of free fall, Be/Ti torsion balance (Eot-Wash 2008)", 0.0, eta_ew, sig_ew, ["eotwash"],
      "GUID-specific parameter (lambda); WEP shared with GR", guid_text=f"0 for the frame; scalar term {k_ew:.2e} lambda^2",
      data_text="(0.3 +- 1.8) e-13")

# ---- cosmological evolution of the scalar ---------------------------------------------------------------------------------------
# Units: H0 = 1, 8 pi G = 1 (reduced Planck mass 1), N = ln a. phi is the paper's dimensionless scalar (kinetic term (M_pl^2/2)(d phi)^2).
N0 = math.log(1e-5)


def solve_model_A(Om=Om_P, Ob=Ob_P):
    """The paper's action: no potential; the scalar is driven by the electrostatic energy of baryons, rho_em = f_b rho_b, with
    d rho_b / d phi = lambda f_b rho_b. Field equation: phi'' + 3 H phi' = -lambda f_b rho_b. Solution per unit (lambda f_b)."""
    def rhs(N, y):
        phi, u = y
        E2 = Om * math.exp(-3 * N) + (1 - Om)
        dlnH = -1.5 * Om * math.exp(-3 * N) / E2
        return [u, -(3 + dlnH) * u - 3 * Ob * math.exp(-3 * N) / E2]
    return integrate.solve_ivp(rhs, (N0, 0.0), [0.0, 0.0], method="DOP853", rtol=1e-10, atol=1e-14, dense_output=True)


def solve_thawing(s, Om=Om_P):
    """Model B: a canonical scalar with a linear potential V = V0 - s phi that is also the dark energy; starts frozen (Hubble friction).
    V0 is fixed so that H(today) = H0 with Omega_m(today) = Om. Returns (solution, V0)."""
    def rhs(N, y, V0):
        phi, u = y
        rho_m = 3 * Om * math.exp(-3 * N)
        H2 = (rho_m + V0 - s * phi) / (3 - 0.5 * u * u)
        dlnH = -0.5 * (rho_m / H2 + u * u)
        return [u, -(3 + dlnH) * u + s / H2]

    def miss(V0):
        sol = integrate.solve_ivp(rhs, (N0, 0.0), [0.0, 0.0], args=(V0,), method="DOP853", rtol=1e-10, atol=1e-14)
        phi, u = sol.y[:, -1]
        return (3 * Om + V0 - s * phi) / (3 - 0.5 * u * u) - 1.0
    V0 = optimize.brentq(miss, 0.5, 6.0, xtol=1e-13)
    sol = integrate.solve_ivp(rhs, (N0, 0.0), [0.0, 0.0], args=(V0,), method="DOP853", rtol=1e-10, atol=1e-14, dense_output=True)
    return sol, V0


def thawing_today(s, Om=Om_P):
    sol, V0 = solve_thawing(s, Om)
    phi, u = sol.y[:, -1]
    ke, V = 0.5 * u * u, V0 - s * phi              # H = 1 today
    return sol, (ke - V) / (ke + V), u, (ke + V) / 3


def s_for(onepw, Om=Om_P):
    return optimize.brentq(lambda s: thawing_today(s, Om)[1] + 1 - onepw, 1e-4, 5.0, xtol=1e-12)


solA = solve_model_A()
U0 = solA.y[1, -1]                       # phi' today per unit lambda f_b
s_shape = s_for(1e-3)
sol_th, w0_th, u0_th, OmDE_th = thawing_today(s_shape)
s_desi = s_for(1 - 0.838)               # 1 + w0 of DESI DR2 + CMB + Pantheon+ (CPL w0; at z = 0 a canonical scalar has phi'^2 = 3 Omega (1 + w0))
sol_desi, w0_desi, u0_desi, OmDE_desi = thawing_today(s_desi)
method(f"thawing solution obeys phi'^2 = 3 Omega_phi (1 + w0) today ({u0_th**2:.4e} vs {3 * OmDE_th * (1 + w0_th):.4e})",
       abs(u0_th**2 / (3 * OmDE_th * (1 + w0_th)) - 1) < 1e-6)
method(f"Model A: matter-era attractor phi' = -2 Omega_b/Omega_m per unit lambda f_b (at z = 50: {solA.sol(-math.log(51))[1]:.4f} vs "
       f"{-2 * Ob_P / Om_P:.4f})", abs(solA.sol(-math.log(51))[1] / (-2 * Ob_P / Om_P) - 1) < 0.02)


def G_shape(z, sol=sol_th, u0=None):
    """G(z) = [phi(0) - phi(z)] / phi'(0): Delta alpha/alpha(z) = -(alpha-dot/alpha today / H0) G(z) in the thawing model."""
    u0 = sol.y[1, -1] if u0 is None else u0
    Nz = max(-math.log1p(z), N0)
    return (sol.y[0, -1] - sol.sol(Nz)[0]) / u0


# Oklo: 1.8 Gyr ago (Damour and Dyson's rates and bounds imply 1.8 Gyr)
def lookback_gyr(z):
    f = lambda zz: 1 / ((1 + zz) * math.sqrt(Om_P * (1 + zz) ** 3 + OL_P))
    return integrate.quad(f, 0, z)[0] / H0_si / year / 1e9


z_oklo = optimize.brentq(lambda z: lookback_gyr(z) - 1.8, 0.01, 1.0)
alpha_data = [  # (label, ref, z, value, sigma(1 sigma)); sigma for a 95% bound is bound / 1.96
    ("Oklo", "oklo_dh", z_oklo, 0.0, 1.1e-8 / Z95),
    ("ESPRESSO", "espresso", 1.15, 1.3e-6, math.hypot(1.3e-6, 0.4e-6)),
    ("quasars z~6", "wilczynska", 6.3, -2.18e-5, 7.27e-5),
    ("CMB", "hartchluba", 1100.0, -0.7e-3, 2.5e-3),
    ("BBN", "avelino", 1e9, -7e-3, 5e-3),
]
d_clock, s_clock = 1.8e-19, 2.5e-19            # Filzinger 2023 (includes Lange 2021's Yb+ E3/E2 data)
implied = [("clocks", "filzinger", 0.0, d_clock, s_clock)]
for lab, ref, z, v, s in alpha_data:
    Gz = G_shape(z)
    implied.append((lab, ref, z, -v * H0_yr / Gz, s * H0_yr / Gz))
w = np.array([1 / s**2 for *_, s in implied])
d_vals = np.array([d for *_, d, s in implied])
d_hat = float(np.sum(w * d_vals) / np.sum(w))
d_sig = float(1 / math.sqrt(np.sum(w)))
chi2_alpha = float(np.sum(w * (d_vals - d_hat) ** 2))
P_neg = stats.norm.cdf(-d_hat / d_sig)
d95 = (d_hat - Z95 * d_sig, d_hat + Z95 * d_sig)
print("\nModel B (thawing scalar = dark energy, linear potential, small-slope shape): G(z) = [phi(0) - phi(z)]/phi'(0)")
for lab, ref, z, d, s in implied:
    print(f"   {lab:<12} z = {z:<9.3g} G = {G_shape(z) if z > 0 else 0:.4f}   implied present drift {d:+.2e} +- {s:.1e} /yr")
print(f"   joint: alpha-dot/alpha = ({d_hat:.2e} +- {d_sig:.2e}) /yr, chi2 = {chi2_alpha:.2f} for {len(implied) - 1} dof; "
      f"P(drift < 0) = {P_neg:.3f}")
G_inf_small, G_inf_desi = G_shape(1e9), G_shape(1e9, sol_desi)
print(f"   shape dependence: G(z=1.15) = {G_shape(1.15):.4f} (1+w0 = 1e-3) vs {G_shape(1.15, sol_desi):.4f} (1+w0 = 0.162); "
      f"G(inf) = {G_inf_small:.4f} vs {G_inf_desi:.4f}")

# Model A numbers: alpha-dot/alpha = lambda * H0 * phi'(0) = lambda^2 f_b H0 U0 (U0 < 0). f_b = electrostatic share of cosmic baryons:
# He-4 Coulomb share times a helium mass fraction ~0.25 is 6e-5; the electromagnetic self-energy of a nucleon is below 1 MeV, i.e.
# below ~1e-3 of its mass. f_b = 1e-3 is used as a generous upper value; dark matter (a remnant, Section 11.6) carries no charge.
f_b_hi, f_b_lo = 1e-3, 0.25 * f_coulomb(2, 4)
dA_max = lam95**2 * f_b_hi * H0_yr * U0
PhiA_cmb = (solA.sol(max(-math.log(1101), N0))[0] - solA.y[0, -1])     # per unit lambda f_b; Delta alpha/alpha = lambda^2 f_b * this
dalpha_A_cmb = lam95**2 * f_b_hi * PhiA_cmb
print(f"\nModel A (Part I's action, no potential): phi'(today) = {U0:.4f} lambda f_b; alpha-dot/alpha = {U0 * H0_yr:.3e} lambda^2 f_b /yr "
      f"<= 0 for f_b > 0. At |lambda| = {lam95:.1e} and f_b = {f_b_hi:.0e}: alpha-dot/alpha = {dA_max:.1e} /yr; Delta alpha/alpha(z=1100) = "
      f"{dalpha_A_cmb:.1e}")

gauss("D1.3", "Present drift of alpha, optical clocks (Yb+ E3/E2, PTB 2023)", dA_max, d_clock, s_clock, ["filzinger"],
      "GUID-specific (forward statement: drift zero or negative)", unit="/yr",
      guid_text=f"Model A: -{abs(U0 * H0_yr):.1e} lambda^2 f_b /yr, i.e. between {dA_max:.0e} and 0 (<= 0); Model B: free sign",
      data_text="(1.8 +- 2.5) e-19 /yr",
      note=f"no sign is measured: P(drift < 0 | clocks) = {stats.norm.cdf(-d_clock / s_clock):.2f}")
gauss("D1.4", "Present drift of alpha, optical clocks (PTB 2021; superseded by D1.3, which includes its data)", dA_max, 1.0e-18, 1.1e-18,
      ["lange"], "GUID-specific", unit="/yr", data_text="(1.0 +- 1.1) e-18 /yr", scored=False,
      guid_text="as D1.3", note="version 5.1's predictions table quoted this value; the newer value of D1.3 is 4.4 times tighter")
inside("D1.5", "Oklo natural reactor, 1.8 Gyr ago", lam95**2 * f_b_hi * (solA.sol(-math.log1p(z_oklo))[0] - solA.y[0, -1]), -1.1e-8, 1.1e-8,
       "95% CL", ["oklo_dh", "oklo_dd"], "GUID-specific", guid_text="Model A: < 1e-15; Model B: -(drift/H0) G(z_Oklo)",
       note=f"z_Oklo = {z_oklo:.3f} (1.8 Gyr in Planck 2018 LambdaCDM)")
for rid, (lab, ref, z, v, s), title in (("D1.6", alpha_data[1], "Quasar absorption, ESPRESSO, z = 1.15"),
                                         ("D1.7", alpha_data[2], "Quasar absorption, four systems at z = 5.5 to 7.1"),
                                         ("D1.8", alpha_data[3], "CMB (Planck 2015), alpha at recombination"),
                                         ("D1.9", alpha_data[4], "BBN (alpha alone varying; 2001 abundances)")):
    vA = lam95**2 * f_b_hi * (solA.sol(max(-math.log1p(z), N0))[0] - solA.y[0, -1])
    gauss(rid, f"Delta alpha/alpha: {title}", vA, v, s, [ref], "GUID-specific", guid_text=f"Model A: {fmt(vA)} (at the largest allowed lambda)",
          data_text=f"{fmt(v)} +- {fmt(s)} (1 sigma)")
gauss("D1.10", "Planck intermediate XXIV, alpha at recombination (same data family as D1.8)", 0.0, 3.6e-3, 3.7e-3, ["planck_xxiv"],
      "GUID-specific", scored=False, guid_text="~0")
record("D1.11", "BBN in GUT-type models where all couplings vary with alpha", "not applicable: GUID's scalar multiplies only the Maxwell term",
       "|Delta alpha/alpha| < 50 ppm (2 sigma, no priors)", ["martins21"], "model assumption differs; listed for completeness", True, "-",
       scored=False)
gauss("D1.12", "Joint fit, Model B (thawing): present drift from clocks, Oklo, quasars, CMB and BBN together", 0.0, d_hat, d_sig,
      ["filzinger", "oklo_dh", "espresso", "wilczynska", "hartchluba", "avelino"], "GUID-specific", unit="/yr",
      guid_text="zero or negative (forward statement)", data_text=f"({d_hat:.2e} +- {d_sig:.2e}) /yr",
      note=f"P(drift < 0) = {P_neg:.2f}; the data do not determine the sign (a negative drift is disfavoured by {d_hat / d_sig:.2f} sigma)")
lam_desi = max(abs(d95[0]), abs(d95[1])) / (H0_yr * abs(u0_desi))
lam_lcdm_like = max(abs(d95[0]), abs(d95[1])) / (H0_yr * abs(u0_th))
print(f"\nIf the information scalar is the field behind DESI's dark energy (1 + w0 = {1 + w0_desi:.3f}, phi'_0 = {u0_desi:.3f}), the drift bound "
      f"requires |lambda| < {lam_desi:.1e}, {lam95 / lam_desi:.0f} times below the free-fall bound. For 1 + w0 = 1e-3: |lambda| < {lam_lcdm_like:.1e}.")
D1 = dict(f_Ti=f_Ti, f_Pt=f_Pt, f_Be=f_Be, f_Earth=f_E, k_mic=k_mic, k_eotwash=k_ew, lambda_best=lam_best, lambda_95=lam95,
          lambda_95_microscope_only=lam95_mic, lambda_paper_1sigma_level=lam_paper,
          modelA=dict(phi_prime_today_per_lambda_fb=U0, drift_coeff_per_yr=U0 * H0_yr, f_b_upper=f_b_hi, f_b_helium_only=f_b_lo,
                      drift_at_lambda95_per_yr=dA_max, dalpha_cmb_at_lambda95=dalpha_A_cmb),
          modelB=dict(slope_shape=s_shape, one_plus_w0_shape=1 + w0_th, G={lab: G_shape(z) for lab, _, z, _, _ in alpha_data},
                      z_oklo=z_oklo, implied_drift=[dict(label=l, ref=r, z=z, drift=d, sigma=s) for l, r, z, d, s in implied],
                      drift_hat=d_hat, drift_sigma=d_sig, chi2=chi2_alpha, P_negative=P_neg, drift_95=list(d95),
                      one_plus_w0_desi=1 + w0_desi, phi_prime_desi=u0_desi, lambda_max_if_desi_thawing=lam_desi,
                      lambda_max_if_1pw0_1e3=lam_lcdm_like))

# =================================================================================================================================
print("\n" + "=" * 100 + "\nD2  PPN gravity: GUID predicts general relativity's values (minimal coupling, Proposition 2)\n" + "=" * 100)
gr = "shared with GR"
gauss("D2.1", "Light bending / Shapiro delay, gamma - 1 (Cassini)", 0.0, 2.1e-5, 2.3e-5, ["cassini"], gr, guid_text="0 exactly")
gauss("D2.2", "gamma - 1, planetary ephemerides (combined intervals)", 0.0, 0.55e-5, 1.35e-5, ["fienga"], gr, guid_text="0 exactly",
      note="Cassini tracking data enter the ephemerides")
gauss("D2.3", "beta - 1, planetary ephemerides (combined intervals)", 0.0, -0.45e-5, 1.75e-5, ["fienga"], gr, guid_text="0 exactly")
gauss("D2.4", "beta - 1, Mercury from MESSENGER (gamma fixed to Cassini)", 0.0, -1.6e-5, 1.8e-5, ["genova", "fienga"], gr, guid_text="0 exactly")
gauss("D2.5", "Nordtvedt parameter eta, MESSENGER", 0.0, -6.6e-5, 7.2e-5, ["genova"], gr, guid_text="0 exactly")
gauss("D2.6", "beta - 1, lunar laser ranging", 0.0, 6.2e-5, 7.2e-5, ["biskupek"], gr, guid_text="0 exactly")
gauss("D2.7", "gamma - 1, lunar laser ranging", 0.0, 1.7e-4, 1.6e-4, ["biskupek"], gr, guid_text="0 exactly")
gauss("D2.8", "Earth-Moon free fall towards the Sun, Delta(m_g/m_i) (WEP + SEP), lunar laser ranging", 0.0, -2.1e-14, 2.4e-14,
      ["biskupek"], gr, guid_text="0 (scalar term 2 lambda^2 f_Sun (f_E - f_Moon) < 1e-17)")
gauss("D2.9", "Strong-field SEP, pulsar in a triple system (Delta)", 0.0, 0.5e-6, 1.8e-6 / Z95, ["voisin"], gr, guid_text="0 exactly",
      data_text="(0.5 +- 1.8) e-6 at 95% (0.92e-6 at 1 sigma)")
gauss("D2.10", "Gravitational redshift (local position invariance), Galileo satellites", 0.0, 0.19e-5, 2.48e-5, ["delva"], gr,
      guid_text="0 (the lapse of GR, Section 6.2)")
inside("D2.11", "Speed of gravitational waves, (c_gw - c)/c (GW170817 + GRB 170817A)", 0.0, -3e-15, 7e-16,
       "interval stated by the collaborations, conservative, no CL", ["gw170817"], gr,
       guid_text="0 (classical waves of the frame at c)")
inside("D2.12", "Graviton mass", 0.0, 0.0, 2.42e-23, "90% credible", ["gwtc3tgr"], gr, unit="eV/c^2", guid_text="0 (massless spin-2 wave of the frame)")
record("D2.13", "Gravitational-wave polarizations", "two tensor polarizations (D(D-3)/2 = 2 in 3+1)", "no evidence for non-GR polarization modes",
       ["gwtc3tgr"], "qualitative", True, gr, scored=False)
d2_pulls = [r["pull"] for r in ROWS if r["section"] == "D2" and r["pull"] is not None and r["scored"]]
chi2_d2 = sum(p * p for p in d2_pulls)
p_d2 = stats.chi2.sf(chi2_d2, len(d2_pulls))
print(f"\nD2 combined: chi2 = {chi2_d2:.2f} for {len(d2_pulls)} scored Gaussian pulls (p = {p_d2:.2f}); D2.6 to D2.8 come from one lunar "
      f"fit and D2.3/D2.5 share MESSENGER data, so this p-value is indicative.")

# =================================================================================================================================
print("\n" + "=" * 100 + "\nD3  Cosmology of the balanced state: flat LambdaCDM with a de Sitter floor\n" + "=" * 100)
lcdm = "shared with LambdaCDM"


def z_t(Om):
    return (2 * (1 - Om) / Om) ** (1 / 3) - 1


def z_t_err(Om, dOm):
    return abs(z_t(Om + 1e-6) - z_t(Om - 1e-6)) / 2e-6 * dOm


zt_P, zt_P_err = z_t(Om_P), z_t_err(Om_P, Om_P_err)
zt_D, zt_D_err = z_t(0.3027), z_t_err(0.3027, 0.0036)
# Transition-redshift determinations: one value per independent data set; the three parametrizations of Jesus et al. (same data)
# are merged into one value whose error adds their half-range (parametrization systematics) to the mean statistical error.
jz = np.array([0.806, 0.870, 0.973])
js = np.array([0.094, 0.063, 0.058])
j_mean, j_sig = float(jz.mean()), float(math.hypot(js.mean(), (jz.max() - jz.min()) / 2))
zt_meas = [("cosmic chronometers (Moresco 2016)", "moresco", 0.4, 0.1), ("SNe Ia + H(z), 3 parametrizations (Jesus 2018)", "jesus", j_mean, j_sig)]
# Farooq et al. 2017 (H(z) compilation): the weighted mean depends mainly on the H0 prior; reported, not combined.
zt_farooq = [("H(z) data, H0 prior 68 +- 2.8 (Farooq 2017)", "farooq", 0.72, 0.05), ("H(z) data, H0 prior 73.24 +- 1.74 (Farooq 2017)", "farooq", 0.84, 0.03)]
wz = np.array([1 / s**2 for *_, s in zt_meas])
vz = np.array([v for _, _, v, _ in zt_meas])
zt_mean = float(np.sum(wz * vz) / np.sum(wz))
chi2_zt = float(np.sum(wz * (vz - zt_mean) ** 2))
S_zt = max(1.0, math.sqrt(chi2_zt / (len(vz) - 1)))
zt_sig = S_zt / math.sqrt(np.sum(wz))
print(f"GUID transition redshift: {zt_P:.3f} +- {zt_P_err:.3f} (Planck Omega_m), {zt_D:.3f} +- {zt_D_err:.3f} (DESI DR2 + CMB Omega_m)")
for lab, ref, v, s in zt_meas:
    print(f"   {lab}: {v:.3f} +- {s:.3f} -> pull against GUID {(v - zt_P) / math.hypot(s, zt_P_err):+.2f} sigma")
print(f"   the two determinations disagree with each other by {abs(vz[0] - vz[1]) / math.sqrt(1 / wz[0] + 1 / wz[1]):.1f} sigma; "
      f"PDG-style scale factor S = {S_zt:.2f}; combined z_t = {zt_mean:.3f} +- {zt_sig:.3f}")
zt_all = zt_meas + zt_farooq
zt_pulls = {lab: (v - zt_P) / math.hypot(s, zt_P_err) for lab, _, v, s in zt_all}
record("D3.1", "Transition redshift to acceleration, z_t = (2 Omega_L/Omega_m)^(1/3) - 1", f"{zt_P:.3f} +- {zt_P_err:.3f} (Planck 2018 Omega_m)",
      "inconclusive: 0.40 +- 0.10 (chronometers), 0.72 +- 0.05 or 0.84 +- 0.03 (H(z), H0 prior 68 or 73.24), "
                f"{j_mean:.2f} +- {j_sig:.2f} (SNe + H(z))",
      ["moresco", "jesus", "farooq", "planck18"], "inconclusive: individual pulls in rows D3.1a to D3.1d", True, lcdm,
      note="pulls against GUID: " + ", ".join(f"{lab} {pv:+.1f} sigma" for lab, pv in zt_pulls.items()) +
           f". The determinations disagree with each other (chronometers against SNe + H(z) at {abs(vz[0] - vz[1]) / math.sqrt(1 / wz[0] + 1 / wz[1]):.1f} "
           f"sigma) and depend on the H0 prior and the parametrisation; a post-hoc scaled mean of two of them ({zt_mean:.2f} +- {zt_sig:.2f}, "
           f"S = {S_zt:.2f}) is reported here and not scored. Dahiya & Jain 2023: best fits 0.61-0.82.")
for k, (lab, ref, v, s) in enumerate(zt_all):
    gauss("D3.1" + "abcd"[k], f"Transition redshift, {lab}", zt_P, v, s, [ref], lcdm, guid_sig=zt_P_err,
          scored=False, guid_text=f"{zt_P:.3f}")
# de Sitter rate H_inf = H0 sqrt(Omega_L); with Omega_m h^2 fixed by the CMB, H_inf^2 = H0^2 - 1e4 omega_m
om_h2 = ombh2 + omch2 + 0.06 / 93.14
Hinf_P = math.sqrt(H0_kms**2 - 1e4 * om_h2)
Hinf_P_err = H0_kms / Hinf_P * H0_err
Hinf_D = 68.17 * math.sqrt(1 - 0.3027)
Hinf_D_err = math.hypot(math.sqrt(1 - 0.3027) * 0.28, 68.17 * 0.0036 / (2 * math.sqrt(1 - 0.3027)))
record("D3.2", "de Sitter floor of the Hubble rate, H_inf = sqrt(Omega_L) H0", f"{Hinf_P:.2f} +- {Hinf_P_err:.2f} km/s/Mpc (Planck 2018); "
       f"r_dS = c/H_inf = {c / (Hinf_P * 1e3 / Mpc):.3e} m", f"DESI DR2 + CMB LambdaCDM: {Hinf_D:.2f} +- {Hinf_D_err:.2f} km/s/Mpc",
       ["planck18", "desi2"], "derived, not measured: H_inf exists only if w = -1", True, lcdm, scored=False)
desi_rows = [("DESI DR2 BAO + CMB", -0.42, 0.21, -1.75, 0.58, 3.1), ("+ Pantheon+", -0.838, 0.055, -0.62, 0.205, 2.8),
             ("+ Union3", -0.667, 0.088, -1.09, 0.29, 3.8), ("+ DES-SN5YR", -0.752, 0.057, -0.86, 0.215, 4.2),
             ("+ DES-Dovekie (recalibrated)", -0.803, 0.054, -0.72, 0.21, 3.2)]
record("D3.3", "de Sitter floor (w = -1 for all time) against DESI DR2's evolving dark energy (w0, wa)",
       "w0 = -1, wa = 0 (the balanced state as a cosmological constant)",
       "LambdaCDM disfavoured at 2.8 to 4.2 sigma (DESI DR2 + CMB + SNe), 3.1 sigma without SNe, 3.2 sigma with recalibrated DES SNe",
       ["desi2", "dovekie"], "significance quoted by the collaborations (Delta chi^2 of w0waCDM against LambdaCDM, 2 parameters, as "
                             "Gaussian-equivalent sigma); scored on the least significant combination, 2.8 sigma", False, lcdm,
       note="tension, not discovery: below 5 sigma in every combination and dependent on the supernova sample; the DES recalibration "
            "lowered 4.2 to 3.2 sigma with Bayesian odds of only ~5:1. If it holds, the de Sitter floor and the reading of Section 11.5 "
            "must be redone, as Part I says.", pull=2.8)
gauss("D3.4", "Hubble constant: GUID's late universe (flat LambdaCDM fitted to the CMB) against the Cepheid distance ladder (SH0ES)", H0_kms,
      73.04, 1.04, ["sh0es", "planck18"], lcdm, guid_sig=H0_err, unit="km/s/Mpc", guid_text="67.4 +- 0.5 km/s/Mpc (Planck 2018 LambdaCDM)",
      data_text="73.04 +- 1.04 km/s/Mpc", note="the Hubble tension of LambdaCDM, inherited unchanged; GUID adds nothing that moves H0")
gauss("D3.5", "Hubble constant against the tip of the red giant branch (CCHP, HST + JWST)", H0_kms, 70.39, math.sqrt(1.22**2 + 1.33**2 + 0.70**2),
      ["cchp", "planck18"], lcdm, guid_sig=H0_err, unit="km/s/Mpc", guid_text="67.4 +- 0.5 km/s/Mpc",
      data_text="70.39 +- 1.22 (stat) +- 1.33 (sys) +- 0.70 (SN), combined 1.94 km/s/Mpc")
inside("D3.6", "Spatial flatness after inflation (Section 11.3): Omega_K, Planck 2018 + BAO", 0.0, -0.004, 0.004, "95% CL", ["planck18x"],
       "shared with inflation + LambdaCDM", guid_text="0 to within ~1e-5", data_text="flat to 0.4% (95% CL)")
gauss("D3.7", "Spatial flatness: Omega_K, DESI DR2 BAO + CMB", 0.0, 2.3e-3, 1.1e-3, ["desi2"], "shared with inflation + LambdaCDM",
      guid_text="0 to within ~1e-5", note="DESI: 'no significant preference for non-flat LambdaCDM'")
D3 = dict(z_t_planck=zt_P, z_t_planck_err=zt_P_err, z_t_desi=zt_D, z_t_desi_err=zt_D_err, z_t_combined=zt_mean, z_t_combined_err=zt_sig,
          z_t_scale_factor=S_zt, jesus_merged=[j_mean, j_sig], H_inf_planck=[Hinf_P, Hinf_P_err], H_inf_desi=[Hinf_D, Hinf_D_err],
          desi_w0wa=[dict(data=a, w0=b, w0_err=cc, wa=d, wa_err=e, sigma=f) for a, b, cc, d, e, f in desi_rows])

# =================================================================================================================================
print("\n" + "=" * 100 + "\nD4  Inflation and the start: Starobinsky / Higgs inflation, n_s = 1 - 2/N, r = 12/N^2\n" + "=" * 100)
Ns = np.arange(50, 61)
ns_pred = 1 - 2 / Ns
r_pred = 12 / Ns**2
ns_data = [("Planck 2018 (TT,TE,EE+lowE+lensing)", "planck18x", 0.9649, 0.0042), ("P-ACT (ACT DR6 + Planck)", "act_dr6", 0.9709, 0.0038),
           ("P-ACT-LB (+ CMB lensing + DESI DR1 BAO)", "act_dr6", 0.974, 0.003)]
D4 = dict(N=Ns.tolist(), n_s=ns_pred.tolist(), r=r_pred.tolist(), datasets=[])
for i, (lab, ref, v, s) in enumerate(ns_data):
    pulls = (v - ns_pred) / s
    best = int(np.argmin(np.abs(pulls)))
    lo, hi = v - Z95 * s, v + Z95 * s
    Nmin, Nmax = 2 / (1 - lo), (2 / (1 - hi) if hi < 1 else math.inf)
    ok = bool(np.any(np.abs(pulls) < Z95))
    D4["datasets"].append(dict(label=lab, n_s=v, sigma=s, best_N=int(Ns[best]), pull_best=float(pulls[best]), pull_N50=float(pulls[0]),
                               pull_N60=float(pulls[-1]), N_range_95=[Nmin, Nmax]))
    record(f"D4.{i + 1}", f"Scalar spectral index n_s for N = 50 to 60 e-folds, against {lab}",
           f"n_s = {ns_pred[0]:.4f} (N = 50) to {ns_pred[-1]:.4f} (N = 60)", f"{v} +- {s} (68%)", [ref],
           f"best N = {Ns[best]}: pull {pulls[best]:+.2f} sigma (N = 50: {pulls[0]:+.2f}, N = 60: {pulls[-1]:+.2f}); 95% needs N in "
           f"[{Nmin:.1f}, {Nmax:.1f}]",
           ok, "plateau potential named by Part I (Starobinsky/Higgs), not derived by GUID",
           scored=(i != 1), pull=float(pulls[best]),
           note=("P-ACT overlaps both neighbours; reported, not scored" if i == 1 else
                 ("the leading-order plateau predictions need N >= 63 here; the shift comes partly from the BAO in the combination"
                  if i == 2 else "")))
inside("D4.4", "Tensor-to-scalar ratio r = 12/N^2 (N = 50 to 60)", float(r_pred[0]), 0.0, 0.036, "95% CL", ["bk18"],
       "plateau potential named by Part I (Starobinsky/Higgs), not derived by GUID", guid_text=f"{r_pred[-1]:.4f} to {r_pred[0]:.4f}",
       data_text="r_0.05 < 0.036 (95%), sigma(r) = 0.009",
       note="the next generation (sigma(r) ~ 1e-3) reaches it; GUID itself allows the standard spectrum (Section 11.4)")
# Ordering of the strong split and inflation (Hypothesis 6'): monopoles. Kibble-Preskill estimate without inflation: one monopole per
# horizon at the split, n/T^3 ~ (H/T)^3 with H = 1.66 sqrt(g*) T^2 / M_Pl, T_c ~ M_X = 1e16 GeV, g* = 106.75; today n = (n/s) s0.
M_Pl = 1.220890e19
Tc = 1e16
n_over_T3 = (1.66 * math.sqrt(106.75) * Tc / M_Pl) ** 3
n_over_s = n_over_T3 / (2 * math.pi**2 / 45 * 106.75)
s0 = 2891.2                                         # entropy density today, cm^-3 (T_CMB = 2.7255 K)
flux_noinfl = n_over_s * s0 * (1e-3 * c * 100) / (4 * math.pi)
record("D4.5", "Ordering: the strong split before or during inflation (Hypothesis 6') against relic monopoles",
       "no relic monopoles (diluted by >= 50 e-folds, e^-150)", "MACRO: flux < 1.4e-16 cm^-2 s^-1 sr^-1 (90% CL)", ["macro"],
       f"a split after inflation (Kibble-Preskill estimate, T_c = 1e16 GeV, v = 1e-3 c) gives {flux_noinfl:.0e} cm^-2 s^-1 sr^-1, "
       f"{flux_noinfl / 1.4e-16:.0e} times the bound; GUID's ordering gives 0", True, "shared with standard inflationary cosmology",
       note="the same datum is scored once, in D8.2", scored=False)
record("D4.6", "Reheating below the unification energy (needed for D4.5)",
       "T_reh < M_X", "instantaneous reheating at the r bound gives T_reh <= (30/(pi^2 g*))^(1/4) V^(1/4) = 5.7e15 GeV for V^(1/4) < 1.4e16 GeV; "
       "proton decay gives M_X >~ 4.8e15 GeV (Part I's estimate, [Q20])", ["bk18", "superk"],
       "not decided by data: both orderings of T_reh,max and M_X,min are still allowed; a constraint on the reheating model", True,
       "shared with standard inflationary cosmology", scored=False)

# =================================================================================================================================
print("\n" + "=" * 100 + "\nD5  Black holes: Kerr efficiency, spins, the area theorem, Hawking radiation\n" + "=" * 100)


def r_isco(a):
    aa = abs(a)
    z1 = 1 + (1 - aa * aa) ** (1 / 3) * ((1 + aa) ** (1 / 3) + (1 - aa) ** (1 / 3))
    z2 = math.sqrt(3 * aa * aa + z1 * z1)
    sgn = -1 if a >= 0 else 1                              # prograde (a > 0) or retrograde (a < 0) orbit
    return 3 + z2 + sgn * math.sqrt((3 - z1) * (3 + z1 + 2 * z2))


def eff(a):
    """Novikov-Thorne radiative efficiency 1 - E_isco (Bardeen, Press and Teukolsky 1972), signed spin."""
    r = r_isco(a)
    return 1 - (r**1.5 - 2 * r**0.5 + a) / (r**0.75 * math.sqrt(r**1.5 - 3 * r**0.5 + 2 * a))


eff_min, eff0, eff_max = eff(-1.0), eff(0.0), eff(1 - 1e-12)
method(f"Kerr efficiency: a = -1 gives {eff_min:.4f} (1 - sqrt(25/27) = {1 - math.sqrt(25 / 27):.4f}), a = 0 gives {eff0:.4f} "
       f"(1 - sqrt(8/9)), a -> 1 gives {eff_max:.4f} (1 - 1/sqrt 3)",
       abs(eff_min - (1 - math.sqrt(25 / 27))) < 1e-9 and abs(eff0 - (1 - math.sqrt(8 / 9))) < 1e-12 and abs(eff_max - (1 - 1 / math.sqrt(3))) < 1e-3)


def spin_of(e):
    if e <= eff_min:
        return -1.0
    if e >= eff(0.9999999):
        return 1.0
    return optimize.brentq(lambda a: eff(a) - e, -1.0, 0.9999999)


soltan = [("Marconi et al. 2004", "marconi", 0.04, 0.16), ("Shankar et al. 2009", "shankar", 0.075, 0.075 * 1.25),
          ("Yu & Tremaine 2002 (luminous QSOs)", "yu_tremaine", 0.1, None), ("Davis & Laor 2011 (sample mean)", "davis_laor",
                                                                                10 ** -1.05, None)]
D5 = dict(eff_min=eff_min, eff_a0=eff0, eff_max=eff_max, soltan=[])
for i, (lab, ref, lo, hi) in enumerate(soltan):
    a_lo, a_hi = spin_of(lo), (spin_of(hi) if hi else None)
    D5["soltan"].append(dict(label=lab, eps_lo=lo, eps_hi=hi, spin_lo=a_lo, spin_hi=a_hi))
    rng = f"{lo:.3f} to {hi:.3f}" if hi else (f"above {lo:.2f}" if "Yu" in lab else f"{lo:.3f} (scatter 0.52 dex)")
    spins = f"a = {a_lo:+.2f} to {a_hi:+.2f}" if hi else (f"a > {a_lo:+.2f}" if "Yu" in lab else f"a = {a_lo:+.2f} at the mean")
    top = hi if hi else lo
    record(f"D5.{i + 1}", f"Radiative efficiency of accretion (Soltan argument): {lab}",
           f"thin disk at the ISCO: {eff_min:.3f} (a = -1) to {eff_max:.3f} (a = 1); implied {spins}", f"epsilon = {rng}", [ref],
           f"measured efficiency {'up to ' if hi else ''}{top:.3f} {'<=' if top <= eff_max else '>'} the Kerr maximum {eff_max:.3f}",
           top <= eff_max, "shared with GR (Kerr)",
           note="the Kerr value is an upper bound; efficiencies below 5.7% are possible for radiatively inefficient flows")
# Measured spins (Reynolds 2021, Tables 1 and 2): 90% ranges; lower limits as (lo, 1). Kerr bound |a| <= 1.
smbh = [(0.12, 0.96), (0.9, 1), (0.92, 1), (0.99, 1), (0.97, 1), (0.94, 1), (0.84, 0.97), (0.89, 0.97), (0.975, 1), (0.98, 1), (0.92, 1),
        (0.52, 0.86), (0.99, 1), (0.99, 1), (0.88, 1), (0.9, 1), (0.9, 1), (0.5, 1), (0.91, 0.99), (0.7, 1), (0.95, 1), (0.52, 1),
        (0.87, 0.96), (0.85, 1), (0.8, 1), (0.72, 0.95), (0.37, 0.71), (0.98, 1), (0.97, 1), (0.71, 0.80), (0.83, 1), (0.4, 1),
        (0.77, 1), (0.91, 0.96), (0.75, 1), (0.97, 1)]
xrb = [(0.78, 0.89), (0.79, 0.89), (-0.04, 0.45), (0.85, 0.97), (-0.07, 0.31), (0.44, 0.79), (0.98, 1), (0.59, 0.82), (0.33, 0.77),
       (0.97, 1), (0.78, 0.80), (0.43, 0.47), (0.9, 1), (0.95, 1), (0.2, 0.8), (0.92, 1), (0.86, 0.98), (0.61, 0.87), (0.85, 0.91),
       (0.99, 1), (0.66, 0.84), (-1.0, -0.32), (0.75, 0.94), (0.92, 1), (0.6, 0.8)]
n_bad = sum(1 for lo, hi in smbh + xrb if lo > 1 or hi < -1)
record("D5.5", "Kerr bound |a| <= 1 (Christodoulou's formula has no solution above a = 1) against measured spins",
       "every spin in [-1, 1]", f"{len(smbh)} supermassive (X-ray reflection) and {len(xrb)} stellar (reflection / continuum) spins, 90% ranges",
       ["reynolds"], f"{n_bad} of {len(smbh) + len(xrb)} ranges outside [-1, 1]", n_bad == 0, "shared with GR (Kerr)",
       note="weak test: the spectral models are Kerr models restricted to |a| <= 0.998, so the bound is partly built in; the measurements "
            "show the ergosphere engines run fast (most SMBHs below 3e7 solar masses have a > 0.9)")
record("D5.6", "Area theorem: the horizon never shrinks classically (GW150914 ringdown)", "Delta A >= 0",
       "area increased with probability 97% (95% without overtones)", ["isi"], "probability that the area did not shrink: 0.97",
       True, "shared with GR")
record("D5.7", "Area theorem (GW250114)", "Delta A >= 0", "remnant area larger than the sum of the initial areas 'to high credibility'",
       ["gw250114"], "qualitative statement of the collaboration", True, "shared with GR")
T_H_sun = hbar * c**3 / (8 * math.pi * G * M_sun * kB)
record("D5.8", "Hawking radiation of astrophysical black holes", f"unobservable: a solar-mass hole is at {T_H_sun:.1e} K, below the 2.7 K sky",
       "not observed", [], "no datum distinguishes", True, "shared with semiclassical gravity", scored=False)
D5.update(n_smbh=len(smbh), n_xrb=len(xrb), T_H_sun=T_H_sun)

# =================================================================================================================================
print("\n" + "=" * 100 + "\nD6  Bridge B: Diosi-Penrose decoherence rate G M^2 / (hbar R) against existing superpositions and bounds\n" + "=" * 100)


def E_sphere(M, R, d):
    """Penrose's self-energy difference E_Delta = (G/2) int int (rho1-rho2)(rho1'-rho2')/|x-x'| for a uniform sphere displaced by d."""
    x = d / R
    if x >= 2:
        return G * M * M / R * (1.2 - 1 / x)
    return G * M * M / R * (x * x / 2 - 3 * x**3 / 16 + x**5 / 160)


def E_gauss(M, s, d):
    """The same for a mass smeared as a Gaussian of width s (the DP regularisation R0)."""
    return G * M * M * (1 / (math.sqrt(math.pi) * s) - special.erf(d / (2 * s)) / d)


def E_fourier(M, formfactor2, d, kmax):
    """Quadrature check: E_Delta = (2 G M^2 / pi) int_0^inf F(k)^2 [1 - sin(k d)/(k d)] dk."""
    f = lambda k: formfactor2(k) * (1 - np.sinc(k * d / math.pi))
    return 2 * G * M * M / math.pi * integrate.quad(f, 0, kmax, limit=2000)[0]


Rt, Mt = 1.0, 1.0 / math.sqrt(G)
F_sph = lambda k: (3 * (math.sin(k * Rt) - k * Rt * math.cos(k * Rt)) / (k * Rt) ** 3) ** 2 if k > 1e-6 else 1.0
F_gau = lambda k: math.exp(-k * k * Rt * Rt)          # |F|^2 of exp(-r^2 / 2 s^2)
ok_sph = all(abs(E_fourier(Mt, F_sph, d, 4000) / E_sphere(Mt, Rt, d) - 1) < 2e-3 for d in (0.3, 1.0, 2.0, 5.0))
ok_gau = all(abs(E_fourier(Mt, F_gau, d, 60) / E_gauss(Mt, Rt, d) - 1) < 1e-6 for d in (0.3, 1.0, 5.0))
method("closed-form DP self-energy of a uniform sphere agrees with the Fourier quadrature (d/R = 0.3, 1, 2, 5)", ok_sph)
method("closed-form DP self-energy of a Gaussian mass agrees with the Fourier quadrature", ok_gau)

R0_min, R0_fig = 0.54e-10, 4e-10      # Donadi 95% bound; Figurato's summary of current bounds
expts = [  # label, ref, mass kg, radius m (sphere) or None (atom), separation m, coherence time s, atoms, mass per atom (u)
    ("Oligoporphyrins, 28 kDa (Fein et al. 2019)", "fein", 28000 * u_kg, (3 * 28000 * u_kg / (4 * math.pi * 1300.0)) ** (1 / 3), 266e-9, 7e-3,
     2000, 28000 / 2000),
    ("Na clusters, 197 kDa (Pedalino et al. 2025)", "pedalino", 197000 * u_kg, 4e-9, 80e-9, 2 * 0.983 / 160, 7000, 197000 / 7000),
    ("Rb-87 atoms, 54 cm (Kovachy et al. 2015)", "kovachy", 86.909 * u_kg, None, 0.54, 1.0, 1, 86.909),
    ("Cs-133 atoms held 20 s (Xu et al. 2019)", "xu", 132.905 * u_kg, None, 3.9e-6, 20.0, 1, 132.905),
]
D6 = dict(R0_min_donadi=R0_min, R0_figurato=R0_fig, experiments=[])
for i, (lab, ref, M, R, d, tau, nat, ma) in enumerate(expts):
    if R is None:      # one atom: its mass, smeared over R0
        rate_paper = G * M * M / (hbar * R0_min)
        E_full = E_gauss(M, R0_min, d)
    else:              # bulk sphere plus the granular term of its nuclei, smeared over the smallest allowed R0 (conservative)
        rate_paper = G * M * M / (hbar * R)
        E_full = E_sphere(M, R, d) + nat * E_gauss(ma * u_kg, R0_min, d)
    rate_full = E_full / hbar
    rate = max(rate_paper, rate_full)
    loss = rate * tau
    D6["experiments"].append(dict(label=lab, ref=ref, mass_kg=M, radius_m=R, separation_m=d, coherence_s=tau, rate_paper=rate_paper,
                                  rate_full=rate_full, decoherence_in_run=loss, margin=1 / loss))
    record(f"D6.{i + 1}", f"Coherence of the largest superpositions: {lab}",
           f"Bridge B rate {rate:.1e} /s (G M^2/hbar R: {rate_paper:.1e}; full DP with R0 = {R0_min:.2e} m: {rate_full:.1e}); "
           f"coherence time {1 / rate:.1e} s",
           f"M = {M:.2e} kg, separation {d:.2e} m, coherence ~{tau:.3g} s, interference seen", [ref],
           f"predicted decoherence during the run Gamma tau = {loss:.1e} (OK if < 0.1); margin {1 / loss:.0e}", loss < 0.1,
           "GUID-specific (Bridge B = Diosi-Penrose)")
inside("D6.5", "Diosi-Penrose smearing length R0 against spontaneous radiation (underground Ge detector)", R0_fig, R0_min, math.inf,
       "95% probability", ["donadi"], "GUID-specific (Bridge B needs a smearing length)", unit="m",
       guid_text="R0 >= 4e-10 m adopted (version 5.1 wrote 'at least about 1e-10 m')",
       note="Penrose's parameter-free choice (R0 = nuclear wave-function size, 5e-12 m for Ge) is excluded; Bridge B survives only with a free R0")
inside("D6.6", "R0 against the summary of current bounds", R0_fig, R0_fig, math.inf, "as stated", ["figurato"],
       "GUID-specific", unit="m", guid_text="R0 >= 4e-10 m", note="version 5.1's '1e-10 m' sat below this summary; v6 uses 4e-10 m")
inside("D6.7", "R0 against gravitational-wave-detector heating", R0_fig, 40.1e-15, math.inf, "as stated", ["donadi"], "GUID-specific", unit="m",
       guid_text="R0 >= 4e-10 m")
DP_kernel = m_P**2 / c
disc = m_P * (L_P / c)
inside("D6.8", "Bridge B's diffusion, Diosi-Penrose kernel: l_P^2 D2 = m_P^2 / c", DP_kernel, 1e-40, 1e-9, "experimental window",
       ["osswd"], "GUID-specific", unit="kg^2 s/m", note="the window comes from torsion-balance noise (upper) and molecule interferometry (lower)")
inside("D6.9", "Bridge B's diffusion, discrete (local) model: (l_P^3/m_P) D2 = m_P t_P", disc, 1e-25, 1e-1, "experimental window", ["osswd"],
       "GUID-specific", unit="kg s", scored=False, note="this version is excluded, as Part I says")
# BMV microsphere and the first experiment that would see Bridge B
mm = 1e-14
R_bmv = (3 * mm / (4 * math.pi * 3510.0)) ** (1 / 3)
tau_bmv_paper = hbar * R_bmv / (G * mm * mm)
tau_bmv_full = hbar / E_sphere(mm, R_bmv, 250e-6)
granular_bmv = (mm / (12 * u_kg)) * E_gauss(12 * u_kg, R0_fig, 250e-6)
method(f"BMV microsphere: the granular term at R0 = 4e-10 m ({granular_bmv:.1e} J) is below 1e-3 of the bulk term ({E_sphere(mm, R_bmv, 250e-6):.1e} J)",
       granular_bmv < 1e-3 * E_sphere(mm, R_bmv, 250e-6))


def mass_for(tau, rho, geom=1.2):
    """Mass of a uniform sphere of density rho whose DP time (separation >> size) equals tau."""
    f = lambda lm: math.log(hbar * (3 * 10**lm / (4 * math.pi * rho)) ** (1 / 3) / (geom * G * 10 ** (2 * lm))) - math.log(tau)
    return 10 ** optimize.brentq(f, -30, 0)


first = {f"{t:g} s": dict(silica=mass_for(t, 2200.0), diamond=mass_for(t, 3510.0)) for t in (0.01, 0.1, 1.0, 10.0, 100.0)}
heaviest = max(e[2] for e in expts)
print(f"\nBMV microsphere (1e-14 kg, R = {R_bmv * 1e6:.2f} um): DP coherence time {tau_bmv_paper * 1e3:.1f} ms (paper's formula), "
      f"{tau_bmv_full * 1e3:.1f} ms (full DP, separation 250 um)")
for t, mm_ in first.items():
    print(f"   Bridge B decoheres a silica sphere within {t:>6} once M >= {mm_['silica']:.1e} kg "
          f"({mm_['silica'] / heaviest:.0e} times the heaviest superposed mass so far)")
D6.update(bmv=dict(radius_m=R_bmv, tau_paper_s=tau_bmv_paper, tau_full_s=tau_bmv_full), first_detection_mass_kg=first,
          heaviest_superposed_kg=heaviest)

# =================================================================================================================================
print("\n" + "=" * 100 + "\nD7  Contained remnants: primordial black holes in the asteroid-mass window\n" + "=" * 100)


def T_hawking(M):
    return hbar * c**3 / (8 * math.pi * G * M * kB)


t_age = 13.8e9 * year
M_ev = (t_age * hbar * c**4 / (5120 * math.pi * G**2)) ** (1 / 3)
record("D7.1", "Contained remnant (primordial black holes from the start) as all of the dark matter: the open window",
       "1e14 to 1e19 kg (1e17 to 1e22 g)", "window ~1e17 to 1e22 g open for current constraints (narrower for extended mass functions)",
       ["gorton_green"], "the GUID window coincides with the open window", True, "GUID route shares the PBH literature",
       note="edges: INTEGRAL/SPI MeV gamma rays and Voyager 1 e+- (light), Subaru-HSC M31 microlensing (heavy)")
inside("D7.2", "Mass below which holes have evaporated by now", M_ev, 1e12 / 10, 1e12 * 10, "order of magnitude", ["carr21"],
       "shared with semiclassical gravity", unit="kg", guid_text=f"{M_ev:.1e} kg (Stefan-Boltzmann estimate; Part I: a few 1e11 kg)",
       note=f"agreement within a factor {1e12 / M_ev:.1f}, inside the tolerance of ten chosen here",
       data_text="about 1e15 g = 1e12 kg (allowed: within a factor 10)")
record("D7.3", "Hawking temperatures at the window edges", f"{T_hawking(1e14):.2e} K (1e14 kg, kT = {kB * T_hawking(1e14) / eV / 1e6:.3f} MeV) and "
       f"{T_hawking(1e19):.2e} K (1e19 kg)", "the light edge is set by the evaporation products themselves (MeV photons, e+-)",
       ["gorton_green"], "the prediction 'Hawking glow at the light edge' is what bounds the window: live", True, "GUID route", scored=False)
D7 = dict(M_evaporated_kg=M_ev, T_1e14kg=T_hawking(1e14), T_1e19kg=T_hawking(1e19))

# =================================================================================================================================
print("\n" + "=" * 100 + "\nD8  The electroweak and strong splits\n" + "=" * 100)
hbar_GeVs = hbar / GeV
m_p_GeV = 0.93827


def tau_p(M_X, alpha_G=1 / 40):
    return M_X**4 / (alpha_G**2 * m_p_GeV**5) * hbar_GeVs / year


inside("D8.1", "Proton decay after a unification before the start (Hypothesis 6')", tau_p(1e16), 2.4e34, math.inf, "90% CL",
       ["superk"], "GUID allows, does not require", unit="yr", guid_text=f"possible; tau ~ {tau_p(1e16):.1e} yr for M_X = 1e16 GeV (to a factor ~10)",
       data_text="tau/B(p -> e+ pi0) > 2.4e34 yr", note="needs M_X >~ 4.8e15 GeV in Part I's estimate; Hyper-Kamiokande is the live test")
inside("D8.2", "Relic magnetic monopoles", 0.0, 0.0, 1.4e-16, "90% CL", ["macro"], "shared with standard inflationary cosmology",
       unit="cm^-2 s^-1 sr^-1", guid_text="0 (the strong split lies within the start)")
inv_a, s2, GF, mZ = 127.950, 0.23129, 1.1663787e-5, 91.1880
alpha0 = 1 / 137.035999177
mW_meas, mW_err = 80.3692, 0.0133
v_H = (math.sqrt(2) * GF) ** -0.5
mW_1 = math.sqrt(math.pi / inv_a / (math.sqrt(2) * GF * s2))           # g v / 2 with g = e/sin, e from alpha-hat(M_Z): Part I's route
mZ_1 = mW_1 / math.sqrt(1 - s2)
mW_2 = mZ * math.sqrt(1 - s2)                                            # m_Z cos theta-hat
A0 = math.pi * alpha0 / (math.sqrt(2) * GF * mZ**2)                     # on-shell with alpha(0), G_F, m_Z
s2_os = (1 - math.sqrt(1 - 4 * A0)) / 2
mW_3 = mZ * math.sqrt(1 - s2_os)
spread = (max(mW_1, mW_2, mW_3) - min(mW_1, mW_2, mW_3)) / 2
print(f"v = (sqrt2 G_F)^(-1/2) = {v_H:.2f} GeV; tree-level m_W: {mW_1:.3f} (Part I's route, alpha-hat(M_Z), s^2-hat, G_F), "
      f"{mW_2:.3f} (m_Z cos theta-hat), {mW_3:.3f} (on-shell alpha(0), G_F, m_Z); scheme half-spread {spread:.2f} GeV")
inside("D8.3", "W mass from the Higgs vacuum at tree level, m_W = g v / 2 (Part I: within half a per cent)", (mW_1 / mW_meas - 1) * 100, -0.5, 0.5,
       "Part I's stated tolerance, 0.5%", ["mw_comb", "alpha_mz", "s2w", "gf_mulan"], "Standard Model (tree level)", unit="%",
       guid_text=f"{mW_1:.3f} GeV ({(mW_1 / mW_meas - 1) * 100:+.2f}%)", data_text=f"{mW_meas} +- {mW_err} GeV",
       note=f"tree level is scheme dependent: MS-bar route {(mW_1 / mW_meas - 1) * 100:+.2f}%, m_Z cos theta-hat {mW_2:.2f} GeV "
            f"({(mW_2 / mW_meas - 1) * 100:+.2f}%), on-shell alpha(0), G_F, m_Z {mW_3:.2f} GeV ({(mW_3 / mW_meas - 1) * 100:+.2f}%); only the "
            f"MS-bar route meets 0.5%; the full Standard Model reaches 1e-4")
inside("D8.4", "Z mass at tree level, m_Z = m_W / cos theta_W", (mZ_1 / mZ - 1) * 100, -0.5, 0.5, "Part I's stated tolerance, 0.5%",
       ["mz_pdg", "alpha_mz", "s2w", "gf_mulan"], "Standard Model (tree level)", unit="%", guid_text=f"{mZ_1:.3f} GeV ({(mZ_1 / mZ - 1) * 100:+.2f}%)",
       data_text="91.1880 +- 0.0020 GeV")
inside("D8.5", "alpha born near 1/128 at the electroweak split, running to 1/137", abs(inv_a / 128 - 1) * 100, 0.0, 1.0, "within 1% of 1/128",
       ["alpha_mz", "codata22"], "Standard Model", unit="%", guid_text="1/alpha(M_Z) ~ 128; 1/alpha(0) = 137.036",
       data_text="1/alpha-hat(M_Z) = 127.950 +- 0.017 (MS-bar); 1/alpha(0) = 137.035999177(21)")
inside("D8.6", "The electroweak split is a smooth crossover (Higgs mass above the end point of the first-order line)", 125.11, 95.0, math.inf,
       "lattice end point < 95 GeV", ["atlas_mh", "kajantie", "donofrio"], "Standard Model", unit="GeV",
       guid_text="crossover at T_c = 159.5 +- 1.5 GeV (lattice), about 9e-12 s", data_text="m_H = 125.11 +- 0.11 GeV")
D8 = dict(v_GeV=v_H, mW_tree=[mW_1, mW_2, mW_3], mZ_tree=mZ_1, mW_meas=[mW_meas, mW_err], tau_p_1e16=tau_p(1e16),
          monopole_flux_without_inflation=flux_noinfl)

# =================================================================================================================================
print("\n" + "=" * 100 + "\nD9  The rest of the predictions table and ledger\n" + "=" * 100)
tsirelson = 2 * math.sqrt(2)
gauss("D9.1", "Content is quantum and reaches, but does not exceed, Tsirelson's bound 2 sqrt 2 (CHSH)", tsirelson, 2.82759, 0.00051, ["poh"],
      "shared with quantum mechanics", guid_text=f"S <= {tsirelson:.5f}, attainable (content); gates give 2",
      data_text="2.82759 +- 0.00051", note="S above 2 sqrt 2 would refute quantum content; the measured S lies 1.65 sigma below the bound")
inside("D9.2", "Loophole-free Bell violation, CHSH S (electron spins 1.3 km apart)", 2.42, 2.0, tsirelson, "quantum range", ["hensen"],
       "shared with quantum mechanics", guid_text="2 < S <= 2.828 for content", data_text="2.42 +- 0.20 (p = 0.039)")
frac_desi = 0.064 / 93.14 / omch2
frac_katrin = 3 * 0.45 / 93.14 / omch2
inside("D9.3", "The known neutrinos are not the remnant (cosmology)", frac_desi * 100, 0.0, 1.0, "95% CL", ["desi2", "planck18"],
       "shared with LambdaCDM", unit="% of the dark matter", guid_text="refuted as the remnant (ledger)",
       data_text=f"sum m_nu < 0.064 eV -> Omega_nu < {frac_desi * 100:.2f}% of Omega_c",
       note="version 5.1 used 0.072 eV (DESI 2024), which gives 0.6%; DESI DR2 tightens it")
inside("D9.4", "The known neutrinos are not the remnant (laboratory, KATRIN)", frac_katrin * 100, 0.0, 100.0, "90% CL", ["katrin"],
       "shared with the Standard Model", unit="% of the dark matter", guid_text="refuted as the remnant",
       data_text=f"m_nu < 0.45 eV -> 3 flavours below {frac_katrin * 100:.0f}% of Omega_c")
f_ref = 1 / year
omega_gw = 2 * math.pi**2 * f_ref**2 * (2.4e-15 + 0.7e-15) ** 2 / (3 * H0_si**2)
inside("D9.5", "The radiated remnant (gravitational waves) is not the dark matter", omega_gw, 0.0, 0.26 * 1e-7, "upper end of the 90% interval",
       ["nanograv"], "GUID route; shared with GR", guid_text=f"Omega_gw(1/yr) <= {omega_gw:.1e} (radiation, w = 1/3)",
       data_text="h_c = 2.4 (+0.7 -0.6) e-15 at 1/yr; allowed: below 1e-7 of Omega_c")
eta_higgs = 1.0e-3
record("D9.6", "Gravity weighs all energy (Hypothesis 1'), not only the Higgs-given share", "eta(Ti,Pt) = 0 for the plane",
       "MICROSCOPE eta = (-1.5 +- 2.75) e-15", ["microscope"], f"a Higgs-share-only gravity predicts eta ~ 1e-3 [Q6], excluded by "
       f"{eta_higgs / sig_mic:.0e} sigma; the plane's prediction is D1.1", True, "GUID v5.1 refinement; shared with GR", scored=False)

# =================================================================================================================================
NO_DATA = [
    ("Entanglement of two masses through gravity alone (Bose-Marletto-Vedral)", "N = 0; with Bridge B, decoherence at 72/s for 1e-14 kg",
     f"no experiment yet; masses superposed so far are {1e-14 / max(e[2] for e in expts):.0e} times lighter"),
    ("LOCC inequality with massive oscillators (Lami, Pedernales, Plenio)", "satisfied", "proposed"),
    ("Decoherence-diffusion trade-off at equality (balance rule)", "2 D2 = D1 D0^-1 D1^T",
     "only the window of D6.8 is known; neither decoherence nor diffusion has been measured"),
    ("Bridge B's decoherence of mesoscopic superpositions", "Gamma = G M^2 / hbar R",
     f"needs >~ {first['10 s']['silica']:.0e} kg held ~10 s, or 1e-14 kg for ~14 ms"),
    ("Single-graviton clicks", "possible from a classical wave", "do not discriminate"),
    ("Primordial tensor modes", "standard spectrum, r = 12/N^2 for Starobinsky", "only the bound r < 0.036"),
    ("Hawking glow at the light edge of the PBH window", "MeV photons and 511 keV positron annihilation", "bounds only"),
    ("Return of information from evaporating holes", "open in GUID", "no observation reaches it"),
    ("Proton decay", "possible, ~5e35 yr for M_X = 1e16 GeV", "bounds only (D8.1)"),
    ("Sign of the drift of alpha", "zero or negative", f"clocks and cosmology: P(negative) = {P_neg:.2f}; Model A's drift <~ 1e-23 /yr"),
]
COVERED = [("Galactic rotation curves, stochastic remnant, Bridge A", "docs/simulation/results/sparc_rotation.{json,md}",
            "Bridge A refuted by the rotation-curve points (98% of points below the model); one universal |gamma1| fits worse than the RAR "
            "(Delta BIC +5066)"),
           ("Accumulated remnant, history, halos, joint fit, cosmic time", "docs/simulation/results/remnant_history.{json,md}",
            "the two remnants do not combine; the consistent reading is the contained remnant (primordial black holes as cold dark matter) "
            "with a stochastic term too small to matter in galaxies"),
           ("BMV witness, hosted benchmarks, holographic codes, gravity ensembles", "docs/simulation/results/{bmv_witness,hosted_benchmarks,"
            "holographic_code,gravity_simulated}.json", "separate workstreams")]

# =================================================================================================================================
by_kind = {k: [r for r in ROWS if r["kind"] == k] for k in ("scored", "conditional", "consistency", "info")}
scored = by_kind["scored"]
n_ok = sum(1 for r in scored if r["verdict"] == "OK")
fails = [r for r in scored if r["verdict"] == "FAIL"]
specific = [r for r in scored if r["cls"].startswith("GUID-specific")]
cond_ok = [r["id"] for r in by_kind["conditional"] if r["verdict"] == "OK"]
cond_fail = [r["id"] for r in by_kind["conditional"] if r["verdict"] == "FAIL"]
cons_fail = [r["id"] for r in by_kind["consistency"] if r["verdict"] == "FAIL"]
m_ok = all(m["ok"] for m in METHOD)
CORREL = ("D3.3 and D3.7 both use DESI DR2 BAO with the CMB, D3.4 rests on the CMB fit of LambdaCDM, and the conditional D4.3 uses the CMB "
          "with DESI DR1 BAO: the FAILs are correlated, and the chance expectation assumes an independence that does not hold")
print("\n" + "=" * 100)
print(f"Method checks: {sum(m['ok'] for m in METHOD)} of {len(METHOD)} passed")
print(f"Rows: {len(ROWS)} = {len(scored)} scored + {len(by_kind['conditional'])} conditional + {len(by_kind['consistency'])} consistency "
      f"+ {len(by_kind['info'])} info")
print(f"Scored: {len(scored)}, OK {n_ok}, FAIL {len(fails)}; GUID-specific (scalar, Bridge B) {len(specific)}, shared with GR, LambdaCDM, "
      f"the Standard Model or quantum mechanics {len(scored) - len(specific)}")
print(f"Conditional on the plateau potential: OK {cond_ok}, FAIL {cond_fail}; consistency rows (not counted): {len(by_kind['consistency'])}"
      f"{', FAIL ' + str(cons_fail) if cons_fail else ''}")
print(f"If the scored rows were independent, a correct theory would fail about {0.05 * len(scored):.1f} of {len(scored)} at 95%; but {CORREL}.")
for r in fails + [r for r in by_kind["conditional"] if r["verdict"] == "FAIL"]:
    print(f"   FAIL [{r['id']}] ({r['kind']}) {r['observable']} ({r['measure']}; {r['cls']})")


# =================================================================================================================================
# Figures. Each is drawn at the width it prints in the paper (text width 6.3 in: A4 with 2.5 cm margins), so it is included at scale 1
# and its fonts print at 8 to 9 pt.
TEXTW = 6.3
INK, INK2, GRID = "#0b0b0b", "#52514e", "#d9d8d4"
C1, C2, C3 = "#2a78d6", "#eb6834", "#1baf7a"
CRIT = "#d03b3b"
FS = 8.0                                  # smallest font (ticks, legends, annotations), pt
plt.rcParams.update({"font.size": 8.5, "axes.titlesize": 8.5, "axes.labelsize": 8.5, "xtick.labelsize": FS, "ytick.labelsize": FS,
                     "legend.fontsize": FS, "axes.edgecolor": INK2, "axes.labelcolor": INK, "xtick.color": INK2, "ytick.color": INK2,
                     "axes.spines.top": False, "axes.spines.right": False, "axes.grid": True, "grid.color": GRID, "grid.linewidth": 0.5,
                     "legend.frameon": False, "pdf.fonttype": 42, "lines.linewidth": 1.6, "axes.titlelocation": "left"})


def save(fig, name):
    FIGURES.mkdir(parents=True, exist_ok=True)
    fig.savefig(FIGURES / name, metadata={"CreationDate": None, "Creator": None, "Producer": None})
    plt.close(fig)


FIGS = []
# 1. pull chart: two panels side by side, one row per scored Gaussian confrontation
SHORTP = {"D1.1": "free fall Ti/Pt", "D1.2": "free fall Be/Ti", "D1.3": r"$\dot\alpha$, clocks", "D1.6": r"$\Delta\alpha$, quasar $z=1.15$",
          "D1.7": r"$\Delta\alpha$, quasars $z\approx6$", "D1.8": r"$\Delta\alpha$, CMB", "D1.9": r"$\Delta\alpha$, BBN",
          "D1.12": r"$\dot\alpha$, joint (model B)", "D2.1": r"$\gamma$, Cassini", "D2.2": r"$\gamma$, ephemerides", "D2.3": r"$\beta$, ephemerides",
          "D2.4": r"$\beta$, MESSENGER", "D2.5": r"$\eta_N$, MESSENGER", "D2.6": r"$\beta$, lunar ranging", "D2.7": r"$\gamma$, lunar ranging",
          "D2.8": "Earth-Moon free fall", "D2.9": "SEP, triple pulsar", "D2.10": "redshift, Galileo", "D3.1": r"$z_t$, two determinations",
          "D3.3": r"$w=-1$ vs DESI DR2", "D3.4": r"$H_0$ vs SH0ES", "D3.5": r"$H_0$ vs CCHP (TRGB)", "D3.7": r"$\Omega_K$, DESI DR2 + CMB",
          "D4.1": r"$n_s$, Planck 2018", "D4.3": r"$n_s$, P-ACT-LB", "D9.1": "CHSH vs Tsirelson"}
pr = [r for r in ROWS if r["kind"] in ("scored", "conditional") and r["pull"] is not None]
groups = [[r for r in pr if r["section"] in ("D1", "D2")], [r for r in pr if r["section"] not in ("D1", "D2")]]
nmax = max(len(g) for g in groups)
fig, axes = plt.subplots(1, 2, figsize=(TEXTW, 0.15 * nmax + 0.75))
for ax, g in zip(axes, groups):
    ax.axvspan(-Z95, Z95, color="#e3edf9", zorder=0, lw=0)
    ax.axvline(0, color=INK2, lw=0.8)
    for i, r in enumerate(g):
        p = r["pull"]
        ok = r["verdict"] == "OK"
        cond = r["kind"] == "conditional"
        ax.plot([p], [i], marker="o" if ok else "X", ms=5 if ok else 7, color=C1 if ok else CRIT, ls="none",
                markerfacecolor="white" if cond else None, markeredgewidth=1.2)
        if not ok:
            ax.annotate(f"{'cond. ' if cond else ''}FAIL {p:+.1f}", (p, i), xytext=(-7, 0), textcoords="offset points", color=INK,
                        fontsize=FS, ha="right", va="center")
    ax.set_yticks(range(len(g)))
    ax.set_yticklabels([f"{r['id']}  {SHORTP.get(r['id'], r['observable'][:24])}{' (cond.)' if r['kind'] == 'conditional' else ''}"
                        for r in g])
    ax.set_ylim(nmax - 0.5, -0.5)
    ax.set_xlim(-5.5, 5.5)
    ax.set_xticks([-4, -2, 0, 2, 4])
    ax.grid(axis="y", lw=0)
    ax.set_xlabel(r"pull $(x-x_G)/\sigma$")
axes[0].set_title("D1, D2")
axes[1].set_title("D3, D4, D9")
axes[1].text(0.03, 0.05, "shaded: consistent at 95%\n" + r"$\times$: FAIL (shared with $\Lambda$CDM)" + "\nopen: conditional on the\nplateau potential",
             transform=axes[1].transAxes, fontsize=FS, color=INK2, va="bottom")
fig.tight_layout(w_pad=1.0)
save(fig, "data_pulls.pdf")
FIGS.append("data_pulls.pdf")

# 2. the information scalar
fig, (a1, a2) = plt.subplots(1, 2, figsize=(TEXTW, 2.45), gridspec_kw={"width_ratios": [1, 1.3]})
labels = [l for l, *_ in implied] + ["joint"]
bounds = [abs(d) + Z95 * s for *_, d, s in implied] + [max(abs(d95[0]), abs(d95[1]))]
for i, (l, b) in enumerate(zip(labels, bounds)):
    col = C2 if l == "joint" else C1
    a1.plot([1e-20, b], [i, i], color=col, lw=2, solid_capstyle="round")
    a1.plot([b], [i], "o", color=col, ms=4)
    a1.annotate(f"{b:.0e}", (b, i), xytext=(4, 0), textcoords="offset points", va="center", fontsize=FS, color=INK2)
a1.set_xscale("log")
a1.set_xlim(1e-20, 1e-8)
a1.set_xticks([1e-20, 1e-17, 1e-14, 1e-11, 1e-8])
a1.set_yticks(range(len(labels)))
a1.set_yticklabels(labels)
a1.invert_yaxis()
a1.set_xlabel(r"95% bound on $|\dot\alpha/\alpha|$ today, yr$^{-1}$")
a1.set_title("(a) what each datum allows (model B)")
lam = np.logspace(-11, -4, 400)
dgrid = np.linspace(-1.5e-18, 1.5e-18, 301)
LL, DD = np.meshgrid(lam, dgrid)
chi_l = np.array([chi2_ep(l) for l in lam])
CH = chi_l[None, :] + ((DD - d_hat) / d_sig) ** 2
CH -= CH.min()
a2.contourf(LL, DD * 1e18, CH, levels=[0, stats.chi2.ppf(0.95, 2)], colors=["#d6e6f8"])
a2.contour(LL, DD * 1e18, CH, levels=[stats.chi2.ppf(0.95, 2)], colors=[C1], linewidths=1.2)
for uu, col, lab in ((u0_desi, C2, f"thawing, $1+w_0={1 + w0_desi:.2f}$"),
                     (u0_th, C3, r"thawing, $1+w_0=10^{-3}$")):
    a2.plot(lam, lam * H0_yr * uu * 1e18, color=col, lw=1.4, label=lab)
    a2.plot(lam, -lam * H0_yr * uu * 1e18, color=col, lw=1.4)
a2.axhline(0, color=INK, lw=1.0, ls="--", label=r"model A, $|\dot\alpha/\alpha|<10^{-23}$ yr$^{-1}$")
a2.set_xscale("log")
a2.set_ylim(-1.5, 1.5)
a2.set_xticks([1e-10, 1e-8, 1e-6, 1e-4])
a2.set_xlabel(r"coupling $|\lambda|=|d\ln\alpha/d\phi|$")
a2.set_ylabel(r"$\dot\alpha/\alpha$ today, $10^{-18}$ yr$^{-1}$")
a2.set_title("(b) allowed region, 95% (shaded)")
fig.legend(*a2.get_legend_handles_labels(), loc="lower center", ncol=3, handlelength=1.6, columnspacing=1.2, borderaxespad=0.2)
fig.tight_layout(w_pad=1.0, rect=(0, 0.095, 1, 1))
save(fig, "data_alpha_scalar.pdf")
FIGS.append("data_alpha_scalar.pdf")

# 3. cosmology
fig, (b1, b2, b3) = plt.subplots(1, 3, figsize=(TEXTW, 2.05))
zl = [("Moresco 2016", 0.4, 0.1), ("Jesus 2018", j_mean, j_sig), ("combined", zt_mean, zt_sig)]
for i, (l, v, s) in enumerate(zl):
    b1.errorbar([v], [i], xerr=[[s], [s]], fmt="o", color=C2 if l == "combined" else C1, ms=4, lw=1.4)
b1.axvspan(zt_P - zt_P_err, zt_P + zt_P_err, color="#e6e6e3", lw=0)
b1.axvline(zt_P, color=INK, lw=1)
b1.set_yticks(range(len(zl)))
b1.set_yticklabels([l for l, *_ in zl])
b1.set_ylim(len(zl) - 0.5, -0.5)
b1.set_xlabel(r"$z_t$ ($1\sigma$)")
b1.set_title("(a) $z_t$; line: GUID")
hl = [("Planck LCDM", 67.4, 0.5), ("DESI+CMB LCDM", 68.17, 0.28), ("SH0ES", 73.04, 1.04), ("CCHP TRGB", 70.39, 1.94)]
for i, (l, v, s) in enumerate(hl):
    b2.errorbar([v], [i], xerr=[[s], [s]], fmt="o", color=C1 if "LCDM" in l else C2, ms=4, lw=1.4)
b2.set_yticks(range(len(hl)))
b2.set_yticklabels([l for l, *_ in hl])
b2.set_ylim(len(hl) - 0.5, -0.5)
b2.set_xlabel(r"$H_0$, km s$^{-1}$ Mpc$^{-1}$ ($1\sigma$)")
b2.set_title("(b) $H_0$; blue: GUID")
short_desi = ["BAO+CMB", "+Pantheon+", "+Union3", "+DES-SN5YR", "+DES-Dovekie"]
for i, ((l, w0v, w0e, wav, wae, sg), sl) in enumerate(zip(desi_rows, short_desi)):
    b3.errorbar([w0v], [i], xerr=[[w0e], [w0e]], fmt="o", color=C1, ms=4, lw=1.4)
    b3.annotate(f"{sg:.1f}$\\sigma$", (w0v, i), xytext=(0, 4), textcoords="offset points", fontsize=FS, ha="center", va="bottom",
                color=INK2)
b3.axvline(-1, color=INK, lw=1)
b3.set_xlim(-1.08, -0.1)
b3.set_yticks(range(len(desi_rows)))
b3.set_yticklabels(short_desi)
b3.set_ylim(len(desi_rows) - 0.5, -0.8)
b3.set_xlabel(r"$w_0$ (CPL, $1\sigma$)")
b3.set_title("(c) DESI DR2 $w_0$")
fig.tight_layout(w_pad=0.8)
save(fig, "data_cosmology.pdf")
FIGS.append("data_cosmology.pdf")

# 4. inflation (printed beside figure 6, 3.0 in wide)
fig, ax = plt.subplots(figsize=(3.0, 2.8))
for (lab, ref, v, s), col, name in zip(ns_data, (C1, C3, C2), ("Planck 2018", "P-ACT", "P-ACT-LB")):
    ax.axvspan(v - Z95 * s, v + Z95 * s, color=col, alpha=0.16, lw=0)
    ax.axvline(v, color=col, lw=1.2, label=f"{name}, 95% band")
ax.plot(ns_pred, r_pred, color=INK, lw=2, label="Starobinsky/Higgs, $N$=50-60")
for N in (50, 60):
    ax.plot([1 - 2 / N], [12 / N**2], "o", color=INK, ms=3.5)
    ax.annotate(f"$N$={N}", (1 - 2 / N, 12 / N**2), xytext=(0, -11), textcoords="offset points", fontsize=FS, ha="center")
ax.axhline(0.036, color=INK2, lw=1, ls="--", label="BICEP/Keck $r<0.036$")
ax.set_yscale("log")
ax.set_ylim(1e-3, 0.4)
ax.set_xlim(0.952, 0.982)
ax.set_xticks([0.955, 0.965, 0.975])
ax.set_xlabel("$n_s$")
ax.set_ylabel("$r$")
ax.legend(loc="upper left", frameon=True, framealpha=0.92, edgecolor="none", borderaxespad=0.3, handlelength=1.4, labelspacing=0.25)
fig.tight_layout()
save(fig, "data_inflation.pdf")
FIGS.append("data_inflation.pdf")

# 5. Kerr efficiency and spins
fig, (k1, k2) = plt.subplots(1, 2, figsize=(TEXTW, 2.35))
aa = np.linspace(-1, 0.99999, 800)
k1.plot(aa, [eff(a) for a in aa], color=INK, lw=2, label=r"Kerr thin disk, $1-E_{\rm isco}$")
k1.axhline(eff_max, color=INK2, lw=0.8, ls=":", label=f"$a\\to1$ limit, {eff_max:.3f}")
k1.axhspan(0.04, 0.16, color=C1, alpha=0.12, lw=0, label="Marconi 2004: 0.04-0.16")
k1.axhspan(0.075, 0.094, color=C2, alpha=0.45, lw=0, label="Shankar 2009: 0.075-0.094")
k1.axhline(0.1, color=C3, lw=1.3, ls="--", label="Yu & Tremaine 2002: > 0.1")
k1.axhline(10**-1.05, color="#6250d6", lw=1.3, ls="-.", label="Davis & Laor 2011: mean 0.089")
k1.set_ylim(0, 0.45)
k1.set_xlabel("spin $a$ (negative: retrograde)")
k1.set_ylabel("radiative efficiency")
k1.legend(loc="upper left", bbox_to_anchor=(0.0, 0.93), handlelength=1.6, labelspacing=0.2)
k1.set_title("(a) Soltan efficiencies on the Kerr curve")
for j, (lst, col, lab) in enumerate(((smbh, C1, "SMBH, X-ray reflection"), (xrb, C2, "X-ray binaries"))):
    for i, (lo, hi) in enumerate(sorted(lst)):
        k2.plot([lo, hi], [i + 0.35 * j, i + 0.35 * j], color=col, lw=1.4, label=lab if i == 0 else None)
k2.axvline(1, color=INK, lw=1)
k2.axvline(-1, color=INK, lw=1)
k2.set_xlabel("spin $a$, 90% range; lines: $|a|=1$")
k2.set_yticks([])
k2.legend(loc="upper left", handlelength=1.6)
k2.set_title("(b) measured spins (Reynolds 2021)")
fig.tight_layout(w_pad=1.0)
save(fig, "data_kerr.pdf")
FIGS.append("data_kerr.pdf")

# 6. Bridge B (printed beside figure 4, 3.2 in wide)
fig, ax = plt.subplots(figsize=(3.2, 2.8))
Mg = np.logspace(-26, -12, 300)
for rho, col, lab in ((2200.0, C1, "silica"), (19300.0, C2, "gold")):
    Rg = (3 * Mg / (4 * math.pi * rho)) ** (1 / 3)
    ax.plot(Mg, hbar * Rg / (1.2 * G * Mg**2), color=col, lw=1.6, label=f"Bridge B time, {lab} sphere")
short_exp = ["28 kDa", "197 kDa", "Rb, 54 cm", "Cs, 20 s"]
offsets = [(0, -11), (5, 3), (-5, -9), (5, 2)]
has = ["center", "left", "right", "left"]
for e, sl, off, ha in zip(D6["experiments"], short_exp, offsets, has):
    ax.plot([e["mass_kg"]], [e["coherence_s"]], "o", color=C3, ms=5)
    ax.annotate(sl, (e["mass_kg"], e["coherence_s"]), xytext=off, textcoords="offset points", fontsize=FS, ha=ha)
ax.plot([mm], [25.0], "s", color=INK, ms=5)
ax.annotate("BMV: needs 8-25 s,\nBridge B: 12 ms", (mm, 25.0), xytext=(0, 40), textcoords="offset points", fontsize=FS, ha="center",
            arrowprops=dict(arrowstyle="-", color=INK2, lw=0.6))
ax.plot([], [], "o", color=C3, label="superpositions made")
ax.set_xscale("log")
ax.set_yscale("log")
ax.set_xlim(1e-26, 1e-12)
ax.set_ylim(1e-4, 1e21)
ax.set_xticks([1e-26, 1e-22, 1e-18, 1e-14])
ax.set_yticks([1e0, 1e5, 1e10, 1e15, 1e20])
ax.set_xlabel("mass, kg")
ax.set_ylabel("coherence time, s")
ax.legend(loc="upper right", handlelength=1.4, labelspacing=0.25)
fig.tight_layout()
save(fig, "data_bridgeB.pdf")
FIGS.append("data_bridgeB.pdf")

# =================================================================================================================================
# Outputs
RESULTS.mkdir(parents=True, exist_ok=True)
summary = dict(rows=len(ROWS), scored=len(scored), passed=n_ok, failed=[r["id"] for r in fails], guid_specific_scored=[r["id"] for r in specific],
               shared_scored=len(scored) - len(specific), conditional=[r["id"] for r in by_kind["conditional"]], conditional_ok=cond_ok,
               conditional_fail=cond_fail, consistency=[r["id"] for r in by_kind["consistency"]], info=[r["id"] for r in by_kind["info"]],
               expected_chance_fails_if_independent=0.05 * len(scored), correlation_note=CORREL,
               method_checks=len(METHOD), method_passed=sum(m["ok"] for m in METHOD))
out = dict(script="docs/simulation/predictions_vs_data.py", verified_on=DATE_VERIFIED, criterion="scored and conditional rows: OK = consistent at 95% "
           "(|pull| < 1.96 or inside the stated allowed region, 90% regions labelled); consistency rows (prediction set from the datum) are "
           "CONS and not counted; info rows are not scored", summary=summary, rows=ROWS, method=METHOD, D1=D1, D2=dict(chi2=chi2_d2, n=len(d2_pulls), p=p_d2),
           D3=D3, D4=D4, D5=D5, D6=D6, D7=D7, D8=D8, no_data=[dict(prediction=a, guid=b, status=cc) for a, b, cc in NO_DATA],
           covered_elsewhere=[dict(topic=a, files=b, result=cc) for a, b, cc in COVERED], citations=CITATIONS, figures=FIGS)


def clean(o):
    if isinstance(o, dict):
        return {k: clean(v) for k, v in o.items()}
    if isinstance(o, (list, tuple)):
        return [clean(v) for v in o]
    if isinstance(o, (np.floating, float)):
        return None if not math.isfinite(float(o)) else float(f"{float(o):.6g}")
    if isinstance(o, np.integer):
        return int(o)
    return o


(RESULTS / "predictions_vs_data.json").write_text(json.dumps(clean(out), indent=1, ensure_ascii=True) + "\n")


def md_escape(s):
    return str(s).replace("|", "\\|")


SHORT = dict(microscope="Touboul et al. 2022 (MICROSCOPE)", eotwash="Schlamminger et al. 2008", lange="Lange et al. 2021",
             filzinger="Filzinger et al. 2023", oklo_dh="Davis & Hamdan 2015", oklo_dd="Damour & Dyson 1996", espresso="Murphy et al. 2022",
             wilczynska="Wilczynska et al. 2020", hartchluba="Hart & Chluba 2018", planck_xxiv="Planck 2015 (int. XXIV)",
             avelino="Avelino et al. 2001", martins21="Martins 2021", cassini="Bertotti et al. 2003 (Cassini)",
             fienga="Fienga & Minazzoli 2024", genova="Genova et al. 2018", biskupek="Biskupek et al. 2021", voisin="Voisin et al. 2020",
             gw170817="Abbott et al. 2017 (GW170817)", gwtc3tgr="LVK 2025 (GWTC-3 tests)", delva="Delva et al. 2018", planck18="Planck 2018 VI",
             planck18x="Planck 2018 X", desi2="DESI DR2 2025", dovekie="Popovic et al. 2025 (DES)", sh0es="Riess et al. 2022 (SH0ES)",
             cchp="Freedman et al. 2025 (CCHP)", moresco="Moresco et al. 2016", jesus="Jesus et al. 2018", dahiya="Dahiya & Jain 2023",
             farooq="Farooq et al. 2017",
             bk18="BICEP/Keck 2021", act_dr6="Louis et al. 2025 (ACT DR6)", macro="MACRO 2002", superk="Takenaka et al. 2020 (Super-K)",
             mw_comb="LHC-TeV MW WG 2024", mz_pdg="PDG (Z mass)", atlas_mh="ATLAS 2023", alpha_mz="Erler & Freitas, PDG 2017",
             s2w="PDG 2024", gf_mulan="MuLan 2013", codata22="CODATA 2022", donofrio="D'Onofrio & Rummukainen 2016",
             kajantie="Kajantie et al. 1996", yu_tremaine="Yu & Tremaine 2002", marconi="Marconi et al. 2004", shankar="Shankar et al. 2009",
             davis_laor="Davis & Laor 2011", reynolds="Reynolds 2021", isi="Isi et al. 2021", gw250114="LVK 2025 (GW250114)",
             fein="Fein et al. 2019", pedalino="Pedalino et al. 2025", kovachy="Kovachy et al. 2015", xu="Xu et al. 2019",
             donadi="Donadi et al. 2021", figurato="Figurato et al. 2024", osswd="Oppenheim et al. 2023", gorton_green="Gorton & Green 2024",
             carr21="Carr et al. 2021", poh="Poh et al. 2015", hensen="Hensen et al. 2015", katrin="KATRIN 2025", nanograv="NANOGrav 2023")
assert set(SHORT) == set(CITATIONS), set(CITATIONS) ^ set(SHORT)
cite_names = SHORT
L = []
L.append("# GUID's predictions against existing data\n")
L.append("Workstream of *GUID v6: Our theory as simulated*. Written by `docs/simulation/predictions_vs_data.py` (deterministic; numpy, "
         "scipy, matplotlib; no network); every number is also in `predictions_vs_data.json`. Figures: " +
         ", ".join(f"`docs/simulation/figures/{f}`" for f in FIGS) + ".\n")
L.append(f"**{len(ROWS)} rows: {len(scored)} scored, {len(by_kind['conditional'])} conditional, {len(by_kind['consistency'])} consistency, "
         f"{len(by_kind['info'])} info. Scored: {n_ok} OK, {len(fails)} FAIL** (" + ", ".join(r["id"] for r in fails) + "), all shared with "
         f"LambdaCDM. Of the {len(scored)} scored rows, {len(specific)} test GUID-specific content (the information scalar and Bridge B) and "
         f"{len(scored) - len(specific)} test content GUID shares with general relativity, LambdaCDM or quantum mechanics. Conditional on the "
         f"Starobinsky/Higgs plateau potential: OK " + ", ".join(cond_ok) + "; FAIL " + ", ".join(cond_fail) + ". The consistency rows were "
         f"set from their own data and are never counted as successes. If the scored rows were independent, a correct theory would fail about "
         f"{0.05 * len(scored):.1f} of them by chance at 95%; but {CORREL}. Method checks of the script's own numerics: "
         f"{sum(m['ok'] for m in METHOD)} of {len(METHOD)}.\n")
L.append("Kinds: **scored** rows confront a prediction with a datum it was not set from: **OK** if GUID is consistent with the datum at 95% "
         "(|pull| < 1.96, or the GUID value inside the allowed region; rows at 90% CL say so), **FAIL** otherwise, also when general "
         "relativity, LambdaCDM or the Standard Model share it. **Conditional** rows apply the same test to a model Part I names but GUID does "
         "not derive. **Consistency** rows (CONS) hold by construction, because the prediction was set from the datum. **INFO** rows are "
         "superseded, derived, overlapping or without a usable uncertainty. The reason for every non-scored kind is given with the row.\n")
L.append("Every measured number was checked on " + DATE_VERIFIED + " against the arXiv text or abstract of its source; rows read only "
         "through secondary sources (a web search of the journal record, or a review that quotes the value) are listed in the citations.\n")
L.append("## Summary\n")
L.append(
    "- **Consistent and distinctive of GUID:** none yet has data that could tell GUID apart. The information scalar is consistent with every "
    f"datum: free fall bounds its coupling to |lambda| < {lam95:.1e} (95% CL; version 5.1's 2e-5 is the one-sigma-level value), and the drift "
    f"of alpha is consistent with zero. The data say **nothing about the sign** of the drift: the newest clock value is "
    f"(1.8 +- 2.5)e-19 /yr, and the joint fit of a slowly rolling scalar gives ({d_hat:.1e} +- {d_sig:.1e}) /yr, P(negative) = {P_neg:.2f}. "
    f"Part I's action (no potential, the scalar driven by the electrostatic energy of baryons) predicts a drift that is negative, "
    f"as GUID's forward statement says, but of size <~ 1e-23 /yr, four orders of magnitude below the clocks: the forward statement is derived "
    f"in that model and untestable. If the scalar instead rolled with DESI's dark energy (1 + w0 ~ 0.16), the clocks would force "
    f"|lambda| < {lam_desi:.0e}. Bridge B (the Diosi-Penrose rate) is consistent with every superposition made so far, by factors of "
    f"{min(e['margin'] for e in D6['experiments']):.0e} and more, and with the radiation bounds once the smearing length is R0 >= 4e-10 m.\n"
    "- **Consistent, not distinctive (shared with general relativity, quantum mechanics):** gamma = beta = 1, the Nordtvedt and strong-field "
    f"equivalence tests, the gravitational redshift, the speed and mass of gravitational waves (D2, 10 scored rows, chi2 = {chi2_d2:.1f} for "
    f"{len(d2_pulls)} Gaussian pulls); Soltan efficiencies inside the Kerr range and the area theorem (D5); Tsirelson's bound (D9).\n"
    "- **Consistent by construction, not counted (prediction set from the datum):** the smearing length of Bridge B, the black-hole window, "
    "monopoles and proton decay, alpha(M_Z) near 1/128, the electroweak crossover, the neutrinos and the gravitational-wave background as "
    "non-remnants, the Kerr bound on measured spins.\n"
    "- **In tension (all shared with LambdaCDM, and correlated):** DESI DR2's evolving dark energy against the de Sitter floor (2.8 to 4.2 "
    "sigma; 3.2 sigma with recalibrated DES supernovae) [D3.3]; the Hubble tension against SH0ES (4.9 sigma) while the TRGB value agrees "
    "[D3.4, D3.5]; DESI DR2 + CMB curvature at 2.1 sigma [D3.7]. Conditional on the plateau potential Part I names: ACT DR6 + lensing + BAO "
    "puts n_s = 0.974 +- 0.003, which the leading-order predictions reach only for N >= 63 (2.4 sigma at N = 60) [D4.3].\n"
    "- **No data yet:** gravitationally mediated entanglement (Bose-Marletto-Vedral), the LOCC test, the decoherence-diffusion trade-off at "
    "the needed sensitivity, Bridge B's decoherence, single-graviton clicks, primordial tensor modes, the Hawking glow at the light edge of "
    "the window, the return of information, proton decay (table below).\n")
L.append("## Master table\n")
L.append("| ID | Prediction / observable | Data source | Measured | GUID value | Pull / bound | Verdict | Kind | Class |")
L.append("|---|---|---|---|---|---|---|---|---|")
for r in ROWS:
    src = "; ".join(cite_names.get(k, k) for k in r["refs"]) or "-"
    kind = r["kind"] + (f": {r['kind_reason']}" if r["kind_reason"] else "")
    L.append(f"| {r['id']} | {md_escape(r['observable'])} | {md_escape(src)} | {md_escape(r['data'])} | {md_escape(r['guid'])} | "
             f"{md_escape(r['measure'])} | **{r['verdict']}** | {md_escape(kind)} | {md_escape(r['cls'])} |")
L.append("\nNotes on rows:\n")
L.extend(f"- {r['id']}: {md_escape(r['note'])}" for r in ROWS if r["note"])
L.append("")
L.append("## Method\n")
L.append(
    "**D1, the information scalar.** Part I's action gives the scalar phi a kinetic term normalised to the reduced "
    "Planck mass and a coupling lambda = d ln alpha / d phi. A body whose mass has electrostatic share f carries the scalar charge lambda f, "
    "so a pair falling towards the Earth differs by eta = 2 lambda^2 f_Earth (f_1 - f_2) (Eq. fifth); shares from the Coulomb term of the "
    f"semi-empirical mass formula as in checks.py [Q6] (Ti {f_Ti:.3e}, Pt {f_Pt:.3e}, Be {f_Be:.3e}, Earth {f_E:.3e}; the MICROSCOPE alloys "
    "TA6V and PtRh10 change the difference by about 3%). The bound on lambda is a profile likelihood with lambda^2 >= 0 (Delta chi^2 = 3.84). "
    "Two cosmological models: **Model A** is Part I's action as written, with no potential: the scalar obeys phi'' + 3 H phi' = "
    "-lambda f_b rho_b, driven only by the electrostatic energy of baryons (dark matter, a gravitational remnant, carries none). It is solved "
    f"in flat LambdaCDM (Planck 2018); the attractor gives phi'(today) = {U0:.3f} lambda f_b, so d ln alpha/dt = {U0 * H0_yr:.2e} lambda^2 "
    "f_b per year, negative for f_b > 0; f_b <= 1e-3 is used as a generous upper value (He-4 Coulomb energy alone gives 6e-5). This is "
    "BSBM-like evolution (Sandvik, Barrow and Magueijo) with a positive electrostatic share, which drives alpha down. **Model B** gives the "
    "scalar a linear potential and makes it the (thawing) dark energy: it is frozen by Hubble friction early and rolls late, with phi'^2 = "
    "3 Omega_phi (1 + w) exactly. For small slopes the history has a universal shape: Delta alpha/alpha(z) = -(alpha-dot/alpha today / H0) "
    f"G(z) with G(z_Oklo = {z_oklo:.3f}) = {G_shape(z_oklo):.3f}, G(1.15) = {G_shape(1.15):.3f}, G(6.3) = {G_shape(6.3):.3f}, G(>=1100) = "
    f"{G_inf_small:.3f} (for 1 + w0 = 0.16 the same numbers change by less than {abs(G_inf_desi / G_inf_small - 1) * 100:.0f}%). Every alpha "
    "datum is then a measurement of the present drift; the joint fit is their weighted mean. In Model B the drift and lambda are independent "
    "parameters linked only by the field speed, drift = lambda H0 phi'_0, which the dark energy's 1 + w0 fixes; the allowed region is shown in "
    "`data_alpha_scalar.pdf`. Oklo's 1.8 Gyr is the elapsed time implied by Damour and Dyson's quoted bounds and rates. The clock value of "
    "Filzinger et al. 2023 includes the data of Lange et al. 2021, so only the newer value enters the fit.\n")
L.append(
    "**D2.** Pulls against general relativity's values. The LLR errors of Biskupek et al. are read as 1 sigma (their paper does not say; "
    "this is the stricter reading). The pulsar SEP bound is converted from 95% to 1 sigma. Of overlapping pairs one row is scored: Cassini "
    "(D2.1) for gamma, the ephemeris combination (D2.3) for beta. The combined chi2 is indicative only, since the lunar rows come from one fit.\n")
L.append(
    "**D3.** GUID's late universe is flat LambdaCDM with a de Sitter floor. The transition redshift follows from Omega_m. Its published "
    "determinations (cosmic chronometers; H(z) compilations, whose weighted mean depends mainly on the H0 prior; SNe Ia + H(z), whose three "
    "parametrisations are merged with their half-range as a systematic) disagree with each other, so D3.1 is reported as inconclusive and not "
    "scored (rows D3.1a to D3.1d give the individual pulls). Of the two flatness data, the newer (DESI DR2 with the CMB, D3.7) is scored. "
    "The DESI significances are the collaboration's (Delta chi^2 for two extra parameters, converted to Gaussian "
    "sigma); the check scores the least significant combination. H_inf is derived (H_inf^2 = H0^2 - (100 km/s/Mpc)^2 omega_m) and is reported, "
    "not scored: it exists only if w = -1.\n")
L.append(
    "**D4.** Leading-order plateau predictions n_s = 1 - 2/N, r = 12/N^2 for Starobinsky and Higgs inflation, N = 50 to 60. These rows are "
    "conditional on that potential, which Part I names but GUID does not derive. The n_s datum is ACT DR6 + Planck + lensing + DESI DR1 BAO "
    "(it includes the Planck data, so Planck alone and P-ACT are reported). A prediction band passes when some N in [50, 60] is within 95%; "
    "the pull quoted is the one at the best N.\n")
L.append(
    "**D5.** Novikov-Thorne efficiency 1 - E_isco from Bardeen, Press and Teukolsky, signed spin (retrograde a < 0): 3.8% (a = -1), 5.7% (a = 0), "
    "42.3% (a -> 1). The Soltan efficiencies are read on that curve to give the typical spin. The spin tables are entered as 90% ranges "
    "(lower limits as [limit, 1]).\n")
L.append(
    "**D6.** Bridge B's rate for each experiment is computed two ways, and the larger is used: Part I's G M^2/(hbar R) and the full "
    "Diosi-Penrose self-energy difference E_Delta = (G/2) int int (rho_1 - rho_2)(rho_1' - rho_2')/|x - x'| for the actual separation, a "
    "uniform sphere for the bulk plus each nucleus smeared as a Gaussian of width R0 = 0.54e-10 m (the smallest allowed; larger R0 lowers "
    "the rate). Single atoms are their nucleus smeared over R0. The closed forms are checked against Fourier quadrature. An experiment is "
    "consistent if the predicted decoherence during its observed coherence time is below 0.1. Particle radii of the molecules are estimates "
    "from mass and density (1300 kg/m^3 for the porphyrins; 8 nm diameter stated for the Na clusters); they enter linearly and are far from "
    "mattering.\n")
L.append(
    "**D8.** Tree-level masses from alpha-hat(M_Z) = 1/127.950, sin^2 theta-hat = 0.23129 and v = (sqrt2 G_F)^(-1/2) = " + f"{v_H:.2f}" +
    " GeV, Part I's route; two other standard tree-level routes show the scheme spread. Part I's claim, agreement within half a per cent, "
    "holds only in that route, so these rows are reported as tree-level Standard Model values (INFO).\n")
L.append("## D1 in numbers\n")
L.append(f"| quantity | value |\n|---|---|\n| 95% CL bound on lambda (MICROSCOPE + Eot-Wash) | {lam95:.2e} |\n| same, MICROSCOPE alone | "
         f"{lam95_mic:.2e} |\n| version 5.1's bound (\\|eta\\| < 2.7e-15) | {lam_paper:.2e} |\n| Model A drift coefficient | {U0 * H0_yr:.2e} lambda^2 f_b /yr |\n"
         f"| Model A drift at the largest lambda, f_b = 1e-3 | {dA_max:.1e} /yr |\n| Model B joint drift | ({d_hat:.2e} +- {d_sig:.2e}) /yr |\n"
         f"| P(drift < 0) | {P_neg:.3f} |\n| lambda bound if the scalar is DESI-like thawing dark energy (1 + w0 = 0.162) | {lam_desi:.1e} |\n")
L.append("Implied present drift per datum in Model B (1 sigma):\n")
L.append("| datum | z | G(z) | implied drift [1/yr] |\n|---|---|---|---|")
for lab, ref, z, d, s in implied:
    L.append(f"| {lab} | {z:.3g} | {G_shape(z) if z > 0 else 0:.3f} | {d:+.2e} +- {s:.1e} |")
L.append("\n## D6 in numbers\n")
L.append("| experiment | mass [kg] | separation [m] | coherence [s] | Bridge B rate [1/s] | decoherence in the run | margin |\n|---|---|---|---|---|---|---|")
for e in D6["experiments"]:
    L.append(f"| {e['label']} | {e['mass_kg']:.2e} | {e['separation_m']:.2e} | {e['coherence_s']:.3g} | {max(e['rate_paper'], e['rate_full']):.1e} | "
             f"{e['decoherence_in_run']:.1e} | {e['margin']:.0e} |")
L.append(f"\nThe BMV microsphere (1e-14 kg, R = {R_bmv * 1e6:.2f} um) decoheres in {tau_bmv_paper * 1e3:.1f} ms by Part I's formula and "
         f"{tau_bmv_full * 1e3:.1f} ms by the full Diosi-Penrose energy at 250 um separation. **The first experiment to see Bridge B** is a "
         "centre-of-mass superposition, separated by more than the particle's size, of a silica particle of " +
         ", ".join(f"{v['silica']:.0e} kg held {k}" for k, v in first.items()) +
         f"; the heaviest superposed mass so far is {heaviest:.1e} kg, so the step is {math.log10(first['100 s']['silica'] / heaviest):.0f} to "
         f"{math.log10(first['0.01 s']['silica'] / heaviest):.0f} orders of magnitude in mass, depending on how long the superposition is held. Until then "
         "the absence of any anomalous decoherence is consistent with Bridge B and does not test it.\n")
L.append("## No data yet\n")
L.append("| prediction | GUID | status |\n|---|---|---|")
for a, b, cc in NO_DATA:
    L.append(f"| {md_escape(a)} | {md_escape(b)} | {md_escape(cc)} |")
L.append("\n## Covered by other workstreams (not redone here)\n")
L.append("| topic | files | result |\n|---|---|---|")
for a, b, cc in COVERED:
    L.append(f"| {md_escape(a)} | `{b}` | {md_escape(cc)} |")
L.append("\n## Corrections made to version 5.1 (applied in Part I of the v6 paper)\n")
L.append(
    f"1. Version 5.1, Section 4.1, Eq. (lambdabound): |lambda| < 2e-5 is the one-sigma-level value (|eta| < 2.7e-15); the 95% CL profile-likelihood bound "
    f"from MICROSCOPE and Eot-Wash is |lambda| < {lam95:.1e}.\n"
    "2. Section 11.7 and the predictions table: the newest clock bound is (1.8 +- 2.5)e-19 /yr (Filzinger et al. 2023, which includes the "
    "data of Lange et al. 2021).\n"
    "3. Section 11.7: with Part I's action (no potential) the drift is negative, -C lambda^2 f_b with C ~ 1e-11 /yr, so the forward "
    "statement 'zero or negative' is derived there, but it is below 1e-23 /yr; a measurable drift needs a potential, and then the sign is "
    "not predicted.\n"
    "4. Section 5.4 (Bridge B): 'smeared over at least about 1e-10 m' should read 'at least 4e-10 m' (Figurato et al. 2024 summarise the "
    "current bounds so; Donadi et al.'s own 95% bound is 0.54e-10 m).\n"
    "5. Section 11.4: 'Starobinsky's R^2 inflation, which fits the scalar data' holds for Planck 2018; ACT DR6 with lensing and BAO "
    "(n_s = 0.974 +- 0.003) needs N >= 63 at leading order.\n"
    "6. Section 11.6 (3): DESI DR2 bounds sum m_nu < 0.064 eV, so the neutrinos are below 0.6% of the dark matter.\n"
    "7. Section 11.5: the DESI DR2 range 2.8 to 4.2 sigma is correct; the DES supernova recalibration (Popovic et al. 2025/2026) lowers its "
    "end to 3.2 sigma. The Hubble tension (4.9 sigma against SH0ES) and the DESI curvature (2.1 sigma) are inherited LambdaCDM tensions and "
    "could be named alongside.\n"
    "8. Add the graviton-mass bound m_g <= 2.42e-23 eV/c^2 (GWTC-3 tests, final version) next to the speed of gravity.\n")
L.append("## Numbers left out\n")
L.append(
    "- Tristram et al. (r < 0.032) and the Planck 2018 curvature with BAO (0.0007 +- 0.0019) were not re-verified in this session; the "
    "BICEP/Keck bound and Planck X's 0.4% flatness statement are used instead.\n"
    "- The MICROSCOPE alloy compositions, the Sun's composition for the LLR scalar term and the nucleon electromagnetic self-energy are model "
    "inputs, not data; they are stated as such and do not change any verdict.\n"
    "- An individual area value for GW250114 and a significance in sigma (press releases quote 99.999%) were not found in the "
    "collaboration's abstract or HTML; only the abstract's statement is used.\n"
    "- Bild et al. 2023 (a 16 microgram mechanical cat state) is not a centre-of-mass superposition, so a Diosi-Penrose rate needs its mode "
    "shape; it is left out.\n")
L.append("## Citations (all verified " + DATE_VERIFIED + ")\n")
for k, v in CITATIONS.items():
    L.append(f"- **{k}**: {v['ref']}. Read: {v['read']}. Value: {v['value']}.")
L.append("")
(RESULTS / "predictions_vs_data.md").write_text("\n".join(L))

print(f"\nWrote {RESULTS / 'predictions_vs_data.json'}, {RESULTS / 'predictions_vs_data.md'} and {len(FIGS)} figures.")
if not m_ok:
    print("METHOD CHECK FAILED")
print(f"\n{n_ok} of {len(scored)} scored confrontations passed ({len(fails)} FAIL; conditional: {len(cond_ok)} OK, {len(cond_fail)} FAIL; "
      f"{len(by_kind['consistency'])} consistency rows not counted; {len(by_kind['info'])} info)")
print(f"{n_ok} of {len(scored)} checks passed")
sys.exit(0 if (n_ok == len(scored) and m_ok) else 1)
