"""GUID v6, workstream SM6 of docs/simulation/sm_preregistration.md: hadrons as binary trees of dualities (Hypothesis H8) against
hadron spectroscopy, with tetraquarks and pentaquarks as the test bed.

Run:  python3 docs/simulation/exotic_hadrons.py
Needs numpy, scipy, matplotlib. Deterministic: fixed seeds, BLAS on one thread, no clock in any output except the runtime field, no
network, no machine name; the PDF figures are written without a creation date. Runs in about a minute on one core, memory under 200 MB.
Writes docs/simulation/results/exotic_hadrons.{json,md} and docs/simulation/figures/exotic_{fit,spectrum,levels,thresholds,alpha}.pdf.

Every measured number below was read on 2026-10-31 in its source: the arXiv abstract or full text, or, for current Particle Data Group
(PDG) values, the PDG listing as returned by a web search (the PDG server itself was not reachable from this environment). CITATIONS
lists for each source what was read and the value. Values that could not be re-read are marked "unverified"; none of them enters a
verdict (the threshold test is repeated with every unverified mass perturbed, test B4).

Checks print OK or FAIL and the last line counts them; the exit code is 0 only if all checks pass. The checks test the script's own
numerics (colour and spin algebra against closed forms, the reproduction of Karliner and Rosner's published numbers, the fit's
convergence, analytic null distributions against Monte Carlo). Every confrontation with data is a result, never a check.

HYPOTHESIS H8 (fixed in sm_preregistration.md, SM6, before this script existed): every hadron is a binary tree of two colour-conjugate
halves, each internal node a bound duality: meson (q)(qbar); baryon (q)[qq]; tetraquark [qq][qbar qbar] (compact) or (q qbar)(q qbar)
(molecular); pentaquark [qq][qq]qbar or (qqq)(q qbar). Predictions (a) compact exotics, (b) threshold proximity of molecular exotics,
(c) partners.

THE MODEL, fixed before any exotic state was computed (the established colour-spin model of De Rujula, Georgi and Glashow 1975 in the
form of Karliner and Rosner 2014, 2017, called KR below):
  M = sum_i m_i + sum_{i<j} B_ij + sum_{i<j} (-C_ij) <lambda_i.lambda_j sigma_i.sigma_j>
  * colour: lambda_i.lambda_j = sum_a lambda^a_i lambda^a_j (Gell-Mann matrices; -lambda^a* for an antiquark); spin: Pauli matrices.
  * the state is the H8 tree: every internal node except the root couples two colour triplets to the conjugate triplet (Casimir 4/3),
    the root couples to a singlet; every internal node carries a spin; within a fixed colour tree the node spins that give the same
    total J are mixed and the Hamiltonian is diagonalised (for neutral hidden-flavour states the eigenvectors are sorted by C).
    A diquark of two identical s, c or b quarks has spin 1 (Pauli); a light [qq] pair has isospin I = spin.
  * effective masses m_i: meson set m^m_f for mesons, baryon set m^b_f for baryons and, as in KR 2017, for every constituent of a
    compact multiquark.
  * hyperfine couplings from mesons (quark-antiquark pairs) and baryons (quark-quark pairs):
      meson sigma.sigma coefficient v^m_ij = 2 b k_ij / (m^m_i m^m_j), baryon coefficient v^b_ij = a k_ij / (m^b_i m^b_j);
      C_ij = (3/16) v^m_ij for a quark-antiquark pair and (3/8) v^b_ij for a quark-quark pair, so that the colour factor -16/3 of a
      meson and -8/3 of a baryon pair return v^m and v^b. k_ij = k_s for a (c,s) or (b,s) pair, 1 otherwise (KR's a_cs = a_bs).
      Heavy-heavy pairs: v^m_ccbar = [M(J/psi) - M(eta_c)]/4, v^m_bbbar = [M(Upsilon) - M(eta_b)]/4, v^m_bcbar interpolated as
      |psi(0)|^2 ~ (reduced mass)^p between them (KR 2014, Sec. VII); a heavy-heavy quark-quark pair has the same C (KR: a_QQ = a_QQbar/2).
  * binding terms (KR): B_ij = B^(1)_ij <lambda_i.lambda_j>/(-16/3), with the colour-singlet values B^(1) for (c,sbar), (b,sbar),
    (c,cbar), (b,bbar), (b,cbar) fitted to mesons; so B(QQ) = B(QQbar)/2 in a baryon or diquark, exactly KR's rule, and a pair in
    different halves of a tetraquark or pentaquark gets B^(1)/4 (KR's stated assumption that the potential factorises into a colour
    factor and a common spatial factor, applied to every pair). No binding term for pairs with a u or d quark.
  Variants, fixed at the same time, reported for every state and never used for a verdict:
    P-in: as the primary model, but binding only between constituents of the same half (no pair across the root of a multiquark).
    J:    universal effective masses for all hadrons plus a constant S per string junction (KR 2017 Sec. VI; Karliner, Nussinov and
          Rosner 2017): 0 for a meson, 1 for a baryon, 2 for a tetraquark, 3 for a pentaquark (= the internal nodes below the root).
  FIT: the parameters are fitted by unweighted least squares to 42 conventional ground-state hadrons (FIT_DATA) and to nothing else.
  The doubly charmed baryon Xi_cc++ is held out: it tests KR's rule B(cc) = B(ccbar)/2 that every doubly heavy prediction uses.
  The model uncertainty is sigma_model = sqrt(RSS/(N - p)) of that fit; the uncertainty of a prediction adds the parameter
  covariance sigma_model^2 (J^T J)^-1 propagated to the state. Both are fixed before any exotic state is compared.
  HOSTING CHECK: with KR's published parameters the implementation reproduces KR's tables and their T_cc, T_bb, T_bc and Xi_cc masses.

SCORING (fixed beforehand): pull z = (M_model - M_data) / sqrt(sigma_pred^2 + sigma_data^2), with the data error on the side of the
model; holds if |z| < 2, refuted if |z| >= 2 (as in predictions_vs_data.py, 95%); states not yet observed are live, with the binding
relative to the lowest two-hadron threshold allowed in an S wave. Assignments (pre-registered):
  T_cc+       [cc]_1[ubar dbar]_0, J^P = 1+                      against LHCb T_cc+(3875)
  T_bb-       [bb]_1[ubar dbar]_0, 1+                            live; lattice QCD for comparison
  T_bc        [bc]_0[ubar dbar]_0, 0+ and [bc]_1[ubar dbar]_0, 1+   live; lattice QCD for comparison
  X0(2900)    [ud]_0[cbar sbar]_0, 0+                            against LHCb X0(2900) (X1(2900) is 1-, a P wave: outside the model)
  T_csbar     lowest 0+ of [cq][sbar qbar]                       against LHCb T_csbar0(2900)
  cc cbar cbar  [cc]_1[cbar cbar]_1: 0++, 1+-, 2++               against LHCb X(6900) with the 2++ (the most favourable S-wave
                                                                 assignment); CMS and ATLAS structures shown, not scored
  P_c         lowest level of ([cq][qq]) cbar, I = 1/2           against P_c(4312); P_c(4440), P_c(4457) against the nearest level
                                                                 (an assignment by proximity, flagged)
  P_psis      lowest I = 0, J = 1/2 level of udsc cbar           against P_psis(4338); P_cs(4459) against the nearest level (flagged)
  P_cc        lowest ([cc]_1[ud]_0) qbar                         live
  compact X(3872) / Z_c(3900): [cq][cbar qbar] 1++ and 1+-      reported for the partner test (c), not scored in (a)
THRESHOLD TEST (b), fixed beforehand: a catalogue of established exotic hadrons (CATALOGUE, >= 5 sigma states with a measured mass),
each with the nearest S-wave two-hadron threshold allowed by flavour, J, P and (for neutral hidden-flavour states) C, built from the
hadrons of THRESH_HADRONS (all with width below 60 MeV). Null: each mass uniform in [M - W, M + W], W = 150 MeV (300 MeV as a
variant); per-state p_i = P(distance <= observed) computed exactly; combined by Fisher's method.
PARTNERS (c): the model's isospin and spin partners of the compact states against the searches in PARTNER_SEARCHES.

  [E] the colour-spin engine: colour and spin factors against closed forms
  [H] hosting check: KR 2014 Tables I to VII and IX, KR 2017 Tables I to III; KNR 2017 eq. (8)
  [F] the fit to conventional hadrons, sigma_model, leave-one-out, Xi_cc++ held out
  [A] compact exotics: predictions and pulls (results)
  [B] threshold proximity (results; analytic null checked by Monte Carlo)
  [C] partners (results)
  [I] Hypothesis H9, the minting in hadrons (SM7): I1 no open flavour, I2 hidden-bottom pentaquarks, I3 the general rule, I4 the
      alpha M / 2 splitting rule (results; checks I0a-I0e test the block's own numerics)
"""

import os

for _v in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"   # deterministic BLAS

import itertools  # noqa: E402
import json  # noqa: E402
import math  # noqa: E402
import sys  # noqa: E402
import time  # noqa: E402
from fractions import Fraction  # noqa: E402
from pathlib import Path  # noqa: E402

import numpy as np  # noqa: E402
from scipy import optimize, stats  # noqa: E402

T_START = time.perf_counter()
HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
FIGURES = HERE / "figures"
SEED = 20210901                     # fixed; used only by the Monte Carlo checks and the robustness perturbations of test B
N_MC = 20000                        # Monte Carlo placements per state for the check of the analytic null
N_PERTURB = 200                     # perturbed threshold tables for test B4

results = []
check_log = []


def check(label, got, want, atol):
    got, want = float(got), float(want)
    ok = abs(got - want) <= atol
    print(f"{'OK  ' if ok else 'FAIL'} {label}: {got:.6g} (expected {want:.6g} +- {atol:g})")
    results.append(ok)
    check_log.append({"label": label, "ok": ok, "got": got, "want": want, "atol": atol})


def check_true(label, cond):
    print(f"{'OK  ' if cond else 'FAIL'} {label}")
    results.append(bool(cond))
    check_log.append({"label": label, "ok": bool(cond)})


# =====================================================================================================================================
# Sources. Each entry: reference, what was read, the values used.
# =====================================================================================================================================
CITATIONS = {
    "DGG1975": {"ref": "A. De Rujula, H. Georgi, S. L. Glashow, Phys. Rev. D 12, 147 (1975)", "read": "the reference as given in "
                "KR2014 ref. [23]; cited for the colour-spin (chromomagnetic) hyperfine interaction; the paper itself not re-read "
                "(no arXiv version)", "values": "none used"},
    "KR2014": {"ref": "M. Karliner, J. L. Rosner, Phys. Rev. D 90, 094007 (2014), arXiv:1408.5877",
               "read": "full text: Tables I, II, IV, VI, VII, IX; eqs. (1)-(20)",
               "values": "m^b_q=363, m^b_s=538, a/(m^b_q)^2=50, m^m_q=310, m^m_s=483, b/(m^m_q)^2=80, m^m_c=1663.3, m^b_c=1710.5, "
                         "m^m_b=5003.8, m^b_b=5043.5, B(cs bar)=-69.9, B(cs)=-35.0, B(bs bar)=-83.6, 6a_cs/(m_s m_c)=70.7, "
                         "a_bs=(70.7/43.0)a, Mbar(cc bar)=3068.6, M(J/psi)-M(eta_c)=113.2, Mbar(bb bar)=9444.7, "
                         "M(Upsilon)-M(eta_b)=62.3, M(B_c)=6274.5, B_c* - B_c = 68.0, p=1.46; hadron masses quoted in the tables "
                         "(PDG 2012 and KR's b-baryon averages); predictions Xi_cc=3627+-12, Xi_cc*=3690, Xi_bb=10162, Xi_bb*=10184"},
    "KR2017": {"ref": "M. Karliner, J. L. Rosner, Phys. Rev. Lett. 119, 202001 (2017), arXiv:1707.07666",
               "read": "full text: Tables I-III, Secs. II, III, VI",
               "values": "T(bb ubar dbar) 1+ = 10389.4+-12 (215 below BB* at 10604; 170 below B- B0bar gamma at 10559); "
                         "T(cc ubar dbar) 1+ = 3882.2+-12 (7 above D0 D*+ at 3875); T(bc ubar dbar) 0+ = 7133.7+-13 (11 below "
                         "B0bar D0 at 7144.5); M(D0)+M(D*+)=3875.09+-0.07; string-junction term S=165 MeV"},
    "KNR2017": {"ref": "M. Karliner, S. Nussinov, J. L. Rosner, Phys. Rev. D 95, 034011 (2017), arXiv:1611.00348",
                "read": "Sec. II, eqs. (1)-(8)", "values": "S=165.1, m_c=1655.6, m_b=4988.6, M(cc,3bar)=3204.1, B=-388.3, "
                "Delta M_3=79.3, M(cc cbar cbar, 0++) = 6191.5 (abstract 6192+-25); J/psi J/psi threshold 6193.8"},
    "LHCb_Tcc_NP": {"ref": "LHCb, Nature Phys. (2022), doi:10.1038/s41567-022-01614-y, arXiv:2109.01038", "read": "abstract",
                    "values": "narrow state just below the D*+ D0 threshold, mass about 3875 MeV"},
    "LHCb_Tcc_NC": {"ref": "LHCb, Nature Commun. 13, 3351 (2022), arXiv:2109.01056", "read": "full text, eqs. (1), (4), (5), (12), "
                    "Table 2, Fig. 4 and conclusions", "values": "delta m_U = -359+-40 (+9 -6) keV; pole delta m = -360+-40 (+4 -0) "
                    "keV, Gamma_pole = 48+-2 (+0 -14) keV; delta m_BW = -273+-61 keV; J^P = 1+ favoured; no signal in D+D0pi+ "
                    "(3.9-4.0 GeV) or D+D+ (to 3.87 GeV): isovector interpretation disfavoured"},
    "LHCb_X6900": {"ref": "LHCb, Sci. Bull. 65, 1983 (2020), arXiv:2006.16957", "read": "full text, Sec. 5 and conclusions",
                   "values": "model I: m = 6905+-11+-7, Gamma = 80+-19+-33; model II: m = 6886+-11+-11, Gamma = 168+-33+-69; broad "
                             "structure 6.2-6.8 GeV"},
    "CMS_diJpsi": {"ref": "CMS, Phys. Rev. Lett. 132, 111901 (2024), arXiv:2306.07164", "read": "abstract and Table I",
                   "values": "no interference: 6552+-10+-12 (Gamma 124), 6927+-9+-4 (122), 7287+20-18+-5 (95); interference: "
                             "6638+43+16-38-31, 6847+44+48-28-20, 7134+48+41-25-15"},
    "ATLAS_diJpsi": {"ref": "ATLAS, Phys. Rev. Lett. 131, 151902 (2023), arXiv:2304.08962", "read": "Table 2",
                     "values": "model A: 6.41+-0.08(+0.08-0.03), 6.63+-0.05(+0.08-0.01), 6.86+-0.03(+0.01-0.02) GeV; model B: "
                               "6.65+-0.02(+0.03-0.02), 6.91+-0.01+-0.01 GeV"},
    "LHCb_X2900": {"ref": "LHCb, Phys. Rev. D 102, 112003 (2020), arXiv:2009.00026 (and PRL 125, 242001, arXiv:2009.00025)",
                   "read": "full text, Table 4 and conclusions", "values": "X0(2900): spin 0, M = 2866+-7+-2, Gamma = 57+-12+-4; "
                   "X1(2900): spin 1, M = 2904+-5+-1, Gamma = 110+-11+-4; D-K+ channel, minimal content cbar d sbar u"},
    "LHCb_Tcsbar": {"ref": "LHCb, Phys. Rev. Lett. 131, 041902 (2023), arXiv:2212.02716", "read": "abstract",
                    "values": "M = 2908+-11+-20, Gamma = 136+-23+-11, J^P = 0+, isospin triplet (D_s+ pi+ and D_s+ pi-)"},
    "LHCb_Pc2019": {"ref": "LHCb, Phys. Rev. Lett. 122, 222001 (2019), arXiv:1904.03947", "read": "full text, Table 1 and text",
                    "values": "P_c(4312): 4311.9+-0.7(+6.8-0.6), Gamma 9.8+-2.7(+3.7-4.5); P_c(4440): 4440.3+-1.3(+4.1-4.7), "
                              "Gamma 20.6+-4.9(+8.7-10.1); P_c(4457): 4457.3+-0.6(+4.1-1.7), Gamma 6.4+-2.0(+5.7-1.9); 7.3 sigma "
                              "and 5.4 sigma; J^P not determined"},
    "LHCb_Pcs4459": {"ref": "LHCb, Sci. Bull. 66, 1278 (2021), arXiv:2012.10380", "read": "abstract",
                     "values": "evidence: M = 4458.8+-2.9(+4.7-1.1), Gamma = 17.3+-6.5(+8.0-5.7)"},
    "LHCb_Ppsis4338": {"ref": "LHCb, Phys. Rev. Lett. 131, 031901 (2023), arXiv:2210.10346", "read": "abstract",
                       "values": "M = 4338.2+-0.7+-0.4, Gamma = 7.0+-1.2+-1.3, J = 1/2, negative parity preferred"},
    "MPR2015": {"ref": "L. Maiani, A. D. Polosa, V. Riquer, Phys. Lett. B 749, 289 (2015), arXiv:1507.04980", "read": "full text",
                "values": "P = epsilon cbar [cq]_{s=0,1} [q'q'']_{s=0,1}, colour-3bar units; S-wave multiplicities "
                          "J=1/2 (2), 3/2 (1) for s(q'q'')=0 and 1/2 (3), 3/2 (3), 5/2 (1) for s=1"},
    "MPPR2005": {"ref": "L. Maiani, F. Piccinini, A. D. Polosa, V. Riquer, Phys. Rev. D 71, 014028 (2005), hep-ph/0412098",
                 "read": "abstract", "values": "X(3872) as [cq][cbar qbar] with two neutral components and charged partners X+-"},
    "BaBar_Xminus": {"ref": "BaBar, Phys. Rev. D 71, 031501 (2005), hep-ex/0412051", "read": "full text",
                     "values": "B(B0 -> X- K+, X- -> J/psi pi- pi0) < 5.4e-6, B(B- -> X- K0bar) < 22e-6 (90% CL); isovector X "
                               "predicts 75+-25 events, 2.56e-5; null favoured by likelihood ratio 1.1e4"},
    "Belle_X3872": {"ref": "Belle, Phys. Rev. D 84, 052004 (2011), arXiv:1107.0163", "read": "abstract",
                    "values": "charged-partner limits well below the isospin-triplet expectation; M = 3871.84+-0.27+-0.19"},
    "Francis2017": {"ref": "A. Francis, R. J. Hudspith, R. Lewis, K. Maltman, Phys. Rev. Lett. 118, 142001 (2017), arXiv:1607.05214",
                    "read": "abstract", "values": "ud bbar bbar 1+ 189(10) MeV below threshold"},
    "Leskovec2019": {"ref": "L. Leskovec, S. Meinel, M. Pflaumer, M. Wagner, Phys. Rev. D 100, 014503 (2019), arXiv:1904.04197",
                     "read": "abstract", "values": "binding -128+-24+-10 MeV, mass 10476+-24+-10 MeV"},
    "Aoki2023": {"ref": "T. Aoki, S. Aoki, T. Inoue, arXiv:2306.03565 (2023)", "read": "abstract",
                 "values": "83(10) MeV below B B* (coupled channel), +-20 MeV systematic; single channel 155(17)"},
    "Hudspith2023": {"ref": "R. J. Hudspith, D. Mohler, Phys. Rev. D 107, 114510 (2023), arXiv:2303.17295", "read": "abstract",
                     "values": "112.0(13.2) MeV below B B*"},
    "Tripathy2025": {"ref": "B. S. Tripathy, N. Mathur, M. Padmanath, Phys. Rev. D 111, 114504 (2025), arXiv:2503.09760",
                     "read": "abstract",
                     "values": "Delta E = -116 (+30 -36) MeV relative to B B*"},
    "Francis2019": {"ref": "A. Francis, R. J. Hudspith, R. Lewis, K. Maltman, Phys. Rev. D 99, 054505 (2019), arXiv:1810.10550",
                    "read": "abstract", "values": "ud cbar bbar 0(1+) 15 to 61 MeV below Dbar B*"},
    "Padmanath2024": {"ref": "M. Padmanath, A. Radhakrishnan, N. Mathur, Phys. Rev. Lett. 132, 201902 (2024), arXiv:2307.14128",
                      "read": "abstract", "values": "1+: -43(+6-7)(+14-24) MeV with respect to D Bbar*"},
    "Alexandrou2024": {"ref": "C. Alexandrou et al., Phys. Rev. Lett. 132, 151902 (2024), arXiv:2312.02925", "read": "abstract",
                       "values": "shallow bound or virtual states a few MeV or less below the B(*) Dbar thresholds"},
    "LHCb_X3872_ls": {"ref": "LHCb, Phys. Rev. D 102, 092005 (2020), arXiv:2005.13419", "read": "abstract",
                      "values": "m(chi_c1(3872)) - m(psi(2S)) = 185.598+-0.067+-0.068; Gamma_BW = 1.39+-0.24+-0.10"},
    "LHCb_X3872_JPC": {"ref": "LHCb, Phys. Rev. Lett. 110, 222001 (2013), arXiv:1302.6269", "read": "abstract",
                       "values": "J^PC = 1++"},
    "BESIII_Zc3900": {"ref": "BESIII, Phys. Rev. Lett. 110, 252001 (2013), arXiv:1303.5949", "read": "abstract",
                      "values": "3899.0+-3.6+-4.9, Gamma 46+-10+-20"},
    "BESIII_Zc3900_JP": {"ref": "BESIII, Phys. Rev. Lett. 119, 072001 (2017), arXiv:1706.04100", "read": "abstract",
                         "values": "J^P = 1+"},
    "BESIII_Zc4020": {"ref": "BESIII, Phys. Rev. Lett. 111, 242001 (2013), arXiv:1309.1896", "read": "abstract",
                      "values": "4022.9+-0.8+-2.7, Gamma 7.9+-2.7+-2.6"},
    "LHCb_Z4430": {"ref": "LHCb, Phys. Rev. Lett. 112, 222002 (2014), arXiv:1404.1903", "read": "full text",
                   "values": "4475+-7(+15-25), Gamma 172+-13(+37-34), J^P = 1+"},
    "BESIII_Zcs3985": {"ref": "BESIII, Phys. Rev. Lett. 126, 102001 (2021), arXiv:2011.07855", "read": "abstract",
                       "values": "pole 3982.5(+1.8-2.6)+-2.1, Gamma 12.8(+5.3-4.4)+-3.0; 5.3 sigma"},
    "LHCb_JpsiK": {"ref": "LHCb, Phys. Rev. Lett. 127, 082001 (2021), arXiv:2103.01803", "read": "abstract and Table 1",
                   "values": "Zcs(4000) 1+ 4003+-6(+4-14), Gamma 131+-15+-26; Zcs(4220) 1+ or 1- 4216+-24(+43-30), Gamma 233; "
                             "X(4140) 1+ 4118+-11(+19-36), Gamma 162; X(4274) 1+ 4294+-4(+3-6), Gamma 53; X(4500) 0+ 4474+-3+-3, "
                             "Gamma 77; X(4700) 0+ 4694+-4(+16-3), Gamma 87; X(4685) 1+ 4684+-7(+13-16), Gamma 126; X(4630) 1- "
                             "4626+-16(+18-110), Gamma 174; all above 5 sigma"},
    "LHCb_JpsiPhi2016": {"ref": "LHCb, Phys. Rev. Lett. 118, 022003 (2017), arXiv:1606.07895", "read": "full text, Table 2",
                         "values": "X(4140) and X(4274) J^PC = 1++, X(4500) and X(4700) 0++"},
    "LHCb_X3960": {"ref": "LHCb, Phys. Rev. Lett. 131, 071901 (2023), arXiv:2210.15153", "read": "abstract",
                   "values": "3956+-5+-10, Gamma 43+-13+-8, J^PC = 0++, > 12 sigma"},
    "BESIII_Y4230": {"ref": "BESIII, Phys. Rev. Lett. 118, 092001 (2017), arXiv:1611.01317", "read": "abstract",
                     "values": "4222.0+-3.1+-1.4, Gamma 44.1+-4.3+-2.0 (e+e- -> pi+pi- J/psi, J^PC = 1--)"},
    "Belle_Zb": {"ref": "Belle, Phys. Rev. Lett. 108, 122001 (2012), arXiv:1110.2251", "read": "abstract",
                 "values": "10607.2+-2.0, Gamma 18.4+-2.4; 10652.2+-1.5, Gamma 11.5+-2.2"},
    "LHCb_Xicc": {"ref": "LHCb, JHEP 02 (2020) 049, arXiv:1911.08594", "read": "abstract",
                  "values": "M(Xi_cc++) = 3621.55+-0.23+-0.30"},
    "LHCb_Xibprime": {"ref": "LHCb, Phys. Rev. Lett. 114, 062004 (2015), arXiv:1411.4849", "read": "abstract",
                      "values": "m(Xi_b'-) - m(Xi_b0) - m(pi-) = 3.653+-0.018+-0.006"},
    "PDG2024": {"ref": "S. Navas et al. (Particle Data Group), Phys. Rev. D 110, 030001 (2024) and 2025 update",
                "read": "listings returned by web search (pdgLive, the 2024/2025 listings): D0 1864.84, D+ 1869.66, D*0 2006.85, "
                        "D*+ 2010.26, D_s 1968.35, D_s* 2112.2, D2*(2460)0 2461.1, D_s1(2536) 2535.11, eta_c 2984.1, J/psi "
                        "3096.900, chi_c0 3414.71, chi_c1 3510.67, h_c 3525.37, chi_c2 3556.17, eta_c(2S) 3637.7, psi(2S) "
                        "3686.097, eta_b 9398.7, h_b(1P) 9899.3, B* 5324.75, omega 782.66, phi 1019.461, K*(892)0 895.55, "
                        "K*(892)+ 891.88, Lambda_c 2286.46, Xi_c+ 2467.71, Xi_c0 2470.44, Xi_c'0 2578.7, Lambda_c(2595) 2592.25, "
                        "Lambda_c(2625) 2628.11, Omega_c 2695.2, Omega_c(2770) 2765.9, Sigma(1385)+ 1382.83, Sigma(1385)0 "
                        "1383.7, Xi_b- 5797.0, Sigma_b*+ 5830.32, Xi_b(5945)0 5952.3; D_s0*(2317) 2317.7 and D_s1(2460) "
                        "2459.5 as quoted in arXiv:2409.05337",
                "values": "see THRESH_HADRONS; entries not in this list are PDG 2024 values not re-read (unverified)"},
}

# =====================================================================================================================================
# Section E: the colour-spin engine
# =====================================================================================================================================
GELLMANN = np.zeros((8, 3, 3), dtype=complex)
GELLMANN[0][0, 1] = GELLMANN[0][1, 0] = 1
GELLMANN[1][0, 1], GELLMANN[1][1, 0] = -1j, 1j
GELLMANN[2][0, 0], GELLMANN[2][1, 1] = 1, -1
GELLMANN[3][0, 2] = GELLMANN[3][2, 0] = 1
GELLMANN[4][0, 2], GELLMANN[4][2, 0] = -1j, 1j
GELLMANN[5][1, 2] = GELLMANN[5][2, 1] = 1
GELLMANN[6][1, 2], GELLMANN[6][2, 1] = -1j, 1j
GELLMANN[7] = np.diag([1, 1, -2]) / math.sqrt(3)
PAULI = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]], dtype=complex)


def embed(op, i, n, d):
    out = np.array([[1.0 + 0j]])
    for k in range(n):
        out = np.kron(out, op if k == i else np.eye(d))
    return out


def leaves(node):
    return [node] if isinstance(node, int) else leaves(node[0]) + leaves(node[1])


def internal_nodes(node):
    """Post-order list of internal nodes (tuples); the last one is the root."""
    if isinstance(node, int):
        return []
    return internal_nodes(node[0]) + internal_nodes(node[1]) + [node]


_COLOUR_CACHE = {}
_SPIN_CACHE = {}


def colour_factors(anti, tree):
    """<c|lambda_i.lambda_j|c> for the H8 colour tree: non-root internal nodes in the (anti)triplet (Casimir 4/3), root singlet."""
    key = (tuple(anti), tree)
    if key in _COLOUR_CACHE:
        return _COLOUR_CACHE[key]
    n = len(anti)
    F = [[embed(-GELLMANN[a].conj() / 2 if anti[i] else GELLMANN[a] / 2, i, n, 3) for a in range(8)] for i in range(n)]
    nodes = internal_nodes(tree)
    M = np.zeros((3 ** n, 3 ** n), dtype=complex)
    for nd in nodes:
        lv = leaves(nd)
        cas = sum((sum(F[i][a] for i in lv)) @ (sum(F[i][a] for i in lv)) for a in range(8))
        target = 0.0 if nd is tree else 4.0 / 3.0
        D = cas - target * np.eye(3 ** n)
        M += D.conj().T @ D
    w, V = np.linalg.eigh(M)
    null = V[:, w < 1e-8]
    if null.shape[1] != 1:
        raise RuntimeError(f"colour tree {tree} is not unique: {null.shape[1]}")
    c = null[:, 0]
    cc = {}
    for i, j in itertools.combinations(range(n), 2):
        op = sum(F[i][a] @ F[j][a] for a in range(8)) * 4.0
        val = np.vdot(c, op @ c)
        cc[(i, j)] = float(val.real)
    _COLOUR_CACHE[key] = cc
    return cc


def spin_ops(n):
    if n in _SPIN_CACHE:
        return _SPIN_CACHE[n]
    S = [[embed(PAULI[k] / 2, i, n, 2) for k in range(3)] for i in range(n)]
    ss = {}
    for i, j in itertools.combinations(range(n), 2):
        ss[(i, j)] = (4.0 * sum(S[i][k] @ S[j][k] for k in range(3))).real
    _SPIN_CACHE[n] = (S, ss)
    return S, ss


def spin_state(n, tree, node_spins, J):
    """The spin vector with node spins node_spins (dict node -> s, root -> J) and S_z = J (real, normalised)."""
    S, _ = spin_ops(n)
    dim = 2 ** n
    M = np.zeros((dim, dim))
    for nd in internal_nodes(tree):
        lv = leaves(nd)
        s = float(J if nd is tree else node_spins[nd])
        S2 = sum((sum(S[i][k] for i in lv)) @ (sum(S[i][k] for i in lv)) for k in range(3)).real
        D = S2 - s * (s + 1) * np.eye(dim)
        M += D.T @ D
    Sz = sum(S[i][2] for i in range(n)).real
    D = Sz - J * np.eye(dim)
    M += D.T @ D
    w, V = np.linalg.eigh(M)
    null = V[:, w < 1e-8]
    if null.shape[1] != 1:
        raise RuntimeError(f"spin tree {tree} {node_spins} J={J} is not unique: {null.shape[1]}")
    v = null[:, 0]
    k = int(np.argmax(np.abs(v)))
    return v * np.sign(v[k])


def node_spin_options(tree, flav, anti, fixed):
    """All assignments of node spins (dict) allowed by angular momentum and Pauli (identical s, c or b quarks in a node: spin 1)."""
    nodes = internal_nodes(tree)[:-1]

    def spin_of(nd, assign):
        return Fraction(1, 2) if isinstance(nd, int) else assign[nd]

    opts = [dict()]
    for nd in nodes:
        new = []
        for asg in opts:
            s1, s2 = spin_of(nd[0], asg), spin_of(nd[1], asg)
            for s in [abs(s1 - s2) + k for k in range(int(s1 + s2 - abs(s1 - s2)) + 1)]:
                if isinstance(nd[0], int) and isinstance(nd[1], int):
                    i, j = nd
                    if flav[i] == flav[j] and anti[i] == anti[j] and flav[i] in "scb" and s != 1:
                        continue
                if nd in fixed and s not in fixed[nd]:
                    continue
                a2 = dict(asg)
                a2[nd] = s
                new.append(a2)
        opts = new
    return opts


def root_spins(tree, asg):
    l, r = tree
    s1 = Fraction(1, 2) if isinstance(l, int) else asg[l]
    s2 = Fraction(1, 2) if isinstance(r, int) else asg[r]
    return [abs(s1 - s2) + k for k in range(int(s1 + s2 - abs(s1 - s2)) + 1)]


class Config:
    """A multiquark (or ordinary hadron) in an H8 tree: flavours, antiquark flags, the tree, J, allowed node spins."""

    def __init__(self, name, flav, anti, tree, J, fixed=None, cperm=None):
        self.name, self.flav, self.anti, self.tree = name, list(flav), list(anti), tree
        self.J = Fraction(J)
        self.n = len(flav)
        self.cc = colour_factors(self.anti, tree)
        asgs = [a for a in node_spin_options(tree, self.flav, self.anti, fixed or {}) if self.J in root_spins(tree, a)]
        if not asgs:
            raise RuntimeError(f"{name}: no spin configuration with J={J}")
        self.asgs = asgs
        S, ss = spin_ops(self.n)
        self.vecs = np.array([spin_state(self.n, tree, a, float(self.J)) for a in asgs])
        self.ssm = {p: self.vecs @ ss[p] @ self.vecs.T for p in ss}      # <a|sigma_i.sigma_j|b> in the block basis
        self.cperm = cperm                                               # leaf permutation for C parity (tetraquarks)
        if cperm is not None:
            self.cmat = self.vecs @ permutation_matrix(self.n, cperm) @ self.vecs.T
        nodes = internal_nodes(tree)
        self.n_junction = len(nodes) - 1
        root = tree
        self.cross = {}
        for (i, j) in self.cc:
            # lowest common ancestor is the root: the pair sits in different halves
            lca_root = not any(i in leaves(nd) and j in leaves(nd) for nd in nodes if nd is not root)
            self.cross[(i, j)] = lca_root


def permutation_matrix(n, perm):
    dim = 2 ** n
    P = np.zeros((dim, dim))
    for idx in range(dim):
        bits = [(idx >> (n - 1 - k)) & 1 for k in range(n)]
        nb = [0] * n
        for k in range(n):
            nb[perm[k]] = bits[k]
        jdx = sum(b << (n - 1 - k) for k, b in enumerate(nb))
        P[jdx, idx] = 1.0
    return P


# =====================================================================================================================================
# Model parameters and the mass of a configuration
# =====================================================================================================================================
FLAVOURS = "qscb"
HEAVY = "cb"


class Params:
    """Masses (meson set mm, baryon set mb; scheme J uses mm for everything plus S per junction), hyperfine b, a, k_s, the binding
    singlet values B1 and heavy-heavy meson hyperfine values v (ccbar, bbbar; bcbar by interpolation)."""

    def __init__(self, mm, mb, b, a, ks_m, ks_b, B1, v_cc, v_bb, S=0.0, v_bc=None, ks_b_bs=None):
        self.mm, self.mb, self.b, self.a = dict(mm), dict(mb), b, a
        self.ks_m, self.ks_b = ks_m, ks_b
        self.ks_b_bs = ks_b if ks_b_bs is None else ks_b_bs
        self.B1 = dict(B1)
        self.v_cc, self.v_bb, self.S = v_cc, v_bb, S
        self.v_bc = v_bc if v_bc is not None else interp_vbc(v_cc, v_bb, mm["c"], mm["b"])[0]


def interp_vbc(v_cc, v_bb, mc, mb):
    """KR 2014 Sec. VII: hyperfine splitting ~ mu^p / (m1 m2), p from ccbar and bbbar."""
    mu_cc, mu_bb, mu_bc = mc / 2, mb / 2, mc * mb / (mc + mb)
    p = math.log((v_cc / v_bb) * (mc * mc) / (mb * mb)) / math.log(mu_cc / mu_bb)
    v_bc = v_cc * (mu_bc / mu_cc) ** p * (mc * mc) / (mc * mb)
    return v_bc, p


def pairkey(f1, f2):
    return "".join(sorted((f1, f2), key=FLAVOURS.index))


def v_meson(P, f1, f2):
    k = pairkey(f1, f2)
    if k == "cc":
        return P.v_cc
    if k == "bb":
        return P.v_bb
    if k == "cb":
        return P.v_bc
    kap = P.ks_m if k in ("sc", "sb") else 1.0
    return 2.0 * P.b * kap / (P.mm[f1] * P.mm[f2])


def v_baryon(P, f1, f2, scheme):
    k = pairkey(f1, f2)
    if k in ("cc", "bb", "cb"):
        return v_meson(P, f1, f2) / 2.0
    kap = P.ks_b if k == "sc" else (P.ks_b_bs if k == "sb" else 1.0)
    m = P.mm if scheme == "J" else P.mb
    return P.a * kap / (m[f1] * m[f2])


def binding1(P, f1, f2):
    return P.B1.get(pairkey(f1, f2), 0.0)


def hamiltonian(cfg, P, scheme="P", kind=None):
    """Hamiltonian matrix of the configuration's spin block. kind: 'meson', 'baryon' or 'multi' (masses and couplings follow it)."""
    if kind is None:
        kind = {2: "meson", 3: "baryon"}.get(cfg.n, "multi")
    if scheme == "J":
        mass = sum(P.mm[f] for f in cfg.flav) + P.S * cfg.n_junction
    else:
        mset = P.mm if kind == "meson" else P.mb
        mass = sum(mset[f] for f in cfg.flav)
    nb = len(cfg.asgs)
    H = np.eye(nb) * mass
    for (i, j), cij in cfg.cc.items():
        fi, fj = cfg.flav[i], cfg.flav[j]
        b1 = binding1(P, fi, fj)
        if b1 != 0.0 and not (scheme == "P-in" and kind == "multi" and cfg.cross[(i, j)]):
            H += np.eye(nb) * b1 * cij / (-16.0 / 3.0)
        if cfg.anti[i] != cfg.anti[j]:
            C = 3.0 / 16.0 * v_meson(P, fi, fj)
        else:
            C = 3.0 / 8.0 * v_baryon(P, fi, fj, scheme)
        H += -C * cij * cfg.ssm[(i, j)]
    return H


def levels(cfg, P, scheme="P"):
    """Eigenvalues and, for configurations with a C operator, the C parity of each eigenvector."""
    H = hamiltonian(cfg, P, scheme)
    w, V = np.linalg.eigh(H)
    if cfg.cperm is None:
        return w, [None] * len(w)
    cs = []
    for k in range(len(w)):
        val = V[:, k] @ cfg.cmat @ V[:, k]
        cs.append(int(round(val)))
    return w, cs


# =====================================================================================================================================
# Configurations used everywhere
# =====================================================================================================================================
def meson(name, f1, f2, S):
    return Config(name, [f1, f2], [False, True], (0, 1), S)


def baryon(name, f_out, f1, f2, s_dq, J):
    """(f_out)[f1 f2]_{s_dq} with total J (KR's basis: the odd or heaviest quark outside the diquark)."""
    return Config(name, [f_out, f1, f2], [False, False, False], (0, (1, 2)), J, fixed={(1, 2): [Fraction(s_dq)]})


def tetra(name, f1, f2, f3, f4, J, s12=None, s34=None, cperm=None):
    fixed = {}
    if s12 is not None:
        fixed[(0, 1)] = [Fraction(s) for s in np.atleast_1d(s12)]
    if s34 is not None:
        fixed[(2, 3)] = [Fraction(s) for s in np.atleast_1d(s34)]
    return Config(name, [f1, f2, f3, f4], [False, False, True, True], ((0, 1), (2, 3)), J, fixed=fixed, cperm=cperm)


def penta(name, f1, f2, f3, f4, f5bar, J, s12=None, s34=None):
    fixed = {}
    if s12 is not None:
        fixed[(0, 1)] = [Fraction(s) for s in np.atleast_1d(s12)]
    if s34 is not None:
        fixed[(2, 3)] = [Fraction(s) for s in np.atleast_1d(s34)]
    return Config(name, [f1, f2, f3, f4, f5bar], [False, False, False, False, True], (((0, 1), (2, 3)), 4), J, fixed=fixed)


H = Fraction(1, 2)
print("[E] colour-spin engine")
_m = meson("chk", "q", "q", 0)
check("E1 meson colour factor <lambda1.lambda2> (singlet)", _m.cc[(0, 1)], -16 / 3, 1e-10)
check("E2 meson spin singlet <sigma1.sigma2>", _m.ssm[(0, 1)][0, 0], -3, 1e-10)
check("E3 meson spin triplet <sigma1.sigma2>", meson("chk", "q", "q", 1).ssm[(0, 1)][0, 0], 1, 1e-10)
_b = baryon("chk", "q", "q", "q", 0, H)
check("E4 baryon pair colour factor (3bar)", _b.cc[(1, 2)], -8 / 3, 1e-10)
check("E5 baryon pair colour factor (outer quark)", _b.cc[(0, 1)], -8 / 3, 1e-10)
_t = tetra("chk", "c", "q", "c", "q", 0, cperm=[2, 3, 0, 1])
check("E6 tetraquark diquark colour factor (3bar)", _t.cc[(0, 1)], -8 / 3, 1e-10)
check("E7 tetraquark cross colour factor (-4/3)", _t.cc[(0, 2)], -4 / 3, 1e-10)
check("E8 tetraquark colour sum = -32/3", sum(_t.cc.values()), -32 / 3, 1e-10)
_p = penta("chk", "c", "q", "q", "q", "c", H)
check("E9 pentaquark colour sum = -40/3", sum(_p.cc.values()), -40 / 3, 1e-10)
check("E10 pentaquark diquark-diquark cross pair (-2/3)", _p.cc[(0, 2)], -2 / 3, 1e-10)
check("E11 pentaquark antiquark pair (-4/3)", _p.cc[(0, 4)], -4 / 3, 1e-10)
check_true("E12 MPR S-wave multiplicities, light diquark spin 0: J=1/2 (2), 3/2 (1)",
           [len(penta("chk", "c", "q", "q", "q", "c", J, s34=0).asgs) for J in (H, 3 * H)] == [2, 1])
check_true("E13 MPR S-wave multiplicities, light diquark spin 1: J=1/2 (3), 3/2 (3), 5/2 (1)",
           [len(penta("chk", "c", "q", "q", "q", "c", J, s34=1).asgs) for J in (H, 3 * H, 5 * H)] == [3, 3, 1])
_d = baryon("chk", "q", "u", "u", 1, 3 * H)
check("E14 Delta: sum of <sigma.sigma> = +3", sum(_d.ssm[p][0, 0] for p in _d.ssm), 3, 1e-10)
_x = tetra("chk", "c", "q", "c", "q", 1, cperm=[2, 3, 0, 1])
_cvals = sorted(int(round(v)) for v in np.linalg.eigvalsh(_x.cmat))
check_true("E15 [cq][cbar qbar] J=1: C eigenvalues {-1,-1,+1} (one 1++, two 1+-)", _cvals == [-1, -1, 1])
# H8's two tetraquark trees span the colour-singlet space: the compact [12]_3bar[34]_3 and the molecular (13)_1(24)_1 states are two
# vectors of the two-dimensional singlet space of q q qbar qbar with overlap 1/sqrt(3)
def _colour_singlets(anti, node_targets):
    n = len(anti)
    F = [[embed(-GELLMANN[a].conj() / 2 if anti[i] else GELLMANN[a] / 2, i, n, 3) for a in range(8)] for i in range(n)]
    M = np.zeros((3 ** n, 3 ** n), dtype=complex)
    for lv, target in node_targets:
        cas = sum((sum(F[i][a] for i in lv)) @ (sum(F[i][a] for i in lv)) for a in range(8))
        D = cas - target * np.eye(3 ** n)
        M += D.conj().T @ D
    w, V = np.linalg.eigh(M)
    return V[:, w < 1e-8]


_tet_anti = [False, False, True, True]
_all = _colour_singlets(_tet_anti, [((0, 1, 2, 3), 0.0)])
_cmp = _colour_singlets(_tet_anti, [((0, 1), 4 / 3), ((2, 3), 4 / 3), ((0, 1, 2, 3), 0.0)])
_mol = _colour_singlets(_tet_anti, [((0, 2), 0.0), ((1, 3), 0.0)])
check("E17 dimension of the q q qbar qbar colour-singlet space", _all.shape[1], 2, 0)
check("E18 |<compact tree|molecular tree>|^2 = 1/3 (the two H8 trees span the singlet space)",
      abs(np.vdot(_cmp[:, 0], _mol[:, 0])) ** 2, 1 / 3, 1e-10)
_cc4 = [tetra("chk", "c", "c", "c", "c", J, cperm=[2, 3, 0, 1]) for J in (0, 1, 2)]
check_true("E16 [cc]_1[cbar cbar]_1: C = +, -, + for J = 0, 1, 2",
           [int(round(c.cmat[0, 0])) for c in _cc4] == [1, -1, 1])


# =====================================================================================================================================
# Section H: hosting check against Karliner and Rosner's published numbers
# =====================================================================================================================================
def ordinary_configs():
    """The ordinary hadrons in KR's trees (the odd or heaviest quark outside the diquark)."""
    c = {}
    c["pi"], c["rho"], c["omega"] = meson("pi", "q", "q", 0), meson("rho", "q", "q", 1), meson("omega", "q", "q", 1)
    c["K"], c["K*"], c["phi"] = meson("K", "q", "s", 0), meson("K*", "q", "s", 1), meson("phi", "s", "s", 1)
    c["D"], c["D*"] = meson("D", "c", "q", 0), meson("D*", "c", "q", 1)
    c["Ds"], c["Ds*"] = meson("Ds", "c", "s", 0), meson("Ds*", "c", "s", 1)
    c["B"], c["B*"] = meson("B", "b", "q", 0), meson("B*", "b", "q", 1)
    c["Bs"], c["Bs*"] = meson("Bs", "b", "s", 0), meson("Bs*", "b", "s", 1)
    c["eta_c"], c["J/psi"] = meson("eta_c", "c", "c", 0), meson("J/psi", "c", "c", 1)
    c["eta_b"], c["Upsilon"] = meson("eta_b", "b", "b", 0), meson("Upsilon", "b", "b", 1)
    c["Bc"], c["Bc*"] = meson("Bc", "b", "c", 0), meson("Bc*", "b", "c", 1)
    c["N"], c["Delta"] = baryon("N", "q", "q", "q", 0, H), baryon("Delta", "q", "q", "q", 1, 3 * H)
    c["Lambda"], c["Sigma"] = baryon("Lambda", "s", "q", "q", 0, H), baryon("Sigma", "s", "q", "q", 1, H)
    c["Sigma*"] = baryon("Sigma*", "s", "q", "q", 1, 3 * H)
    c["Xi"], c["Xi*"] = baryon("Xi", "q", "s", "s", 1, H), baryon("Xi*", "q", "s", "s", 1, 3 * H)
    c["Omega"] = baryon("Omega", "s", "s", "s", 1, 3 * H)
    for Q in "cb":
        c[f"Lambda_{Q}"] = baryon(f"Lambda_{Q}", Q, "q", "q", 0, H)
        c[f"Sigma_{Q}"] = baryon(f"Sigma_{Q}", Q, "q", "q", 1, H)
        c[f"Sigma_{Q}*"] = baryon(f"Sigma_{Q}*", Q, "q", "q", 1, 3 * H)
        c[f"Xi_{Q}"] = baryon(f"Xi_{Q}", Q, "q", "s", 0, H)
        c[f"Xi_{Q}'"] = baryon(f"Xi_{Q}'", Q, "q", "s", 1, H)
        c[f"Xi_{Q}*"] = baryon(f"Xi_{Q}*", Q, "q", "s", 1, 3 * H)
        c[f"Omega_{Q}"] = baryon(f"Omega_{Q}", Q, "s", "s", 1, H)
        c[f"Omega_{Q}*"] = baryon(f"Omega_{Q}*", Q, "s", "s", 1, 3 * H)
        c[f"Xi_{Q}{Q}"] = baryon(f"Xi_{Q}{Q}", "q", Q, Q, 1, H)
        c[f"Xi_{Q}{Q}*"] = baryon(f"Xi_{Q}{Q}*", "q", Q, Q, 1, 3 * H)
    return c


ORD = ordinary_configs()


def mass1(name, P, scheme="P"):
    return float(hamiltonian(ORD[name], P, scheme)[0, 0])


KR_MM = {"q": 310.0, "s": 483.0, "c": 1663.3, "b": 5003.8}
KR_MB = {"q": 363.0, "s": 538.0, "c": 1710.5, "b": 5043.5}
KR_A = 50.0 * 363.0 ** 2
KR_KS_C = (70.7 / 6.0) * 538.0 * 1710.5 / KR_A           # 6 a_cs/(m_s m_c) = 70.7 (Omega_c* - Omega_c)
KR_KS_B = 70.7 / 43.0                                      # a_bs = (70.7/43.0) a, KR 2014 Table VI
KR = Params(KR_MM, KR_MB, 80.0 * 310.0 ** 2, KR_A, 1.0, KR_KS_C,
            {"sc": -69.9, "sb": -83.6, "cc": 3068.6 - 2 * 1663.3, "bb": 9444.7 - 2 * 5003.8, "cb": -341.5},
            113.2 / 4, 62.3 / 4, v_bc=68.0 / 4, ks_b_bs=KR_KS_B)

# exotic configurations (the H8 compact trees)
T_CC = tetra("T_cc", "c", "c", "q", "q", 1, s12=1, s34=0)
T_BB = tetra("T_bb", "b", "b", "q", "q", 1, s12=1, s34=0)
T_BC0 = tetra("T_bc(0+)", "b", "c", "q", "q", 0, s12=0, s34=0)
T_BC1 = tetra("T_bc(1+)", "b", "c", "q", "q", 1, s12=1, s34=0)

print("[H] hosting check: Karliner-Rosner 2014 and 2017 with their published parameters")
for nm, want in [("N", 939), ("Delta", 1239), ("Lambda", 1114), ("Sigma", 1179), ("Sigma*", 1381), ("Xi", 1327), ("Xi*", 1529),
                 ("Omega", 1682), ("pi", 140), ("rho", 780), ("K", 485), ("K*", 896), ("phi", 1032)]:
    check(f"H KR2014 Tables I-II {nm}", mass1(nm, KR), want, 0.6)
check("H KR2014 eq.(1)-(2) D*-D = 8b/(m_q m_c)", mass1("D*", KR) - mass1("D", KR), 119.3, 0.06)
check("H KR2014 Sec.IV B*-B", mass1("B*", KR) - mass1("B", KR), 39.7, 0.06)
check("H KR2014 Sec.IV Bs*-Bs = 8b/(m_b m_s)", mass1("Bs*", KR) - mass1("Bs", KR), 25.5, 0.06)
for nm, want in [("Sigma_c", 2444.0), ("Sigma_c*", 2507.7), ("Xi_c", 2475.3), ("Xi_c'", 2565.4), ("Xi_c*", 2632.6),
                 ("Omega_c", 2692.1), ("Omega_c*", 2762.8), ("Sigma_b", 5805.1), ("Sigma_b*", 5826.7), ("Xi_b", 5801.5),
                 ("Xi_b'", 5921.3), ("Xi_b*", 5944.1), ("Omega_b", 6042.8), ("Omega_b*", 6066.7)]:
    check(f"H KR2014 Tables IV, VI {nm}", mass1(nm, KR), want, 0.15)
for nm, want in [("Xi_cc", 3627), ("Xi_cc*", 3690), ("Xi_bb", 10162), ("Xi_bb*", 10184)]:
    check(f"H KR2014 Tables VII, IX {nm}", mass1(nm, KR), want, 0.6)
_vbc, _p = interp_vbc(113.2 / 4, 62.3 / 4, 1663.3, 5003.8)
check("H KR2014 Sec.VII power p of |psi(0)|^2 ~ mu^p", _p, 1.46, 0.005)
check("H KR2014 Sec.VII Bc*-Bc", 4 * _vbc, 68.0, 0.05)
check("H KR2014 eq.(19) spin-averaged bc: M(Bc)+3/4*68.0", 6274.5 + 0.75 * 68.0, 6325.5, 1e-9)
check("H KR2017 Table I T(bb ubar dbar) 1+", levels(T_BB, KR)[0][0], 10389.4, 0.15)
check("H KR2017 Table II T(cc ubar dbar) 1+", levels(T_CC, KR)[0][0], 3882.2, 0.15)
check("H KR2017 Table III T(bc ubar dbar) 0+", levels(T_BC0, KR)[0][0], 7133.7, 0.15)
check("H KR2017 T_bb - B B* threshold (10604)", levels(T_BB, KR)[0][0] - 10604, -215, 0.6)
check("H KR2017 T_cc - D0 D*+ threshold (3875)", levels(T_CC, KR)[0][0] - 3875, 7, 0.6)
check("H KR2017 T_bc - B0bar D0 threshold (7144.5)", levels(T_BC0, KR)[0][0] - 7144.5, -11, 0.6)
_B1, _B2, _M1, _M2 = -242.7, -532.2, 1655.6, 4988.6
_Mcc = 2 * 1655.6 - 121.3 + 14.2
_pk = math.log(_B1 / _B2) / math.log(_M1 / _M2)
_qk = math.log(113.5 / 62.3) / math.log(_M1 / _M2)
_B3 = _B1 * (_Mcc / _M1) ** _pk
_dM3 = 113.5 * (_Mcc / _M1) ** _qk
check("H KNR2017 p (binding power law)", _pk, 0.7120, 0.0006)
check("H KNR2017 B((cc)(cbar cbar))", _B3, -388.3, 0.1)
check("H KNR2017 Delta M_3", _dM3, 79.3, 0.05)
check("H KNR2017 eq.(8) M(cc cbar cbar, 0++)", 2 * 165.1 + 2 * _Mcc + _B3 - 2 * _dM3, 6191.5, 0.15)
KNR_CCCC = 2 * 165.1 + 2 * _Mcc + _B3 - 2 * _dM3


# =====================================================================================================================================
# Section F: the fit to conventional ground-state hadrons (and nothing else)
# =====================================================================================================================================
# (name, mass in MeV, source). Isospin averages where the model has no isospin breaking. KR2014 = the value as tabulated by Karliner
# and Rosner (PDG 2012 edition, their b-baryon averages); PDG2024 = current PDG value read via search (CITATIONS["PDG2024"]).
FIT_DATA = [
    ("pi", 138.0, "KR2014 Table II"), ("rho", 775.0, "KR2014 Table II"), ("omega", 782.66, "PDG2024"),
    ("K", 496.0, "KR2014 Table II"), ("K*", (891.88 + 895.55) / 2, "PDG2024 (K*+ hadroproduced, K*0)"),
    ("phi", 1019.461, "PDG2024"),
    ("D", (1864.84 + 1869.66) / 2, "PDG2024"), ("D*", (2006.85 + 2010.26) / 2, "PDG2024"),
    ("Ds", 1968.35, "PDG2024"), ("Ds*", 2112.2, "PDG2024"),
    ("B", 5279.4, "KR2014 eq.(7)"), ("B*", 5324.75, "PDG2024"), ("Bs", 5366.77, "KR2014 eq.(10)"), ("Bs*", 5415.4, "KR2014 eq.(10)"),
    ("eta_c", 2984.1, "PDG2024"), ("J/psi", 3096.900, "PDG2024"),
    ("eta_b", 9398.7, "PDG2024"), ("Upsilon", 9444.7 + 62.3 / 4, "KR2014 eqs.(16),(18)"), ("Bc", 6274.5, "KR2014 eq.(19)"),
    ("N", 939.0, "KR2014 Table I"), ("Delta", 1232.0, "KR2014 Table I"), ("Lambda", 1116.0, "KR2014 Table I"),
    ("Sigma", 1193.0, "KR2014 Table I"), ("Sigma*", 1385.0, "KR2014 Table I"), ("Xi", 1318.0, "KR2014 Table I"),
    ("Xi*", 1530.0, "KR2014 Table I"), ("Omega", 1672.0, "KR2014 Table I"),
    ("Lambda_c", 2286.46, "PDG2024"), ("Sigma_c", 2453.4, "KR2014 Table IV"), ("Sigma_c*", 2518.1, "KR2014 Table IV"),
    ("Xi_c", (2467.71 + 2470.44) / 2, "PDG2024"), ("Xi_c'", 2578.7, "PDG2024 (Xi_c'0)"), ("Xi_c*", 2645.9, "KR2014 Table IV"),
    ("Omega_c", 2695.2, "PDG2024"), ("Omega_c*", 2765.9, "PDG2024"),
    ("Lambda_b", 5619.5, "KR2014 Table V"), ("Sigma_b", 5814.26, "KR2014 Table V"), ("Sigma_b*", 5833.83, "KR2014 Table V"),
    ("Xi_b", 5792.68, "KR2014 Table V"), ("Xi_b'", 5791.84 + 139.57 + 3.653, "LHCb_Xibprime + KR2014 Table V (Xi_b0) + m(pi-)"),
    ("Xi_b*", 5952.3, "PDG2024 (Xi_b(5945)0)"), ("Omega_b", 6046.38, "KR2014 Table V"),
]
XICC = (3621.55, math.hypot(0.23, 0.30))          # LHCb_Xicc, held out
FIT_NAMES = [d[0] for d in FIT_DATA]
FIT_M = np.array([d[1] for d in FIT_DATA])
PAR_P = ["m^m_q", "m^m_s", "m^m_c", "m^m_b", "m^b_q", "m^b_s", "m^b_c", "m^b_b", "b/(310)^2", "a/(363)^2", "k_s",
         "B1(c sbar)", "B1(b sbar)", "B1(c cbar)", "B1(b bbar)", "B1(b cbar)", "v(c cbar)", "v(b bbar)"]
PAR_J = ["m_q", "m_s", "m_c", "m_b", "S", "b/(310)^2", "a/(363)^2", "k_s",
         "B1(c sbar)", "B1(b sbar)", "B1(c cbar)", "B1(b bbar)", "B1(b cbar)", "v(c cbar)", "v(b bbar)"]


def params_from(theta, scheme):
    t = list(theta)
    if scheme == "J":
        mm = dict(zip("qscb", t[0:4]))
        return Params(mm, mm, t[5] * 310.0 ** 2, t[6] * 363.0 ** 2, t[7], t[7],
                      {"sc": t[8], "sb": t[9], "cc": t[10], "bb": t[11], "cb": t[12]}, t[13], t[14], S=t[4])
    return Params(dict(zip("qscb", t[0:4])), dict(zip("qscb", t[4:8])), t[8] * 310.0 ** 2, t[9] * 363.0 ** 2, t[10], t[10],
                  {"sc": t[11], "sb": t[12], "cc": t[13], "bb": t[14], "cb": t[15]}, t[16], t[17])


THETA0_P = np.array([310, 483, 1663.3, 5003.8, 363, 538, 1710.5, 5043.5, 80, 50, 1.6, -69.9, -83.6, -258, -562.8, -341.5,
                     28.3, 15.6])
THETA0_J = np.array([310, 483, 1655.6, 4988.6, 165, 80, 50, 1.6, -69.9, -83.6, -243, -532, -341.5, 28.3, 15.6])


def fit_masses(theta, scheme, names=FIT_NAMES):
    P = params_from(theta, scheme)
    return np.array([mass1(nm, P, scheme) for nm in names])


def do_fit(scheme, idx=None):
    names = [FIT_NAMES[i] for i in idx] if idx is not None else FIT_NAMES
    target = FIT_M[idx] if idx is not None else FIT_M
    th0 = THETA0_J if scheme == "J" else THETA0_P
    r = optimize.least_squares(lambda th: fit_masses(th, scheme, names) - target, th0, method="lm", xtol=1e-12, ftol=1e-12,
                               gtol=1e-12, max_nfev=20000)
    return r


def jac_num(fun, theta, h=1e-5):
    f0 = np.atleast_1d(fun(theta))
    Jm = np.zeros((len(f0), len(theta)))
    for k in range(len(theta)):
        step = h * max(1.0, abs(theta[k]))
        tp, tm = theta.copy(), theta.copy()
        tp[k] += step
        tm[k] -= step
        Jm[:, k] = (np.atleast_1d(fun(tp)) - np.atleast_1d(fun(tm))) / (2 * step)
    return Jm


print("[F] fit to 42 conventional ground-state hadrons")
FIT = {}
for scheme in ("P", "J"):
    r = do_fit(scheme)
    th = r.x
    res = fit_masses(th, scheme) - FIT_M
    npar = len(th)
    dof = len(FIT_M) - npar
    sig = math.sqrt(float(res @ res) / dof)
    Jm = jac_num(lambda t: fit_masses(t, scheme), th)
    cov = sig ** 2 * np.linalg.inv(Jm.T @ Jm)
    FIT[scheme] = {"theta": th, "res": res, "sigma": sig, "dof": dof, "cov": cov, "P": params_from(th, scheme),
                   "cost": float(r.cost), "status": int(r.status), "jac_rank": int(np.linalg.matrix_rank(Jm, tol=1e-8))}
    check_true(f"F{'1' if scheme == 'P' else '2'} fit converged (scheme {scheme}, status {r.status})", r.status > 0)
    check(f"F{'3' if scheme == 'P' else '4'} Jacobian full rank (scheme {scheme})", FIT[scheme]["jac_rank"], npar, 0)
    g = Jm.T @ res
    check(f"F{'5' if scheme == 'P' else '6'} gradient of RSS at the minimum (scheme {scheme}, max |J^T r|)",
          float(np.max(np.abs(g))), 0.0, 1e-4 * float(res @ res) + 1e-6)
    print(f"     scheme {scheme}: sigma_model = {sig:.2f} MeV (dof {dof}), max |residual| = {np.max(np.abs(res)):.1f} MeV")

# a second start far from KR's values must find the same minimum
_r2 = optimize.least_squares(lambda th: fit_masses(th, "P") - FIT_M, THETA0_P * 1.05, method="lm", xtol=1e-12, ftol=1e-12,
                             gtol=1e-12, max_nfev=20000)
check("F7 fit from a start 5% away reaches the same RSS", 2 * _r2.cost, 2 * FIT["P"]["cost"], 1e-6 * 2 * FIT["P"]["cost"])
SIG = FIT["P"]["sigma"]
PFIT = FIT["P"]["P"]

# leave-one-out (hadrons whose removal leaves a parameter undetermined are skipped: they fix it exactly)
EXACT = {"eta_c", "J/psi", "eta_b", "Upsilon", "Bc"}
loo = {}
for i, nm in enumerate(FIT_NAMES):
    if nm in EXACT:
        continue
    idx = [k for k in range(len(FIT_NAMES)) if k != i]
    r = do_fit("P", idx)
    loo[nm] = float(fit_masses(r.x, "P", [nm])[0] - FIT_M[i])
LOO_RMS = math.sqrt(np.mean(np.array(list(loo.values())) ** 2))
_res_ne = np.array([FIT["P"]["res"][i] for i, nm in enumerate(FIT_NAMES) if nm not in EXACT])
check_true("F8 leave-one-out residuals at least as large as in-sample (RMS)", LOO_RMS >= math.sqrt(np.mean(_res_ne ** 2)) - 1e-9)
print(f"     leave-one-out RMS over {len(loo)} hadrons: {LOO_RMS:.2f} MeV (in-sample RMS {math.sqrt(np.mean(_res_ne ** 2)):.2f})")


def predict(fun, scheme="P"):
    """Value and 1-sigma error (sigma_model in quadrature with the propagated parameter covariance) of fun(Params); the variant
    P-in uses the parameters of the primary fit."""
    fs = "J" if scheme == "J" else "P"
    th = FIT[fs]["theta"]
    f = lambda t: fun(params_from(t, fs))    # noqa: E731
    val = float(f(th))
    g = jac_num(f, th)[0]
    var_par = float(g @ FIT[fs]["cov"] @ g)
    return val, math.sqrt(FIT[fs]["sigma"] ** 2 + var_par), math.sqrt(var_par)


_xicc = predict(lambda P: mass1("Xi_cc", P))
XICC_PULL = (_xicc[0] - XICC[0]) / math.hypot(_xicc[1], XICC[1])
print(f"     Xi_cc++ held out: model {_xicc[0]:.1f} +- {_xicc[1]:.1f}, LHCb {XICC[0]} -> pull {XICC_PULL:+.2f}")
print("     parameters:", ", ".join(f"{n}={v:.4g}" for n, v in zip(PAR_P, FIT["P"]["theta"])))
print("     residuals:", ", ".join(f"{n} {r:+.1f}" for n, r in zip(FIT_NAMES, FIT["P"]["res"])))


# =====================================================================================================================================
# Hadrons for two-hadron thresholds (width below 60 MeV), PDG 2024 values. ver: True if re-read (CITATIONS PDG2024, KR2014 or an
# experiment), False if not re-read. Content: lower case quarks, upper case antiquarks. C only for self-conjugate states.
# =====================================================================================================================================
THRESH_HADRONS = [
    # name, mass, width, J, P, C, content, verified
    ("pi+", 139.57039, 0.0, 0, -1, None, "uD", False), ("pi0", 134.9768, 0.0, 0, -1, 1, "uU", False),
    ("K+", 493.677, 0.0, 0, -1, None, "uS", True), ("K0", 497.611, 0.0, 0, -1, None, "dS", False),
    ("eta", 547.862, 0.0, 0, -1, 1, "uU", False), ("eta'", 957.78, 0.2, 0, -1, 1, "uU", False),
    ("omega", 782.66, 8.7, 1, -1, -1, "uU", True), ("phi", 1019.461, 4.2, 1, -1, -1, "sS", True),
    ("K*+", 891.88, 51.4, 1, -1, None, "uS", True), ("K*0", 895.55, 47.3, 1, -1, None, "dS", True),
    ("D0", 1864.84, 0.0, 0, -1, None, "cU", True), ("D+", 1869.66, 0.0, 0, -1, None, "cD", True),
    ("D*0", 2006.85, 0.1, 1, -1, None, "cU", True), ("D*+", 2010.26, 0.1, 1, -1, None, "cD", True),
    ("Ds+", 1968.35, 0.0, 0, -1, None, "cS", True), ("Ds*+", 2112.2, 0.1, 1, -1, None, "cS", True),
    ("Ds0*(2317)+", 2317.7, 3.8, 0, 1, None, "cS", True), ("Ds1(2460)+", 2459.5, 3.5, 1, 1, None, "cS", True),
    ("Ds1(2536)+", 2535.11, 0.9, 1, 1, None, "cS", True), ("Ds2*(2573)+", 2569.1, 16.9, 2, 1, None, "cS", False),
    ("D1(2420)0", 2422.1, 31.3, 1, 1, None, "cU", False), ("D1(2420)+", 2426.2, 25.0, 1, 1, None, "cD", False),
    ("D2*(2460)0", 2461.1, 47.3, 2, 1, None, "cU", True), ("D2*(2460)+", 2465.4, 46.7, 2, 1, None, "cD", False),
    ("eta_c", 2984.1, 30.5, 0, -1, 1, "cC", True), ("J/psi", 3096.900, 0.1, 1, -1, -1, "cC", True),
    ("chi_c0", 3414.71, 10.7, 0, 1, 1, "cC", True), ("chi_c1", 3510.67, 0.8, 1, 1, 1, "cC", True),
    ("h_c", 3525.37, 0.8, 1, 1, -1, "cC", True), ("chi_c2", 3556.17, 2.0, 2, 1, 1, "cC", True),
    ("eta_c(2S)", 3637.7, 11.8, 0, -1, 1, "cC", True), ("psi(2S)", 3686.097, 0.3, 1, -1, -1, "cC", True),
    ("psi(3770)", 3773.7, 27.2, 1, -1, -1, "cC", False),
    ("B+", 5279.34, 0.0, 0, -1, None, "uB", False), ("B0", 5279.66, 0.0, 0, -1, None, "dB", False),
    ("B*+", 5324.75, 0.0, 1, -1, None, "uB", True), ("B*0", 5324.75, 0.0, 1, -1, None, "dB", True),
    ("Bs0", 5366.92, 0.0, 0, -1, None, "sB", False), ("Bs*0", 5415.8, 0.0, 1, -1, None, "sB", False),
    ("eta_b", 9398.7, 10.0, 0, -1, 1, "bB", True), ("Upsilon(1S)", 9460.40, 0.1, 1, -1, -1, "bB", False),
    ("chi_b0(1P)", 9859.44, 0.0, 0, 1, 1, "bB", False), ("chi_b1(1P)", 9892.78, 0.0, 1, 1, 1, "bB", False),
    ("h_b(1P)", 9899.3, 0.0, 1, 1, -1, "bB", True), ("chi_b2(1P)", 9912.21, 0.0, 2, 1, 1, "bB", False),
    ("Upsilon(2S)", 10023.4, 0.0, 1, -1, -1, "bB", False), ("chi_b0(2P)", 10232.5, 0.0, 0, 1, 1, "bB", False),
    ("chi_b1(2P)", 10255.46, 0.0, 1, 1, 1, "bB", False), ("h_b(2P)", 10259.8, 0.0, 1, 1, -1, "bB", False),
    ("chi_b2(2P)", 10268.65, 0.0, 2, 1, 1, "bB", False), ("Upsilon(3S)", 10355.1, 0.0, 1, -1, -1, "bB", False),
    ("p", 938.272, 0.0, H, 1, None, "uud", False), ("n", 939.565, 0.0, H, 1, None, "udd", False),
    ("Lambda", 1115.683, 0.0, H, 1, None, "uds", False), ("Sigma+", 1189.37, 0.0, H, 1, None, "uus", False),
    ("Sigma0", 1192.642, 0.0, H, 1, None, "uds", False), ("Sigma-", 1197.449, 0.0, H, 1, None, "dds", False),
    ("Xi0", 1314.86, 0.0, H, 1, None, "uss", False), ("Xi-", 1321.71, 0.0, H, 1, None, "dss", False),
    ("Omega-", 1672.45, 0.0, 3 * H, 1, None, "sss", False),
    ("Sigma(1385)+", 1382.83, 36.0, 3 * H, 1, None, "uus", True), ("Sigma(1385)0", 1383.7, 36.0, 3 * H, 1, None, "uds", True),
    ("Sigma(1385)-", 1387.2, 39.4, 3 * H, 1, None, "dds", False),
    ("Xi(1530)0", 1531.80, 9.1, 3 * H, 1, None, "uss", False), ("Xi(1530)-", 1535.0, 9.9, 3 * H, 1, None, "dss", False),
    ("Lambda_c+", 2286.46, 0.0, H, 1, None, "udc", True),
    ("Sigma_c++", 2453.97, 1.9, H, 1, None, "uuc", False), ("Sigma_c+", 2452.65, 4.6, H, 1, None, "udc", False),
    ("Sigma_c0", 2453.75, 1.8, H, 1, None, "ddc", False),
    ("Sigma_c*++", 2518.41, 14.8, 3 * H, 1, None, "uuc", False), ("Sigma_c*+", 2517.4, 17.2, 3 * H, 1, None, "udc", False),
    ("Sigma_c*0", 2518.48, 15.3, 3 * H, 1, None, "ddc", False),
    ("Xi_c+", 2467.71, 0.0, H, 1, None, "usc", True), ("Xi_c0", 2470.44, 0.0, H, 1, None, "dsc", True),
    ("Xi_c'+", 2578.2, 0.0, H, 1, None, "usc", False), ("Xi_c'0", 2578.7, 0.0, H, 1, None, "dsc", True),
    ("Xi_c(2645)+", 2645.10, 2.1, 3 * H, 1, None, "usc", False), ("Xi_c(2645)0", 2646.16, 2.4, 3 * H, 1, None, "dsc", False),
    ("Omega_c0", 2695.2, 0.0, H, 1, None, "ssc", True), ("Omega_c(2770)0", 2765.9, 0.0, 3 * H, 1, None, "ssc", True),
    ("Lambda_c(2595)+", 2592.25, 2.6, H, -1, None, "udc", True), ("Lambda_c(2625)+", 2628.11, 1.0, 3 * H, -1, None, "udc", True),
    ("Xi_cc++", 3621.55, 0.0, H, 1, None, "ucc", True),
]
CHARGE = {"u": 2 / 3, "d": -1 / 3, "s": -1 / 3, "c": 2 / 3, "b": -1 / 3}


def flavour_vector(content):
    nc, ncb = content.count("c"), content.count("C")
    nb, nbb = content.count("b"), content.count("B")
    S = content.count("S") - content.count("s")
    bary = sum(1 for x in content if x.islower()) - sum(1 for x in content if x.isupper())
    Q = sum(CHARGE[x] for x in content if x.islower()) - sum(CHARGE[x.lower()] for x in content if x.isupper())
    return (nc, ncb, nb, nbb, S, bary, int(round(3 * Q)))


def anti_content(content):
    return content.swapcase()


class Hadron:
    def __init__(self, name, m, w, J, P, C, content, ver, anti_of=None):
        self.name, self.m, self.w, self.J, self.P, self.C, self.content, self.ver = name, m, w, Fraction(J), P, C, content, ver
        self.fv = flavour_vector(content)
        self.self_conj = C is not None
        self.species = name if anti_of is None else anti_of
        self.is_anti = anti_of is not None


def hadron_list(table):
    out = []
    for (nm, m, w, J, P, C, content, ver) in table:
        if w >= 60.0:
            continue
        out.append(Hadron(nm, m, w, J, P, C, content, ver))
        if C is None:
            Pa = P if len(content) == 2 else -P          # an antifermion has the opposite intrinsic parity
            out.append(Hadron(nm + "~", m, w, J, Pa, None, anti_content(content), ver, anti_of=nm))
    return out


def spin_range(j1, j2):
    return [abs(j1 - j2) + k for k in range(int(j1 + j2 - abs(j1 - j2)) + 1)]


def s_wave_allowed(state, h1, h2):
    """state: dict with fv, J (Fraction or None), P, C (None unless a neutral hidden-flavour state)."""
    if tuple(a + b for a, b in zip(h1.fv, h2.fv)) != state["fv"]:
        return False
    Ss = spin_range(h1.J, h2.J)
    if state["J"] is not None:
        if state["J"] not in Ss:
            return False
        Ss = [state["J"]]
    if state["P"] is not None and h1.P * h2.P != state["P"]:
        return False
    if state["C"] is not None:
        if h1.self_conj and h2.self_conj:
            return h1.C * h2.C == state["C"]
        if h1.self_conj or h2.self_conj:
            return False
        if h1.species == h2.species and h1.is_anti != h2.is_anti:      # particle and its own antiparticle: C = (-1)^(L+S), L = 0
            return any((-1) ** int(S) == state["C"] for S in Ss)
        return True
    return True


def thresholds_for(state, hadrons):
    out = []
    for h1, h2 in itertools.combinations_with_replacement(hadrons, 2):
        if s_wave_allowed(state, h1, h2):
            out.append((h1.m + h2.m, f"{h1.name} {h2.name}", h1.ver and h2.ver))
    out.sort(key=lambda t: t[0])
    # identical sums from charge-conjugate duplicates are merged
    merged = []
    for t in out:
        if merged and abs(merged[-1][0] - t[0]) < 1e-9:
            continue
        merged.append(t)
    return merged


HADRONS = hadron_list(THRESH_HADRONS)


# =====================================================================================================================================
# Section A: compact exotics. The model, as fitted, applied without refitting.
# =====================================================================================================================================
print("[A] compact exotics (results, not checks)")
Hh, H3, H5 = H, 3 * H, 5 * H
CFG = {
    "T_cc": [T_CC], "T_bb": [T_BB], "T_bc0": [T_BC0], "T_bc1": [T_BC1],
    "T_cc(I=1)": [tetra(f"T_cc I=1 J={J}", "c", "c", "q", "q", J, s12=1, s34=1) for J in (0, 1, 2)],
    "T_bb(I=1)": [tetra(f"T_bb I=1 J={J}", "b", "b", "q", "q", J, s12=1, s34=1) for J in (0, 1, 2)],
    "X0": [tetra("[ud]0[cbar sbar]0", "q", "q", "c", "s", 0, s12=0, s34=0)],
    "X0(1+)": [tetra("[ud]0[cbar sbar]1", "q", "q", "c", "s", 1, s12=0, s34=1)],
    "Tcsbar": [tetra(f"[cq][sbar qbar] J={J}", "c", "q", "s", "q", J) for J in (0, 1, 2)],
    "cccc": [tetra(f"[cc]1[cbar cbar]1 J={J}", "c", "c", "c", "c", J, cperm=[2, 3, 0, 1]) for J in (0, 1, 2)],
    "hidden_c": [tetra(f"[cq][cbar qbar] J={J}", "c", "q", "c", "q", J, cperm=[2, 3, 0, 1]) for J in (0, 1, 2)],
    "Pc": [penta(f"([cq][qq]_{s})cbar J={J}", "c", "q", "q", "q", "c", J, s34=s)
           for s, Js in ((0, (Hh, H3)), (1, (Hh, H3, H5))) for J in Js],
    "Ppsis_A": [penta(f"([cs][ud]_0)cbar J={J}", "c", "s", "q", "q", "c", J, s34=0) for J in (Hh, H3)],
    "Ppsis_B": [penta(f"([cq][qs])cbar J={J}", "c", "q", "q", "s", "c", J) for J in (Hh, H3, H5)],
    "Pcc": [penta(f"([cc]1[ud]_{s})qbar J={J}", "c", "c", "q", "q", "q", J, s34=s)
            for s, Js in ((0, (Hh, H3)), (1, (Hh, H3, H5))) for J in Js],
}


def spectrum(key, P, scheme):
    """All levels of a configuration family: list of (mass, cfg index, eigen index, J, C)."""
    out = []
    for ci, cfg in enumerate(CFG[key]):
        w, cs = levels(cfg, P, scheme)
        for k in range(len(w)):
            out.append((float(w[k]), ci, k, cfg.J, cs[k]))
    return out


def level_fn(key, ci, k):
    return lambda P, scheme="P": float(levels(CFG[key][ci], P, scheme)[0][k])


def pick(key, P, scheme, rule):
    """Pre-registered selection: rule = ('lowest', filter) or ('nearest', target, filter). Returns (ci, k)."""
    sp = spectrum(key, P, scheme)
    flt = rule[-1]
    cand = [t for t in sp if flt(t)]
    if rule[0] == "lowest":
        t = min(cand, key=lambda t: t[0])
    else:
        t = min(cand, key=lambda t: abs(t[0] - rule[1]))
    return t[1], t[2]


ANY = lambda t: True          # noqa: E731


def lowest_threshold(content, J, P, C=None):
    st = {"fv": flavour_vector(content), "J": None if J is None else Fraction(J), "P": P, "C": C}
    return thresholds_for(st, HADRONS)[0]


def err_toward(model, data):
    m, lo, hi = data
    return hi if model > m else lo


ITEMS = []      # every prediction row of (a)


def add_item(label, key, rule, kind, data=None, data_src=None, thr=None, note="", jpc=""):
    row = {"label": label, "family": key, "kind": kind, "note": note, "JPC": jpc}
    for scheme in ("P", "P-in", "J"):
        Pp = FIT["J"]["P"] if scheme == "J" else PFIT
        ci, k = pick(key, Pp, scheme, rule)
        fn = level_fn(key, ci, k)
        val, err, err_par = predict(lambda Pq, fn=fn, scheme=scheme: fn(Pq, scheme), scheme)
        row[scheme] = {"M": val, "err": err, "err_par": err_par, "config": CFG[key][ci].name, "level": k}
    ci, k = pick(key, KR, "P", rule)
    row["KRpar"] = {"M": level_fn(key, ci, k)(KR, "P"), "config": CFG[key][ci].name}
    if thr is not None:
        row["threshold"] = {"pair": thr[1], "M": thr[0], "verified": thr[2]}
        for scheme in ("P", "P-in", "J"):
            row[scheme]["binding"] = row[scheme]["M"] - thr[0]
    if data is not None:
        row["data"] = {"M": data[0], "err_lo": data[1], "err_hi": data[2], "source": data_src}
        for scheme in ("P", "P-in", "J"):
            e = err_toward(row[scheme]["M"], data)
            row[scheme]["pull"] = (row[scheme]["M"] - data[0]) / math.hypot(row[scheme]["err"], e)
        z = row["P"]["pull"]
        row["verdict"] = ("holds" if abs(z) < 2 else "refuted") if kind == "scored" else "info"
    elif kind == "live":
        row["verdict"] = "live"
    ITEMS.append(row)
    return row


TH_TCC = (2010.26 + 1864.84, "D*+ D0", True)
DATA_TCC = (TH_TCC[0] - 0.360, 0.08, 0.08)       # pole delta m = -360 +- 40 keV; threshold error 0.07 MeV
add_item("T_cc+ (cc ubar dbar)", "T_cc", ("lowest", ANY), "scored", DATA_TCC, "LHCb_Tcc_NC", TH_TCC, jpc="1+")
add_item("T_bb- (bb ubar dbar)", "T_bb", ("lowest", ANY), "live", thr=lowest_threshold("bbUD", 1, 1), jpc="1+")
add_item("T_bc (bc ubar dbar), 0+", "T_bc0", ("lowest", ANY), "live", thr=lowest_threshold("bcUD", 0, 1), jpc="0+")
add_item("T_bc (bc ubar dbar), 1+", "T_bc1", ("lowest", ANY), "live", thr=lowest_threshold("bcUD", 1, 1), jpc="1+")
add_item("X0(2900) (ud cbar sbar)", "X0", ("lowest", ANY), "scored", (2866.0, math.hypot(7, 2), math.hypot(7, 2)), "LHCb_X2900",
         lowest_threshold("udCS", 0, 1), jpc="0+")
add_item("T_csbar0(2900) (c sbar u dbar)", "Tcsbar", ("lowest", lambda t: t[3] == 0), "scored",
         (2908.0, math.hypot(11, 20), math.hypot(11, 20)), "LHCb_Tcsbar", lowest_threshold("cSuD", 0, 1), jpc="0+")
TH_JJ = lowest_threshold("ccCC", 2, 1, 1)
add_item("cc cbar cbar 2++ vs X(6900)", "cccc", ("lowest", lambda t: t[3] == 2), "scored",
         (6905.0, math.hypot(11, 7), math.hypot(11, 7)), "LHCb_X6900", TH_JJ, jpc="2++")
add_item("cc cbar cbar 0++ vs X(6900)", "cccc", ("lowest", lambda t: t[3] == 0), "info",
         (6905.0, math.hypot(11, 7), math.hypot(11, 7)), "LHCb_X6900", lowest_threshold("ccCC", 0, 1, 1), jpc="0++")
add_item("cc cbar cbar 1+-", "cccc", ("lowest", lambda t: t[3] == 1), "live", thr=lowest_threshold("ccCC", 1, 1, -1), jpc="1+-")
TH_PC = lowest_threshold("uudcC", None, -1)
add_item("P_c(4312) (lowest uud c cbar)", "Pc", ("lowest", ANY), "scored", (4311.9, math.hypot(0.7, 0.6), math.hypot(0.7, 6.8)),
         "LHCb_Pc2019", TH_PC)
add_item("P_c(4440) (nearest level)", "Pc", ("nearest", 4440.3, ANY), "scored",
         (4440.3, math.hypot(1.3, 4.7), math.hypot(1.3, 4.1)), "LHCb_Pc2019", TH_PC, note="assignment by proximity")
add_item("P_c(4457) (nearest level)", "Pc", ("nearest", 4457.3, ANY), "scored",
         (4457.3, math.hypot(0.6, 1.7), math.hypot(0.6, 4.1)), "LHCb_Pc2019", TH_PC, note="assignment by proximity")


def ppsis_lowest_half(P, scheme):
    a = [t for t in spectrum("Ppsis_A", P, scheme) if t[3] == Hh]
    b = [t for t in spectrum("Ppsis_B", P, scheme) if t[3] == Hh]
    return min(a + b, key=lambda t: t[0])


# P_psis: the lowest J = 1/2 level of the two I = 0 families
_fa = [t for t in spectrum("Ppsis_A", PFIT, "P") if t[3] == Hh]
_fb = [t for t in spectrum("Ppsis_B", PFIT, "P") if t[3] == Hh]
_fam = "Ppsis_A" if min(_fa)[0] <= min(_fb)[0] else "Ppsis_B"
TH_PS = lowest_threshold("udscC", None, -1)
add_item("P_psis(4338) (lowest I=0, J=1/2)", _fam, ("lowest", lambda t: t[3] == Hh), "scored", (4338.2, math.hypot(0.7, 0.4),
         math.hypot(0.7, 0.4)), "LHCb_Ppsis4338", lowest_threshold("udscC", Hh, -1), jpc="1/2-")
_near_A = min(spectrum("Ppsis_A", PFIT, "P"), key=lambda t: abs(t[0] - 4458.8))
_near_B = min(spectrum("Ppsis_B", PFIT, "P"), key=lambda t: abs(t[0] - 4458.8))
_fam2 = "Ppsis_A" if abs(_near_A[0] - 4458.8) <= abs(_near_B[0] - 4458.8) else "Ppsis_B"
add_item("P_cs(4459) (nearest level; evidence only)", _fam2, ("nearest", 4458.8, ANY), "scored",
         (4458.8, math.hypot(2.9, 1.1), math.hypot(2.9, 4.7)), "LHCb_Pcs4459", TH_PS, note="assignment by proximity; 'evidence'")
add_item("P_cc ([cc][ud] qbar), lowest", "Pcc", ("lowest", ANY), "live", thr=lowest_threshold("ccudU", Hh, -1), jpc="1/2-")
add_item("compact X(3872): [cq][cbar qbar] 1++", "hidden_c", ("lowest", lambda t: t[3] == 1 and t[4] == 1), "info",
         (185.598 + 3686.097, math.hypot(0.067, 0.068), math.hypot(0.067, 0.068)), "LHCb_X3872_ls",
         lowest_threshold("cCuU", 1, 1, 1), jpc="1++")
add_item("compact Z_c(3900): [cq][cbar qbar] 1+-", "hidden_c", ("lowest", lambda t: t[3] == 1 and t[4] == -1), "info",
         (3899.0, math.hypot(3.6, 4.9), math.hypot(3.6, 4.9)), "BESIII_Zc3900", lowest_threshold("cCuD", 1, 1), jpc="1+-")
for J in (0, 1, 2):
    add_item(f"T_cc partner I=1, J={J}", "T_cc(I=1)", ("lowest", lambda t, J=J: t[3] == J), "live",
             thr=lowest_threshold("ccUU", J, 1), jpc=f"{J}+")
    add_item(f"T_bb partner I=1, J={J}", "T_bb(I=1)", ("lowest", lambda t, J=J: t[3] == J), "live",
             thr=lowest_threshold("bbUU", J, 1), jpc=f"{J}+")
add_item("X0 partner [ud]0[cbar sbar]1, 1+", "X0(1+)", ("lowest", ANY), "live", thr=lowest_threshold("udCS", 1, 1), jpc="1+")

for row in ITEMS:
    s = f"  {row['label']:<44s} P {row['P']['M']:8.1f} +- {row['P']['err']:4.1f}  P-in {row['P-in']['M']:8.1f}  J {row['J']['M']:8.1f}"
    if "data" in row:
        s += f"  data {row['data']['M']:8.1f}  pull {row['P']['pull']:+6.2f}  {row['verdict']}"
    if "threshold" in row:
        s += f"  [{row['threshold']['pair']} {row['threshold']['M']:.1f}: {row['P']['binding']:+.1f}]"
    print(s)


# chance proximity of the 'nearest level' assignments: the fraction of a +-150 MeV window around the datum that lies as close to
# some level of the multiplet as the datum does (the look-elsewhere cost of choosing the level after seeing the mass)
def proximity_p(levels_list, m, d, W=150.0):
    return interval_cover([(x - d, x + d) for x in levels_list], m - W, m + W) / (2 * W)


def interval_cover(intervals, lo, hi):
    iv = sorted((max(a, lo), min(b, hi)) for a, b in intervals if b > lo and a < hi)
    tot, cur_a, cur_b = 0.0, None, None
    for a, b in iv:
        if cur_b is None or a > cur_b:
            if cur_b is not None:
                tot += cur_b - cur_a
            cur_a, cur_b = a, b
        else:
            cur_b = max(cur_b, b)
    if cur_b is not None:
        tot += cur_b - cur_a
    return tot


for row in ITEMS:
    if row.get("note", "").startswith("assignment by proximity"):
        fam = row["family"]
        lv = [t[0] for t in spectrum(fam, PFIT, "P")]
        if fam.startswith("Ppsis"):
            lv = [t[0] for t in spectrum("Ppsis_A", PFIT, "P")] + [t[0] for t in spectrum("Ppsis_B", PFIT, "P")]
        d = abs(row["P"]["M"] - row["data"]["M"])
        row["p_chance"] = proximity_p(lv, row["data"]["M"], d)
        row["n_levels"] = len(lv)
        print(f"  {row['label']}: |model - data| = {d:.1f} MeV; chance that a mass placed at random within +-150 MeV lies as close "
              f"to one of the {len(lv)} levels: {row['p_chance']:.2f}")

# =====================================================================================================================================
# Section B: threshold proximity of the established exotic hadrons
# =====================================================================================================================================
print("[B] threshold proximity (results; the Monte Carlo agreement is a check)")
# name, mass, err, width, J, P, C, content, source
CATALOGUE = [
    ("chi_c1(3872)", 3686.097 + 185.598, 0.10, 1.39, 1, 1, 1, "cCuU", "LHCb_X3872_ls"),
    ("Z_c(3900)+", 3899.0, 6.1, 46.0, 1, 1, None, "cCuD", "BESIII_Zc3900"),
    ("Z_c(4020)+", 4022.9, 2.8, 7.9, None, None, None, "cCuD", "BESIII_Zc4020"),
    ("Z_c(4430)+", 4475.0, 19.0, 172.0, 1, 1, None, "cCuD", "LHCb_Z4430"),
    ("Z_cs(3985)+", 3982.5, 3.1, 12.8, None, None, None, "cCuS", "BESIII_Zcs3985"),
    ("Z_cs(4000)+", 4003.0, 11.0, 131.0, 1, 1, None, "cCuS", "LHCb_JpsiK"),
    ("Z_cs(4220)+", 4216.0, 40.0, 233.0, 1, None, None, "cCuS", "LHCb_JpsiK"),
    ("chi_c1(4140)", 4118.0, 28.0, 162.0, 1, 1, 1, "cCsS", "LHCb_JpsiK"),
    ("chi_c1(4274)", 4294.0, 5.5, 53.0, 1, 1, 1, "cCsS", "LHCb_JpsiK"),
    ("chi_c0(4500)", 4474.0, 4.2, 77.0, 0, 1, 1, "cCsS", "LHCb_JpsiK"),
    ("chi_c0(4700)", 4694.0, 10.0, 87.0, 0, 1, 1, "cCsS", "LHCb_JpsiK"),
    ("X(4685)", 4684.0, 15.0, 126.0, 1, 1, 1, "cCsS", "LHCb_JpsiK"),
    ("X(4630)", 4626.0, 60.0, 174.0, 1, -1, 1, "cCsS", "LHCb_JpsiK"),
    ("X(3960)", 3956.0, 11.2, 43.0, 0, 1, 1, "cCsS", "LHCb_X3960"),
    ("psi(4230)", 4222.0, 3.4, 44.1, 1, -1, -1, "cCuU", "BESIII_Y4230"),
    ("Z_b(10610)+", 10607.2, 2.0, 18.4, None, None, None, "bBuD", "Belle_Zb"),
    ("Z_b(10650)+", 10652.2, 1.5, 11.5, None, None, None, "bBuD", "Belle_Zb"),
    ("T_cc(3875)+", TH_TCC[0] - 0.360, 0.08, 0.048, 1, 1, None, "ccUD", "LHCb_Tcc_NC"),
    ("X0(2900)", 2866.0, 7.3, 57.0, 0, 1, None, "udCS", "LHCb_X2900"),
    ("X1(2900)", 2904.0, 5.1, 110.0, 1, -1, None, "udCS", "LHCb_X2900"),
    ("T_csbar0(2900)++", 2908.0, 22.8, 136.0, 0, 1, None, "cSuD", "LHCb_Tcsbar"),
    ("P_c(4312)+", 4311.9, 3.0, 9.8, None, None, None, "uudcC", "LHCb_Pc2019"),
    ("P_c(4440)+", 4440.3, 4.6, 20.6, None, None, None, "uudcC", "LHCb_Pc2019"),
    ("P_c(4457)+", 4457.3, 2.5, 6.4, None, None, None, "uudcC", "LHCb_Pc2019"),
    ("P_psis(4338)0", 4338.2, 0.8, 7.0, H, -1, None, "udscC", "LHCb_Ppsis4338"),
    ("X(6900)", 6905.0, 13.0, 80.0, None, None, 1, "ccCC", "LHCb_X6900"),
]
W_MAIN, W_ALT = 150.0, 300.0
TEXNAME = {"chi_c1(3872)": r"$\chi_{c1}(3872)$", "Z_c(3900)+": r"$Z_c(3900)^+$", "Z_c(4020)+": r"$Z_c(4020)^+$",
           "Z_c(4430)+": r"$Z_c(4430)^+$", "Z_cs(3985)+": r"$Z_{cs}(3985)^+$", "Z_cs(4000)+": r"$Z_{cs}(4000)^+$",
           "Z_cs(4220)+": r"$Z_{cs}(4220)^+$", "chi_c1(4140)": r"$\chi_{c1}(4140)$", "chi_c1(4274)": r"$\chi_{c1}(4274)$",
           "chi_c0(4500)": r"$\chi_{c0}(4500)$", "chi_c0(4700)": r"$\chi_{c0}(4700)$", "X(4685)": r"$X(4685)$", "X(4630)": r"$X(4630)$",
           "X(3960)": r"$X(3960)$", "psi(4230)": r"$\psi(4230)$", "Z_b(10610)+": r"$Z_b(10610)^+$", "Z_b(10650)+": r"$Z_b(10650)^+$",
           "T_cc(3875)+": r"$T_{cc}(3875)^+$", "X0(2900)": r"$X_0(2900)$", "X1(2900)": r"$X_1(2900)$",
           "T_csbar0(2900)++": r"$T_{c\bar s0}(2900)^{++}$", "P_c(4312)+": r"$P_c(4312)^+$", "P_c(4440)+": r"$P_c(4440)^+$",
           "P_c(4457)+": r"$P_c(4457)^+$", "P_psis(4338)0": r"$P_{\psi s}(4338)^0$", "X(6900)": r"$X(6900)$"}


def state_qn(c):
    return {"fv": flavour_vector(c[7]), "J": None if c[4] is None else Fraction(c[4]), "P": c[5], "C": c[6]}


def proximity(c, hadrons, W):
    thr = thresholds_for(state_qn(c), hadrons)
    ms = np.array([t[0] for t in thr])
    d_signed = c[1] - ms
    k = int(np.argmin(np.abs(d_signed)))
    d = abs(d_signed[k])
    p = interval_cover([(t - d, t + d) for t in ms], c[1] - W, c[1] + W) / (2 * W)
    n_win = int(np.sum(np.abs(ms - c[1]) <= W))
    return {"nearest": thr[k][1], "T": float(ms[k]), "d": float(d_signed[k]), "p": float(p), "n_window": n_win,
            "nearest_verified": bool(thr[k][2]), "thresholds": ms}


THR = {}
for c in CATALOGUE:
    THR[c[0]] = {"main": proximity(c, HADRONS, W_MAIN), "alt": proximity(c, HADRONS, W_ALT)}
    t = THR[c[0]]["main"]
    print(f"  {c[0]:<18s} M {c[1]:8.1f}  nearest {t['nearest']:<26s} {t['T']:8.1f}  M-T {t['d']:+7.1f}  p {t['p']:.3f}  "
          f"(n in window {t['n_window']}, threshold masses verified: {t['nearest_verified']})")

rng = np.random.default_rng(SEED)
mc_ok = True
for c in CATALOGUE:
    t = THR[c[0]]["main"]
    x = rng.uniform(c[1] - W_MAIN, c[1] + W_MAIN, N_MC)
    dd = np.min(np.abs(x[:, None] - t["thresholds"][None, :]), axis=1)
    pm = float(np.mean(dd <= abs(t["d"])))
    tol = 4.5 * math.sqrt(max(t["p"] * (1 - t["p"]), 1.0 / N_MC) / N_MC) + 1e-12
    mc_ok &= abs(pm - t["p"]) <= tol
check_true(f"B1 analytic null p-values agree with {N_MC} Monte Carlo placements per state (4.5 sigma)", mc_ok)


def fisher(ps):
    X = -2.0 * float(np.sum(np.log(ps)))
    return X, float(stats.chi2.sf(X, 2 * len(ps)))


P_MAIN = np.array([THR[c[0]]["main"]["p"] for c in CATALOGUE])
P_ALT = np.array([THR[c[0]]["alt"]["p"] for c in CATALOGUE])
FISH_MAIN, FISH_ALT = fisher(P_MAIN), fisher(P_ALT)
check("B2 Fisher statistic equals -2 sum ln p (consistency of chi2 tail)", stats.chi2.sf(FISH_MAIN[0], 2 * len(P_MAIN)),
      FISH_MAIN[1], 1e-15)
N_CLOSE = {d: int(sum(abs(THR[c[0]]["main"]["d"]) <= d for c in CATALOGUE)) for d in (5.0, 10.0, 20.0)}


def expected_close(dmax):
    tot = 0.0
    for c in CATALOGUE:
        ms = THR[c[0]]["main"]["thresholds"]
        tot += interval_cover([(t - dmax, t + dmax) for t in ms], c[1] - W_MAIN, c[1] + W_MAIN) / (2 * W_MAIN)
    return tot


EXP_CLOSE = {d: expected_close(d) for d in (5.0, 10.0, 20.0)}
P_CLOSE = {d: float(stats.poisson.sf(N_CLOSE[d] - 1, EXP_CLOSE[d])) for d in (5.0, 10.0, 20.0)}
N_BELOW = int(sum(THR[c[0]]["main"]["d"] < 0 for c in CATALOGUE))
MEAN_NWIN = float(np.mean([THR[c[0]]["main"]["n_window"] for c in CATALOGUE]))
# B4: robustness to the threshold masses not re-read: perturb each by a Gaussian of 1 MeV (and 3 MeV), recompute
pert = {}
for sd in (1.0, 3.0):
    rngp = np.random.default_rng(SEED + int(sd))
    fs = []
    for _ in range(N_PERTURB):
        tab = [(nm, m + (0.0 if ver else rngp.normal(0, sd)), w, J, P, C, ct, ver) for (nm, m, w, J, P, C, ct, ver) in THRESH_HADRONS]
        hs = hadron_list(tab)
        ps = np.array([proximity(c, hs, W_MAIN)["p"] for c in CATALOGUE])
        fs.append(fisher(ps)[1])
    pert[sd] = (float(np.min(fs)), float(np.median(fs)), float(np.max(fs)))
# B7: distances below the measurement error are not resolved: replace |M - T| by max(|M - T|, sigma_M)
def proximity_floor(c, W):
    t = THR[c[0]]["main"]
    d = max(abs(t["d"]), c[2])
    return interval_cover([(x - d, x + d) for x in t["thresholds"]], c[1] - W, c[1] + W) / (2 * W)


FISH_FLOOR = fisher(np.array([proximity_floor(c, W_MAIN) for c in CATALOGUE]))
# B5: the same test on the subset of states whose J^P is measured (no free choice of partial wave)
KNOWN_JP = [c for c in CATALOGUE if c[4] is not None and c[5] is not None]
FISH_KNOWN = fisher(np.array([THR[c[0]]["main"]["p"] for c in KNOWN_JP]))
# B6: leave out the states that sit within 1 MeV of a threshold (T_cc, X(3872)), the clearest cases
FAR = [c for c in CATALOGUE if abs(THR[c[0]]["main"]["d"]) > 1.0]
FISH_FAR = fisher(np.array([THR[c[0]]["main"]["p"] for c in FAR]))
print(f"  Fisher (W=150): X2 = {FISH_MAIN[0]:.1f} for {2 * len(P_MAIN)} dof, p = {FISH_MAIN[1]:.2e};  W=300: p = {FISH_ALT[1]:.2e}")
print(f"  within 5/10/20 MeV: {N_CLOSE[5.0]}/{N_CLOSE[10.0]}/{N_CLOSE[20.0]} observed, {EXP_CLOSE[5.0]:.2f}/{EXP_CLOSE[10.0]:.2f}/"
      f"{EXP_CLOSE[20.0]:.2f} expected; below threshold: {N_BELOW} of {len(CATALOGUE)}; mean thresholds per window {MEAN_NWIN:.1f}")
print(f"  perturbed unverified masses: 1 MeV -> p in [{pert[1.0][0]:.1e}, {pert[1.0][2]:.1e}], 3 MeV -> [{pert[3.0][0]:.1e}, "
      f"{pert[3.0][2]:.1e}];  measured-J^P subset ({len(KNOWN_JP)}): p = {FISH_KNOWN[1]:.2e};  without the two <1 MeV states: "
      f"p = {FISH_FAR[1]:.2e};  distances floored at sigma_M: p = {FISH_FLOOR[1]:.2e}")


# =====================================================================================================================================
# Section C: partners
# =====================================================================================================================================
print("[C] partners (results)")
ROW = {r["label"]: r for r in ITEMS}
_xc = ROW["compact X(3872): [cq][cbar qbar] 1++"]
_zc = ROW["compact Z_c(3900): [cq][cbar qbar] 1+-"]
_tI1 = [ROW[f"T_cc partner I=1, J={J}"] for J in (0, 1, 2)]
_bI1 = [ROW[f"T_bb partner I=1, J={J}"] for J in (0, 1, 2)]
_pc_levels = sorted(spectrum("Pc", PFIT, "P"))
_pc_I32 = [t for t in _pc_levels if CFG["Pc"][t[1]].asgs[0][(2, 3)] == 1]
PARTNERS = [
    {"id": "C1", "prediction": "compact (diquark-tree) X(3872) = [cq][cbar qbar] 1++ has charged isospin partners X+- at about the "
           "X(3872) mass, produced in B -> X- K at twice the neutral rate (Maiani et al. 2005; the isovector hypothesis of BaBar)",
     "search": "BaBar: B(B0 -> X- K+, X- -> J/psi pi- pi0) < 5.4e-6 (90% CL) where 2.56e-5 (75+-25 events) was expected; likelihood "
               "ratio 1.1e4 for no signal. Belle: limits well below the isospin-triplet expectation",
     "sources": ["MPPR2005", "BaBar_Xminus", "Belle_X3872"], "verdict": "refuted (failed prediction of the compact X(3872) reading)"},
    {"id": "C2", "prediction": f"our model's compact 1++ isomultiplet (I = 0 and 1 degenerate) at {_xc['P']['M']:.0f} +- "
           f"{_xc['P']['err']:.0f} MeV, {_xc['P']['M'] - _xc['data']['M']:.0f} MeV above X(3872): the model does not make X(3872) "
           "compact; its charged 1++ partners lie near 4.1 GeV",
     "search": "no search for a charged C = + (G = -) hidden-charm state near 4.1 GeV verified", "sources": [],
     "verdict": "untested"},
    {"id": "C3", "prediction": "T_cc isospin partners [cc]_1[qbar qbar]_1 (I = 1) with J = 0, 1, 2 at "
           + ", ".join(f"{r['P']['M']:.0f}" for r in _tI1) + " MeV, i.e. "
           + ", ".join(f"{r['P']['binding']:+.0f}" for r in _tI1) + " MeV above their lowest S-wave thresholds (open, so broad); "
           "no isoscalar spin partner (a good antidiquark has spin 0)",
     "search": "LHCb: no narrow signal in D+ D0 pi+ (3.9-4.0 GeV) or D+ D+ (up to 3.87 GeV); the isovector reading of T_cc+ itself "
               "is disfavoured. The predicted I = 1 states lie above these windows and would be broad",
     "sources": ["LHCb_Tcc_NC"], "verdict": "consistent (the model's T_cc+ is isoscalar); the I = 1 partners are untested"},
    {"id": "C4", "prediction": "T_bb isospin partners (I = 1) with J = 0, 1, 2 at " + ", ".join(f"{r['P']['M']:.0f}" for r in _bI1)
           + " MeV, " + ", ".join(f"{r['P']['binding']:+.0f}" for r in _bI1) + " MeV from their lowest S-wave thresholds",
     "search": "none (no doubly bottom hadron observed)", "sources": [], "verdict": "live"},
    {"id": "C5", "prediction": f"hidden-charm pentaquark multiplet: {len(_pc_levels)} S-wave levels with I = 1/2 from "
           f"{_pc_levels[0][0]:.0f} to {_pc_levels[-1][0]:.0f} MeV, and I = 3/2 partners degenerate with the {len(_pc_I32)} levels "
           "that contain a spin-1 light diquark",
     "search": "LHCb Lambda_b -> J/psi p K- shows three narrow peaks; no search for I = 3/2 (doubly charged) hidden-charm "
               "pentaquarks verified; production in Lambda_b decay favours the spin-0 [ud] diquark (MPR 2015), so absent peaks "
               "do not exclude partners", "sources": ["LHCb_Pc2019", "MPR2015"], "verdict": "untested"},
    {"id": "C6", "prediction": "fully charmed S-wave triplet 0++, 1+-, 2++ at "
           + ", ".join(f"{t[0]:.0f}" for t in sorted(spectrum('cccc', PFIT, 'P'), key=lambda t: t[3]))
           + " MeV; the 1+- cannot decay to J/psi J/psi",
     "search": "di-J/psi structures of LHCb, CMS, ATLAS (Table of Section A); no 1+- channel searched", "sources":
         ["LHCb_X6900", "CMS_diJpsi", "ATLAS_diJpsi"], "verdict": "the S-wave triplet is not X(6900) (Section A); untested otherwise"},
    {"id": "C7", "prediction": f"X0(2900) partner [ud]_0[cbar sbar]_1 with J^P = 1+ at {ROW['X0 partner [ud]0[cbar sbar]1, 1+']['P']['M']:.0f}"
           " MeV", "search": "a 1+ state cannot decay to D- K+ (two pseudoscalars); not visible in the LHCb analysis",
     "sources": ["LHCb_X2900"], "verdict": "untested"},
]
for pt in PARTNERS:
    print(f"  {pt['id']}: {pt['verdict']}")


# lattice QCD for the live doubly heavy states (binding = mass minus the lowest S-wave threshold; comparison only, not a verdict)
LATTICE = {
    "T_bb- (bb ubar dbar)": [("Francis2017", -189.0, 10.0, 10.0), ("Leskovec2019", -128.0, math.hypot(24, 10), math.hypot(24, 10)),
                             ("Aoki2023", -83.0, math.hypot(10, 20), math.hypot(10, 20)), ("Hudspith2023", -112.0, 13.2, 13.2),
                             ("Tripathy2025", -116.0, 36.0, 30.0)],
    "T_bc (bc ubar dbar), 1+": [("Francis2019", -38.0, 23.0, 23.0), ("Padmanath2024", -43.0, math.hypot(7, 24), math.hypot(6, 14))],
    "T_bc (bc ubar dbar), 0+": [],
}
for lab, lst in LATTICE.items():
    row = ROW[lab]
    row["lattice"] = []
    for (src, bnd, elo, ehi) in lst:
        e = ehi if row["P"]["binding"] > bnd else elo
        z = (row["P"]["binding"] - bnd) / math.hypot(row["P"]["err"], e)
        row["lattice"].append({"source": src, "binding": bnd, "err_lo": elo, "err_hi": ehi, "pull_P": z})
ROW["T_bc (bc ubar dbar), 0+"]["lattice_note"] = "Alexandrou2024: shallow bound or virtual states a few MeV or less below the " \
                                                 "B(*) Dbar thresholds (no number in the abstract)"
for lab in LATTICE:
    print(f"  {lab}: model binding {ROW[lab]['P']['binding']:+.1f} +- {ROW[lab]['P']['err']:.1f}; lattice pulls "
          + ", ".join(f"{d['source']} {d['binding']:+.0f} ({d['pull_P']:+.1f})" for d in ROW[lab]["lattice"]))

# =====================================================================================================================================
# Figures (print size: 6.3 in full width, 3.1 in half width; text 8 to 9 pt)
# =====================================================================================================================================
COL = {"P": "#2a78d6", "P-in": "#eb6834", "J": "#1baf7a"}       # validated categorical slots 1-3 (dataviz reference palette)
MRK = {"P": "o", "P-in": "s", "J": "^"}
LBL = {"P": "model (KR masses)", "P-in": "variant P-in", "J": "variant J (junctions)"}


def figures():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    plt.rcParams.update({"pdf.fonttype": 42, "font.size": 8, "axes.labelsize": 8.5, "legend.fontsize": 7.5, "xtick.labelsize": 8,
                         "ytick.labelsize": 8, "axes.linewidth": 0.6, "xtick.major.width": 0.6, "ytick.major.width": 0.6,
                         "xtick.minor.width": 0.5, "ytick.minor.width": 0.5, "xtick.major.size": 3, "ytick.major.size": 3,
                         "xtick.minor.size": 1.5, "ytick.minor.size": 1.5, "xtick.direction": "in", "ytick.direction": "in",
                         "xtick.top": True, "ytick.right": True, "lines.linewidth": 1.0, "legend.handlelength": 1.6,
                         "legend.borderaxespad": 0.3, "legend.labelspacing": 0.3, "savefig.bbox": None})
    FIGURES.mkdir(parents=True, exist_ok=True)
    meta = {"CreationDate": None, "ModDate": None, "Producer": None, "Creator": None}
    INK, MUTED, GRID = "#0b0b0b", "#52514e", "#d9d8d4"

    def new_fig(w, h, ncols=1, **kw):
        fig, axs = plt.subplots(1, ncols, figsize=(w, h), layout="constrained", **kw)
        fig.get_layout_engine().set(w_pad=0.02, h_pad=0.02, wspace=0.04)
        return fig, axs

    # --- fit residuals
    fig, ax = new_fig(3.1, 2.55)
    res = FIT["P"]["res"]
    isb = np.array([ORD[n].n == 3 for n in FIT_NAMES])
    ax.axhspan(-SIG, SIG, color=GRID, lw=0, zorder=0)
    ax.axhline(0, color=MUTED, lw=0.6, zorder=1)
    ax.plot(FIT_M[~isb], res[~isb], "o", ms=4, mfc=COL["P"], mec="white", mew=0.5, label="mesons", zorder=3)
    ax.plot(FIT_M[isb], res[isb], "s", ms=4, mfc=COL["P-in"], mec="white", mew=0.5, label="baryons", zorder=3)
    lo_m = np.array([FIT_M[i] for i, n in enumerate(FIT_NAMES) if n in loo])
    lo_r = np.array([loo[n] for n in FIT_NAMES if n in loo])
    ax.plot(lo_m, lo_r, "o", ms=4.5, mfc="none", mec=MUTED, mew=0.6, label="left out of the fit", zorder=2)
    ax.errorbar([XICC[0]], [_xicc[0] - XICC[0]], yerr=[_xicc[1]], fmt="D", ms=4.5, color=INK, mfc=COL["J"], mec=INK, mew=0.6,
                capsize=2, lw=0.8, label=r"$\Xi_{cc}^{++}$ (held out)", zorder=4)
    for n in ("Sigma", "Delta", "D", "D*", "K", "Xi_b"):
        i = FIT_NAMES.index(n)
        lab = {"Sigma": r"$\Sigma$", "Delta": r"$\Delta$", "D": "$D$", "D*": "$D^*$", "K": "$K$", "Xi_b": r"$\Xi_b$"}[n]
        ax.annotate(lab, (FIT_M[i], res[i]), xytext=(3, 0), textcoords="offset points", fontsize=7, color=MUTED, va="center")
    ax.set_xscale("log")
    ax.set_xlim(100, 12000)
    ax.set_ylim(-34, 34)
    ax.set_xlabel("hadron mass [MeV]")
    ax.set_ylabel("model $-$ measured [MeV]")
    ax.legend(loc="lower left", ncol=2, frameon=False, columnspacing=0.8, handletextpad=0.3)
    ax.text(0.98, 0.95, rf"$\sigma_{{\rm model}}={SIG:.1f}$ MeV", transform=ax.transAxes, ha="right", va="top", fontsize=7.5)
    fig.savefig(FIGURES / "exotic_fit.pdf", metadata=meta)
    plt.close(fig)

    # --- scored confrontations and live doubly heavy bindings
    fig, (ax1, ax2) = new_fig(6.3, 2.9, 2, gridspec_kw={"width_ratios": [1.7, 1]})
    scored = [r for r in ITEMS if r["kind"] == "scored"]
    names = {"T_cc+ (cc ubar dbar)": r"$T_{cc}^+$", "X0(2900) (ud cbar sbar)": r"$X_0(2900)$",
             "T_csbar0(2900) (c sbar u dbar)": r"$T_{c\bar s}(2900)$", "cc cbar cbar 2++ vs X(6900)": r"$X(6900)$",
             "P_c(4312) (lowest uud c cbar)": r"$P_c(4312)$", "P_c(4440) (nearest level)": r"$P_c(4440)^\dagger$",
             "P_c(4457) (nearest level)": r"$P_c(4457)^\dagger$", "P_psis(4338) (lowest I=0, J=1/2)": r"$P_{\psi s}(4338)$",
             "P_cs(4459) (nearest level; evidence only)": r"$P_{cs}(4459)^\dagger$"}
    y = np.arange(len(scored))[::-1]
    ax1.axvline(0, color=MUTED, lw=0.6)
    for k, sch in enumerate(("P", "P-in", "J")):
        dx = [r[sch]["M"] - r["data"]["M"] for r in scored]
        if sch == "P":
            ex = [math.hypot(r["P"]["err"], err_toward(r["P"]["M"], (r["data"]["M"], r["data"]["err_lo"], r["data"]["err_hi"])))
                  for r in scored]
            ax1.errorbar(dx, y + 0.18, xerr=ex, fmt=MRK[sch], ms=4.5, color=COL[sch], mec="white", mew=0.4, lw=0.9, capsize=1.5,
                         label=LBL[sch] + r" $\pm1\sigma$", zorder=3)
        else:
            ax1.plot(dx, y + (0.0 if sch == "P-in" else -0.18), MRK[sch], ms=4, color=COL[sch], mec="white", mew=0.4,
                     label=LBL[sch], zorder=3)
    ax1.set_yticks(y)
    ax1.set_yticklabels([names[r["label"]] for r in scored])
    ax1.set_xscale("symlog", linthresh=30)
    ax1.set_xlim(-650, 380)
    ax1.set_xticks([-300, -100, -30, 0, 30, 100, 300])
    ax1.set_xticklabels(["$-300$", "$-100$", "$-30$", "0", "30", "100", "300"])
    ax1.set_xlabel("model $-$ measured mass [MeV] (linear within $\\pm30$)")
    ax1.legend(loc="lower center", bbox_to_anchor=(0.5, 1.0), ncol=3, frameon=False, fontsize=7, columnspacing=0.8,
               handletextpad=0.3)
    ax1.set_ylim(-0.6, len(scored) - 0.4)
    # right panel: doubly heavy binding energies
    live = ["T_cc+ (cc ubar dbar)", "T_bc (bc ubar dbar), 0+", "T_bc (bc ubar dbar), 1+", "T_bb- (bb ubar dbar)"]
    lab2 = [r"$T_{cc}$ $1^+$", r"$T_{bc}$ $0^+$", r"$T_{bc}$ $1^+$", r"$T_{bb}$ $1^+$"]
    kr = {"T_cc+ (cc ubar dbar)": 3882.2 - 3875.09, "T_bc (bc ubar dbar), 0+": 7133.7 - 7144.5,
          "T_bb- (bb ubar dbar)": 10389.4 - 10604.0}
    ax2.axhline(0, color=MUTED, lw=0.6)
    for i, lab in enumerate(live):
        r = ROW[lab]
        ax2.errorbar([i - 0.12], [r["P"]["binding"]], yerr=[r["P"]["err"]], fmt="o", ms=4.5, color=COL["P"], mec="white", mew=0.4,
                     lw=0.9, capsize=1.5, label=LBL["P"] if i == 0 else None, zorder=3)
        ax2.plot([i - 0.12], [r["J"]["binding"]], "^", ms=4, color=COL["J"], mec="white", mew=0.4,
                 label=LBL["J"] if i == 0 else None, zorder=3)
        if lab in kr:
            ax2.plot([i + 0.02], [kr[lab]], "x", ms=4.5, color=INK, mew=0.9, label="KR 2017" if i == 0 else None, zorder=3)
        for j, d in enumerate(r.get("lattice", [])):
            ax2.errorbar([i + 0.12 + 0.05 * j], [d["binding"]], yerr=[[d["err_lo"]], [d["err_hi"]]], fmt="s", ms=3, color=MUTED,
                         mfc="white", mew=0.7, lw=0.7, capsize=1, label="lattice QCD" if (i == 2 and j == 0) else None, zorder=2)
    ax2.plot([0 + 0.02], [-0.36], "*", ms=6, color=INK, label="LHCb (measured)", zorder=4)
    ax2.set_xticks(range(len(live)))
    ax2.set_xticklabels(lab2)
    ax2.set_xlim(-0.5, 3.6)
    ax2.set_ylabel("mass $-$ lowest S-wave threshold [MeV]")
    ax2.legend(loc="lower left", frameon=False, fontsize=6.8, handletextpad=0.3)
    ax2.set_ylim(-260, 140)
    fig.savefig(FIGURES / "exotic_spectrum.pdf", metadata=meta)
    plt.close(fig)

    # --- level diagrams: P_c, udsc cbar, cc cbar cbar
    fig, axs = new_fig(6.3, 3.0, 3)

    def draw_levels(ax, lv, xpos, color, lw=1.4):
        for (m, x) in zip(lv, xpos):
            ax.plot([x - 0.3, x + 0.3], [m, m], color=color, lw=lw, solid_capstyle="butt")

    ax = axs[0]
    for t in spectrum("Pc", PFIT, "P"):
        s = CFG["Pc"][t[1]].asgs[0][(2, 3)]
        x = {Hh: 0, H3: 1, H5: 2}[t[3]] + (-0.17 if s == 0 else 0.17)
        ax.plot([x - 0.14, x + 0.14], [t[0], t[0]], color=COL["P"] if s == 0 else COL["P-in"], lw=1.6, solid_capstyle="butt")
    for m, nm, va in ((4311.9, "4312", "center"), (4440.3, "4440", "top"), (4457.3, "4457", "bottom")):
        ax.axhline(m, color=INK, lw=0.8, ls="-", zorder=0)
        ax.text(2.55, m, nm, fontsize=6.5, va=va, ha="left", color=INK)
    for m, nm, va in ((2452.65 + 1864.84, r"$\Sigma_c\bar D$", "bottom"), (2452.65 + 2006.85, r"$\Sigma_c\bar D^*$", "bottom"),
                      (2517.4 + 1864.84, r"$\Sigma_c^*\bar D$", "bottom")):
        ax.axhline(m, color=MUTED, lw=0.6, ls=(0, (3, 2)), zorder=0)
        ax.text(-0.55, m + 2, nm, fontsize=6.3, va=va, ha="left", color=MUTED)
    ax.set_xticks([0, 1, 2])
    ax.set_xticklabels(["1/2", "3/2", "5/2"])
    ax.set_xlim(-0.6, 2.95)
    ax.set_xlabel("$J$ (parity $-$)")
    ax.set_ylabel("mass [MeV]")
    ax.set_title(r"$uudc\bar c$: $([cq][qq])\bar c$", fontsize=8)
    ax.plot([], [], color=COL["P"], lw=1.6, label="light diquark spin 0")
    ax.plot([], [], color=COL["P-in"], lw=1.6, label="light diquark spin 1")
    ax.legend(loc="lower right", frameon=False, fontsize=6.3)
    ax.set_ylim(4230, 4640)

    ax = axs[1]
    for fam, col, dx in (("Ppsis_A", COL["P"], -0.17), ("Ppsis_B", COL["P-in"], 0.17)):
        for t in spectrum(fam, PFIT, "P"):
            x = {Hh: 0, H3: 1, H5: 2}[t[3]] + dx
            ax.plot([x - 0.14, x + 0.14], [t[0], t[0]], color=col, lw=1.6, solid_capstyle="butt")
    for m, nm in ((4338.2, "4338"), (4458.8, "4459")):
        ax.axhline(m, color=INK, lw=0.8, zorder=0)
        ax.text(2.55, m, nm, fontsize=6.5, va="center", ha="left")
    for m, nm in ((2467.71 + 1869.66, r"$\Xi_c\bar D$"), (2467.71 + 2010.26, r"$\Xi_c\bar D^*$")):
        ax.axhline(m, color=MUTED, lw=0.6, ls=(0, (3, 2)), zorder=0)
        ax.text(-0.55, m + 3, nm, fontsize=6.3, va="bottom", ha="left", color=MUTED)
    ax.set_xticks([0, 1, 2])
    ax.set_xticklabels(["1/2", "3/2", "5/2"])
    ax.set_xlim(-0.6, 2.95)
    ax.set_xlabel("$J$ (parity $-$)")
    ax.set_title(r"$udsc\bar c$, $I=0$", fontsize=8)
    ax.plot([], [], color=COL["P"], lw=1.6, label=r"$([cs][ud]_0)\bar c$")
    ax.plot([], [], color=COL["P-in"], lw=1.6, label=r"$([cq][qs])\bar c$")
    ax.legend(loc="lower right", frameon=False, fontsize=6.3)
    ax.set_ylim(4280, 4700)

    ax = axs[2]
    for sch, dx in (("P", -0.2), ("P-in", 0.0), ("J", 0.2)):
        for t in spectrum("cccc", FIT["J"]["P"] if sch == "J" else PFIT, sch):
            x = int(t[3]) + dx
            ax.plot([x - 0.08, x + 0.08], [t[0], t[0]], color=COL[sch], lw=1.6, solid_capstyle="butt")
        ax.plot([], [], color=COL[sch], lw=1.6, label=LBL[sch])
    for m, e, nm in ((6905, 13, "LHCb"), (6552, 16, "CMS"), (6927, 10, "CMS"), (7287, 20, "CMS"), (6410, 89, "ATLAS"),
                     (6630, 66, "ATLAS"), (6860, 33, "ATLAS")):
        x = {"LHCb": 2.55, "CMS": 2.75, "ATLAS": 2.95}[nm]
        ax.errorbar([x], [m], yerr=[e], fmt={"LHCb": "*", "CMS": "D", "ATLAS": "s"}[nm], ms=4, color=INK, mfc="white"
                    if nm != "LHCb" else INK, mew=0.7, lw=0.7, capsize=1.2)
    for nm, mk in (("LHCb", "*"), ("CMS", "D"), ("ATLAS", "s")):
        ax.plot([], [], mk, ms=4, color=INK, mfc=INK if nm == "LHCb" else "white", mew=0.7, label=nm)
    ax.axhline(2 * 3096.9, color=MUTED, lw=0.6, ls=(0, (3, 2)))
    ax.text(-0.45, 2 * 3096.9 + 6, r"$J/\psi J/\psi$", fontsize=6.3, color=MUTED, va="bottom")
    ax.set_xticks([0, 1, 2, 2.75])
    ax.set_xticklabels(["$0^{++}$", "$1^{+-}$", "$2^{++}$", "data"])
    ax.set_xlim(-0.5, 3.15)
    ax.set_ylim(6150, 7350)
    ax.set_title(r"$cc\bar c\bar c$: $[cc]_1[\bar c\bar c]_1$", fontsize=8)
    ax.legend(loc="upper left", bbox_to_anchor=(0.0, 0.97), frameon=False, fontsize=6.0, ncol=1, handletextpad=0.3)
    fig.savefig(FIGURES / "exotic_levels.pdf", metadata=meta)
    plt.close(fig)

    # --- threshold proximity
    fig, (ax1, ax2) = new_fig(6.3, 2.75, 2, gridspec_kw={"width_ratios": [1.45, 1]})
    order = sorted(CATALOGUE, key=lambda c: abs(THR[c[0]]["main"]["d"]))
    dd = np.array([abs(THR[c[0]]["main"]["d"]) for c in order])
    yy = np.arange(len(order))[::-1]
    # median null distance for each state (half the window covered)
    med = []
    for c in order:
        ms = THR[c[0]]["main"]["thresholds"]
        f = lambda d, ms=ms, m=c[1]: interval_cover([(t - d, t + d) for t in ms], m - W_MAIN, m + W_MAIN) / (2 * W_MAIN) - 0.5  # noqa
        med.append(optimize.brentq(f, 1e-6, 2000.0))
    ax1.barh(yy, np.maximum(dd, 0.03), height=0.55, color=COL["P"], lw=0, label="measured distance")
    ax1.plot(med, yy, "|", ms=6, mew=1.2, color=INK, label="median under the null")
    ax1.set_xscale("log")
    ax1.set_xlim(0.03, 600)
    ax1.set_yticks(yy)
    ax1.set_yticklabels([TEXNAME[c[0]] for c in order], fontsize=6.2)
    ax1.set_xlabel("|mass $-$ nearest allowed S-wave threshold| [MeV]")
    ax1.legend(loc="lower center", bbox_to_anchor=(0.5, 1.0), ncol=2, frameon=False, fontsize=6.8)
    ax1.set_ylim(-0.7, len(order) - 0.3)
    ps = np.sort(P_MAIN)
    n = len(ps)
    ax2.plot([0, 1], [0, 1], color=MUTED, lw=0.8, ls=(0, (3, 2)), label="null (uniform)")
    ax2.step(np.concatenate([[0], ps, [1]]), np.concatenate([[0], np.arange(1, n + 1) / n, [1]]), where="post", color=COL["P"],
             lw=1.3, label=rf"catalogue, $W={W_MAIN:.0f}$ MeV")
    ps2 = np.sort(P_ALT)
    ax2.step(np.concatenate([[0], ps2, [1]]), np.concatenate([[0], np.arange(1, n + 1) / n, [1]]), where="post", color=COL["P-in"],
             lw=1.0, ls="-", label=rf"$W={W_ALT:.0f}$ MeV")
    ax2.set_xlabel("per-state $p_i$")
    ax2.set_ylabel(r"fraction of states with $p \leq p_i$")
    ax2.set_xlim(0, 1)
    ax2.set_ylim(0, 1)
    ax2.legend(loc="lower right", frameon=False, fontsize=6.8)
    ax2.text(0.04, 0.95, f"Fisher: $p$ = {FISH_MAIN[1]:.1e} (W = 150)\n            $p$ = {FISH_ALT[1]:.1e} (W = 300)",
             transform=ax2.transAxes, fontsize=6.8, va="top")
    fig.savefig(FIGURES / "exotic_thresholds.pdf", metadata=meta)
    plt.close(fig)


figures()


# =====================================================================================================================================
# Section I: Hypothesis H9, the minting in hadrons (SM7 of sm_preregistration.md, fixed after the SM6 results and before this block).
# A pentaquark is a minting: a bound triple of colour-bearers plus a quark and its own antiquark (a pair of one flavour).
# Honesty note (SM7): H9 was conceived after seeing that every established pentaquark carries c cbar, so those states are not
# evidence for it.
#   I1 (P1) no open flavour: every claimed pentaquark, hidden versus open flavour, crossed with established versus not; Fisher's
#      exact test (one-sided: open-flavour claims less often established).
#   I2 (P2) hidden bottom: masses from heavy-quark flavour symmetry (molecular: the binding energies of P_c(4312), P_c(4440),
#      P_c(4457) and P_psis(4338) relative to isospin-averaged Sigma_c Dbar(*) and Xi_c Dbar thresholds carried over unchanged to
#      Sigma_b B(*) and Xi_b B; variant: binding scaled with the reduced mass) and the colour-spin model's compact levels; live
#      unless a search excludes them.
#   I3 (P3) the general rule "every exotic hadron contains a pair of one flavour" against the SM6 catalogue.
#   I4 (P4) the splitting rule Delta M = alpha M / 2 for spin doublets. Eligibility is decided from quark content and J^P only and
#      the list I4_ELIGIBLE below was written before any splitting was computed (the masses of these states were known from SM6):
#      two exotic states with the same quark content (isospin partners counted as one), each reported as an observation, with equal
#      or unknown parity and |J1 - J2| <= 1 (unknown J allowed); P_c(4440)/P_c(4457), which suggested the rule, excluded; states
#      reported only as evidence, or as an unresolved two-peak hypothesis, are not resolved. A pair passes if |Delta - alpha M/2| <
#      2 sigma_Delta. Look-elsewhere: under a null with Delta uniform in [0, 300] MeV a pair passes by chance with probability
#      p_k = |[alpha M/2 - 2 sigma, alpha M/2 + 2 sigma] cap [0, 300]| / 300; the observed number of passes is compared with sum p_k.
#      QCD baseline: the colour-spin model's splitting of the same two S-wave levels where the model has such a pair.
# =====================================================================================================================================
print("[I] Hypothesis H9, the minting in hadrons (results, not checks)")
ALPHA = 1.0 / 137.035999177                  # CODATA 2022, as in predictions_vs_data.py
CITATIONS.update({
    "LEPS2003": {"ref": "T. Nakano et al. (LEPS), Phys. Rev. Lett. 91, 012002 (2003), hep-ex/0301020", "read": "abstract",
                 "values": "S=+1 baryon (Theta+) at 1.54+-0.01 GeV, width < 25 MeV, 4.6 sigma"},
    "CLAS2006": {"ref": "B. McKinnon, K. Hicks et al. (CLAS), Phys. Rev. Lett. 96, 212001 (2006), hep-ex/0603028", "read": "abstract",
                 "values": "no evidence for a narrow pentaquark with more than 30 times the luminosity of the earlier measurement; "
                           "sigma(gamma d -> p K- Theta+) < 0.3 nb (95% CL), 1.52-1.56 GeV"},
    "HERAB2004": {"ref": "K. T. Knoepfle, M. Zavertyaev, T. Zivko for HERA-B, J. Phys. G 30, S1363 (2004), hep-ex/0403020",
                  "read": "abstract", "values": "no evidence for Theta+(1540) or Xi--(1862); Theta+/Lambda(1520) < 0.02, "
                                                "Br x Xi--/Xi(1530)0 < 0.077 (95% CL)"},
    "NA49_2004": {"ref": "NA49, Phys. Rev. Lett. 92, 042003 (2004), hep-ex/0310014", "read": "abstract",
                  "values": "S=-2, Q=-2 baryon at 1.862+-0.002 GeV, width below 0.018 GeV, 4.0 sigma"},
    "H1_2004": {"ref": "H1, Phys. Lett. B 588, 17 (2004), hep-ex/0403017", "read": "abstract",
                "values": "anti-charmed baryon uuddcbar at 3099+-3+-5 MeV, Gaussian width 12+-3 MeV"},
    "ZEUS2004": {"ref": "ZEUS, Eur. Phys. J. C 38, 29 (2004), hep-ex/0409033", "read": "abstract",
                 "values": "no resonance in D*p with more than 60000 D*; not compatible with the H1 report"},
    "LHCb_Pc2015": {"ref": "LHCb, Phys. Rev. Lett. 115, 072001 (2015), arXiv:1507.03414", "read": "abstract",
                    "values": "4380+-8+-29 (Gamma 205+-18+-86) and 4449.8+-1.7+-2.5 (Gamma 39+-5+-19), each above 9 sigma"},
    "LHCb_Pc4337": {"ref": "LHCb, Phys. Rev. Lett. 128, 062001 (2022), arXiv:2108.04720", "read": "abstract",
                    "values": "evidence: 4337(+7-4)(+2-2), Gamma 29(+26-12)(+14-14), 3.1 to 3.7 sigma"},
    "LHCb_Pcs4459_text": {"ref": "LHCb, Sci. Bull. 66, 1278 (2021), arXiv:2012.10380", "read": "full text, Sec. 4 and 5",
                          "values": "3.1 sigma including systematics and look-elsewhere; two-peak fit 4454.9+-2.7 (Gamma 7.5+-9.7) and "
                                    "4467.8+-3.7 (Gamma 5.2+-5.3), statistical only; 'cannot confirm or refute the two-peak "
                                    "hypothesis'"},
    "LHCb_Pc2019_text": {"ref": "LHCb, Phys. Rev. Lett. 122, 222001 (2019), arXiv:1904.03947", "read": "full text",
                         "values": "verification of the P_c(4380)+ state awaits an amplitude analysis"},
    "LHCb_LcDs2025": {"ref": "LHCb, Phys. Rev. D 112, 052013 (2025), arXiv:2507.10713", "read": "abstract",
                      "values": "no evidence for P_ccbars(4338) or P_ccbars(4459) in Lambda_c+ D_s-; production ratios < 0.12 and "
                                "< 0.20 (95% CL)"},
    "LHCb_prompt2024": {"ref": "LHCb, Phys. Rev. D 110, 032001 (2024), arXiv:2404.07131", "read": "abstract",
                        "values": "no significant signal for hidden-charm (Sigma_c Dbar, Lambda_c Dbar) or doubly charmed (Sigma_c D, "
                                  "Lambda_c D) pentaquarks in prompt production; known pentaquark yields consistent with zero"},
    "Belle2017": {"ref": "Belle, Phys. Rev. D 96, 051102 (2017), arXiv:1707.00089", "read": "abstract",
                  "values": "hidden-strangeness pentaquark P_s+ -> phi p: B(Lambda_c+ -> P_s+ pi0) x B(P_s+ -> phi p) < 8.3e-5 "
                            "(90% CL), no evidence"},
    "Cao2020": {"ref": "X. Cao et al., Phys. Rev. D 101, 074010 (2020), arXiv:1912.12054", "read": "abstract",
                "values": "proposes a P_b search in gamma p -> Upsilon p at an electron-ion collider; no P_b observed"},
    "CODATA2022": {"ref": "CODATA 2022, arXiv:2409.03787", "read": "the value used in predictions_vs_data.py",
                   "values": "1/alpha = 137.035999177"},
})

# ---------------------------------------------------------------- I1: claimed pentaquarks
# name, content (lower case quark, upper case antiquark), status, claim source, non-confirmations
PENTA_CLAIMS = [
    ("Theta+(1540)", "uuddS", "unconfirmed", "LEPS2003", ["CLAS2006", "HERAB2004"]),
    ("Xi--(1860)", "ddssU", "unconfirmed", "NA49_2004", ["HERAB2004"]),
    ("Theta_c(3100)", "uuddC", "unconfirmed", "H1_2004", ["ZEUS2004"]),
    ("P_c(4380)", "uudcC", "unconfirmed", "LHCb_Pc2015", ["LHCb_Pc2019_text"]),
    ("P_c(4312)", "uudcC", "established", "LHCb_Pc2019", []),
    ("P_c(4440)", "uudcC", "established", "LHCb_Pc2019", []),
    ("P_c(4457)", "uudcC", "established", "LHCb_Pc2019", []),
    ("P_c(4337)", "uudcC", "unconfirmed", "LHCb_Pc4337", []),
    ("P_cs(4459)", "udscC", "unconfirmed", "LHCb_Pcs4459_text", ["LHCb_LcDs2025"]),
    ("P_psis(4338)", "udscC", "established", "LHCb_Ppsis4338", []),
]
PENTA_SEARCHES = [("doubly charmed, Sigma_c D channel, e.g. Sigma_c++ D+ (cc u u dbar)", "ccuuD", "LHCb_prompt2024"),
                  ("doubly charmed, Lambda_c+ D0 channel (cc u d ubar)", "ccudU", "LHCb_prompt2024"),
                  ("hidden-strange P_s (uud s sbar)", "uudsS", "Belle2017")]


def one_flavour_pair(content):
    """True if some flavour appears both as a quark (lower case) and as an antiquark (upper case)."""
    return any(f in content and f.upper() in content for f in "udscb")


def antiquark_paired(content):
    """H9's condition for a pentaquark: its antiquark has a partner quark of the same flavour."""
    anti = [x for x in content if x.isupper()]
    return len(anti) == 1 and anti[0].lower() in content


check_true("I0a flavour-pair test: T_cc (ccUD) has none, Z_c (cCuD) has one, Theta+ (uuddS) is open, P_c (uudcC) is hidden",
           (not one_flavour_pair("ccUD")) and one_flavour_pair("cCuD") and (not antiquark_paired("uuddS"))
           and antiquark_paired("uudcC"))
I1_TABLE = [[0, 0], [0, 0]]       # rows: hidden, open; columns: established, not established
for (nm, ct, st, src, nul) in PENTA_CLAIMS:
    I1_TABLE[0 if antiquark_paired(ct) else 1][0 if st == "established" else 1] += 1
I1_FISHER_ONE = float(stats.fisher_exact(I1_TABLE, alternative="greater")[1])
I1_FISHER_TWO = float(stats.fisher_exact(I1_TABLE, alternative="two-sided")[1])
_a, _b, _c, _d = I1_TABLE[0][0], I1_TABLE[0][1], I1_TABLE[1][0], I1_TABLE[1][1]
_n, _k, _m = _a + _b + _c + _d, _a + _c, _a + _b
_hyp = sum(math.comb(_m, x) * math.comb(_n - _m, _k - x) for x in range(_a, min(_k, _m) + 1)) / math.comb(_n, _k)
check("I0b Fisher one-sided p equals the hypergeometric tail", I1_FISHER_ONE, _hyp, 1e-12)
I1_OPEN_UNCONFIRMED = all(st != "established" for (nm, ct, st, src, nul) in PENTA_CLAIMS if not antiquark_paired(ct))
# SM7 names "doubly charmed pentaquarks (cc q q qbar)" as forbidden, but H9's rule (the antiquark has a partner quark of its flavour)
# forbids only those whose light antiquark has no partner, e.g. cc u u dbar (I = 3/2); cc u d ubar contains u ubar. SM6's lowest
# doubly charmed level ([cc]_1[ud]_0)qbar has I = 1/2 and contains such a pair; the I = 3/2 levels ([cc]_1[qq]_1)qbar, which include
# cc u u dbar, are the ones H9 forbids.
_pcc32 = [t for t in spectrum("Pcc", PFIT, "P") if CFG["Pcc"][t[1]].asgs[0][(2, 3)] == 1]
_pcc32_low = min(_pcc32, key=lambda t: t[0])
I1_PCC_I32 = predict(lambda P, ci=_pcc32_low[1], k=_pcc32_low[2]: float(levels(CFG["Pcc"][ci], P, "P")[0][k]))
I1_PCC_I32_J = _pcc32_low[3]
TH_PCC32 = lowest_threshold("ccuuD", None, -1)
print(f"  I1 table (hidden/open x established/not): {I1_TABLE}; Fisher p one-sided {I1_FISHER_ONE:.3f}, two-sided "
      f"{I1_FISHER_TWO:.3f}; every open-flavour claim unconfirmed: {I1_OPEN_UNCONFIRMED}; SM6 level forbidden by H9 (cc u u dbar, "
      f"I = 3/2, J = {I1_PCC_I32_J}): {I1_PCC_I32[0]:.1f} +- {I1_PCC_I32[1]:.1f}, {I1_PCC_I32[0] - TH_PCC32[0]:+.1f} from {TH_PCC32[1]} "
      f"{TH_PCC32[0]:.1f}")

# ---------------------------------------------------------------- I2: hidden-bottom pentaquarks
# isospin-averaged thresholds from the fit inputs (KR2014 Tables IV-V, PDG2024)
M_SIGC, M_SIGCS, M_XIC = 2453.4, 2518.1, (2467.71 + 2470.44) / 2
M_SIGB, M_SIGBS, M_XIB = 5814.26, 5833.83, 5792.68
M_D, M_DS_, M_B, M_BS_ = (1864.84 + 1869.66) / 2, (2006.85 + 2010.26) / 2, 5279.4, 5324.75
PB_INPUT = [  # name, measured mass, charm threshold (masses), bottom threshold (masses)
    ("P_c(4312)", 4311.9, (M_SIGC, M_D), (M_SIGB, M_B), "Sigma_b Bbar"),
    ("P_c(4440)", 4440.3, (M_SIGC, M_DS_), (M_SIGB, M_BS_), "Sigma_b Bbar*"),
    ("P_c(4457)", 4457.3, (M_SIGC, M_DS_), (M_SIGB, M_BS_), "Sigma_b Bbar*"),
    ("P_psis(4338)", 4338.2, (M_XIC, M_D), (M_XIB, M_B), "Xi_b Bbar"),
]
I2_MOL = []
for nm, m, (a1, a2), (b1, b2), lab in PB_INPUT:
    Tc, Tb = a1 + a2, b1 + b2
    Bc = Tc - m                                    # binding (positive below threshold)
    mu_c, mu_b = a1 * a2 / Tc, b1 * b2 / Tb
    I2_MOL.append({"partner_of": nm, "bottom_threshold": lab, "T_charm": Tc, "binding_charm": Bc, "T_bottom": Tb,
                   "M_same_binding": Tb - Bc, "M_mu_scaled": Tb - Bc * mu_b / mu_c, "mu_ratio": mu_b / mu_c})
check("I0c Sigma_b Bbar threshold (isospin averages) = 5814.26 + 5279.4", I2_MOL[0]["T_bottom"], 11093.66, 1e-6)
CFG["Pb"] = [penta(f"([bq][qq]_{s})bbar J={J}", "b", "q", "q", "q", "b", J, s34=s)
             for s, Js in ((0, (Hh, H3)), (1, (Hh, H3, H5))) for J in Js]
CFG["Pbs_A"] = [penta(f"([bs][ud]_0)bbar J={J}", "b", "s", "q", "q", "b", J, s34=0) for J in (Hh, H3)]
CFG["Pbs_B"] = [penta(f"([bq][qs])bbar J={J}", "b", "q", "q", "s", "b", J) for J in (Hh, H3, H5)]
_pb_low = pick("Pb", PFIT, "P", ("lowest", ANY))
I2_PB_COMPACT = predict(lambda P, ci=_pb_low[0], k=_pb_low[1]: float(levels(CFG["Pb"][ci], P, "P")[0][k]))
_pb_all = sorted(t[0] for t in spectrum("Pb", PFIT, "P"))
_fa = [t for t in spectrum("Pbs_A", PFIT, "P") if t[3] == Hh]
_fb = [t for t in spectrum("Pbs_B", PFIT, "P") if t[3] == Hh]
_pbs_fam = "Pbs_A" if min(_fa)[0] <= min(_fb)[0] else "Pbs_B"
_pbs_low = pick(_pbs_fam, PFIT, "P", ("lowest", lambda t: t[3] == Hh))
I2_PBS_COMPACT = predict(lambda P, ci=_pbs_low[0], k=_pbs_low[1], f=_pbs_fam: float(levels(CFG[f][ci], P, "P")[0][k]))
I2_PB_COMPACT_J = predict(lambda P, ci=pick("Pb", FIT["J"]["P"], "J", ("lowest", ANY))[0],
                          k=pick("Pb", FIT["J"]["P"], "J", ("lowest", ANY))[1]: float(levels(CFG["Pb"][ci], P, "J")[0][k]), "J")
TH_PB = lowest_threshold("uudbB", None, -1)
TH_PBS = lowest_threshold("udsbB", None, -1)
print("  I2 molecular: " + "; ".join(f"{d['partner_of']} -> {d['bottom_threshold']} {d['T_bottom']:.1f}: {d['M_same_binding']:.1f} "
                                       f"(mu-scaled {d['M_mu_scaled']:.1f})" for d in I2_MOL))
print(f"  I2 compact: lowest ([bq][qq])bbar {I2_PB_COMPACT[0]:.1f} +- {I2_PB_COMPACT[1]:.1f} (variant J {I2_PB_COMPACT_J[0]:.1f}); "
      f"levels {_pb_all[0]:.0f} to {_pb_all[-1]:.0f}; lowest J=1/2 udsb bbar {I2_PBS_COMPACT[0]:.1f}; lowest S-wave thresholds "
      f"{TH_PB[1]} {TH_PB[0]:.1f}, {TH_PBS[1]} {TH_PBS[0]:.1f}")

# ---------------------------------------------------------------- I3: the general rule
I3_ROWS = [{"state": c[0], "content": c[7], "one_flavour_pair": one_flavour_pair(c[7])} for c in CATALOGUE]
I3_VIOLATORS = [r["state"] for r in I3_ROWS if not r["one_flavour_pair"]]
print(f"  I3 established exotic hadrons without a pair of one flavour: {I3_VIOLATORS}")

# ---------------------------------------------------------------- I4: alpha M / 2 for spin doublets
# Eligible doublets, fixed from quark content and J^P only before any splitting was computed (see the header of Section I).
I4_STATES = {   # name: (mass, error, J, P) -- J, P as in the SM6 catalogue; CMS structures from Table I (no interference)
    "Z_c(3900)+": (3899.0, 6.1, 1, 1), "Z_c(4020)+": (4022.9, 2.8, None, None), "Z_c(4430)+": (4475.0, 19.0, 1, 1),
    "Z_cs(3985)+": (3982.5, 3.1, None, None), "Z_cs(4000)+": (4003.0, 11.0, 1, 1), "Z_cs(4220)+": (4216.0, 40.0, 1, None),
    "X(3960)": (3956.0, 11.2, 0, 1), "chi_c1(4140)": (4118.0, 28.0, 1, 1), "chi_c1(4274)": (4294.0, 5.5, 1, 1),
    "chi_c0(4500)": (4474.0, 4.2, 0, 1), "X(4685)": (4684.0, 15.0, 1, 1), "chi_c0(4700)": (4694.0, 10.0, 0, 1),
    "Z_b(10610)+": (10607.2, 2.0, None, None), "Z_b(10650)+": (10652.2, 1.5, None, None),
    "P_c(4312)+": (4311.9, 3.0, None, None), "P_c(4440)+": (4440.3, 4.6, None, None), "P_c(4457)+": (4457.3, 2.5, None, None),
    "X(6600) CMS": (6552.0, math.hypot(10, 12), None, None), "X(6900) CMS": (6927.0, math.hypot(9, 4), None, None),
}
I4_GROUPS = {"c cbar u dbar": ["Z_c(3900)+", "Z_c(4020)+", "Z_c(4430)+"],
             "c cbar u sbar": ["Z_cs(3985)+", "Z_cs(4000)+", "Z_cs(4220)+"],
             "c cbar s sbar, P = +": ["X(3960)", "chi_c1(4140)", "chi_c1(4274)", "chi_c0(4500)", "X(4685)", "chi_c0(4700)"],
             "b bbar u dbar": ["Z_b(10610)+", "Z_b(10650)+"],
             "u u d c cbar": ["P_c(4312)+", "P_c(4440)+", "P_c(4457)+"],
             "c c cbar cbar": ["X(6600) CMS", "X(6900) CMS"]}
I4_NOT_ELIGIBLE = [("X(4630)", "c cbar s sbar with P = -: parity differs from the other c cbar s sbar states"),
                   ("X(3872), psi(4230)", "c cbar q qbar with I = 0: parities differ"),
                   ("X0(2900), X1(2900)", "cbar sbar u d: parities differ"),
                   ("P_c(4440), P_c(4457)", "the pair that suggested the rule"),
                   ("P_cs(4459) two-peak fit", "not resolved: LHCb 'cannot confirm or refute the two-peak hypothesis'"),
                   ("X(7100) CMS, P_c(4337), P_c(4380)", "not established as observations")]


def jp_compatible(a, b):
    Ja, Pa, Jb, Pb = a[2], a[3], b[2], b[3]
    if Pa is not None and Pb is not None and Pa != Pb:
        return False
    if Ja is not None and Jb is not None and abs(Ja - Jb) > 1:
        return False
    return True


I4_ELIGIBLE = []
for grp, members in I4_GROUPS.items():
    for s1, s2 in itertools.combinations(members, 2):
        if {s1, s2} == {"P_c(4440)+", "P_c(4457)+"}:
            continue
        if jp_compatible(I4_STATES[s1], I4_STATES[s2]):
            I4_ELIGIBLE.append((grp, s1, s2))
check("I0d number of eligible doublets fixed by content and J^P (3 + 3 + 15 + 1 + 2 + 1)", len(I4_ELIGIBLE), 25, 0)

# QCD baseline: the colour-spin model's splitting of two S-wave levels of the same J^P(C) where the model has such a pair
CFG["hidden_b"] = [tetra(f"[bq][bbar qbar] J={J}", "b", "q", "b", "q", J, cperm=[2, 3, 0, 1]) for J in (0, 1, 2)]
CFG["hidden_cs"] = [tetra(f"[cs][cbar sbar] J={J}", "c", "s", "c", "s", J, cperm=[2, 3, 0, 1]) for J in (0, 1, 2)]
CFG["hidden_cqs"] = [tetra(f"[cq][cbar sbar] J={J}", "c", "q", "c", "s", J) for J in (0, 1, 2)]


def model_split(key, J, C):
    """Splitting of the two lowest S-wave levels with total spin J (and C parity C, if given) of a configuration family."""
    def f(P, scheme="P"):
        lv = sorted(t[0] for t in spectrum(key, P, scheme) if t[3] == J and (C is None or t[4] == C))
        return lv[1] - lv[0]
    return f


I4_MODEL = {("Z_c(3900)+", "Z_c(4020)+"): ("hidden_c", 1, -1, "two 1+- levels of [cq][cbar qbar] (taking Z_c(4020) as 1+-)"),
            ("Z_b(10610)+", "Z_b(10650)+"): ("hidden_b", 1, -1, "two 1+- levels of [bq][bbar qbar] (taking both as 1+-)"),
            ("Z_cs(3985)+", "Z_cs(4000)+"): ("hidden_cqs", 1, None, "two lowest 1+ levels of [cq][cbar sbar]"),
            ("X(3960)", "chi_c0(4500)"): ("hidden_cs", 0, 1, "two 0++ levels of [cs][cbar sbar]"),
            ("X(3960)", "chi_c0(4700)"): ("hidden_cs", 0, 1, "two 0++ levels of [cs][cbar sbar]"),
            ("chi_c0(4500)", "chi_c0(4700)"): ("hidden_cs", 0, 1, "two 0++ levels of [cs][cbar sbar]")}
I4_ROWS = []
for grp, s1, s2 in I4_ELIGIBLE:
    m1, e1 = I4_STATES[s1][:2]
    m2, e2 = I4_STATES[s2][:2]
    dlt, sd = abs(m2 - m1), math.hypot(e1, e2)
    pred = ALPHA * (m1 + m2) / 2 / 2
    z = (dlt - pred) / sd
    pch = interval_cover([(pred - 2 * sd, pred + 2 * sd)], 0.0, 300.0) / 300.0
    row = {"group": grp, "pair": [s1, s2], "Delta": dlt, "err": sd, "alpha_M_over_2": pred, "pull": z, "passes": abs(z) < 2,
           "p_chance": pch}
    if (s1, s2) in I4_MODEL:
        key, J, C, desc = I4_MODEL[(s1, s2)]
        val, err, _ = predict(model_split(key, J, C))
        row["model"] = {"Delta": val, "err": err, "desc": desc, "pull": (dlt - val) / math.hypot(sd, err)}
    I4_ROWS.append(row)
I4_PASS = sum(r["passes"] for r in I4_ROWS)
I4_EXPECT = sum(r["p_chance"] for r in I4_ROWS)
I4_P_EXCESS = float(stats.poisson.sf(I4_PASS - 1, I4_EXPECT))
I4_FAIL3 = sum(abs(r["pull"]) >= 3 for r in I4_ROWS)
rng_i4 = np.random.default_rng(SEED + 4)
_mc_pass = np.zeros(4000)
for r in I4_ROWS:
    _mc_pass += np.abs(rng_i4.uniform(0, 300, 4000) - r["alpha_M_over_2"]) < 2 * r["err"]
check("I0e expected chance passes: analytic sum against 4000 Monte Carlo replicas (5 sigma)", float(np.mean(_mc_pass)), I4_EXPECT,
      5 * float(np.std(_mc_pass)) / math.sqrt(4000) + 1e-9)
I4_MOTIVATING = {"pair": ["P_c(4440)+", "P_c(4457)+"], "Delta": 4457.3 - 4440.3, "alpha_M_over_2": ALPHA * (4440.3 + 4457.3) / 4}
I4_PCS_INFO = {"pair": ["4454.9", "4467.8"], "Delta": 4467.8 - 4454.9, "err": math.hypot(2.7, 3.7),
               "alpha_M_over_2": ALPHA * (4454.9 + 4467.8) / 4, "note": "unresolved two-peak hypothesis, statistical errors only"}
for r in I4_ROWS:
    s = f"  I4 {r['pair'][0]:<14s} {r['pair'][1]:<14s} Delta {r['Delta']:6.1f} +- {r['err']:5.1f}  alpha M/2 {r['alpha_M_over_2']:5.1f}  " \
        f"pull {r['pull']:+6.1f}  {'pass' if r['passes'] else 'fail'}"
    if "model" in r:
        s += f"  | model {r['model']['Delta']:5.1f} +- {r['model']['err']:4.1f} pull {r['model']['pull']:+5.1f}"
    print(s)
print(f"  I4: {I4_PASS} of {len(I4_ROWS)} pass; {I4_EXPECT:.2f} expected by chance (Poisson p of >= {I4_PASS}: {I4_P_EXCESS:.2f}); "
      f"{I4_FAIL3} fail by 3 sigma or more")
H9 = {"I1": {"claims": [{"state": nm, "content": ct, "pair": "hidden" if antiquark_paired(ct) else "open", "status": st,
                         "source": src, "not_confirmed_by": nul} for (nm, ct, st, src, nul) in PENTA_CLAIMS],
             "searches_without_claim": [{"state": a, "content": b, "source": c} for a, b, c in PENTA_SEARCHES],
             "table_hidden_open_x_established_not": I1_TABLE, "fisher_p_one_sided": I1_FISHER_ONE,
             "fisher_p_two_sided": I1_FISHER_TWO, "every_open_claim_unconfirmed": I1_OPEN_UNCONFIRMED,
             "Pcc_forbidden_level": {"M": I1_PCC_I32[0], "err": I1_PCC_I32[1], "J": I1_PCC_I32_J, "content": "cc u u dbar",
                                     "threshold": {"pair": TH_PCC32[1], "M": TH_PCC32[0]}},
             "ill_posed_note": "SM7's example 'doubly charmed pentaquarks (cc q q qbar)' is forbidden by H9's rule only when the light "
                               "antiquark has no partner quark (e.g. cc u u dbar, I = 3/2); cc u d ubar contains a pair of one flavour",
             "verdict": "holds (every open-flavour claim is unconfirmed); not significant as a contrast (Fisher p one-sided "
                        f"{I1_FISHER_ONE:.2f}); conflicts with SM6's I = 3/2 doubly charmed levels, neither decided"},
      "I2": {"molecular": I2_MOL, "compact_Pb_lowest": {"M": I2_PB_COMPACT[0], "err": I2_PB_COMPACT[1]},
             "compact_Pb_lowest_J": {"M": I2_PB_COMPACT_J[0], "err": I2_PB_COMPACT_J[1]},
             "compact_Pb_levels": _pb_all, "compact_Pbs_lowest_half": {"M": I2_PBS_COMPACT[0], "err": I2_PBS_COMPACT[1]},
             "lowest_S_wave_threshold_Pb": {"pair": TH_PB[1], "M": TH_PB[0]},
             "lowest_S_wave_threshold_Pbs": {"pair": TH_PBS[1], "M": TH_PBS[0]},
             "search_status": "no experimental search for hidden-bottom pentaquarks found on arXiv; proposals (Cao2020)",
             "verdict": "live"},
      "I3": {"rows": I3_ROWS, "violators": I3_VIOLATORS, "verdict": "refuted" if I3_VIOLATORS else "holds"},
      "I4": {"eligible": [{"group": g, "pair": [a, b]} for g, a, b in I4_ELIGIBLE], "not_eligible": I4_NOT_ELIGIBLE,
             "rows": I4_ROWS, "n_pass": I4_PASS, "n_eligible": len(I4_ROWS), "expected_chance": I4_EXPECT,
             "poisson_p_excess": I4_P_EXCESS, "n_fail_3sigma": I4_FAIL3, "motivating_pair": I4_MOTIVATING,
             "Pcs4459_two_peak_info": I4_PCS_INFO, "alpha": ALPHA,
             "verdict": "refuted as a rule for every resolved doublet" if I4_FAIL3 else "holds"}}


# I4 figure: splittings against alpha M / 2
def figure_alpha():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    meta = {"CreationDate": None, "ModDate": None, "Producer": None, "Creator": None}
    fig, ax = plt.subplots(1, 1, figsize=(3.1, 2.7), layout="constrained")
    fig.get_layout_engine().set(w_pad=0.02, h_pad=0.02)
    mm = np.linspace(3500, 11500, 200)
    ax.plot(mm, ALPHA * mm / 2, color="#0b0b0b", lw=1.0, label=r"$\alpha M/2$")
    for r in I4_ROWS:
        mbar = (I4_STATES[r["pair"][0]][0] + I4_STATES[r["pair"][1]][0]) / 2
        ax.errorbar([mbar], [r["Delta"]], yerr=[min(r["err"], r["Delta"] * 0.95)], fmt="o", ms=3.8,
                    color=COL["P"] if r["passes"] else COL["P-in"], mec="white", mew=0.4, lw=0.7, capsize=1, zorder=3)
        if "model" in r:
            ax.plot([mbar], [r["model"]["Delta"]], "^", ms=4, color=COL["J"], mec="white", mew=0.4, zorder=4)
    ax.plot([], [], "o", ms=3.8, color=COL["P"], label=r"eligible pair, within $2\sigma$")
    ax.plot([], [], "o", ms=3.8, color=COL["P-in"], label="eligible pair, outside")
    ax.plot([], [], "^", ms=4, color=COL["J"], label="colour-spin model")
    mot = I4_MOTIVATING
    ax.plot([(4440.3 + 4457.3) / 2], [mot["Delta"]], "*", ms=6, color="#52514e", label=r"$P_c(4440)/P_c(4457)$ (excluded)")
    ax.set_yscale("log")
    ax.set_ylim(0.3, 1500)
    ax.set_xlim(3500, 11500)
    ax.set_xlabel("mean mass $M$ [MeV]")
    ax.set_ylabel(r"splitting $\Delta$ [MeV]")
    ax.legend(loc="lower right", frameon=False, fontsize=6.3, handletextpad=0.3)
    fig.savefig(FIGURES / "exotic_alpha.pdf", metadata=meta)
    plt.close(fig)


figure_alpha()

CHOICES_AFTER_DATA_H9 = [
    "H9 itself was conceived after seeing that every established pentaquark carries c cbar (SM7's honesty note); those states are "
    "not evidence for it.",
    "The claimed-pentaquark list was compiled from the claims we could find and verify on arXiv; light hidden-flavour candidates "
    "are not claimed as pentaquarks in the literature we read, so the table has no light hidden-flavour row.",
    "I2: the molecular masses carry over binding energies relative to isospin-averaged thresholds (the lead's instruction and SM7); "
    "the reduced-mass scaling is a variant added with it, not chosen after seeing anything, since no hidden-bottom pentaquark is "
    "known.",
    "I4: the eligibility rule and the list were written before any splitting was computed, but the masses of all candidate states "
    "were known from SM6, and the P_cs(4459) two-peak masses were read (for the status in I1) before the list was written; it is "
    "listed as not resolved by the rule. The chance null (Delta uniform in 0 to 300 MeV) and the 2 sigma pass criterion were fixed "
    "with the list.",
]
H9["choices_after_data"] = CHOICES_AFTER_DATA_H9


# =====================================================================================================================================
# Outputs
# =====================================================================================================================================
CHOICES_AFTER_DATA = [
    "The rule for binding across the two halves (primary: KR's factorised potential applied to every pair; variant P-in: no binding "
    "across the root) was written into the script before any exotic state was computed, but by authors who knew the published "
    "masses of the exotic states. Both rules are reported for every state; they differ only where a heavy or strange pair sits in "
    "different halves (hidden-charm and fully charmed states, P_c, T_csbar).",
    "k_s (KR's heavy-strange hyperfine enhancement a_cs = a_bs) is shared between mesons and baryons. KR apply it in baryons only; "
    "the extension was fixed before the fit, motivated by KR's own observation that the D_s* - D_s splitting is enhanced by the "
    "same factor, not by any exotic comparison.",
    "For each catalogue state one measurement was taken: the most recent one of the cited collaboration that we could read (LHCb 2021 "
    "for the J/psi phi states, not the 2016 values; the BESIII discovery values for Z_c(3900) and Z_c(4020), not PDG averages, which "
    "we could not read). The catalogue excludes X(3915) (exotic status disputed), P_cs(4459) and P_c(4337) (evidence below 5 sigma).",
    "The chance-proximity numbers for the three 'nearest level' assignments (p_chance) were added after seeing that they hold.",
    "Tests B5 (states with measured J^P only), B6 (without the two states within 1 MeV of a threshold) and B7 (distances floored at "
    "the mass error) were added after seeing the Fisher result, to show what drives it.",
    "The CMS and ATLAS di-J/psi structures are shown with the fully charmed levels but not scored; that the lowest ATLAS structure "
    "(6.41 GeV) lies near the model's S-wave levels was noticed after the comparison and is not a test.",
]
_tet = [ROW[l]["J"]["M"] - ROW[l]["P"]["M"] for l in ("T_cc+ (cc ubar dbar)", "T_bb- (bb ubar dbar)", "T_bc (bc ubar dbar), 0+",
                                                      "X0(2900) (ud cbar sbar)", "T_csbar0(2900) (c sbar u dbar)",
                                                      "cc cbar cbar 2++ vs X(6900)")]
_pen = [ROW[l]["J"]["M"] - ROW[l]["P"]["M"] for l in ("P_c(4312) (lowest uud c cbar)", "P_psis(4338) (lowest I=0, J=1/2)",
                                                      "P_cc ([cc][ud] qbar), lowest")]
DELTA_J = {"tetraquarks": (min(_tet), max(_tet)), "pentaquarks": (min(_pen), max(_pen))}
CAVEATS = [
    f"Effective-mass conventions dominate the multiquark predictions. Baryon masses for every constituent (KR) and universal masses "
    f"with string junctions (variant J) differ by {min(_tet):.0f} to {max(_tet):.0f} MeV for the tetraquarks and {min(_pen):.0f} to "
    f"{max(_pen):.0f} MeV for the lowest pentaquarks, ten to twenty-five times sigma_model; the fit to ordinary hadrons cannot choose "
    f"between them (sigma_model {FIT['P']['sigma']:.1f} and {FIT['J']['sigma']:.1f} MeV).",
    "sigma_model is the spread of ordinary hadrons. It does not include the uncertainty of carrying the model to four and five "
    "constituents (colour configurations outside the H8 tree, the spatial size of a diquark pair, binding across the halves).",
    "The H8 tree keeps one colour configuration (3bar x 3 for tetraquarks). The full colour-spin model also has 6 x 6bar; mixing would "
    "lower the lowest levels, mostly for the fully heavy and hidden-charm states.",
    "Only S-wave ground states are computed. Radial and orbital excitations (X1(2900) is 1-) are outside the model, so a mismatch "
    "refutes an S-wave assignment, not every compact reading.",
    "Threshold test: the catalogue is not a random sample. Many exotic states were found as narrow structures near thresholds, and "
    "threshold cusps can mimic peaks, so proximity is partly a selection effect. The threshold list (hadrons narrower than 60 MeV) "
    f"and the S-wave and C rules set the look-elsewhere count, on average {MEAN_NWIN:.1f} thresholds per +-150 MeV window; isospin "
    "and G parity are not imposed.",
    "Threshold proximity is the standard signature of hadronic molecules and of threshold cusps in QCD; it supports the molecular "
    "branch of H8 only in the sense that H8 includes that branch.",
    "Lattice QCD results for T_bb scatter from 83 to 189 MeV binding; the comparison is not a measurement.",
]


def clean(o):
    if isinstance(o, dict):
        return {str(k): clean(v) for k, v in o.items()}
    if isinstance(o, (list, tuple)):
        return [clean(v) for v in o]
    if isinstance(o, Fraction):
        return float(o)
    if isinstance(o, (np.floating, float)):
        return float(f"{float(o):.6g}")
    if isinstance(o, (np.integer,)):
        return int(o)
    if isinstance(o, np.ndarray):
        return clean(o.tolist())
    if isinstance(o, np.bool_):
        return bool(o)
    return o


n_ok = sum(results)
n_all = len(results)
scored = [r for r in ITEMS if r["kind"] == "scored"]
n_hold = sum(r["verdict"] == "holds" for r in scored)
out = {
    "script": "docs/simulation/exotic_hadrons.py", "seed": SEED, "n_mc": N_MC, "n_perturb": N_PERTURB,
    "checks": {"passed": n_ok, "total": n_all, "list": check_log},
    "hosting_KR": {"T_cc": levels(T_CC, KR)[0][0], "T_bb": levels(T_BB, KR)[0][0], "T_bc0": levels(T_BC0, KR)[0][0],
                   "Xi_cc": mass1("Xi_cc", KR), "KNR_cccc": KNR_CCCC},
    "fit": {
        "P": {"params": dict(zip(PAR_P, FIT["P"]["theta"])), "param_err": dict(zip(PAR_P, np.sqrt(np.diag(FIT["P"]["cov"])))),
              "sigma_model": FIT["P"]["sigma"], "dof": FIT["P"]["dof"], "n_data": len(FIT_M),
              "residuals": dict(zip(FIT_NAMES, FIT["P"]["res"])), "max_abs_residual": float(np.max(np.abs(FIT["P"]["res"]))),
              "rms_mesons": float(np.sqrt(np.mean([FIT["P"]["res"][i] ** 2 for i, n in enumerate(FIT_NAMES) if ORD[n].n == 2]))),
              "rms_baryons": float(np.sqrt(np.mean([FIT["P"]["res"][i] ** 2 for i, n in enumerate(FIT_NAMES) if ORD[n].n == 3]))),
              "v_bc": PFIT.v_bc, "p_interp": interp_vbc(PFIT.v_cc, PFIT.v_bb, PFIT.mm["c"], PFIT.mm["b"])[1]},
        "J": {"params": dict(zip(PAR_J, FIT["J"]["theta"])), "sigma_model": FIT["J"]["sigma"], "dof": FIT["J"]["dof"]},
        "loo": {"rms": LOO_RMS, "n": len(loo), "residuals": loo},
        "Xi_cc_heldout": {"model": _xicc[0], "err": _xicc[1], "data": XICC[0], "data_err": XICC[1], "pull": XICC_PULL},
        "inputs": [{"name": d[0], "mass": d[1], "source": d[2]} for d in FIT_DATA],
    },
    "A": {"items": ITEMS, "n_scored": len(scored), "n_holds": n_hold,
          "n_refuted": sum(r["verdict"] == "refuted" for r in scored),
          "n_holds_by_scheme": {sch: sum(abs(r[sch]["pull"]) < 2 for r in scored) for sch in ("P", "P-in", "J")}},
    "B": {"W": W_MAIN, "W_alt": W_ALT, "n_states": len(CATALOGUE),
          "states": [{"name": c[0], "mass": c[1], "err": c[2], "width": c[3], "J": c[4], "P": c[5], "C": c[6], "content": c[7],
                      "source": c[8], "nearest": THR[c[0]]["main"]["nearest"], "threshold": THR[c[0]]["main"]["T"],
                      "M_minus_T": THR[c[0]]["main"]["d"], "p": THR[c[0]]["main"]["p"], "p_W300": THR[c[0]]["alt"]["p"],
                      "n_in_window": THR[c[0]]["main"]["n_window"], "nearest_masses_verified": THR[c[0]]["main"]["nearest_verified"]}
                     for c in CATALOGUE],
          "fisher": {"X2": FISH_MAIN[0], "dof": 2 * len(CATALOGUE), "p": FISH_MAIN[1]},
          "fisher_W300": {"X2": FISH_ALT[0], "p": FISH_ALT[1]},
          "close": {f"{int(d)}MeV": {"observed": N_CLOSE[d], "expected": EXP_CLOSE[d], "poisson_p": P_CLOSE[d]} for d in N_CLOSE},
          "n_below": N_BELOW, "mean_thresholds_per_window": MEAN_NWIN,
          "perturbed_unverified_1MeV": pert[1.0], "perturbed_unverified_3MeV": pert[3.0],
          "known_JP": {"n": len(KNOWN_JP), "p": FISH_KNOWN[1]}, "without_sub_MeV": {"n": len(FAR), "p": FISH_FAR[1]},
          "distance_floored_at_sigma_M": {"p": FISH_FLOOR[1]},
          "n_threshold_hadrons": len(THRESH_HADRONS), "n_unverified_hadrons": sum(1 for h in THRESH_HADRONS if not h[7])},
    "C": PARTNERS,
    "I": H9,
    "delta_J_minus_P": DELTA_J,
    "choices_after_data": CHOICES_AFTER_DATA, "caveats": CAVEATS,
    "citations": CITATIONS,
    "runtime_s": round(time.perf_counter() - T_START, 1),
}
RESULTS.mkdir(parents=True, exist_ok=True)
(RESULTS / "exotic_hadrons.json").write_text(json.dumps(clean(out), indent=1, ensure_ascii=True) + "\n")


def fmt_row(r):
    d = r.get("data")
    dat = f"{d['M']:.1f} (-{d['err_lo']:.1f} +{d['err_hi']:.1f})" if d else "-"
    pull = f"{r['P']['pull']:+.2f}" if d else "-"
    thr = f"{r['threshold']['pair']} {r['threshold']['M']:.1f}: {r['P']['binding']:+.1f}" if "threshold" in r else "-"
    return (f"| {r['label']} | {r['P']['config']} | {r['P']['M']:.1f} +- {r['P']['err']:.1f} | {r['KRpar']['M']:.1f} | "
            f"{r['P-in']['M']:.1f} | {r['J']['M']:.1f} | {dat} | {pull} | {r['verdict']} | {thr} |")


md = []
md.append("# Hadrons as trees of dualities (H8): tetraquarks and pentaquarks against data\n")
md.append(f"Workstream SM6 of *GUID v6*. Written by `docs/simulation/exotic_hadrons.py` (seed {SEED}); every number is also in "
          f"`exotic_hadrons.json`. Figures: `docs/simulation/figures/exotic_fit.pdf`, `exotic_spectrum.pdf`, `exotic_levels.pdf`, "
          f"`exotic_thresholds.pdf`. Checks: **{n_ok} of {n_all} passed** (engine, hosting check, fit numerics, null "
          f"distribution); every confrontation with data is a result, not a check. Runtime {out['runtime_s']:.0f} s.\n")
md.append("## Verdict\n")
md.append(f"- **Model.** The colour-spin model of De Rujula, Georgi and Glashow in Karliner and Rosner's form reproduces KR's "
          f"published numbers to 0.15 MeV (T_cc 3882.2, T_bb 10389.4, T_bc 7133.7, Xi_cc 3627). Refitted to 42 ordinary ground-state "
          f"hadrons it has sigma_model = {SIG:.1f} MeV ({FIT['P']['dof']} dof; leave-one-out {LOO_RMS:.1f} MeV). The held-out "
          f"Xi_cc++ comes out at {_xicc[0]:.1f} +- {_xicc[1]:.1f} MeV against 3621.55 (pull {XICC_PULL:+.2f}).")
md.append(f"- **(a) Compact exotics: {n_hold} of {len(scored)} scored confrontations hold, "
          f"{out['A']['n_refuted']} are refuted.** T_cc+ holds ({ROW['T_cc+ (cc ubar dbar)']['P']['M']:.1f} +- "
          f"{ROW['T_cc+ (cc ubar dbar)']['P']['err']:.1f} against 3874.7, pull {ROW['T_cc+ (cc ubar dbar)']['P']['pull']:+.2f}), but "
          f"the model puts it {ROW['T_cc+ (cc ubar dbar)']['P']['binding']:+.0f} MeV from the D*+ D0 threshold where it is bound by "
          f"0.36 MeV. X0(2900), T_csbar(2900), X(6900) as an S-wave [cc][cbar cbar], P_c(4312) and P_psis(4338) are refuted. The "
          f"three assignments by proximity (P_c(4440), P_c(4457), P_cs(4459)) hold, with chance probabilities "
          + ", ".join(f"{r['p_chance']:.2f}" for r in scored if 'p_chance' in r) + ".")
md.append(f"- **Live predictions.** T_bb- at {ROW['T_bb- (bb ubar dbar)']['P']['M']:.0f} +- {ROW['T_bb- (bb ubar dbar)']['P']['err']:.0f}"
          f" MeV, {ROW['T_bb- (bb ubar dbar)']['P']['binding']:+.0f} MeV below B B* (lattice: 83 to 189 MeV); T_bc 0+ at "
          f"{ROW['T_bc (bc ubar dbar), 0+']['P']['M']:.0f} ({ROW['T_bc (bc ubar dbar), 0+']['P']['binding']:+.0f} MeV from B0bar D0), "
          f"T_bc 1+ at {ROW['T_bc (bc ubar dbar), 1+']['P']['M']:.0f} ({ROW['T_bc (bc ubar dbar), 1+']['P']['binding']:+.0f} MeV "
          f"from D0 B*); P_cc at {ROW['P_cc ([cc][ud] qbar), lowest']['P']['M']:.0f} MeV, "
          f"{ROW['P_cc ([cc][ud] qbar), lowest']['P']['binding']:+.0f} MeV above Xi_cc pi.")
md.append(f"- **(b) Threshold proximity.** Of {len(CATALOGUE)} established exotic hadrons, {N_CLOSE[10.0]} lie within 10 MeV of an "
          f"allowed S-wave two-hadron threshold where {EXP_CLOSE[10.0]:.1f} are expected for random placement in +-150 MeV windows. "
          f"Fisher's combined p = {FISH_MAIN[1]:.1e} (W = 150 MeV; {FISH_ALT[1]:.1e} for W = 300 MeV). Without T_cc+ and X(3872), "
          f"p = {FISH_FAR[1]:.2f}. Selection and look-elsewhere caveats below.")
md.append("- **(c) Partners.** The compact (diquark-tree) reading of X(3872) predicts charged partners that BaBar and Belle exclude: "
          "a failed prediction. Our model itself places the compact 1++ state "
          f"{_xc['P']['M'] - _xc['data']['M']:.0f} MeV above X(3872). Every other predicted partner is untested or live.")
md.append("- **H8 as such.** Any colour singlet can be written as a binary tree of colour-conjugate pairs (3 x 3 contains 3bar, "
          "3 x 3bar contains 1), so the generic statement holds as a reading and cannot fail; with its either-or (compact or molecular) "
          "for every multiquark, it also cannot fail on any single state. Its content is in the model's masses, and there it fails more "
          "often than it holds.\n")
md.append("## (a) Compact exotics and live predictions\n")
md.append("Model P: KR's convention, parameters fitted here. P-in: no binding across the halves. J: universal masses plus junctions. "
          "Pull with sigma_pred and the data error on the side of the model; |pull| < 2 holds.\n")
md.append("| state | level (model P) | model P [MeV] | KR parameters | P-in | J | data | pull | verdict | lowest S-wave threshold "
          "(~ = antiparticle): M - T |")
md.append("|---|---|---|---|---|---|---|---|---|---|")
for r in ITEMS:
    md.append(fmt_row(r))
md.append("")
for lab in LATTICE:
    r = ROW[lab]
    md.append(f"- {lab}: model binding {r['P']['binding']:+.1f} +- {r['P']['err']:.1f} MeV; lattice: "
              + ", ".join(f"{d['source']} {d['binding']:+.0f} (pull {d['pull_P']:+.1f})" for d in r["lattice"])
              + (f"; {r['lattice_note']}" if "lattice_note" in r else ""))
md.append("")
md.append("## Fit to ordinary hadrons\n")
md.append("| parameter | value | 1 sigma |")
md.append("|---|---|---|")
for n, v, e in zip(PAR_P, FIT["P"]["theta"], np.sqrt(np.diag(FIT["P"]["cov"]))):
    md.append(f"| {n} | {v:.4g} | {e:.2g} |")
md.append(f"\nKR's values: m^m = 310, 483, 1663.3, 5003.8; m^b = 363, 538, 1710.5, 5043.5; b/310^2 = 80; a/363^2 = 50; "
          f"a_cs/a = {KR_KS_C:.3f}; B1 = -69.9, -83.6, -258.0, -562.8, -341.5. Scheme J: S = {FIT['J']['theta'][4]:.1f} MeV, "
          f"sigma_model = {FIT['J']['sigma']:.2f} MeV.\n")
md.append("| hadron | input [MeV] | source | model - input |")
md.append("|---|---|---|---|")
for (n, m, src), rr in zip(FIT_DATA, FIT["P"]["res"]):
    md.append(f"| {n} | {m:.2f} | {src} | {rr:+.1f} |")
md.append("\n## (b) Threshold proximity\n")
md.append("| state | M [MeV] | J^P(C) | nearest allowed S-wave threshold | T [MeV] | M - T | p (W=150) | p (W=300) | source |")
md.append("|---|---|---|---|---|---|---|---|---|")
for c in CATALOGUE:
    t = THR[c[0]]
    jp = ("?" if c[4] is None else str(Fraction(c[4]))) + ({1: "+", -1: "-", None: "?"}[c[5]]) + \
         ({1: "+", -1: "-", None: ""}[c[6]])
    md.append(f"| {c[0]} | {c[1]:.1f} | {jp} | {t['main']['nearest']}{'' if t['main']['nearest_verified'] else ' (u)'} | "
              f"{t['main']['T']:.1f} | {t['main']['d']:+.1f} | {t['main']['p']:.4f} | {t['alt']['p']:.4f} | {c[8]} |")
md.append(f"\n(u): a threshold hadron mass not re-read. Fisher X2 = {FISH_MAIN[0]:.1f} ({2 * len(CATALOGUE)} dof), p = "
          f"{FISH_MAIN[1]:.2e}; W = 300: p = {FISH_ALT[1]:.2e}. Within 5/10/20 MeV: {N_CLOSE[5.0]}/{N_CLOSE[10.0]}/{N_CLOSE[20.0]} "
          f"observed, {EXP_CLOSE[5.0]:.2f}/{EXP_CLOSE[10.0]:.2f}/{EXP_CLOSE[20.0]:.2f} expected (Poisson p {P_CLOSE[5.0]:.3f}/"
          f"{P_CLOSE[10.0]:.3f}/{P_CLOSE[20.0]:.3f}). Below the nearest threshold: {N_BELOW} of {len(CATALOGUE)}. Mean number of "
          f"allowed thresholds per window: {MEAN_NWIN:.1f}. Unverified threshold masses perturbed by 1 MeV: p from {pert[1.0][0]:.1e} "
          f"to {pert[1.0][2]:.1e}; by 3 MeV: {pert[3.0][0]:.1e} to {pert[3.0][2]:.1e}. States with measured J^P only "
          f"({len(KNOWN_JP)}): p = {FISH_KNOWN[1]:.1e}. Without T_cc+ and X(3872): p = {FISH_FAR[1]:.3f}. Distances floored at "
          f"the mass error: p = {FISH_FLOOR[1]:.1e}.\n")
md.append("## (c) Partners\n")
for pt in PARTNERS:
    md.append(f"- **{pt['id']}** {pt['prediction']}. *Search:* {pt['search']}. **{pt['verdict']}**.")
md.append("\n## Hypothesis H9: the minting in hadrons (SM7)\n")
md.append("H9 (fixed in sm_preregistration.md, SM7, after the SM6 results and before this analysis): a pentaquark is a minting, a "
          "bound triple of colour-bearers plus a quark and its own antiquark. **Honesty note:** H9 was conceived after seeing that "
          "every established pentaquark carries c cbar, so those states are not evidence for it.\n")
md.append("### I1 (P1) no open flavour\n")
md.append("| claimed pentaquark | content | pair | status | claim | not confirmed by |")
md.append("|---|---|---|---|---|---|")
for c in H9["I1"]["claims"]:
    md.append(f"| {c['state']} | {c['content']} | {c['pair']} | {c['status']} | {c['source']} | "
              f"{', '.join(c['not_confirmed_by']) or '-'} |")
for c in H9["I1"]["searches_without_claim"]:
    md.append(f"| {c['state']} | {c['content']} | {'hidden' if antiquark_paired(c['content']) else 'open'} | no claim; searched "
              f"| - | {c['source']} |")
md.append(f"\nHidden/open x established/not: {I1_TABLE} (rows hidden, open). Fisher's exact p = {I1_FISHER_ONE:.3f} one-sided, "
          f"{I1_FISHER_TWO:.3f} two-sided. Every open-flavour claim unconfirmed: {I1_OPEN_UNCONFIRMED}. Verdict: "
          f"{H9['I1']['verdict']}. Light hidden-flavour pentaquarks (uud s sbar, uud u ubar) would mix with N* resonances and are hard "
          "to tag, and the open-flavour claims date from 2003-2004 while the hidden-charm ones come from far larger LHCb samples: "
          "selection, not only physics. Ill-posed example: " + H9["I1"]["ill_posed_note"] + ". SM6's lowest doubly charmed level "
          f"([cc]_1[ud]_0)qbar at {ROW['P_cc ([cc][ud] qbar), lowest']['P']['M']:.0f} MeV has I = 1/2 and is allowed; its I = 3/2 "
          f"level cc u u dbar at {I1_PCC_I32[0]:.0f} +- {I1_PCC_I32[1]:.0f} MeV ({I1_PCC_I32[0] - TH_PCC32[0]:+.0f} MeV from "
          f"{TH_PCC32[1]}) is forbidden by H9: the two readings conflict there. LHCb's prompt search saw no doubly charmed "
          "pentaquark, which bounds production, not existence.\n")
md.append("### I2 (P2) hidden-bottom pentaquarks\n")
md.append("| partner of | bottom threshold | T [MeV] | binding carried over [MeV] | M (same binding) | M (binding x mu_b/mu_c) |")
md.append("|---|---|---|---|---|---|")
for d in I2_MOL:
    md.append(f"| {d['partner_of']} | {d['bottom_threshold']} | {d['T_bottom']:.1f} | {d['binding_charm']:+.1f} | "
              f"{d['M_same_binding']:.1f} | {d['M_mu_scaled']:.1f} |")
md.append(f"\nCompact ([bq][qq]) bbar (colour-spin model, KR convention): lowest level {I2_PB_COMPACT[0]:.1f} +- "
          f"{I2_PB_COMPACT[1]:.1f} MeV (variant J {I2_PB_COMPACT_J[0]:.1f}), multiplet {_pb_all[0]:.0f} to {_pb_all[-1]:.0f} MeV; "
          f"lowest J = 1/2 udsb bbar {I2_PBS_COMPACT[0]:.1f} +- {I2_PBS_COMPACT[1]:.1f} MeV. Lowest S-wave thresholds: {TH_PB[1]} "
          f"{TH_PB[0]:.1f}, {TH_PBS[1]} {TH_PBS[0]:.1f} MeV. Search status: {H9['I2']['search_status']}. Verdict: live.\n")
md.append("### I3 (P3) the general rule\n")
md.append(f"Established exotic hadrons without a pair of one flavour: {', '.join(I3_VIOLATORS)}. Verdict: {H9['I3']['verdict']}.\n")
md.append("### I4 (P4) Delta M = alpha M / 2 for spin doublets\n")
md.append("Eligible doublets, fixed from quark content and J^P only before any splitting was computed:\n")
for g, a1, a2 in I4_ELIGIBLE:
    md.append(f"- {g}: {a1} / {a2}")
md.append("\nNot eligible: " + "; ".join(f"{a} ({b})" for a, b in I4_NOT_ELIGIBLE) + ".\n")
md.append("| pair | Delta [MeV] | alpha M/2 | pull | colour-spin model Delta (pull) |")
md.append("|---|---|---|---|---|")
for r in I4_ROWS:
    mo = f"{r['model']['Delta']:.1f} +- {r['model']['err']:.1f} ({r['model']['pull']:+.1f}); {r['model']['desc']}" if "model" in r else "-"
    md.append(f"| {r['pair'][0]} / {r['pair'][1]} | {r['Delta']:.1f} +- {r['err']:.1f} | {r['alpha_M_over_2']:.1f} | "
              f"{r['pull']:+.1f} | {mo} |")
md.append(f"\n{I4_PASS} of {len(I4_ROWS)} pass at 2 sigma; {I4_EXPECT:.2f} expected by chance (Poisson p of at least {I4_PASS}: "
          f"{I4_P_EXCESS:.2f}); {I4_FAIL3} fail by 3 sigma or more. Motivating pair (excluded): Delta = {I4_MOTIVATING['Delta']:.1f}, "
          f"alpha M/2 = {I4_MOTIVATING['alpha_M_over_2']:.1f}. P_cs(4459) two-peak hypothesis (not resolved, info): Delta = "
          f"{I4_PCS_INFO['Delta']:.1f} +- {I4_PCS_INFO['err']:.1f} against {I4_PCS_INFO['alpha_M_over_2']:.1f}. Verdict: "
          f"{H9['I4']['verdict']}.\n")
md.append("### H9: choices made after seeing the data\n")
for i, c in enumerate(CHOICES_AFTER_DATA_H9, 1):
    md.append(f"{i}. {c}")
md.append("\n## Choices made after seeing the data\n")
for i, c in enumerate(CHOICES_AFTER_DATA, 1):
    md.append(f"{i}. {c}")
md.append("\n## Caveats\n")
for c in CAVEATS:
    md.append(f"- {c}")
md.append("\n## Citations (what was read, the values used)\n")
for k, v in CITATIONS.items():
    md.append(f"- **{k}**: {v['ref']}. Read: {v['read']}. Values: {v['values']}.")
md.append(f"\n## Checks\n\n{n_ok} of {n_all} passed.\n")
for c in check_log:
    md.append(f"- {'OK' if c['ok'] else 'FAIL'} {c['label']}")
(RESULTS / "exotic_hadrons.md").write_text("\n".join(md) + "\n")

print(f"{n_ok} of {n_all} checks passed; {n_hold} of {len(scored)} scored confrontations hold; runtime {out['runtime_s']:.0f} s")
sys.exit(0 if n_ok == n_all else 1)
