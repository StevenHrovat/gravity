# GUID v5: Quantum Gravity

"GUID v5: Quantum Gravity. A classical existence frame carrying quantum information: what the axioms of the Dark Matter Protocol fix
about gravity, what they leave to quantum theory, and the experiments that decide." Authors: Steven Hrovat, Sirius (Claude, Anthropic).
Licence: Apache License 2.0. **Draft; nothing here is released, nothing here changes DMP.** DMP pinned at 0.9.9 (`4400cce`).

The fifth paper of the GUID series and the first that states the whole account of quantum gravity in one place. It stands on its own: it
cites DMP 0.9.9 and the physics literature only, quotes DMP's text where the wording matters, and states every reading of the axioms as a
numbered hypothesis (H1 to H7) instead of quoting notes. It consolidates the verdict of `docs/qg-verdict.md`, the papers in `docs/guid/`,
`docs/existence/` and `docs/balance/`, the Bell follow-up draft (gravity#29), the refutation record (`docs/refutation.md`) and the
owner's notes on dmp#25 up to and including the dark-matter note of 2026-10-30; and it adds what those did not have: the consistency of a
classical frame with quantum matter (the decoherence-diffusion trade-off), the identification of DMP's record-and-recompute structure with
measurement-and-feedback models of gravity, the LOCC test without entanglement, the effective-field-theory baseline, the primordial tensor
modes and the start, three routes by which the theory traps remnants of interactions in the gravitational field (dark matter), and a
comparison with the main approaches to quantum gravity.

## Files

| File | What |
|---|---|
| `quantum-gravity.tex` | the paper (LaTeX, `article` class, inline bibliography, 37 pages, one appendix) |
| `quantum-gravity.pdf` | the paper as PDF, built from `quantum-gravity.tex` |
| `checks.py` | every numerical claim: checks Q1 to Q19, 112 of 112 (numpy, scipy, sympy) |
| `de/guid-v5-quantengravitation.pdf` | the German translation; the English original governs. Only the PDF is tracked, as for v4: the public-repository scan rejects German letters in tracked text |
| `README.md` | this file: what backs each claim, the sources |

## Build and check

```sh
python3 docs/quantum-gravity/checks.py          # 112 of 112 checks passed
python3 docs/qg-verdict/assembly.py             # 18 of 18: the holographic-code assembly (A1 to A5 in the paper)
cd docs/quantum-gravity && pdflatex quantum-gravity.tex && pdflatex quantum-gravity.tex && pdflatex quantum-gravity.tex \
  && rm -f quantum-gravity.aux quantum-gravity.log quantum-gravity.out quantum-gravity.toc
```

Three runs because of the table of contents. Built clean (no overfull box, no undefined reference) on 2026-10-30.

## What backs each claim

| Claim | Backing |
|---|---|
| The only energy of g, h, c is g h / c = 4 pi^2 k T_Unruh; T_U, T_H, S_BH; Jacobson's eta returns G; the EFT quantum term at 1 m | [Q1] |
| Lapse: Pound-Rebka 2.46e-15, 33 cm 3.6e-17, zero at the horizon | [Q2] |
| No-cloning (overlap 0 or 1); a fixed-basis copier broadcasts exactly the diagonal states | [Q3] |
| A recorded mediator never entangles (300 random couplings), a coherent one does (Lemma 4) | [Q4]; assembly [6] |
| BMV geometry: 0.126 rad/s, 1 rad after 8.0 s, maximal after 25 s; zero with a recorded field | [Q5] |
| MICROSCOPE: abs(d ln alpha / d phi) < 2e-5; a Higgs-share-only gravity would give eta ~ 1e-3 | [Q6] |
| Brans-Dicke omega > 4e4 (Cassini) | [Q7] |
| D(D-3)/2 polarisations, Weyl components: 2, 10 in 3+1; 0, 0 in 2+1 | [Q8] |
| One quantum inside its own horizon at sqrt(4 pi) L_P, sqrt(pi) E_P; 100 Hz graviton 1.9e-41 of it; GW150914 > 1e78 quanta | [Q9] |
| Kerr: ergosphere outside the horizon, Christodoulou's formula, 29%, efficiencies 5.7%, 32%, 42.3% | [Q10] |
| Solar-mass hole 6.2e-8 K < 2.7 K; equal-temperature mass 0.6 lunar masses; evaporation > 1e66 yr | [Q11] |
| 2 G M_H / c^2 = c / H at every epoch | [Q12] (sympy) |
| About 62 e-folds for flatness; de Sitter floor 0.83 H0; acceleration since z = 0.63 | [Q13] |
| P_t = 16 G hbar H^2 / (pi c^5); r < 0.036 means V^(1/4) < 1.4e16 GeV; Starobinsky r = 0.0033; n_t = -r/8 | [Q14] |
| Requirements on any remnant: neutrinos < 0.7% of dark matter; Pauli bound > 170 eV for a dwarf; relic 3200 km/s and stellar ~c against 533 km/s escape; baryon share 0.157 | [Q15] |
| a_e = alpha / 2 pi within 0.15%; r_e / lambda_C-bar = lambda_C-bar / a_0 = alpha; gravity/EM in hydrogen 4.4e-40; G m_e^2 / hbar c; 1/alpha(E_P) = 105 | [Q16] |
| abs(c_gw / c - 1) of order 4e-16 from GW170817 | [Q17] |
| Stochastic remnant: Lambda = 1.09e-52 /m^2, c^2 sqrt(Lambda/3)/2pi = 8.6e-11 m/s^2; r* = 17 kpc, v* = 227 km/s for 1e11 solar masses and abs(gamma1) = 1e-10 m/s^2 (gamma1 < 0, attractive; the Lambda term subtracts); 12% change from r*/2 to 2 r*; v^4 proportional to M. Contained remnant: T_H 1.2e9 K and 1.2e4 K at 1e14 and 1e19 kg, kT 0.1 MeV, evaporated below a few 1e11 kg. Radiated remnant: Omega_gw 8e-9 at 1/yr | [Q18] |
| Bridge A (cosmological event horizon as cut-off): abs(gamma1) = 0.90 to 1.00 c H_inf = 4.9 to 5.4e-10 m/s^2, 8.1 times too strong in v^4 (1.69 in v); 337 km/s at 7.6 kpc against 200 km/s for 1e11 solar masses; 620 km/s at 50 kpc. Bridge B (Planck-strength record, trade-off at equality): discrete model 1.2e-51 kg s, excluded; Diosi-Penrose kernel 1.6e-24 kg^2 s/m, allowed; rate G M^2 / hbar R; fullerene 6.3e-16 /s; the 1e-14 kg diamond microsphere (R = 0.88 um) 72 /s, 13.9 ms, 1.74e-3 rad of entangling phase | [Q19] |
| Minimal cuts, any 3 of 5, syndrome reading, CHSH 2.83 against 2 | `docs/qg-verdict/assembly.py` [1] to [5] |

## Sources

**Checked by web search on 2026-10-30 for this paper:** Goroff and Sagnotti, Nucl. Phys. B 266, 709 (1986); Oppenheim, Sparaciari,
Soda, Weller-Davies, Nat. Commun. 14, 7910 (2023), arXiv:2203.01982, the trade-off quoted from its Eq. (23) in the arXiv text;
Kafri, Taylor, Milburn, New J. Phys. 16, 065020 (2014); Tilloy and Diosi, Phys. Rev. D 93, 024026 (2016); Krauss and Wilczek, Phys. Rev.
D 89, 047501 (2014); BICEP/Keck, Phys. Rev. Lett. 127, 151301 (2021), r < 0.036; Tristram et al., Phys. Rev. D 105, 083524 (2022), r <
0.032; Donadi et al., Nat. Phys. 17, 74 (2021); Lami, Pedernales, Plenio, Phys. Rev. X 14, 021022 (2024); Piffl et al., A&A 562, A91
(2014), 533 km/s; LiteBIRD, PTEP 2023, 042F01; Jacobson 1995, the sound-in-air sentence (it is in the paper's conclusion, worded as quoted).
Ambjorn et al., arXiv:0712.2485: the journal reference could not be confirmed, so only the arXiv number is cited. For the dark-matter
section: Oppenheim and Russo, arXiv:2402.19459 (2024; the potential with linear and quadratic terms, gamma2 = Lambda/3, gamma1 of order
1e-10 m/s^2, and the authors' caveats, read in the arXiv HTML); Cotner, Kusenko, Takhistov, Phys. Rev. D 98, 083513 (2018); Gorton and
Green, SciPost Phys. 17, 032 (2024); NANOGrav 15 yr, ApJL 951, L8 (2023), h_c = 2.4e-15 at 1/yr; Clowe et al., ApJL 648, L109 (2006);
Amin et al., Phys. Rev. Lett. 108, 241302 (2012); Milgrom, ApJ 270, 365 (1983); Hehl and Mashhoon, arXiv:0812.1059 (its journal reference
could not be confirmed, so the arXiv number is cited).

**Carried from the earlier papers of the series, checked there on 2026-10-27 and 2026-10-29:** Galley-Giacomini-Selby, Bose et al.,
Marletto-Vedral, Barnum et al., Wootters-Zurek, Dieks, Brandao-Piani-Horodecki, Vidal-Werner, the HaPPY model, Almheiri-Dong-Harlow,
Ryu-Takayanagi, Harlow 2017, Dong-Harlow-Marolf, Laflamme et al., Heydeman et al., Gubser et al., Rabinovich-Raz, Deser-Jackiw-'t Hooft,
Witten 1988, Brown-Henneaux, Maloney-Witten, Nelson-Regge, 't Hooft 1988, Aziz-Howl, Marletto-Oppenheim-Vedral-Wilson, Diosi 2025,
Schneider-Huggett-Linnemann, Gundhi-Infantino-Bassi, Christodoulou et al. 2023, Dyson, Rothman-Boughn, Tobar et al., Carney-Domcke-Rodd,
MICROSCOPE, Dvali-Zaldarriaga, Lange et al., Murphy et al. (ESPRESSO), Planck XXIV, DESI 2024 VI, DESI DR2, Yang et al., Fan et al.,
Bekenstein 1982, Sandvik-Barrow-Magueijo, Pathria.

**Taken as standard without a fresh check:** 't Hooft and Veltman 1974; Donoghue 1994; Bjerrum-Bohr, Donoghue and Holstein 2003 (the
41/(10 pi) coefficient); Hawking 1975; Bekenstein 1973; Page 1993; Penington 2020; Almheiri, Engelhardt, Marolf and Maxfield 2019; Eppley
and Hannah 1977; Page and Geilker 1981; Oppenheim 2023 (PRX); Moller 1962; Rosenfeld 1963; Diosi 1987; Penrose 1996; Westphal et al.
2021; Colella, Overhauser and Werner 1975; Nesvizhevsky et al. 2002; Carney, Stamp and Taylor 2019; Unruh 1976; Pound and Rebka 1960;
Chou et al. 2010; Jacobson 2016; Landauer 1961; Israel 1967; Kerr 1963; Christodoulou 1970; Bardeen, Carter and Hawking 1973; Penrose
1969; Blandford and Znajek 1977; Bardeen, Press and Teukolsky 1972; Cleve, Gottesman and Lo 1999; Gell-Mann and Hartle 1990; Halliwell
1989; Kiefer 1987; Hartle and Hawking 1983; Guth 1981; Planck 2018 VI; Starobinsky 1979 and 1980; Polarski and Starobinsky 1996;
Tremaine and Gunn 1979; Kofman, Linde and Starobinsky 1994; Higgs 1964; Englert and Brout 1964; Schwinger 1948; Glashow 1961; Weinberg 1964, 1967
and 1979; Salam 1968; Deser 1970; Amaldi, de Boer and Furstenau 1991; Maldacena 1998; Ashtekar 1986; Rovelli and Smolin 1995; Reuter
1998; Bombelli, Lee, Meyer and Sorkin 1987; Van Raamsdonk 2010; Maldacena and Susskind 2013; Aldrovandi and Pereira 2013; Jacobson and
Mattingly 2001; GW170817; GW150914; Will 2014; Brans and Dicke 1961; Cassini; Deutsch 1985; Zurek 2009; Mead 1964; Goguen and Meseguer
1982; Denning 1976; Malkhi and Reiter 1998; O'Hearn, Reynolds and Yang 2001; de Moura and Ullrich 2021. Each is to be checked against
the publisher's or arXiv's page before release.

Constants: SI 2019, CODATA 2018, PDG 2024, Planck 2018.

## The owner's answers (2026-10-30)

- The beginning: inflation and the decay of its oscillons are one start, the minting (Hypothesis 6).
- Dark matter: the trapped-neutrino idea is dropped; the paper proposes that the modelling lets remnants of interactions be trapped in the
  gravitational field (Hypothesis 7) and calculates three routes (Section 11.6, [Q18]).
- The stance: supplied with the base configuration currently assumed for our universe, DMP hosts the proposed theory of quantum gravity
  (Theorem 1).
- Category gr-qc; a German translation.
- The author line: the owner asked for "Opus 5.5" after Sirius. Sessions that write to these repositories may not put a model identifier
  into pushed files, so the line reads "Sirius (Claude, Anthropic)"; the owner can change it in `quantum-gravity.tex` (the `\author` line and
  "Contributions and use of AI").

## Follow-up (2026-10-30, the owner: "Please correct the mistakes, add the new stuff and merge")

- Corrected: the circular speed of the stochastic remnant. gamma1 is negative (its mean attracts) and the Lambda term subtracts:
  v^2 = G M / r + abs(gamma1) r / 2 - gamma2 r^2 (Section 11.6 and the same line in `checks.py`). No number changes: the Lambda term is
  below 1e-4 of v^2 there.
- Added: "What is new and what is not" (Section 1.3): the physics belongs to the classical-quantum family; what is new is the route from an
  information principle and four statements. Section 5.4, "Fixing the free constant": the balance rule (the trade-off at equality), Bridge A
  (refuted) and Bridge B (the Diosi-Penrose rate, live), with checks Q19. The tables, the conclusion, the abstract and the German
  translation follow.
- Sources for Section 5.4, checked 2026-10-30: Oppenheim et al. 2023, Eqs. (44), (46), (47) and their numerical windows (read in the arXiv
  text); Oppenheim and Russo 2024, Eq. (20) and the definitions of gamma0, gamma1, gamma2 (arXiv HTML); Donadi et al. 2021 (the lower bound
  on the nuclear smearing length, of order 1e-10 m as reported); Figurato et al., New J. Phys. 26, 113004 (2024), which quotes 4e-10 m.

## Open

- The owner's review; nothing merges and nothing in DMP changes without his word.
