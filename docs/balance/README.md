# GUID v4: The Balanced State

"GUID v4: The Balanced State. Existence as the grant of the ground: spinning horizons, inflation, the Higgs field, the tiers of the forces
and the fine-structure constant, read from the axioms of DMP 0.9.9 and tested against what is measured." Authors: Steven Hrovat, Sirius
(Claude Opus 5.5). Licence: Apache License 2.0. **Draft; nothing here is released, nothing here changes DMP.** DMP pinned at 0.9.9
(`4400cce`). The fourth paper of the GUID series; complete on its own, it cites only DMP 0.9.9 and the physics literature.

The owner, 2026-10-29 21:33Z: "So over the hours I thought through some stuff in the last paper and answered some questions. Could you
please also take all the new comments and assemble a brand new paper?" At 21:37Z he asked to see what did not hold before the paper was
written, so he could adjust it, and sent corrections from 21:46Z to 22:18Z. At 21:54Z he asked to leave one withdrawn idea out entirely;
it is not in the paper, the checks or this file. At 22:28Z: "Please make them all full, complete papers, able to stand on their own. I
want to document my path to Insight in complete stages", and at 22:31Z "Let's just try GUID v4, to stay consistent" (the earlier papers
stay as they are). So the paper states the axioms, the ground and the VIBE field in full, derives its foundations (Propositions 1 and 2,
Lemmas 1 and 2), states each claim as its own, and collects the notes it is built from, in the order written, in Appendix A.

## Files

| File | What |
|---|---|
| `balance.tex` | the paper (LaTeX, `article` class, inline bibliography, 18 pages, two appendices) |
| `balance.pdf` | the paper as PDF, built from `balance.tex` |
| `de/guid-v4-der-ausgeglichene-zustand.pdf` | the German translation (19 pages), at the owner's request (2026-10-29 22:20Z, 22:26Z); the English original governs. Only the PDF is tracked: the public-repository scan (`tools/scrub-scan.sh`) rejects German letters in tracked text, so the LaTeX source stays outside the repository |
| `checks.py` | every numerical claim: checks B1 to B19, 56 of 56 (numpy) |
| `README.md` | this file: what backs each claim, which notes are quoted where, the sources |

## Build and check

```sh
python3 docs/balance/checks.py                   # 56 of 56 checks passed
cd docs/balance && export SOURCE_DATE_EPOCH=$(git log -1 --format=%ct -- balance.tex) FORCE_SOURCE_DATE=1 \
  && pdflatex balance.tex && pdflatex balance.tex && rm -f balance.aux balance.log balance.out
```

## What backs each claim

| Claim | Backing |
|---|---|
| About 62 e-folds flatten an order-one curvature to Planck's bound (reheating at 1e15 GeV) | [B1] |
| Hubble rate falls monotonically to sqrt(Omega_L) H0 = 0.83 H0; acceleration since z = 0.63 | [B2] |
| Shor period finding for 15: factors 3 and 5 with a coherent register, a flat 1/256 with a recorded one | [B3] |
| Ergosphere (r = 2M) outside the horizon; extractable spin energy up to 29% | [B4] |
| Seven decays keep charge, baryon and lepton number and lose rest mass | [B5] |
| h (1/c) alpha is mass times length; r_e / lambda_C-bar = lambda_C-bar / a_0 = alpha | [B6] |
| Colour singlet: each pair of colours fixes the third; invariant under SU(3) | [B7] |
| Lee-Quigg-Thacker unitarity bound about 1 TeV; Higgs at 125 GeV below it | [B8] |
| sin^2 theta_W = 0.2304 from alpha(M_Z), G_F, m_W; alpha_s / alpha = 15 at M_Z; alpha_s reaches 1 near 0.2 GeV | [B9] |
| a_e = alpha / 2 pi within 0.15% of the measured value | [B10] |
| alpha h / c = m_e 2 pi r_e | [B11] |
| Light crossing of the proton 2.8e-24 s | [B12] |
| Higgs lifetime 1.6e-22 s; gravity's coupling to the electron 1e39 times weaker than the Higgs coupling | [B13] |
| SM couplings come within about 10% near 1e14 GeV and do not meet (one loop) | [B14] |
| Electromagnetic self-energy of the proton about 1 MeV, 1/900 of its mass | [B15] |
| Gravity weighing only the Higgs share would split titanium and platinum by about 1e-3; MICROSCOPE: equal to 1e-15 | [B16] |
| One unitary copies two states only if their overlap is 0 or 1; |0> and |+> cannot be broadcast (Lemma 1) | [B17] |
| Brans-Dicke gamma - 1 = -1/(omega + 2); Cassini forces omega > 4e4 (Proposition 2) | [B18] |
| Hawking temperature of a solar-mass hole 6.2e-8 K, far below the 2.7 K sky | [B19] |


## The owner's words in the paper

All of them stand in Appendix A, in the order written, with [...] for passages left out; the main text quotes short pieces as each claim.
Thread messages of 2026-10-29: 15:25 (one existence, one information; Definition 1), 16:21 (spin ladder; section 3), 21:46 (spin, Higgs,
tiers of IM, 137, information is the witness; sections 3, 5, 7, 8), 21:52 (defining existence, mass times length, gluons; sections 6, 7,
10), 22:09 (Higgs field as G0's grant, VIBE coefficient; sections 5.3 and 11), 22:18 (photon, the share the Higgs field leaves out,
equation, alpha binds for witness acts; sections 5 and 11), 23:43 (Variable Influence Balancing Equation; the Higgs field IS G0
providing existence, with his thanks to Peter Higgs and all who laid the groundwork, in full in the Acknowledgements at his request;
Hawking-Penrose-Information radiation; sections 2.3, 4.1, 5.3, 11). Comments on dmp#25 (2026-10-29): 17:14 (inflation; 4.2), 17:57 (QC; 10),
18:57 (spinning holes; 4.1), 19:35 (decay; 9), 19:58 (exist formula, tax rate, baryons; 6, 8), 20:18 (Bell retraction; 10), 20:41 (Higgs,
electron size, a first grouping of the forces; 5, 6, 7), 21:27 (Higgs, BSD; 5, 11; the rest of that note is left out at the owner's
request). 16:37 was a pointer to the previous draft and is not quoted; 21:54 (keep one idea out; QC is for experts; gravity first) shaped
the paper and is not quoted. A search for comments by the owner on dmp, gravity, im and cm since 2026-10-29 15:15Z found only these nine.

## Sources

Checked by web search on 2026-10-29: DESI DR2 results II, Phys. Rev. D 112, 083515 (2025), arXiv:2503.14738 (dynamical dark energy
preferred at 2.8 to 4.2 sigma with supernovae); Blandford and Znajek, MNRAS 179, 433 (1977); Lee, Quigg and Thacker, Phys. Rev. D 16, 1519
(1977) (bound about 1 TeV). Taken as standard without a fresh check: Guth 1981, Planck 2018 VI, Penrose 1969, Christodoulou 1970, Shor
1997, Farhi et al. 2001, Aharonov et al. 2007, Wootters-Zurek 1982, Barnum et al. 1996, Galley-Giacomini-Selby 2022, ATLAS and CMS 2012
and 2022, PDG 2024, Glashow 1961, Weinberg 1964 and 1967, Salam 1968, Deser 1970, Yang et al. 2018, Joos-Zeh 1985, Zurek 2009,
Schwinger 1948, Fan et al. 2023, Hensen 2015, Rosenfeld 2017, Storz 2023, Oppenheim 2023, Bose et al. and Marletto-Vedral 2017,
Aldrovandi-Pereira 2013, Bekenstein 1982. Also taken as standard without a fresh check: Touboul et al.
(MICROSCOPE), Phys. Rev. Lett. 129, 121102 (2022); Bertotti, Iess and Tortora (Cassini), Nature 425, 374 (2003); AME2020 atomic masses; Will, Living Rev. Relativ. 17, 4 (2014); Higgs, Phys. Rev. Lett. 13, 508 (1964); Englert and Brout, Phys. Rev. Lett. 13, 321 (1964); Hawking, Commun. Math. Phys. 43, 199 (1975); Brans and Dicke, Phys. Rev. 124, 925 (1961).
Constants: CODATA 2018, PDG 2024, Planck 2018.

## Open

- The owner's review; nothing merges and nothing in DMP changes without his word.
