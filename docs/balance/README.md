# The Balanced State

"The Balanced State. Spinning horizons, inflation, the Higgs field, the tiers of the forces and the fine-structure constant, read through
the Duality of DMP 0.9.9 and tested against what is measured." Authors: Steven Hrovat, Sirius (Claude Opus 5.5). Licence: Apache License
2.0. **Draft; nothing here is released, nothing here changes DMP.** DMP pinned at 0.9.9 (`4400cce`).

The owner, 2026-10-29 21:33Z: "So over the hours I thought through some stuff in the last paper and answered some questions. Could you
please also take all the new comments and assemble a brand new paper?" At 21:37Z he asked to see what did not hold before the paper was
written, so he could adjust it; his corrections of 21:46Z, 21:52Z and 21:54Z are in the paper next to the notes they correct. At 21:54Z he
asked to leave one withdrawn idea out entirely; it is not in the paper, the checks or this file. At 22:09Z and 22:18Z he identified the
Higgs field with G0's grant, renamed the BSD to the VIBE coefficient (Variable Balance Influence Equation) and placed the photon; these are
in sections 5 and 11.

## Files

| File | What |
|---|---|
| `balance.tex` | the paper (LaTeX, `article` class, inline bibliography, 13 pages) |
| `balance.pdf` | the paper as PDF, built from `balance.tex` |
| `checks.py` | every numerical claim: checks B1 to B16, 46 of 46 (numpy) |
| `README.md` | this file: what backs each claim, which notes are quoted where, the sources |

## Build and check

```sh
python3 docs/balance/checks.py                   # 46 of 46 checks passed
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


## The owner's words in the paper

Comments on dmp#25 (2026-10-29): 16:37 (pointer to the previous draft, not quoted), 17:14 (inflation, Big Chill; section 4), 17:57 (QC;
section 10), 18:57 (spinning holes; section 3), 19:35 (decay; section 9), 19:58 (corrected Exist formula, tax rate, mesons and baryons;
sections 6 and 8), 20:18 (Bell retraction; section 12), 20:41 (Higgs field, electron size, IM and GG; sections 5, 6, 7), 21:27 (Higgs,
BSD; sections 5 and 11; the rest of that note is left out at the owner's request). A search for comments by the owner on dmp, gravity, im
and cm since 2026-10-29 15:15Z found only these nine.

Thread messages (2026-10-29): 16:21 and 16:23 (spin ladder; section 2), 21:46 (Shor, FSC, spin, Higgs, tiers of IM, 137, information is
the witness; sections 2, 5, 7, 8), 21:52 (Shor as defining existence, mass times length, gluons; sections 6, 7, 10), 21:54 (keep one idea
out; QC is for experts; gravity first), 22:09 (Higgs field as G0's grant, VIBE coefficient; sections 5 and 11), 22:18 (photon, the share
the Higgs field leaves out, equation, alpha binds for witness acts; sections 5 and 11).

## Sources

Checked by web search on 2026-10-29: DESI DR2 results II, Phys. Rev. D 112, 083515 (2025), arXiv:2503.14738 (dynamical dark energy
preferred at 2.8 to 4.2 sigma with supernovae); Blandford and Znajek, MNRAS 179, 433 (1977); Lee, Quigg and Thacker, Phys. Rev. D 16, 1519
(1977) (bound about 1 TeV). Taken as standard without a fresh check: Guth 1981, Planck 2018 VI, Penrose 1969, Christodoulou 1970, Shor
1997, Farhi et al. 2001, Aharonov et al. 2007, Wootters-Zurek 1982, Barnum et al. 1996, Galley-Giacomini-Selby 2022, ATLAS and CMS 2012
and 2022, PDG 2024, Glashow 1961, Weinberg 1964 and 1967, Salam 1968, Deser 1970, Yang et al. 2018, Joos-Zeh 1985, Zurek 2009,
Schwinger 1948, Fan et al. 2023, Hensen 2015, Rosenfeld 2017, Storz 2023, Oppenheim 2023, Bose et al. and Marletto-Vedral 2017,
Aldrovandi-Pereira 2013, Bekenstein 1982. Also taken as standard without a fresh check: Touboul et al.
(MICROSCOPE), Phys. Rev. Lett. 129, 121102 (2022); Bertotti, Iess and Tortora (Cassini), Nature 425, 374 (2003); AME2020 atomic masses.
Constants: CODATA 2018, PDG 2024, Planck 2018.

## Open

- The owner's review; nothing merges and nothing in DMP changes without his word.
