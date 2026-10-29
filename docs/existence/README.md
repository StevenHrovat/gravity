# Existence and Information

"Existence and Information. One vector field and one scalar field: the Duality of DMP 0.9.9 read as physics, derived where it can be and
tested where it touches data." Authors: Steven Hrovat, Sirius (Claude Opus 5.5). Licence: Apache License 2.0. **Draft; nothing
here is released, nothing here changes DMP.** DMP pinned at 0.9.9 (`4400cce`).

The paper is an application of DMP 0.9.9 to physics and stands alone: it cites DMP and the physics literature, and every number in it
comes from `checks.py` in this folder. The owner, 2026-10-29 15:57Z: "Please do not write it as referring to previous paper, but instead,
since the content varies so dramatically and is only an application of DMP, please write it as completely new."

## Files

| File | What |
|---|---|
| `existence.tex` | the paper (LaTeX, `article` class, inline bibliography, 21 pages) |
| `existence.pdf` | the paper as PDF, built from `existence.tex` |
| `checks.py` | every numerical claim: checks E1 to E22, 80 of 80 (numpy, sympy, scipy) |
| `README.md` | this spec: what backs each claim, which notes are quoted where, the sources checked |

## Build and check

```sh
python3 docs/existence/checks.py                 # 80 of 80 checks passed
cd docs/existence && export SOURCE_DATE_EPOCH=$(git log -1 --format=%ct -- existence.tex) FORCE_SOURCE_DATE=1 \
  && pdflatex existence.tex && pdflatex existence.tex && rm -f existence.aux existence.log existence.out
```

## The result in one paragraph

The owner's structure, stated first in the paper in his words (2026-10-29 15:25Z, 15:26Z, 15:33Z): one existence field, a vector frame
spanning all 3+1 directions (read as the tetrad), and one information field, a scalar that sets the fine-structure constant. Through DMP's
axioms: Axiom 3 gives universality of free fall, so the scalar may barely pull on matter (MICROSCOPE: |d ln alpha / d phi| < 2e-5, E3);
Axiom 1 keeps the scalar out of the gravitational equation, so gamma = 1 exactly (unlike Brans-Dicke, where Cassini forces omega > 4e4, E4);
Axiom 3's record, read in full by every witness, makes the existence field classical by no-broadcasting (E17), so DMP cannot model quantum
gravity and can host it as content. So the structure is general relativity plus a Bekenstein-type varying-alpha field, on
the classical side of the Bose-Marletto-Vedral test. The owner's "Existence = g h / c" is the only energy those three make and equals
4 pi^2 k T_Unruh (E1), the input of Jacobson's thermodynamic derivation of Einstein's equations: a new reading of known results. The
graviton: established arguments collapse the detector, not the graviton; one quantum forms a horizon only at the Planck energy, and then
any quantum (E6); single-graviton bars cannot tell a graviton from a classical wave (Carney, Domcke, Rodd 2024), as the owner said; but the
classical choice is falsifiable by gravitationally mediated entanglement. Bell "not violated under Dualism" is refuted as stated and
holds in the hosting reading (E19). Ledger of 33 statements: 19 hold or hold as readings, 9 refuted, 5 untested or live.

## What backs each claim

| Claim | Backing |
|---|---|
| E = g h / c is the unique energy of g, h, c; = 4 pi^2 k T_Unruh; = 4 pi^2 k T_Hawking at surface gravity | [E1] |
| Assertion rate as lapse: Pound-Rebka 2.46e-15, 33 cm clocks 3.6e-17, lapse 0 at the horizon | [E2] |
| Coulomb shares Ti 2.0e-3, Pt 4.1e-3; MICROSCOPE bound on lambda ~2e-5; drift bound 1.4e-15/yr against clocks 1.1e-18 | [E3] (coarse Earth composition, semi-empirical Coulomb term) |
| Brans-Dicke gamma, omega > 39998 at 2 sigma | [E4] |
| D(D-3)/2 polarisations, Weyl components: 2 and 10 in 3+1, 0 and 0 in 2+1 | [E5] |
| Kugelblitz of one quantum at sqrt(4 pi) L_P, sqrt(pi) E_P; 100 Hz graviton at 1.9e-41 of it; GW150914 > 1e78 quanta | [E6] |
| Dyson's count reconstructed: 3.8 absorptions in 5 Gyr | [E7] (inputs named: Gould 1985 luminosity, core temperature, Z/A = 1/2) |
| 2 G M_H / c^2 = c / H exactly | [E8] (sympy) |
| 1/alpha(M_Planck) ~ 105 (SM one loop); pure QED reaches 1 more than 250 orders above E_P | [E9] |
| Accretion efficiency 5.72%, 32.1% (a = 0.998), 42.3%; monotone; extractable share up, entropy down; Kerr-Newman area falls with Q | [E10] |
| Majority voting tolerance 0, 1, 1, 2, 2 for 2..6 nodes; colour singlets exist for every size from 2 | [E11] |
| Omega_nu = 1.4e-3 for 0.06 eV; neutrinos decelerate, Lambda accelerates | [E12] |
| Lab lifetime diverges as m -> 0 | [E13] |
| Boson spins in hbar; h*h not an energy, mass or action | [E14] |
| Grover: 256-bit preimage -> 2^128 | [E15] |
| Gravity / electric force p-e = 4.4e-40; atom-size curvature only above 1e47 kg/m^3 | [E16] |
| A record read in full by two is classical: copying needs overlap 0 or 1; the commutator of a non-commuting pair | [E17] |
| BMV geometry: entangling phase 1 rad after 8 s with a coherent mediator, none with a recorded one | [E18] |
| CHSH: local 2, full reach 4 and signals, singlet 2 sqrt 2, superdeterminism (S - 2)/3, measured S above 2 | [E19] (scipy linear programme) |
| Kerr area, spin bound and 29% from M^2 = m^2 + (J/2m)^2 | [E20] |
| Positronium 125 ps / 142 ns at leading order; muon 2.19 microseconds from Fermi's formula | [E21] |
| Hulse-Taylor orbital decay -2.402e-12 from the quadrupole formula; spin 1/2, 1, 2 rotations (720, 360, 180 degrees) | [E22] |

## The owner's words in the paper

All 42 comments the owner posted on dmp#25 (2026-10-28 12:18Z to 2026-10-29 15:13Z) were read. A search for other comments by the owner on
dmp and gravity pull requests updated since 2026-10-27 found none outside dmp#25. Times are UTC, as GitHub records them; an edited comment
is quoted in its edited form.

| Time | Topic | Section |
|---|---|---|
| 10-28 12:18 | "Information radiation" (HPE named, then withdrawn in an edit) | 3.5 |
| 14:25 | are we the Inflaton | 8.1, 8.2 |
| 14:37 | Event Horizons all the way down | 9 |
| 14:43 | ODP finds the right information fields | 8.1 |
| 14:46 | "Existence POSTs" | not quoted (a joke on the previous note) |
| 14:52, 14:53 | running on a DMP-complete system; "Thanks" | 9 |
| 15:00 | dimension boundaries, black holes as II parts | 5.1 (superseded by his 00:53 correction, which is quoted) |
| 15:04 | shutting the system down ethically | not quoted (personal) |
| 15:18 | AI inference and training | 9 |
| 15:33 | entropy as conversion inefficiency, spinning holes, white hole | 5.1, 5.2 |
| 15:41 | every "-ogy" | 9 |
| 16:06 | gravity is existence asserting itself | 3.6 |
| 16:49 | Bell was right | 6 |
| 16:53 | information fields interact, existence static | 6 |
| 17:01 | photons, gluons, gravitons always a wave | 7.1 |
| 17:30 | superdeterminism | 6 |
| 17:46 | ODP is needed | 8.1 |
| 17:49 | "closes the DoE decay comment" | not quoted (pointer to the previous note) |
| 18:15 | behaviour at horizons, bounce | 5 (superseded by 22:17 and 00:53) |
| 18:18 | photons as act carriers; gravitons shouldn't exist | 4.1, 7.1 |
| 18:22 | gluons as IM packets; CMOS as the strong force | 7.3 (by its 18:25 and 23:43 follow-ups) |
| 18:25 | three-node quark, two-node meson | 7.3 |
| 19:14 | Yang-Mills? | 7.7 |
| 19:30 | strong, weak, dark matter, dark energy | 7.7 |
| 20:19 | IM through a horizon | 7.7 |
| 21:20 | FSC as strong IM / EM binding | 8 (by its 21:47 follow-up, which the owner wrote after looking the formula up) |
| 21:47 | FSC started at 1, early gravity | 2.2, 8.1, 8.2 |
| 22:17 | things go in, total state comes out | 5.1 |
| 22:42 | the horizon question may be undefined | not quoted (superseded by 00:53) |
| 23:43 | part to node; quarks as leaf clusters; 2, 3, 4, 5 nodes | 7.3 (the rename is a proposal; DMP unchanged) |
| 23:58 | IM-net; ~1/137 | 8.1 |
| 10-29 00:53 | black holes contained in the host dimension; possibility space | 5.1 |
| 01:40 | Einstein; Existence = g h / c; the bosons; Trust = Existence | 2.3, 3.1, 3.5, 7.2 |
| 11:37 | neutrinos | 7.6 |
| 12:30 | FSC as coupling per energy; early Kugelblitz | 8.1 |
| 13:23 | FSC is how much the EM field exists | 2.2 |
| 13:26 | FSC as universal lowest entropy | 8.1 |
| 14:39 | Einstein's legacy | not quoted (personal) |
| 15:02 | Higgs as G0's remnant | 7.2 (scope corrected by the owner 16:07: only the bosons that need it) |
| 15:12 | flavours of h; W and Z as h*h | 7.2 |
| 15:13 | QC breaks cryptography | 9 |

Messages in the project threads on 2026-10-29: 09:24 (Bell under Dualism), 09:34 (alpha "slightly lower still"), 09:39 ("we can infer
all that we can and no more"), 09:41 (HPE correction), 15:20 (the graviton), 15:22 (single-graviton bars, simplicity), 15:25
(vector field and scalar field; photons, weight, singular quanta), 15:26 (the firewall origin), 15:33 (3+1 spans the existence vector), 16:07 (Higgs scope: only the bosons that need it), 16:16 (leptons as GG, the protocol between clusters; section 7.4), 16:21 and 16:23 (the spin ladder; gravitational waves from Non-Existence; section 7.5).

Emoji in quotes are written as words in brackets (pdflatex has no emoji font). "in its tooth" (15:20) is quoted as dictated; the paper
reads it as "in its truth".

## Sources checked (2026-10-29, by web search against publisher, arXiv, collaboration or repository records)

New in this paper, each found with matching authors, journal, volume and page or article number: Dyson, IJMPA 28, 1330041 (2013; abstract:
LIGO-type detectors cannot detect single gravitons, the mirrors would collapse into a black hole; Earth-size detector about four events in
the Sun's lifetime, as Quanta reports it); Rothman and Boughn, Found. Phys. 36, 1801 (2006; Jupiter-mass detector near a neutron star,
about one per decade, neutrino shield collapses); Tobar, Manikandan, Beitel, Pikovski, Nat. Commun. 15, 7229 (2024; beryllium 15 kg example,
aluminium 1800 kg, parameter table at 10 mK with bars to 15 000 kg); Tobar, Pikovski, Tobar, arXiv:2406.16898; Carney, Domcke, Rodd, PRD 109,
044009 (2024; the same signal explained by a classical wave); Carney, arXiv:2408.00094; Gould, ApJ 288, 789 (1985; 7.9e14 erg/s); MICROSCOPE,
PRL 129, 121102 (2022; eta = (-1.5 +- 2.3 +- 1.5)e-15); Dvali and Zaldarriaga, PRL 88, 091303 (2002); Sandvik, Barrow, Magueijo, PRL 88,
031302 (2002); Alvarez-Dominguez, Garay, Martin-Martinez, Polo-Gomez, PRL 133, 041401 (2024; Schwinger effect, radii 1e-29 to 1e8 m); Page's
comment arXiv:2505.16202; Pathria, Nature 240, 298 (1972); Yang et al., PRL 121, 212001 (2018; quark mass term 9%); DESI 2024 VI, JCAP 02
(2025) 021 (sum < 0.072 eV); LHCb pentaquarks PRL 115, 072001 (2015). Taken as standard without a fresh check: Weinberg 1964, Deser 1970, Peters-Mathews 1963, Weisberg-Huang 2016, GW150914 PRL 116 061102, Borexino 2015, PDG 2024, Ore-Powell 1949, Unruh 1976, Jacobson 1995,
Brans-Dicke 1961, Bekenstein 1982 and 2004, Jacobson-Mattingly 2001, GW170817 ApJL 848 L13, Will's Living Review 2014, Page-Geilker 1981,
Bardeen-Press-Teukolsky 1972, Landauer 1961, Bekenstein 1973, Mead 1964, Wheeler 1955, Kofman-Linde-Starobinsky 1994, ATLAS and CMS
Nature 607 (2022), LHCb T_cc Nat. Phys. 18, 751 (2022), Shor 1997, Grover 1997, FIPS 205, Aldrovandi-Pereira 2013, von Neumann 1956.
The PDG inputs of E9 (1/alpha(M_Z) = 127.951, sin^2 theta_W = 0.23122) are quoted from memory of the PDG 2024 values; a change in the third
digit does not change the result. Bell and black-hole references (Clauser-Horne-Shimony-Holt 1969, Fine 1982, Cirel'son 1980, Hall 2010,
Hensen 2015, Rosenfeld 2017, Storz 2023, Kerr 1963, Wootters-Zurek 1982, Barnum et al. 1996, Galley-Giacomini-Selby 2022, Bose et al. and
Marletto-Vedral 2017, Oppenheim 2023, Christodoulou 1970) were checked on 2026-10-29 for the same project's earlier drafts.

## Open

- Lean: no toolchain could be installed in the session that wrote this; the paper claims no machine-checked theorem.
- The owner's review; nothing merges and nothing in DMP changes without his "approved".
