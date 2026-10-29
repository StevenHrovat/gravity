# Host, not model: the follow-up to GUID

"Host, Not Model. What the Duality of Trust can say about quantum gravity, and what the Bell experiments say about the Duality."
Authors: Steven Hrovat, Sirius (Claude Opus 5.5). Licence: Apache License 2.0, as GUID. **Draft; nothing here is released, nothing here
changes DMP.** DMP pinned at 0.9.9 (`4400cce`), as GUID.

The owner, 2026-10-29 09:24Z: "Let's make a followup paper about exactly what we can now model from QG and how it could be used for real
science. Let's focus on showing why the 2022 nobel price winning bell experiment actually did not violate Bell inequality under Dualism."

## Files

| File | What |
|---|---|
| `bell.tex` | the paper (LaTeX, `article` class, inline bibliography, 14 pages) |
| `bell.pdf` | the paper as PDF, built from `bell.tex` |
| `checks.py` | every numerical claim: checks B1 to B7, 22 of 22 (numpy; scipy for B5's linear programme) |
| `README.md` | this spec: what backs each claim, the owner's words with times, the open questions |

## Build and check

```sh
python3 docs/bell/checks.py                      # 22 of 22 checks passed
python3 docs/qg-verdict/assembly.py              # GUID's checks, 18 of 18 (used: [2] to [6])
cd docs/bell && export SOURCE_DATE_EPOCH=$(git log -1 --format=%ct -- bell.tex) FORCE_SOURCE_DATE=1 \
  && pdflatex bell.tex && pdflatex bell.tex && rm -f bell.aux bell.log bell.out
```

## The result in one paragraph

The hypothesis "did not violate Bell's inequality under Dualism" does not survive as stated: every loophole-free test measured CHSH above
2 (Delft 2.42 +- 0.20, Munich 2.22 +- 0.033, ETH Zurich 2.0747 +- 0.0033), in four kinds of system, three of them matter. Of four readings
of the Duality, isolated halves are refuted (S <= 2), full reach signals and overshoots to 4 with no DMP principle that stops at 2.83,
a superdeterministic root needs measurement dependence M >= (S - 2)/3 and collides with DMP's own independence of witnesses, and the
hosting reading survives: the measured particles are content, the Duality's verdicts stay at 2. So the Bell experiments are independent
evidence for GUID's "cannot model, can host". Part 1: DMP is on the classical-gravity side, so a positive Bose-Marletto-Vedral test
refutes every reading in which a DMP structure is the geometry; with Oppenheim's dynamics the decoherence-diffusion trade-off applies;
and device-independent protocols can only run in content.

## What backs each claim

| Claim | Backing |
|---|---|
| Isolated halves obey S <= 2 | `checks.py` [B1]; Lean `NoGo.gate_obeys_chsh` (gravity#17, unmerged) |
| Full reach reaches 4 and signals; no-signalling alone reaches 4 | [B2], [B3]; Lean `Refute.rf_full_reach_reaches_four` (main) |
| Quantum mechanics stops at 2 sqrt 2 | [B4] |
| M_min(S) = (S - 2)/3 | [B5], linear programme at six values (not a proof); matches Hall 2010's ~14% for the singlet and 1/3 at S = 4 |
| The measured values | [B6]; references below |
| Coherent gravity entangles, recorded gravity does not | [B7]; GUID check [6] |
| Content at 2 sqrt 2, verdicts at 2, together | GUID check [5] |

## Sources checked (2026-10-29, by web search against publisher, arXiv, collaboration or repository records)

Every entry of the bibliography was found with matching authors, journal, volume and page or article number. Numbers quoted in the text:
Hensen 2015 S = 2.42 +- 0.20, p = 0.039; Giustina 2015 p <= 3.74e-31 (11.5 s.d., published version); Shalm 2015 adjusted p = 2.3e-7;
Rosenfeld 2017 S = 2.22 +- 0.033, p < 1.05e-9; Storz 2023 S = 2.0747 +- 0.0033, > 22 s.d.; Handsteiner 2017 ~600 years; Rauch 2018
>= 7.78 Gyr; BIG Bell Test ~100,000 participants, 12 labs; Aspect 1982 5 s.d.; PDG W mass 80.3692 +- 0.0133 GeV; Super-K p -> e+ pi0
> 2.4e34 yr; neutron 878.4 +- 0.5 s; Borexino electron > 6.6e28 yr; Planck XXIV alpha/alpha0 = 0.9934 +- 0.0042; ESPRESSO combined
-0.5 +- 0.5 (stat) +- 0.4 (sys) ppm over z = 0.6-2.4; Lange 2021 (1.0 +- 1.1)e-18 per year; Chou 2010 33 cm, ~4e-17; Cassini gamma - 1 = (2.1 +- 2.3)e-5; Pound-Rebka 1960 tower 74 ft; PDG charged pion 2.6033e-8 s; Israel 1967; EHT 2019 ApJL 875 L1; Hawking 1975; Page 1993; Fewell 1995 Ni-62 most tightly bound; Dreyer and Martins 2026 BBN bounds of tens
of ppm (2 +- 22 and 2 +- 51 ppm by scenario). Not quoted because not verified: the S value of Weihs 1998 (only a secondary source), the
precise PDG alpha(M_Z) (the text says "close to 1/128"). The Nobel citation sentence is quoted from the press coverage that reproduces it;
nobelprize.org was not reachable from the session.

## The owner's words in the paper (all 2026-10-29, verbatim)

| Time (Z) | Where | Section |
|---|---|---|
| 09:24 | the question | 1, 6 (Hypothesis 1) |
| 09:26 | photons and gluons as act carriers | 7 |
| 09:29 | the mass of the W and Z, "part" to "node" | 8.1 (the rename is a proposal; DMP unchanged) |
| 09:30 | the Higgs mechanism as axiomatic correctness | 8.1 |
| 09:32 | decay, the electron | 8.2 |
| 09:34 | the fine-structure constant | 8.3 |
| 09:37 | the fall during reheating ("Ocelons", read as oscillons) | 8.3 |
| 09:39 | "we can infer all that we can and no more" | 11 (conclusion) |
| 09:40 | the ODP explanation (his comment on dmp#25, 2026-10-28), posted as a screenshot | 8.3 |
| 09:41 | "HPE was wrong, it is just Information and Existence." | 8.3, after the ODP quote |
| 09:42 | his reading of gravity (his comment on dmp#25, 2026-10-28), posted as a screenshot | 3.5 |
| 09:51 | clarifications: the photon carries its existence key (Planck's constant) and obeys curvature; "three nodes" meant more stable than two | 7, 3.5, 8.1 |
| 09:52 | "at the end, maybe give a short outlook and on how our model would model the way through an event horizon" | 10 (outlook) |

## Open

- The owner's choice of framing for the Bell part (asked in the thread; the draft follows the recommended one: "violated; Dualism reads
  it as content").
- The owner wrote that he had "already done it axiomatically": if that derivation is written down, it belongs in Section 6 verbatim.
- Title, author block and release route follow GUID's unless the owner says otherwise.
