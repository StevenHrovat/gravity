# GUID v7: primordial black holes from a lagging switch — report

Private exploration, finished 2026-11-01. Nothing was pushed or published. Every run is logged in `logs/runs.jsonl` with its parameters, outcome and wall time; files are listed in
`README.md`. Each external number carries an arXiv id or DOI and the date read (2026-11-01, `sources/citations.md`) or is marked "from memory".

## Verdict in five lines

1. **WP1:** the spherical collapse code passes its gate. Radiation thresholds are 0.4668 / 0.4978 / 0.5536 for q = 0.5 / 1 / 3 against windows 0.44–0.48 / 0.47–0.51 / 0.53–0.57, and are
   resolution-stable to < 0.0005.
2. **WP2:** the gauge objection holds in radiation. Reproduced and independently confirmed, the late-patch mechanism with fast reheating gives no PBH dark matter at any β/H ≥ 4. The
   early-matter-era rescue works: with Γ/H* = 3e-3 to 3e-4, f = 1 needs β/H ≈ 9.3–15.
3. **WP3:** the window allowed by current limits is 2.0e17–9.8e21 g. f = 1 sits inside it for 1e18–1e21 g with the WP2 parameters; 1e17 g and 1e22 g are now excluded.
4. **WP4:** with the matter-era dilution (exact: D = 0.92 (Γ/H*)^{2/3}) the hum peaks at 0.006–2.4 Hz with Ω h² ≈ 1.5e-11 to 2e-10. DECIGO and BBO hear every case, LISA the heavy end, ET
   and CE the light end. LVK O3 sees nothing.
5. **WP5:** the table is consistent and the inversion closes exactly. But the pass-or-fail test cannot fail yet: it needs β/H to about 2%, while model systematics move the predicted f_PBH by up
   to about 10 orders of magnitude. The exception is the heavy, slow-decay corner, where 20% suffices.

---

## WP1 — validated spherical collapse code (gate PASSED)

Long form: `wp1/RESULTS.md`.

**What holds.**
- **Formulation.** Misner–Sharp in comoving slicing on a staggered Lagrangian grid; the centre is regular by construction (R = U = M = 0 at the central shell, Hamiltonian constraint exact via
  ΔM/ΔV). Quadratic von Neumann–Richtmyer viscosity (C2 = 2, fixed a priori) with its own time-step limit.
- **Initial data.** The gradient expansion is derived symbolically, not calibrated; the only residual is O(ε⁴).
- **Gate thresholds**, all unchanged at N1 = 160 / 320 / 640:

  | q | ours | analytic (Escrivà–Germani–Sheth, 1907.13311) |
  |---|---|---|
  | 0.5 | 0.4668 | 0.4569 |
  | 1 | 0.4978 | 0.4892 |
  | 3 | 0.5536 | 0.5532 |

- **Robustness.** ε₀ = 0.05, viscosity ×0.5 or ×2, and an outer boundary twice as far each move a threshold by ≤ 0.0005. The constraint error converges at second order (3.0e-3 → 7.5e-4 →
  2.1e-4).
- **δ_c(w)** for q = 0.5 / 1 / 3 (Harada–Yoo–Kohri 2013 in the last column):

  | w | q = 0.5 | q = 1 | q = 3 | HYK |
  |---|---|---|---|---|
  | 0.2 | 0.388 | 0.418 | 0.476 | 0.381 |
  | 0.1 | 0.275 | 0.299 | 0.351 | 0.298 |
  | 0.05 | 0.173 | 0.190 | 0.228 | 0.201 |

- **Decaying switch field:** δ_c ≈ 0.052 / 0.067 / 0.082 at Γ/H* = 3e-3 and 0.021 / 0.028 / 0.034 at 3e-4.

**What is only a reading.**
- In the decaying-field era the q = 0.5 and q = 1 numbers are dispersal boundaries. These profiles form a dust-like central singularity before a horizon, and the code cannot follow past it.
- The single-fluid w(t) is an approximation.
- Near-critical shocks carry a constraint error up to 0.13.

**What is open.** Excision past the singularity, anisotropy, type-II profiles, and a two-fluid treatment.

**Which experiment tests it.** None directly. It enters every f_PBH prediction (HSC, Roman, COSI) and the β/H the hum must show.

---

## WP2 — the gauge dispute, decided for our case (gate PASSED)

Long form: `wp2/RESULTS.md`.

**Gate**, one published number from each side, reproduced independently:

| side | published | ours |
|---|---|---|
| Gauge objection (2503.01962 v2, Eqs. 25 and 79) | δ^F ≃ 10 δ^C, δ^N ≃ 4 δ^C, \|ℛ\| ≃ (9/4) δ^C at k = aH in radiation | 10, 4, 9/4 from exact linear radiation-era theory with Φ′ = 0; 9.80 with the exact mode function |
| Rescue (2605.11332 v3) | M_min ~ 1e20 g at T_V = 1e6 GeV | Hubble mass at H*: 0.93e20 g |
| | f_min coefficient 2 | 2.20, only with the reduced Planck mass |
| | T_reh = 0.64 (Γ/H*)^{1/2} T_V | 0.640, from our two-fluid background at ρ_r = ρ_φ |

**What holds.**
- **Radiation era: the gauge objection holds, and our own patch model makes it stronger.** We built a spherical percolation model of a Hubble patch kept in the false vacuum (exact de
  Sitter light cones, exponential nucleation), took its δN profile to the comoving compaction, and evolved it with the WP1 code.

  | β/H | 4 | 6 | 8 | 10 | 12 and 14 |
  |---|---|---|---|---|---|
  | ln P, flat criterion δ_F(0) ≥ 0.5 | −0.6 | −2.7 | −9.1 | −26 | −65, −148 |
  | ln P, full GR evolution of the same patch | −158 | −1262 | −7515 | −36950 | no collapse before the type-II edge |
  | δ_F(0) needed | 22 | 14 | 11 | 10 | — |

  The flat-slicing contrast needed to collapse is 10–22, not 0.5. Typical comoving fluctuations (published σ fits) would have to be 20–90σ events.
- **The radius convention does not change the radiation verdict.** With the patch fixed at the Hubble radius of the transition instead, only β/H = 4 collapses at all (ln P = −201); for
  β/H ≥ 6 nothing collapses before the type-II edge (ln P < −1206).
- **Early matter era (Γ/H* = 3e-3, 3e-4): the rescue works.** The WP1 thresholds drop to 0.02–0.08.
  - Typical fluctuations with σ ≈ 0.002–0.02 then give ln β_k ≈ −20 to −140, depending on β/H and Γ/H*; f = 1 needs ln β ≈ −32.
  - The delayed-patch model gives larger probabilities: ln P = −1.2 … −19 for β/H = 6–14 at Γ/H* = 3e-3, and −0.5 … −3.1 for β/H = 8–14 at 3e-4. It is spherical and uses mean
    profiles, so it is an upper estimate.

**What is only a reading.**
- The size of the matter-era probability: the two estimators differ by tens in ln P, and the patch model is spherical.
- The patch is horizon-sized at formation.
- de Sitter geometry is kept during the delay.

**What is open.**
- The non-Gaussian tail in the matter era.
- Anisotropic collapse beyond the Harada σ⁵ cap.
- Type-II patches at β/H ≥ 12.

**Which experiment tests it.** Indirectly, through f_PBH and the hum's β/H. Directly, only by simulations: lattice nucleation runs with comoving-gauge output.

---

## WP3 — abundance, mass function and current limits (gate PASSED)

Long form: `wp3/RESULTS.md`.

**What holds.**
- **Window.** The window allowed by current limits is 2.0e17–9.8e21 g. Limits: 511 keV (Laha 1906.09994; De la Torre Luque et al. 2406.11949), COMPTEL (2010.04797), INTEGRAL MeV (2004.00627),
  Voyager (1807.03075; 2406.11949), HSC (1701.02151 / 1910.01285 / 2007.12697), OGLE (1901.07120; 2403.02386, inactive below 1e23 g).
- **β/H for f = 1 (no accretion):**

  | M [g] | Γ/H* = 3e-3 | Γ/H* = 3e-4 |
  |---|---|---|
  | 1e18 | 9.71 | 14.79 |
  | 1e19 | 9.61 | 14.68 |
  | 1e20 | 9.50 | 14.57 |
  | 1e21 | 9.38 | 13.56 |

- **Radiation, gauge-corrected:** f ≈ 1e-22 at β/H = 4 (1e19 g).

**What is only a reading.**
- The q, σ and anisotropy choices move the needed β/H by ±1.5.
- The mass function is monochromatic.
- Maximal accretion (Ai & Xie Eq. 18) needs T_V up to 8e8 GeV and β/H about 0.7–1 higher.

**What is open.**
- COSI is figure-only (text: "strongly challenge PBH DM in the 10^16–10^17 g" range). A text-based proxy is drawn.
- No Roman forecast exists inside 1e20–1e25 g.

**Which experiment tests it.** COSI and MeV telescopes at the lower edge, HSC-type microlensing at the upper edge. Nothing listed probes 1e18–1e21 g.

---

## WP4 — the hum (gate PASSED)

Long form: `wp4/RESULTS.md`.

**Gate.** The brief's envelope-against-LVK ratios are reproduced:

| M [g] | 1e15 | 1e16 | 3e16 | 1e17 | 1e18 | 1e19 |
|---|---|---|---|---|---|---|
| brief | 0.27 | 0.60 | 1.03 | 1.87 | 5.9 | 18 |
| ours | 0.27 | 0.59 | 1.02 | 1.85 | 5.8 | 18.1 |

Worst deviation 1.8%.

**What holds.**
- **Matter-era factors** from the two-fluid background: frequency F = 0.979 (Γ/H*)^{1/6}, amplitude D = F⁴ = 0.920 (Γ/H*)^{2/3}.
- **Templates.** The primary is Lewicki & Vaskonen 2208.11697 Table I, "Bubbles, T_rr ∝ R⁻³" (gauge symmetry breaking). The envelope is the cross-check.
- **The hum.**
  - Peaks at 0.006–2.4 Hz, Ω h² = 1.5e-11 (Γ/H* = 3e-4) to 1.9e-10 (3e-3).
  - DECIGO and BBO: SNR 3e3–2e7 everywhere. LISA: M ≳ 1e20 g. ET and CE: M ≲ 1e18–1e19 g with LV22.
  - LVK O3: no constraint (UL/pred ≥ 160).
- **PLS minima (ρ = 10):** LISA 1e-13, DECIGO 7e-16, BBO 9e-17, ET 5e-13, CE 4e-13.

**What is only a reading.**
- The template choice: the envelope is 1.5× louder at 1.9× the frequency and falls as f⁻¹, not f^−2.4.
- CE is modelled as an optimistic co-located pair; ET comes from an analytic Ω-fit with a factor-2 caveat.
- The brief's "ET hears every case" holds only for the envelope.

**What is open.** The matter-era IR tail, a real CE network, and whether the U(1)_X walls run away.

**Which experiment tests it.** DECIGO and BBO decisively; LISA at the heavy end; ET and CE at the light end.

---

## WP5 — cross-check table and inversion

Long form: `wp5/RESULTS.md`.

The table covers f_PBH = 1 with no accretion. The hum uses LV22, envelope in brackets. ε is the value needed for Ω_DM/Ω_b = 5.36, with m_X = T_V.

| M [g] | T_V [GeV] | β/H | Γ/H* | T_reh [GeV] | hum f [Hz] | Ω h² | heard by (SNR ≥ 10) | ε |
|---|---|---|---|---|---|---|---|---|
| 1e17 † | 3.1e7 | 9.82 | 3e-3 | 1.1e6 | 2.3 [4.2] | 1.7e-10 [2.6e-10] | DECIGO, BBO, ET, CE | 4.7e-9 |
| 1e18 | 9.7e6 | 9.71 | 3e-3 | 3.4e5 | 0.72 [1.3] | 1.7e-10 | DECIGO, BBO, ET, CE | 4.7e-9 |
| 1e19 | 3.1e6 | 9.61 | 3e-3 | 1.1e5 | 0.22 [0.41] | 1.7e-10 | DECIGO, BBO, ET [+CE] | 4.7e-9 |
| 1e20 | 9.7e5 | 9.50 | 3e-3 | 3.4e4 | 0.070 [0.13] | 1.8e-10 | LISA, DECIGO, BBO [+ET, CE] | 4.7e-9 |
| 1e21 | 3.1e5 | 9.38 | 3e-3 | 1.1e4 | 0.022 [0.040] | 1.8e-10 | LISA, DECIGO, BBO [+ET, CE] | 4.7e-9 |
| 1e22 † | 9.7e4 | 9.26 | 3e-3 | 3.4e3 | 0.0068 [0.013] | 1.9e-10 | LISA, DECIGO, BBO [+ET] | 4.7e-9 |
| 1e17 † | 3.1e7 | 14.90 | 3e-4 | 3.4e5 | 2.4 [4.4] | 1.5e-11 [2.4e-11] | DECIGO, BBO, ET, CE | 1.5e-8 |
| 1e18 | 9.7e6 | 14.79 | 3e-4 | 1.1e5 | 0.74 [1.4] | 1.6e-11 | DECIGO, BBO, ET [+CE] | 1.5e-8 |
| 1e19 | 3.1e6 | 14.68 | 3e-4 | 3.4e4 | 0.23 [0.43] | 1.6e-11 | DECIGO, BBO [+ET, CE] | 1.5e-8 |
| 1e20 | 9.7e5 | 14.57 | 3e-4 | 1.1e4 | 0.073 [0.14] | 1.6e-11 | LISA, DECIGO, BBO | 1.5e-8 |
| 1e21 | 3.1e5 | 13.56 | 3e-4 | 3.4e3 | 0.022 [0.040] | 1.9e-11 | LISA, DECIGO, BBO | 1.5e-8 |
| 1e22 † | 9.7e4 | 12.21 | 3e-4 | 1.1e3 | 0.0061 [0.011] | 2.3e-11 | LISA, DECIGO, BBO | 1.5e-8 |

† Excluded today by current limits.

**Inversion.** Measured M → T_V; measured (f, Ω) → β/H and Γ/H* (unique); then predict f_PBH.
- **Closure:** f = 1.000 in all rows.
- **Model systematics** (envelope template, threshold shape q = 0.5–3, σ fit, 10% measurement errors) move the prediction by up to about 10 orders of magnitude.
- **Required precision:** a factor-10 test needs β/H to 1.5–2.6%. In the heavy, slow-decay corner (Γ/H* = 3e-4, M ≳ 1e21 g), where the anisotropy cap sets β_k, it needs about 20%.
- **Answer:** f = 1 is reproduced by construction, but the test is **not yet discriminating**.

---

## Everything that failed or stayed unresolved

### Failed or corrected during the work, kept in the log

1. **WP1 dispersal rule v1** left a dispersed q = 0.5 run "undecided"; rule v2 was added and logged. The v1 results are kept; q = 1 and 3 are unchanged.
2. **WP1 decaying-field runs** stop at a dust-like central singularity before any horizon (q = 0.5, 1). We report dispersal boundaries, not horizon thresholds. The q = 3 constraint error at the end
   of collapse is 0.1–0.2.
3. **WP2 first scans were aborted** and kept: ε₀ = 0.1 was invalid for steep patch edges, and the brackets were wrong. Fixed by adaptive ε₀ (ε₀² max|ẽ| ≤ 0.01) and new brackets.
4. **WP2 near-dust shell crossing.** Strongly perturbed shell-like patches fail in the matter era; the upper brackets were stepped down.
5. **WP2 steep edges.** Edges with q ≈ 200–400 carry a constraint error of 0.1–0.2; the outcome is the same at N1 = 160, 480 and 960.
6. **WP2 type-II edge.** For β/H ≥ 12 in radiation, there is no collapse before the type-II edge; beyond it was not simulated.
7. **WP5 closure.** The first inversion closure was off (f = 0.08–49) from solver tolerance; fixed to exact.
8. **WP2 fixed-radius matter era, Γ/H* = 3e-4, β/H = 8 and 10: stopped unfinished.** Both jobs were still in long near-dust runs (up to 1e5 t_H) after more than 30 minutes and were stopped. Their
   cells stay "unresolved" and are not interpolated. The neighbouring cells (−0.07 at β/H = 6, −0.83 at 12) carry the trend. `results_scan_fixed_emd.json` was rebuilt from the run log.

### Brief statements that did not survive

9. **The matter-era frequency factor (Γ/H*)^{1/6}/0.64 is 1.6× too high.** The exact value is 0.979 (Γ/H*)^{1/6}. The amplitude (Γ/H*)^{2/3} is right to 8%.
10. **"ET hears every case"** holds only for the envelope template.
11. **The mass range 1e17–1e22 g:** 1e17 g is now excluded (2024 evaporation updates) and 1e22 g sits at the HSC edge. The T_V range 1e5–3e7 GeV maps to 1e22–1e17 g, so only T_V ≈ 1e5–2e7 GeV
    is allowed.
12. **The Ai–Xie formulas** in the brief match only v3 of 2605.11332 (v1 and v2 differ). The brief's M and f are the no-accretion lower bounds (their Eq. 17); maximal accretion (Eq. 18) changes
    both.

### Unresolved

13. **The early-matter-era collapse probability.** The typical-fluctuation estimator and the delayed-patch model differ by tens in ln β. Non-Gaussian tails and anisotropy beyond the σ⁵ cap are not
    computed.
14. **The forecasts.** COSI is figure-only (2210.09310), so only a text-based proxy is drawn. No Roman forecast exists inside 1e20–1e25 g, and the source of the "Roman M31" curve in the Snowmass
    white paper is unresolved.
15. **Detector models.** No analytic CE fit exists; the CE data file was used with an optimistic co-located pair. The ET-D Ω-fit carries a factor-2 normalisation caveat. The matter-era IR tail of
    the hum is not modelled.
16. **Template choice.** Envelope or LV22 bubbles or fluid depends on whether U(1)_X walls run away (Boedeker & Moore 2017, 1703.08215, from memory).
17. **The pass-or-fail test** cannot discriminate until β/H, σ(β/H) and the hum template are known to about 2%.
18. **The ε relation** uses m_X = T_V (the brief's assumption); it is not derived.
19. **Source ledger.** The id 1604.05349, from the main session's own memory, was wrong; the correct paper is 1609.01588. The helper also flagged two inconsistencies inside 2305.04942: Eqs. 11 and
    48 use different denominators, and its "1% of DM" sentence disagrees with its Eqs. 16 and 60 by 33–45×, which we confirmed.
