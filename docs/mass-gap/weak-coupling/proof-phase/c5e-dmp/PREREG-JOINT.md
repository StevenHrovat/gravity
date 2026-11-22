# Pre-registration: the two act numbers z₀(L) and z_e(L) on the same periodic boxes (c5e-dmp, 2026-11-22; written, not run)

Status: **written, not run.** No GPU was used. The measurement code is the existing `lattice/run_su2_gpu.py`, unchanged; the analysis
is to be written before any run, from the rules below, and tested on the existing files of Stage 0 only after this text is fixed.
Section "Photon control: proposal" is a proposal that changes a pre-registration and **needs the owner's decision**; nothing in the
main plan depends on it.

## Question

Blueprint v4 section 6 states the infrared statement as a doubling law for the vacuum act number z₀(L) = L·E₀(L) above thresholds
of z₀ and of the flux act number z_e(L) = L·E_e(L) (Lean: `ProofPhase.DMP.DS`, `DT`, `su2_box_gap_of_DS_DT`). Measured here, on
periodic boxes L³ × T, for pure SU(2) at β = 2.3, 2.4, 2.5:
1. z₀(L) and z_e(L) at L√σ from 1.03 to 4.20, on the **same configurations**;
2. the doubling ratio g₀ = z₀(2L)/z₀(L) for 9 pairs (L, 2L) at fixed β, and the loss η = 1 − g₀/2;
3. which state is the lowest centre-even zero-momentum state: a pair of flux tubes (z₀ ≈ 2z_e) or a glueball, and where the switch is.

What it can show: the numerical shape of D-T on the measured stretch, the location of a usable start (ζ₀, ζe) for D-S, and whether the
"sector transfer" holds literally below the switch. What it cannot show: anything rigorous; anything beyond L√σ ≈ 4.4; the continuum
limit (three spacings, scaling check only). The qualitative picture (glueball mass constant at large L, torelon-pair states in small
boxes) is known physics (recalled); new are the act-number form, the per-doubling loss and the joint reading.

## Instrument

* **Runs**: `lattice/run_su2_gpu.py BETA L T N_THERM N_MEAS SEED OUT.npz 3 2 CHAINS 2,6,12,20` (cold start, Kennedy–Pendleton heat
  bath + 3 overrelaxation steps, measurement every 2 sweeps, APE smearing α = 0.5 at levels 2, 6, 12, 20). It records per time slice the
  zero-momentum sums of the spatial 1×1 and 2×2 Wilson loops over the three planes (A1⁺⁺, centre-even) and the summed spatial Polyakov
  loops (torelons, centre-odd), at every smearing level. Unchanged code; its GPU self-test (agreement with `su2.py` to 1e-10) is run
  first in the queue.
* **Flux-pair operator** (analysis only, no new measurement): O_pp(t) = (Σ torelon)(t)², centre-even, zero momentum, at each smearing
  level. It is the projection of a pair of flux tubes winding in opposite senses (two Z₂ units = none) onto the A1⁺⁺ channel.
* **z₀**: variational analysis (`lattice/analyse.py`: `correlator_matrix` (vacuum subtracted), `best_projection` with t₀ = 0, t₁ = 1)
  over the basis {1×1, 2×2 at 4 levels} ∪ {O_pp at 4 levels} (16 operators; operators with relative noise above 50 % at t = 0 dropped by
  a fixed rule: diagonal C(0) error > 0.5·C(0)); **cosh effective mass** m(t) from c(t−1)/c(t), c(t+1) solved for E with the period T
  (as `analyse.cosh_mass`); plateau rule of `analyse_plateau.plateau` (smallest t ≥ 1 with m(t) agreeing with m(t+1), m(t+2) within
  combined errors and relative error ≤ 25 %); E₀ = m(t*); z₀ = L·E₀.
* **z_e^{per}**: the same on the torelon basis (4 levels); z_e = L·E_e. (The twisted-box z_e of `r4-actnumber` is a different
  object; it is cross-referenced, not used.)
* **Errors**: jackknife over 20 contiguous bins, bins never crossing a chain boundary (10 chains: 2 bins per chain), as in
  `analyse.jackknife`. Systematic: E taken at t* + 1, reported next to every number and every verdict.
* **Centre sectors.** z₀ uses centre-even operators only, whose distribution is the same in every centre sector (the centre flip is a
  symmetry of the measure that maps sectors onto each other); frozen tunnelling between centre sectors cannot bias z₀. z_e counts only
  if the sign of the summed Polyakov loop of each direction flips at least 10 times per chain (the act-number rule); otherwise z_e is
  reported as NOT COUNTED and readings that need it are NOT RESOLVED.
* **Scale**: a√σ = 0.350 (β = 2.3), 0.258 (2.4), 0.1825 (2.5), the values of `r4-actnumber/PREREG.md` (fixed now; the project's own
  torelon values 0.363, 0.273, 0.199 are a systematic of the L axis only, quoted with J2 and J5).

## Runs (`runtime_estimate.py`, rate model from the existing `run_su2_gpu.py` logs: 0.55 µs per site and sweep ±20 %)

| # | β | L | T | L√σ | therm | meas (every 2) | chains | est. min |
|---|---|---|---|---|---|---|---|---|
| 0 | — | — | — | — | — | GPU self-test (`run_su2_gpu.py selftest`) | — | 1 |
| 1–4 | 2.3 | 4, 6, 8, 12 | 32 | 1.40, 2.10, 2.80, 4.20 | 500 | 2000, 2000, 2000, 1500 | 10 | 1, 3, 7, 18 |
| 5–9 | 2.4 | 4, 6, 8, 12, 16 | 32 | 1.03, 1.55, 2.06, 3.10, 4.13 | 500 | 2000, 2000, 2000, 1500, 1000 | 10 | 1, 3, 7, 18, 31 |
| 10–13 | 2.5 | 6, 8, 12, 16 | 32 | 1.09, 1.46, 2.19, 2.92 | 500 | 2000, 2000, 1500, 1000 | 10 | 3, 7, 18, 31 |
| 14 (optional) | 2.5 | 24 | 48 | 4.38 | 500 | 600 | 8 | 83 |

Seeds 900 + 10·(β index) + L, fixed now. Main plan **about 2.5 GPU hours (±50 %)**; the optional run 1.4 h. If the first two runs'
log lines project more than 4 h for the main plan, cut in this order: run 9 (β = 2.4, L = 16: loses the pair 8 → 16), run 13 (2.5, 16:
loses 8 → 16 at β = 2.5), run 4 (2.3, 12). No other change without a written amendment.

**Doubling pairs** (fixed β): 2.3: 4→8 (1.40→2.80), 6→12 (2.10→4.20); 2.4: 4→8 (1.03→2.06), 6→12 (1.55→3.10), 8→16 (2.06→4.13);
2.5: 6→12 (1.09→2.19), 8→16 (1.46→2.92), optional 12→24 (2.19→4.38). Scaling sets (J5): {1.40, 1.46}, {2.06, 2.10, 2.19},
{2.80, 2.92}, {4.13, 4.20, 4.38}.

## Stage 0 (pilot, CPU, before the GPU runs; reported, never counted)

The existing runs `lattice/runs-gpu/luscher_b2.3_L{6,8,10,12,14}.npz` (β = 2.3, T = 16, 10 chains × 2000, same operators) are read
with the analysis above, after this text is fixed: z₀, z_e, the flux-pair overlap. T = 16 is short for the cosh form at small E and
the glueball channel was noisy there (`zeta/PREREG-LUSCHER.md`): the pilot tests the analysis code and the branch reading, nothing
else. Its numbers are labelled "pilot (existing data, T = 16)".

## Readings (counted points only)

**J1, doubling verdict per pair.** With the photon's exact doubling ratio g_γ(L) (free lattice photon, one-photon z₀ =
2L·arsinh(sin(π/L)): g_γ = 1.136, 1.064, 1.037, 1.024 for L = 4, 6, 8, 12; `photon_exact.json`):
* **DOUBLES** if g₀ − 2σ ≥ 1.8 (η ≤ 0.1 at 2σ) with E at t* and at t* + 1;
* **GROWS, NOT DOUBLING** if g₀ − 2σ > g_γ(L) + 0.1 and g₀ + 2σ < 1.8;
* **FROZEN (photon-like)** if |g₀ − g_γ(L)| ≤ 2σ + 0.1;
* **NOT RESOLVED** otherwise, or if either point does not count. "Not robust to the plateau choice" if the verdict differs between t*
  and t* + 1.

**J2, the start.** L_D√σ := the smallest L√σ that begins a DOUBLES pair at two β (within the scaling sets). Reported: L_D√σ and the
D-S candidate (ζ₀, ζe) = (z₀, z_e) there, with errors. If no pair doubles: "NO START ON THE MEASURED STRETCH".

**J3, the branch (sector transfer made literal).** For each counted L: the normalised overlap of the variational ground state with
the flux-pair operators, w_pp = |v_pp|²/|v|² (in the basis normalised by C(0)), and Δ = E₀ − 2E_e. **FLUX-PAIR BRANCH** if w_pp ≥ 0.5
and |Δ| ≤ 2σ_Δ + 0.1·E₀; **GLUEBALL BRANCH** if w_pp < 0.5 and Δ < −2σ_Δ; **MIXED** otherwise. The switch L_s√σ := midpoint of the
last flux-pair and the first glueball point at each β. Reported with the reading "below the switch the vacuum act is built from two
flux acts".

**J4, the loss.** For DOUBLES pairs: η = 1 − g₀/2 with error, and the trend of η with L (reported, no verdict).

**J5, scaling.** Within each scaling set: z₀ agree at 2σ ("SCALING OK") or not ("ARTEFACTS VISIBLE", with the size of the spread).

**J6, the joint picture.** z₀ and z_e against L√σ, all β, with the infinite-volume line z₀ = (m/√σ)·L√σ for m/√σ = 3.6 (the
project's TTL values 3.41–3.64) drawn for orientation.

## Expectations (stated before data, not criteria)

* Small boxes (L√σ ≈ 1.0–1.1): z₀ of order 1–3; J3 FLUX-PAIR or MIXED.
* Crossover pairs (1.03→2.06, 1.09→2.19, 1.40→2.80): g₀ well above 2 (z₀ rises from the small-box value to about m·L ≈ 7–10):
  DOUBLES.
* Large pairs (≥ 2.06 → ≥ 4.13): g₀ ≈ 2 with η ≲ 0.05: DOUBLES, if the statistics at L = 16 allow (the glueball signal is lost by
  t ≈ 4 at β = 2.4; NOT RESOLVED is a likely outcome there).
* Switch L_s√σ ≈ 1.6–2.1 (where 2E_e^{per} ≈ m₀₊₊).
* L_D√σ ≈ 1.0–1.5, i.e. a start near the deconfinement length (heuristic link to round 4's self-dual point).

## Controls

* **Code**: GPU self-test (run 0) must pass; otherwise nothing runs.
* **Analysis**: on Stage 0 data the analysis must reproduce the project's earlier torelon energies at β = 2.3 (L = 6, 8, 10: aE = 0.599, 0.980, 1.223) within
  2σ (from `results/luscher_summary.json`); otherwise the analysis is fixed before any GPU run, and the fix is recorded.
* **Photon (frozen) control**: the exact formula (proposal below). Under the present rules of the act-number line a simulated U(1)
  gate is used; this measurement does not need one, because the photon's z₀ is coupling independent and known exactly.
* **No Z₂ or 2I run** (the existing Z₂/2I code measures twisted flux only). Their unit tests stay on paper (NOTE section 6).

## Limits

Three spacings; the largest box 4.2–4.4/√σ; glueball noise grows with L at fixed statistics; the flux-pair operator is a product of
two zero-momentum sums (all relative momenta), not a projected two-particle operator; finite T = 32 (thermal flux states e^{−E_e T} are
negligible above L√σ ≈ 1.4 and at the per-mille level at L√σ ≈ 1.0, reported). The measurement says nothing about D-T beyond the
measured stretch, which is where it matters for the proof.

---

## Photon control: proposal (changes a pre-registration; owner's decision)

**Situation.** `r4-actnumber/PREREG.md`, last section: the simulated U(1) photon gate failed at L = 8, 10 because cold and hot starts
sit in different long-lived sectors of the Coulomb phase (likely the integer magnetic fluxes through the planes, changed only by rare
monopole currents); the queue is stopped by its rule; no SU(2) act-number data exist.

**Proposal A (recommended).** Replace the simulated gate by the exact theorem:
1. **z_e of the free lattice photon is g²/2 = 2πα at every L, exactly** (`r4-conjw` §2, proved; numerically checked to 1e−14): E_n =
   g² n² L_z/(2 L_x L_y). Set the photon's doubling factor to g_photon := 1 exactly; the growth threshold of `r4-actnumber` R1 becomes
   max(1.5, 1 + 0) = 1.5 (as expected before).
2. **z₀ of the free lattice photon** (for this measurement): one photon at the smallest momentum, sinh²(E/2) = sin²(π/L), z₀ =
   2L·arsinh(sin(π/L)) (5.27, 5.77, 5.98, 6.14, 6.20 at L = 4, 6, 8, 12, 16; → 2π); two photons at zero momentum, twice that (→ 4π).
   Coupling independent. Check against the project's own U(1) data (β = 1.2, 8³ × 16, `lattice/README.md`): formula 0.748 and 1.317
   at the two smallest momenta, measured 0.70(3) and 1.33(9).
3. The simulated U(1) points at L = 4, 6 (already run: z = 0.686(18), 0.540(13)) are kept as a **code check only** (the update and the
   estimator run on an abelian group), with no pass/fail role.
4. What is lost: an end-to-end check that the estimator reports "frozen" on a simulated frozen theory at L ≥ 8. Partly replaced by the
   exact Z₂ validation, which already tests the estimator on a theory with an exactly known answer.

**Proposal B (optional addition, new code).** A sector-aware U(1) control: per configuration, the integer magnetic flux through each
coordinate plane, m_ij = (1/2π) Σ_{plaquettes of one ij-plane} [θ_p] (reduced angles; averaged over the parallel planes and rounded);
report z_e per sector, gate on the sector m = 0 with cold starts, and check the diagnosis (hot chains carry m ≠ 0, cold chains m = 0).
About 1–2 hours of code and tests in `actnumber.py`'s U(1) path; GPU cost as the present gate. It tests the diagnosis; it does not
change what the gate certifies.

**What to decide**: A, A + B, or keep the simulated gate (the queue then stays stopped). This text only drafts the change; it does not
amend `r4-actnumber/PREREG.md`.

## Owner's decision on the photon control (2026-11-22, before any run)

Option **A** adopted (the owner: "Feel free to run the measurement"): the photon control of this measurement is the exact free-photon
formula (z₀ = 2L·arsinh(sin(π/L)), z_e = g²/2, doubling factor of the photon's z_e exactly 1), as in the proposal above; no simulated
U(1) gate. Option B (sector-resolved U(1) control) is not part of this run. Nothing else changes.
