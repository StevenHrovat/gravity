# Pre-registration: how much physical content does the block field carry? (c5b-content, 2026-11-22)

Status: **written before any physics data.** Only the instrument was tested before this was written (`selftest`, `cpu-test/selftest.log`;
a 9-configuration pipeline test `cpu-test/pipe_test.json`, which is not physics: far too few samples, no number from it is used).
Part A (CPU lower bounds) is run after this file is fixed. Part B (GPU, conditional replicas) is **written, not run**.
Claim levels as in `../../attempts/RULES.md`. Roles, not values: no host, account or address appears in this folder.

## 1. The quantity

Fine field U (SU(2) Wilson measure on a periodic 4D lattice, direction 0 is time). Block field Phi_b: the good blocking of
`../c3b-refit/goodblock.py` (spatial staple smearing with weight w = 2, temporal decimation, projection to SU(2), iterated), block size
b = 2, 4, 8 fine spacings. For a local fine observable F:

    R2(F; b) = Var( E[F | Phi_b] ) / Var(F)  =  1 - E Var(F | Phi_b) / Var(F)        (0 <= R2 <= 1)

the **explained variance**. Observables F (0++, gauge invariant, cell-centre placement: the window sits at the centre of a block cell):
* **P_s**, s = 1, 2, 4: the plaquette scalar (sum over the 6 planes of (1/2) tr of the plaquette), averaged over the hypercube of
  side s fine spacings. Physical size relative to the 0++ glueball (m = 3.75 sqrt(sigma), the value the notes use, so 1/m = 0.267/sqrt(sigma)):
  at beta = 2.3 (a sqrt(sigma) = 0.35) s = 1, 2, 4 are 1.3, 2.6, 5.2 of 1/m; at beta = 2.5 (0.1825) 0.7, 1.4, 2.7 of 1/m.
* **W_2**: the 1x2 and 2x1 rectangle scalar, window s = 2.
* **Primary target: P_2** (side about 1.4 to 2.6 of 1/m). The others are reported, not used for the verdicts.

Block levels b = 2, 4, 8 at beta = 2.3 (L sqrt(sigma) = 0.70, 1.40, 2.80) and beta = 2.5 (0.37, 0.73, 1.46); the review's working
point L1 sqrt(sigma) = 2.8 is (beta 2.3, b = 8).

### Exact relations (so the number can be tied to Lemma X). All are one-line consequences of the tower property.
Write h_F = E[F|Phi], sigma_F^2 = Var F, rho(F,G) the correlation, rho_c(F,G) = E Cov(F,G|Phi) / (sigma_F sigma_G) (the quantity of part (c)),
rho_Phi = corr(h_F, h_G), R_F^2 = R2(F;b).
* (E1) `Var F = Var h_F + E Var(F|Phi)` (Pythagoras).
* (E2) `Cov(F,G) = E Cov(F,G|Phi) + Cov(h_F, h_G)` (this is `condDefect_eq`, `UV/Split.lean`), hence
  **rho_c = rho - R_F R_G rho_Phi**.
* (E3) The information bound in its L2 form (Cauchy-Schwarz on E2): **|rho_c - rho| <= R_F R_G** and **|rho_c| <= sqrt((1-R_F^2)(1-R_G^2))**.
  (The project's L1 bound `|(c) - Cov| <= ||E[F|Phi] - EF||_1` follows the same way; the L2 form is written here because R2 is an L2 number.
  Derived in this note, not in Lean.)
* (E4) Regression residuals r_F = F - h(Phi) for ANY function h of Phi: `Cov(r_F, r_G) = (c) + Cov(h_F - h, h_G - h')`. The residual
  covariance is the conditional covariance up to the regression's own deficiency (used only as an exploratory proxy, section 3).

### What the number can and cannot decide (written before data, because it limits the verdicts)
(E3) pins the conditional correlation to the unconditional one only up to R2 (a constant), while the correlators the route needs, at
separations D >= L1, are exponentially small (about e^{-m L1} = 3e-5 at L1 sqrt(sigma) = 2.8). So:
* **R2 small does NOT by itself prove "Lemma X is the gap" at D >= L1**: (E3) is silent below R2. It proves it for the separations where
  rho(D) >= 10 R2, i.e. up to D_10 = ln(1/(10 R2))/m (for R2 = 0.02: about 1.4/m = 0.37/sqrt(sigma)).
* **R2 large does not prove decay**, only that conditioning removes at least R2 of the variance and that |rho_c| <= 1 - R2.
* What decides Lemma X at large D is the **capture fraction** of the long-distance covariance, `chi(D) = Cov(h_F,h_G)/Cov(F,G) = 1 - rho_c/rho`
  (by E2), equivalently `R_c(D) = rho_c(D)/rho(D) = 1 - chi(D)`, the "conditional-to-unconditional ratio" of c4c. If R_c(D) -> 1 for D beyond the
  correlation length, Lemma X is the gap; if R_c(D) -> small, the conditioned fine field decorrelates by the constraint mechanism and Lemma X
  is not the gap. R2 is the cheap gauge of content; R_c is the decisive number. The CPU part measures R2 (rigorously, from below) and gives
  R_c only as an exploratory proxy where it is resolved; the GPU part measures both.

## 2. Thresholds (fixed now)

### 2.1 Reading of R2 for the primary target P_2 (applies to a lower bound or an estimate; the table says which verdicts each supports)

| class | R2 | reading |
|---|---|---|
| CONTENT-RICH | >= 0.50 | the block field fixes at least half of the variance of a glueball-scale local observable; by E3 |rho_c| <= 0.5 at every separation. Consistent with "Lemma X is not the gap" at that b; still needs R_c at large D. |
| CONTENT-PARTIAL | 0.10 to 0.50 | real but incomplete content; the verdict rests on R_c |
| CONTENT-SMALL | 0.02 to 0.10 | little content; E3 bracket is +-R2: (c) equals Cov within 10 percent only where rho >= 10 R2 |
| NEAR-NOISE | < 0.02 (estimate with its 2-sigma upper end below 0.02; GPU only) | (c) equals Cov to within 0.02 sigma^2 at every separation: Lemma X is the gap where the correlator is resolved above 0.2 |

**A regression lower bound can support CONTENT-RICH / PARTIAL / SMALL only. A small lower bound is INCONCLUSIVE** (the regression may be
weak, the model class too small); it never supports NEAR-NOISE. Only the GPU measurement (an estimate, with an independent upper-side
check, section 5) can support NEAR-NOISE.

### 2.2 CPU verdicts (part A)
Per (theory, beta, b, w), primary target P_2, test-phase value LB = max(0, 1 - MSE_test/Var F), jackknife error err:
* **LB >= 0.50** CONTENT-RICH (rigorous lower bound, up to the statistical error). **0.10 <= LB < 0.50** CONTENT-PARTIAL. **0.02 <= LB < 0.10**
  CONTENT-SMALL. **LB < 0.02, or LB - 2 err < 0.02 for the class below**: reported as the lower class, INCONCLUSIVE about the true R2.
* A class is claimed only if LB - 2 err is inside it.
* **The central CPU question** (review 2.2): is LB(P_2; beta = 2.3, b = 8, w = 2) >= 0.10? YES means the block field at L1 sqrt(sigma) = 2.8
  carries measurable content (so "near noise" is wrong as stated), but note the lattice caveat for b = 8 below. NO is inconclusive.
* **Decimation control** (same configurations, w = 0): the w = 2 blocking must beat w = 0 at b = 4 and 8: LB(w=2) - LB(w=0) > 2 err_combined
  for P_2 in the SU(2) runs, or the comparison is reported as "not resolved". (c3a's Gaussian computation says decimation loses content with b.)
* **Photon control** (U(1), beta = 1.1): the same pipeline. Expected (not a criterion): the photon's LB is larger than SU(2)'s at the same
  b and falls more slowly with b (long-wavelength content survives blocking). It is reported with the SU(2) numbers; **the control is
  passed if LB_U1(P_2, b=4) > LB_SU2(P_2, b=4) at beta 2.3 by more than 2 err_combined**, otherwise reported as failed and the interpretation of
  the SU(2) numbers is flagged (the instrument cannot see long-wavelength content that must be there). The two theories have different
  lattice scales, so the comparison is "same b in fine spacings", not "same physical size"; stated limitation.
* **Instrument gates** (must hold or the run is void): selftest passed in this folder; the validation-phase and test-phase values of the
  chosen model agree: |R2_val - R2_test| < 0.03 + 3 err for P_2 at b = 2 (the best-resolved
  point); plaquette mean drift between the first and last third of the collection phase < 3 sigma.

### 2.3 Exploratory (not a verdict): the residual-covariance proxy S(D) for the capture fraction
`S(D) = Cov(r_0, r_D) / Cov(F_0, F_D)` with r = F - h_hat(Phi) (the regression residual), F_0, F_D the target at cells separated by D = j b in
time (j = 1, 2) at the same origin, estimated on the held-out configurations, jackknife over configurations. By E4, S(D) = R_c(D) + (regression
deficiency term); **it is not a bound in either direction.** Read: S(D) near 1 (within errors) means the regression-explained part carries none
of the covariance at D; S(D) well below 1 means it does. Reported only where `Cov(F_0,F_D) > 3 sigma_Cov`.

## 3. Part A: the CPU lower bound (the instrument is `content.py`)

**Method.** Lower bound by held-out regression. For any function h of Phi fixed on other data, Var(E[F|Phi]) >= Var F - E(F-h(Phi))^2 (E[F|Phi] is
the L2-best predictor). The code uses the same Markov chain in three phases: training, validation (model class and ridge strength chosen),
and a **held-out test phase after 20 decorrelating sweeps**, on which R2_LB = 1 - MSE_test/Var F is computed; the MSE includes any bias.
Features: gauge-invariant loops of the block lattice (traces of 1x1 plaquettes, adjoint traces, 1x2/2x1 rectangles with fundamental and adjoint
traces) in the neighbourhood of the cell, **summed over orbits** of the loop position relative to the cell centre (|d_t|, spatial radius^2, loop
class: 108 orbit features). Model classes: (A) ridge on the orbit features; (B) A plus all products of the 14 features most correlated with the target
(linear or even); (C) A plus 600 random tanh features of the 40 most correlated ones. Pooling: all (origin, cell) pairs of the block lattice (by
translation covariance every pair has the same joint law as (F, Phi) of origin 0; checked by the alignment selftest). R2 is clamped at 0 from below
(the constant predictor is a function of Phi); the raw value is also stored.

**Runs** (CPU, one process at a time, `CUDA_VISIBLE_DEVICES=-1`, each at most 30 minutes, outputs in `runs-cpu/`):

| run | theory | beta | lattice | seed | train / val / test configs | every | notes |
|---|---|---|---|---|---|---|---|
| C1 | SU(2) | 2.3 | 16^4 | 2301 | 110 / 40 / 80 | 3 sweeps (1 heat bath + 1 overrelaxation) | b = 2, 4, 8; w = 2 and w = 0 |
| C2 | SU(2) | 2.5 | 16^4 | 2501 | 110 / 40 / 80 | 3 | same |
| C3 | U(1) | 1.1 | 16^4 | 1101 | 110 / 40 / 80 | 3 | photon control; same blocks and w |

M = 1500 random cells per configuration and (w, b) for training and validation; the test phase uses **all** cells. Thermalisation 80 sweeps from a
cold start (plaquette printed every 20). beta = 2.4 is not run (budget); the review's range 2.3 to 2.5 is covered at its ends.
**What the lattice limits.** 16^4 is 5.6/sqrt(sigma) per side at beta 2.3 and 2.9/sqrt(sigma) at beta 2.5; with 2 chains of a few hundred sweeps. For b = 2
and 4 the block lattices have 8^4 and 4^4 cells and the features are local; **for b = 8 the block lattice is 2^4**: the neighbourhood wraps around
(a feature at offset 2 is a feature at offset 0), so b = 8 is a weak and not a clean test: a lower bound still, but the features cannot see
beyond one cell. Finite-size effects at 2.5 (box 2.9/sqrt(sigma), about 1.9 times 1/T_c) are not controlled. The window pooling over origins uses
only even origins of the fine lattice. Only the cell-centre placement and 0++ plaquette and rectangle scalars are covered; glueball operators
built from smeared links (APE) are not. The regression class is limited (orbit sums lose the orientation of a loop relative to its displacement;
products are found by marginal screening only); a better model gives a larger bound, never a smaller true value.

**Optional follow-up C4** (only if C1 shows b = 8 resolved or unresolved in a way that a clean test would change): SU(2) beta 2.3, 24^4, blocks 4 and 8
only (`CM_BLOCKS=4,8`), about 40 test configurations; the stock updater costs about 8 s per sweep at 24^4, so the statistics are small.

## 4. Part B: the GPU measurement (written, NOT run; reuses `../c4c-seg2/PREREG.md`)

### 4.1 Instrument
The conditional-replica instrument of c4c: soft blocking `P(U,Y) = mu_W(U) prod_l p_kappa(Y_l; Phi_l(U))`, `p_kappa(Y;V) ~ exp(kappa (1/2) Re tr(Y^dag V))` (Haar in
Y). Y is a randomised function of Phi (U -> Phi -> Y), so **R2(F; Y_kappa) <= R2(F; Phi) for every kappa**: soft replicas bound the hard value from below, and
the kappa trend is evidence for the limit. Procedure per sample: draw an equilibrium U0; set Y = Phi(U0) eta (eta from the kappa-law); then **U0 is an exact draw
from the conditional law given Y** (replica a, no thermalisation bias). Replica b: **start from replica a** and run the Metropolis-corrected HMC of the
conditional action `S_W(U) - kappa sum_l (1/2) Re tr(Y_l^dag Phi_l(U))` (gradient by the adjoint of the smearing and the SU(2) projection, written for the GPU
and tested against finite differences to 1e-8, as in c4c run 0), with full momentum refresh, recording `C_Y(T) = Cov(F(0), F(T))` at even HMC trajectory counts
T = 0, 2, 4, ..., T_max.

### 4.2 Two-sided estimate (a design improvement over c4c, derived here, to be checked on the photon)
Let P_Y be the HMC kernel; it is reversible with respect to the conditional law given Y and (because replica a is an exact conditional draw) stationary.
For even T, `E_Y <f, P_Y^T f>_Y = E_Y ||P_Y^{T/2} f||^2 >= E_Y (E[f|Y])^2`, and the left side is non-increasing in even T and tends to Var(E[F|Y]) if the
conditional chain is ergodic. So **R2_UB(T) = Cov(F(0), F(T)) / Var F (even T, Y-averaged) is a non-increasing sequence that bounds R2(F; Y_kappa) from above,
and converges to it.** Together with the CPU lower bound this is a bracket: `max(CPU LB (hard Phi), R2_a) <= R2(F;Phi) ...` and `R2_LB_soft <= R2(F;Y_kappa) <= R2_UB(T)`.
The estimate is read as the plateau of R2_UB(T): if R2_UB(T) is flat to within errors over T from T_1 to T_max, that is the value; if it still decreases,
the answer is "at most R2_UB(T_max)" only (an upper bound, and the conditional field has slow modes: report that). **This is the upper-side check
that makes the NEAR-NOISE verdict possible.** (Independent-start replica b, as in c4c, is run as a cross-check on the first (beta, b) only.)
The same replicas give the conditional covariance `Gamma(D) = E_Y Cov(F_0, G_D | Y)` at the plateau (G = F shifted by D = j b, j = 1, 2, 3, same Y) and so
`R_c(D) = Gamma(D)/C(D)`, `C(D)` from the unconditioned equilibrium configurations, with the finite-T caveat as above (Gamma at finite T is not a bound).

### 4.3 Runs (priority order; each stops at the first failed gate; fine lattices as c4c's)

| run | theory | beta | lattice | b | L sqrt(sigma) | role |
|---|---|---|---|---|---|---|
| 0 | | | | | | selftest (gradient vs finite differences 1e-8; replica a is an exact conditional draw: Cov(F(0),F(0)) = Var F; photon exact check) and bench |
| 1 | U(1) | 1.1 | 16^3 x 48 | 2, 4, 8 | photon | **photon control** |
| 2 | SU(2) | 2.3 | 16^3 x 48 | 2, 4, 8 | 0.70, 1.40, **2.80** | **main** |
| 3 | SU(2) | 2.3 | 16^3 x 48 | 4, 8 | 1.40, 2.80 | **decimation control** (w = 0, near-noise by construction) |
| 4 | SU(2) | 2.5 | 32^3 x 96 | 8, 16 | 1.46, **2.92** | scaling partner of run 2's b = 8 |
| 5 | U(1) | 1.1 | 16^3 x 48 | 4, 8 | | decimation control for the photon (w = 0) |

kappa in {16, 64} (soft to nearly hard); F = P_2 and P_4 (primary P_2), and W_2. Y-samples per (run, b, kappa): 8 (b = 2), 60 (b = 4), 300 (b = 8, b = 16),
chosen so that the R2 error is about 0.005 (the estimate averages over 12288, 768, 48 cells per Y-sample at b = 2, 4, 8 on 16^3 x 48; 48 cells at b = 16 on 32^3 x 96;
errors by jackknife over Y-samples, to be checked in run 0; Y-samples of b = 16 may be cut to 100 by the budget rule below). Origin 0 only.

### 4.4 Gates and verdicts (fixed now)
* **Photon gate (run 1):** R2_UB(T) must plateau (change < 0.02 between T_max/2 and T_max) and R2 at b = 4 and 8 must exceed the SU(2) lower bounds of part A at
  beta 2.3 (same b) by 2 sigma; **R_c(D = b) <= 0.3** for the photon at b = 4 and 8 (c3a's Gaussian computation: conditional correlation of block-averaged F_12 at D = 3 L1 is
  5e-7 of its variance). If it fails: stop, the instrument is wrong; do not interpret SU(2).
* **Decimation gate (runs 3, 5):** R2(w=0) < R2(w=2) at b = 8 by at least 0.02 (both with their errors), else INCONCLUSIVE for SU(2).
* **SU(2) verdicts (runs 2, 4), per b at kappa = 64 (kappa = 16 must agree within 30 percent of R2 or the trend is reported):**
  * **NOISE** (Lemma X is the gap at this b): R2 + 2 err <= 0.02 **and** R_c(D = b) >= 0.9 (or unresolved with C(D) < 3 sigma, in which case NEAR-NOISE only).
  * **CONTENT** (Lemma X is not the gap at this b): R2 >= 0.50 **and** R_c(D = b) <= 0.3, or R_c(D) <= 0.3 at the largest resolved D whatever R2 (the pole is captured).
  * **SLOW** (the conditional field has slow modes: R2_UB(T) not plateaued by T_max, or 0.3 < R_c < 0.9): report; a candidate hidden conditional near-transition; the
    Dobrushin route at that b needs more than a gap-free Lemma X.
  * otherwise INCONCLUSIVE.
* **Scaling check (runs 2 and 4):** R2 at (beta 2.3, b = 8, 2.80) against (beta 2.5, b = 16, 2.92): consistent if they agree within 2 sigma plus 30 percent; otherwise
  the point is lattice-spacing dependent and not a continuum statement.

### 4.5 Runtime estimate (assumptions stated; plus or minus a factor 3 until run 0 benches)
Basis: the c3b bench on this GPU, heat-bath sweep of one chain 0.96 s at 48^4 (5.3e6 sites). Assumed: one conditional HMC trajectory (10 leapfrog steps; the force costs about 3 sweep
equivalents with the adjoint of the smearing) at 16^3 x 48 (2.0e5 sites) about 1.0 s per chain, 8 chains in a batch at about 1.5 times that per batch (0.19 s per chain-trajectory);
at 32^3 x 96 (16 times the sites) about 3 s per chain-trajectory. T_max = 80 (T_max = 40 at 32^3 x 96). Hours:

| run | b and Y-samples | kappa values | hours |
|---|---|---|---|
| 1 photon | 8, 60, 300 | 2 | about 1.2 (U(1) is cheaper, about 0.6 of SU(2)) |
| 2 SU(2) 2.3 | 8, 60, 300 | 2 | about 3.2 |
| 3 decimation | 60, 150 | 2 | about 1.1 |
| 4 SU(2) 2.5 | 150, 100 | 2 | about 7 (dominated by b = 16 at 32^3 x 96; 100 Y-samples, T_max = 40) |
| 5 photon w = 0 | 60, 150 | 2 | about 0.7 |
| 0 | selftest, bench, cross-check with independent-start replica b on run 2 b = 4 | | about 0.5 |
| **total** | | | **about 14 h, range 5 to 40 h** |

Budget rule: after run 0's bench, if the projection exceeds 20 h, drop run 4 (the scaling partner) and cut run 2 to kappa = 64 only (about 6 h in total); runs 1 to 3 are the minimum that
decides the question at the working point. The queue stops at the first failed gate.

## 5. What each outcome would decide
* **NOISE at (2.3, b = 8):** review 2.2 is confirmed as a number: Lemma X at L1 sqrt(sigma) = 2.8 is the lattice gap for block observables; strategy (a) (lossy block to L1) is kept only as a proved
  reduction, and the route moves to strategy (b) (lossless cells) or (d) (finite volume) as the blueprint-v4 plan says.
* **CONTENT at (2.3, b = 8):** the constraint mechanism is alive at the working point: Lemma X (`CondMassAnn`) is not the gap there, the gap content sits in `LevelDprimeW`, and the version-3
  route survives with Lemma X as a gap-free but non-perturbative statement (conditional uniqueness).
* **CONTENT at b = 2 or 4 only (NOISE or SLOW at 8):** a crossover scale b_X between 1.4 and 2.8 over sqrt(sigma) where the block field stops carrying the glueball channel; then the choice of
  L_* (blueprint v4: cut at L_*, not at L1) has a measured upper limit: L_* must be below b_X, and Lemma X is gap-free only up to b_X.
* **SLOW anywhere:** there is a hidden conditional near-transition at that b; strategy (a) at that b needs a conditional Dobrushin-Shlosman statement (c4c's follow-on) not a decay estimate.
* The CPU part alone can only move the first two cases in the direction of CONTENT; it cannot establish NOISE.

## 6. Files
`PREREG.md` (this file), `content.py` (instrument: selftest, run), `run_cpu.sh` (the three runs, one after the other), `NOTE.md` (results and claims), `cpu-test/` (selftest log, pipeline test),
`runs-cpu/` (JSON and logs of C1 to C3).
