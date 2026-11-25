# c5b-content: how much physical content does the block field carry, as a number (2026-11-22)

Claim levels as in `../../attempts/RULES.md`. `PREREG.md` was fixed before the CPU runs (only instrument tests and a 9-configuration pipeline test came before). No GPU was used; nothing outside this folder was written; nothing committed.

## 0. Result in one paragraph
**Measured (lower bounds only).** Held-out regression finds explained variance for the good blocking at b = 2 and essentially none at b >= 4. Primary target P_2 (plaquette scalar, window 2 fine spacings): SU(2) beta 2.3: b=2 0.061(1), b=4 0.000, b=8 0.000 (w = 0 decimation: 0.021, 0, 0); beta 2.5: 0.038(1), 0.0001(1), 0.000 (decimation 0.018, 0, 0). P_4 at b=2: 0.183(4) at 2.3, 0.123(3) at 2.5. **Every number is a LOWER BOUND by regression (108 local orbit features, 16^4 lattice); a value near 0 is INCONCLUSIVE about the true R2 (PREREG 2.2), not evidence of noise.** The central question (R2 >= 0.10 at beta 2.3, b = 8, L1 sqrt(sigma) = 2.80?) gets NO by the registered rule, i.e. inconclusive. **The photon control FAILED** (U(1) beta 1.1: b=2 0.035, b=4 0.000, b=8 0.000; the registered pass condition LB_U1(b=4) > LB_SU2(b=4) is not met), so this instrument cannot show long-wavelength content that must exist, and the SU(2) zeros at b >= 4 carry no weight. **The sharper finding is conceptual (section 1):** R2 of a plaquette scalar is dominated by short-distance noise and cannot decide Lemma X; the capture fraction R_c(D) can. The GPU pre-registration measures both and adds an upper-side check, so it can establish NEAR-NOISE, which the CPU part cannot.

## 1. What R2 can and cannot decide (derived here, not in Lean; one-line consequences of the tower property)
`rho_c = rho - R_F R_G rho_Phi` (from `condDefect_eq`), so `|rho_c - rho| <= R_F R_G` and `|rho_c| <= sqrt((1-R_F^2)(1-R_G^2))`. The bracket is a constant, while the correlators the route needs (D >= L1) are about e^{-m L1} = 3e-5 at 2.8. A small R2 therefore proves "(c) equals Cov" only up to the separation where rho(D) = 10 R2 (about 0.4/sqrt(sigma) for R2 = 0.02). A large R2 gives only |rho_c| <= 1 - R2. R2 can also be small while Lemma X is gap-free: if F = slow part + short-distance noise and the block field fixes the slow part, R2 equals the slow fraction (a few percent is typical) while the conditional covariance at large D vanishes. The decisive quantity is `R_c(D) = rho_c/rho = 1 - Cov(E[F|Phi],E[G|Phi])/Cov(F,G)`. The photon control failure fits this: the fine plaquette scalar is mostly noise, so even for the photon its R2 on a coarse field is small.

## 2. CPU results (`runs-cpu/*.json`, `*.out`; runs C1 to C3 as registered: 110 training, 40 validation, 80 held-out configurations, every 3 sweeps)
Test-phase lower bound (clamped at 0; error by jackknife over test configurations; ridge on orbit features, class A, won almost everywhere):

| run | b | w | P_1 | P_2 (primary) | P_4 | W_2 |
|---|---|---|---|---|---|---|
| SU(2) 2.3 | 2 | 2 | 0.0026(2) | **0.0613(9)** | 0.183(4) | 0.096(1) |
| | 4 | 2 | 0 | **0.0000** | 0.0045(4) | 0.0002 |
| | 8 | 2 | 0 | **0.0000** | 0 | 0 |
| | 2 | 0 | 0.0003 | 0.0213(6) | 0.065(2) | 0.039(1) |
| | 4, 8 | 0 | 0 | 0 | 0 | 0 |
| SU(2) 2.5 | 2 | 2 | 0.0010(1) | **0.0379(7)** | 0.123(3) | 0.065(1) |
| | 4 | 2 | 0 | **0.0001(1)** | 0.0058(6) | 0.0005 |
| | 8 | 2 | 0 | 0 | 0 | 0 |
| | 2 | 0 | 0.0001 | 0.0177(5) | 0.058(2) | 0.035(1) |
| U(1) 1.1 | 2 | 2 | 0.0006 | 0.0348(7) | 0.112(3) | 0.054(1) |
| | 4 | 2 | 0 | 0.0000 | 0.0031(3) | 0.0001 |
| | 8 | 2 | 0 | 0 | 0 | 0 |
| | 2 | 0 | 0 | 0.0212(5) | 0.075(2) | 0.036(1) |

Registered readings: P_2 at b=2 is CONTENT-SMALL at beta 2.3 (0.061) and 2.5 (0.038); b=4 and 8 are INCONCLUSIVE. Decimation control: w = 2 beats w = 0 at b = 2 (all targets, many sigma); not resolved at b >= 4 (both 0). Photon control: failed. Instrument gates: selftest passed (cell-to-block alignment exact to 1e-15, planted R2 = 0.30 recovered as 0.295, null target -0.0015); validation and test values agree (P_2 b=2: 0.061 and 0.061); plaquette means stable (0.6029 after thermalisation, 0.6019 over collection at 2.3). The exploratory residual proxy S(D) is unresolved everywhere (covariance at D = b below 1 sigma): no statement. Larger windows carry more (P_4 at b=2 is 0.18).

**Limits.** 16^4 lattice (5.6/sqrt(sigma) at 2.3, 2.9 at 2.5; finite-size effects at 2.5 uncontrolled); b = 8 has a 2^4 block lattice and features wrap (not a clean test); only cell-centre 0++ plaquette and rectangle scalars, no smeared glueball operators; the regression class is small (orbit sums lose loop orientation, interactions are found only by marginal screening), so the bounds can sit far below the truth. beta 2.4 and the optional 24^4 run C4 were not run.

## 3. The GPU pre-registration (`PREREG.md` section 4; written, not run)
c4c's soft-blocking conditional replicas with two changes. (i) Replica b starts from replica a (an exact conditional draw) and is evolved by Metropolis-corrected HMC of the conditional action; for even trajectory counts T, the Y-averaged `Cov(F(0),F(T))/Var F` is non-increasing in T and bounds R2(F;Y_kappa) from above (reversibility argument, derived in the file, to be checked on the photon in run 0), converging to it; with the CPU lower bound this is a bracket, and a plateau is the estimate. (ii) Y is a randomised function of Phi, so the soft R2 bounds the hard R2 from below for every kappa. The same replicas give R_c(D). Runs: photon control, SU(2) beta 2.3 b = 2, 4, 8 (L sqrt(sigma) = 0.70, 1.40, **2.80**), decimation controls, scaling partner beta 2.5 b = 16 (2.92); kappa in {16, 64}. Verdicts fixed in advance: NOISE (R2 + 2 err <= 0.02 and R_c >= 0.9), CONTENT (R2 >= 0.5 and R_c <= 0.3, or R_c <= 0.3 at the largest resolved D), SLOW, INCONCLUSIVE; gates: photon, decimation. Runtime about 14 h (range 5 to 40 h) under stated assumptions (1 s per conditional HMC trajectory at 16^3 x 48, 3 s at 32^3 x 96); a budget rule drops the 32^3 x 96 partner above 20 h.

## 4. What it would decide
NOISE at (2.3, b=8): review 2.2 becomes a number; strategy (a) stays a reduction only; the route goes to lossless cells (b) or finite volume (d). CONTENT: the constraint mechanism is alive at 2.8; the v3 route survives with Lemma X gap-free but non-perturbative. CONTENT at small b only: a crossover scale b_X, an upper limit for L_*. SLOW: a hidden conditional near-transition. The CPU part has decided nothing about the working point.

## 5. Next step
Make the control meaningful before spending GPU time: add orientation-resolved products of neighbouring coarse plaquette traces (the photon's conditional mean is quadratic in linear combinations of coarse angles), re-run the photon at 16^4; if it passes, re-run SU(2).

Files: `PREREG.md`, `NOTE.md`, `content.py`, `run_cpu.sh`, `cpu-test/` (selftest log, pipeline test), `runs-cpu/`.
