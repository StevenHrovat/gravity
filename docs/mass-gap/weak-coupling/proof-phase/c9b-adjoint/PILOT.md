# CPU pilot: results (PREREG-PILOT.md), 2026-11-23

Status: **E1 PASSED (run 3), calibration C1 PASSED, E2 PASSED (run 3); P FAILED (no production data within its cap). Under the
owner's stop rule (amendment 4) there is no further amendment: the pilot stops, and the design review is at the end of this file. The
GPU timing job was not run.** E2 and P were not run
(their pass rules use the same bootstrap errors, which E1 found too small), and no GPU job was started. Owner's approval for the pilot and
one timing job: relayed by the coordinator ("Yes, pilot + timing").

## E1: estimator against exact samples (`pilot_E1.json`, `pilot_E1.log`; 2 min 34 s, CPU)

Exact (closed form): TV 0.07031, KR_upper 0.09590, Jbar 0.342.

| criterion | result | verdict |
|---|---|---|
| 1. `|TV_hat - exact| <= 2 sigma_boot` in >= 9 of 10 | 8 of 10 | **FAIL** |
| 2. mean of 10 within `2 sd/sqrt(10)` | 0.07020 vs 0.07031 (diff 0.00012, allowed 0.00094) | pass |
| 3a. `sigma_boot` in `[0.0012, 0.005]` | 0.00085 to 0.00167 | **FAIL** |
| 3b. ratio `sigma_boot`/(sd over reps) in `[0.6, 1.6]` | 0.81 (sd over reps 0.00149) | pass |
| 4. mean null TV `<= 0.01` | 0.0041 | pass |
| 5. Jbar, KR_upper within 2 sd in >= 9 of 10 | 9 / 10 and 10 / 10 (means 0.3402, 0.09566) | pass |

**Reading.** The estimator is unbiased at this sample size: the mean is 0.07020 against 0.07031, and Jbar and KR_upper agree too. What
failed is the **error estimate**. The 30-resample blocked bootstrap is noisy and about 20 % below the true spread (ratio 0.81), so 2 of
10 repetitions fall outside 2 `sigma_boot`. The pre-registered band for `sigma_boot` (prediction 0.0024 from the near-uniform Fisher
information) was a factor 1.6 too high: the true spread is 0.0015. This also means `PREREG-GPU.md`'s sample-size estimate
(`N_eff = 2.5 x 10^5` for `+-0.004`) is conservative by about that factor. The finite-sample bias of TV (null 0.004) is small but not zero.

## Proposed amendment (not applied; a pre-registration change, so the owner's decision; run 1 stays on record as FAILED)

1. Errors from 200 bootstrap resamples (instead of 30); in addition, report the spread over repetitions as the reference error.
2. Replace the `sigma_boot` band by the coordinator's rule-based band: 0.6 to 1.6 times run 1's spread over repetitions (0.0015),
   i.e. `[0.0009, 0.0024]` (the pre-registration's own ratio test). My first proposal `[0.0008, 0.003]` is withdrawn: its floor sat just
   under the observed minimum, so it was set by eye from the data, and I have no principled reason for it.
3. Keep criterion 1 unchanged, and rerun E1 with seed 20261125. Only if it passes, run E2 and P as pre-registered, with 200 resamples in
   their analyses.

## Prepared for the timing job (not run)

`ir_constrained.py` now has a lean path: the block variable is computed only on the sublattices it needs, and the plaquette gradient one
plane at a time. The selftest shows it equals the default path (block variables and action exactly, gradient to 3e-16). There is also a
`timing` subcommand: GPU, heat-bath background from c3b's updater, the tuning rule, a progress line per trajectory, saves every 10
trajectories, self-stop at `--max-wall`. A toy CPU run exercised it. Not written yet: `TIMING.md` and the external watcher.

The GPU was not free when checked: 91 % utilisation, from two `diag3.py` processes in another session's scratchpad (PIDs 3572, 4036).
They were the crossover session's diagnostics, started about 10 minutes earlier. (A first report here misread their start time as a
day earlier; corrected.) They have since finished. The coordinator sequences GPU slots between this job and the crossover session's
timing job.

## E1, run 2 (amendment 1 applied: 200 resamples, band [0.0009, 0.0024], seed 20261125; `pilot_E1_run2.json` / `.log`; 14 min 40 s)

Evaluated by `pilot_eval.py` (written before the data):

| criterion | result | verdict |
|---|---|---|
| 1. within 2 `sigma_boot` in >= 9 of 10 | 8 of 10 | **FAIL** |
| 2. mean within `2 sd/sqrt(10)` | 0.07065 vs 0.07031 (diff 0.00033, allowed 0.00087) | pass |
| 3a. `sigma_boot` in `[0.0009, 0.0024]` | 0.00098 to 0.00141 | pass |
| 3b. ratio to the sd over reps in `[0.6, 1.6]` | 0.84 (sd 0.00138) | pass |
| 4. mean null TV `<= 0.01` | 0.0040 | pass |
| 5. Jbar, KR_upper in >= 9 of 10 | 10 / 10, 9 / 10 (means 0.3442, 0.0963) | pass |

**Diagnosis (both runs pooled, 20 repetitions; numerical).** In units of `sigma_boot`, the deviations `z = (TV_hat - exact)/sigma_boot`
have mean 0.1, so there is no bias. Their rms is **1.16** (1.0 expected), and 4 of 20 lie outside 2 (at |z| = 2.04 to 2.36; about 1
expected). The blocked bootstrap underestimates the error of TV by about 15 %, consistently in both runs. The estimator itself is fine;
its error bar is not.

Options (for the owner; none applied, and none chosen here):
- (a) Errors from independent replicas (several independent sub-ensembles per law, their spread) instead of the bootstrap. This is
  natural on the GPU with B chains.
- (b) Keep the bootstrap with a calibration factor fixed from E1. That is a fit to E1's data, so it would need a fresh validation run.
- (c) Accept 80 % coverage at 2 `sigma_boot` and widen the verdict bands of `PREREG-GPU.md` by the factor 1.16. This changes no physics
  verdict at the precision planned (the UNDECIDED bands are 0.95 to 1.05).

E2, P and the GPU timing job were not run.

## E1, run 3 (amendment 2: jackknife over K = 20 replicas, t = 2.140; seed 20261126; `pilot_E1_run3.json` / `.log`; 4 min): PASS

All criteria pass:
- 10 / 10 within `t sigma`;
- mean TV 0.07059 vs 0.07031;
- sigma 0.00102 to 0.00156, ratio to the spread 1.20;
- null TV 0.0039;
- Jbar and KR_upper both 10 / 10.

## E2 (amendment 2; `pilot_E2.log`, `pilot_E2a`-`e.npz`; 28 min, every run at its 330 s cap, 420-466 measured trajectories x 16 chains): FAIL

| criterion | result | verdict |
|---|---|---|
| 1a acceptance >= 0.6 | 0.99 in all five runs (tuning kept `eps = 0.05`, `nleap = 20`) | pass |
| 1b `resid_y < 3/kappa_c` (flip runs) | 0.0075 < 0.0150; 0.0019 < 0.0037 | pass |
| 2 `TV_inf` within `t sigma_inf` (t = 2.181) | TV 0.0682 (`kappa_c` 200), 0.0718 (800), extrapolated 0.0730 +- 0.0091 vs 0.0703 | pass |
| 3 `Jbar_inf` within `t sigma_inf` | 0.3015, 0.3566, extrapolated 0.375 +- 0.046 vs 0.342 | pass |
| 4 null TV `(c, e) <= 1.5 t sigma` | 0.0287 vs 3.27 x 0.0083 = 0.0272 | **FAIL** |

Also measured: `tau_int` of `V_x` 0.66 to 0.80 trajectories; constraint residual about `1.5/kappa_c` (0.0075, 0.0019), as predicted.

**Diagnosis (post-hoc, `e2_null_posthoc.py` / `.log`, 2.4 min CPU, not a rerun).** The null TV of two independent samples of one exact
law, each fitted, has mean 0.023 (sd 0.0044, 95 % quantile 0.030) at 7400 i.i.d. samples, and 0.030 (sd 0.0055, q95 0.041) at 4600 (about
`7400/(2 tau_int)`). The observed 0.0287 is in that range. So the sampler adds no spurious signal; **criterion 4 was ill-posed**.

The trouble: TV is nonnegative and, between two fits of the same law, is of order `sqrt(13/N)` (the norm of a 13-dimensional fluctuation),
not centred at 0. Comparing it with a multiple of its own spread fails at small `N` by construction. (E1's version of this criterion, an
absolute bound 0.01 at `n = 2.5 x 10^5`, was well posed.)

**Consequence for `PREREG-GPU.md` (to be fixed before any GPU data).** The same upward bias, about `0.023 sqrt(7400/N_eff)`, sits in
every **small** per-pair TV. At the planned `N_eff = 2.25 x 10^4` it is about 0.013 per pair, comparable to the ts coefficients (0.023)
and far above the rectangle class (0.004). Summed over a column it would add about 0.2. Large TVs (the ss class, 0.07) are in the smooth
regime, where the bias is `O(1/N)` and small. The plan needs a debiased small-coefficient estimator before the projection means anything.
One option: the squared parameter difference minus its trace bias, `||Delta theta_hat||^2_I - tr(I^-1 Cov)`, turned into TV in the
linear regime.

Options for the pilot (owner's call; none applied):
- (i) Amendment 3: replace E2's criterion 4 by "null TV below the 95 % quantile of the simulated null distribution at the ensemble's
  effective size `N/(2 tau_int)`" (derived from the law, like the floor), and rerun E2 with fresh seeds before P.
- (ii) As (i), plus make the debiased estimator part of the pilot, so that E2 and P test it before the GPU run.

## E2, run 2 (amendment 3; seeds 111-115; `pilot_E2r2.log`, `pilot_E2r2a`-`e.npz`; 32 min): FAIL on criterion 7 only

| criterion | result | verdict |
|---|---|---|
| 1a / 1b | acceptance 0.99; `resid_y` 0.0075 < 0.015, 0.0019 < 0.0037 | pass |
| 2 TV_inf | 0.0690 +- 0.0094 vs 0.0703 (`kappa_c` 200: 0.0851, 800: 0.0730) | pass |
| 3 Jbar_inf | 0.331 +- 0.042 vs 0.342 | pass |
| 4 null TV below the simulated q95 at `N/(2 tau)` | 0.0221 vs 0.0366 (simulated mean 0.0282, `n_eff` 5148) | pass |
| 5 null `D^2_U` consistent with 0 | -0.0011 +- 0.0013 | pass |
| 6 `D^2_inf` vs 0.02784 | 0.0234 +- 0.0079 (200: 0.0378, 800: 0.0270); `C_D,inf` 0.076 vs 0.0834 | pass |
| 7 `sigma_jk(D^2) >= 0.491 sigma_floor` | pairs (a, b) 0.0092 vs 0.0038 pass; (c, d) 0.0055 vs 0.0035 pass; **null (c, e) 0.00131 vs 0.00136 (ratio 0.475)** | **FAIL** |

**Reading.** The debiased estimator does what it should: the null is consistent with 0, the true value is recovered, and the replaced null
test passes. The failure is the floor rule on the null pair, by 3 %. Possible causes, not separable with this run:
- (a) a jackknife fluctuation (K = 8; the threshold is the 2.5 % quantile per pair, so about 7 % for three pairs);
- (b) the floor is too high at the null. `d2_floor` used `tau` = the max `tau_int` over the `V_x` components (0.66-0.76), not the
  influence-series `tau` that 6c prescribes. And in the i.i.d. smoke test, before this run, the null U-statistic's actual spread was
  0.77 of the Gaussian floor (0.00116 vs 0.0015; 15 draws).

(b) is a defect in my floor implementation for the U-statistic at the null, not in the sampler or the estimator.

Proposal (owner's call; none applied): compute the floor with the influence-series `tau` (6c), and calibrate the null floor of the
U-statistic on exact i.i.d. samples in a pre-registered E1-type check before it is used as a rule. Then rerun E2's criterion 7 on fresh
seeds, then P.

## Calibration C1 (amendment 4; `pilot_C1.json` / `.log`; 19 min CPU): PASS

The corrected floor `Var(D^2_U) = 4 d.I Sigma I d + (2K/(K - 1)) tr((I Sigma)^2)` against the actual spread of `D^2_U` over 200
independent draws on exact i.i.d. samples (K = 8 replicas of 980):

| pair | spread | floor | ratio (pass band [0.90, 1.10]) | mean (target) |
|---|---|---|---|---|
| null | 0.00140 | 0.00139 | 1.004 | -0.00009 (0; allowed +-0.00026) |
| true | 0.00528 | 0.00553 | 0.955 | 0.02764 (0.02784; allowed +-0.00097) |

Mean jackknife error / actual spread (information): 1.42 at the null (conservative, as expected for a degenerate U-statistic), 1.06 at
the true pair.

## E2, run 3 (amendment 4; seeds 211-215; `pilot_E2r3.log`, `pilot_E2r3a`-`e.npz`; 32 min): PASS

| criterion | result |
|---|---|
| 1a / 1b | acceptance 0.99; `resid_y` 0.0076 < 0.015, 0.0018 < 0.0037 |
| 2 TV_inf | 0.0711 +- 0.0096 vs 0.0703 |
| 3 Jbar_inf | 0.367 +- 0.050 vs 0.342 |
| 4 null TV vs simulated q95 | 0.0227 vs 0.0403 (`n_eff` 4588) |
| 5 null `D^2_U` | -0.0020 +- 0.0021 |
| 6 `D^2_inf` | 0.0267 +- 0.0105 vs 0.02784 (`C_D,inf` 0.082 vs 0.083) |
| 7 floor anchoring (corrected floor) | 0.00622 / 0.491 x 0.00622; 0.00771 / 0.491 x 0.00617; null 0.00208 / 0.491 x 0.00243: all pass |

## P, run 1 (`pilot_P.log`, `pilot_Pa`-`c.npz`; 30 min): FAIL, no production data

The tuning rule needed four halvings in every run. Acceptance by step:

| step | `eps` | `nleap` | acceptance |
|---|---|---|---|
| 1 | 0.05 | 10 | 0.0 |
| 2 | 0.025 | 20 | 0.0 |
| 3 | 0.0125 | 40 | 0.0 to 0.5 |
| 4 | 0.00625 | 80 | 0.8 to 0.9 |

A trajectory then costs about 50 s on this CPU at 8^4, b = 2, so each run reached its 600 s cap after 10-11 trajectories, all spent in
tuning: **0 measured trajectories** (`stopped_at` 10-11). The analysis then crashed on the empty arrays, a robustness bug in `analyse`.
Criterion 1 cannot be evaluated; the check failed for lack of data.

## Design review (stop rule of amendment 4)

**The attempts, and why each failed.**

| attempt | what failed | cause |
|---|---|---|
| E1 run 1 | criteria 1, 3a | the blocked bootstrap underestimated the TV error by about 15 %, and my predicted error band had a factor-2 slip (`dTV/d(Delta a)` = 0.212, not 0.424) |
| E1 run 2 | criterion 1 | the same bootstrap underestimate (pooled rms z 1.16) |
| E2 run 1 | criterion 4 | ill-posed null test: TV between two fits of one law is nonnegative, of order `sqrt(13/N)`, not centred at 0 |
| E2 run 2 | criterion 7 | my floor implementation: a scalar max `tau` instead of the influence-series covariance, and a missing `K/(K - 1)` |
| P run 1 | no data | sampler stiffness: the penalty on blocked variables forces `eps` 8 times smaller, and the 600 s budget had no room for it |

What finally passed, after the redesign during the pilot: replica (jackknife) errors, the debiased `D^2_U` estimator, the corrected floor
(C1: spread / floor = 1.00 and 0.96), and E2 with all eight criteria. The statistics layer is now validated on exact and sampled data.

**Shared cause.** Attempts 1-4 share one: **the statistics layer was pre-registered before its pieces were derived.** The error method,
the null test, the expected error and the floor were written down as numbers or rules, and the derivations (the sampling distribution of
each estimator, done afterwards and each in minutes) came only after a run had failed. Attempt 5 has a related cause, in the budget rather
than the statistics: **the run budget was fixed before the step size was measured.** The plumbing had already shown stiffness at toy size
(`eps` 0.025 needed at 4^4), but the pre-registration did not turn that into a budget rule. Common to all five: **a number entered a pass
rule or a budget before the quantity behind it had been computed or measured cheaply.**

**A clean redesign (for the owner; nothing applied).**
1. **Derive first, then pre-register.** For every estimator, the sampling distribution: floor, bias, null distribution. Each criterion is
   then a coverage statement at a stated level; no hand-set bands. (Done now for TV, Jbar, KR_upper, `D^2_U`; still to do for `KR_D`,
   the W1 analogue, before the GPU.)
2. **A separate, cheap tuning pre-step per setting**, recorded before the production plan. It fixes `eps` and `nleap` and measures
   seconds per trajectory; the production length is then computed (cap minus overheads, divided by seconds per trajectory). If that
   leaves fewer than 100 measured trajectories, the setting is redesigned, not run.
3. **The sampler for blocked constraints needs preconditioning**, not just a smaller step:
   - (a) a kinetic mass per fine link from the blocking Jacobian (`1 + kappa_c x` the summed squared sensitivity of the constrained
     block variables to that link), computed once; still exact HMC. It is the blocked analogue of the pinned-link mass that worked at
     n = 0 (acceptance 0.99, `eps` 0.05);
   - (b) smaller `kappa_c` (10, 20, 40) with the `1/kappa_c` extrapolation, which E2 validated (`TV_inf`, `D^2_inf` recovered).

   With (a) and (b), P is expected to run near `eps` 0.05 again. That is to be shown by the tuning pre-step, not assumed.
4. **Consequence for the GPU timing job:** at `b = 8`, `kappa_c = 200` the stiffness will be worse than at `b = 2`, `kappa_c = 100`. The
   timing job as written would mostly measure tuning. It should run only after (3) is in place and a CPU tuning pre-step at `b = 4` has
   shown `eps >= 0.02` with acceptance >= 0.6.
5. **Robustness:** `analyse` must report "no data" instead of crashing on empty arrays.
