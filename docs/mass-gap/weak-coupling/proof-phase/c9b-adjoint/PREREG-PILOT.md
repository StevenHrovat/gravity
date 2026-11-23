# Pre-registration: CPU pilot for the constrained-sampling measurement (c9b, 2026-11-23)

Status: **written before any pilot data. Not run.** The three checks below start only after the owner's explicit OK (forwarded by the
coordinator). CPU only, one process at a time, each check capped at 30 minutes wall (`--max-wall`). No GPU. Parent draft:
`PREREG-GPU.md` (section 6, step 1). Code: `ir_condlaw.py`, `ir_constrained.py`; commands: `run_pilot.sh`.

What was done before this file (plumbing only, no result-bearing numbers): `py ir_condlaw.py selftest` and `py ir_constrained.py selftest`
pass. The latter checks the HMC force against finite differences (relative error 7e-10, blocking and penalty on); leapfrog reversibility
(8e-16); `|dH|` scaling with `eps^2` (ratio 4.0); the block variable against `../c3b-refit/goodblock.py` (n = 2, w = 2, difference 2.5e-15).
Toy runs on 4^4 lattices exercised the run, anneal and analysis paths; their numbers were discarded. Plumbing timings that sized this
pilot: one force evaluation takes 4.9 s at 16^4, b = 4 and 0.07 s at 8^4, b = 2 (numpy; level 1 is computed on the whole fine grid).
One trajectory takes 0.52 s at 4^4, n = 0, 16 chains, 20 steps.

**Deviation from the draft, decided now:** the blocked check runs at 8^4, b = 2 (coarse 4^4) instead of 16^4, b = 4. A 16^4 trajectory
costs about a minute on this CPU, so the draft's size would give no usable statistics in 30 minutes. The b = 4 path is covered by the
goodblock cross-check only. The GPU timing job stays as drafted.

**A finding from the plumbing, decided now:** the penalty makes stiff modes (frequency about `sqrt(kappa_c)`). Without a remedy, HMC
at `eps = 0.05` rejected every trajectory at `kappa_c = 200`. Remedies, both exact: (a) for n = 0, a kinetic mass `1 + kappa_c` on the
pinned links (`--pin-mass`); (b) for n >= 1, a step-size tuning rule run before production. The rule: at the final `kappa_c` on the
unmoved target, run 10 trajectories; while their acceptance is below 0.6, halve `eps` and double the number of steps (at most 6 times).
The tuning trajectories are discarded. The GPU plan's `kappa_c` values (100, 200, 400) are to be revisited with check P's tuning result.

## Reference values (closed form, computed before any data: `py ir_condlaw.py expected`)

The test law: a **spatial** link `x` of the **fitted coarse plaquette action** at `L sqrt(sigma) = 2.80`, central fit (`F_ts = 0.054`,
`F_ss = 0.171`, `A_ts = -0.000595`, `A_ss = 0.00149`; c3b base fit, central values, **not** the c4d box corner). The background is
block-flat (every other link `= 1`). The move is the flip of one ss partner `y` (`1 -> -1`). The exact conditional laws of `x` before
and after the move differ by:

* `TV_exact = 0.07031`, `KR_upper_exact = 0.09590` (the H^-1 bound, same function as the estimator), `Jbar_exact = 0.342` (= 2 F_ss).

## Check E1: the estimator against exact samples (`ir_condlaw.py exactcheck`)

10 repetitions. Each draws `2.5 x 10^5` exact samples from each law (rejection from Haar), fits both, and computes TV, KR_upper and Jbar.
It adds a blocked-bootstrap `sigma_boot` (8 pseudo-chains, 30 resamples) and a null TV (two independent samples of the same law).

Prediction for `sigma_boot(TV)`: `0.424 sqrt(8/n) = 0.0024`, from the Fisher information of the degree-1 coefficients near uniform.

PASS needs all of:
1. `|TV_hat - 0.07031| <= 2 sigma_boot` in at least 9 of 10 repetitions;
2. `|mean of the 10 TV_hat - 0.07031| <= 2 (sd over repetitions)/sqrt(10)`;
3. `sigma_boot` in `[0.0012, 0.005]`, and its ratio to the sd over repetitions in `[0.6, 1.6]`;
4. mean null TV `<= 0.01`;
5. `Jbar_hat` within 2 sd (over repetitions) of 0.342 in at least 9 of 10 repetitions; the same rule for `KR_upper_hat` against 0.09590.

## Check E2: sampler plus estimator on the fitted coarse action (`ir_constrained.py`, n = 0)

4^4 coarse lattice, the fitted action, block-flat background, `x = (0,0,0,0; 1)`, `y = (0,0,0,0; 2)`. All links except `x` are pinned by
the penalty, with `--pin-mass`, 16 chains, 30 thermalisation and 600 measured trajectories (`eps = 0.05`, 20 steps). Five runs: (a)
`kappa_c = 200`, no move; (b) 200, flip; (c) 800, no move; (d) 800, flip; (e) 800, no move, independent seed (null). Analyses: (a, b),
(c, d), (c, e).

Predictions: acceptance `>= 0.6`. Constraint residual about `1.5/kappa_c` (0.0075 and 0.0019; within a factor 2). The finite-`kappa_c`
bias is linear in `1/kappa_c`.

PASS needs all of:
1. acceptance `>= 0.6` in every run, and `resid_y` below `3/kappa_c` in the flip runs (the move took);
2. `TV_inf = (4 TV_800 - TV_200)/3` within `2 sigma_inf` of 0.07031 (`sigma_inf = sqrt(16 s_800^2 + s_200^2)/3`, `s` the bootstrap errors);
3. the same extrapolation for Jbar, within `2 sigma` of 0.342;
4. the null TV `(c, e)` `<= 3 sigma_boot` of that pair.

## Check P: the blocked pipeline (`ir_constrained.py`, n = 1)

SU(2) Wilson `beta = 0.5`, 8^4, b = 2 (good blocking, `w = 2`), coarse 4^4, the whole torus dynamic. `x = (0,0,0,0; 1)`,
`y = (0,0,0,0; 2)`. One typical background (`--bgseed 1000`, 30 unconstrained trajectories), shared by three runs: none (seed 21),
flip (seed 22), none again (seed 23, null). Each run uses `kappa_c = 100`, the tuning rule, a 20-trajectory anneal, 20 thermalisation and
150 measured trajectories, and a 600 s wall cap.

This is a **plumbing** check: at `beta = 0.5` the blocked couplings are tiny (coarse 2x2 Wilson loops about `(beta/4)^4`), so the true
flip coefficient is predicted `< 0.01`.

PASS needs all of:
1. acceptance `>= 0.6` after tuning;
2. `resid_y < 0.05` in the flip run (the coarse move took), constraint residual `< 0.05`;
3. `tau_int` (max over the components of `V_x`) finite and `< 15` trajectories;
4. `TV(none, flip) - TV(none, null)` consistent with 0 within `2 sigma` (bootstrap errors of the two pairs combined).

Reported as numbers for the GPU projection: `eps`, `nleap` after tuning, wall seconds per trajectory, `tau_int`, and `t_eff` (wall
seconds per effective sample).

## Verdicts

E1 or E2 fails: the estimator or the sampler is wrong, and no GPU job is proposed until it is fixed and the failing check is rerun under
an amendment. P fails 1-3: retune (an amendment, rerun). P fails 4: a bug or an unexpected strong-coupling effect; investigate before any
GPU job. All pass: the projection of `PREREG-GPU.md` step 3 uses P's `t_eff` (scaled to the GPU by the timing job, not by guesswork).

Marks: every pilot number is **numerical** (estimator and sampler validation). None of them is a statement about the true law at `L1`.

## Run-control change (2026-11-23, after E1's first run; no prediction or pass rule changed)

At the coordinator's request, E1 is wrapped in a hard 30-minute cap in `run_pilot.sh` (`timeout 1800`). E2 and P were already capped
by `--max-wall`. E1's first run happened **before** this cap was added; it took 2 min 34 s. Its result (a failure of criteria 1 and
3a) is in `PILOT.md`.

## Amendment 1, APPLIED (2026-11-23, before the rerun of E1; run 1 stays on record as FAILED, `PILOT.md`)

Approved by the owner (relayed by the coordinator): "And the ammendment is approved, since nothing rests on it."

1. All bootstrap errors (E1, and the analyses of E2 and P) use **200 resamples** instead of 30 / 50.
2. E1 criterion 3a: the `sigma_boot` band `[0.0012, 0.005]` is replaced by **`[0.0009, 0.0024]`**, the rule 0.6 to 1.6 times run 1's spread
   over repetitions (0.0015). All other criteria are unchanged.
3. E1 is rerun with **seed 20261125** (outputs `pilot_E1_run2.json` / `.log`; run 1's files are kept). E2 and P follow only if the
   rerun passes, stopping at the first failure.

## Amendment 2, APPLIED (2026-11-23 03:22, before any new data; runs 1 and 2 of E1 stay on record as FAILED, `PILOT.md`)

Approved by the owner (relayed by the coordinator): "Yes, replicas (a)".

**Why.** Pooled over runs 1 and 2, the blocked bootstrap underestimated the TV error by about 15 % (rms z 1.16).

**Error estimate (replaces the bootstrap everywhere in this pilot).** Each law's samples are split into K independent replicas, and
the error of the full-sample estimate is the delete-one jackknife over the replicas:
`sigma^2 = sum over the two compared (independent) ensembles of (K - 1)/K sum_i (theta_(i) - mean theta_(.))^2`. Each ensemble is
jackknifed separately: `theta_(i)` is the statistic with replica `i` of that ensemble removed and the other ensemble whole. (Corrected
before any data: the first version of this text deleted replica `i` of both ensembles together, which adds a spurious cross term.
For a difference of means, the separate form equals the exact standard error; selftest.)
- **E1:** K = 20 replicas of `2.5 x 10^5 / 20` exact samples each.
- **E2:** K = 16, one replica per chain (16 independent chains).
- **P:** one chain only, so no independent replicas exist. Its replicas are K = 5 consecutive time blocks of 30 trajectories, used
  only if P's criterion 3 (`tau_int < 15`, so blocks of at least 2 `tau_int`) passes first. This is a weaker error than true
  replicas, stated as such.

**Threshold rule (stated, not tuned to runs 1-2).** "Within 2 sigma" meant 95.45 % coverage for a known sigma. A jackknife sigma from K
replicas carries K - 1 degrees of freedom, so the same coverage needs `t_{K-1}(0.97725) x sigma`:
- **2.140** (K = 20, E1);
- **2.181** (K = 16, E2);
- **2.869** (K = 5, P).

Every "2 sigma" in the pass criteria below becomes this factor times the jackknife sigma; every "3 sigma" becomes 1.5 times that factor.
Nothing else changes:
- the counts (>= 9 of 10);
- the null-TV bound;
- the extrapolation formulas;
- criterion 3a's band `[0.0009, 0.0024]` and criterion 3b's ratio range `[0.6, 1.6]`, now for the jackknife sigma.

**Rerun.** E1 with seed 20261126 under the 30-minute cap (`pilot_E1_run3.json` / `.log`); then E2, then P, stopping at the first failure.
The bootstrap stays in the code as an option and is not used.

## Amendment 3, APPLIED (2026-11-23, before any new data; E2 run 1 stays on record as FAILED, `PILOT.md`)

Approved by the owner (relayed by the coordinator): "Yes, option (ii)".

**Why.** TV between two fits of the same law is nonnegative and of order `sqrt(13/N)` (E2 run 1: observed null 0.0287; simulated null
mean 0.023 to 0.030). E2's criterion 4 was therefore ill-posed, and every small per-pair TV carries the same upward bias.

**E2 criterion 4 (replaced).** The null TV (ensembles c, e) must lie below the **95 % quantile of the simulated null distribution**: 200
pairs of independent i.i.d. samples of the fitted law of ensemble c, each of size `n_eff = min_k N_k/(2 tau_k)` (`tau_k` the measured
`tau_int` of `V_x`, max over components), each fitted, TV computed.

**The debiased small-coefficient estimator (new).**
- **Estimand:** `D^2 = Delta theta . I_mid Delta theta`, with `Delta theta = theta_1 - theta_0` and `I_mid = (I(theta_0) + I(theta_1))/2`
  (the Fisher metric).
- **Estimator: the cross-replica U-statistic.** The ensemble's chains are grouped into **K = 8 replicas** (2 chains each in E2; P's 5
  time blocks, information only). Each replica `r` of each ensemble is fitted; with `Delta_r = theta_hat_1,r - theta_hat_0,r`,
  `D^2_U = (1/(K(K - 1))) sum_{r != s} Delta_r . I_hat_mid Delta_s` (`I_hat_mid` from the pooled fits). Different replicas have
  independent noise, so `D^2_U` is unbiased (up to the `O(1/n_r)` maximum-likelihood bias) with no model of the noise. It can be negative.
- **Coefficient:** `C_D = (1/2) sqrt(max(0, D^2_U))`. In the linear regime it is an upper bound on TV (Cauchy-Schwarz:
  `(1/2) E|Delta h| <= (1/2) sqrt(E Delta h^2)`; Pinsker to second order). It is conservative by the factor `E sqrt(X^2)/E|X|` of the
  direction (1.19 for this law; 0.5/0.424 = 1.18 for a linear flip at the uniform law).
- **Error:** delete-one jackknife over the K items `Delta_r` (the U-statistic is a function of these i.i.d. items), with threshold
  factor **`t_7 = 2.429`**.
- **Floor (paper, Gaussian quadratic form):** `Var(D^2_hat) >= 4 Delta theta . I Sigma I Delta theta + 2 tr((I Sigma)^2)`, with
  `Sigma = 2 tau (I_0^-1/N_0 + I_1^-1/N_1)`, evaluated at the fits, `tau` the measured `tau_int`.

**Reference values (closed form, now):** `D^2_exact = 0.02784`, `C_D,exact = 0.0834` (TV 0.0703).

**New E2 criteria (in addition to 1a-3 and the replaced 4):**
- 5. **Null:** `D^2_U(c, e)` consistent with 0: `|D^2_U| <= t_7 sigma_jk`.
- 6. **Recovery:** `D^2_inf = (4 D^2_U(800) - D^2_U(200))/3` within `t_7 sigma_inf` of 0.02784
  (`sigma_inf = sqrt(16 s_800^2 + s_200^2)/3`).
- 7. **Floor anchoring:** `sigma_jk(D^2) >= 0.491 sigma_floor(D^2)` for each of the three pairs (rule as in `PREREG-GPU.md` 6c).

**Rerun.** E2 with fresh seeds 111-115 (outputs `pilot_E2r2a`-`e.npz`, `pilot_E2r2.log`; 330 s cap per run). Then P as pre-registered
(its analyses print `D^2_U` and `C_D` for information; P's criteria are unchanged). Stop at the first failure.

## Amendment 4, APPLIED (2026-11-23, before any new data; E2 runs 1 and 2 stay on record as FAILED, `PILOT.md`)

Approved by the owner (relayed by the coordinator; question "Approve the 1.55 h W2 run, and the IR floor fix with a stop rule?"):
"Yes, both". **Stop rule:** if anything below fails, no further amendment. The pilot stops, and a short design review goes into `PILOT.md`.

**Defects of the old floor (`d2_floor`, used in E2 run 2):**
- (1) It modelled the chain correction by one scalar, the max `tau_int` over the components of `V_x`, instead of the influence-series
  correction that `PREREG-GPU.md` 6c prescribes.
- (2) For the cross-replica U-statistic it omitted the factor `K/(K - 1)` of the noise term.

**Corrected floor (paper).** With replica errors `epsilon_r` of covariance `K Sigma` (`Sigma` = covariance of the pooled difference of
the fits), `Var(D^2_U) = 4 Delta theta . I Sigma I Delta theta + (2K/(K - 1)) tr((I Sigma)^2)`, with
`Sigma = I_A^-1 Gamma_A I_A^-1/N_A + I_B^-1 Gamma_B I_B^-1/N_B`. Here `Gamma` is the long-run covariance of the 13-component series
`phi(V_x(t))`: the multivariate influence-series correction, which equals `I` for i.i.d. data. It is estimated by batch means: each
chain's series cut into batches of 20 trajectories, `Gamma_hat = 20 x Cov(batch means)`, pooled over the chains. `I` and `Delta theta`
are taken at the pooled fits.

**Calibration C1 (pre-registered here; exact i.i.d. samples; CPU; 30-min cap).** The fitted law at 2.80 (flat background), the null pair
`(theta_0, theta_0)` and the true pair `(theta_0, theta_1)`. 200 independent draws, each of K = 8 replicas of 980 samples per ensemble
(E2's size). For each draw: `D^2_U` and its jackknife. Floor at the exact parameters with `Gamma = I` and `N = 7840`.

PASS needs all of:
- (i) the spread of `D^2_U` over the 200 draws, divided by the floor, lies in **[0.90, 1.10]** (the 95 % band of a 199-dof sample sd),
  for the null and for the true pair;
- (ii) the mean of the null `D^2_U` is within `2.6 x sd/sqrt(200)` of 0, and the mean of the true `D^2_U` within `2.6 x sd/sqrt(200)` of
  0.02784 (2.6 = the 99 % two-sided normal point, for two tests);
- (iii) reported, not judged: the mean jackknife error divided by the actual spread, for both pairs. This tells whether the jackknife
  itself is calibrated at K = 8.

**Then E2 run 3:** fresh seeds 211-215 (`pilot_E2r3*`), all of E2's criteria (1a-7), with criterion 7 using the corrected floor.
**Then P** as pre-registered. Stop at the first failure.
