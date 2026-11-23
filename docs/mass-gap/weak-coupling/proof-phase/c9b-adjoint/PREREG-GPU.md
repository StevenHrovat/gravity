# DRAFT pre-registration (not run, not approved): the true law's c0, c1 and W1 column at L1 by constrained sampling

Status: **draft, 2026-11-23.** Nothing here has been run. No GPU job may start without the owner's explicit OK, and only after the timing
job of section 6 has been run and the whole run projected from it. The code does not exist yet (section 7). Shared with c8a's H_sat test
(`../c8a-saturation/NOTE.md` section 6.3): the centre-flip runs below measure H_sat's quenched centre constant at block level 1.

Marks used for outcomes: **numerical** (Monte Carlo, statistical and systematic errors stated). A pass is evidence about the true law at the
tested backgrounds, **not** a bound: the sup over all coarse data is replaced by a max over a finite list. A fail at one background is
decisive for the sup form at that `L1` and that block variable (one background with column > 1 refutes the sup-form condition there; it does
not refute the gap).

## 1. What is measured, and why

c9b (section 1.3) reduced the adjoint budget to single-site quantities of the **true** coarse conditional specification at `L1`:
`H(v_x | rest)`, the conditional log-density of one coarse block variable `V_x` (SU(2), the good blocking of c3b, `w = 2`) given all other coarse
variables and the fine outside. Round 2 (`ROUND2.md`, N2) showed that for the **fitted** action at `L sqrt(sigma) = 2.80`:

* sharp sup-form pair coefficients are 0.43 x the crude ones used in N1; sharp spatial column 1.021 (central fit), weighted spectral radius
  0.960 (post-hoc); W1 column 0.73 (certified, c4d); TV-Lipschitz column 0.51 per radian;
* so the fitted action is within a few per cent of the sup-form Dobrushin window and inside the W1 window. The question is the true law.

Per pair `(x, y)` of coarse links and per background (all other coarse data and the fine outside fixed), the measurement estimates the
conditional law `p(v_x | V_y = w)` for a few values `w`, and from it:

| quantity | definition | role |
|---|---|---|
| `C_xy` (sharp sup form, **max over the listed moves**) | `TV(p(. | w), p(. | -w))` (centre flip), `TV(p(. | w), p(. | w R))` (`R` a 90-degree SO(3) rotation), and in Stage B 4 random `w'` per class; max over these | Hamming Dobrushin column (H_prop, sup form); a lower estimate of the sup over moves (N2: the antipodal flip is the maximiser for every fit) |
| `C1_xy` | the centre-flip TV alone | centre-odd half, `c1`; **H_sat at block level 1** |
| `C0_xy` | TV of the centre-symmetrised laws `(p(.|w) + p(.|-w))/2` vs `(p(.|wR) + p(.|-wR))/2` | centre-blind half, `c0` (H_adj) |
| `K_xy` (W1) | `KR(p(.|w), p(.|w e^{delta X}))/delta`, `delta = 0.2 rad`, geodesic cost | W1 column (c4d's quantity, true law) |
| `Lam_xy` | `TV(p(.|w), p(.|w e^{delta X}))/delta` | smoothing constant (round 2, section 1) |
| `Jbar_xy` | half the sup over `v` of the change of the centre log-odds `log p(v|.)/p(-v|.)` under the flip of `w` | c8a's `Jbar_P` (block level 1): H_sat needs `18 tanh(Jbar) < 1` |

Columns: `c = sum_y C_xy` over measured pair classes times their multiplicities (18 plaquette partners: classes s<-ss (12), s<-ts (2 spatial +
4 temporal), t<-ts (6 temporal + 12 spatial); 90 rectangle partners in their symmetry classes; two classes at coarse distance 2 to bound
the tail); the 2x2 type matrix and its spectral radius (weighted form, as in N2 post-hoc).

## 2. Points, backgrounds, controls

* **Primary:** SU(2), `beta = 2.3`, `b = 8`, `L sqrt(sigma) = 2.80` (c3b's only content-PASS point; c4d's certified fit).
* **Secondary (only if the timing allows and the primary is not decisive):** a larger `L1` with content: `beta = 2.3`, `b = 12`
  (`L sqrt(sigma) about 4.2`) on a fine lattice large enough for coarse 6^4 (72^4), with c3b's content check (>= 3 sigma) run first. The
  existing larger-`L` fits (2.92, 4.13, 5.60) failed the content check, so their small columns (N2: 0.89, 0.62, 0.55) are noise-limit
  suspects; no verdict is drawn at a point without content.
* **Backgrounds** (all other coarse variables in the region and the fine outside): (a) 8 typical ones, sampled from the unconstrained
  ensemble; (b) extremes: block-flat (`V = 1` around `x`), random Haar coarse data, a centre twist through the plaquettes of `x`, and
  large coarse curvature (coarse plaquettes near `-1`). Fine outside: taken from the sampled configuration of the background; UV-bad
  outsides are excluded by construction (they are handled by the pattern-conditioned assembly, ROUND2.md section 2).
* **Controls (gates; no SU(2) verdict unless both behave):** U(1) `beta = 1.1` (Coulomb, same blocking): predicted centre-flip column
  `> 2` (the photon propagates: FAIL expected); 2I `beta = 6` (c8b's tie point): predicted at least one pair with `C > 0.5` (frozen
  sectors). A CPU pilot at SU(2) `beta = 0.5` on a small lattice (where the blocked conditional law is close to the fitted plaquette form)
  must reproduce the N2 quadrature for the fitted couplings within 2 sigma. **Estimator test** (separate from the physics): the same
  sampler and fit run on the **fitted coarse plaquette action itself** (sampled exactly, coarse lattice, no blocking), where the single-link
  conditional law is known in closed form; agreement within 2 sigma is required before any blocked run.

## 3. Method (constrained sampling)

* **Region.** The fine links of the coarse cells within coarse distance 2 of `x` (for `b = 8`: a 40^4 fine region minus the frozen
  outside layer); everything outside the region frozen at the background's fine configuration.
* **Constraint.** All coarse variables `V_y` in the region except `V_x` constrained to prescribed values `w_y` by a penalty
  `kappa_c sum_y (1 - (1/2) Re tr(V_y(U) w_y^dagger))` added to the Wilson action; `kappa_c in {100, 200, 400}`, linear extrapolation in
  `1/kappa_c` (the penalty width must be well below the scale on which `p(v_x | .)` changes; checked by the extrapolation slope).
* **Sampler.** HMC on the fine links of the region with the penalty force (the block variable's derivative through the smearing and the
  SU(2) projection, as in `goodblock.py`), `B = 64` independent chains in parallel on the GPU per ensemble; integrated autocorrelation of
  the `V_x` moments measured per ensemble.
* **Density estimate.** Maximum likelihood fit of `log p(v_x)` in SU(2) characters/Wigner functions up to `j = 1` (13 coefficients;
  `j = 3/2` added as a check), TV and KR computed from the fitted densities by quadrature (the N2 code), errors by blocked bootstrap over
  chains. Precision target: pair TV to `+-0.004` (1 sigma), i.e. column to about `+-0.05`; from the Fisher information of the
  `j = 1/2` coefficients (`Var = 4/N` per component near uniform) this needs about `N_eff = 2.5 x 10^5` effective samples per ensemble.
* **Ensembles per (background, pair class):** `w`, `-w`, `wR`, `w e^{delta X}` (4); `kappa_c`: 3 values for the primary typical
  backgrounds and the plaquette classes, 1 value (`kappa_c = 400`) elsewhere. For the single-`kappa_c` ensembles the penalty bias is
  taken as the largest extrapolation shift `|C(400) - C(infinity)|` seen in the 3-value ensembles of the same class type and added to
  the systematic error.

## 4. Predictions and verdicts (fixed before any data)

Fit predictions (N2 diagnostics, fitted action): `C(s<-ss) = 0.074`, `C(s<-ts) = 0.023`, `C(t<-ts) = 0.023`; sharp column 1.02, spectral
radius 0.96; `c0` column about 0.02 (N1, crude; the sharp value is smaller); W1 column 0.73 (plaquettes) / 0.964 (with the rectangle,
c4d); Lam column 0.51/rad; rectangle class: W1 `k_R = 0.00255` per pair (c4d, 90 pairs: +0.23), sharp TV estimate `0.424 b_R = 0.0036` per
pair (90 pairs: about +0.32 to the sup column; an estimate, not computed in N2).

* **H_adj(L1):** PASS if the max over backgrounds of the `C0` column is `< 0.1` (upper 2-sigma); FAIL if `> 0.5`.
* **H_prop(L1), sup form:** PASS if the spectral radius of the max-over-backgrounds type matrix (plaquette + rectangle classes, plus the
  distance-2 tail) is `< 0.95` (upper 2-sigma); FAIL if `> 1.05` (lower 2-sigma); otherwise UNDECIDED. A PASS is "max over listed
  backgrounds and moves", not a sup. **Expected outcome at 2.80: UNDECIDED or FAIL** (fit: 0.96 plaquettes only, plus about 0.3 from the
  rectangle). Deciding a value near 0.96 needs about `+-0.02` on the column, six times the samples of section 3: not planned; the
  sup form is decided only if the true value is far from the fit.
* **H_prop(L1), W1 form + smoothing:** PASS if the W1 column (plaquette + rectangle + tail classes) is `< 0.9` (upper 2-sigma) and the
  Lam column is finite; FAIL if `> 1.05` (lower 2-sigma); otherwise UNDECIDED. This is the **decisive quantity at 2.80**; then the round-2 count
  `kappa_Ham <= K_s (col_TV + Lam_col pi c_W/(1 - c_W))` is evaluated with the measured numbers (K_s from the measured class matrix).
* **H_sat (block level 1):** report `18 tanh(Jbar)` (max over backgrounds); c8a's criterion `< 1`.
* **Tail:** rectangles are part of every verdict (they are not a tail: c4d's fitted `b_R` is a real coupling). If the distance-2 classes
  add more than 0.1 to a column, that verdict is void and the next shell is required.
* **Noise-limit rule:** a verdict is drawn only at a point with c3b's content PASS, with the block variable for which the UV term is bounded.

## 5. What a result would and would not show

A PASS of H_adj and H_prop (either form) at 2.80 is numerical evidence that the true coarse conditional specification at `L1` satisfies the
single-site hypotheses of c9b section 1.3 at the tested backgrounds; it is not a proof (finite backgrounds, finite `kappa_c`, finite
statistics), and the two-level coupling's UV terms (`b_UV`, `C_UV`) are not measured here. A FAIL of the sup form with a W1 PASS sends the
route to the W1-plus-smoothing count. A FAIL of both at a point with content is the first real obstruction for the one-box route at that `L1`.

## 6. Timing plan (before any production)

1. **CPU pilot** (pre-registered in `PREREG-PILOT.md`, which supersedes the sizes given here: 8^4, b = 2 for the blocked check): the full pipeline at SU(2) `beta = 0.5`, a 16^4 lattice, `b = 4`, two backgrounds,
   one pair class; checks of section 2's pilot gate and of the TV/KR estimators against N2's quadrature.
2. **One timing job on the GPU** (after the owner's OK for this job alone): the primary point, one typical background, class s<-ss,
   `w` only, `kappa_c = 200`, `B = 64` chains, 30 minutes wall. Record: wall time per trajectory, acceptance, `tau_int` of the `V_x`
   moments, GPU memory. Output `t_eff` = wall seconds per effective sample.
3. **Projection** = `t_eff x N_eff x (number of ensembles)`, with `N_eff = 2.5 x 10^5` and the ensemble count:
   primary: 3 plaquette classes x 4 values x (8 typical backgrounds x 3 `kappa_c` + 4 extremes x 1) = 336, plus 12 backgrounds x 8
   further classes (rectangles, tail) x 4 x 1 = 384: **720 ensembles**; controls U(1) and 2I: 2 backgrounds x 3 classes x 4 x 1 = 24 each;
   secondary point: as the primary. Reported to the owner as GPU-hours per block, with a staged plan:
   **Stage A** (decisive subset): 4 typical + block-flat backgrounds, plaquette classes, all 4 values, `kappa_c` 2 values: 120 ensembles,
   plus the rectangle classes at the same 5 backgrounds, `kappa_c = 400`: about 120 more (rectangles enter every verdict);
   **Stage B**: the rest of the primary; **Stage C**: controls; **Stage D**: secondary point. Each stage needs its own OK.
4. If `t_eff` makes Stage A exceed 24 GPU-hours, the precision target is relaxed to column `+-0.1` (a factor 4 fewer samples) and the
   UNDECIDED band widened accordingly, decided before Stage A starts.

## 6a. Hardware constraint (recorded 2026-11-23, before any GPU data)

The GPU is an 8 GB laptop card. It sets the lattice for the timing job and for any later production on this machine: fine 40^4 at
`b = 8` (coarse 5^4, region radius 2 = the whole coarse torus), `B` as memory allows (expected 1 to 2 chains). The block variable is
computed only on the sublattices it needs (`ir_constrained.py`, lean path; equal to the default path, selftest). The 72^4 secondary
point of section 2 does not fit this card; it needs a larger GPU or a region-only implementation.

## 6b. Amendment (2026-11-23, before any GPU data): replica errors

The pilot showed that the blocked bootstrap underestimates the error of TV by about 15 % (`PILOT.md`). Following the owner's choice for
the pilot ("Yes, replicas (a)"), the measurement switches too:
- **Errors.** Every error in sections 3 and 4 is the jackknife over K independent replicas per ensemble (`ir_condlaw.jackknife`: each
  compared ensemble separately, variances added). The replicas are independent chains: the `B` chains of one run where memory allows,
  otherwise separate runs with their own seeds, sharing the background and the tuned step size. **K = 8.** Time blocks of one chain are
  not used.
- **Thresholds.** Every "upper 2-sigma" / "lower 2-sigma" in section 4 becomes `t_7(0.97725) = 2.43` times the jackknife sigma (the
  same 95.45 % coverage).
- **Precision target.** Unchanged (`+-0.004` per pair TV). The cost per ensemble now includes K independent thermalisations; the
  projection (`TIMING.md`) accounts for it.

## 6c. Amendment (2026-11-23, before any GPU data): the statistical floor of every error bar

Owner's question: "I would assume we can derive the expected minimum error bar that is associated with the measurement uncertainty for
the system, right? In that case it would let us make the error bar not arbitrary."

**The floor (paper; `floor.py`, `floor.log`).** For `n` i.i.d. samples per law, the fitted parameters of the 13-parameter family are
asymptotically normal with covariance `I(theta)^-1 / n`, where `I = Cov_theta(phi)` (Cramer-Rao; attained by maximum likelihood). For a
smooth statistic `g` of two independent fits, the delta method gives
`sigma_floor^2 = (grad_0 g . I_0^-1 grad_0 g + grad_1 g . I_1^-1 grad_1 g)/n`. For TV, `grad_0 TV = (1/2) E_0[sign(p_0 - p_1)
(phi - E_0 phi)]` (smooth: TV >> 0 and the set `p_0 = p_1` is null; it agrees with finite differences to 2e-12). For Markov-chain data
the variance of each fit's contribution is multiplied by `2 tau_psi`, where `tau_psi` is the integrated autocorrelation time of that
ensemble's influence series `psi(t) = grad g . I^-1 phi(V_x(t))`, measured. (This is the right time, not the max over components of
`V_x`.) With `N` total samples over the replicas: `sigma_floor^2 = sum over the two ensembles of 2 tau_psi grad g . I^-1 grad g / N`.

**Check against the pilot (numerical, no new run).** E1's setting (`n = 2.5 x 10^5`):

| statistic | floor | observed sd over 30 repetitions (runs 1-3 pooled) | ratio | 95 % band of the ratio for 29 dof |
|---|---|---|---|---|
| TV | 0.00119 | 0.00129 | 1.08 | [0.74, 1.26] |
| Jbar | 0.0061 | 0.0069 | 1.14 | |
| KR_upper | 0.00163 | 0.00174 | 1.07 | |

The observed spread sits at or just above the floor, as it should. The earlier prediction `0.424 sqrt(8/n) = 0.0024` had a factor 2
slip: 0.424 is `dTV/dbeta` for an antipodal flip, but the fitted linear coefficient moves by `Delta a = 2 beta`, so `dTV/d(Delta a) =
0.212` (exact gradient: 0.201 and 0.209 for the two laws). Corrected: `0.212 sqrt(8/n) = 0.0012`. (Run 1 and 2's bootstrap errors
reached down to 0.00085, below the floor: the rule below would have flagged them.)

**Rules for the GPU run onward (pilot checks E2 and P keep their pre-registered criteria):**
1. **Floor check per ensemble pair.** The jackknife error from K = 8 replicas must satisfy
   `sigma_jk >= sqrt(chi2_{K-1}(0.025)/(K - 1)) x sigma_floor = 0.491 sigma_floor` (the 2.5 % quantile of a K-replica error whose true
   value is the floor). Below it: a **bug flag**; that pair's verdict is suspended until it is explained.
2. **Pooled floor check per stage.** Over the M ensemble pairs of a stage,
   `sum (K - 1) sigma_jk^2 / sigma_floor^2 >= chi2_{M(K - 1)}(0.025)` (for M = 30: mean ratio of variances >= 0.818). Fail: the whole
   stage's errors are suspended.
3. **The error used in the verdicts** is `max(sigma_jk, sigma_floor)`: a jackknife error that passes rule 1 but sits below the floor is
   replaced by the floor.
4. **Sample size from the floor.** For the precision target `+-0.004` per pair TV, near the uniform law (`dTV/d(Delta a) = 0.212`,
   `I^-1 = 4` on the linear block): `N_eff = (0.212^2 x 8)/0.004^2 = 2.25 x 10^4` effective samples per ensemble, summed over the
   replicas. This replaces the draft's `2.5 x 10^5` and the E1-scaled `3.5 x 10^4`, which were guesses. `t_eff` turns it into wall
   time.

## 6d. Amendment (2026-11-23, before any GPU data): debiased coefficients ("Yes, option (ii)")

**Why.** A plug-in TV between two fitted laws is biased upward by the sampling noise, about `0.023 sqrt(7400/N_eff)` for this
13-parameter family (pilot E2, `PILOT.md`). At the planned sample sizes that is as large as the small coefficients themselves (ts pairs,
rectangle partners) and adds about 0.2 to a column. The same holds for the KR/W1 bound (also a norm).

**Estimator (as in `PREREG-PILOT.md` amendment 3; `ir_condlaw.d2_cross`).**
- Per pair: the cross-replica U-statistic `D^2_U` over the K = 8 independent replicas (section 6b), unbiased for
  `D^2 = Delta theta . I_mid Delta theta`.
- Per pair coefficient: `C_D = (1/2) sqrt(max(0, D^2_U))`. This is an upper bound on the sup-form TV coefficient in the linear regime;
  conservative by the direction factor, about 1.19 for these laws.
- **W1 coefficients:** the same U-statistic with the H^-1 metric `M` in place of `I`, where `M_ij` is the H^-1 inner product of
  `p (phi_i - E phi_i)`, with the degree split of `kr_upper`. That gives `KR_D = sqrt(max(0, Delta theta . M Delta theta)_U)`, and the
  coefficient per radian is `KR_D / delta`. **Not coded yet**; it must be coded and selftested before the GPU analysis.
- **W1 move size:** `delta = 0.5 rad` (changed from 0.2), so that the per-pair KR change is resolvable. Linearity is checked on the
  s<-ss class at `delta = 0.2` (Stage A).
- **Class level:** pairs in one lattice-symmetry class have equal true coefficients. A class contributes multiplicity x
  `(1/2) sqrt(max(0, D^2_U))` for each background.
- **Plug-in TV and KR_upper** are reported alongside, for comparison only; **verdicts use `C_D` and `KR_D`**.
- **Errors and floor:** jackknife over the K items, `t_7 = 2.429`. Floor
  `Var(D^2) >= 4 Delta theta . I Sigma I Delta theta + 2 tr((I Sigma)^2)` (pilot E2, amendment 3), with the 6c rules 1-3 applied to
  `D^2`.

**Consequence for the verdicts (fit predictions, numerical).** In `C_D` units (bound, factor 1.19), the fitted action's spatial sup
column at 2.80 is about **1.05 (ss) + 0.17 (ts) + 0.38 (rectangles) = 1.6**. So with the conservative estimator the sup-form H_prop is
expected to **FAIL** at 2.80. That is consistent with "UNDECIDED or FAIL" in section 4. The decisive quantities there remain H_adj and
the **W1 column (`KR_D`, with rectangles)**.

**Sample size per class from the floor** (two ensembles of `N_eff` each; `sigma^2(D^2) = 8 D^2/N + 104/N^2`; requirement
`sigma(D^2) <= D^2_fit/3`):

| class | fit TV per pair | `C_D` per pair | column share (C_D x multiplicity) | `N_eff` needed per ensemble |
|---|---|---|---|---|
| s<-ss (12) | 0.0735 | 0.0875 | 1.05 | 2.7 x 10^3 |
| ts (6 for spatial z) | 0.0232 | 0.0276 | 0.17 | 2.7 x 10^4 |
| rectangle (90) | about 0.0036 | 0.0042 | 0.38 | **1.2 x 10^6** |

The rectangle class is the expensive part (`D^2` per pair 7 x 10^-5, in the noise-dominated regime). Rule: classes whose fit-predicted
column share is below 0.05 are measured at the ts sample size and reported as **upper limits**:
`(1/2) sqrt(D^2_U + t_7 sigma)` x multiplicity, added to the column. The rectangle class gets its own `N_eff` from this table; its cost
is projected separately in `TIMING.md`, and the owner decides whether to buy it.

## 6e. Amendment (2026-11-23, before any GPU data): the corrected floor (pilot amendment 4, calibrated by C1)

Everywhere 6c and 6d use a floor, the following applies:
- **Single statistics** (TV, Jbar, plug-in KR): `sigma_floor^2 = sum over the two ensembles of grad g . I^-1 Gamma I^-1 grad g / N`, with
  `Gamma` the batch-means long-run covariance of `phi(V_x(t))` (batches of 20 trajectories). This replaces the scalar `2 tau_psi` form;
  it is the multivariate version of the same influence-series correction.
- **`D^2_U`:** `Var = 4 d.I Sigma I d + (2K/(K - 1)) tr((I Sigma)^2)`, `Sigma = sum_k I_k^-1 Gamma_k I_k^-1/N_k`
  (`ir_condlaw.d2_floor4`).
- **Calibration:** C1 on exact i.i.d. samples gave spread / floor = 1.004 (null) and 0.955 (true pair).
- **Unchanged:** the 6c rules 1-3. The sample sizes of 6d (computed with `Gamma = I` and without `K/(K - 1)`) rise by at most
  `K/(K - 1) = 1.14` in the noise-dominated classes (the rectangle class: about `1.3 x 10^6`); the projection uses the corrected values.

## 7. Code (not written)

New: `constrained.py` (penalty HMC on a region of `docs/mass-gap/lattice/boundary.py`'s `Box`, the block variable and its force from c3b's
`goodblock.py`), `condlaw.py` (character fit, TV/KR by the N2 quadrature, bootstrap), `queue_condlaw_gpu.ps1`. Reused unchanged:
`docs/mass-gap/lattice/`, `c3b-refit/goodblock.py`, `c8b-decisive/tiecore.py` (2I updater).
