# Redesign of the infrared measurement (c9b), 2026-11-23

Owner's instruction (relayed by the coordinator): "For the IR propagation: Please redesign in the shape that most fits the approaches to
PvsNP and GRH." Inputs: `docs/pnp/DICTIONARY.md` (sections 0-3, 7), `docs/rh-guide/grh/ATTEMPT.md` (sections 0, 4, 5), the pilot record
(`PILOT.md`, its design review). Everything below is written **before any data** of the new pre-registration (`PREREG-PILOT2.md`). Marks:
**Lean**, **paper** (derived here), **numerical** (quadrature or code checks, no samples), **classical**, **reading**.

## 0. The shape, in five rules

1. **Certify the instrument before production.** The sampler is itself a Markov operator with a spectral gap in Monte Carlo time
   (`ProofPhase/Mixing/TimeGap.lean`: geometric decay of time correlations iff no spectral mass above `e^{-m}`). A cheap tuning pre-step
   measures that gap (step size, acceptance, `tau_int`, seconds per trajectory). The production length and budget are **computed from it**,
   never fixed beforehand. If the pre-step shows no usable gap, the setting is redesigned before any production.
2. **Precondition the sampler** so the gap does not close under the constraint (section 2).
3. **One-sided decisions** (Landau/Stepanov): the decisive column is read as a certificate. PASS iff the upper confidence bound is `< 1`;
   FAIL iff the lower bound is `> 1`; otherwise UNDECIDED. Confidence level by rule (section 4).
4. **No-loss estimators near the threshold** (the GRH lesson: when the margin collapses, positivity has to come out as an exact identity,
   not as an inequality with losses). Every small coefficient enters the column through an **unbiased** estimator of its square (`D^2_U`,
   `KR_D`), never as a plug-in TV, which is biased upward by `O(sqrt(p/N))`. Each estimator's sampling distribution and floor is derived
   before it is pre-registered (section 3).
5. **The double reading.** A column below 1 at a scale certifies two things at once: the gap propagates (M1, physics) and the coarse
   system is samplable in polynomial time from that scale on (`Mixing/Glauber.lean`, `Link.lean`, algorithms). Every verdict is written
   both ways (section 5).

The design review's common cause ("a number entered a pass rule or a budget before the quantity behind it had been computed or measured
cheaply") is answered by rules 1 and 4: budgets come from the measured gap, pass rules from derived sampling distributions.

## 1. Rule 1: the tuning pre-step as the instrument's certificate

**What it measures** (`ir_constrained.py tune`; per setting and per `kappa_c`):
- the preconditioning mass (section 2);
- the step-size rule (from `eps = 0.05`, `nleap = 10`, halve `eps` and double `nleap` while the acceptance over 10 trajectories is
  below 0.6, at most 6 times);
- then `n_meas` trajectories: acceptance, seconds per trajectory, `tau_int` of the four components of `V_x` and of the action `S`.

**Reading** (paper, from TimeGap.lean). For the reversible HMC operator `P` (with momentum refresh it is reversible with respect to the
target), the autocorrelation of an observable `F` is `integral lambda^k d rho_F`. `tau_int = 1/2 + sum_k rho(k)` is finite iff `rho_F`
has no mass at 1, and the decay rate `1/tau` (roughly) bounds the gap seen by `F` from above. A measured `tau_int` of a few trajectories
for the slowest monitored observable is the instrument's gap certificate (a numerical one: measured, not proved). The action `S` is the
global observable, `V_x` the measured one.

**Usable** (pass rules in `PREREG-PILOT2.md`): acceptance >= 0.6 at `eps >= 0.0125` (at most two halvings); `tau_int(V_x)`,
`tau_int(S) <= 10` trajectories; production capacity in the stage budget >= 100 measured trajectories per replica. Otherwise: redesign
before any production.

## 2. Rule 2: the preconditioned sampler

**The failure it fixes.** Pilot P: the penalty `-kappa_c sum_y <V_y(U), w_y>` makes stiff modes in the fine links that feed the block
variables. Frequency `sqrt(kappa_c h_l)` for link `l`, with `h_l` the squared sensitivity below. With unit mass the leapfrog needs
`eps < 2/sqrt(kappa_c h_max)`, which forced `eps = 0.00625` (`PILOT.md`).

**The preconditioner** (paper; `Model.precond_mass`). The Gauss-Newton diagonal of the penalty's Hessian at the target,
`H_ll = kappa_c h_l`, with `h_l = (1/3) sum_{y constrained} |d V_y / d theta_l|^2` (average over the three Lie directions of link `l`).
For unit vectors near the target `d^2 <V, w> = -|dV|^2`, so this is the penalty's curvature. Kinetic mass per fine link `M_l = 1 + H_ll`,
constant during a run, so HMC stays exact (any fixed positive mass). Every stiff mode then has frequency at most about 1. `h_l` is
estimated once by Hutchinson probes: `h_l = (1/3) E_r |Im(J_l^T r U_l^dagger)|^2` with Gaussian `r` on the constrained coarse links (one
backward pass per probe; 16 probes). This is the blocked analogue of the pinned-link mass `1 + kappa_c` that gave acceptance 0.99 at
`eps = 0.05` in pilot E2.

**Checks** (numerical, code, no samples): mass >= 1, finite; the leapfrog with mass is reversible (6e-16, selftest). The Hutchinson `h`
agrees with the finite-difference curvature of the penalty on the sensitive links: 3.74 vs 3.66, 3.49 vs 3.60, 3.44 vs 3.27, 0.84 vs 0.82
(800 probes, 4^4, b = 2; the differences are probe noise).

**`kappa_c` and the extrapolation.** Use `kappa_c in {10, 20, 40}` with a straight-line extrapolation in `1/kappa_c`, the method E2
validated at n = 0 (`TV_inf`, `D^2_inf` recovered within errors). With three points the line's own residual is tested (chi^2, 1 dof,
p >= 0.05); if it fails, the two largest `kappa_c` are used and the result is flagged.

## 3. Rule 4: the no-loss estimators and their floors (all paper + numerical; no samples)

Notation: two independent ensembles A, B, each with K independent replicas (chains). `theta_hat` are the 13-parameter fits. `Sigma =
I_A^-1 Gamma_A I_A^-1/N_A + I_B^-1 Gamma_B I_B^-1/N_B`, where `Gamma` is the batch-means long-run covariance of `phi(V_x(t))` (`= I`
for i.i.d. data).

**3.1 `D^2_U` (sup form, TV-type).** The estimand is `D^2 = Delta theta . I_mid Delta theta`. The estimator is
`D^2_U = (1/(K(K - 1))) sum_{r != s} Delta_r . I_mid Delta_s`: unbiased, because different replicas have independent noise.
`C_D = (1/2) sqrt(max(0, D^2_U))` bounds the TV coefficient from above in the linear regime (Cauchy-Schwarz). Floor:
`Var = 4 d.I Sigma I d + (2K/(K - 1)) tr((I Sigma)^2)`. Calibrated in pilot C1 (spread / floor 1.004 null, 0.955 true; `PILOT.md`) and
used in E2 run 3 (pass).

**3.2 `KR_D` (W1 form; the decisive quantity).** First-order density change:
`delta p = p (Delta theta . (phi - E_p phi))`. The W1 bound used throughout (c4d tool (i), `kr_upper`) is the H^-1 norm with the degree
split `||g||^2 = ||g_1||^2/3 + ||g_2||^2/8 + ||rest||^2/15` (`>= KR^2` for the geodesic cost). To first order it is a quadratic form,
`||delta p||^2 = Delta theta . M Delta theta`, with `M_ij` the split H^-1 inner product of `g_i = p (phi_i - E phi_i)`
(`ir_condlaw.h1_metric`). The estimator is the same U-statistic with `M_mid` in place of `I_mid`: `Q_U`, unbiased for `Q`, and
`KR_D = sqrt(max(0, Q_U))`, with the per-radian coefficient `KR_D / delta`. Floor: the same formula with `M` in the metric slot,
`Var(Q_U) = 4 d.M Sigma M d + (2K/(K - 1)) tr((M Sigma)^2)` (`q_floor`).

Linearisation check (`krd_derive.py` / `.log`, quadrature, fitted law, block-flat background):

| move of one ss partner | exact `KR_upper` | `sqrt(d.M d)` | relative difference | TV | `C_D` |
|---|---|---|---|---|---|
| flip | 0.09590 | 0.09583 | -6.7e-4 | 0.0703 | 0.0834 |
| SO(3) 90 degrees | 0.03753 | 0.03752 | -1.3e-4 | 0.0274 | 0.0323 |
| W1 move 0.5 rad | 0.02431 | 0.02431 | -5.7e-5 | 0.0177 | 0.0209 |
| W1 move 0.2 rad | 0.00982 | 0.00982 | -9e-6 | 0.0072 | 0.0084 |

So `KR_D` estimates exactly the quantity c4d certified, with no linearisation loss at the planned move (`delta = 0.5`: 6e-5). The per-
radian coefficient there is 0.0486; c4d's sup over all conditional laws was `k_ss = 0.0544`. Still to do before the production
pre-registration: the calibration of `Q_U`'s floor on exact i.i.d. samples (a C1-type check), as for `D^2_U`.

**3.3 Class level, and why this is "no-loss".** Pairs in one lattice-symmetry class have equal true coefficients, so a class contributes
multiplicity x `sqrt(max(0, Q_U))/delta`. The column is a sum of such class terms. Every term is the square root of an unbiased estimate
of its square, so the column carries no `sqrt(p/N)` noise floor. The only bias left is the concavity of the square root
(`O(sigma_Q^2/Q^{3/2})`), negligible for classes whose `Q` is resolved (`sigma_Q <= Q/3`, rule 4 of 6d). Classes not resolved enter
one-sidedly through their upper bounds (section 4), never through a point value.

## 4. Rule 3: one-sided decisions

**Confidence level by rule.** One decision is taken at one-sided level `alpha = 0.02275`, the project's "2 sigma" rule. With `m`
backgrounds tested, it is Bonferroni over the backgrounds: per-background level `alpha/m`, with Student-t quantile `t_{K-1}(1 - alpha/m)`
for the jackknife errors (K = 8: 2.43 for m = 1, 3.57 for m = 5, 4.25 for m = 12).

**The certificate.** For each background `b`, `C_b = sum_classes mult_c sqrt(Q_c,b)/delta` (W1 column; the sup column likewise with
`D^2`). The bounds are built class by class, with a Bonferroni split of `alpha/m` over the `n_c` classes:
- upper bound `U_b = sum_c mult_c sqrt(max(0, Q_c + z_c s_c))/delta`;
- lower bound `L_b = sum_c mult_c sqrt(max(0, Q_c - z_c s_c))/delta`;
- `z_c = t_{K-1}(1 - alpha/(m n_c))`, `s_c = max(sigma_jk, sigma_floor)` (6c rule 3).

Monotone transforms of one-sided bounds stay one-sided bounds.

**Verdict.**
- **PASS** iff `max_b U_b < 1` (every tested background certified below 1).
- **FAIL** iff `max_b L_b > 1` (one background certified above 1 suffices).
- Otherwise **UNDECIDED**.

As in Landau's argument, only the side that is certified is claimed, and a PASS is a statement about the tested backgrounds.

## 5. Rule 5: the double reading of a verdict

For the coarse system at scale `L1` (sites = coarse links, the true conditional specification as measured):

| verdict | physics reading | algorithm reading |
|---|---|---|
| W1 column PASS (upper bound < 1) | the W1 Dobrushin condition holds at the tested backgrounds; with one smoothing step it gives the coarse one-box influence (`Adjoint2/CostCoupling.lean`, `isInfluenceBoundOn_of_costSmooth`), i.e. the gap propagates from `L1` (M1's route) | the coarse heat-bath sampler contracts in the W1 metric, so it mixes in `O(n log n)` updates from that scale on (path coupling, Bubley-Dyer / Ollivier curvature) **[classical]**; the Lean statement (`Mixing/Glauber.lean`) is the Hamming form |
| sup (TV) column PASS | Dobrushin's condition in sup form: decay under every boundary condition (Chatterjee 2.3) | `Glauber.lean` `mixing_rs` / `mixing_sweep`: `O(n log n)` single-site updates, and `TimeGap.lean` `spectral_gap_of_column`: a spectral gap `>= (1 - alpha)/n` per step **[Lean]**, given the measured coefficients as hypotheses |
| FAIL (lower bound > 1) | the condition fails at that scale for this block variable; not a statement against the gap | local dynamics on the coarse system are not certified fast from that scale; in the dictionary's terms, the boundary cost (critical slowing down) is still visible there |
| UNDECIDED | neither | neither |

Both readings hold only for the tested backgrounds and the measured block variable. They are not statements about the true law under all
boundaries; the instrument certificate (rule 1) qualifies them.

## 6. What changes in the plan

- `PREREG-PILOT2.md`: the tuning pre-step (the only thing run now), its pass rules, and the redesigned production rules, written
  before data.
- `PREREG-GPU.md` gets these rules as amendment 6f once the pre-step has run (budget from the measured gap; verdict as in section 4;
  `KR_D`).
- The GPU timing job waits for the pre-step's result and a separate OK.

## 7. Not checked / open

- `Q_U`'s floor is derived but not yet calibrated on exact samples (a C1-type check is needed before production).
- The W1 double reading (path coupling) is classical, not Lean.
- The `tau_int`-based gap certificate is numerical (measured `tau` from at most 40 trajectories is coarse).
- The preconditioner uses the target-configuration curvature; far from the target it is approximate (HMC stays exact, only efficiency
  changes).

## 8. Measured quantity -> the Lean statement it would discharge (design rule, 2026-11-23)

Owner: "We have to keep the attributes of DBs in mind when we simulate actually sound systems. What we want to get out has to be provable
in its statement of existence, otherwise we can't get anything useful out." Each quantity is listed with the exact Lean statement whose
hypothesis it would instantiate (file, name), the boundary condition under which it is measured (the DB), and the gap between what is
measured and what the statement asks. A quantity that discharges no statement is **diagnostic only**.

The general gap is the quantifier. Every influence hypothesis in Lean is a "for all": for every boundary, or for every in-support pair.
A measurement covers finitely many boundaries. So a measured number never discharges a hypothesis by itself. It is evidence for the
hypothesis's instance set, and it discharges the hypothesis only together with an argument (paper or Lean) that the tested boundaries
are the worst case or cover the required set. Where such an argument exists it is named. The pattern-conditioned form is the closest
fit, because it asks only for in-support pairs (`DisintBound.pair`, all pairs in a set of full measure), i.e. for the sampled
backgrounds' type; it still needs the "all" in the full-measure set.

| measured quantity | Lean target (file: name) | boundary condition (the DB) | measured vs required | status |
|---|---|---|---|---|
| **W1 column with the rectangle class** (`sum_c mult_c KR_D,c / delta`, one-sided upper bound) | `Certified/AdjointW.lean`: `SiteInfluenceW` (W1 influence `k i z` for the geodesic cost; column `< 1` gives `LimitDprimeW`); then `Adjoint2/CostCoupling.lean`: `CostWeights.influence` / `costDS_bound` (the comparison theorem) and, with smoothing, `CostSmoothData` -> `isInfluenceBoundOn_of_costSmooth` -> the influence slot of `OneBox/Fine.lean`: `FineOneBox` (coarse level); M1's assembly `M1/Assembly.lean`: `m1_assembly` consumes the per-scale coupling statements | the frozen fine outside of the region plus the constrained coarse data (`masks`, `R = 2`); the free target link `x` | measured: the max over the tested backgrounds of the conditional W1 response to a move of one partner; required: every boundary (`SiteInfluenceW`: every `sigma`, `s`) | evidence for the instance set; discharges nothing alone; the worst-case argument is open (`NOTE.md` 1.4: the coarse worst case at `L1` is not removed by the support restriction) |
| **sup (TV) column** (`sum_c mult_c C_D,c`, `C_D = sqrt(D^2_U)/2`) | `Mixing/Classical.lean`: `dob` (classical Dobrushin coefficient) in `mixing_rs_dobrushin` / `mixing_sweep_dobrushin`, and `Mixing/FiniteSpectral.lean`: `spectral_gap_dobrushin` (unconditional for **finite** spin spaces, commit 3c425bf); for continuous SU(2): `Mixing/Glauber.lean`: the `hcol` hypothesis of `mixing_rs`, `tv_rs_le` with `SiteDynamics.A`, and `Mixing/Link.lean`: `spectral_gap_of_column` | as above | `C_D` bounds the pair TV from above (linear regime) at the tested backgrounds; required: the sup over all boundaries (`dob` is a max over pairs differing at `z`). Classical.lean needs `[Fintype S]`, so for SU(2) it applies only to a finite discretisation (e.g. the 120-element 2I), which changes the system | evidence; the finite-S theorem is unconditional but is about a different (discretised) system |
| **`c0` / H_adj** (the centre-blind column, `C0`) | `Adjoint2/Transfer.lean`: `column_lt_one_of_mix`, `residual_budget` (pair coefficients `<= (e^{m} - 1)/2` from mixed variations) | as above, centre-symmetrised moves | the Lean asks for a bound on the **mixed variation** (a sup over values); the measurement gives TV-type coefficients at tested backgrounds | evidence for the hypothesis's size; does not instantiate `residual_budget`'s mixed-variation input |
| **`Jbar` / H_sat at block level 1** | `Saturation/Tests.lean`: `z2_background_saturation` (couplings `|J_p| <= Jbar` for every background) and c8a's `centre_area_law` route | as above, centre flips | "every background" required; tested backgrounds measured | evidence only |
| **`D^2_U`, `Q_U` per pair** (the no-loss squares) | the pair entries `A x z` / `k i z` of the rows above (through `C_D`, `KR_D`) | as above | as above | inputs to the rows above |
| **null `D^2_U`, null TV, the floors, `sigma_jk`** | none | the null pair (identical laws) | they validate the estimator | **diagnostic only** |
| **tuning pre-step: `eps`, acceptance, `tau_int`, seconds per trajectory** | `Mixing/TimeGap.lean`: `time_gap_iff`, `gap_of_geometric` speak about the spectral gap of the sampler's operator, but the measured `tau_int` is an estimate from a finite series, not a bound on the spectral measure | the constrained ensemble itself | a measured decay rate is not the "no mass above `e^{-m}`" statement | **diagnostic only** (it certifies the instrument numerically; nothing in Lean) |
| **cost per effective sample vs beta** | none | | | **diagnostic only** (budget, stop rule) |
| **T-A / T-B / T-B' results** | none | | | **diagnostic only** |

**Consequence for the plan.** Only the first two rows feed theorems, and only through a "for all" that sampling cannot discharge. The
measurement can therefore at most:
- (i) **refute** a hypothesis: one background with a certified lower bound above 1 is a counterexample to the "for all", so the
  statement cannot hold for this block variable at this scale. This is the one-sided FAIL of section 4, and it is a provable negative
  statement about the measured system: existence of a bad boundary.
- (ii) **support** it, with the tested backgrounds named.

A PASS becomes a discharge only with a worst-case argument. That argument is the open item, and it is where the mathematics has to come
from (`NOTE.md` section 2(a): the true conditional density's mixed variations, worst case over the coarse data).
