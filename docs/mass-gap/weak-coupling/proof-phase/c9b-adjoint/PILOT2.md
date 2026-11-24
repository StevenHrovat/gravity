# Pilot 2: the tuning pre-step, results (PREREG-PILOT2.md), 2026-11-23

Status: **T-A USABLE. T-B NOT USABLE (no data within its cap). T-B' (12^4, `b = 4`, `beta = 2.3`, `kappa_c = 10`) USABLE, with
tuned `eps = 0.0125` exactly as the coherent-mode model predicted.** No production run, no GPU job. Per `PREREG-PILOT2.md`, T-B's outcome means a redesign before any `b = 4` / GPU step.

## T-A: SU(2) Wilson `beta = 0.5`, 8^4, `b = 2`, preconditioned (`pilot2_TA.json` / `.log`; 4 min CPU)

| `kappa_c` | tuning (`eps`: acceptance) | tuned `eps`, `nleap` | acceptance | s / trajectory | `tau_int(V_x)` | `tau_int(S)` | mass max |
|---|---|---|---|---|---|---|---|
| 10 | 0.05: 0.0; 0.025: 0.9 | 0.025, 20 | 0.93 | 1.02 | 0.74 | 0.81 | 245 |
| 20 | 0.05: 0.0; 0.025: 0.9 | 0.025, 20 | 1.00 | 0.92 | 2.92 | 2.00 | 420 |
| 40 | 0.05: 0.0; 0.025: 0.1; 0.0125: 1.0 | 0.0125, 40 | 0.98 | 1.87 | 3.30 | 0.61 | 880 |

Background: 18 s. Rules:
1. Acceptance >= 0.6 at `eps >= 0.0125`: pass for all three (`kappa_c = 40` at the limit, two halvings).
2. `tau_int <= 10` and below `n_meas/4 = 10`: pass (max 3.3).
3. Capacity: `s_traj <= (1800 - overhead)/100` (about 17 s): pass (at most 1.9 s, so about 900 trajectories in a 30-minute stage).

**USABLE.**

**Prediction miss.** "Every `kappa_c` at `eps >= 0.025`" failed at `kappa_c = 40` (0.0125). Even with the preconditioner the
acceptance at `eps = 0.05` is 0. The Hutchinson estimate with 16 probes is noisy, and the Wilson part and the off-diagonal penalty
curvature are not preconditioned, so some stiffness remains. Compared with pilot P (unpreconditioned, `kappa_c = 100`,
`eps = 0.00625`, 0 measured trajectories), the gain is a factor 2-4 in step size and a working instrument.

## T-B: SU(2) Wilson `beta = 2.3`, 16^4, `b = 4`, preconditioned (`pilot2_TB.log`, empty; no JSON; 30 min CPU)

The run hit the hard cap (`timeout 1800`, exit 124) before completing its first `kappa_c` (10). `tune` writes a result only after
each `kappa_c`, so nothing was recorded: **no measurement**. Where the time went cannot be read off; this is an instrumentation gap.
Estimate (reading, not measured):
- background (CPU heat bath, 100 sweeps at 16^4): about 5 min (T-A's 18 s x 16);
- one trajectory at `nleap = 10`: about 8 s (lean force 0.73 s, plumbing);
- tuning blocks of 10 trajectories: 80 s, 160 s, 320 s, 640 s at `nleap` 10, 20, 40, 80.

So 25 minutes is consistent with **four or more halvings** at `beta = 2.3`, `b = 4`, i.e. `eps <= 0.00625`. That would fail rule 1.

**NOT USABLE** (no measurement within the cap; rule 3 at best unverified).

## What this says for the GPU step (reading)

At the GPU's target (`b = 8`, `beta = 2.3`) the stiffness is expected to be at least as large as at T-B. The timing job as designed would
spend its 30 minutes tuning. Before any GPU step, two things (redesign; nothing applied, each needs an OK):
1. **Instrumentation:** `tune` writes a progress line per tuning block and saves after each block, with a self-stop that saves, so a
   capped run still reports how far it got.
2. **The sampler at weak coupling:** the remaining stiffness comes from the Wilson term at `beta = 2.3` and from the off-diagonal penalty
   curvature. Options:
   - (a) more Hutchinson probes (64) and a diagonal Wilson-term mass (the plaquette curvature, `beta` x number of plaquettes per link);
   - (b) a Fourier-accelerated or multiscale kinetic term;
   - (c) a cheaper diagnostic first: T-B again at 12^4, `b = 4`, `kappa_c = 10`, which measures the tuned `eps` there in a few minutes.

   Recommended order: (1), then (c), then decide between (a) and (b) from the measured `eps`.

## Options for the sampler at weak coupling (design choice; the owner decides after T-B')

**What limits the step (derived; `PREREG-PILOT2.md` addition).** After the diagonal preconditioner, each constrained block variable
leaves one coherent stiff mode: the fine links that feed it move together. Its squared frequency is
`n_eff = sum_l kappa_c h_l/(1 + kappa_c h_l)`: 12 (`b = 2`), 47 (`b = 4`), 306 (`b = 8`) at `kappa_c = 10`. A diagonal mass cannot
remove a coherent direction. The Wilson term's own curvature at `beta = 2.3` is of order `beta x 6 x <t>`, about 7 (paper, rough). It
is comparable at `b = 2` and small against 306 at `b = 8`.

**Option A: more probes plus a Wilson-term diagonal mass.**
- What: 64 instead of 16 Hutchinson probes, plus a diagonal mass `beta x (number of plaquettes per link) x <t_P>` from the Wilson
  curvature.
- Cost: about 2 hours of code. Per-step cost unchanged; the mass pass takes four times longer, once per run.
- Expected gain: removes the probe noise and the Wilson stiffness, but not the coherent mode. At `b = 8` the step stays about
  `0.025 sqrt(12.3/306) = 0.005`. A unit-length trajectory then needs about 200 leapfrog steps, against about 20 for an unconstrained
  pure-gauge HMC at `beta = 2.3`.
- Helps when the measured step sits well below the coherent-mode prediction (some other stiffness dominates).

**Option B: a low-rank-exact kinetic term.**
- What: `M = 1 + kappa_c J_0^T J_0`, with `J_0` the blocking Jacobian at the target configuration (fixed during a run, so HMC stays
  exact).
  - Momentum draw (exact, cheap): `p = xi + sqrt(kappa_c) J_0^T eta`, with `xi`, `eta` standard normal on the fine and coarse spaces.
    One backward pass.
  - Velocity `M^-1 p` by Woodbury: `M^-1 = 1 - kappa_c J_0^T (1 + kappa_c J_0 J_0^T)^-1 J_0`, a linear solve in the coarse space
    (3 x number of coarse links unknowns). Conjugate gradients with a block-diagonal preconditioner (the 3x3 blocks of `J_0 J_0^T`, one
    per coarse link, computed once). Each iteration is one forward plus one backward pass of the blocking.
- Cost:
  - Code: about one day (forward-mode derivative of the blocking, the solver, selftests: exactness, reversibility, `M^-1 M = 1`).
  - Per leapfrog step: `1 + 2 n_CG c_blk` force-equivalents, with `c_blk` (one blocking pass relative to a force) about 0.3 (lean
    path, plumbing) and `n_CG` the CG iterations.
  - With the block preconditioner the remaining condition number comes from overlaps between neighbouring block variables; estimate
    `n_CG = 5-10`, i.e. 4-7 times the per-step cost.
- Expected gain: removes the coherent modes, so the step goes back towards the unconstrained value (0.05-0.1) at every `b`. At `b = 8`:
  10-20 times fewer steps at 4-7 times the cost per step, a net factor of about 2-5. It is the only option that scales to larger `b`.
- Helps when the measured step follows the coherent-mode prediction.

**What decides.** T-B''s tuned step against the prediction 0.0125:
- within one halving: the coherent-mode model holds, and B is needed for `b = 8`; A alone would leave about 200 steps per trajectory;
- `eps <= 0.003`: something else dominates; do A first, then re-measure.

A second, data-free check before building B: the CG iteration count, from the spectrum of the block-preconditioned `J_0 J_0^T` on one
configuration at `b = 4` (one assembly, about 40 minutes CPU). It turns B's cost estimate into a number.

## Cost scaling with beta (the owner's caution: weak coupling may become much harder than expected)

**Model (paper; the exponents from the literature are marked "recalled").** At fixed physical precision and a fixed physical block
`L1` (`L1 sqrt(sigma) = 2.80`), the cost of one measurement is
`C(beta) ~ (L/a)^4 x S(a) x tau_int(a) x 1/margin^2`:
- `(L/a)^4`: the fine region, radius 2 coarse cells, so side `5b` with `b = L1/a`.
- `S(a)`: leapfrog steps per unit trajectory.
- `tau_int ~ xi^z ~ a^-z`: critical slowing down in Monte Carlo time.
- The margin `1 - column` is a physical quantity at fixed `L1 sqrt(sigma)`, so it does not scale with `a`.

Inputs: `a sqrt(sigma)` = 0.350, 0.258, 0.182 at `beta` = 2.3, 2.4, 2.5 (c3b); `n_eff ~ b^2.6` (12, 47, 306 at b = 2, 4, 8, exact `h`).

| | Option A (diagonal mass) | Option B (low-rank-exact kinetic term) |
|---|---|---|
| `S(a)` | `~ sqrt(n_eff) ~ b^1.3 ~ a^-1.3` (the coherent mode remains) | about constant; per step `x(1 + 2 n_CG c_blk)`, with `n_CG` constant to `~log b` (block-preconditioned overlaps; estimate) |
| `z` | recalled: HMC on local observables `z` about 1-2 (Kennedy-Pendleton: `z = 1` for the free field with trajectory length `~ xi`; about 2 at fixed trajectory length). A remaining stiff mode forces short steps at fixed length, so the pessimistic `z = 2` applies | recalled: the same HMC values for the unconstrained modes (`z` about 1-2); B removes the constraint's stiffness, not the critical slowing down of the physics modes. Fourier acceleration gives `z = 0` only for free fields (Davies et al. 1988, recalled); for a gauge theory it needs gauge fixing and is not planned |
| topology | recalled: topological charge freezes as `a -> 0` (`tau_int(Q)` grows like `a^-5` or faster, Schaefer-Sommer-Virotta 2011); at `beta <= 2.5` in SU(2) it is not frozen, but it is the first thing that would break the projection | same |
| cost ratio `beta 2.4 / 2.3` | 7-9 | 5-8 |
| cost ratio `beta 2.5 / 2.3` | 60-120 | 26-80 |

**Memory (8 GB card, hard limit).** The fine region side is `5b`: 40 at `beta = 2.3` (`b = 8`; at the card's limit with the lean path),
54 at 2.4 and 77 at 2.5. So on this card **only `beta = 2.3` at `b = 8` fits**. Weaker coupling at fixed physical `L1` needs a larger GPU
or a region-only implementation (no full periodic lattice).

**What T-B' (12^4, `b = 4`, `beta = 2.3`) measures towards this.** One point of `S` (the tuned `eps` and `nleap` at `b = 4`; with T-A's
`b = 2` it tests the `b^1.3` law, although T-A is at another `beta`) and one point of `tau_int` at `beta = 2.3`. **It does not measure `z`.**
`z` needs two `beta` values at a matched physical point. The nearest matched pair in c3b's table is `beta = 2.3, b = 4`
(`L sqrt(sigma) = 1.40`) against `beta = 2.5, b = 8` (1.46). The second point needs 24^4 at `b = 8` (about 4 s per force on the CPU),
which is GPU-sized, so it belongs to the GPU timing stage and needs a separate OK.

**Stop rule (also added to `PREREG-PILOT2.md`).** When the cost per effective sample, `s_traj x 2 tau_int`, has been measured at two
`beta` values, the measured ratio is compared with the projected one above, for the option in use and the pessimistic `z = 2`. If the
measured ratio exceeds **3 times** the projection, stop and report before any larger run.

## T-B': SU(2) Wilson `beta = 2.3`, 12^4, `b = 4`, `kappa_c = 10`, preconditioned (`pilot2_TBp.json`, progress `.jsonl`; 12 min CPU)

| tuning block (`eps`, `nleap`) | acceptance | s / trajectory |
|---|---|---|
| 0.05, 10 | 0.0 | 3.6 |
| 0.025, 20 | 0.4 | 6.0 |
| **0.0125, 40** | **0.8** | 12.2 |

Measurement (30 trajectories at `eps = 0.0125`, `nleap = 40`): acceptance 0.87, 11.6 s per trajectory, `tau_int(V_x)` 1.8,
`tau_int(S)` 1.3 (both resolved, below `n_meas/4 = 7.5`). Background 139 s, mass 2.4 s (max 86).

Rules:
1. pass (`eps = 0.0125`, two halvings);
2. pass;
3. pass narrowly: `(1800 - 139 - 2 - 216 s tuning)/100 = 14.4 s >= 11.6 s`.

**USABLE.**

**Diagnostic reading (pre-registered).** The prediction from `n_eff` was `0.025 sqrt(12.3/46.8) = 0.0128`; measured: 0.0125. **The
coherent-mode model holds**: after the diagonal preconditioner, the step is set by the fine links that feed one block variable moving
together. By the decision rule written before the data, **option B (the low-rank-exact kinetic term) is needed for `b = 8`**. With A
alone the step there would be about 0.005 (about 100-200 steps per unit trajectory).

**Cost per effective sample at this point** (CPU): `s_traj x 2 tau = 11.6 x 2 x 1.8 = about 42 s`. This is the first point for the
cost-scaling stop rule (`beta = 2.3`, `b = 4`, `L sqrt(sigma) = 1.40`). The matched second point (`beta = 2.5`, `b = 8`) is GPU-sized.

## Option B built and measured: the CG count (data-free; `cgcount_b4.json`, `cgcount_b8.json`; owner: "Yes, build B")

**Built** (`ir_lowrank.py`, new):
- `M = 1 + kappa_c J0^T J0`, exact momenta `xi + sqrt(kappa_c) J0^T eta`;
- velocity by Woodbury and a coarse conjugate-gradient solve (tolerance 1e-10), with a tangent-only Jacobi-block preconditioner;
- `J0 x` by exact tangent propagation through the strided blocking; `J0^T r` by the tape.

**Selftests** (`py ir_lowrank.py selftest`):

| check | result |
|---|---|
| `J x` vs finite differences | 6e-11 |
| dot test `<r, J x> = <J^T r, x>` | to 12 digits |
| `M^-1 M = 1` | 5e-11 |
| momentum covariance (mean `p.M^-1 p` against the dimension) | z = -0.58 |
| leapfrog reversibility | 1e-14 |
| `dH` ratio per halving of `eps` (0.02 -> 0.01 -> 0.005) | 3.7, 4.0 |

`eps = 0.04` is pre-asymptotic on the hot test configuration. The first selftest version used the pair 0.04/0.02 and failed on that;
the pair was changed to 0.02/0.01.

**A bug found by the count, and fixed.** The first preconditioner scaled all four quaternion components, including the radial direction
outside the range of `J`. It made CG slower than plain CG (468 against 109 iterations; `cgcount_b4_run1_badprec.*`, kept).

**The count** (one heat-bath background, 20 sweeps, `beta = 2.3`, `kappa_c = 10`; right-hand sides `b = J p` from the momentum draw):

| `b` | lattice | CG iterations (preconditioned / plain) | one `J` and one `J^T` against one force | cost per leapfrog step (forces) |
|---|---|---|---|---|
| 4 | 12^4 | 66 / 91 | 0.44 | **about 60** |
| 8 | 24^4 | 93 / 126 | 0.33 | **about 63** |

The design estimate (`n_CG` 5-10, 4-7 times per step) was wrong by a factor of 10. The block variables overlap strongly (smearing
`w = 2`), so `1 + kappa_c J J^T` is ill-conditioned beyond what a per-link block preconditioner reaches. Each CG iteration costs a full
forward and backward blocking pass.

**Net against the diagonal sampler (A).** B's gain is the step count: `eps` about 0.05 against A's 0.0125 at `b = 4` (measured) and
about 0.005 at `b = 8` (predicted), i.e. 4 times and about 10 times fewer steps. B is therefore about **15 times worse at `b = 4`** and
about **6 times worse at `b = 8`**. Its relative cost improves with `b`, with a crossover far beyond `b = 8`.

**Conclusion: option B as designed is not viable.** The diagonal preconditioner (A, already in `ir_constrained.py`) remains the sampler.
At `b = 8` it is expected at `eps` about 0.005, about 100 steps per half-unit trajectory; on the GPU the force is cheap, and the timing
job measures what that costs.

Not run, and why: the T-B' repeat with B. Its pre-registerable expectation is a capacity failure: about `10 x 60 x 0.15 s = 90 s` per
trajectory at 12^4, so 30 measured trajectories would take about 45 minutes against a 30-minute cap. The agreement run is also not run:
B's exactness is already shown by the selftests, and if B is dropped the run has no purpose. Both are left for the owner's decision.

Directions if a non-diagonal kinetic term is still wanted (none started):
- (i) assemble `J J^T` once and use a direct (Cholesky) solve; the coarse dimension is small, but assembly costs one forward-and-backward
  pair per coarse component (about 10^4 at coarse 5^4); feasible on the GPU, not on this CPU;
- (ii) a deflation or two-level preconditioner on the smooth overlap modes;
- (iii) less smearing in the block variable (smaller `w`). That reduces the overlaps but changes the measured object; it would need c3b's
  content check redone.
