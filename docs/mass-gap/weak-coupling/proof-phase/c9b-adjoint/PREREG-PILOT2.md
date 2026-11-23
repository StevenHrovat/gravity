# Pre-registration: pilot 2, the tuning pre-step (c9b), 2026-11-23

Status: written before any pre-step data. Design: `REDESIGN.md`. Approval: the owner's "For the IR propagation: Please redesign in the
shape that most fits the approaches to PvsNP and GRH" (relayed by the coordinator), with the instruction to run **only the CPU tuning
pre-step** now. No production runs, no GPU. CPU, one process at a time, each setting capped at 30 minutes (`timeout 1800`, internal
`--max-wall 1500`). Commands: `run_pilot2.sh`.

## The pre-step (instrument certificate; `ir_constrained.py tune`)

Per setting and per `kappa_c`, in this order:
1. **Background:** one configuration from c3b's heat bath plus overrelaxation (`npre` sweeps), shared by all `kappa_c` of the setting.
2. **Constraint:** every coarse link of the region except the target link `x = (0,0,0,0; 1)` is constrained to its current value
   (no move).
3. **Preconditioning mass:** `1 + kappa_c h_l` with 16 Hutchinson probes (`REDESIGN.md` section 2).
4. **Step-size rule:** start at `eps = 0.05`, `nleap = 10`; while the acceptance over 10 trajectories is below 0.6, halve `eps` and
   double `nleap` (at most 6 times).
5. **Measurement:** `n_meas` trajectories at the tuned step; record the acceptance, the median seconds per trajectory, `tau_int` (max
   over the four components of `V_x`) and `tau_int(S)`.

| setting | point | lattice, block | `kappa_c` | `n_meas` | why |
|---|---|---|---|---|---|
| T-A | SU(2) Wilson `beta = 0.5` | 8^4, `b = 2` (coarse 4^4), `npre` 100 | 10, 20, 40 | 40 | pilot P's setting, where the unpreconditioned sampler had no usable gap |
| T-B | SU(2) Wilson `beta = 2.3` | 16^4, `b = 4` (coarse 4^4), `npre` 100 | 10, 40 | 30 | the `b = 4` step towards the GPU's `b = 8` at the same `beta` (design review, point 4) |

## Predictions (fixed now)

- **T-A:** with the preconditioner, every `kappa_c` reaches acceptance >= 0.6 at `eps >= 0.025` (at most one halving). Without it, P
  needed `eps = 0.00625` at `kappa_c = 100`.
- **T-B:** acceptance >= 0.6 at `eps >= 0.0125` for both `kappa_c`. This is less certain: `beta = 2.3` adds the Wilson force's own
  stiffness.
- `tau_int(V_x)` and `tau_int(S)` <= 10 trajectories everywhere they are measured. Seconds per trajectory at the tuned step: T-A about
  0.5-2 s, T-B about 8-30 s (CPU; lean force 0.04 s at 8^4 and 0.73 s at 16^4, b = 4, plumbing timings).

## Pass rules ("usable gap"), per setting and `kappa_c`

1. Acceptance >= 0.6 reached at `eps >= 0.0125` (at most two halvings).
2. `tau_int(V_x) <= 10` and `tau_int(S) <= 10` trajectories, with `tau_int` measured, i.e. below `n_meas/4`; otherwise "not resolved",
   which counts as a failure.
3. **Production capacity:** with the measured seconds per trajectory, a 30-minute CPU stage (T-A) or the GPU timing budget (T-B; GPU
   speed-up unknown, so judged on CPU at 30 minutes as a lower bound) holds >= 100 measured trajectories after tuning, i.e.
   `s_traj <= (1800 s - t_overhead)/100`.

**Verdict per setting:** USABLE if rules 1-3 hold for every `kappa_c` of the setting. NOT USABLE otherwise: redesign before any production
(`REDESIGN.md` rule 1). The pre-step reports numbers only for planning. No physics number is read from it (`V_x` is used only for
`tau_int`).

## What follows (not run now; each needs a separate OK)

- **If T-A is USABLE:** the C1-type calibration of `Q_U` (W1, `KR_D`); then pilot P' (P's checks with the preconditioned sampler,
  `kappa_c` 10/20/40, the `1/kappa_c` extrapolation, `D^2_U` and `KR_D` with the floors, production lengths computed from T-A).
- **If T-B is USABLE:** the GPU timing job at `b = 8` with the preconditioner, its budget computed from the measured gap.
- **If NOT USABLE:** a written redesign, no runs.

## Addition (2026-11-23, after T-A and T-B, before any T-B' data): T-B' and the progress instrumentation

Approved by the coordinator within the owner's CPU pre-step approval. T-B produced no data (the 30-minute cap, results only per
`kappa_c`). `tune` now writes a progress line per tuning block and per 10 measured trajectories (`<out>.progress.jsonl`), rewrites the
result JSON after every block, and stops itself, saving, at `--max-wall` (toy check passed; the selftest still passes).

**T-B':** SU(2) Wilson `beta = 2.3`, 12^4, `b = 4` (coarse 3^4), `kappa_c = 10`, preconditioned, `npre` 100, `n_meas` 30, seeds 43 /
4002, 30-minute cap (`--max-wall 1500`, `timeout 1800`).

**Expectation (derived now, `REDESIGN.md` section 2 extended; numerical, no samples).** After diagonal preconditioning, one constrained
block variable leaves a coherent stiff mode with squared frequency `n_eff = sum_l kappa_c h_l/(1 + kappa_c h_l)`. This counts the fine
links that feed it; diagonal masses cannot remove the coherent direction. Exact `h` on random configurations, `kappa_c = 10`:

| block | fine links feeding one `V_y` | `n_eff` |
|---|---|---|
| `b = 2` | 18 | 12.3 |
| `b = 4` | 218 | 46.8 |
| `b = 8` | 2178 | 306 |

If this mode limits the step, `eps` scales as `1/sqrt(n_eff)`. From T-A (`b = 2`, `kappa_c = 10`: `eps = 0.025`) the prediction for
`b = 4` is `0.025 sqrt(12.3/46.8) = 0.0128`, i.e. **tuned `eps = 0.0125`**. For `b = 8` it is about 0.005.

**Rules:** as for T-A (acceptance >= 0.6 at `eps >= 0.0125`; `tau_int <= 10` and below `n_meas/4`; at least 100 measured trajectories
in a 30-minute budget).

**Diagnostic reading (decides the sampler option, `PILOT2.md` section "Options"):**
- tuned `eps` within one halving of 0.0125 (`0.00625 <= eps <= 0.025`): the coherent-mode model holds;
- `eps <= 0.003`: some other stiffness dominates.

## Stop rule for cost growth (2026-11-23, at the owner's caution; before any data at a second beta)

Owner: "We have to be very careful about simulating a weak coupling. The closer we get to reality, the more intensive it is to be precise,
so when we have to compute large interactions, it might suddenly be much harder than expected."

Whenever the cost per effective sample, `s_traj x 2 tau_int` (`tau_int` = the max over the monitored observables), has been measured at
two `beta` values at a matched physical point, the measured ratio is compared with the projected ratio of `PILOT2.md` ("Cost scaling
with beta": the option in use, `z = 2`, the measured `S` exponent where available). **If the measured ratio exceeds 3 times the
projection, stop and report before any larger run.** Separately, if any monitored `tau_int` is not resolved (above `n_meas/4`), that
also stops before any larger run.
