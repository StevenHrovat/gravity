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
