# The GPU timing job (c9b), setup: written 2026-11-23, before any GPU data. Not run.

Authorisation: the owner approved "pilot + timing" (relayed by the coordinator). The job runs only (i) after the CPU pilot
(`PREREG-PILOT.md`) has passed all its checks, and (ii) in a GPU slot assigned by the coordinator, who sequences it with the crossover
session's timing job. **One job, hard cap 30 minutes.** The full measurement (`PREREG-GPU.md`) is **not** authorised; the projection
below goes to the owner for a separate decision.

## What runs

`py ir_constrained.py timing --go --gpu ...`, started and policed by `timing_watch.ps1`:

| item | value |
|---|---|
| point | SU(2) Wilson `beta = 2.3`, good blocking `w = 2`, `b = 8` (`L sqrt(sigma) = 2.80`, the primary point) |
| lattice | fine 40^4 periodic, coarse 5^4; region radius `R = 2` (= the whole coarse torus); set by the 8 GB card (`PREREG-GPU.md` 6a) |
| background | one typical configuration: 200 heat-bath + overrelaxation sweeps (c3b's updater), `--bgseed 3000` |
| ensemble | target `x = (0,0,0,0; 1)`, no move (the `w` ensemble of class s<-ss), `kappa_c = 200`, `B = 1` chain |
| sampler | lean path (sublattice block variable, plane-by-plane plaquette gradient), HMC, the pre-registered tuning rule (10 trajectories per step, halve `eps` / double `nleap` while acceptance < 0.6, at most 6 times) |
| stop | the job stops itself at 28 minutes (`--max-wall 1680`); the watcher kills it at 30 minutes regardless |

## What is measured (and nothing else)

Seconds per trajectory (median over production), `eps` and `nleap` after tuning, acceptance, `tau_int` of the four components of `V_x`
(`ir_condlaw.tauint`, max over components), device memory (cupy pool), background time, tuning time. **No physics number** is reported
from this job: `V_x` is saved only to measure `tau_int`.

Outcomes: OK if at least 50 production trajectories were recorded with acceptance >= 0.6; otherwise the projection is reported as
"not possible at this setting", with the reason (tuning did not converge, memory, time).

## The watcher (`timing_watch.ps1`)

1. Checks the GPU first. It aborts if utilisation is above 20 % or another compute process holds memory, in addition to the coordinator's
   slot.
2. Starts the job with `Start-Process` and records its process id.
3. Every 15 s, prints the elapsed time, the job's last progress line and the estimate. The estimate is background + tuning + production
   time, updated from the measured seconds per trajectory.
4. Kills the process tree (`taskkill /T /F`) at the hard cap of 1800 s, whatever the job reports. It never waits only for a DONE marker
   (the lesson from the one-box overrun).
5. Writes everything to `timing_watch.log`. The job writes `timing_progress.jsonl` and `timing_job.npz`; the npz is saved every 10
   trajectories, so a kill loses at most 10.

## Projection (formula fixed now)

`t_eff = s_traj x 2 tau_int / B` (wall seconds per effective sample). Per ensemble, with K = 8 independent replicas
(`PREREG-GPU.md` 6b):
`T_ens = T_tune + K (T_anneal + T_therm) + N_eff x t_eff`.
- `T_tune` is as measured, once per ensemble.
- `T_anneal = 20 s_traj`, per replica, moved ensembles only.
- `T_therm = 20 s_traj` per replica.
- `N_eff` is the total over the replicas.

Per background, add `T_bg` once (it is shared by all its ensembles).

`N_eff` per ensemble (sum over replicas), **by class (`PREREG-GPU.md` 6d)**: s<-ss `2.7 x 10^3`, ts `2.7 x 10^4`, rectangle `1.2 x 10^6`
(projected separately), the others at the ts size as upper limits. (Superseded: one `N_eff = 2.25 x 10^4`, from 6c rule 4 for `+-0.004` per pair TV.) The draft's `2.5 x 10^5` is also reported, as a conservative bound. The E1-scaled `3.5 x 10^4` is withdrawn: it was
scaled from a spread, not derived.

| stage | content (`PREREG-GPU.md` sections 3, 6) | ensembles | backgrounds |
|---|---|---|---|
| A | 4 typical + block-flat; plaquette classes (3) x 4 values x 2 `kappa_c`; rectangle classes (6) x 4 values x 1 `kappa_c` | 120 + 120 = 240 | 5 |
| B | rest of the primary: the other 7 backgrounds, the third `kappa_c`, the 2 tail classes | 720 - 240 = 480 | 7 more |
| C | controls U(1) `beta = 1.1` and 2I `beta = 6` | 48 | 4 |
| D | secondary point 72^4 | does not fit this card (6a): not projected | |

Stage C needs U(1) and 2I code paths in `ir_constrained.py`, which do not exist yet; its projection assumes the SU(2) cost per
trajectory and is marked as such. Reported per stage, in GPU-hours, for (a) and (b).
