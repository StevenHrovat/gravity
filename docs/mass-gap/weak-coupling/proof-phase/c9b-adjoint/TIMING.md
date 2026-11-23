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

## Setup as run (2026-11-23, written before the job; owner: "Yes, time it"; supersedes the table above where they differ)

- **Sampler A:** the diagonal preconditioning mass `1 + kappa_c h_l` (16 Hutchinson probes), `kappa_c = 10` (pilot-validated: T-A,
  T-B'), not 200.
- **Point:** SU(2) Wilson `beta = 2.3`, fine 40^4, `b = 8` (coarse 5^4), region radius 2 (the whole coarse torus), `B = 1`. Background:
  200 heat-bath plus overrelaxation sweeps (c3b's GPU updater).
- **Code changes since the pilot (plumbing; selftest passes):**
  - the sublattice index arrays are cached;
  - the quaternion product uses c3b's fused CUDA kernel (equal to the array expression to 5e-16);
  - GPU force cost: 0.14 s at 8^4, 0.33 s at 24^4 (plumbing timings, 8^4 and 24^4).
- **Tuning start (rule, set now):** `eps = 0.0125`, `nleap = 40` (trajectory length 0.5). This is T-B''s measured value at `b = 4`;
  `b = 8` can only be stiffer, and starting at 0.05 would spend the whole cap tuning (blocks at `nleap` 10-80 cost about 34-85 min at
  40^4). 5 trajectories per tuning block; halve while acceptance < 0.6, at most 4 times.
- **Then production** until the job stops itself at 28 min (`--max-wall 1680`); the watcher kills at 1800 s.

**Expectation (fixed now):**
- force at 40^4: **0.6-1.5 s** (extrapolated from the plumbing timings);
- tuned `eps`: **0.00625** (the coherent-mode prediction `0.0125 sqrt(46.8/306) = 0.0049` rounds to the rule's 0.00625 if the
  acceptance there is >= 0.6, else 0.003125);
- seconds per trajectory = `nleap x s_force x 1.1`: about 50-130 s at `nleap = 80`;
- background about 1.5 min, mass and tuning 5-20 min;
- hence only about **5-20 production trajectories**, so **`tau_int` will probably not be resolved** (it needs at least `4 tau`
  trajectories at the measured `tau`). By `PREREG-PILOT2.md`'s stop rule an unresolved `tau_int` stops any larger run. The projection
  then uses T-B''s `tau_int` (1.8, `b = 4`) with a transfer factor, marked as such.

**Measured:** `s_force`, the tuned `eps` and `nleap`, acceptance, seconds per trajectory, `tau_int` of `V_x` and of `S` if resolved,
device memory, GPU clocks and temperature (watcher log, rule 4 of `c9a-crossover/w2/PROJECTION.md` section 8). No physics number.

**Projection after the job:** `c9a-crossover/w2/PROJECTION.md` section 8's rule:
- central value x 1.33, band x [0.9, 1.9] (the content-spread floor);
- beta transfer factor 1.0 +- 0.3 for any other `beta`;
- +25 % drift allowance for long runs;
- the cost-growth stop rule of `PREREG-PILOT2.md`.

## Result of the timing job (2026-11-23 08:12-08:42 UTC; `timing_watch.log`, `timing_progress.jsonl`; killed at the hard cap)

The watcher killed the job at 1801 s, as designed (exit at 1804 s). No production trajectory was recorded; everything below is timing.

| quantity | expected (before the run) | measured |
|---|---|---|
| background (200 sweeps, GPU heat bath) | about 1.5 min | 95 s |
| preconditioning mass (16 probes) | (in 5-20 min of set-up) | 87 s |
| **one force at 40^4, `b = 8`** | **0.6-1.5 s** | **9.85 s** (7-16 times the expectation) |
| seconds per trajectory at `nleap = 40` | (50-130 s at `nleap = 80`) | 320-370 s (= 40 forces, consistent) |
| tuning at `eps = 0.0125` | acceptance < 0.6, then 0.00625 | 4 trajectories, **acceptance 0, `dH` = 40-96**; the cap came before the first halving |
| device memory | (below 8 GB) | **7.9 GB of 8 GB** from the second minute on |
| GPU clock and temperature (rule 4) | | 1815 MHz throughout, 56-62 C: no thermal throttling |

**Reading.**
- (i) The force is 7-16 times slower than the plumbing extrapolation. The device memory was full (7.9 of 8 GB) for the whole run, so
  WDDM's spill of device allocations into shared system memory is the likely cause (hypothesis, not measured). The extrapolation from
  24^4, where memory was low, did not see it.
- (ii) `dH` = 40-96 at `eps = 0.0125` is much worse than the coherent-mode model's estimate (0.0049 would be needed). Since
  `dH ~ eps^2`, about `eps ~ 0.0125/sqrt(50) ~ 0.002` is needed, i.e. `nleap` about 250-300 per trajectory. This is an extrapolation
  from 4 trajectories, not a tuning result.
- (iii) `tau_int` is not measured. By `PREREG-PILOT2.md`'s stop rule (an unresolved `tau_int` stops any larger run), the decisive run
  stops here.

## Projection (section 8's rule; numbers from this job; all marked as extrapolations)

- per trajectory at `eps` about 0.002: `nleap` about 280 x 9.85 s = **about 2800 s**;
- `tau_int` not measured: T-B''s 1.8 (`b = 4`) is used, marked, so `t_eff = 2 x 1.8 x 2800` = **about 1.0 x 10^4 s** per effective
  sample;
- per ensemble (N_eff from 6d/6e): ss class `2.7 x 10^3 x 10^4 s` = **about 7.5 x 10^3 GPU-hours**; ts class about 7.5 x 10^4 h;
  rectangle class about 3.6 x 10^6 h;
- Stage A (5 backgrounds; plaquette classes x 4 moves x 3 `kappa_c`; rectangles x 4 moves x 1): about **10^7-10^8 GPU-hours**
  (central x 1.33 x 1.25 drift; band x [0.9, 1.9]).
- Even with the **expected** force (1 s) and step (0.00625, `nleap` 80): `t_eff` about 290 s, ss ensemble about 220 h, Stage A about
  10^5-10^6 h.

**Verdict: the decisive constrained-sampling run is infeasible on this hardware by 5-8 orders of magnitude**, already at
`beta = 2.3`, `b = 8`, before any weaker coupling. By the stop rules (unresolved `tau_int`; cost far above the projection) no larger
run is proposed in this form.

**What could change the order of magnitude (for the owner; none done):**
1. **Memory and precision:** float32 halves the memory and may remove the spill (the force could return to about 1 s); a region-only
   lattice instead of the full periodic 40^4.
2. **A smaller region:** radius 1 (24^4 fine at `b = 8`): force 0.33 s, about 30 times cheaper. But only the nearest coarse neighbours
   are then constrained, which changes the conditional law measured.
3. **Fewer ensembles:** measure only the decisive W1 classes (ss and rectangles) at the 5 Stage-A backgrounds, one `kappa_c` plus the
   extrapolation pair.
4. **A different estimator:** the single-link conditional law from unconstrained ensembles by reweighting or pseudo-likelihood. That is
   what the fits did, with the closure-residual and average-not-sup problems this design was built to avoid.

Combining 1-3 might buy 10^2-10^3, not 10^5-10^8. **The honest conclusion is that the worst-case single-site coefficients of the true
law at `L1` are not measurable to the planned precision by direct constrained sampling on this hardware.** This matches `REDESIGN.md`
section 8: the measurement could at most support or refute, and even that is out of reach at the planned precision.
