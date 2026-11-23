# Pilot 2: the tuning pre-step, results (PREREG-PILOT2.md), 2026-11-23

Status: **T-A USABLE (all three rules, every `kappa_c`). T-B NOT USABLE: it produced no measurement within its 30-minute cap.** No
production run, no GPU job. Per `PREREG-PILOT2.md`, T-B's outcome means a redesign before any `b = 4` / GPU step.

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
