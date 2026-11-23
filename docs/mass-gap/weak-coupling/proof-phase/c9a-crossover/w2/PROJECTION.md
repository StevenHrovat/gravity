# W2 projection from the one timed job (c9a-crossover, 2026-11-23)

**Status:** one timed GPU job run (owner's scope, via the coordinator). The full run is **not** authorised; it needs the owner's
separate OK on this projection. Nothing committed.

## 1. The timed job (`runs/timing_b3.5.json`, `runs/timing_b3.5.log`)

* Started 03:11:59 on an idle GPU (3 %), watcher `time_job.ps1` (checkpoint every 30 s, soft cap 2400 s inside the job,
  hard kill at 2640 s). Ended cleanly at the soft cap after **2465 s (41 min)**; no hard kill.
* Configuration: β = 3.5 (the slower end by the pilot: `T(3.5) = 600`, `T(2.3) = 300`), `ℓ = 6`, κ = 16, A3 (twisted block
  field), greedy pool of 8 outsides, **one full launch batch: 3 jobs, 480 coupled pairs** (32 shell links + 8 block variables,
  `θ = π/2, π`, 2 starts, per job).
* Sanity: box plaquette 0.742 (equilibrium 0.768; the twisted block field forces a sheet through the box, so a lower value is
  expected); coupled-pair disagreement at the end 4630 of 5184 box links (89 %, saturated, as in the pilot).

| stage | measured | per sweep |
|---|---|---|
| geometry (index tables) | 3.4 s | |
| greedy pool: 3 × 64 pairs, 60 sweeps (`T/10`) | 540 s | **9.0 s** |
| build of the main batch + heating of start 1 (20 sweeps at κ = 0) | 75 s | |
| main: 480 pairs, 180 of 600 sweeps before the cap | 1847 s | **10.26 s** |
| **one launch batch at `T = 600`, extrapolated** | **6775 s = 1.88 h** | |
| per job (3 per batch) | 2258 s = 38 min | |

Per unit at β = 2.3 (`T = 300`, same per-sweep cost by amendment A4): main 3078 s + pool 270 s + set-up 78 s = 3426 s per batch,
19 min per job. `ℓ = 4` batches (6 jobs, 960 pairs) are costed at 1.096 × the `ℓ = 6` sweep cost (profiling ratio of the full
batches; not re-timed with the final sampler). U(1) and 2I are not implemented and are costed like SU(2) groups at `T(2.3)`.

## 2. Projection of the full run (`py project.py runs/timing_b3.5.json 300 600 [--mixed]`)

Two packings: **as implemented** (`job` takes one instance class per launch, so each adversarial class gets its own batch) and
**mixed** (classes of one `(β, κ, ℓ)` packed into shared launches; a small code change, not yet made).

| plan | as implemented | mixed packing |
|---|---|---|
| full design (amended: both `θ`, 160 pairs per job) | **539 h** | **248 h** |
| cut (i): κ = 4 only at β = 2.3 and 3.5 | 394 h | 186 h |
| cut (ii): + `ℓ = 4` only at β = 2.3 | 252 h | 139 h |
| cut (iii): + sampled `Y` 16 → 8 | 224 h | 109 h |
| cut (iv): + `θ = π` only | 203 h | **58 h** |
| budget cap | 20 h | 20 h |

Per β, full design, mixed packing: β = 2.3: 31.6 h; β = 2.6, 3.0, 3.5: 62.4 h each; U(1): 14.5 h; 2I: 14.5 h (estimates).
After cuts (i)-(iii), mixed: β = 2.3: 22.5 h; 2.6: 14.3 h; 3.0: 14.3 h; 3.5: 28.6 h; controls 29 h.

The β dependence comes only from `T` (300 at β = 2.3, 600 at the other three, by the rule `T(2.6) = T(3.0) = max`).

**Verdict by the pre-registered rule (section 8, step 4): the projection exceeds the 20-hour cap even after every
pre-registered cut (58 h in the best packing). The rule says: ask the owner.**

## 3. What could bring it under the cap (for the owner's decision; none of it done)

1. **Mixed packing** (small code change): already counted in the right-hand column.
2. **A fused update kernel.** The run is launch-bound: the GPU sat at 25-47 % during the timed job, and one sweep costs
   10.3 s whether the launch carries 80 or 480 pairs (profiling). The cost is about 300 small kernel launches per colour class
   × 324 classes per sweep. One custom CUDA kernel per class update would remove most of that; a factor 5 to 20 is plausible
   but **not measured** (estimate). At 5× the cut plan (iv, mixed) would be about 12 h.
3. **A smaller `T`.** `T(3.5) = 600` comes from a crude agreement test (window means, autocorrelation ignored); the
   disagreement plateau itself is reached by about sweep 100 at both β. A stricter statistical test could give a smaller or a
   larger `T`. Not changed after seeing the data.
4. **A narrower scientific scope.** The pilot already shows the coupled-chain upper side saturating (83-89 % of the box links
   disagree at both β). The pass verdict (`R_up < 1`) is therefore out of reach with this instrument, as the pre-registration
   anticipated. What a full run would deliver is the lower side `R_low`, the bad-cluster statistics and the adversarial (`WL-Q`)
   tests. A run limited to those, at the two ends β = 2.3 and 3.5, κ = 16, `ℓ = 6`, mixed packing, sampled `Y` = 8, `θ = π`
   only (80 pairs per job, 6 jobs per batch, 23 jobs per β: 4 batches), costs about 4 × 0.95 h (β = 2.3) + 4 × 1.88 h
   (β = 3.5) ≈ 11-12 h, SU(2) only, without the U(1) and 2I controls (estimate from the same numbers).

## 4. Caveats

* One timed job at one β; β = 2.3 is projected with the same per-sweep cost (amendment A4). The MH acceptance differs slightly
  (0.85 at β = 2.3, 0.92 at 3.5), which affects the rejection loops only.
* The cupy memory pool reported 12 GB in total during the job (the GPU has 8 GB; Windows lets the pool spill into shared
  memory). `nvidia-smi` showed about 3 GB in use. If spilling occurred it slowed the run; smaller batches might be marginally
  faster per pair. Not tested (no further GPU use).
* Not implemented, needed before a production run: U(1) and 2I paths, A5 (adjoint generator), the photon content gate G2,
  the Pinsker diagnostic, the rarity cluster analysis, the influence-bad classification (`../INFLUENCE-BAD.md`), mixed packing.

---

# Narrow run with the fused update (amendment A6, owner's decision)

## 5. The timed fused launch (`runs/timing_fused_b3.5.json`, `.log`, `.npz`)

* Started 04:21:53 on an idle GPU (0 %), watcher with hard kill at 44 min; ended 04:43:27, **1294 s, full `T = 600` completed,
  no cap reached**.
* One mixed launch: β = 3.5, `ℓ = 6`, κ = 16, `θ = π`, 6 jobs (A3 and A1 with a pool of 8; A2, A4, A6, sampled `Y` with the
  equilibrium outside), 480 coupled pairs, fused path.
* Sanity: MH acceptance 0.90 (CPU pilot 0.92); box plaquette 0.732 (mixed launch with twisted instances; equilibrium 0.768);
  end disagreement 4682 of 5184 box links (90 %, saturated as before).

| stage | measured |
|---|---|
| geometry | 3.7 s |
| greedy pool, 2 jobs × 64 pairs, 60 sweeps | 71.5 s (1.19 s/sweep) |
| build of 6 jobs + heating start 1 (20 sweeps, κ = 0) | 30 s |
| main, 480 pairs, 600 sweeps, measurements every 10 sweeps included | 1175 s (**1.96 s/sweep**) |
| **one launch of 6 jobs** | **1280 s = 21 min** (3.6 min per job) |

**Speed-up.** Per sweep of a full `ℓ = 6` batch: 12.1 s (reference) → 1.47 s (fused kernel only): 8.3×. At the launch level,
with the measurements (alignment, disagreement, plaquettes every 10 sweeps, still array code): 10.26 s → 1.96 s per sweep.
Per job: 38 min (first timed job, both `θ`, as implemented) → 3.6 min (narrow job, `θ = π`, fused).

## 6. Projection of the narrow run (`py project_narrow.py runs/timing_fused_b3.5.json`)

Per β: 8 sampled + A1-A4 (equilibrium outside) + A1-A4 (worst of 8) + A6 = 17 jobs = 3 launches; the 4 pool jobs share one
pool phase. Per-sweep cost taken β-independent (A4); `T(2.3) = 300`, `T(3.5) = 600`.

| β | `T` | launches | main | pool | total |
|---|---|---|---|---|---|
| 2.3 | 300 | 3 | 0.52 h | 0.6 min | 0.53 h |
| 3.5 | 600 | 3 | 1.01 h | 1.2 min | 1.03 h |
| **narrow run** | | 6 | | | **1.55 GPU-hours** (target: under 3 h) |

Margin: a 2× overrun still fits the target. The abort rule (a launch above twice its projected time stops the queue) bounds
the damage.

## 7. Saved data and the CPU cost of the two-level bad-set analysis

* **Saved per launch** (`*.npz`, compressed): 39.5 MB (55 MB raw: box plaquettes of both chains of every pair 29 MB, lever
  snapshots 2 × 7.8 MB, series and tables < 1 MB). **Narrow run: about 240 MB** (6 launches; pool phases save nothing).
* **Lever snapshots:** chain A box links (samples of `K(Y, ·)` at the unperturbed outside) of 8 pairs per start per job, at
  `T/2` and at the end: 32 fine configurations per job, 34 jobs, about 1100 configurations, each with its `Y` and outside.
* **CPU cost of the two-level classification (estimates; the analysis code is not written yet):**
  * *Full local influence* (the pre-registered `κ_b`: an `ℓ = 4` box centred on a block, 32 coupled shell pairs, `T(β)` sweeps,
    reference path on the CPU at about 2 s per sweep for 32 pairs, extrapolated from 1.27 s at 8 pairs and about 1.5 s at 16):
    10-20 min per local box. A subsample of 1 snapshot per start × 4 blocks per job (8 per job, 272 local boxes) costs
    **about 70 CPU-hours, about 9 hours wall on 8 cores**. All 81 blocks of all snapshots would be thousands of CPU-hours:
    not sensible.
  * *Cheap proxy* (single-link Dobrushin column sums at the actual configuration, Pinsker bound with the closed-form
    Kullback-Leibler divergence between the two von Mises-Fisher single-link laws): microseconds per link pair; every block of
    every snapshot (about 88 000 local boxes) in **a few CPU-hours**. It is an upper-type proxy, not the pre-registered
    quantity; it ranks blocks and locates candidates for the full computation.
  * *Alternative on the GPU* (fused path, not requested): the 272 local boxes as `ℓ = 4` launches of 960 pairs, about 9 launches
    of 10-20 min, **about 2-3 GPU-hours**.

## 8. Outcome against the projection, and the error band of a single-timing projection (reusable rule)

**The narrow run** (04:49:21-07:04:36): **8115 s = 2.25 GPU-hours against 1.55 h projected (1.45×)**; all 6 launches completed,
no abort, no hard kill (cap 3 h).

| launch | content | actual / projected | s per sweep (main) | MH acceptance |
|---|---|---|---|---|
| β 2.3 s101 | 4 pool jobs (A1-A4) + A1, A2: rough (Haar) block fields | 1220 / 657 s = **1.86** | 3.80 | 0.83 |
| β 2.3 s102 | A3, A4, A6 + 3 sampled | 791 / 657 = **1.20** | 2.52 | 0.85 |
| β 2.3 s103 | 5 sampled | 598 / 657 = **0.91** | 1.92 | 0.85 |
| β 3.5 s101 | as s101 above | 2278 / 1280 = **1.78** | 3.59 | 0.89 |
| β 3.5 s102 | as s102 above | 1583 / 1280 = **1.24** | 2.57 | 0.92 |
| β 3.5 s103 | 5 sampled | 1562 / 1280 = **1.22** | 2.54 | 0.92 |
| timed launch (β 3.5, before the run) | A3, A1 pool + A2, A4, A6, sampled | 1.00 by construction | 1.96 | 0.90 |

**What drove the overrun.** (a) **Launch content**, dominant: launches with Haar-random (rough) block fields cost about 1.8× a
mixed launch per sweep at either β (the in-kernel rejection loops of the coupled proposal run longer on rough fields). (b) **A
slow drift over the run**, observed but not explained: the β = 3.5 launches, run 1.3 to 2.2 hours into the job, were slower per
sweep than the timed launch and than their β = 2.3 counterparts with the same or lighter content (sampled only: 2.54 s at β 3.5
late in the run, 1.92 s at β 2.3 early). Laptop-GPU thermal throttling would do this; clocks were not logged, so it is a
hypothesis. (c) **β itself**: no clean separation from (a) and (b) in these data (same-content pairs differ by −6 % to +32 %); my
earlier remark during the run that the cost "depends on β" overstated it.

**Rule for projecting a GPU run from one timed unit (use for later projections, the IR timing job included):**
1. **Floor of the uncertainty: the content spread.** Per-launch actual/projected ratios from this run: 0.91, 1.20, 1.22, 1.24,
   1.78, 1.86; geometric mean 1.33, standard deviation of the log 0.27. So a projection of one launch from one timing of a
   different launch carries **at least ±30 % (one sigma) and a range of 0.9× to 1.9×**, however carefully the timed unit was
   measured. This is the minimum honest error bar; it is not reduced by timing the same unit again.
2. **Time the content, not just the size.** If launches differ in content (rough versus smooth fields, pool phases), time one
   unit of each content class (short timings suffice: the cost per sweep is constant after a few sweeps), or scale with the
   class factors measured here (rough-field launch ≈ 1.8× a mixed one, sampled-only ≈ 0.75-1.0× a mixed one).
3. **Transfer between couplings.** Projected unit time = set-up + `T(β)` × `s(β, content)`. Take `T(β)` from the pilot at each β
   (here 300 and 600: a factor 2, the dominant β dependence). Take `s` from the timed unit with a factor 1.0 ± 0.3 for another
   β unless it was timed there too; a short timing at the other β removes that factor.
4. **Long runs:** add a drift allowance for runs much longer than the timed unit (+25 % observed here over 2 hours on the laptop
   GPU) until its cause is known; log GPU clocks and temperature at the watcher's checkpoints to decide it.
5. **Report** the projection as a central value with the band of rule 1 (and rule 4 for long runs), and set the hard cap at or
   above the band's upper edge (here 1.55 h × 1.9 ≈ 2.9 h; the 3-hour cap held).

Applied after the fact: 1.55 h × [0.9, 1.9] = 1.4 to 2.9 h, central 1.55 × 1.33 = 2.1 h; the actual 2.25 h lies inside the band.
