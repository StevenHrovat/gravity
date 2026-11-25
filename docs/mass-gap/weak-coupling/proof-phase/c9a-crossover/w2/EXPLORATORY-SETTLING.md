# EXPLORATORY / POST-HOC: do boxes with bad clusters settle more slowly in Monte Carlo time? (W2 narrow run, 2026-11-23)

**Status: EXPLORATORY, POST-HOC.** Not part of the pre-registered W2 verdict (`../W2-PREREG.md`, amendment A6). Requested by the
owner during the production run: "It is now monte-carlo time, but it should be 1:1 transferrable to GR. Please add the test and
continue." The transfer to GR is the owner's reading; this note tests only the Monte Carlo statement. Written at 05:15 on
2026-11-23, **before any settling series of the production run was looked at**. (Only the stage timings of launch 1 had been
read, for the run's time budget. The earlier timing launch, `runs/timing_fused_b3.5.*`, whose end-of-run disagreement I had
seen, is excluded from this test.) CPU only, after the GPU run; no GPU work.

## 1. What the saved data allows

* Per launch, per coupled pair: the disagreement count `d(t)` and the geodesic disagreement sum `W(t)` between the two chains,
  every 10 sweeps (`T/10` values at β = 2.3, `T/10` at 3.5), and the time-averaged box plaquettes of both chains.
* Per job (= one box = one instance: outside, block field `Y`, class): 80 pairs (40 per start: 32 shell links + 8 block
  variables at `θ = π`), and chain-A box snapshots (8 pairs per start) at `T/2` and at the end.
* **No per-block time series.** Series are per pair over the whole box. So the settling time is measured per pair, averaged per
  box, and boxes are classified as a whole. A per-block settling time would need per-link disagreement maps, which were not
  saved; no new GPU run is made for it.

## 2. Box classification (fixed now)

* **Primary (by design, known before the run):** *bad* boxes = the instances with a built-in defect or rough field: A2 (Haar-random
  block field), A3 (twisted block field: a sheet through the box), A4 (one boundary block link rotated by `π`: a large-field
  block plaquette), A6 (a thin vortex sheet in the outside attached to the box). *Clean* boxes = sampled `Y` (equilibrium) and
  A1 (flat block field). Pool and equilibrium-outside variants of a class count the same.
* **Secondary (from the data, within the sampled boxes only):** the number of fine plaquettes of the box with `1 − ½ tr > 1.0`
  in the chain-A snapshots at `T/2` (mean over the 16 snapshots of the box), split at the median over the sampled boxes of that
  β: *rough* vs *smooth*. (The proxy influence classification of `lever_proxy.py` is not used: at these couplings it marks every
  block bad, so it cannot split boxes.)

## 3. Settling measures (fixed now), per pair, start 0 only

Start 0 begins at the equilibrium interior (an exact draw for the sampled boxes), with chain B differing by one perturbed link,
so `d(t)` grows from 0 to its plateau.
* **Primary: integrated autocorrelation time `τ_int` of `W(t)`** over the second half of the run (after the plateau), with the
  self-consistent window `c = 6` (as `lattice/gpu/gauge.py tau_int`), in sweeps (× 10 for the measurement spacing). It measures
  how slowly the coupled pair's disagreement fluctuates once settled: the Monte Carlo correlation time of the box dynamics as seen
  through the pair. Caveat fixed now: at β = 2.3 a pair has 30 measurements (15 in the second half), at β = 3.5 60 (30), so
  `τ_int` is coarse, especially at β = 2.3; a box value is still an average over 40 pairs.
* **Secondary: spreading time `t_e`**: the first measurement time at which `d(t) ≥ (1 − 1/e) × plateau`, plateau = mean of the
  last three measurements of that pair. Resolution 10 sweeps; if `t_e = 10` for more than 80 % of the pairs of a β, the
  secondary measure is reported as *unresolved* for that β.
* **Box value:** the mean over the box's 40 start-0 pairs (shell-link and block-variable pairs together).
* **Confound of `t_e` (added before any data, coordinator's point).** The primary classification is by designed start type,
  and `t_e` is measured from `t = 0`. For a bad box, start 0 is the equilibrium interior of the *unmodified* instance, which is
  farther from the conditional law of the modified block field or outside than for a clean box. A larger `t_e` can therefore mean
  "started farther away", not "held back by the defect". **`t_e` is reported for description only; `τ_int` over the second half
  decides.**
* **Is the defect held fixed? (added before any data.)** Yes, for every bad class: A2, A3, A4 live in the block field `Y`, and A6
  in the frozen outside. Both are conditioning data, not updated during the run, so the defect itself cannot relax; it is present
  at `T/2` by construction. What can lag is the fine field's adjustment to it. Recorded, descriptively, at `T/2` for the A3 and
  A4 boxes: the mean alignment `⟨Y_l, Φ̃_l⟩ / |Φ̃_l|` of the chain-A snapshots over the defect's coarse links (A3: the flipped
  half-slice; A4: the rotated link) and over all other constraint links of the box. If the fine field has not adapted by `T/2`
  (alignment over the defect links far below the rest), the second-half `τ_int` of that box may still contain relaxation, and this
  is stated with the result.

## 4. Comparison and threshold (fixed now)

* Per β separately: ratio `ρ = mean over bad boxes of the box value / mean over clean boxes`, for each measure. Error: jackknife
  **over boxes** (leave one box out; boxes are the independent units, pairs within a box share the instance). Also reported:
  the jackknife over pairs within boxes (leave one pair index out across all boxes), as the coordinator asked, as a secondary
  error.
* **"Slower" means:** `ρ ≥ 1.5` and `ρ − 1 > 2σ` (box jackknife), for the primary measure. **"Not slower":** `ρ < 1.2` or
  `ρ − 1 < 2σ`. Anything else: *inconclusive*. Same rule for the secondary classification (rough vs smooth sampled boxes).
* Counts per β (narrow design): clean = 8 sampled + 2 A1 = 10 boxes; bad = 2 A2 + 2 A3 + 2 A4 + 1 A6 = 7 boxes. Small samples:
  the box jackknife will be wide, and the outcome may well be inconclusive.

## 5. What this can and cannot say

* It compares Monte Carlo correlation times of the coupled-pair disagreement, not physical relaxation, and only for this
  sampler (heat-bath proposal plus Metropolis, fixed colour order). A slower box under this sampler need not be slower under
  another one.
* The coupled pair is saturated (about 90 % of the links disagree), so `W(t)` mostly reflects the two chains' independent
  fluctuations: `τ_int` is close to the single-chain autocorrelation time of the box's total "distance", which is what is wanted
  here.
* Nothing here enters the W2 verdicts.

Code: `exploratory_settling.py` (to be written after this plan, run on the CPU after the GPU run).
