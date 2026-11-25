# EXPLORATORY / POST-HOC result: do boxes with bad clusters settle more slowly in Monte Carlo time? (2026-11-23)

**Status: EXPLORATORY, POST-HOC; not part of the W2 verdict.** Plan fixed before any settling data was opened:
`EXPLORATORY-SETTLING.md` (committed in bc601c9; plan and script unchanged since). Run on the CPU after the GPU run and after the
pre-registered analysis and the proxy: `py exploratory_settling.py runs/narrow/launch_b*.json` ->
`runs/narrow/exploratory_settling.json`. The owner's transfer to GR is not tested here.

## Result, scored by the plan's rule

| β | measure | bad / clean (boxes 7 / 10) | box jackknife | pair jackknife | verdict |
|---|---|---|---|---|---|
| 2.3 | **`τ_int` of `W(t)`, second half (decides)** | 5.43 / 5.47 sweeps = **0.99** | ± 0.02 | ± 0.02 | **not slower** |
| 2.3 | `t_e` from `t = 0` (descriptive only) | 10.5 / 10.4 sweeps = 1.02 | ± 0.01 | ± 0.02 | unresolved (`t_e` = 10 sweeps for most pairs) |
| 2.3 | secondary: rough vs smooth sampled boxes, `τ_int` (4 / 4) | 0.97 | ± 0.03 | | not slower |
| 3.5 | **`τ_int` of `W(t)`, second half (decides)** | 6.62 / 6.30 sweeps = **1.05** | ± 0.13 | ± 0.04 | **not slower** |
| 3.5 | `t_e` from `t = 0` (descriptive only) | 10.5 / 10.8 = 0.98 | ± 0.02 | ± 0.02 | unresolved |
| 3.5 | secondary: rough vs smooth sampled boxes, `τ_int` (4 / 4) | 0.97 | ± 0.04 | | not slower |

## Two limits that bound what "not slower" means

1. **Resolution.** `τ_int` is at its floor (0.5 measurement = 5 sweeps) for 80 % of the pairs at β = 2.3 and 64 % at β = 3.5
   (medians 5.0 sweeps; 90th percentiles 6.7 and 10.0; maxima 11 and 26). The coupled pair's disagreement sum decorrelates
   within the 10-sweep measurement spacing for most pairs. So the result says: **no settling difference between bad and clean boxes
   is visible at a resolution of 10 sweeps.** A difference on shorter Monte Carlo times is not excluded; measuring it would need
   denser series (a new GPU run).
2. **The twisted defect was not taken up by the fine field.** The plan's adaptation check at `T/2` (alignment
   `⟨Y_l, Φ̃_l⟩ / |Φ̃_l|`):
   * A3 (twisted half-slice of the block field): **−0.10 to +0.01 on the defect's coarse links, 0.96-0.97 on the rest**. The fine
     field does not follow the flipped block links: it does not form the vortex sheet the twisted block field asks for, and pays the
     constraint cost instead (or has not nucleated the sheet within `T/2` = 150 or 300 sweeps). So the A3 boxes did not carry a
     fine-level defect, and they count as "bad" only by their block field.
   * A4 (one boundary block link rotated by `π`): 0.84-0.95 on the defect link against 0.96-0.97 on the rest: largely adopted.
   * A2 and A6 were not checked by this measure (A2 is rough everywhere; A6's sheet is in the frozen outside).

## Reading

At these two couplings, with this sampler, boxes with built-in rough or defect block fields (and an attached outside sheet) do not
settle measurably more slowly than clean boxes, at the 10-sweep resolution of the saved series. The strongest built-in defect, the
twisted block field, did not even produce a defect in the fine field within the run, which is a finding in its own right: under the
soft constraint at κ = 16 the fine field prefers to ignore a twisted block field rather than carry a sheet.
