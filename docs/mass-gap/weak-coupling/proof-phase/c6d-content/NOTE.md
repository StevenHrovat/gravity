# c6d-content: the photon control with the amended instrument (2026-11-22)

Amends c5b (`PREREG-AMEND.md`, fixed before the run). CPU, one process, no GPU, nothing committed. **Every number is a LOWER BOUND by held-out regression (700 orbit features v2; 108 of them are c5b's v1), 16^4 lattice; a value near 0 is INCONCLUSIVE about the true R2.**

## Result
**The photon gate FAILED (narrowly on P8, clearly on Q4). SU(2) was not run (as registered).**

Photon U(1) beta 1.1, w = 2, test-phase lower bounds (err = jackknife), v2 [v1 in brackets]:

| b | P2 | P4 | P8 | Q4 | Q8 |
|---|---|---|---|---|---|
| 2 | 0.044(1) [0.035] | 0.117(3) [0.112] | 0.145(12) [0.126] | 0.107(4) [0.106] | 0.134(9) [0.121] |
| 4 | 0.000 [0.000] | 0.0041(4) [0.0032] | 0.0136(20) [0.0129] | 0.0081(7) [0.0063] | 0.0269(30) [0.0277] |
| 8 | 0 [0] | 0.0000(1) | 0.0000(3) | 0.0000(1) | 0.0016(7) |

w = 0 (decimation): b = 2 below w = 2 on every target; b = 4: P8 0.0017(5), others about 0; b = 8: 0.

Gate (PREREG-AMEND section 3, at b = 4, w = 2): G1 needs LB - 2 err >= 0.01 for Q4 and P8: Q4 0.0081 - 0.0014 = 0.0067 (fail), P8 0.0136 - 0.0040 = 0.0096 (fail by 0.0004). G2 (P4 above the c5b value 0.0031 by 2 err): 0.0041 - 0.0008 = 0.0033 (pass, barely). G3 (instrument gates): selftest passed (alignment, planted 0.295 for 0.30, null 0.0001, plus gauge invariance, Fourier orbit sums vs explicit shifts, targets); val/test agreement Q4 b = 2: 0.117 vs 0.107 (pass); plaquette drift 0.2 sigma (pass). Gate not passed. Threshold was not moved after the result.

## What it says
1. The instrument now sees photon content at b = 4: Q8 0.027, P8 0.014, Q4 0.008 (all lower bounds), against 0.000 for c5b's P2 and 0.003 for P4. **Almost all of the gain comes from the new targets, not from the new features:** the same c5b features (v1) already give Q8 0.028, P8 0.013, Q4 0.006 at b = 4. The new loops and pair traces add +30 percent on Q4, +30 percent on P4, nothing on P8 and Q8 (within errors). So the conditional mean of these targets is not limited by the features' reach.
2. Content falls steeply with block size even for the photon (b = 2 to 4: factor 5 to 25), and is zero at b = 8, where the block lattice is 2^4 and the features wrap: b = 8 is not a clean test on 16^4.
3. The gate itself was pitched at the edge: the longest-window targets sit at about 0.01 to 0.03, so a bound of 0.01 minus two errors is on the instrument's noise-limited edge, not a property of the physics.

## Proposed next fix (not done)
(a) Make the control cleaner: the photon at beta 1.1 is just above the compact U(1) bulk transition, so monopoles dilute the Coulomb-phase content; add a photon at larger beta (about 2, close to free). (b) Give b = 4 and 8 room: the b = 4 block lattice is 4^4 (features wrap with loops up to extent 3 around +-1.5 cells) and b = 8 is 2^4; a 32^4 lattice (16 times the cost per sweep, so about 30 minutes needs fewer configurations) or the GPU instrument. (c) Replace the regression bound on this scale by an exact reference: for the Gaussian photon the conditional mean is a quadratic form in the coarse fluxes and its R2 can be computed by linear algebra (ceiling for any flux-quadratic predictor), which would tell whether 0.01 to 0.03 at b = 4 is the ceiling or a regression deficiency. (d) Re-pitch the gate on that reference instead of an absolute 0.01.

Files: `PREREG-AMEND.md`, `content.py` (v2 instrument), `run_cpu.sh`, `cpu-test/selftest.log`, `runs-cpu/u1_b1.1_N16.{json,out,log}`.
