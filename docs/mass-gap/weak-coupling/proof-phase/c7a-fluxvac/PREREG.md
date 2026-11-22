# Pre-registration: what the joint z0/z_e measurement should show if the c7a reading holds (c7a-fluxvac, 2026-11-22)

Written before any file of the running joint measurement (`c5e-dmp/runs-gpu/joint_*`) was read. Read before writing: only the
Stage 0 pilot report (`c5e-dmp/pilot/pilot_report.txt`, existing beta = 2.3 data at T = 16, never counted), which fixed the binding
band below (z0 = 6.48 at L sqrt(sigma) = 2.10 against 2 z_e = 7.19). The model and its numbers: `predict_pairs.py` ->
`predict_pairs.log` (pure arithmetic). No GPU, no simulation.

## 1. The reading under test

* (R1) **The flux window holds no doubling.** The lowest centre-even state is a flux pair (z0 ~ 2 z_e) only on a stretch from about
  the deconfinement length (L sqrt(sigma) ~ 1.4) to the switch (~2.0 to 2.3), a factor below 2. No dyadic pair has both ends on
  the flux-pair branch, so the window implication (Lean `doubling_of_window`) applies to no measured pair.
* (R2) **Above the switch the vacuum act does not inherit the flux gain.** The vacuum doubling there is carried by the glueball
  branch (persistence of E0), not by the flux act: the vacuum gain is far smaller than twice the flux gain.
* (R3) **The loss stays far inside one quantum.** c = 2 z0(L) - z0(2L) <= 1 at every counted pair (negative at most).
* (R4) **No pair state in small boxes.** At L sqrt(sigma) <= 1.1 the electric flux energy is small (tunnelling), and the lowest
  centre-even state lies above the pair threshold: z0 > 2 z_e.
* (R5) **The flux pair cannot supply a 4 pi start.** z0 < 4 pi on the whole flux-pair branch and up to 3.1; z0 > 4 pi from 4.1 on.
* (R6) **Upper sector transfer (a theorem, Lean `su2_E0_le_pairRate`).** z0 <= z_pp, the act of the flux-pair operator alone.

## 2. Model behind the numbers (fixed now)

x = L a sqrt(sigma) with the PREREG-JOINT scale. Flux act for x >= 1.4: band [x^2 - pi/3, x sqrt(x^2 - pi/3)], centre x^2 - 0.88
(c6b). Glueball branch z_g = r x, r in [3.4, 3.8]. Pair threshold 2 z_e. Vacuum act z0 = min(2 z_e, z_g) - b, binding b in [0, 1]
within 0.4 of the switch. No prediction from string formulas below x = 1.4.

## 3. Criteria (counted points of the joint measurement, its own J1/J3 rules and errors)

| id | statement | holds if | against the reading if |
|---|---|---|---|
| P1 (R1) | no counted pair has both ends J3 = FLUX-PAIR | true | a pair with both ends FLUX-PAIR |
| P2 (R2) | at every counted pair starting at x >= 2.0 (2.3: 6->12, 2.4: 8->16, 2.5: 12->24 if run): R = (z0(2L) - 2 z0(L)) / (2 (z_e(2L) - 2 z_e(L))) < 0.3 | R + 2 sigma_R < 0.3 at every such pair | R - 2 sigma_R > 0.6 at any such pair (vacuum gain tracking the flux gain: the vacuum still built from flux above the switch) |
| P3 (R3) | c = 2 z0(L) - z0(2L) <= 1 at every counted pair | c - 2 sigma_c <= 1 everywhere | c - 2 sigma_c > 1 anywhere; c - 2 sigma_c > 2 pi would contradict the one-quantum loss bound outright |
| P4 (R4) | at x = 1.03 (2.4, L 4) and 1.09 (2.5, L 6): Delta = E0 - 2 E_e > 0 | Delta > 2 sigma_Delta (J3 then reads MIXED) | Delta < -2 sigma_Delta (a state below the pair threshold) |
| P5 (R5) | z0 < 4 pi at every counted x <= 3.10; z0 > 4 pi at every counted x >= 4.13 | both | a flux-pair-branch point with z0 > 4 pi, or z0 < 4 pi at x >= 4.13 |
| P6 (R6) | z0 <= z_pp at every point where the pair-operator-only plateau can be read (post hoc, labelled) | z0 - z_pp <= 2 sigma | z0 - z_pp > 2 sigma (an estimator problem, not physics: it is a theorem for the exact gaps) |

Expected numbers (centre of the model, `predict_pairs.log`): g0 = 4.7 (2.3: 4->8), 2.3 (2.3: 6->12), 3.7 (2.4: 6->12), 2.4 (2.4:
8->16), 4.2 (2.5: 8->16), 2.2 (2.5: 12->24); c from -6 to -1; R about 0.5 on the crossover pairs and 0.05 to 0.12 on the pairs that
start at x >= 2.0. The switch at x_s = 2.0 to 2.35 (where z0 is 7 to 9, about one quantum plus one); z0 reaches 4 pi at x = 3.3 to 3.7.

Not tested here: anything beyond x = 4.4, the continuum limit, and the open premise itself (X, the persistence of the non-flux
branch); the measurement can only show that its numerical shape is as stated.
