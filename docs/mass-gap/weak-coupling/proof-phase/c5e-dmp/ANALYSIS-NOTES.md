# Analysis notes for the joint z0/z_e measurement (c5e-dmp)

Written by the analysis workstream before any data was read with `analyse_joint.py` (copied by the coordinator from the script's docstring, where they are authoritative).

```
Analysis of the joint measurement of z0(L) and z_e(L) (c5e-dmp, PREREG-JOINT.md), written 2026-11-22 before any data was read with it.

ANALYSIS CHOICES (everything the prereg leaves open; the prereg wins wherever it speaks). Written before the first run on data; only the
synthetic --selftest existed then. See the "Fix log" at the end of this docstring for any later change.

Inputs/bookkeeping
 1. Input: .npz of lattice/run_su2_gpu.py (glue (n,8,T), tor (n,4,T), levels 2,6,12,20, chain-major). partial=1 or chains not dividing 20: refused.
 2. Jackknife: 20 contiguous equal bins (analyse.jackknife formula, re-implemented only to keep the replicas for derived quantities; tested
    against analyse.jackknife in --selftest). With 10 chains each bin lies inside one chain.
 3. Scale a*sqrt(sigma) = 0.350, 0.258, 0.1825 (beta 2.3, 2.4, 2.5); the project's torelon values 0.363, 0.273, 0.199 give a second axis column.
Operators and variational step
 4. z0 basis: 8 glueball ops (file order) + 4 flux-pair ops O_pp,k = tor_k(t)^2 = 12 ops (the prereg says 16; 8 + 4 = 12, all 4 levels used). z_e basis: the 4 torelon ops (tor is already the zero-
    momentum sum over lines and the three directions).
 5. Noise drop: with the full data an op is dropped if the jackknife error of its diagonal C(0) is > 0.5*C(0) (C vacuum subtracted as in
    analyse.correlator_matrix). The kept set is fixed from the full data, used unchanged in all replicas. No op left: channel NOT COUNTED.
 6. analyse.best_projection(C, t0=0, t1=1), recomputed in every replica; c(t) = v C(t) v, t = 0..T/2.
 7. m(t) = analyse.cosh_mass(c, t, T) (c(t)/c(t+1), periodic cosh form; the prereg's "c(t-1)/c(t), c(t+1)" is read as this cited function),
    for t = 0..min(T/2-1, 8) (tmax = 8 as analyse_plateau.meff).
 8. Plateau: analyse_plateau.plateau(m, e), imported unchanged; E = m(t*), t* from the full data, replicas at the same t*. COUNTED for z0
    only if t* exists and m(t*+1) is finite with finite error. A NaN in any replica makes that t unusable (no interpolation).
 9. z = L*E (errors scaled by L). Systematic = the same at t*+1, printed next to every number.
z_e counting rule
10. The file holds the torelon summed over the three directions only, so the >= 10 sign flips per chain rule is applied to this sum: per
    measurement the level-0 torelon averaged over the T slices; sign changes counted per chain; counted if the minimum over chains >= 10.
    (Weak at small L: noise near zero also flips the sign. Reported with the flips per chain; no other test.) Diagnostic only, no gate:
    chain mean of that quantity in units of its within-chain rms.
11. z_e also needs a plateau as in 8.
Readings
12. g_gamma(L) = z0g(2L)/z0g(L), z0g(L) = 2L asinh(sin(pi/L)), cross-checked against photon_exact.json at run time.
13. J1 per pair (beta, L, 2L), both z0 counted: g0 = z0(2L)/z0(L), sigma_g = g0 hypot(s1/z1, s2/z2). Rules evaluated at E(t*) (shift 0) and
    E(t*+1) (shift 1), each point with its own t*. DOUBLES needs the DOUBLES condition at both shifts; a shift-0 DOUBLES failing at shift 1
    is NOT RESOLVED; otherwise the verdict is that of shift 0. "Not robust to the plateau choice" if the shift-1 verdict differs from the final one.
14. J2: pair-start "scaling sets" = the J5 sets plus {1.03 (beta 2.4), 1.09 (beta 2.5)} (the two smallest boxes, 6 % apart; the prereg's sets list
    boxes that also occur as doubled partners and have no member there). A set qualifies if DOUBLES pairs start at two different beta in it.
    L_D sqrt(sigma) = smallest start L sqrt(sigma) of a DOUBLES pair in the lowest qualifying set; D-S candidate (zeta0, zeta_e) printed for every
    DOUBLES start in that set (z_e NOT COUNTED if it is). Otherwise "NO START ON THE MEASURED STRETCH".
15. J3: v from step 6 normalised by diag C(0): v_n,i = v_i sqrt(C_ii(0)); w_pp = sum_{O_pp} v_n^2 / sum v_n^2 (kept ops). Delta = E0 - 2E_e at
    shift 0 (shift 1 printed). Needs z0 and z_e counted, else NOT RESOLVED. Switch per beta: g = first (smallest L) GLUEBALL point, f = last
    FLUX-PAIR point with L below g, L_s sqrt(sigma) = midpoint; otherwise "no switch in the measured stretch" with the reason.
16. J4: eta = 1 - g0/2, sigma_eta = sigma_g/2, DOUBLES pairs, by increasing L sqrt(sigma), no verdict.
17. J5: sets of boxes (beta, L): {1.40: (2.3,4), 1.46: (2.5,8)}, {2.06: (2.4,8), 2.10: (2.3,6), 2.19: (2.5,12)}, {2.80: (2.3,8), 2.92: (2.5,16)},
    {4.13: (2.4,16), 4.20: (2.3,12), 4.38: (2.5,24) optional, not in the plan}. Counted members: SCALING OK if every pair agrees within
    2 hypot(s_i, s_j), else ARTEFACTS VISIBLE (spread = max - min); fewer than two counted: NOT RESOLVED.
18. J6: table and plot of z0 and z_e against L sqrt(sigma) with the line z0 = 3.6 L sqrt(sigma); NOT COUNTED points are not plotted.
Controls and outputs
19. Stage 0 control (--control): torelon E_e at beta 2.3, T = 16, L = 6, 8, 10 against results/luscher_summary.json, pass if
    |E_e - E_ref| <= 2 hypot(sigma, sigma_ref) at E(t*) (the earlier numbers used t = a..2a with a plain log mass).
20. Outputs: --out summary JSON, --report text, --plot png. Pilot output carries --label and is never counted.

Usage:
  python analyse_joint.py FILE.npz|GLOB ... [--label TEXT] [--out summary.json] [--report report.txt] [--plot z.png] [--control]
  python analyse_joint.py --selftest

Fix log: (empty at the time of writing)
```
