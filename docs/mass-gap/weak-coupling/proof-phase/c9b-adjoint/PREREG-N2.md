# c9b round 2, CPU check N2: sharp sup-form columns, the W1-plus-smoothing count, larger L1 (pre-registration)

Written 2026-11-23 before any code of `n2_sharp.py` was run. CPU only (Windows Python, numpy), one process, expected runtime under
15 minutes. No GPU. Inputs are only the existing fitted actions: the c3b refit base fits (`../c3b-refit/runs-gpu/analysis.log`,
"base couplings [F_ts, F_ss, A_ts, A_ss, ...]") at all nine SU(2) points, and the c4d certified W1 column 0.7318 (base box,
`../c4d-certified/NOTE.md`). Nothing is refitted. Marks: every number this check produces is **numerical** (quadrature on S^3, no
interval arithmetic), about the **fitted** action only.

## Why

c9b (N1) used the per-incidence sup-form coefficient `tanh(beta_F)` (centre-odd) and `tanh(2 beta_A/3)` (centre-blind): the two-point
sharp bound for a log-weight change of mixed variation `4 beta_F`. The fitted single-link conditional laws are smooth densities on S^3,
`rho ~ exp(<A, u> + Psi(u))` with `|A| <= a` (a = sum of the fundamental couplings through the link), so the true sup-form Dobrushin
coefficient (sup over all boundary data and all pairs of values of the moved neighbour of the total-variation distance of the
conditional law) can be far below `tanh(beta_F)`. Small-coupling estimate: `beta_F E|<u, s>| = (4/(3 pi)) beta_F = 0.424 beta_F`.

## What is computed

For each fit and each pair type (ss: `(F_ss, A_ss)`, ts: `(F_ts, A_ts)`) and receiving link type (spatial: `a_s = 4|F_ss| + 2|F_ts|`;
temporal: `a_t = 6|F_ts|`):

1. **Sharp sup-form pair coefficient** `C = q(D) sup TV(rho_1, rho_2)`, `rho_i ~ exp(<A_r + beta s_i, u> + (alpha/3)(4<u, s_i>^2 - 1))`,
   sup over the rest field `|A_r| <= a - beta` (direction free) and the unit staples `s_1, s_2`; reduced by symmetry to four
   parameters (`r`, angle of `s_2` to `s_1`, two angles of `A_r`), coarse grid then local refinement, quadrature on S^3 (midpoint grid in
   Hopf-type angles, about 10^5 points in the search, about 10^6 for the reported values). `q(D) = (3 e^D - 1)/2` covers the
   adjoint terms of the other plaquettes of the receiving link (oscillation `D = sum (4/3)|alpha_p|`; bound proved on paper in the
   NOTE: a tilt `w` with `osc log w <= D` multiplies a total variation by at most `(3 e^D - 1)/2`).
2. **Crude coefficient** as in c9b N1: `tanh(beta_F) + tanh(2 |beta_A|/3)`.
3. **Columns** (sum over the 18 neighbours: a spatial link has 12 ss + 6 ts incidences, a temporal link 18 ts), row sums likewise;
   reported per link type; the binding number is the maximum.
4. **TV-Lipschitz pair constant** (smoothing): `Lam = q(D) sup (1/2) E_rho |G - E_rho G|`, `G = (beta + (8 alpha/3) <u, s>) <u, b>`, `b`
   unit, `b perp s`: the total-variation change of the conditional law per radian of geodesic move of the neighbour. Columns as in 3.
5. **The smoothing count at L sqrt(sigma) = 2.80** (sketch-level constants, section 1 of the round note): 8 colour classes of links
   (direction, parity of the transverse coordinate sum; no two links of a class share a plaquette), one heat-bath pass per class in an
   order chosen to minimise the amplification `K_s = max column sum of sum_{n < 8} Lhat^n` (`Lhat` the class-level matrix of sharp
   coefficients from earlier to later classes); Hamming count per outside change
   `kappa_Ham <= K_s (col_TV + Lam_col pi c_W/(1 - c_W))`, `c_W = 0.7318` (certified, c4d); then the box side `l_min` with
   `N_adj(l) kappa_Ham / l^4 < 1` (`N_adj(l)` = outside coarse sites with a link sharing a plaquette with the box, counted exactly).
6. **Direct Hamming route** where the sharp column `c_TV < 1`: `kappa_Ham <= col_TV/(1 - c_TV)` and its `l_min`.
7. Controls: (i) the quadrature at `A_r = 0`, `alpha = 0`, `s_2 = -s_1` against the 1D integral `E sign(t)` for the density
   `e^{beta t} sqrt(1 - t^2)`; (ii) the small-beta ratio sharp/(beta) against `4/(3 pi)`; (iii) the crude column at 2.80 reproduces
   N1's 2.397 (spatial).

## Predictions (fixed now)

* **P1** ratio sharp/crude per pair in `[0.35, 0.55]` for every fit and pair type.
* **P2** at `L sqrt(sigma) = 2.80` the sharp sup-form spatial column lies in `[0.85, 1.20]`; I do **not** predict its side of 1.
* **P3** at the fits with larger `L sqrt(sigma)` (2.92, 4.13, 5.60) the sharp sup-form column (max over types) is `< 1`.
* **P4** along each beta line (b = 4, 8, 16) the sharp column decreases with `L sqrt(sigma)`.
* **P5** TV-Lipschitz spatial column at 2.80 in `[0.4, 0.9]` per radian.
* **P6** `K_s` finite and `<= 10^4`; `l_min` (W1 plus smoothing, 2.80) finite and `<= 10^5` cells.
* **P7** controls (i)-(iii) agree to 1e-3 (relative 1 %).

A failure of P7 means the code is wrong and nothing else is reported as a result. P1-P6 failures are reported as findings.

## What it does not show

All numbers are about the fitted, truncated plaquette action (closure residuals up to 67 %, c4d). The points 2.92, 4.13, 5.60 failed
c3b's content check (NO_CONTENT: coarse 3^4 lattice, Creutz ratio not resolved), so their fits are exactly where the noise-limit trap
can make a column look small; a pass there is **not** evidence for the true law. The true law's columns are the GPU measurement's job
(`PREREG-GPU.md`, draft).

## Amendment after the run (2026-11-23, written after reading the log; the text above is unchanged)

* P7(iii) failed: the reference 2.397 is N1's crude column at the c4d **box corner**; the central fit used here gives 2.370 (the post-hoc
  check `n2_posthoc.log` (a) reproduces 2.3968 at the box corner). By the rule above, N2 is **void as a pre-registered result**; its
  numbers are reported in `ROUND2.md` as numerical diagnostics only.
* The tolerance "1e-3 (relative 1 %)" above is ambiguous. The code tested 1e-2 relative for (i), (ii) (observed 5e-5 and 5e-5) and 0.02
  absolute for (iii). Recorded here, not used to rescue anything.
* P1 failed at `L sqrt(sigma) = 0.73, 1.03` (strong coupling, and the adjoint tilt factor); P2-P6 passed.
