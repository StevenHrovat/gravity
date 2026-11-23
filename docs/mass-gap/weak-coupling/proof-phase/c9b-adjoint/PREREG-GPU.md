# DRAFT pre-registration (not run, not approved): the true law's c0, c1 and W1 column at L1 by constrained sampling

Status: **draft, 2026-11-23.** Nothing here has been run. No GPU job may start without the owner's explicit OK, and only after the timing
job of section 6 has been run and the whole run projected from it. The code does not exist yet (section 7). Shared with c8a's H_sat test
(`../c8a-saturation/NOTE.md` section 6.3): the centre-flip runs below measure H_sat's quenched centre constant at block level 1.

Marks used for outcomes: **numerical** (Monte Carlo, statistical and systematic errors stated). A pass is evidence about the true law at the
tested backgrounds, **not** a bound: the sup over all coarse data is replaced by a max over a finite list. A fail at one background is
decisive for the sup form at that `L1` and that block variable (one background with column > 1 refutes the sup-form condition there; it does
not refute the gap).

## 1. What is measured, and why

c9b (section 1.3) reduced the adjoint budget to single-site quantities of the **true** coarse conditional specification at `L1`:
`H(v_x | rest)`, the conditional log-density of one coarse block variable `V_x` (SU(2), the good blocking of c3b, `w = 2`) given all other coarse
variables and the fine outside. Round 2 (`ROUND2.md`, N2) showed that for the **fitted** action at `L sqrt(sigma) = 2.80`:

* sharp sup-form pair coefficients are 0.43 x the crude ones used in N1; sharp spatial column 1.021 (central fit), weighted spectral radius
  0.960 (post-hoc); W1 column 0.73 (certified, c4d); TV-Lipschitz column 0.51 per radian;
* so the fitted action is within a few per cent of the sup-form Dobrushin window and inside the W1 window. The question is the true law.

Per pair `(x, y)` of coarse links and per background (all other coarse data and the fine outside fixed), the measurement estimates the
conditional law `p(v_x | V_y = w)` for a few values `w`, and from it:

| quantity | definition | role |
|---|---|---|
| `C_xy` (sharp sup form, **max over the listed moves**) | `TV(p(. | w), p(. | -w))` (centre flip), `TV(p(. | w), p(. | w R))` (`R` a 90-degree SO(3) rotation), and in Stage B 4 random `w'` per class; max over these | Hamming Dobrushin column (H_prop, sup form); a lower estimate of the sup over moves (N2: the antipodal flip is the maximiser for every fit) |
| `C1_xy` | the centre-flip TV alone | centre-odd half, `c1`; **H_sat at block level 1** |
| `C0_xy` | TV of the centre-symmetrised laws `(p(.|w) + p(.|-w))/2` vs `(p(.|wR) + p(.|-wR))/2` | centre-blind half, `c0` (H_adj) |
| `K_xy` (W1) | `KR(p(.|w), p(.|w e^{delta X}))/delta`, `delta = 0.2 rad`, geodesic cost | W1 column (c4d's quantity, true law) |
| `Lam_xy` | `TV(p(.|w), p(.|w e^{delta X}))/delta` | smoothing constant (round 2, section 1) |
| `Jbar_xy` | half the sup over `v` of the change of the centre log-odds `log p(v|.)/p(-v|.)` under the flip of `w` | c8a's `Jbar_P` (block level 1): H_sat needs `18 tanh(Jbar) < 1` |

Columns: `c = sum_y C_xy` over measured pair classes times their multiplicities (18 plaquette partners: classes s<-ss (12), s<-ts (2 spatial +
4 temporal), t<-ts (6 temporal + 12 spatial); 90 rectangle partners in their symmetry classes; two classes at coarse distance 2 to bound
the tail); the 2x2 type matrix and its spectral radius (weighted form, as in N2 post-hoc).

## 2. Points, backgrounds, controls

* **Primary:** SU(2), `beta = 2.3`, `b = 8`, `L sqrt(sigma) = 2.80` (c3b's only content-PASS point; c4d's certified fit).
* **Secondary (only if the timing allows and the primary is not decisive):** a larger `L1` with content: `beta = 2.3`, `b = 12`
  (`L sqrt(sigma) about 4.2`) on a fine lattice large enough for coarse 6^4 (72^4), with c3b's content check (>= 3 sigma) run first. The
  existing larger-`L` fits (2.92, 4.13, 5.60) failed the content check, so their small columns (N2: 0.89, 0.62, 0.55) are noise-limit
  suspects; no verdict is drawn at a point without content.
* **Backgrounds** (all other coarse variables in the region and the fine outside): (a) 8 typical ones, sampled from the unconstrained
  ensemble; (b) extremes: block-flat (`V = 1` around `x`), random Haar coarse data, a centre twist through the plaquettes of `x`, and
  large coarse curvature (coarse plaquettes near `-1`). Fine outside: taken from the sampled configuration of the background; UV-bad
  outsides are excluded by construction (they are handled by the pattern-conditioned assembly, ROUND2.md section 2).
* **Controls (gates; no SU(2) verdict unless both behave):** U(1) `beta = 1.1` (Coulomb, same blocking): predicted centre-flip column
  `> 2` (the photon propagates: FAIL expected); 2I `beta = 6` (c8b's tie point): predicted at least one pair with `C > 0.5` (frozen
  sectors). A CPU pilot at SU(2) `beta = 0.5` on a small lattice (where the blocked conditional law is close to the fitted plaquette form)
  must reproduce the N2 quadrature for the fitted couplings within 2 sigma. **Estimator test** (separate from the physics): the same
  sampler and fit run on the **fitted coarse plaquette action itself** (sampled exactly, coarse lattice, no blocking), where the single-link
  conditional law is known in closed form; agreement within 2 sigma is required before any blocked run.

## 3. Method (constrained sampling)

* **Region.** The fine links of the coarse cells within coarse distance 2 of `x` (for `b = 8`: a 40^4 fine region minus the frozen
  outside layer); everything outside the region frozen at the background's fine configuration.
* **Constraint.** All coarse variables `V_y` in the region except `V_x` constrained to prescribed values `w_y` by a penalty
  `kappa_c sum_y (1 - (1/2) Re tr(V_y(U) w_y^dagger))` added to the Wilson action; `kappa_c in {100, 200, 400}`, linear extrapolation in
  `1/kappa_c` (the penalty width must be well below the scale on which `p(v_x | .)` changes; checked by the extrapolation slope).
* **Sampler.** HMC on the fine links of the region with the penalty force (the block variable's derivative through the smearing and the
  SU(2) projection, as in `goodblock.py`), `B = 64` independent chains in parallel on the GPU per ensemble; integrated autocorrelation of
  the `V_x` moments measured per ensemble.
* **Density estimate.** Maximum likelihood fit of `log p(v_x)` in SU(2) characters/Wigner functions up to `j = 1` (13 coefficients;
  `j = 3/2` added as a check), TV and KR computed from the fitted densities by quadrature (the N2 code), errors by blocked bootstrap over
  chains. Precision target: pair TV to `+-0.004` (1 sigma), i.e. column to about `+-0.05`; from the Fisher information of the
  `j = 1/2` coefficients (`Var = 4/N` per component near uniform) this needs about `N_eff = 2.5 x 10^5` effective samples per ensemble.
* **Ensembles per (background, pair class):** `w`, `-w`, `wR`, `w e^{delta X}` (4); `kappa_c`: 3 values for the primary typical
  backgrounds and the plaquette classes, 1 value (`kappa_c = 400`) elsewhere. For the single-`kappa_c` ensembles the penalty bias is
  taken as the largest extrapolation shift `|C(400) - C(infinity)|` seen in the 3-value ensembles of the same class type and added to
  the systematic error.

## 4. Predictions and verdicts (fixed before any data)

Fit predictions (N2 diagnostics, fitted action): `C(s<-ss) = 0.074`, `C(s<-ts) = 0.023`, `C(t<-ts) = 0.023`; sharp column 1.02, spectral
radius 0.96; `c0` column about 0.02 (N1, crude; the sharp value is smaller); W1 column 0.73 (plaquettes) / 0.964 (with the rectangle,
c4d); Lam column 0.51/rad; rectangle class: W1 `k_R = 0.00255` per pair (c4d, 90 pairs: +0.23), sharp TV estimate `0.424 b_R = 0.0036` per
pair (90 pairs: about +0.32 to the sup column; an estimate, not computed in N2).

* **H_adj(L1):** PASS if the max over backgrounds of the `C0` column is `< 0.1` (upper 2-sigma); FAIL if `> 0.5`.
* **H_prop(L1), sup form:** PASS if the spectral radius of the max-over-backgrounds type matrix (plaquette + rectangle classes, plus the
  distance-2 tail) is `< 0.95` (upper 2-sigma); FAIL if `> 1.05` (lower 2-sigma); otherwise UNDECIDED. A PASS is "max over listed
  backgrounds and moves", not a sup. **Expected outcome at 2.80: UNDECIDED or FAIL** (fit: 0.96 plaquettes only, plus about 0.3 from the
  rectangle). Deciding a value near 0.96 needs about `+-0.02` on the column, six times the samples of section 3: not planned; the
  sup form is decided only if the true value is far from the fit.
* **H_prop(L1), W1 form + smoothing:** PASS if the W1 column (plaquette + rectangle + tail classes) is `< 0.9` (upper 2-sigma) and the
  Lam column is finite; FAIL if `> 1.05` (lower 2-sigma); otherwise UNDECIDED. This is the **decisive quantity at 2.80**; then the round-2 count
  `kappa_Ham <= K_s (col_TV + Lam_col pi c_W/(1 - c_W))` is evaluated with the measured numbers (K_s from the measured class matrix).
* **H_sat (block level 1):** report `18 tanh(Jbar)` (max over backgrounds); c8a's criterion `< 1`.
* **Tail:** rectangles are part of every verdict (they are not a tail: c4d's fitted `b_R` is a real coupling). If the distance-2 classes
  add more than 0.1 to a column, that verdict is void and the next shell is required.
* **Noise-limit rule:** a verdict is drawn only at a point with c3b's content PASS, with the block variable for which the UV term is bounded.

## 5. What a result would and would not show

A PASS of H_adj and H_prop (either form) at 2.80 is numerical evidence that the true coarse conditional specification at `L1` satisfies the
single-site hypotheses of c9b section 1.3 at the tested backgrounds; it is not a proof (finite backgrounds, finite `kappa_c`, finite
statistics), and the two-level coupling's UV terms (`b_UV`, `C_UV`) are not measured here. A FAIL of the sup form with a W1 PASS sends the
route to the W1-plus-smoothing count. A FAIL of both at a point with content is the first real obstruction for the one-box route at that `L1`.

## 6. Timing plan (before any production)

1. **CPU pilot** (separately pre-registered; short): the full pipeline at SU(2) `beta = 0.5`, a 16^4 lattice, `b = 4`, two backgrounds,
   one pair class; checks of section 2's pilot gate and of the TV/KR estimators against N2's quadrature.
2. **One timing job on the GPU** (after the owner's OK for this job alone): the primary point, one typical background, class s<-ss,
   `w` only, `kappa_c = 200`, `B = 64` chains, 30 minutes wall. Record: wall time per trajectory, acceptance, `tau_int` of the `V_x`
   moments, GPU memory. Output `t_eff` = wall seconds per effective sample.
3. **Projection** = `t_eff x N_eff x (number of ensembles)`, with `N_eff = 2.5 x 10^5` and the ensemble count:
   primary: 3 plaquette classes x 4 values x (8 typical backgrounds x 3 `kappa_c` + 4 extremes x 1) = 336, plus 12 backgrounds x 8
   further classes (rectangles, tail) x 4 x 1 = 384: **720 ensembles**; controls U(1) and 2I: 2 backgrounds x 3 classes x 4 x 1 = 24 each;
   secondary point: as the primary. Reported to the owner as GPU-hours per block, with a staged plan:
   **Stage A** (decisive subset): 4 typical + block-flat backgrounds, plaquette classes, all 4 values, `kappa_c` 2 values: 120 ensembles,
   plus the rectangle classes at the same 5 backgrounds, `kappa_c = 400`: about 120 more (rectangles enter every verdict);
   **Stage B**: the rest of the primary; **Stage C**: controls; **Stage D**: secondary point. Each stage needs its own OK.
4. If `t_eff` makes Stage A exceed 24 GPU-hours, the precision target is relaxed to column `+-0.1` (a factor 4 fewer samples) and the
   UNDECIDED band widened accordingly, decided before Stage A starts.

## 7. Code (not written)

New: `constrained.py` (penalty HMC on a region of `docs/mass-gap/lattice/boundary.py`'s `Box`, the block variable and its force from c3b's
`goodblock.py`), `condlaw.py` (character fit, TV/KR by the N2 quadrature, bootstrap), `queue_condlaw_gpu.ps1`. Reused unchanged:
`docs/mass-gap/lattice/`, `c3b-refit/goodblock.py`, `c8b-decisive/tiecore.py` (2I updater).
