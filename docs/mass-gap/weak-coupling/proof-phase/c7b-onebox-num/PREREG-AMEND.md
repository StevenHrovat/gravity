# Amendment to PREREG.md: the criterion Q(ell) of c7c-onebox (2026-11-22, before any production data)

`PREREG.md` stays as written. This file replaces its sections 1 (mapping), 4 (verdict rules) and the S_est estimate by the statement of
`weak-coupling/proof-phase/c7c-onebox/NOTE.md` section 1-3 (the Lean criterion), and adds the tie backgrounds. Code: `onebox.py`
(amended, analysis keys `Q_LB`, `Q_cell`, `tie`), queue: `queue_onebox_gpu.ps1` (amended, not started). Nothing in `lattice/` is changed.

## 1. The quantity (Lean NOTE, section 1-2)

    Q(ell) = (1 / ell^4) * sum over outside cells u of kappa(u),    criterion Q(ell) <= gamma_0 < 1,

cell = one correlation length (side n lattice sites), ell the box side **in cells**, kappa(u) = expected number of box cells that must
differ (modulo interior gauge) under the best coupling of two boundary conditions that differ in the single outside cell u, supremum over
boundary conditions. Gauge differences do not count (closed loops are gauge invariant; gate G0 below).

## 2. Three measurements

**(L) Rigorous lower bound, conclusive FAIL only.** For two boundary conditions that differ in at most one cell per shell position
(a whole-face centre flip, a patch, hot / typical / twist / flux against calm, the tie pair below: all qualify) and range-one observables
O_x localised in single box cells (O = (1 - W)/2 for a Wilson loop W in [-1, 1]; U(1) odd: (1 + sin)/2; cell average of the loops in
the cell, range one):

    sum_u kappa(u)  >=  sum over box cells x of | E O_x(sigma) - E O_x(sigma') |,
    Q_LB(ell) = (1/ell^4) * sum_x |Delta E O_x|   (cells = lattice sites here: the ratio does not depend on the cell side n, because a
    cell average has the same shift and there are n^4 times fewer cells, as is ell^4).

Implementation: per depth d the depth-pooled shift (a lower bound for the sum of the per-site |shifts|) times the number of sites at that
depth, for the best of the 1x1 loop, 2x2 loop (and odd sin for U(1)) at that depth, summed over the **whole depth profile**; the 3-sigma
lower value is used for the verdict. **Rule L: FAIL (conclusive) at that box size iff Q_LB - 3 sigma > 1.** The rule can never certify a
pass.

*Honest expectation, written in advance:* closed-loop observables localised in cells can only register the cells where the boundary
change leaves a trace. For a hot or typical boundary against calm that is the boundary layer; for a **thin vortex sheet** it is the
cells the sheet passes through (about ell^2 of ell^4), and for the photon the linear response falls like ell^-2 (pilot: Q_LB 0.05-0.10 at
ell = 4-6 and falling). So Rule L will very likely **not** fire for any model here, including the ones that must fail; its pilot values are
0.0003 to 0.10, all far below 1. The failure of the discrete groups and of the photon is therefore *not* expected to be detected by (L); it
is a theorem of the Lean note ((T) and (P)) and appears numerically only in (D) and (T) below. (L) is run because it is the rigorous
direction and because it costs nothing extra: it uses the runs of (D).

**(D) Diagnostics (evidence, not bounds).**
- *Cell-influencer estimate:* the patch of side b = 2 (one cell of side 2, all its tangential face links flipped) is the influencer, **no
  division by the patch size is made for the sum, only the cell count of the Lean formula**:
  Q_cell(ell; b) = 8 (ell/b)^3 * K / (ell/b)^4 = 8 K / (ell b^3)   with K = (1/b^4) sum_x |Delta E O_x| the number of box cells moved by that
  one cell (central values; the noise floor biases it upward, conservative). It assumes every shell cell has the influence of the
  face-centre cell: an estimate of the sum, not a bound. The old S_est (division by the patch size inside a linear-response guess) is
  kept in the output only as `S_est`, marked superseded.
- *Extreme-pair persistence* (rule E of PREREG.md: centre influence of hot / typical / twist / flux against calm across ell; exponential
  against power-law fit, needs three sizes).

**(T) Tie backgrounds (the test 2I and deconfined Z2 must fail).** Boundary data of two thin centre-vortex sheets (twist data twice: flux
pi on a single xy plaquette, Dirac strings over all z and t faces) at the xy positions x = c -/+ s, y = c, s = ell/4. The interior can
host the two sheets flat (area 2 ell^2) or joined into a tube along the walls (area about 8 ell s): at s = ell/4 the two topologies have
equal area, the tie. The tie breaker is **one shell cell**: one frozen link of the +s Dirac string on the face y = 0 (a link that sits in
plaquettes with dynamic links) is flipped, and the shift of the **frustration indicator** (the xy plaquette at the two sheet positions, deep
(z, t) slices, O = (1 - plaquette)/2) is measured. Reported: base frustration (0 = tube, 1 = flat sheets), the shift per slice, and
Q_LB_tie = 2 n_slices |shift| / ell^4 (rigorous direction, tiny, about ell^-2 for the same reason as above).
*What the tie does and does not measure:* the shift is the total variation of the sheet-position indicator under one shell cell. Moving the
sheets changes about ell^3 cells (Dirac volume) in the coupling metric but only about ell^2 cells in any localised closed-loop observable;
the ell^3 is the combinatorial step of NOTE section 5 (T) (classical estimate, not simulated). So a bistable tie with a shift of order 1 at
every ell is the numerical signature that the Lean mechanism (T) applies; it is not by itself a bound. Run for Z2 beta 0.6 and 0.3
(controls) and SU(2) beta 2.3, 2.5 (test).

**(U) Upper bound (optional, later; not implemented, not in the queue).** Two coupled heat-bath chains with the gauge-aligned maximal
coupling of NOTE section 3.4: per interior site a gauge label h_x, staple of chain 2 aligned S'' = h_y^-1 S' h_x, maximal coupling of the
two heat-bath laws, count of cells with a link U' != h_x U h_y^-1; the labels are re-chosen on the running pair. It bounds kappa from above
and is the only measurement that can support a pass. `boundary.py couple` (plain shared random numbers, relative Landau alignment as a
post-processing step, link distance) is **not** used: it inflates the count (NOTE 2.2), which is a likely reason the earlier link-level
k_hat grew with ell. Needs the maximal coupling of the SU(2) staple laws (one-dimensional in x0 plus a direction alignment); a separate
piece of work, to be pre-registered with its own box sizes (about 8 cells of side 2 to 3, the order of one correlation length).

## 3. Runs (queue)

As in PREREG.md section 3 with these changes: twist runs only as the extreme pair against calm (no whole-face flip on twist); tie runs
(tie, tie with the tie breaker) added for SU(2) at every box size and for Z2 at ell = 6, 8, 10; SU(2) beta 2.3 with 6 chains x 600
measurements, beta 2.5 with 4 x 400, strong coupling 4 x 400 (to keep Tier 1 near 4 h). Unchanged: calm / typical / hot, patches b = 2 and
ceil(ell/2), whole face, the gauge-control run, U(1) beta 2 (calm, flux), Z2 0.6 and 0.3 (calm, twist).

**Runtime (queue dry run).** GPU (SU(2), 1.5e-6 s per site, chain and measurement): **Tier 1 4.0 h, Tier 2 7.0 h, +/- 50 %** (123 and 138
GPU jobs, run one after another); CPU controls, 96 jobs, 4 at a time: 1.5 to 2.5 h wall beside the GPU.

## 4. Verdict rules, re-derived for Q(ell)

**G0 (instrument gate):** gauge-control runs: max_d |shift|/error < 4 in every group. If it fails nothing else counts.

**Rule L:** conclusive FAIL if Q_LB (3-sigma lower) > 1 for any pair or tie run at any ell. Otherwise: "no violation found by the lower
bound" (this is not a pass).

**Rule Q (estimate):** per (group, beta, background), Q_cell(b = 2) at the largest and the second-largest ell:
FAIL-indicated if Q_cell(ell_max) > 1 or Q_cell(ell_max) >= Q_cell(ell_prev); "no violation found" if Q_cell(ell_max) <= 0.5 and <= half
of the previous value; otherwise INCONCLUSIVE. (A single box size cannot show shrinking: INCONCLUSIVE unless Q_cell is below 0.5 with
one size, reported as such.)

**Rule E:** as PREREG.md (extreme pair; three sizes to separate exponential from power law; FAIL-like if the centre influence is >= 0.1,
resolved, and not falling by 2 (or a power law fits better); PASS-like if unresolved or an exponential fits better and falls by 2).

**Rule T:** per (group, beta): |tie-breaker shift| >= 0.1, resolved at 3 sigma, and not falling by 2 between the two largest ell: "tie bistable,
FAIL-indicated through NOTE (T)"; shift unresolved or < 0.02: "tie not decided by one cell"; otherwise INCONCLUSIVE.

**Controls (gate C):** Z2 beta 0.6 must be FAIL-like under E (twist) and tie bistable under T; Z2 beta 0.3 PASS-like under E and "not decided"
under T; U(1) beta 2 FAIL-like under E (needs its four sizes: power law); strong-coupling SU(2) beta 0.8: no conclusive FAIL, Q_cell "no
violation found", E PASS-like. Rule L is *not* expected to fire for the controls that must fail (see the expectation in section 2): its
control is that it does not fire for the passing anchors. If a control is wrong, SU(2) numbers are not evidence either way.

**SU(2) report (not a gate):** *conclusive violation* iff rule L fires for SU(2); *violation indicated* iff rule Q, E or T gives FAIL-indicated
at l sqrt(sigma) >= 3 on a beta with the gates passed; *no violation found among the extremes tried* iff none of the rules does, with
Q_cell and the tie shift shrinking across beta 2.3 / 2.5 at equal l sqrt(sigma) within a factor 2; otherwise not decided. No numerical
outcome of (L), (D) or (T) is a pass certificate; only (U), if built, supports a pass, and only for the sampled boundary conditions.

## 5. Caveats (additions to PREREG.md section 5)

1. The lower bound (L) is far from the criterion for sheet-like and long-range responses (ell^2 or ell^-2 against ell^4); expect it to stay
   below 1 everywhere.
2. Q_cell assumes all shell cells behave like the face-centre cell and uses one boundary condition family; it is an estimate in both
   directions. The cell side b = 2 may be below or above the true correlation length at a given beta (xi about 0.8-1 lattice unit at
   beta 2.3, about 2 at beta 2.5, from the earlier influence profiles); the patches b = ceil(ell/2) are kept as a linear-response check.
3. The tie is built for a cube with frozen faces; the two sheet topologies are equal only up to lattice corrections (the base frustration
   shows which one the heat bath prefers at each ell, a switch is first order and slow: long autocorrelation, large errors expected).
4. Everything else of PREREG.md section 5 (finite sampling of boundary conditions, observables are lower bounds on influence) stands.

## 6. Pilot of the amended pipeline (CPU, ell 4-8, 100-300 measurements: **PILOT, not data**)

Old runs of PREREG.md section 6 reused, plus ten tie runs (`tie-pilot/`); analysis in `pilot-analysis-amend.txt/json`.
- **Gate G0** passes (max 1.5 sigma over five groups). Selftest passes.
- **Q_LB (rule L) is tiny everywhere**, as predicted in section 2: SU(2) beta 2.3 typical vs calm 0.040 (ell 6), U(1) beta 2 flux 0.095 (ell 4)
  and 0.053 (ell 6), Z2 beta 0.6 twist 0.025 and 0.014, Z2 beta 0.3 about 0.001, SU(2) beta 0.8 0.009; Rule L does not fire for any model.
- **Q_cell (b = 2), ell = 4 only:** SU(2) beta 2.3 calm 0.46, typical 0.26; beta 0.8 0.02; Z2 0.6 0.63; Z2 0.3 0.47; U(1) 0.53 to 0.71
  (one size: no shrinking can be judged; the noise floor biases these upward at ell = 4).
- **Extreme pairs, rule E:** Z2 beta 0.6 twist 0.79, 0.82 (FAIL-like, as required); Z2 0.3 about 0 (PASS-like); U(1) flux J_centre 0.73, 0.34 with
  two sizes: INCONCLUSIVE, as designed (the production run has four sizes).
- **Tie runs: plumbing works, the test does not yet.** Two defects found, to be fixed before the tie result is read:
  (a) the tie breaker as built (one Dirac-string link on the face y = 0) shifts the indicator by 0.000 +- 0.003 in every model: it changes the
  endpoint of both sheet topologies equally, so it does not favour one of them; a breaker that does must change the area difference of the
  two topologies by O(1), e.g. a one-cell kink that shortens only the flat sheet's boundary loop;
  (b) a heat bath cannot tunnel between the two sheet topologies in the deconfined phase (an area-law barrier): Z2 beta 0.6 at ell = 8 sits in the flat-sheet
  state (frustration 0.94) while at ell = 6 (where the tube is smaller, 0.13) it stays in the tube; the interior sector is chosen by the start,
  not sampled, so the shift of the law under the tie breaker cannot be read from one run. Needed: start the interior from both topologies
  and compare free energies (tempering or a multicanonical weight on the sheet area). Until then the tie rows of the queue are run as a
  **stickiness diagnostic** (the verdict text says "not sampled" when the indicator never switches) and they are **not** a control gate.
  The queue uses independent seeds for the two tie runs; the analysis uses the larger of the paired and the independent-pair error
  everywhere (shared random numbers merged deconfined Z2 pairs exactly, paired error 0, which would have counted a zero as resolved).
