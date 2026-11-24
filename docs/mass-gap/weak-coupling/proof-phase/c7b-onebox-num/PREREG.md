# Pre-registration: numerical test of the one-box, worst-case-boundary criterion (c7b-onebox-num, cycle 7, 2026-11-22)

**Status:** written before any production data. The CPU pilot (tiny boxes, section "Pilot") only tests the pipeline and the controls;
its numbers are labelled pilot and decide nothing. Code: `onebox.py` (reuses `lattice/boundary.py` and `lattice/analyse_boundary.py`
unchanged). GPU plan: `queue_onebox_gpu.ps1` (not started). Rules of `weak-coupling/attempts/RULES.md` apply (photon and Z2 unit tests,
claim discipline, CPU-only pilot, no GPU, no change to lattice/).

## 1. What is tested, and how it maps to the criterion

The criterion (template: Dobrushin-Shlosman C_V; Martinelli-Olivieri; see `c7d-onebox-lit/LITERATURE.md`; Lean statement in
`c7c-onebox/` when it appears): for a box V of fixed size, with the outside replaced by a boundary condition B,

    C_V = sup over B, over single boundary sites y, of  W(law_B, law_B')  (B, B' differing at y), summed over y in the boundary,
          compared with |V|:    sum_y k_V(y) <= gamma |V|,   gamma < 1,

which in the project's notation is the GDS ratio R(ell) = sum_{y in dV} k_V(y) / |V| of `BLUEPRINT-REDUCTION.md` (the instrument of
`lattice/PREREG-BOUNDARY.md` measured it with coupled chains for the calm boundary only). If the Lean workstream states it differently
(e.g. interior depth, a decay weight e^{m d}, a different distance) the map is: the same measured quantities J(d, patch, ell) below, summed
with the weights of its statement; the instrument does not depend on the choice.

**What a simulation can and cannot give.**
1. The boundary-site influence is a *supremum over all boundary conditions*; a simulation samples a handful of them (the extremes below).
   A pass is therefore only "no violation found among the extremes tried", never a proof of the worst case. A **fail** (a boundary pair that
   shows long-range influence or a surface-count sum above 1) is conclusive for that box and that observable class.
2. Interior observables give *lower bounds* on the influence (|shift of E f| <= osc(f) * TV, and <= Lip(f) * W1). A small observed shift
   does not bound the Wasserstein distance of the whole interior law. We use one-loop and two-loop Wilson loops, the most sensitive
   gauge-invariant local observables available; the claim is "consistent with", not "implies".
3. The Wasserstein distance of the link configurations (what the coupled chains of `boundary.py couple` upper-bound) is already known from
   Leg B: the coupled single-link estimate k_hat grows with ell (SU(2), beta 2.3: 3.4, 8.9, 21 at ell = 4, 6, 8; R_face 6.8, 10.7, 18 > 1),
   because the pair of chains is not contractive on the scale of the correlation length at these box sizes. It is therefore *not* repeated
   here; it is reported alongside as the known upper-side number (one lattice link as the boundary cell is far finer than the physical
   cell: the sum over cells beats 1 only for cells of the order of the correlation length). The present instrument measures the
   observable-level influence of **patches** of the boundary of growing size, which is the coarse-cell version.

**Gauge.** Boundary data matter only modulo gauge; all observables are closed loops of dynamic and frozen links, invariant under
gauge transformations of every site (interior, and boundary sites together with their frozen links). Instrument check built in:
`--pert gauge` multiplies the boundary data of a box by a random gauge transformation at the boundary sites; the measured influence on the
interior loops **must vanish within errors** (gate G0 below).

## 2. Measured quantities

Box: sites 0..ell in each direction, frozen face links (the boundary condition), dynamic interior, exactly as `boundary.py`
(`Box`), heat bath + overrelaxation (3 overrelaxation steps per heat bath, one measurement every 2 sweeps). Observables per measurement:
mean and mean square of the 1x1 and 2x2 Wilson loops, per plane, binned by **depth d** = smallest distance from the box boundary of the
loop's four corners (d = 0 touches the boundary; the deepest bin is the box centre), pooled over the six planes.

**Boundary conditions B (the sampled "worst cases"):** calm (all links 1, cold); typical (frozen face of an equilibrium periodic
configuration, one per chain); hot (Haar random frozen links, a random frozen boundary); twist (one thin centre vortex through the box,
`boundary.py`); flux (uniform flux Phi through every cross-section: SU(2) centre element, U(1) 2 pi). (SU(2) gets all five; U(1) calm and
flux; Z2 calm and twist.)

**Boundary changes (pairs):**
- *whole face*: centre flip of all tangential links of the face x = 0 (SU(2): link times -1; U(1), Z2: angle + pi). The "centre-flipped face".
- *patch of side b* at the face centre (b = 2 and b = ceil(ell/2); b = 1, one boundary cell = the three tangential links of one site, is
  noise limited and is run only in the pilot and, if time, with many more measurements): influence vs the number of changed cells.
- *different backgrounds* (hot, typical, twist, flux versus calm): pairs differing on the whole boundary.
- *gauge control*: calm and calm re-gauged (gate G0).
Pairs share the seed: same boundary, same random-number streams, so errors are taken from blocks of the paired difference.

**Influence.** shift Delta(d) = mean loop(perturbed) - mean loop(base), blocked errors (at least 20 blocks, blocks inside chains).
Normalised influence **J(d) = |Delta(d)| / s(d)**, s(d) the standard deviation of a single loop at that depth in the base run. For small shifts
the total variation of the single-loop law is about 0.4 J (exact for a Gaussian); this is an estimate, not a bound.

**Surface-count (Dobrushin-Shlosman-type) estimate at depth d, from a patch run of b^3 cells:**

    S_est(d, ell) = 8 (ell + 1)^3 * 0.4 * J(d; patch) / n_cells(patch),

eight facets of (ell + 1)^3 sites; linear response in the number of cells (influences of different cells add; screening makes this an
over-estimate for large patches). It compares directly with 1 and with gamma. The centre depth (deepest bin) is the reported value, the
profile S_est(d) is reported in full. Physical depth: d * a sqrt(sigma) (a sqrt(sigma) from `results/ttl_summary.json`).

**Decay length** xi: weighted fit of ln |Delta(d)| over the leading run of 3-sigma points from d = 1 (`analyse_boundary.exp_fit`); physical
xi * a sqrt(sigma). **Scaling with ell:** centre J against ell: exponential fit (rate kappa) versus power-law fit (exponent p); chi^2 of both.

## 3. Runs

Boxes of fixed physical size l * sqrt(sigma) = 2 to 4.4 (a sqrt(sigma): 0.350 at beta 2.3, 0.182 at beta 2.5, from the TTL scan):

| group | beta | ell | l sqrt(sigma) | chains x meas | role |
|---|---|---|---|---|---|
| SU(2) | 2.3 | 6, 8, 10, 12 | 2.1, 2.8, 3.5, 4.2 | 8 x 600 | test |
| SU(2) | 2.5 | 11, 15 (19 in Tier 2) | 2.0, 2.7 (3.5) | 4 x 400 | test (second beta: scaling in sqrt(sigma)) |
| SU(2) | 0.8 | 6, 8, 10 | strong coupling | 4 x 600 | anchor (must pass) |
| U(1) | 2.0 | 4, 6, 8, 10 | Coulomb photon | 4 x 400 | control (must fail) |
| Z2 | 0.6 | 4, 6, 8, 10 | deconfined, gapped | 4 x 400 | control (must fail) |
| Z2 | 0.3 | 4, 6, 8, 10 | confined | 4 x 400 | control (must pass) |

Per (group, beta, ell) and background: unchanged, b = 2, b = ceil(ell/2), whole face; on calm also the gauge control. SU(2) test boxes:
calm, typical, twist, hot (hot and twist: unchanged and whole face only). 200 thermalisation sweeps, typical stage 300 periodic sweeps.

**Runtime.** GPU (SU(2), fused kernels, 1.5e-6 s per site, chain and measurement, from `lattice/PREREG-BOUNDARY.md`; dry-run of the queue
prints the sum): **Tier 1 about 4.2 h, Tier 2 about 6.8 h, each +/- 50 %**; the GPU jobs run one after another. CPU controls (84 jobs, 4 at a
time, beside the GPU): from the pilot (U(1)/Z2 about 0.11 s per sweep at ell = 6, scaling with the number of sites) about
5.5 CPU-hours, so **1.5 to 2.5 h wall** at 4 in parallel. If the GPU is shared the numbers are upper bounds. Cheapest cuts: drop hot (about 15 %),
drop beta 2.5 ell 19 (Tier 1), halve measurements at beta 2.5.

## 4. Verdict rules (fixed now)

**G0 gauge gate (instrument):** every gauge-control run has max_d |Delta(d)| / error < 4 (the maximum over about 3-6 depths of a standardised
Gaussian; a value at 4 or more is a failed gate). If G0 fails nothing else counts.

**Per (group, beta, background family)**, with ell from small to large, taking at each ell the smallest patch whose centre influence is
resolved (J > 3 errors); if none is resolved, the 3-sigma upper limit from the whole-face run:
- **PASS-like:** S_est(centre, ell_max) <= gamma = 0.5 **and** S_est(centre, ell_max) <= 0.5 * S_est(centre, ell_prev) (the surface sum is
  shrinking at least by a factor 2 per box-size step). With only upper limits: PASS-like if all limits are <= 0.5.
- **FAIL-like:** S_est(centre, ell_max) > 1, **or** S_est(centre, ell_max) >= S_est(centre, ell_prev) (the surface sum does not shrink with the box).
- otherwise INCONCLUSIVE.
Reported next to it: exponential vs power-law chi^2 of centre J(ell); xi(d); the profile.

**Controls (gate C):** U(1) beta 2 must be FAIL-like (on flux and on the patch family) and its centre J must be better fitted by a power law
than by an exponential; Z2 beta 0.6 on the twist background must be FAIL-like (pinned vortex); Z2 beta 0.3 and SU(2) beta 0.8 must be
PASS-like or PASS-like with upper limits. If any control gives the wrong verdict, the SU(2) numbers are not evidence either way (the
instrument does not separate gapped-and-confining from the failures), exactly as the photon gate of `PREREG-BOUNDARY.md`.

**SU(2) result (reported, not a gate):**
- *numerically consistent with the one-box criterion* iff every SU(2) test family is PASS-like at both beta, with the beta 2.3 and beta 2.5
  surface sums at equal l sqrt(sigma) within a factor 2 (scaling in physical units), and the controls pass gate C;
- *numerically violated* iff some SU(2) family is FAIL-like at l sqrt(sigma) >= 3 on at least one beta, with the control gates passed;
- otherwise *not decided at these box sizes* (the likely outcome if the criterion needs boxes beyond l sqrt(sigma) = 4.4).
In every case the sentence "a simulation samples the extremes it was given, it does not prove the worst case" accompanies the verdict.

## 5. Caveats written in advance

1. Finite sampling of "all boundary conditions" (see section 1). A boundary the sampler never saw could be worse; in particular a boundary
   engineered adaptively against the interior (the true supremum) is not searched.
2. Observable-level influence is a lower estimate of the Wasserstein/TV influence; S_est converts it by a Gaussian rule of thumb and a
   linear-response extrapolation in the number of changed cells. It is an estimate, not a bound, in both directions.
3. The calm boundary is cold and the interior is thermalised from it; the whole-face centre flip is a dense vortex layer (every plaquette
   touching the face changes sign) that the interior cannot remove (the layer can move inward at no action cost but a heat bath moves it
   slowly); readings at d >= 1 of the whole-face flip include that pinned layer. Patches are the cleaner measurement.
4. Strong-coupling SU(2) at beta 0.8 and Z2 at beta 0.3 have correlation lengths of about one lattice spacing, so their patches are
   unresolved beyond d = 1 or 2; their verdict will often rest on upper limits.
5. Box sizes l sqrt(sigma) <= 4.4 may be smaller than the scale at which the surface count is beaten.
6. U(1) beta 2 is deep in the Coulomb phase; the compact U(1) flux flip is not a centre element and is an extreme change, not a gauge-group symmetry.

## 6. Pilot results (CPU, tiny boxes ell = 4 and 6, 120-300 measurements, 4 chains: **PILOT, not data**)

Run with `python onebox.py pilot` (6 processes, `CUDA_VISIBLE_DEVICES=-1`, about 8 minutes wall for 46 runs, plus a 2-minute rerun of the
U(1) runs after adding the odd observable); output in `pilot-runs/`, `pilot-analysis.txt`, `pilot-analysis.json`. Self-test (`onebox.py
selftest`): loops equal `boundary.py`'s plaquettes to 0, interior gauge invariance 1e-16, face-flip touches exactly the expected 540 links.

- **Gate G0 (gauge control) passes in every group:** max |shift|/error 0.8 to 1.6 (SU(2) 2.3, U(1), Z2 0.3, Z2 0.6).
- **Z2 separates gapped-deconfined from confined (extreme pair twist vs calm, centre of the box):** beta 0.6: J = 0.79 (ell 4), 0.82 (ell 6),
  not decaying (FAIL-like, as required); beta 0.3: 0.006, 0.001 (PASS-like).
- **U(1) beta 2 (photon):** the flux pair shows the field at the centre with no decay with depth (ell 6: J = 0.36, 0.33, 0.34 at d = 0, 1, 2)
  and J_centre 0.73 (ell 4), 0.34 (ell 6), a fall of 2.2 for a size ratio of 1.5, i.e. the l^-2 of a free field. With two sizes the rule E
  cannot separate this from an exponential and says INCONCLUSIVE (as designed: the production run has four sizes). The even loops
  (cos) see the photon only at second order: the first pilot, with even loops only, showed no U(1) signal at all (J about 0.01); the odd
  observable sin(theta_p) was added for U(1) for that reason (the photon witness, as in `PREREG-BOUNDARY.md`).
- **SU(2) beta 2.3, typical versus calm:** J(d) = 0.49, 0.15, 0.05 at ell = 6, a clear fall with depth; patch influence at the centre
  unresolved at ell = 6 with 120 measurements. **SU(2) beta 0.8** (strong coupling): typical vs calm J = 0.085, 0.003 at ell = 4.
- **Verdict machinery:** with two box sizes every SU(2) family is INCONCLUSIVE except strong coupling (upper limits only: PASS-like) and the
  Z2 pair above; no SU(2) conclusion is drawn from the pilot (boxes of l sqrt(sigma) 1.4-2.1, far too small, ell = 4 has only two depth bins).
- Two defects found by the pilot and fixed before any production data: the first version took the "unresolved" upper limit from the
  whole-face run (invalid direction: sub-additivity bounds a patch from above, not a cell), now from the smallest patch; and the U(1)
  control lacked the odd observable. Rule E now needs three sizes to separate exponential from power law.
