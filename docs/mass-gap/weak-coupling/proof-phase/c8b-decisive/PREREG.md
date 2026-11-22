# Pre-registration: the decisive one-box measurement (c8b-decisive, cycle 8, workstream 2, 2026-11-22)

**Status:** written before any production data. Everything under "Pilot" (section 6) is a CPU pilot of the tools and decides nothing about
SU(2). Code: `decisive.py` (coupled chains and CLI), `tiecore.py` (tie test), queue `queue_decisive_gpu.ps1` (not started: the GPU belongs to
the running c7b queue). `lattice/` and `c7b-onebox-num/` are read, not changed. Rules of `weak-coupling/attempts/RULES.md` apply (photon and Z2
unit tests, claim discipline, CPU-only pilots, no GPU).

Quantity (Lean criterion, `c7c-onebox/NOTE.md`): `Q(ell) = (1/ell^4) sum_u kappa(u)`, criterion `Q <= gamma_0 < 1`; `kappa(u)` = expected
number of box **cells** (coarse links, 4 per site) that must differ, modulo gauge of the box interior, under the best coupling of two boundary
conditions that differ in one outside cell `u`; `ell` = box side in cells.

## 0. Results in one paragraph (read this first)

Both tools exist and are validated on cases with known answers, but the first one has a **hard limit that decides how the decisive test can
be used**.

1. **Upper bound (gauge-aligned maximal coupling).** Implemented exactly (single-link maximal coupling of the SU(2) and U(1) heat-bath laws,
   exact marginals and exact maximality checked, running Hamming-optimal gauge alignment of chain 2). Validation passes: identical boundaries
   give D = 0 exactly; a gauge-rotated copy is recovered exactly (D = 0) while plain coupling without alignment gives D = all cells; a pure-gauge
   boundary change gives D = 0 exactly once the gauge labels at the changed sites are allowed; at strong coupling (SU(2) beta = 0.1, U(1)
   beta = 0.05) D is local (D(r) = 0.65, 0.43, 0 cells at r = 0, 1, 2) and K saturates with the box; the photon (U(1) beta = 2) is saturated.
   **The limit: the Markov coupling needs Dobrushin-type contraction at the link level, and that fails above beta about 0.25 (SU(2)) and
   about 0.15 (U(1)): mismatches then spread over the whole box in a few sweeps and D saturates at all cells.** At SU(2) beta 2.3 and 2.5
   (every Tier-1 box, ell = 6 to 15) the bound is therefore **vacuous (D = all cells)**; it cannot certify Q < 1 there, and no larger box
   would help (a heuristic estimate, section 1.4, finds the branching of disagreements scale free at weak coupling; the pilot has beta 2.3 at ell = 6 and
   beta 2.5 at ell = 11, both completely saturated). What the tool can do is to give a bound with a
   clean surface-count floor at strong coupling (Q_U = 8 K / nc with K = 1.08, 1.36, 1.77 cells per boundary cell at nc = 3, 4, 6, tending to about 2,
   so Q_U < 1 needs about 16 cells per side even at beta = 0.1) and to measure where it stops working. A tool that bounds kappa at weak coupling needs coupling at the
   cell level (cell conditional laws), which is not built.
2. **Tie test (works).** Sheet geometry, a one-cell breaker whose effect on the log-odds of the two arrangements is O(beta), and a
   sampler that sees both arrangements: runs started from both arrangements plus thermodynamic integration of the breaker in each (ratio
   method), and direct occupation if the chain mixes. Validation: **Z2 beta = 0.6 (deconfined) shows the tie** (ell = 9: both arrangements
   persist, the breaker shifts the log-odds by 2.30 +- 0.02; tie strength tanh(delta/4) = 0.52); **Z2 beta = 0.3 (confined) does not** (the
   two starts are indistinguishable from the first measurement and the indicator switches about once per sweep and chain; delta = 0.06 +- 0.03). 2I: its sheets are at least five lattice units thick (section 2.5), so the thin-sheet indicator fails at beta 4 and ell = 9, and at beta 8 the
   chain is frozen; at **beta = 6, ell = 13 the pilot shows both arrangements persisting and clearly distinguishable** (loop indicator
   0.96 and 0.15, 80 sweeps, 2 chains), but the ratio-method run for 2I is not piloted (cost): the queue has it, and gate G6 for 2I rests on it.
3. **Pre-registered plan (sections 3, 4):** Tier 1 about 3 h GPU (assumed speed, factor 3 uncertain) plus about 2 h wall on 4 CPU workers (8 CPU-hours);
   verdicts fixed in section 4. The decisive SU(2) statement comes from the **tie test** and from the **saturation finding**, not from Q_U.

## 1. Tool 1: the gauge-aligned maximal coupling (upper bound)

### 1.1 Method

Two chains for the box (frozen faces = boundary condition, dynamic interior, `boundary.py`'s `Box`), chain 1 with boundary `sigma`, chain 2
with `sigma'` that differs in one outside cell: the tangential frozen links of one cell-sized patch of the face x = 0 (`flip`: centre element;
`rand`: fresh Haar links; `gauge`: control, a random gauge transformation at the sites of the patch, applied to every box link touching them).

* **Single-link law.** For a link with staple sum A the heat-bath law is `p(U) ~ exp(beta Re(U A))`, a von Mises-Fisher law on S^3
  (SU(2)) or a von Mises law on the circle (U(1)). `Law.coupled(A1, A2)` is the **maximal coupling** of the laws for two staples: draw `U1 ~ p1`;
  accept `U2 = U1` with probability `min(1, p2/p1)`; otherwise draw `U2` from the residual `(p2 - p1)_+` by rejection from `p2` with acceptance
  `(1 - p1/p2)_+ / a_max`, `a_max` its supremum (so the acceptance stays of order one when the laws almost agree). The normalisation `ln Z`
  is a periodic trapezoid sum (exact to rounding, checked against Bessel functions). Self-test: both marginals are exact (z-scores below 2.2 on
  4 x 10^5 draws), and `P(U1 = U2) = 1 - TV` to 0.0005 (SU(2) and U(1), nearly equal, far apart and identical staples).
* **Aligned frame.** Chain 2 is stored in the frame aligned to chain 1 (`W_e = h_x^-1 V_e h_y`): its staples are then exactly the aligned
  staples `S'' = h_y^-1 S' h_x` of NOTE section 3.4, no explicit labels are carried, and a **relabelling** of chain 2 (applying a gauge
  transformation to `W` at any time and as a function of the running pair) leaves the law of the true chain 2 untouched, because `V` itself is
  never modified. Chain 2 therefore keeps exactly its own heat-bath law whatever the alignment does; D bounds `d~` from above.
* **Alignment (`HamAligner`).** After every sweep, at every free site, replace the label by the best of the identity and the 8 rotations that
  make one incident link agree exactly, the best = largest number of agreeing links (the Hamming optimum, checkerboard passes, sparse). A
  Landau-type sum of distances (the `boundary.py couple` aligner) rotates agreeing links by small angles and inflates the cell count, so it is
  not used. Free sites = box interior (NOTE: the gauge group K of the interior); for the pure-gauge control also the changed boundary sites.
* **Count.** `D` = number of box cells with at least one disagreeing dynamic link (distance above 1e-7; agreement after a maximal-coupling
  success is bit exact). Cell = one coarse link: the fine links of one direction in one block of the partition of the site coordinates 0..ell
  into `nc` equal blocks (`ncell`), 4 nc^4 cells; cell side ell / nc (SU(2): 0.7 / sqrt(sigma): nc = ell/2 at beta 2.3, ell/3.7 at beta 2.5).
* **The one-box sum.** The changed cell runs over the cells of one face (a 3D grid of nc^3 cells), grouped into symmetry classes (sorted depth
  triples, multiplicities exact; one run holds every class, chains per class independent). `Q_U = 8 sum_classes mult * D / nc^4` (8 faces; edge
  and corner shell cells with no frozen link are not counted; for calm boundaries the classes are exact by symmetry, for random boundaries
  they are an average). `K = (sum mult * D)/(sum mult)` is the mean number of disagreeing cells per changed face cell; `Q_U = 8 K / nc`, the
  **surface-count floor**: each boundary cell disturbs at least its neighbouring cell, so Q_U >= 8 / nc and the criterion needs nc >= 9.
* **Equilibrium.** Chain 1 is thermalised alone (fast heat bath plus overrelaxation, `--pre`), then both run coupled for `--therm` sweeps
  before measuring. The coupled chains' marginals are exact at every time; the bound is valid once both marginals are stationary. Checked by the
  two halves of the measurement series (`Q_U_first_half`, `Q_U_second_half`; coded: their difference below 4.5 blocked errors of the full series).

### 1.2 Validation (CPU pilots, `pilot/`, SU(2) unless noted; numbers in section 6)

| test | expected | result |
|---|---|---|
| identical boundaries, same start | D = 0 | D = 0 exactly (beta 2.3, ell 6) |
| identical boundaries, independent start (beta 0.1) | coalescence, D = 0 | D = 152 cells -> 0 within 10 sweeps |
| identical boundaries, chain 2 = random interior gauge copy | D = 0 after alignment | D = 0 exactly; without alignment D = 324 of 324 cells |
| pure-gauge boundary change, labels at the changed sites | kappa = 0 | D = 0 exactly (beta 2.3 and 0.1) |
| pure-gauge boundary change, no labels (NOTE 3.2: boundary layer) | boundary layer only | beta 0.1: Q_U = 2.87, the same as a real change (the touching cells); beta 2.3: saturated |
| strong coupling beta = 0.1 | small, local, decaying with depth | D(r) = 0.65, 0.43, 0.00 (ell 6), 0.79, 0.57, 0, 0 (ell 8), 0.96, 0.80, 0, 0, 0, 0 (ell 12): nothing beyond r = 1; K = 1.08, 1.36, 1.77 (nc 3, 4, 6; Q_U = 2.88, 2.73, 2.36), K tends to about 2 as the interior cells (more neighbours) dominate |
| photon, U(1) beta = 2 | large, flat | saturated: K = 320 of 324 cells |
| U(1) beta = 0.05 / 0.1 / 0.2 | local / spreading / saturated | K = 0.72, 1.01 (ell 6, 8) / 1.97 / 147 of 324 |

### 1.3 The saturation finding (the limit of the tool)

Scan at ell = 6, one flipped cell, calm boundary (cells differing out of 324): beta 0.1: 1.1; 0.2: 4.5 (D(r) = 1.2, 2.9, 0.4: spreading);
0.3: 133 (41 %); 0.5: 271 (84 %); 0.8: 312; 1.5: 323; 2.3: 323 (100 %); `ell = 11, beta 2.5` is in the queue. Growth with the box near the
threshold (beta 0.2, K at ell = 6, 8, 12: 4.5, 5.9, 9.4, with D(r) = 1.7, 5.7, 1.6, 0.4, 0.04 at ell = 12: the disagreement cloud is several cells wide). At weak coupling, with the heat-bath kernel and with a coupled-Metropolis kernel (vMF proposals of concentration 40, 100, 300,
1 to 3 hits; overrelaxation not tried), the disagreement spreads to the whole box in 10 to 30 sweeps. This is a property of single-link
Markov couplings, not a bug: the gauge-copy, identical-boundary and gauge-boundary controls are exact.

### 1.4 Why, and what would help

A disagreement of size d at one link changes the staples of its 18 neighbouring links by about d; the heat-bath laws for the two staples then
differ by TV about `0.4 sqrt(beta) d / sqrt(k)` (k = |A| about 4 to 6; heuristic estimate, not measured separately); a failed maximal coupling leaves a disagreement of the order of the
link's own fluctuation `1/sqrt(beta k)`, so the expected number of new disagreements per old one is about `18 * 0.4 * sqrt(beta)/sqrt(k) *
1/sqrt(beta k)` = O(1) **independent of beta** (about 1.5 to 2 at weak coupling) and drops below one only at strong coupling. Smaller
disagreements (Metropolis with small steps) heal more slowly in proportion. The count is a property of the Hamming metric on links: a cell
holds n^4 links, and a link-wise coupling fails a cell about sqrt(n^4) times more often than a cell-level maximal coupling would. The tool
that would bound kappa at weak coupling is therefore a **cell-level coupling** (block updates with the exact conditional laws of a cell given
its surroundings, coupled maximally), which needs cell conditional sampling (nested chains) and is not built here.

## 2. Tool 2: the tie test (works)

### 2.1 Geometry (all groups)

Boundary data of two thin centre-vortex sheets (twist data twice): Dirac strings, flux pi on the xy plaquettes at `(x, y) = (c -/+ s, c)`,
`c = (ell - 1)/2`, continued through all (z, t). Two arrangements of the interior:

* **A, flat sheets:** the two sheets stay flat, frustrated xy plaquettes at the sheet positions for every (z, t): `2 (ell - 1)^2` dynamic
  plaquettes.
* **B, tube:** the dynamic y-links at `y = c`, `x = c - s + 1 .. c + s`, z and t in `1 .. ell - 1`, multiplied by the centre element: the sheets
  are joined into a tube along the four walls z, t = 0, ell (frustrated yz and yt plaquettes there): `8 s (ell - 1)` dynamic plaquettes.

Equal area (the tie) for `ell = 4 s + 1`: **ell = 5, 9, 13, 17, 21, 25** with `s = 1 ... 6` (checked by counting the frustrated dynamic plaquettes of the two initial states: 32 / 32, 128 / 128, 288 / 288, 512 / 512 at ell = 5, 9, 13, 17;
at ell = 15, s = 4 it is 392 / 448, not a tie; the c7b default `s = ell/4` was not a tie). Both arrangements are gauge-invariant
sectors; the sector indicator is `f = (1 - W)/2`, W the R x R Wilson loop in the xy plane centred on each sheet position, mean over the two
positions and over the deep (z, t) slices (R = 2 for Z2 and SU(2), 5 for 2I): a loop that encloses a sheet is negative, f above 1/2 for A,
below 1/2 for B.

### 2.2 The breaker (one cell, O(beta) effect on the log-odds)

One **frozen** link: the y-link on the face z = 0 at `(x, y, t) = (c, c, ell/2)`. Its only dynamic plaquette is the yz plaquette at that place,
which the tube passes (sector B) and the flat sheets do not (A); changing the link (centre element) flips the sign of that plaquette's action
term, so the free energy of A and of B change by opposite amounts `+-2 beta <Re P>`: for Z2 beta 0.6, 1.16 and -1.14. (The c7b breaker, a
Dirac-string link on the face y = 0, changed both arrangements equally: 0.000 +- 0.003.) It is one boundary cell.

### 2.3 The sampler: runs from both arrangements + thermodynamic integration (ratio method)

The breaker is interpolated, the frozen link replaced by the centre element rotated the fraction `lam` of the way (a continuous path of
boundary data; the same code for all groups, the frozen link need not be a group element). For each arrangement X and a ladder of `nodes`
equally spaced `lam` (warm-started from the previous node, `step_therm` sweeps to re-equilibrate, `meas` measurements):

    F_X(1) - F_X(0) = integral_0^1 <dS/dlam>_{lam, X} dlam   (Simpson),    delta = [F_A(1) - F_A(0)] - [F_B(1) - F_B(0)],

with `S = -beta Re P` of the one dynamic plaquette (the frozen-frozen plaquettes cancel in delta). `delta` is the **shift of the log-odds
ln(Z_B/Z_A) of the two arrangements caused by the breaker**; the tie strength is `T = tanh(|delta|/4)`, the largest change of the occupation of
one arrangement that the breaker can cause at the best base boundary (a base with log-odds `-delta/2`; such a base is reached by adding
tuner cells of the same kind on the walls, each shifting the log-odds by a step of the same size, so the sup over boundary conditions of the
Lean criterion contains it). `delta` needs no sampling of the tunnelling between A and B, only that each arrangement is a persistent sector:
**persistence** is checked from the indicator of every chain at every node (A chains above 1/2, B chains below, gap of the means above 0.15). If
the sectors **mix** (the two starts end in the same state), delta is not defined and the direct indicator shift under the breaker is reported
instead (it must be small for the verdict NO TIE).

### 2.4 Validation (numbers in section 6)

Z2 beta 0.6 ell = 9: separated, delta = +2.30 +- 0.02, **TIE**. Z2 beta 0.3 ell = 9: mixed, delta = 0.06 +- 0.03, **NO TIE**. Z2 beta 0.6 at
ell = 5 is too small (the sectors mix, 5 and 6 switches), at ell = 6 no tie area exists (s = 1.25): not used. The integrand `<dS/dlam>` of sector A at lam = 0.5 is +1.84 (ell = 9) and +1.89 (ell = 6), the same within errors: the response is local; in B it
is negative (integral -1.14).

### 2.5 2I (thick sheets)

The binary icosahedral group has smallest non-trivial rotation angle pi/5, so a centre flux pi can be spread over five plaquettes at a cost
of about 0.95 beta per unit area instead of 2 beta (c6c 2.3: at least c beta at every thickness): the thin Dirac sheet is unstable at **every**
beta and thickens within about 15 sweeps; the loops around the former sheet position then give a small positive value (ell = 9, beta 4:
W_1..4 = 0.79, 0.45, 0.15, 0.08 in A and 0.74, 0.38, 0.12, 0.04 in B, indistinguishable). The 2I tie therefore needs boxes in which sheets of width 5 fit
at distance `2 s` with room, and a loop indicator of size R = 5, whose amplitude is the issue: pilot, ell = 13, loop R = 5, 2 chains, 80 sweeps:
beta 4: f = 0.46 to 0.51 in A (W about 0: unresolved); **beta 6: f = 0.96 (A) and 0.15 (B), both persist**; beta 8: f = 1.00 exactly (frozen:
plaquettes of the identity only, no dynamics). The queue has 2I at beta 6, ell = 13 (Tier 2: 17). The Lean note's 2I claim (tie at every cell
size) rests on exactly this width bound.

## 3. The decisive plan (queue `queue_decisive_gpu.ps1`)

`pwsh -File queue_decisive_gpu.ps1 [-Tier 1|2] [-CpuParallel 4]`; `-DryRun` lists every job with its estimate and starts nothing. Resumable
(a job with an "exit 0" line in `runs/queue_decisive.log` is skipped; failed GPU jobs retry after an out-of-memory), ends with the line
`DECISIVE DONE`, then runs `decisive.py analyse` (`runs/decisive_summary.json`, `runs/analysis.log`). Checked with the PowerShell parser and a dry
run (Tier 1: 37 GPU and 20 CPU jobs; Tier 2: 44 and 24).

| block | what | device | size |
|---|---|---|---|
| gates G1-G6 | identical / gauge copy (aligned, plain) / pure-gauge (labels, none) / independent start | CPU | SU(2), ell 6, 100 to 200 sweeps |
| anchors | SU(2) beta 0.1: ell 8, 12, 16, 24 (nc 4, 6, 8, 12; depth classes merged above 2 for nc > 6), flip, and rand up to ell 16; beta 0.2: ell 8, 12; typical at ell 8; Tier 2: beta 0.1 ell 36 (nc 18) | GPU | 4 (2) chains per class, 60 + 300 sweeps |
| scan | SU(2) beta 0.3, 0.5, 0.8, 1.2, 1.8 at ell 8 | GPU | short |
| weak coupling | SU(2) beta 2.3: ell 6, 8, 10, 12; beta 2.5: ell 11, 15; calm; typical and hot at ell 6 and 11 | GPU | short (they saturate within 30 sweeps) |
| U(1) | photon beta 2: ell 6, 8; strong beta 0.05: ell 6, 8 | CPU | |
| tie controls | Z2 beta 0.6 and 0.3: ell 9, 13; 2I beta 6: ell 13 (Tier 2: Z2 ell 17, 2I ell 17) | CPU | 6 (3) chains, 5 nodes |
| tie SU(2) | beta 2.3: ell 5, 9, 13 (l sqrt(sigma) = 1.75, 3.2, 4.6); beta 2.5: ell 9, 13, 17 (1.6, 2.4, 3.1); Tier 2 adds 2.3: 17, 21; 2.5: 21 | GPU | 8 chains, 5 nodes, 40 + 200 sweeps per node |

**Runtime estimate (dry run).** Tier 1: **GPU about 3.2 h, CPU about 8 CPU-hours (about 2 h wall on 4 workers beside the GPU; the longest single job is about 80 minutes)**;
Tier 2: GPU about 10 h, CPU about 19.5 CPU-hours (about 5 h wall). The CPU numbers come from the pilots (couple 8e-6 s per site, pair and sweep; Z2 tie 1e-5 s per site, chain and
sweep, single core); **the GPU numbers are assumptions** (couple 4e-7 s per site, pair and sweep plus 0.1 s launch overhead; SU(2) tie on the
fused kernels 1e-6, from c7b's 1.5e-6 per site, chain and 2 sweeps), uncertain by a factor of 3. The GPU path of `decisive.py` (array code in
CuPy: sampler, maximal coupling, alignment, tie updaters) is written generically but **was not run on the GPU** (no GPU use allowed); if a GPU
job fails the queue logs the exit code and goes on, and the same command with `--cpu` is the fallback.

## 4. Verdict rules (fixed before the data)

**Gates (all must hold, else the SU(2) numbers are not evidence either way).**
G1 identical boundaries: D = 0 exactly. G2 gauge copy aligned: D = 0 exactly (and plain: D above 0.9 of all cells, showing the alignment is
needed). G3 pure-gauge change with labels at the changed sites: D = 0 exactly. G4 anchors: SU(2) beta 0.1 unsaturated (fraction of differing
cells below 0.1), D(r) = 0 beyond r = 2, and K(ell = 24) <= 1.2 K(ell = 16) (K converges from below as the box grows, 1.08, 1.36, 1.77 in the pilot). G5 photon beta 2 saturated
(fraction above 0.5). G6 Z2: beta 0.6 gives TIE at ell 9 and 13 and beta 0.3 gives NO TIE at both; 2I beta 6 ell 13 gives TIE (rule T below).

**Rule U (per coupled run), the upper bound.** `S` = fraction of box cells differing (mean over classes). **SATURATED** if S >= 0.3: the run gives
no bound. **INFORMATIVE** if S <= 0.1 and the two halves of the series agree (difference below 4.5 blocked errors of the full series): then `Q_U` with its blocked error; the **criterion is
supported on this box and boundary family** iff `Q_U + 3 sigma <= 0.9`; if `Q_U > 1` there is no statement (an upper bound above 1 proves
nothing). In between: no statement. The surface-count floor is `Q_U >= 8/nc`, so no run with nc <= 8 can be supported; with K about 2 even beta 0.1 needs nc >= 16 (Tier 2: ell = 36).
*Expected result, stated in advance:* all weak-coupling runs SATURATED; the SU(2) beta 0.1 anchors INFORMATIVE with Q_U falling like 8 K/nc but above 1 up to ell = 24 (Q_U about 1.3 at nc = 12).

**Rule T (per group, beta, ell), the tie.** From delta, its error and persistence (section 2.3):
* **TIE**: sectors separated and |delta| >= 2.0 and |delta| > 3 sigma. The tie strength tanh(|delta|/4) is then at least 0.46.
* **NO TIE**: sectors mixed (largest gap of the two indicator profiles below 0.1, switching seen) **and** the direct indicator shift below 0.1.
* otherwise INCONCLUSIVE.

**SU(2) statement (fixed):**
* **TIE FOUND (violation of the criterion by mechanism T, indicated, not a theorem)**: at either beta the two largest ell are TIE and the gates hold.
* **NO SHARP TIE AMONG THE ARRANGEMENTS TRIED**: at both beta every ell >= 9 is NO TIE, or |delta| falls by a factor 2 between the two largest ell at
  equal l sqrt(sigma)-ordering (beta 2.3: 9 -> 13; beta 2.5: 13 -> 17), and the gates hold. This is **not a pass certificate**: it covers two
  arrangements and one breaker, and the lower bound of the cell count (sheets move about ell^3 cells in the coupling metric but a closed-loop
  observable sees only about ell^2) stays a classical estimate.
* otherwise **NOT DECIDED**.

**Combined decisive verdict.** (1) TIE FOUND for SU(2): the one-box criterion fails at the scales tested. (2) NO SHARP TIE and the U block
saturated at beta 2.3 / 2.5: the criterion is not refuted by the extremes tried and **not supported** either (no upper bound at weak coupling);
what remains open is the bound itself, which needs the cell-level coupling of section 1.4. (3) Anything else: not decided.

## 5. Caveats (plain)

1. **A coupling's D is an upper bound of kappa only in expectation**, only once both marginals are stationary (checked by the halves of the
   series and the burn-in series, not proved), and up to the statistical error; the sampled boundary conditions (calm, typical, hot) and the
   sampled changes (flip, rand) are extremes, **not the worst case**, so a small Q_U would be "no violation among the extremes tried".
2. **The surface-count floor.** Q_U >= 8/nc: the criterion cannot be certified on boxes of fewer than 9 cells per side whatever the coupling;
   the Tier-1 boxes (nc = 3 to 6) are all below that, so the Tier-1 SU(2) runs are about the *behaviour* (saturated or local, growth with ell),
   not about the value of Q.
3. **Tie:** delta is the response of the log-odds of two chosen arrangements to one chosen breaker, measured in persistent sectors; the base
   boundary at which the tie is exact is argued (tuner cells), not built; the cell count moved between the sectors (about ell^3) is not
   measured. A persistent sector can be a metastable state of the finite run: the persistence check is over the run's length (200 to 800 sweeps),
   not a proof; SU(2) arrangements can be connected by low barriers (thick vortices): the verdict NO TIE then rests on the mixing, which is
   exactly the physical statement (no sharp ties at scales above xi).
4. The integration ladder is Simpson with 5 nodes, not checked against a finer ladder: `<dS/dlam>` is smooth (sine and cosine of lam, see the
   node values in the npz files); an error of a few percent of delta is possible and below the verdict thresholds.
5. 2I: only the persistence of the two arrangements and the indicator are piloted (section 2.5), not the ratio-method run; if the 2I run is
   INCONCLUSIVE the 2I part of G6 is reported as not met, and the SU(2) numbers then rest on Z2 only.
6. The depth classes merged above 2 (anchors with nc > 6) assume that a cell's influence does not reach beyond 2 cells; D(r) of the same
   anchors at smaller ell tests it.
7. The GPU code path is untested (section 3).

## 6. Pilot (CPU, tiny boxes: **PILOT, not data**)

See the table in 1.2 and the sections 1.3 and 2.4. Raw outputs: `pilot/*.npz`, `pilot/*.log`; analysis: `python decisive.py analyse pilot`.
### 6.1 Coupled chains (pilot analysis: `pilot/pilot-analysis.txt`, `.json`)

Box ell, nc cells per side, one changed cell, calm boundary, `Q_U` and `K` as in section 1.1, rule U verdict as coded in `decisive.py`.

| run | nc | Q_U (+- error) | K | D(r) by cell distance | verdict (rule U) |
|---|---|---|---|---|---|
| identical boundary, beta 2.3, ell 6 | 3 | 0 | 0 | | D = 0 |
| gauge-rotated copy, aligned | 3 | 0 | 0 | | D = 0 |
| gauge-rotated copy, no alignment | 3 | 863.7 | 323.9 | | all cells differ |
| pure-gauge change with labels, beta 2.3 / 0.1 | 3 | 0 / 0 | 0 | | D = 0 |
| pure-gauge change without labels, beta 0.1 | 3 | 2.87 +- 0.11 | 1.08 | 0.56 0.52 0.00 | boundary layer, as a real change |
| SU(2) beta 0.1, ell 6 | 3 | 2.88 +- 0.09 | 1.08 | 0.65 0.43 0.00 | informative, Q_U > 1 (floor 2.67) |
| SU(2) beta 0.1, ell 8 | 4 | 2.73 +- 0.08 | 1.36 | 0.79 0.57 0 0 | informative, Q_U > 1 (floor 2.0) |
| SU(2) beta 0.1, ell 12 | 6 | 2.36 +- 0.06 | 1.77 | 0.96 0.80 0 0 0 0 | informative, Q_U > 1 (floor 1.33) |
| SU(2) beta 0.2, ell 6 / 8 / 12 | 3 / 4 / 6 | 11.9 / 11.8 / 12.5 | 4.5 / 5.9 / 9.4 | peak at r = 1, width 4 cells at ell 12 | informative, growing with ell: near the threshold |
| SU(2) beta 0.3 / 0.5 / 0.8 / 1.5 / 2.3, ell 6 | 3 | 354 / 722 / 832 / 861 / 862 | 133 / 271 / 312 / 323 / 323 | | SATURATED |
| SU(2) beta 2.5, ell 11 | 3 | 864 | 324 | | SATURATED |
| U(1) beta 0.05, ell 6 / 8 | 3 / 4 | 1.93 / 2.02 | 0.72 / 1.01 | 0.44 0.28 0 / 0.61 0.39 0 0 | informative (local) |
| U(1) beta 0.1, ell 6 | 3 | 5.3 | 1.97 | 0.85 1.11 0.01 | informative, spreading |
| U(1) beta 0.2, ell 6 / 8 | 3 / 4 | 391 / 1121 | 147 / 560 | | SATURATED (S = 0.45 / 0.55) |
| photon, U(1) beta 2, ell 6 | 3 | 852 | 320 | 3.8 95.6 220.2 | SATURATED |

Runs: 30 to 100 measurements of 2 sweeps, 2 to 4 chains per class; chains thermalised alone for 20 to 100 sweeps, then 20 to 60 coupled sweeps;
the two halves of every series agree within the errors.

### 6.2 Tie test (CPU, `pilot/tie_*.npz`; 6 chains (SU(2) ell 9: 4), 5 nodes, 20 (15) sweeps per node, 40 (20) measurements)

| group, beta, ell (s) | f(A) / f(B) at lam = 0 | persistence | delta (ratio method) | verdict (rule T) |
|---|---|---|---|---|
| Z2, 0.6, 9 (2) | 0.96 / 0.01 | both persist, 0 switches in the 600-sweep run | +2.30 +- 0.02 (A +1.16, B -1.14) | **TIE**, strength 0.52 |
| Z2, 0.3, 9 (2) | 0.50 / 0.49 | mix, about 500 switches | +0.06 +- 0.03 | **NO TIE** |
| SU(2), 2.3, 5 (1) | 0.42 / 0.41 | mix | -0.17 +- 0.16 | NO TIE |
| SU(2), 2.3, 9 (2) | 0.41 / 0.41 | mix (A decays to the B-like state in the first 60 sweeps) | +0.14 +- 0.20 | NO TIE (4 chains: statistics small) |
| Z2, 0.6, 5 (1), first version of the indicator | 0.83 / 0.31 | mix (5 / 6 switches): too small a box | +0.58 +- 0.34 | inconclusive |

SU(2) beta 2.5 and ell >= 13 were not piloted (CPU cost), they are the production run. 2I (ell = 13, beta 6, loop R = 5, 2 chains, 80 sweeps, no ladder): f(A) = 0.96 to 0.97, f(B) = 0.13 to 0.19, no switch; beta 4: f(A) = 0.46 to 0.51 (unresolved);
beta 8: f(A) = 1.00 (frozen); ell = 9, beta 4: loops W_1..4 = 0.79, 0.45, 0.15, 0.08 (A) / 0.74, 0.38, 0.12, 0.04 (B).
