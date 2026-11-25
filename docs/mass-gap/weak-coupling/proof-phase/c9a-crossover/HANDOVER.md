# c9a-crossover hand-over

## Round 1 (2026-11-23, committed 5c1e0f3)

`NOTE.md`, `formal/ProofPhase/Crossover/Openness.lean` (5 declarations), `build.sh`, `axioms.sh`, `axioms.log`. P4 stated as
`P4_*`; reduction to a finite system clean (Openness), all content in (WL); W1, W2, W3 and the `γ₀` decision proposed.

## Round 2 (2026-11-23, uncommitted, for the coordinator to verify and commit)

**New files**
* `formal/ProofPhase/Crossover/P4Chain.lean`: 23 theorems, 10 definitions (W1).
* `c9a-crossover/W1-CHAIN.md` (paper note for W1), `WL.md` ((WL) scale by scale, M1's move), `W2-PREREG.md` (GPU design, not
  run), `build-p4.sh`, `axioms-p4.sh`, `axioms-p4.log`, this file.
* Nothing outside `Crossover/` and `c9a-crossover/` was changed.

**Verify**
* `wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/build-p4.sh`
  (copies `~/formal/.lake` into `~/formal-p4` on first use; "Build completed successfully", no warnings in `P4Chain.lean`).
* `... bash .../c9a-crossover/axioms-p4.sh` (23 lines, each `[propext, Classical.choice, Quot.sound]`; log in `axioms-p4.log`).
* `~/formal-p4` was deleted at the end of the round. Scrub scan: rc 0 ("clean").

**Results**
1. W1 (Lean): `P4Star C λ` and `M1HandOver T B C` as named hypotheses; `yang_mills_assembly_p4Star` (unrestricted),
   `yang_mills_assembly_p4StarInv` (gauge-restricted, with `RandObsTransferPhysTWInv`), `yang_mills_assembly_stageTwo` (landing
   at `L₁` plus `V4.StageTwoW`), `p4StarInv_of_net` (closeness plus an explicit tail clause).
2. (WL) (paper/sketch): per-scale forms `WL-Q_i` (quenched) and `WL-S_i` (supported, M1's move). The `P4Star` route needs
   `WL-Q` (the worst case is in the consumer); the stage-two route takes `WL-S`. The move removes every requirement on bad data
   and replaces it by annealed rarity; it keeps a worst case on good data and supplies no smallness. At each scale `WL-S`
   becomes two measurable numbers with a trade-off in the threshold. (WL) is gap-free; the gap sits in closure plus landing.
   **(WL) as stated in `NOTE.md` (quenched, all twisted block fields and outsides) is false at the weak end**, by M1's own
   sub-block vortex example (`UV-TV.md` 3); the supported form is necessary, not optional.
   Correction to `NOTE.md` 2.4: no known estimate covers (WL) at the crossover scales beyond M1's reach (`g ≤ γ₀`); the
   strong-coupling Dobrushin window ends at `β ≈ 0.25`.
3. W2 (design only): measures the good-box column sum, the bad-cluster connectivity and adversarial (quenched) failures at
   `β` 2.3 to 3.5, with photon content gate, 2I expectation, kill rule, and a timing plan (time one full-size job, project, cap
   20 GPU-h, abort at 2× projected).
4. Containment without rarity (paper/sketch; added on the coordinator's request from the owner's reading "Certification and
   the open middle", `WL.md` 10): contained regions pass on only what crosses their boundary, always (exact). That is not
   enough for a contraction: each needs good room of width ~log|W|/m around it, so regions needing containment must be sparse
   relative to the collar volume (crude bars 1e-13 to 2e-5 per cell depending on m and counting). Absolute rarity can go,
   relative sparseness cannot. Lever left: contain only regions that fail to contract, not large-field regions. W2 now also
   measures m and influence-bad blocks.

**Reviews (two independent reviewers, Haiku subagents, read-only).**
* Lean chain reviewer: no fault in the copied proofs or in the named hypotheses; one claim error, flagged FATAL by the reviewer (P4StarInv called the
  weaker hypothesis; it trades a weaker influence clause for covariance, neither implies the other) and several overclaims
  (tail clause necessity, SU(2) usage, R11 fallback, Markov property in the stage-two sketch, (1+R)^4 factor). All fixed in
  the Lean docstring and `W1-CHAIN.md`; rebuilt clean.
* Notes reviewer: no FATAL. Gaps fixed: (G) now requires CouplingDS (I) for all in-support pairs; Lemma C needs M <= 1/4;
  van den Berg-Maes conditional on the positive split, Kotecky-Preiss replacement only at sketch level; "gap-free" made
  conditional on the photon gate; M1 coverage statements reconciled; "two orders" corrected to one; W2: column sums for
  inhomogeneous instances, G0 co-rotates Y, pass side likely unreachable stated up front, Pinsker diagnostic added,
  verdict gaps closed (spanning defined, all else UNRESOLVED), T per beta and both ends timed, G2(a) statistic named.
  Not addressed: whether the photon passes WL-S for M1's blocking (left to W2's gate).

**Waiting on the owner**
* Whether W2 runs (GPU; only after the timing job and projection).
* The `γ₀` desk study (not started, as instructed).

**Open, in order of leverage**
1. R11: the assembly on the `(V, τ)` state space (needed before `P4StarInv` can be instantiated with a covariant
   specification; `W1-CHAIN.md` 2).
2. `RandObsTransferPhysTWInv` from M1's transfer (sketch in `W1-CHAIN.md` 2).
3. A stage-two lemma in Lean from per-scale conditional decorrelation (total covariance along the scales; generic, no
   physics), so that `WL-S_i` becomes the named Lean input instead of `StageTwoW`.
4. (WL) itself; closure; landing with a tail budget (W3).

## Round 3 (2026-11-23, uncommitted; W2 code and timing, the 10.4 lever)

**New:** `w2/` (`constrained.py`, `project.py`, `queue_w2.ps1` dry-run by default, `time_job.ps1`, `PIPELINE.md`,
`PROJECTION.md`, `PROJECTION.json`, `PROJECTION_mixed.json`, `.gitignore` for `runs/*.npz`, `runs/` with pilot and timing JSON
and logs), `INFLUENCE-BAD.md`. Changed: `W2-PREREG.md` (amendment pointer in section 8).
* CPU selftests all pass, including one-link exactness (after a fix: the first update was exact but stuck at kappa = 16) and
  the gauge gate G0. Start 1 redefined (heated equilibrium interior). Amendments A1-A5 recorded before any production data.
* Pilot (CPU): T(2.3) = 300, T(3.5) = 600; coupled pairs saturate at 83-89 % disagreement (upper side vacuous).
* Timed job (one, GPU, 41 min, clean soft cap): 10.26 s per sweep for a full ell = 6 batch (3 jobs, 480 pairs); 1.88 h per
  batch at T = 600. Projection: full design 539 h (248 h mixed packing); after all pre-registered cuts 203 h (58 h mixed):
  over the 20 h cap, so the rule says ask the owner. Options in PROJECTION.md 3.
* Extra GPU use beyond the timed job is recorded in PIPELINE.md (reported to the coordinator).
* INFLUENCE-BAD.md: a coarse-only influence-bad set fails (sub-block vortex outsides); the two-level set (fine-bad by
  contraction, coarse-bad as worst case over fine-good outsides) is measurable in the scale filtration; rarity becomes a
  per-coarse-state number of the reverse kernel; W2 would need conditional rarity per Y.

## Round 4 (2026-11-23, uncommitted; owner's decision: fused SU(2) routine, narrow run)

* W2-PREREG.md amendment A6 (owner's words, narrow scope, what it can and cannot deliver: no WL-S pass verdict).
* `w2/fused.py` (one CUDA kernel per colour-class update), `w2/fused_selftest.py`, `constrained.py launch` (mixed packing,
  lever data saving), `project_narrow.py`, `queue_narrow.ps1` (dry run by default), `time_job.ps1 -Jobs`.
* Correctness: deterministic fields = reference to 6e-14; Bessel 2e-14; G1; one-link |z| <= 1.5; G0; stationarity; reference vs
  fused plateau 881 vs 884. Speed-up 8.3x per sweep (1.47 vs 12.1 s).
* One timed fused launch (04:21:53-04:43:27, 1294 s, full T = 600). Narrow run projected at 1.55 GPU-hours (target < 3 h).
  Saved data 39.5 MB per launch, about 240 MB for the run. Two-level analysis on the CPU: about 70 CPU-hours for a
  272-local-box subsample (about 9 h wall on 8 cores), or a few CPU-hours for the cheap single-link proxy (code not written).
* The narrow run itself waits for the owner's OK (via the coordinator).

## Round 5 (2026-11-23, uncommitted; the narrow W2 production run and its analyses)

* Run (owner's OK): 6 fused launches, 04:49:21-07:04:36, 2.25 GPU-hours against 1.55 h projected (1.45x), no abort, no kill;
  watcher `w2/run_narrow.ps1`. Error-band rule for single-timing projections: `w2/PROJECTION.md` 8.
* Pre-registered (`w2/RESULT.md`): WL-S UNRESOLVED at beta 2.3 and 3.5 (kill rule not triggered; max raw R_low 0.65), WL-Q not
  refuted for this blocking; small resolved boundary sensitivity at beta 3.5 (about 0.1), none at 2.3. Table "measured quantity ->
  statement" added (owner's rule): nothing discharged; lower bounds refute nothing; the upper side is saturated.
* Diagnostic (`w2/PROXY-RESULT.md`): the single-link proxy saturates everywhere (kappa per block 4.9 and up); the lever needs the
  box influence (272-box subsample, about 70 CPU-hours, separate OK).
* Exploratory (`w2/SETTLING-RESULT.md`, plan committed in bc601c9 before the data): bad boxes not slower at either beta, at the
  10-sweep resolution; the twisted block field (A3) was not taken up by the fine field (alignment about 0 on the flipped links).
* Run logs scrubbed of the user-profile path; scrub scan clean. GPU free; no GPU use without a new OK.

## Round 6 (2026-11-23, uncommitted; the worst-case dichotomy)

* `DICHOTOMY.md`; `formal/ProofPhase/Crossover/Dichotomy.lean` (8 theorems, standard axioms, `build-dy.sh`, `axioms-dy.sh`,
  `axioms-dy.log`; `~/formal-dy` deleted).
* Exact (Lean): attachment of sheet pieces in a closed layer, part (b) "uncontained has zero weight", the boundary flux is a
  function of the outside, flux parity, and `window_gap` (sheet-Peierls and saturation regimes are disjoint).
* First unclosable step: part (a) uniformly in the outside. The cost of one centre-layer flip is beta |tr U_p|, zero at the SO(3)
  cut, so no e^{-c|S|} bound uniform in sigma exists; behind it: forced sheets with ties (smallness only annealed; the strict flip
  bound gives < 1 with no rate) and the window between the Peierls and saturation regimes that the crossover crosses.
* Reduction (D'): contract, or one of two bad events (flux-carrying outsides with near-degenerate spanning surfaces; SO(3) cut along
  a surface), plus uncontained (zero weight). Rarity of the two events = conditions B/C again.
* A3 reading: coarse twists are not forced into the fine field (boundary flux is fine-outside data); equilibrium vs kinetics open.

## Round 7 (2026-11-23, uncommitted; coarse-scale test, EXPLORATORY)

* `COARSE-TEST.md` (plan fixed before data, result sections 7-9), `w2/coarse_test.py`, `w2/runs/coarse_test.json`.
* Near-cut set on blocked variables (factors 1, 2, 4) of the saved 16^4 equilibrium configurations: beta 2.3 spans at every
  factor and grows (20, 37, 79 percent; the blocked theory flows to strong coupling); beta 3.5 stays isolated with an exponential
  size tail at every factor. Owner prediction contradicted at 2.3, supported at 3.5.

## Round 8 (2026-11-23, uncommitted; the integer-flux route to a rate)

* `RATE.md`; `formal/ProofPhase/Crossover/FluxRate.lean` (8 theorems) and `HandOver.lean` (3 theorems), standard axioms
  (`axioms-dy.sh` now lists all 22 Crossover theorems, `axioms-dy.log`; `~/formal-dy` deleted); `w2/pastcut.py`,
  `w2/runs/pastcut.json` (CPU, no GPU).
* Closed (Lean): a flux-carrying outside forces a boundary-attached sheet; flux cells even, at least 2; forced area at least
  (flux cells)/4 in d = 4. At every box size max(F_tw, F_e) >= log(1 + sqrt 2) = 0.881 (self-dual point of 't Hooft's duality,
  from the strict bound Z_tw < Z; `0 < Z_tw` taken as a hypothesis).
* Paper: the average cost per sheet plaquette is bounded below (annealed numerically, quenched by compactness for a fixed box) but
  is not a rate (Jensen: it bounds the weight from below); the rate is the free energy of forced sheets, F_tw, and it enters the
  annealed half of the one-box condition (bad-pattern weight). Strict flip gives only the sign; F_tw -> 0 is expected at large L
  in the confined phase, where the electric channel F_e takes over.
* First open step: multiplying one box's rate over D/L boxes (twist side: chessboard weight of the box-flux event vs e^{-F_tw};
  electric side: the binary-channel model of Floor.lean 3). Behind it: annealed torus quantities vs per-outside influence.

## Round 9 (2026-11-23, uncommitted; Y1, a composite Higgs-type field on the collars)

* `HTF.md` (with a DMP section); `formal/ProofPhase/Crossover/CompositeHTF.lean` (5 theorems, standard axioms; `axioms-dy.sh`
  and `axioms-dy.log` now cover 27 Crossover theorems; `~/formal-dy` deleted). No GPU, no new numerics.
* Candidates: lowest eigenvector of the collar's covariant Laplacian (fundamental, quaternionic; adjoint for the SO(3) part).
  Collar-measurable, gauge covariant; exact degeneracies, eigenvector zeros and Gribov copies are null.
* Lean: a gauge-covariant frame is independent of every gauge-invariant observable (finite analogue), so conditioning on the HTF
  gives nothing; frame plus invariant content is the full collar (Markov decoupling, condition A unchanged). First open step:
  step 2, no uniform conditional mass (composite field has kappa = 0: no hopping term, no small parameter).
* Lean: the electric-flux free energy is superadditive up to the neutral excess act c(L) = log(Z0(L)/lambda0^L); the per-box rate
  multiplies iff F_e(L) > 2 c(L) at one scale. c(L) is the neutral gap in disguise (circular) and extensive in the cross-section;
  the twist channel does not multiply.

## Round 10 (2026-11-23, uncommitted; CPU refutation check of F_e(L) > 2 c(L))

* `ONEBOX-CHECK.md` (plan fixed before data, sections 1-3; result 4-6), `w2/onebox_check.py`, `w2/runs/onebox_check.json`,
  `w2/runs/onebox_check_sig4.json` (robustness). CPU under a minute per run; no GPU; no Lean.
* F_e and c themselves are not estimable from saved data (lambda0^L normalisation, twisted ensemble). Used the exact
  F_e - 2c = -log(Z0 Z1 / lambda0^{2L}) and reflection-positive effective-mass upper bounds on energies: R(L) = L dE_f^up -
  log(1 + S(L)) >= F_e - 2c, cross-section 16^3, L = 1..8.
* beta 3.5: refuted at L = 1 (R = -3.1 at 95 %, -1.9 at 99 %; robust to 4 sigma selection). Flux nearly free (m_eff 0.014) and c
  extensive. Not refuted at L >= 2 by this bound (margin 0.01 at L = 2), mainly because of the floor on the flux error.
* beta 2.3: no flux upper bound (Polyakov signal gone after one step), so no test; c(1) >= 4.2, c(2) >= 1.2 (95 %).
* Cubic geometry L_s = L untested; proposal (not run): small-torus CPU simulation with thermodynamic integration and snake.
## Round 10b: ONEBOX-CHECK section 7 POST-HOC (universal floor): beta 3.5 refuted range grows to L <= 2 (95/99 %) and L = 3 (95 %); beta 2.3 still untested; 16^3 geometry, no bearing on the one-box statement. Section 6 proposal states the floor (reading: O(1) on F_e and c, owner's call). Section 4 label corrected (0.196 was the no-covariance delta method).

## Round 11 (2026-11-23, uncommitted; NEIGHBOURS edge, small-torus run in the background)

* `NEIGHBOURS.md`; `formal/ProofPhase/Crossover/Neighbours.lean` (5 theorems; `axioms-dy.log` now 32 Crossover theorems, standard
  axioms; `~/formal-dy` deleted).
* Flux carrier gives one odd channel only in a chain; in a grid flux has 2d - 1 exits. Lean: k (sqrt 2 - 1) < 1 iff k <= 2, so
  the hand-over floor fails the 2d column sum for d >= 2; requirement F > log(2d) (2.08 in d = 4). First open step.
* Neutral part by decimation: with the measured conditional mass (typical fields) the summed boundary influence is below 1 from
  7 cells on (box side about 15 L1 cells); not a certificate (Lemma C needs the supremum).
* Physical units: uniform eta0 at fixed physical box size l_* = L_* a gives m_phys >= -log eta0 / l_* (Lean); Doeblin's
  physical rate goes to 0 as a -> 0 (Lean), so the tick must come from the blocked theory at g_*.
* Small-torus run (ONEBOX-CHECK 8): pre-registered, timed (projection 4.0 h, band 2.7-5.7 h), running as one background process.

## Round 12 (2026-11-23, uncommitted; renormalized Doeblin)

* `RDOEBLIN.md`; `formal/ProofPhase/Crossover/RDoeblin.lean` (5 theorems; `axioms-dy.log` 37 Crossover theorems, standard
  axioms; `~/formal-dy` deleted).
* Premise corrected: M1's L_* is weak coupling; order-one coupling only at L1 after the open crossover P4.
* Lean: an a-independent floor on blocked kernels gives chain contraction (1 - eps)^n and physical decay exp(-m D), m uniform
  in a; with M1's floor (paper) this is a gap uniform in a on a spatial torus of fixed physical size.
* First open step: the 2d sum. Needs floor exponent C < log(8/7) = 0.134 (column) or < 0.22 (disagreement percolation, p_c of
  Z^4 about 0.197); at L_* C is of order 100; larger boxes hurt (C grows like the surface).
* Large fields: small set (rarity) plus a boundary factor e^{-2 K_R}; not null; irrelevant to the failure.

## Round 13 (2026-11-23, uncommitted; transfer round from P vs NP and GRH)

* `TRANSFER.md` (with DMP section); `formal/ProofPhase/Crossover/Runs.lean` (7 theorems, imports GRH/Tate; `axioms-dy.log` 44
  Crossover theorems, standard axioms; `~/formal-dy` deleted).
* Multi-sector duality (1 + S_tw)(1 + S_e) = 2^n (paper, 't Hooft): channels multiply, so duality caps the smaller summed weight
  at sqrt(2^n) - 1 >= 1 for n >= 2 (Lean): no summable floor; pairs across a DB add sectors (worse).
* First open step: S_e(L) < 1, equivalently S_tw(L) > 2^{n-1} - 1 at one box (quantitative 't Hooft criterion; Lean equivalence).
* Holonomy: right carrier, no extra summability (face sum = 2 to 4 x sheet pieces; needs F_tw > log 11).
* "It runs": one-box statement = strict contraction on the neutral sector; runs_two_targets puts it beside GRH's target.

## Round 14 (2026-11-23, uncommitted; twist saturation, our own attempt + bond-moving bounds)

* `SATURATION.md` (with DMP section); `formal/ProofPhase/Crossover/Saturation.lean` (4 theorems; `axioms-dy.log` 48 Crossover
  theorems, standard axioms; `~/formal-dy` deleted). Sources read via arXiv HTML (later sections as summaries).
* Our pieces: tick-unit floor r >= e^{-2 beta L^2} (saturates only for beta L^2 <= 0.42); one-box statement => saturation in long
  boxes (Lean, one way); strict flip / hand-over / conditional mass / M1 give no saturation.
* Bond-moving: upper decimation flows to strong coupling (Ito, citation), but the upper bound's normalisation prod F0^{|Lambda_box|}
  >= 1 (Jensen, Lean) is extensive in (L/b)^4; one-box form localises the interpolation, does not remove it. First open step:
  normalisation-matched lower bound on Z_box (= one-box interpolation; equivalently strong effective coupling at box scale, P4).
* Kanazawa: confirmation; his twisted inequality is non-strict RP; ours strict and machine-checked.
* Numerical (preliminary): beta 2.3 cubic twist ratio crosses 3/7 between L = 4 (0.42) and L = 6 (0.86).

## Round 15 (2026-11-23, uncommitted; reversed P4, containment)

* `CONTAINMENT.md` (with DMP section); `formal/ProofPhase/Crossover/Containment.lean` (8 theorems; `axioms-dy.log` 56 Crossover
  theorems, standard axioms; `~/formal-dy` deleted).
* (a) r < 1 everywhere, r = (1 - e^{-F_e})/(1 + e^{-F_e}) <= F_e (Lean): twist rare where electric flux is cheap (small box,
  perturbative F_e = O(g^2), citation; data beta 3.5 L 2: F_e 0.035).
* (b) Fixed cross-section: positive kernel + Jentzsch => flux sector below vacuum by mu < 1 => F_e(T) grows (Lean core): the
  rarity branch fails in long boxes. Cubic: needs F_e(L) >= 0.881 at some L, beyond perturbative/M1 control.
* (c) Path-Peierls: tube dominance needs F > log mu (Lean); mu >= d so 0.881 fails for d >= 3 (Lean). First open step: strong
  saturation F_e(L) > log mu_4 = 1.91 (r > 0.74) at one box; numerically passed centrally at L = 6, beta 2.3 (not certified).
* Round 15 addendum: CONTAINMENT.md section 6 (Gauss's law gives the tube's shape, not its dominance; Bogomolny floor helps only outside for odd-twist-product sectors, zero for the single-plane twist, and loses to position entropy 4 log(L/a) vs (11/3) log(1/(a Lambda)) at fixed physical size).

## Round 16 (2026-11-23, uncommitted; twist-sector equidistribution, GRH shape)

* EQUIDIST.md (section 1 pre-registered; disclosure: beta 2.3 and beta 3.5 L = 2 ratios seen before the rule), with DMP section;
  formal/ProofPhase/Crossover/Equidist.lean (9 theorems: Z2^n characters, orthogonality, electric sectors, sector product,
  sharp equidistribution bound, per-sector deficit bound); axioms-dy.log 65 Crossover theorems, standard axioms; ~/formal-dy deleted.
* Cancellation: in nonnegative deficits d_k = 1 - Z_k/Z_0 (RP), S_e = D/(2^n - D) exactly: no leftover signed quantity; the identity
  bypasses path sums at one box but moves the requirement to twist saturation at the target scale (a lower bound RP cannot give).
* First open step: lower bound on twist ratios (sum d_k < 2^{n-1}) at one box of fixed physical size.
* Exploratory test (w2/equidist_test.py): beta 2.3 deficit decreasing (floor-like on 2 points, post hoc); beta 3.5 no decrease (unseen).
* Round 16 addendum: EQUIDIST.md section 8. (i),(ii) verified on the torus (P_e projection commuting with T >= 0). With a fixed outside, a box twist is an outside change (flux identity); sectors grow with the faces (2^(2d-1) = 128 at face resolution); RP lost: the grid requirement returns as uniform insensitivity to the outside flux pattern.

## Round 17 (2026-11-23, uncommitted; small-torus check result)

* ONEBOX-CHECK.md section 9; w2/runs/smalltorus/ (278 ensemble jsons), w2/runs/smalltorus_result.json, w2/runs/smalltorus_run.log.
  3.27 CPU-hours (projection 4.0 h, band 2.7-5.7 h). r <= 1 and the hand-over hold everywhere.
* Cubic criterion F_e(L) > 2c(L): refuted at beta 2.3 L = 2 (95 %), beta 3.5 L = 2 (95/99 %), beta 3.5 L = 6 (95 %): the weakly
  coupled side (electric flux nearly free, excess act large). Not refuted at beta 2.3 L = 4 (D = 0.36) and L = 6 (D = -1.8), beta 3.5
  L = 4 (floor). Margins only; c_lb is a lower bound.
