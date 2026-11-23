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
