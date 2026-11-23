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
