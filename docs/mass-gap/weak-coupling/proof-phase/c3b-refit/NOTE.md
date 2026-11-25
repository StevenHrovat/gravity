# Cycle 3, workstream 2: the real click test, prepared (2026-11-22)

Brief: prepare, pre-register and CPU-test the refit of the blocked SU(2) action with **the good blocking** of
`formal/ProofPhase/RouteA/Blocking.lean` as the block variable, with a mandatory content check, at L₁√σ ∈ {2.5, 3, 4} plus a second
β; evaluate the adjoint and centre halves (sup and W₁); gates photon, Z₂ deconfined, deconfinement edge; a queue that waits for the
act-number queue. No GPU was used; nothing outside this folder was written; nothing committed.

Claim levels as in `../../attempts/RULES.md`. Everything here is **instrument** (code, tests, pre-registration); there is no result
about SU(2) yet. The pre-registration is `PREREG.md`; read it for the definitions.

## 0. At a glance

1. **Question (PREREG.md):** does the good-blocking variable keep content at L√σ between 2 and 4.2 (adjoint and fundamental coarse
   plaquettes resolved at ≥ 3σ in both plane classes, half-block Creutz ratio within [0.5, 1.5] of σ), and where it does, does its
   fitted blocked action satisfy the halves criterion (`limitDprime_of_halves`: γ_A + γ_C < 1) in TV or linearised W₁ form? Points
   without content are reported as "NO CONTENT" and do not count.
2. **Instrument:** `goodblock.py` (the blocking exactly as `smearBlock w` iterated; anisotropic Schwinger–Dyson sums; Wilson loops of
   the half-block lattices; Leg C's generator imported unchanged), `analyse_refit.py` (anisotropic fits, class-resolved pair tables,
   halves, content check, gates, flags, scaling check; Leg C's error code and workstream A's constants imported unchanged),
   `wscan.py` (choice of w), `pipeline_test.py`, `queue_refit_gpu.ps1`.
3. **w = 2**, chosen by a rule fixed before the one-loop scan (smallest weight within 5 % of the minimal one-loop coarse-plaquette
   variance at ℓ = 16, no growth from ℓ = 8, no Z₂ ties).
4. **Lattices:** 48⁴, b = 4, 8, 16, at β = 2.3 (L√σ = 1.40, **2.80**, 5.60), 2.4 (1.03, **2.06**, **4.13**), 2.5 (0.73, 1.46,
   **2.92**); scaling pair 2.80/2.92; four points at or below the deconfinement edge as direct negative controls.
5. **CPU:** selftest 18/18 PASS (60 s); pipeline test 305 s, every stage and verdict produced (12⁴, not physics).
6. **GPU estimate: about 2.8 h ± 50 %** (1.4 to 4.2 h), peak memory about 4.5 GB.
7. **Expected (before data, not a criterion):** content PASS at most at L√σ ≈ 2.06; **NO CONTENT from about 2.8 on is the probable
   outcome**, because a coarse plaquette of the good blocking is a spatially smeared L × L Wilson loop (area law; adjoint screening). Section 3.

## 1. Design decisions (behaviour and trade-offs)

* **The blocking, exactly.** Straight path plus w times the spatial staples (4 for a spatial link, 6 for a temporal one), projected
  to SU(2) (`A/√det A`), iterated; spatial links stay in their time slice, temporal links in their strip. Implemented on the even
  fine grid so that every even site is a coarse origin: (b/2)⁴ coarse lattices per configuration (16, 256, 4096 for b = 4, 8, 16),
  all with the same law by translation invariance; this multiplies the coarse-plaquette statistics at b = 16 without changing the
  variable. Tested against an independent scalar path recursion, decimation at w = 0, gauge covariance, the time reflection
  (`smearBlock_thetaConn` holds numerically to 10⁻¹⁶) and the U(1) and Z₂ subgroups.
* **The refit had to become anisotropic.** The good blocking smears in space only, so the blocked action has separate couplings
  for time–space and space–space plaquettes. Leg C's isotropic fit would be mis-specified (the pipeline test shows the size of the
  effect: at 12⁴, β = 2.3, b = 4, β_F is 0.42 (ts) against 0.86 (ss)). The SD sums, the Z₂ pseudo-likelihood, the D′ pair tables and
  the W₁ columns are therefore split by plane class; the halves take the maximum over link types (temporal links see 6 ts
  plaquettes, spatial links 2 ts and 4 ss), and γ_A + γ_C uses the maximum of each half separately, as the Lean hypothesis needs.
  For isotropic couplings everything reduces exactly to workstream A's `evaluate_adjoint.py` (checked).
* **w = 2.** One-loop variance σ²(16) (ts/ss): 0.276/0.239 at w = 0.5, 0.220/0.178 at w = 1, **0.201/0.161 at w = 2**, 0.196/0.163 at
  w = 4; decimation 15.1. Beyond w ≈ 2 nothing is gained. At w = 2 the straight path carries 1/9 (spatial) or 1/13 (temporal) of
  the weight. Z₂ path sums are odd integers, so the projection is never undefined.
* **Content check, part C3.** Coarse Wilson loops larger than the plaquette do not fit on 3⁴–6⁴ coarse lattices and would be far too
  small anyway, so the σ check uses the half-block lattices (spacing L/2), whose 2 × 2 loop has the same physical size as the coarse
  plaquette. Reported alongside: retention ratios (coarse plaquette over the half-block 2 × 2 loop) and a thermalisation drift.
* **Photon gate, item 2 changed from "flat" to "does not fall, rises at most 50 %"** (stated with its reason before data). The
  one-loop variance at w = 2 still falls with ℓ, so the blocked photon coupling should rise by about 20–28 % from b = 4 to 16, near
  the limit of Leg C's symmetric 15 % rule. A rising photon coupling is the opposite of the noise limit the gate is there to catch;
  Leg C's rule is still reported. If the gate fails, the queue stops before SU(2).
* **No noisy variants.** The good blocking is the variable of the halves route in the Lean assembly
  (`massGap_of_goodBlocking_halves`), deterministic; Leg C's noise variants served r3-robust's chain, which is not used here.
* **Volume.** 48⁴ is the largest volume that fits comfortably (2 chains). b = 16 runs on 3⁴ coarse tori (as Leg C's b = 12); D′
  verdicts use the infinite-volume tables; there is no 4⁴ partner (N = 64 would need about 8 GB).

## 2. CPU test

* `goodblock.py selftest` (`cpu-test/selftest.log`): 18/18 PASS in 60 s; list in `PREREG.md`, "The block variable".
* `pipeline_test.py` (`cpu-test/pipeline.log`, `cpu-test/analysis.log`, `cpu-test/summary.json`): U(1) 1.1, Z₂ 0.6, SU(2) 2.3 and
  2.5 on 12⁴, b = 2, 4, 2 chains × 24 measurements, one process, 305 s; photon-gate mode prints PHOTON GATE PASSED; the full analysis
  produces every verdict, the content check (NO CONTENT everywhere at this size: the Creutz ratio is 1.6–6.4 in a 4.2/√σ box), the
  gates (photon PASS, Z₂ PASS), the flags (none) and the scaling check (exercised on an unmatched pair). Not physics.
* `bench --cpu` at 12⁴: code path runs. The queue script parses (PowerShell parser, 0 errors).
* Not tested on CPU (no GPU use allowed): the cupy paths (chain extraction straight from the 2 × 2 form, cupy takes and bincount).
  The queue's first step `selftest --gpu` compares GPU against CPU on blocking, sums and loops for all three groups and checks the
  chain extraction; if the fused kernel fails it retries with the array-code path, and stops if both fail.

## 3. Decision for the coordinator

1. **The content check will probably rule out L√σ ≥ 2.8 by physics, not by the variable.** A coarse plaquette of the good
   blocking is a spatially smeared L × L Wilson loop: about e^{−σL²}, i.e. 4·10⁻⁴ at 2.80, 4·10⁻⁸ at 4.13; the adjoint loop is smaller still
   (Casimir scaling, then screening). With about 10⁻⁴ statistical error, C1/C2 are expected to pass at 2.06 at best. Then the run
   answers "does the good blocking keep content and what does its action look like at 2.06 (and maybe 2.80)", plus the gates and
   edge controls, but cannot show a counted click at 3–4. Leg C's variable resolved its fundamental plaquette at 3.15 (2.2·10⁻³), probably because
   its 4D flow shrinks the effective loop; the good blocking smears only in space, so I do not expect that here.
   **Recommendation:** run as pre-registered (it is the honest test of the brief, and the 2.06/2.80 points decide whether the good
   blocking avoids the noise trap where content is measurable at all). If you want points at 3–4 to be able to count, a
   different content criterion is needed, and it must be fixed **before** the data: e.g. content inherited from the half-block
   level (C1–C3 passing at L/2 for the same run) together with a resolved retention ratio. I have not pre-registered such a rule,
   because it would weaken what the brief made mandatory.
2. **Photon rule** (item 2): accept "does not fall, bounded rise" in place of "flat" (reason in §1), or restore the symmetric rule
   (then a spurious stop of the queue before SU(2) is possible if the rise exceeds about 15 % of the mean).
3. **Budget:** central 2.8 h, upper end 4.2 h. If the bench projection exceeds 4 h, stop after run 4 (β = 2.4): run 5 (β = 2.5) is
   last and costs 49 min; it carries 2.92 and the scaling check.
4. **Queue wait condition:** it waits for the act-number log's "ACTNUMBER DONE" line **or** that queue's early-stop lines
   ("SELFTEST FAILED", "PHOTON GATE FAILED"), since in those cases no DONE line ever comes; then for no actnumber.py, blocked.py or
   boundary.py process (checked twice, 3 minutes apart). If the act-number queue is restarted with `-AddendumW`, its DONE line
   still comes last, after the addendum.
5. **Start:** `pwsh -File queue_refit_gpu.ps1` in this folder, any time; it waits by itself. Outputs in `runs-gpu/`
   (`queue_refit.log`, per-run logs and `.npz`, `analysis.log`, `refit_summary.json`); last line "REFIT DONE".

## 4. Unit tests

Photon: gate (centre half must exclude it; adjoint half alone is not asked to). Z₂ deconfined: gate. Deconfinement: three SU(2)
points below 1.45/√σ and one at it, flagged if NOT_EXCLUDED. Finite subgroups, triviality, Banks–Zaks: not run (no update code for
finite subgroups; the others do not apply to a measurement on SU(2)).

## 5. Blueprint

Changes nothing yet. When run: P4.1′ numerics (the halves on a fitted action of the good blocking, with content), replacing
workstream A's near-noise Leg C reading; the run cannot discharge `AdjointHalf` or `CentreHalf` (fitted, truncated actions).

## Files

`PREREG.md`, `NOTE.md`, `goodblock.py`, `analyse_refit.py`, `wscan.py` (+ `wscan.log`, `wscan.json`), `pipeline_test.py`,
`queue_refit_gpu.ps1`, `cpu-test/` (selftest, pipeline, analysis logs, the 12⁴ `.npz` files, `summary.json`).
