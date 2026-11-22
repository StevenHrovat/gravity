# Handover: the Yang–Mills mass gap work, from the cloud session to a local one

Written 2026-11-21 by the cloud session that opened gravity#37, at the owner's request ("write everything you gather up into a handover
PR", "abort the long run", "I can start a new session locally"). The owner's goal, in their words: "I want to give it my best effort, to
really contribute, if possible in any way, to the YMMG problem, by giving Claude nudges in correct directions." This file is what the
next session needs to continue without re-doing anything. Read it first, then [`README.md`](README.md) (the explainer).

## 1. Where things stand

- **Done and checked:** DMP's own mass gap and the dictionary to lattice gauge theory, in Lean (`evidence/Dmp/MassGap.lean`,
  `evidence/Dmp/Gauge.lean`; 36 theorems, 279 in the chain, `evidence/tools/check.sh` green, CI green on the PR). The explainer, with the
  photon test, the three-piece map of the real problem (existence proven, strong-coupling lattice gap proven, the bridge open), the
  layer-by-layer (Migdal–Kadanoff) computation, the transfer ledger and findings MG1 to MG4 (`docs/findings.md`).
- **Computed:** Migdal–Kadanoff flows for SU(2) and U(1) in d = 3 and 4 (`results/mk_*.json`); SU(2) lattice at β = 2.3 on 10⁴
  (matches Teper); a 200-measurement U(1) smoke test (the photon is massless, as it must be).
- **Stopped part-way (owner's request):** SU(2) at β = 2.4 (14⁴, 400 of 2000 measurements) and β = 2.5 (16⁴, 150 of 1500); the
  scripts save only at the end, so nothing of those two runs survives. The U(1) production runs never started (a wait loop in the
  chaining script hung; the commands are below).
- **Honest assessment given to the owner** (2026-11-21, asked "could there actually be something to it?"): for physics, everything
  here is a correct restatement plus reproductions; nothing yet is new for the Yang–Mills problem. For DMP there are small real gains
  (MG1, MG2, MG3) and one useful negative (MG4: DMP's structures cannot be the mechanism of the physical gap). The owner then asked for
  a full-effort attempt at a real contribution; the ranked threads below are that plan.

## 2. Facts the next session can rely on (with sources)

| Fact | Source |
|---|---|
| OpenAI's Lean submission (28 Oct 2026, Lean 4.32.0, pinned Mathlib, 9,477 files, about 988k lines) proves existence of a Wightman theory as a subsequential scaling limit of 4D Wilson lattice theory for every compact simple group; "does not prove that the infinite-volume limit is unique or that there is a mass gap"; "The construction provides no evidence for or against a mass gap" | committee assessment, https://github.com/yang-mills-group/YM/blob/main/docs/assessment-1.pdf (p. 1, §2) |
| The committee's open list: convergence and uniqueness of the infinite-volume limit; a continuum probability measure; a uniform mass gap; Wilson loops and the area law; single-particle states | same, §8 |
| Checks the committee did not run: "An additional external kernel implementation was not used"; its Comparator runs used a macOS development launcher (no isolation) and the Lean 4.34.0 kernel against a 4.32.0 project | same, §9.2 |
| Lean 4.34.0 fixed two kernel routes to `False` (#14806 `is_def_eq` caching, #14807 `is_prop`) and one runtime one (#14838); "The bogus proof was also accepted by `nanoda`; `lean4lean` is believed not to have the bug" | https://lean-lang.org/doc/reference/4.34.0/releases/v4.34.0/ |
| Strong-coupling lattice gap: proven (Osterwalder–Seiler 1978; Shen–Zhu–Zhu arXiv:2204.12737, β < 1/(16(d−1)) for SU(N)); formalised for U(n), β < 1/(32n(d−1)), in `lgt`, whose "RG scale-transfer bridge" key fields are "still stated as hypotheses" | https://github.com/mrdouglasny/lgt (via the research notes, §2 below) |
| U(1) in 4D has a massless photon at weak coupling (Guth 1980; Froehlich–Spencer 1982): the photon test | README §3.2 |
| Tomboulis's decimation attempt (arXiv:0707.2179) has three unproven steps and "would seem to work" for U(1) too (Ito–Seiler arXiv:0711.4930, 0803.3019; Tomboulis's reply arXiv:0712.2620) | README §5 |
| SU(2) lattice reference numbers: Teper, hep-th/9812187, Table 10 (a√σ, am₀₊₊ per β) and Table 1 (m₀₊₊/√σ = 3.74 ± 0.12) | README §6 |
| Migdal–Kadanoff, d = 4: SU(2) β falls 0.252 per layer (one-loop: 0.2575); U(1) stalls, tail drift ≈ 20·e^(−14.4 β) per layer | `results/mk_*.json`, `hierarchy/summarise.py` |

**The prior research, worth reading before thread A or B** (claude-internal, branch `ccr-9ed5a4e8-x9lo61`, closed draft #165, 13 Nov
2026; parked, never merged; read with `git show origin/ccr-9ed5a4e8-x9lo61:"<path>"` in a claude-internal checkout):

- `reports/Yang Mills proof and GUID contribution.md`: the compiled report with six ranked contribution options and their first steps.
- `research_notes/Yang Mills proof and GUID contribution/openai_proof_facts.md`: what was claimed, proved and released (with the YM
  repository commit `55ba9fc` as read then, the three top-level targets `JointExistence`, `YangMills.constructed`,
  `YMReview.Acceptance.combined_acceptance`, the check table).
- `.../rigorous_yang_mills_open_problems.md`: the state before and after 2026, ranked open problems, partial routes, the formalisation
  ecosystem.
- `.../expert_reception.md`, `.../yang_mills_gravity_bridges.md`, and three inventories of the owner's own work.

These were true on 13 Nov. **Re-check every status before acting on it** (the field moves by the day).

## 3. The threads, ranked by what can really contribute

Each thread: why it counts, the first step, what it needs, and when it is done. The ranking is the cloud session's judgement; the owner
nudges.

### A. Independent-kernel replay of the existence proof (most realistic real contribution)

- **Why:** the committee skipped an external kernel. The project is on Lean 4.32.0, before the 4.34.0 kernel fixes, and `nanoda` shares
  one of the fixed bugs, so the replay that closes the gap is **lean4lean** (or a patched kernel) on an **exported** proof, in a sandbox.
  Gravity's own finding F3 applies word for word: two kernels fed by one exporter are not independent; say so in the report.
- **First step:** check whether it is already done. Read the issue trackers of `yang-mills-group/YM`, `hairer/humanise-yang-mills` and
  `scottnarmstrong/yang-mills-informalization` for "lean4lean", "nanoda", "external kernel", "replay", "export". If nobody has done it,
  continue.
- **Then:** on a Linux machine (WSL works) with at least 60 GB free disk: clone `yang-mills-group/YM`, record the commit, follow its own
  rerun notes (`submissions/openai-20261028/docs/rerun.md`; the research report names `python3 scripts/verify.py integrity`, then the
  build stage without `lake update`); export the dependency cone of the audited roots with a lean4export built on the project's
  toolchain and pinned by commit; replay with lean4lean (and with nanoda for comparison); record tool commits, hardware, wall-clock
  time, declaration counts, pass or fail.
- **Needs:** the committee's build took about 184 minutes on 8 Apple Silicon threads and about 52 GiB of disk (memory undocumented).
- **Done when:** a reproducible record (commands, pins, logs) is published as an issue in the right project, and the result is filed in
  Gravity (a short `docs/mass-gap/replay.md`). Claim nothing beyond "kernel X accepted export Y of commit Z".

### B. Statement-fidelity audit (logic level)

- **Why:** an outside contributor showed (`humanise-yang-mills` issue #58, 12 Nov) that `JointExistence` alone does not force the
  selected theory to come from the Wilson measure; the committee's own target is stronger. Gravity's refutation method (inert witnesses,
  `Dmp/Refute.lean`) is exactly this kind of check.
- **First step:** read #58 and the project's `CONTRIBUTING.md` and `AGENTS.md`; replay its witness on the pinned revision; then aim the same
  inert-witness test at `YangMills.constructed` and `YMReview.Acceptance.combined_acceptance`, clause by clause.
- **Done when:** a Lean file and a table (target, clause, satisfiable without the Wilson measure?) are offered to that project.

### C. Finish the lattice evidence (cheap, laptop)

From `docs/mass-gap/lattice/` (one core each; times on the cloud box, a laptop core is usually faster):

```sh
python3 run_su2.py 2.4 14 14 300 2000 24 su2_b2.4_L14.npz 3 2   # about 2 hours
python3 run_su2.py 2.5 16 16 300 1500 25 su2_b2.5_L16.npz 3 2   # about 3 hours
python3 run_su2.py 2.6 20 20 300 1000 26 su2_b2.6_L20.npz 3 2   # optional, about 5 to 15 hours
python3 run_u1.py 1.2 8 16 300 1500 31 u1_b1.2_L8.npz 3 2       # minutes
python3 run_u1.py 0.8 8 16 300 1500 33 u1_b0.8_L8.npz 3 2
python3 run_u1.py 1.2 12 24 300 1200 32 u1_b1.2_L12.npz 3 2     # about 15 minutes
python3 run_u1.py 0.8 12 24 300 1200 34 u1_b0.8_L12.npz 3 2
python3 run_u1.py 1.2 16 32 300 800 35 u1_b1.2_L16.npz 3 2      # about half an hour
```

Then move the `.npz` files to `../results/`, run `python3 analyse.py ../results/*.npz > ../results/lattice_summary.json` and
`python3 ../figures.py`, and update README §6. Done when β = 2.4 and 2.5 sit next to Teper's values and the U(1) photon's energy falls like
2π/L with the box size in the Coulomb phase while staying large in the confined phase. The GPU path (`lattice/run_su2_gpu.py`, added 2026-11-21,
GUID v7 kernels) does it about 100 times faster.

### D. Turn Ito and Seiler's objection into a number

- **Why:** README §5 measured the tree's U(1) drift; the published objection is about Tomboulis's modified recursion (the parameters α,
  t and the r < 1 device). Computing that recursion for U(1) and SU(2) shows exactly where the photon test fails in the most serious
  layer-based attempt.
- **First step:** read arXiv:0707.2179 (the recursion and its bounds) and 0803.3019 (the three gaps) and write down the recursion in
  `hierarchy/mk_flow.py`'s character-space form before computing anything.
- **Done when:** a table per group and β: does the modified flow reach strong coupling, and at which step does it break for U(1).

### E. Rigorous partial results (needs a human expert in the loop)

- Extend `lgt`'s strong-coupling gap (more groups, better β thresholds) or finish its 2D file, in Lean with Mathlib; or computer-assisted
  (interval-arithmetic) bounds that push the proven region towards weaker coupling at a fixed β. Publishable even when partial, but only
  with a reviewer from constructive field theory or probability. **Find that reviewer first** (C22: "the text itself is verified only by a
  reader who did not write it").

### F. For the owner, any time

- Findings MG1 to MG4 (`docs/findings.md`) wait for the owner's decision.
- A suggested side task (stale facts in Gravity's docs: the missing `Refute.lean` row, the Lean package version, the runner sentence) was
  queued from the cloud session.

### Planned phase: consolidation before the final write-up (the owner, 2026-11-21)

"Before we go further, we should clean all that stuff up and refactor our work [...] That would give a much nicer final result, while
still preserving the way through the git history." Once the weak-coupling attempts have a result, and before the final paper:
- **Lean (`formal/`)**: remove what the final chain does not use (e.g. the cluster-expansion area law is superseded by the twist area law;
  keep it only if the paper cites it as the independent cross-check), merge duplicated lattice lemmas, state theorems at their natural
  generality (any compact group / any plaquette weight where the proof allows it), one consistent naming scheme, and a short map from
  each paper claim to its theorem.
- **Gravity (`evidence/Dmp/`, `docs/mass-gap/`)**: drop superseded notes and scripts, fold the pre-registrations into one index with
  their verdicts, keep every stored result that a claim rests on.
- **DMP**: the few DMP theorems or readings that turn out unneeded or more general go to the DMP repository as proposals through its own
  process (gravity never edits `vendor/dmp`).
- The git history keeps the path; the consolidated tree is what readers see.
- **The final paper explains the theory and the proof itself; Lean is only for verification** (the owner, 2026-11-21, replacing the
  earlier "Lean chapter" plan: "having a guide to the lean seems excessive. We should instead focus on explaining the theory and proof as
  well as possible, so that lean really is just for what it's made for, machine verification, not explanation."). The paper carries the
  argument in mathematics and plain language, complete enough to follow without opening a Lean file; each formal result gets one line
  pointing to its theorem name for anyone who wants to check it by machine.
- **Framing of the contribution, and credit** (the owner, 2026-11-21): "All Insight is [...] a cycle of fuzzing the possibility space and then
  condensing it into actually good ideas to build upon. [...] I have no idea about the tools, but they allowed me to build a language that
  describes all of them [...] Given a tool, something can be done with it, without either the tool or an idea to use it on, neither really
  have a purpose. That is why I am so pedantic about crediting the giants upon whose shoulders I can stand to see." The paper presents its
  contribution as a language (DMP) that places established techniques where they belong (reflection positivity, Dobrushin-Shlosman,
  cluster expansions, centre symmetry, curvature, the renormalisation group, the 2026 construction), with each technique credited at the
  point where it enters the argument, not only in the bibliography.
- **A final round of review, tightening and optimising the paper's knowledge delivery** before it goes out (the owner: "It is the best
  vehicle to get our novel approach, which combines a potpourri of established techniques to make it work mathematically, across to any
  reader."): adversarial review for correctness and claim level, a readability pass for the target reader, and a tightening pass
  (remove what does not serve the argument, make the line of the argument visible: which established technique enters where and why).

### Aspirational: the OpenAI construction in our system (the owner, 2026-11-21)

"Since the current proof is not understood, [...] reformalize OpenAI's proof in our system. That would put a nice bow on it." Scale: the
construction is about 988k lines in 9,477 files (Lean 4.32; the committee's build took about 3 h on 8 cores, 52 GiB disk); `balaban-lean`, a
similar short-distance RG for the simpler O(N) model, is 1.09M lines and unfinished. Staged plan:
1. **Guided reading** (days): an architecture map in plain language (what each part constructs, the key theorems, where reflection
   positivity, chessboard estimates and the Balaban-style RG map sit, how the subsequential limit is taken); feeds the paper's
   explanation chapter.
2. **Statement bridge** (similar): their main theorem restated in our vocabulary, and a proof that our lattice measure (`productHaar` with
   the Wilson weight) is their lattice measure, so Corollary B's "survives every continuum limit" connects to their limit formally.
3. Reformalise the parts our chain touches (reflection positivity, the subsequential limit): tens of thousands of lines.
4. The full short-distance RG: months; aspirational.
Timing (the owner, 2026-11-21): stages 1-4 run sequentially, roughly after the paper and all its associated work are done, as a
background effort while the paper and its material are with expert reviewers; no deadline, "just see how it goes".

## 4. Rules that held, and should keep holding

- **Claim level:** a theorem is what Lean's kernel checked, a number is what a script reproduces; neither is a proof of the mass gap.
  The "what not to claim" lists in README §8 and in the research report stand.
- **The photon test** for every proposed mechanism: an argument that would also give light (4D U(1) at weak coupling) a mass is wrong.
- **Pre-register** a numerical test (observable, window, failure criterion) before running it, as GUID v6 did.
- **Gravity's rules:** `vendor/dmp/` is never edited here; every change is a pull request; `evidence/tools/check.sh` and
  `tools/scrub-scan.sh` before every push (in the cloud box the scan needs `LC_ALL=C.UTF-8`, or its German-letter pattern matches every
  multi-byte character; transliterate names such as Froehlich); roles, not values (no host names, accounts or addresses).
- **Ask the nearest tier first**, name the record used, and say in one line when a search came up empty (CM's CLAUDE.md, chapter 14).

## 5. Local setup (laptop, WSL)

```sh
cd ~ && git clone https://github.com/StevenHrovat/gravity.git && cd gravity && git checkout ccr-be614210-u4r7na
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain "$(cat evidence/lean-toolchain)"
python3 -m pip install --user numpy scipy mpmath matplotlib
evidence/tools/check.sh                                   # expect: OK 285 theorems (279 before Reach.lean)
python3 docs/mass-gap/hierarchy/summarise.py              # reprints the README §5 tables from results/
```

(Use the existing checkout instead of cloning if there is one; the branch is the head of gravity#37.)

## 6. Starting prompt for the local session

```text
Continue the Yang–Mills mass gap work in the gravity repository, branch ccr-be614210-u4r7na (pull request StevenHrovat/gravity#37).
Read docs/mass-gap/HANDOVER.md first, then docs/mass-gap/README.md, and set up with HANDOVER section 5 (Lean via elan, Python with
numpy, scipy, mpmath, matplotlib; evidence/tools/check.sh must report 285 theorems).

My goal: make a real, verifiable contribution to the Yang–Mills existence and mass gap problem. I am a sysadmin, not a mathematician:
explain in infrastructure pictures, recommend one way forward rather than a menu, and I will nudge you in directions. Use this laptop's
cores for long computations.

Plan:
1. Start the lattice runs of HANDOVER thread C in the background, one per spare core, leaving one core free. They need no attention.
2. Thread A: first find out whether an independent-kernel replay (lean4lean, or a patched kernel) of the 2026 Yang–Mills Lean proof
   already exists, in the issue trackers of yang-mills-group/YM, hairer/humanise-yang-mills and scottnarmstrong/yang-mills-informalization,
   and report what you find with links. If nobody has done it, plan the replay on this machine (disk, memory, time, tool pins) and tell me
   what it needs before starting the multi-hour build.
3. Then threads B and D, in the order you judge best; thread E only once we have a human reviewer.

Rules: HANDOVER section 4 (claim level, the photon test, pre-registration, Gravity's pull-request and check rules). Facts in HANDOVER
were true on 13 and 21 November 2026; re-check each one before relying on it. Keep progress in pull requests in gravity (update #37 or
open follow-ups) so the work can be continued. If you have open questions, ask them in one block early; otherwise go ahead.
```

## 7. Local session log

- **2026-11-21, laptop session.** Lean set up in WSL (`check.sh`: OK 279 theorems). Thread C runs started on the laptop, one core each,
  after a pre-registration ([`lattice/PREREG.md`](lattice/PREREG.md)); the run scripts now write a checkpoint every 50 (SU(2)) or 100
  (U(1)) measurements, so a stopped run keeps its data. Thread A searched: no independent-kernel replay exists; findings and the plan in
  [`replay.md`](replay.md), waiting for the owner's go-ahead. Thread B: humanise-yang-mills already proved in Lean that the public target
  `JointExistence` is met by a generalized free field (their PRs #339, #359, #380); what is left for B is the committee's stronger
  `combined_acceptance` (their issue #382 leaves "whether the stronger target admits a degenerate lattice family" undetermined).
- **2026-11-21, later.** Owner's decision: drop the kernel replay beyond prep work and focus on the mass gap. Threads A and B are
  closed here (others are better placed); `replay.md` keeps the search result and the scripts. Next: a mass-gap concept for the owner
  (proven-gap region pushed outward by computer-checked bounds, see the session's proposal), plus thread C's runs.
- **2026-11-21, evening.** With the owner's readings the mass-gap work moved to DMP's own terms: MG5 (IM versus payload is the
  carriers' self-charge; SU(3) zoom-out rate 2.26 against 2.25 predicted), MG6 (in DMP the gap is a node's bounded radius, an axiom),
  MG7 (inside DMP the gap follows from Axiom 1's reach; `Dmp/Reach.lean`, 4 theorems, 283 in the chain; in physics words "confinement
  implies the gap", so the open requirement is that Yang–Mills obeys Axiom 1 for its IM). Thread C: U(1) photon test done (tension by the
  pre-registered rule); SU(2) β = 2.6 stopped at 150 measurements by the owner's leave, β = 2.4 and 2.5 finishing. Threads A and B
  dropped; the quick shots of `dobrushin/` closed the threshold route.

### State at 2026-11-21 ~20:30 (before a context compaction)

Running in the background:
- **Leg B (GPU, overnight):** `lattice/queue_boundary_gpu2.ps1` (reordered: larger boxes β 2.3/ℓ 12 and β 2.4/ℓ 16 first, then β 2.5 flux
  and hot (flux rerun: the first attempt ended with its stopped coordinator), β 2.6, β 2.7 last); log `lattice/runs-gpu/boundary/queue_boundary.log`;
  final analysis `analyse_boundary.py` writes `boundary_summary.json` / `analysis.log` after the photon gate.
- **Leg B controls (CPU):** `lattice/queue_boundary_cpu.ps1` (U(1), Z₂ controls, then the photon gate: "PHOTON TEST PASSED/FAILED" in the
  log). The SU(2) result counts only if the gate passes. Pre-registration with all run-order changes: `lattice/PREREG-BOUNDARY.md`.
- **Attempt round 2** (four Opus agents, notes in `weak-coupling/attempts/r2-2d/`, `r2-coupling/`, `r2-curvature/`, `r2-stepscaling/`;
  Lean in `formal/Attempts/R2/`): A certified 2D worked example; B reflection-positive coupling; C H2 via curvature at L₁; D H1 step-scaling
  interface. Each to be verified (build, escape-hatch scan, axioms) and committed by the coordinating session.

To do next: verify and commit round 2; when Leg B finishes, run the analysis against `PREREG-BOUNDARY.md` (photon gate, Q1, Q2, the decision
rule in `weak-coupling/PREP.md`, the effective coupling at L₁ for attempt C, the twist at the larger box for the root swap); then decide
round 3 or Leg C (bootstrap speed-up, VM prompt when RAM-bound); then the consolidation phase and the paper (plan in this file, §3 planned
phases: the paper explains theory and proof itself, credit at point of use, final review round).

Where things stand: the reduction is machine-checked from H1 `EffectiveConvergence` + H2 `LimitGDS_W` (`formal/OneScale/Effective/Physical.lean`,
`gap_of_effective_W`) and from `UniformGDS_W` (`OneScale/CorollaryBW.lean`); existence layer (reflection positivity, incl. admissible
weights), strong-coupling gap, reach, area laws (SU(n)) proven; round 1 (`weak-coupling/attempts/ROUND-1.md`): one common obstruction
(local flatness; contraction only at the physical scale; exact AF coefficient needed); follow-ups: a Schroedinger-functional-type coupling
runs by the exact rate, 2D U(1) one-box bound switches on near 3/√σ. The owner's readings: `weak-coupling/PREP.md` (guiding principle,
root swap, naked duality, H1/H2 as how/what of existence and quantum/classical halves, curvature tools, existence boundaries).

### State at 2026-11-22 ~03:45 (before a context compaction): the proof phase, cycle 3 running

**Since the last state note:** rounds 2–4 done and reviewed (`weak-coupling/attempts/ROUND-2.md`, `ROUND-3.md`, `ROUND-4.md`; two Fable
reviews `attempts/r3-review/REVIEW.md`, `attempts/r4-review/REVIEW.md` and the free-wins pass `attempts/r4-review/FREE-WINS.md`, which
corrected overclaims: verify the CONTENT of headline theorems, not only build and axioms). Leg B finished; result in
`lattice/PREREG-BOUNDARY.md` (photon gate passed; Q1 fails: the measured decay length is lattice-scale at every β; Q2 twist long-range).
Round 5 is a **proof phase** (the owner's goal: the full proof): map `weak-coupling/PROOF-BLUEPRINT.md` (v2+, two routes, statuses),
reading pack `weak-coupling/proof-phase/READING.md`, rules in `attempts/RULES.md` (phase section: the owner's guiding principle, claim
discipline, unit tests: photon, Z₂, finite subgroups, deconfinement, triviality, Banks–Zaks, mixture, Heller endpoint).

**The assembly (Lean, `formal/ProofPhase/`, lakefile lib `ProofPhase`):** `ProofPhase.Torus.Top`: `yang_mills_assembly` (OpenPieces ⇒
MassGapLoc ∧ LimitRP ∧ NonTrivial) and `yang_mills_assembly_torus` (both orders of limits). Open inputs of the preferred torus route:
`H1Local`, `LimitDprime` (⇐ AdjointHalf ∧ CentreHalf, `Adjoint/CentreSplit.lean`), `ObsTransferPhys`, the line of constant physics
(`OnLCP`, slope 11/(6π²) for our weight exp(β Re tr U)), `NonTrivial`. Route B lands on Route A; Conjecture S breaks at small loops (the gap
is decided on ≤ 3-plaquette loops). Noise-limit trap: Leg C's β 2.3 "click" had no adjoint signal.

**Running now:**
- **GPU queue (chained, starts itself):** Leg C `weak-coupling/attempts/r3-blocked/queue_blocked_gpu.ps1` (β 2.4 and addendum left; log
  `r3-blocked/runs-gpu/queue_blocked.log`, ends "BLOCKED DONE" / addendum "ADDENDUM DONE"), then the act number
  `weak-coupling/attempts/r4-actnumber/queue_actnumber_gpu.ps1` (no four-move addendum; log `r4-actnumber/runs-gpu/queue_actnumber.log`).
  After it: the good-blocking refit (cycle 3 workstream 2 prepares its queue; the coordinator starts it).
- **Cycle 3 workstreams (Opus):** c3a-uv (`ObsTransferPhys` for the good blocking; `formal/ProofPhase/UV/`), c3b-refit (pre-registration of the
  good-blocking refit with a ≥ 3σ content check), c3c-certified (certified adjoint window; `formal/ProofPhase/Certified/`), c3d-h1 (`H1Local`
  uniform in the lattice; `formal/ProofPhase/H1/`). Notes in `weak-coupling/proof-phase/c3*/`.

**To do next:** verify each workstream (read headline statements; build in WSL with `FORMAL_DST`; axioms; scrub scan checking its exit
code; transliterate umlauts), commit, gated push; when Leg C ends, run its analysis and c2a's `evaluate_adjoint.py` on β 2.4; start the
refit queue; update the blueprint; propose cycle 4. Fable review: the owner wants it after construction, not now. The owner's readings of
the phase are at the end of `weak-coupling/PREP.md` (act identity, what is conserved, tie to G0 = reach, something must run, exclusion vs
existence, sector transfer as how existence is built, switching dimensions).
