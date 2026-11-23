# Independent re-check of the Lean layer

Run of 2026-11-23, Lean v4.34.0, Mathlib v4.34.0 (commit `5ed2965256430c3649e86755f9576b54eca72435`).
Script: `tools/independent-check.sh`. Condensed log: `docs/unified/independent-check.log`. Trusted-base stamp: `docs/unified/independent-check.stamp`.

## In plain words

Every Lean proof of the project (six libraries, 317 modules when the run started) was checked again by programs other than the
Lean run that built it. **Every check passed. No proof was rejected.**

- **Lean's own replay checker (`leanchecker`)** took every declaration of the finished build, project and Mathlib together, and fed it
  once more through Lean's kernel, in an empty environment. It passed. This catches tampering with the build (a macro or tactic that
  slipped a declaration into the environment without the kernel seeing it), but it is the *same* kernel code as the original run.
- **`nanoda_lib`** is a different kernel: a separate program in Rust, written by someone else from the published type theory. The
  whole environment (728,263 declarations: project, Mathlib, Batteries, Lean core) was exported with `lean4export` and re-checked by it.
  It passed: "no typechecker errors". This is the check that does not share code with Lean's C++ kernel, so a soundness bug in that kernel
  would have to be reproduced in two independently written programs to go unnoticed.
- **`lean4lean`** is a third kernel, written in Lean. Its author says it follows the C++ kernel closely, so it is less independent than
  `nanoda_lib`; it is a second opinion on top. It passed on 315 of 317 modules; the other two are the empty root files (see below).
- **Axiom audit.** A traversal of the environment written for this check (it does not trust the cached axiom lists inside the
  `.olean` files) went over every declaration of the project and everything they use. The only axioms met: `propext`,
  `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`, no `Lean.ofReduceBool`, no extra axiom, in the compiled
  environment or in the sources.

**What this does not check:** that the Lean *statements* say what the paper means. A kernel proves what is written, not what was intended.

## Checkers

| Checker | Version / source | What it is |
|---|---|---|
| `leanchecker` | shipped with Lean v4.34.0 (the former `lean4checker`; the standalone repository has no tag for v4.34, the toolchain's own copy is the matching one) | replays declarations through Lean's C++ kernel |
| `lean4export` | github `leanprover/lean4export`, tag `v4.34.0` (export format 3.1.0) | writes the environment as a file for external checkers |
| `nanoda_lib` | github `ammkrn/nanoda_lib`, commit `0da9f98feadd` (2026-11-07), crate version 0.4.32, built with cargo release | independent kernel in Rust |
| `lean4lean` | github `digama0/lean4lean`, commit `0048ed7` ("bump Lean toolchain to v4.34.0") | kernel written in Lean |

Settings for `nanoda_lib`: Nat and String kernel extensions on (as Lean's kernel has them); permitted axioms `propext`, `Classical.choice`,
`Quot.sound`, plus `Lean.trustCompiler`, named only because Lean core's own `reduceBool`/`reduceNat` declarations mention it.
`Lean.ofReduceBool` and every other axiom are *not* permitted (skipped), so a declaration that used one would fail; none did.
Every `nanoda_lib` run ends with the line "1 pretty printer errors: Unable to print axioms": that is the pretty printer's optional axiom
listing, not type checking; the same run reports "no typechecker errors".

## Results

### Build (task 1)

All six libraries build with no errors, all 317 modules (AreaLaw 26, Influence 3, Positivity 11, OneScale 21, Attempts 35, ProofPhase 221),
in a private copy of the build project (so other sessions' builds were not disturbed). The build was mostly up to date; Lake verified the
sources against its stored hashes. `Attempts` and `ProofPhase` have no root file, so every module is named explicitly (a plain
`lake build Attempts` fails for that reason). The build prints up to 339 style warnings per library (Influence none) (unused variables and the like), no errors.

### Per library

| Library | Modules | Declarations (theorems) | nanoda: declarations checked incl. what they use, time | Source tokens |
|---|---|---|---|---|
| AreaLaw | 26 | 1,256 (947) | 51,311, 8 s | none |
| Influence | 3 | 41 (38) | 27,702, 3 s | none |
| Positivity | 11 | 465 (390) | 39,479, 5 s | none |
| OneScale | 21 | 578 (469) | 41,495, 6 s | none |
| Attempts | 35 | 1,030 (806) | 47,445, 6 s | none |
| ProofPhase | 221 | 7,492 (5,534) | 84,416, 21 s | none |
| **Project** | **317** | **10,862 (8,184)** | **86,024, 24 s** (all libraries together, with what they use) | none |
| Whole environment | | | 728,263, 363 s | |

Declaration counts include compiler-generated helper declarations. Counts are from the first audit; later edits by other sessions added
10 modules (see below): 11,195 declarations (8,406 theorems), ProofPhase 7,825 (5,756). The "Source tokens" column is a grep for
`sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `extern` outside comments: zero hits. Two docstrings say "no `sorry`".

Per library result of each checker:

| Library | `leanchecker` (inside the whole-environment replay) | `nanoda_lib` | `lean4lean` | Axiom audit |
|---|---|---|---|---|
| AreaLaw | pass | pass | pass (25 submodules; root file empty, not run) | 3 standard axioms |
| Influence | pass | pass | pass | 3 standard axioms |
| Positivity | pass | pass | pass | 3 standard axioms |
| OneScale | pass | pass | pass (20 submodules; root file empty, not run) | 3 standard axioms |
| Attempts | pass | pass | pass | 3 standard axioms |
| ProofPhase | pass | pass | pass | 3 standard axioms |

**Failures: none.** What did not run to completion, listed exactly:
- `leanchecker` as a per-library run was killed for lack of memory (exit 137) for AreaLaw and OneScale while other jobs were running, and
  not run for Attempts and ProofPhase. Influence and Positivity passed that way. The whole-environment replay (below) covers all libraries
  in one process and passed, so every project module was replayed.
- `lean4lean` on the root files `AreaLaw.lean` and `OneScale.lean`: killed for memory (a root name makes it replay all submodules at once,
  26 GB). Those files contain only imports and a docstring (the script checks this), so nothing is left unchecked; every submodule passed.
- One full `nanoda_lib` run was stopped by me after about 25 minutes by mistake (I ended the shell that was running it). Rerun: passed.

### Run times (one heavy job at a time)

| Step | Time | Memory |
|---|---|---|
| `leanchecker --fresh` over the whole environment (project + Mathlib + Batteries + Lean core) | 1,646 s (27 min) | 8 GB |
| `lean4export` of the whole environment (6.0 GB, 113 M lines) | 352 s | 12 GB |
| `nanoda_lib` over that export | 363 s | 6.4 GB |
| `lean4export` of the project closure only (743 MB) | 45 s | 2 GB |
| `nanoda_lib` over the project closure (86,024 declarations) | 24 s | 0.9 GB |
| axiom audit of the whole project | 4 to 10 min (depends on machine load) | 7 GB |
| `lean4lean`, 315 modules | 44 min (three at a time at first, then one at a time) | 5.8 GB per module |
| hashing the Mathlib/core `.olean` files for the stamp | about 1 min | small |

So a **full** run is about 45 to 50 minutes of compute if run in this order, plus 45 minutes if `lean4lean` is included.

**Memory.** The largest single module needs about **5.7 to 5.8 GB** peak, measured for `lean4lean` on the four largest source files and a
module with zero declarations (5.78 GB); the number does not grow with the module's size. Every checker process first loads the whole environment
(Mathlib is most of it), which costs about 5.7 GB and 4 to 5 seconds before it checks a single declaration. This is why running several at once is
dangerous (the machine has 27 GB): three processes at once, or one library-wide run (which starts one task per module: 20 to 27 GB), starve
other builds or get killed. The script now runs one module per process, one process at a time.

### Where the cost goes: general layer versus instances

Checker cost follows the number of declarations checked, plus a fixed base of loading Mathlib. `nanoda_lib` shows it directly: Influence
(41 declarations) costs 3 s and 27,702 declarations checked, almost all of that the Mathlib part it uses; ProofPhase (7,492
declarations) costs 21 s. The project's own declarations add about 2 to 3 ms each over the fixed 3 s. A general lemma is checked once as
one declaration, and every instance that uses it only *refers* to it: the checker does not re-derive it per instance. So a general theorem
for every SU(N) (the reflection chain in `General/SUNTwist.lean`) costs the same as one instance of it; the instances cost only their own
glue. Checking is cheap compared with loading the environment, so the saving from generality is in proof size, not in this check's wall time.

## Split: our proofs versus Mathlib (the stamp)

Mathlib is the bulk of every full check (728,263 declarations of which about 11,000 are ours). So the check is split in two, as the owner proposed:

1. **Trusted base, checked once, recorded as a stamp.** After the full independent check passed, `docs/unified/independent-check.stamp`
   records: result `PASS`, date, Lean toolchain, the Mathlib commit from the lake manifest, the number of non-project `.olean` files and a
   hash over all of them (10,744 modules: Mathlib, Batteries, Lean core and the other packages the project imports), the SHA-256 of the exported
   environment, and the checkers and versions.
2. **Every later run (`quick`)** first recomputes the hash of those `.olean` files and matches it against the stamp (52 s). On a match, Mathlib
   and Lean core are taken as checked and only the project's own declarations are re-checked. On any mismatch (new Mathlib, new Lean, a changed
   file) `quick` refuses and a new full run, and a new stamp, is needed.

This is the same principle as the vendored stamp in DMP: the correctness of the base is established once, by hash, and then assumed.

Mathlib's own CI: it does run a replay check, but only partly. The workflow `.github/workflows/daily.yml` at Mathlib v4.34.0 has a daily job
`check-leanchecker` that runs `lake env leanchecker --fresh Mathlib` and `--fresh Batteries` on `master` and on the latest nightly. The ordinary CI
does not ("we no longer run lean4checker in regular CI, as it is quite expensive", `build_template.yml`), and the job is not run on the
`v4.34.0` tag itself. It is the same C++ kernel, so it is replay, not an independent check. No independent kernel runs on Mathlib in its CI that we found.
For a pinned release the stamp's own run (whole environment by `leanchecker --fresh`, `nanoda_lib`) therefore adds real assurance.

## Incremental

A module is re-checked only if its key changed. The key is a hash of the module's source, the keys of the project modules it imports (so a
change ripples to its dependents), the Lean toolchain and the Mathlib pin. Passed keys are stored; a changed module is replayed by
`leanchecker`, audited for axioms, and its declarations plus what they use are exported and re-checked by `nanoda_lib`.

| Run | What changed | Time |
|---|---|---|
| Full, first time | everything | about 45 to 50 min of compute (about 95 min with `lean4lean`) |
| `quick`, nothing changed | 0 of 323 modules | **124 s** (66 s sync and build, 52 s stamp check, 6 s key comparison) |
| `quick`, 10 new modules added by other sessions | 10 modules, 279 declarations | 1,404 s with the old whole-project axiom audit (638 s of it); the audit now covers only changed modules; replay 9 s per module, `nanoda_lib` 16 s |

Before this work, the only way to ask the question was a library-wide replay (hours, killed by memory), so the full-versus-incremental
difference is: about 50 minutes once, then about 2 minutes when nothing changed and a few minutes when a handful of modules changed.
`DRY=1 bash tools/independent-check.sh replay-inc` shows how many modules a change would re-check before running anything.

## What state was checked

The checks ran in a private copy of the build project. The full run covers the sources at git HEAD `9cb8837` (317 modules). While it
ran, other sessions added 10 modules (333 declarations); they were picked up by the incremental run (replay, axiom audit, `nanoda_lib`:
all passed). `lean4lean` ran on the earlier 317 modules. A `quick` run after any later edit covers that edit.

## What remains trusted

- **The checkers' own correctness.** `leanchecker` and `lean4lean` descend from the same design as Lean's kernel; `nanoda_lib` does not,
  and agreement of an independently written kernel is the main assurance. If both Lean's kernel and `nanoda_lib` shared a bug, we would not see it.
- **`lean4export`**, which writes what the checkers read: a bug there could hide a declaration from the checkers. (The count it exported
  matches what the audit found reachable: 86,024 against 86,613, the difference being axioms and a few auxiliary names.)
- **Lean's type theory** itself (its consistency is assumed) and the **three axioms** `propext`, `Classical.choice`, `Quot.sound`.
- **The stamp for Mathlib and Lean core:** after the first full run, their correctness is assumed on a hash match, not re-derived.
- **That the statements mean what the paper means** (see above), the operating system and the hardware.

## Re-running

In the Linux/WSL shell, from the repository:

```bash
bash tools/independent-check.sh setup        # once: installs the checkers under ~/checkers
bash tools/independent-check.sh full         # first time, or after a toolchain / Mathlib change (about 50 min; writes the stamp)
bash tools/independent-check.sh quick        # every later run
bash tools/independent-check.sh lean4lean    # optional second opinion, one module at a time
```

Run in the background and one heavy stage at a time. The script header lists all stages.
