# Thread A: an independent-kernel replay of the 2026 existence proof

Status 2026-11-21: **searched, not yet run.** Nobody has published one; the plan below waits for the owner's go-ahead (HANDOVER §3 A).
Claim level once it runs: "kernel X accepted export or `.olean` set Y of commit Z", nothing more.

## 1. Has anyone done it? (searched 2026-11-21)

Searched all issues and pull requests of the three trackers named in HANDOVER, downloaded in full and searched locally for
`lean4lean`, `nanoda`, `external kernel`, `independent kernel`, `second kernel`, `lean4export`, `lean4checker`, `leanchecker`,
`comparator`, `replay`.

| Where | What it holds | Second kernel? |
|---|---|---|
| `yang-mills-group/YM` (main at `b379615`, 15 Nov) | issues are disabled and there are no pull requests. `verification/tool-pins.json` pins Comparator `d03acab` (Lean 4.34.0) and lean4export `4e79152` (Lean 4.32.0) with `"external_kernel": false`; `docs/rerun.md` says the runner uses the macOS development launcher "with no external kernel" and asks for an isolated Linux run or an additional-kernel check to be recorded "as a different verification mode" | no |
| `hairer/humanise-yang-mills`, issue #37 (closed 12 Nov) | clean from-source rebuild on an independent Linux x86-64 host (3 h 17 min on 36 threads, 18,126 jobs, `REPLAY_PASS project=100168 external=14364 endpoints=17`), the 1,044 differing `.olean` files explained (absolute paths in linter messages, PR #75), and a sandboxed (`landrun`) Comparator run with Comparator **v4.32.0** and `"enable_nanoda": false` (PR #78). Its last word: everything done "except a second kernel (nanoda or lean4checker)"; the build tree was to be deleted a few days later | **explicitly not done** |
| same repository, PRs #436, #446, #447 and the review PRs of 13 to 17 Nov | each lists "independent kernel replay" or "kernel replay (`leanchecker`)" under checks not run | no |
| same repository, issue #382 (closed 17 Nov) | the assessment's consequences; leaves open "whether the Comparator revision the group used makes our `enable_nanoda` qualification moot" | no |
| `scottnarmstrong/yang-mills-informalization` | one issue and one pull request, neither about kernels | no |
| tool trackers: `digama0/lean4lean`, `ammkrn/nanoda_lib`, `leanprover/comparator`, `leanprover/lean4export` | no issue mentions the Yang–Mills project | no |

**Answer: not done by anyone, as far as the public trackers show.** (The search covers GitHub only, not the Lean Zulip.)

## 2. Facts re-checked for the plan

- The submission is pinned to `leanprover/lean4:v4.32.0`, Mathlib `81a5d25` (`submission/lean-toolchain`, `lake-manifest.json`).
- Lean 4.34.0 fixed #14806 (`is_def_eq` caching) and #14807 (`is_prop`), and the runtime bug #14838 (reference-count overflow, usable
  "on machines with at least 18GB of free RAM"). The two #14806 exploits "are caught by nanoda"; the #14807 proof "was also accepted by
  nanoda; lean4lean is believed not to have the bug" (Lean 4.34.0 release notes).
- So the committee's Comparator runs (4.34.0 kernel on an export of the 4.32.0 project) already used the **patched** kernel, but no
  **different** one; humanise's isolated run used Comparator v4.32.0, the **unpatched** kernel.
- `lean4lean` reads `.olean` files, so it must be compiled on exactly Lean 4.32.0 (the file format carries the version). Its history has
  v4.32.2 (`779c51f`, 4 Aug) but no v4.32.0; main is on v4.33.0-rc2. Its own README: it "likely shares some implementation bugs" with
  the C++ kernel ("it's not really an independent implementation"). Open issues: #17 (cannot replay `Init.Prelude` on v4.26/v4.29),
  #66 (rejects valid `Quot.lift` proofs in `--import` mode).
- `nanoda` (Rust, fed by lean4export) is the more independent kernel, and Comparator can call it (`enable_nanoda`). Open issue #85:
  memory past 100 GiB on a 3.25 GB export; closed #44: a Mathlib export exhausted memory.
- Gravity's finding F3 applies: two kernels fed by one exporter are not independent. lean4lean (reads `.olean`) and nanoda (reads a
  lean4export file) have different front ends, which is the better pair.

## 3. Plan on the owner's laptop (WSL Ubuntu 24.04)

| Stage | What | Tools, pinned | Time (estimate) | Result recorded |
|---|---|---|---|---|
| 1 | Clone YM at `b379615`; `verify.py integrity`; `verify.py all` (fresh build, review modules, controls, Comparator on the three endpoints) | Lean 4.32.0 for the project, Comparator `d03acab` (4.34.0), lean4export `4e79152` | 4 to 8 h on 12 threads | the runner's `result.json`, logs, hardware |
| 2 | lean4lean over every module of the build (multithreaded mode), then `--fresh` on the endpoint modules | lean4lean `779c51f` re-pinned from v4.32.2 to v4.32.0 (the patch is recorded) | unknown; plan on a night | accepted or rejected per module, declaration counts |
| 3 | Comparator with `"enable_nanoda": true`, real `landrun` isolation, on the three endpoints | nanoda at the revision Comparator `d03acab` pins | unknown; may exceed memory | pass, fail, or "out of memory at N GB", which is also a result |

Resources: about 100 GB of disk (humanise's build plus Comparator copy was about that; the laptop has over 300 GB free); memory is the
limit (WSL currently sees 19 GB of the laptop's 32 GB). Publishing: YM has no issue tracker, so the record would go to
`hairer/humanise-yang-mills` under its claim protocol (a CLAIM comment, then a draft pull request), with the owner's approval first.
