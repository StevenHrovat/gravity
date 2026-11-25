# SPEEDFIX: removing the per-sweep overhead of the act-number GPU code (round 4, r4-actnumber, 2026-11-22)

Engineering only. The physics, the plan (`actnumber.PLAN`), the schedule and the observables are unchanged. This file has three parts:
the pre-registration of the statistical equivalence check (written before the runs of check B), then the findings and changes, then
the results (filled in after the runs).

## Check B, pre-registered before any old-versus-new run (2026-11-22)

**What is compared.** The earlier code (`actnumber_old.py`, a verbatim copy of `actnumber.py` as benched) against the new `actnumber.py`,
same `run` command, different seeds (the random stream of the heat bath changed, see below), on four small lattices, 8 chains each, all
on the GPU, fused path, twist in the xy plane:

| name | group | beta | L | T | therm | meas x every | levels |
|---|---|---|---|---|---|---|---|
| su2 | SU(2) | 2.4 | 4 | 8 | 300 | 300 x 6 | 0, 2 |
| u1 | U(1) | 1.1 | 4 | 8 | 300 | 400 x 2 | 0, 2 |
| z2 | Z2 | 0.42 | 2 | 8 | 300 | 500 x 2 | 0 |
| 2i | 2I | 2.4 | 4 | 8 | 100 | 300 x 3 | 0, 2 |

(seeds: old 9001, 9011, 9021, 9031; new 9002, 9012, 9022, 9032.)

**Observables (per group, from the stored output of `run`).** Mean plaquette; signed sheet plaquette; bulk plaquette of the twisted
plane; and for the lowest and the highest smearing level: <|p|^2> (mean over t of Re p(t) p*(t)) and the nearest-neighbour correlator
<p(t) p(t+1)> (cyclic in t). That is 7 observables for SU(2), U(1), 2I (levels 0 and 2) and 5 for Z2 (one level).

**Error and statistic.** Each chain's measurement series is cut into 10 consecutive blocks; the block means of all 8 chains (80
numbers) give the mean and its error (standard deviation over the blocks divided by the square root of 80). z = (old - new) /
sqrt(err_old^2 + err_new^2). The blocks are much longer than the autocorrelation time (180 sweeps for SU(2), 20 measurements for the
others, to be reported).

**Pass rule (fixed now).** A group passes if every |z| <= 2. If exactly one |z| lies in (2, 3] and none above 3, the group is rerun once
with both seeds shifted by 100 (declared now, because with 5 to 7 correlated observables one value beyond 2 sigma is expected in about a
quarter of the cases even for identical codes); it passes if the rerun has every |z| <= 2. Two or more values beyond 2, or one beyond 3
(in either run), is a **failure**: the speed fix is not accepted until the cause is found. Checks that need no statistics are in
check A (`speedfix_check.py`): flux operators and plaquettes against the array code, the new sheet kernel against the earlier
fix-up, the U(1) overrelaxation kernel against the array code, the von Mises kernel sampler (KS).

## Where the time went (profile of the earlier code, idle GPU)

`profile_speedfix.py` (cProfile around a few sweeps; the code of that moment is kept as `actnumber_old.py`). The GPU was never the
limit: every group was bound by Python and kernel-launch overhead, with thousands of tiny array operations per sweep.

| case (8 chains) | earlier ms per sweep | where it went |
|---|---|---|
| SU(2) fused, L = 6, T = 64 | 213 | **98 % in `SheetFix`**: 16 re-updates per sweep, each about 14 ms (about 100 small array operations: 6000 `fetch` calls per 20 sweeps, each a gather plus a quaternion conversion, 4400 `qmul` calls that each stack four arrays, a rejection loop with a host synchronisation for the heat-bath draw). The fused kernels themselves were about 2 ms. |
| U(1), L = 4, T = 32 | 160 | 55 % the von Mises rejection loop (about 10 rounds per call, each ending in a host synchronisation to shrink the column list); 33 % the twisted staple (16 `roll` copies per pass, 160 passes per sweep). |
| Z2, L = 4, T = 32 | 66 | the same staple (`roll` copies), 160 passes per sweep. |
| 2I, L = 4, T = 32 | 476 | 70 % `qmul` (stack of four strided slices, 3360 calls per 5 sweeps) in the staple, plus per-pass boolean-mask indexing and `mean` for the acceptance. |

So the "floor" was not one thing but the cost of about 100 to 160 array operations per checkerboard pass in every group, with no
dependence on the lattice size until the lattice is large. It did not come from the chains (they are already batched in the first
array axis, B = 8) nor from host copies of the links. The measurement showed the same pattern: the flux operators were about 40 array
operations per smearing step on `(..., 4)` arrays (2 ms per step at L = 4, 39 ms per step at L = 16).

**The earlier bench number depended on the load of the machine.** The bench of the queue run (19.68 h, 0.45 to 0.55 s per sweep) was
taken while the machine was busy; the same bench run again on the idle machine before any change gave 9.36 h (0.2 to 0.33 s per sweep,
`runs-gpu/speedfix/bench_old.log`). Python-bound code is slow on a loaded host; the GPU code that replaces it is not.

## What was changed (all in `actnumber.py`; the queue script is unchanged)

1. **SU(2) sheet fix-up as one CUDA kernel** (`SHEET_SRC`, class `FusedSU2`). Same algorithm as before: the links whose staple contains a
   twisted plaquette are re-updated with the correct staple (heat bath: fresh draw from the conditional law; overrelaxation: reflection
   of the old value). The kernel is a copy of the main kernel's update with the twisted staple (each of the six terms times the sign of
   the plaquette it completes). Because a pass never reads the links it writes, the new sheet values are computed before the untwisted
   pass into a buffer (`sheet_new`) and written back after it (`sheet_put`): two launches per pass of a twist-plane direction instead of
   about 100 array operations. The main kernels (`../../../lattice/gpu/gauge.py`, `su3_cuda.py`) are used unchanged, with prebuilt
   launch arguments; the sheet kernel is compiled from the same source plus the new functions. The old class `SheetFix` stays for the
   CPU emulation used by the self-test.
2. **Flux measurement kernels** (`ape_q`, `poly_q`; `flux_ops` and `polyakov_mean` use them for SU(2) and 2I on the GPU): the formulas
   and the operation order of the array code, no FMA contraction, one thread per site. The plaquette field of the quaternion groups on
   the GPU is a kernel too (`plaq_q`).
3. **2I Metropolis as a kernel** (`GPUMetro2I`): same staple, same proposals (12 elements next to 1, 4 hits per link and pass), same
   acceptance rule; acceptance counted on the device (`acc` as before); the snap to the group after the sweep unchanged.
4. **U(1) and Z2 as a kernel** (`GPUAbelian`): same twisted staple, the same Best and Fisher von Mises sampler, the same overrelaxation
   and Z2 heat bath.
5. `bench` now also times the plaquette, the sheet check and the host copies that every measurement of `run` does (the earlier bench
   timed the flux operators only); both projections are printed, the line the queue copies ("PROJECTED TOTAL") is the full one.
6. The GPU self-test calls the new `FusedSU2.pass_` (36/36 pass, was 36/36).

Not changed: the action, the twist, the update algorithm and its acceptance rule, the sweep and measurement schedule (`PLAN`), the
observables, the analysis, the seeds' role (the seed fixes the run, still deterministic). The array code (numpy and cupy) stays in the
file as the reference and as the CPU path.

**What does change: the random stream.** The sheet links of the SU(2) heat bath, and all of U(1), Z2, 2I, now draw from per-site
xorshift states (the generator of the fused SU(2) kernels) instead of the cupy generator, so a run with a given seed is not the same
sequence as before. The law of every update is the same, so the check below is statistical for these parts and exact where there is no
randomness. The SU(2) bulk update (the fused kernels with their own states) is untouched.

## Check A: deterministic equivalence (`speedfix_check.py`, `runs-gpu/speedfix/check_A.log`, 10/10)

- Flux operators (APE levels 0, 3, 8) and all six plaquette fields, GPU kernels against the numpy array code, on random configurations,
  planes (xy), (yz), (xz), boxes (6,6,6), (4,6,8), (6,4,6): maximum difference 2.8e-16 (fluxes), 0 (plaquettes).
- SU(2) overrelaxation (deterministic), new sheet kernel against the earlier array-code fix-up, 3 sweeps of all passes, restarted from a
  common state at every pass (overrelaxation amplifies rounding): maximum difference 2.0e-15, three geometries including the box (8,4,6)
  and the twist in the yz plane. (The existing GPU self-test also checks fused + sheet kernel against the array path, 6.8e-14.)
- U(1) overrelaxation, kernel against the array code, 3 sweeps: exactly equal (0) in two boxes and planes.
- U(1) heat bath: the von Mises sampler of the kernel against the exact density exp(kappa cos theta), kappa = 2.4, 20 000 draws: KS p = 0.73.

## Check B: statistical equivalence (pre-registered above; `speedfix_equiv.py`, `runs-gpu/speedfix/equiv1.log`)

Result of the one pre-registered run (no repeat was needed). All 26 comparisons have |z| <= 1.51; the four groups pass.

| group | observables | max abs z | verdict |
|---|---|---|---|
| SU(2) beta 2.4, L 4, T 8 | 7 | 1.48 (sheet plaquette) | PASS |
| U(1) beta 1.1, L 4, T 8 | 7 | 1.51 (level-2 nearest-neighbour correlator) | PASS |
| Z2 beta 0.42, L 2, T 8 | 5 | 1.00 (plaquette) | PASS |
| 2I beta 2.4, L 4, T 8 | 7 | 0.80 (sheet plaquette) | PASS |

Examples (old / new): SU(2) plaquette 0.63082(18) / 0.63072(21); <|p|^2> level 0 0.1040(9) / 0.1037(9); U(1) plaquette 0.71251(24) /
0.71239(28); Z2 <|p|^2> 0.572(3) / 0.575(3); 2I plaquette 0.63091(21) / 0.63085(25) (2I below its freezing mimics SU(2)). The full
table is in `equiv1.log`. The old runs took 6 to 11 minutes each (four in parallel, so a little over the 10 minute guideline for the
slowest two); the new runs took 13 seconds each.

## Other tests

- `python actnumber.py selftest` (CPU): **28/28** (`runs-gpu/speedfix/selftest_cpu_newcode.log`). `selftest --gpu`: **36/36**, about 3.5
  minutes (`runs-gpu/speedfix/selftest_gpu_new.log`).
- `pipeline_test.py` (CPU, numpy, 706 s): runs through; the CPU code path was not touched and the stored data of every run (operators,
  plaquettes, sheet checks, all 17 files) are **bit-identical** to those in `cpu-test/` (the folder was restored afterwards). The new
  pipeline log differs from the stored one only in the toy photon gate, which now reads PASSED, as PREREG.md records for the U(1) flip
  rule decided after that log was written (the analysis was not touched here). Copy: `runs-gpu/speedfix/pipeline_test_newcode.log`.

## Re-bench (the queue's own `bench`, fused path, idle GPU; `runs-gpu/speedfix/bench_new.log`, `bench_old.log`)

| per sweep, 8 chains | earlier (queue bench) | earlier (idle rerun) | now |
|---|---|---|---|
| U(1) L 4, T 32 | 534 ms | 200 ms | 2.2 ms |
| SU(2) L 4, T 96 (beta 2.4) | 460 ms | 206 ms | 10 ms |
| SU(2) L 14, T 32 | 547 ms | 280 ms | 130 ms (184 ns per site) |
| SU(2) L 16, T 32 | 515 ms | 334 ms | 193 ms (182 ns per site) |
| Z2 L 4, T 32 | 154 ms | 94 ms | 1.2 ms |
| 2I L 4, T 32 | 1020 ms | 542 ms | 4.7 ms |

SU(2) now runs at about 185 to 210 ns per site and sweep at every size (the pre-registered model assumed 450 ns plus a 25 ms floor),
so large lattices are 2 to 2.5 times faster than the model and small ones far below its floor. A measurement costs 2 to 60 ms (flux
operators, plaquette, sheet check, host copies; it was 40 to 940 ms for the flux operators alone).

**Projected total for the unchanged plan: 1.47 h** (1.44 h with the earlier bench definition, flux operators only), against 19.68 h
at the queue bench, 9.36 h for the same code on an idle machine, and the pre-registered 5.2 h (+- 50 %). With the four-move addendum
(`--addendum`): 2.25 h in all, i.e. about 0.8 h for the addendum against the pre-registered 2.4 h.

## For the coordinator

- The plan itself (`actnumber.PLAN`, `PLAN_W`) and `queue_actnumber_gpu.ps1` are unchanged; `PREREG.md` untouched. The queue's
  `selftest --gpu` and `bench` steps work as before (`bench` prints one more line, worded so that the queue's "PROJECTED TOTAL" search
  still finds exactly one line).
- The run is now about 3.5 times shorter than pre-registered. Whether the points that were cut for time in the post-review amendment
  (beta 2.6 L 4, beta 2.7 L 6, the periodic-box comparison, 2I below freezing, the second Coulomb beta) should come back is a decision for
  PREREG.md, not made here.
- A run with a given seed is reproducible, but it is a different sequence from the one the earlier code would have produced (stream
  change above); nothing counted exists, so no data is affected.
- The bench is not a measurement of the whole run: it times 10 sweeps per lattice. The real per-run overhead (checkpoints every 50
  measurements, process start, the one-time kernel compile of a fraction of a second) is small against minutes per run, but the first
  real run should be watched for its time against the bench line.
