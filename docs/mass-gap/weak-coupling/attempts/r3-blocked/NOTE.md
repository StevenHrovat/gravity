# Round 3, attempt 4 (r3-blocked): Leg C, the "click" test, prepared (2026-11-21)

Brief: prepare, pre-register and test (CPU only) a GPU measurement of the blocked SU(2) effective action at L√σ ∈ {2, 3, 4}, decided
against C's windows, B's S′ and (added by the coordinator during the work) r3-robust's D′; the coordinating session runs it after
Leg B. Nothing was run on the GPU. The GPU queue, `lattice/runs-gpu/` and the other attempts' folders were not touched.

Files here:
- `PREREG.md`: question, instrument, runs, criteria, decision rules, controls, limits.
- `blocked.py`: generator, flow, blocking, Schwinger–Dyson sums, `selftest`, `bench`, the run plan `PLAN`.
- `analyse_blocked.py`: fits, criteria, verdicts, controls, click table, GF table.
- `queue_blocked_gpu.ps1`: the GPU queue, not started.
- `cpu-test/`: the CPU self-test and pipeline-test logs and outputs.

`boundary.py` is imported unchanged.

## 1. Design decisions, in brief

1. **One lattice size, two β.** With 36⁴, b ∈ {6, 9, 12} gives L√σ = 2.10, 3.15, 4.20 at β = 2.3, and 1.55, 2.32, 3.10 at β = 2.4
   (coarse lattices 6⁴, 4⁴, 3⁴; box 12.6 and 9.3/√σ). The alternative was 48⁴ at β = 2.4 for 2.06, 3.10, 4.13. It needs one chain
   per run (memory) and about 2.5 times the time per configuration. The scaling check matters most near the crossing (3.1 to 3.2),
   which 36⁴ covers. 48⁴ at β = 2.4 remains an option (section 5).
2. **Block variable: gradient flow, then the straight product of the b flowed links.** The product is gauge covariant at coarse sites
   and is a group element (no projection). The flow is a physical-scale, gauge-covariant smoothing whose radius √(8t) scales with b.
   Primary f = √(8t)/b = 1/2, because per direction √(2t) = b/4 matches the transverse spread of a Balaban-type block average
   (b/√12), the variable C's analysis assumes. f = 1/4 and f = 0 are measured too, since C (§4, item 2) warned that the answer depends
   on the variable. The pipeline test already shows the effect the photon gate is built to catch: raw products (f = 0) halve the free
   photon's blocked coupling at b = 2 (perimeter suppression mimics strong coupling), while f = 1/2 keeps it at the bare value (1.10 ±
   0.23 against 1.1). So the photon test discriminates between block variables, not only between theories.
3. **Fit by Schwinger–Dyson equations, not by demon or pseudo-likelihood**, for SU(2) and U(1). The identities are linear in the
   couplings, need no normaliser, and hold link by link. Characters are Laplace eigenfunctions on S³, which makes every term closed
   form (`blocked.py` docstring). Z₂ has no Lie derivative, so it uses pseudo-likelihood on a 7×19 histogram (the sufficient
   statistic). The extension couplings (spin-3/2, 1×2 rectangle) and the closure residuals give the error bar on Y that C lacked.
4. **Verdict rule: robust under truncation.** A point counts as INSIDE or OUTSIDE only if the base fit and every extension fit agree,
   each with its own 2σ. I first added the extension shift in quadrature as an error bar. The pipeline test showed this is wrong for
   S′ and D′: adding rectangles adds factor types, so the value jumps by construction (S′ from 20 to about 100 at saturation). I fixed
   the rule before any GPU data and marked the change in PREREG.
5. **D′ added (coordinator, from r3-robust).** It is computed from an enumerated pair table: 18 plaquette pairs, each also sharing 2
   rectangles; 2 collinear pairs sharing 6 rectangles; 42 rectangle-only pairs. Distances are ⌈ℓ∞⌉ of the link midpoints. The weighted
   form is reported as λ* = sup{λ : D′_λ < 1}. The code reproduces r3-robust's calibration: Wilson window 0.0556; stand-in β_A <
   0.0834; 5.79 at β_A = 0.5. **One correction to the coordinator's framing: D′ is not the strictest criterion.** S′ is (S′ ⇒ D′,
   r3-robust §1). In the adjoint channel, Bakry–Emery is also stricter (β_A < 0.026 against 0.083). Pure-channel windows:

   | criterion | fundamental | adjoint |
   |---|---|---|
   | S′ | 0.0128 | 0.0192 |
   | D′ | 0.0556 | 0.0834 |
   | BE | 0.0833 | 0.0263 |
   | W1, linearised | 0.196 | 0.289 to 0.392 |

6. **Fused GPU quaternion product.** The flow is cupy array code. I counted its memory traffic exactly on the CPU with a counting
   array type: 55 kB per site per SU(2) flow step, 75 % of it in the product. A cupy `ElementwiseKernel` for the product cuts this to
   19 kB (316 launches instead of 1884), so the flow takes about 1.4 h less. The kernel cannot run on this CPU, so the array-code
   product stays the reference. `selftest --gpu` compares kernel against numpy, and the whole flow, blocking and SD chain GPU against
   CPU. The queue's first step is that selftest; on failure it retries with `BLOCKED_FUSED=0` (array code), and stops if that fails
   too.
7. **Hot starts for the confined controls.** U(1) at β = 0.9 is 10 % below its transition, and a cold 36⁴ start could stay
   metastably in the Coulomb phase.
8. **Gradient-flow coupling as the step-scaling quantity** (section 6). It comes free from the flow, and run 2 extends the flow to
   √(8t) = 9 so it reaches 3.15/√σ.

## 2. CPU test results (`cpu-test/`, one process, `CUDA_VISIBLE_DEVICES=-1`)

**Self-test** (`selftest.log`, 58 s, 13/13 pass):
- **Staples and rectangles.** Staples are identical to boundary.py's. Rectangle and plaquette staples are exact derivatives:
  one-link changes against an independent loop code agree to 8·10⁻¹⁵.
- **Gauge covariance.** Flow, blocking and SD sums are invariant to 10⁻¹⁵ (SU(2), U(1)).
- **Flow normalisation.** The SU(2) Euler step on a U(1)-subgroup field equals the U(1) heat-equation step to 4·10⁻¹⁶. This fixes the
  t normalisation behind √(8t) and the GF coupling.
- **Recovery of known actions.**

  | ensemble | true couplings | fitted |
  |---|---|---|
  | Wilson SU(2), boundary.py heat bath | β = 2.3 | 2.2999 ± 0.0091, adjoint −0.002 ± 0.007 |
  | Wilson U(1), boundary.py heat bath | β = 1.1 | 1.099 ± 0.005 |
  | Z₂, pseudo-likelihood | β = 0.3, 0.6 | 0.301, 0.599 |
  | mixed SU(2), our own Metropolis | (β_F, β_A) = (1.0, 0.8) | (1.0009 ± 0.006, 0.7929 ± 0.0047) |
  | mixed U(1), our own Metropolis | (0.6, 0.4) | (0.6005, 0.3993) |

  The mixed SU(2) case is the decisive check of the adjoint normalisation that the criteria use.

A first version of the self-test sampled every 2 sweeps. Its four-coupling U(1) fit came out 4 to 5σ off (β₁ = 1.128 ± 0.006). A
separate run, 600 configurations 4 sweeps apart, gave (1.0965 ± 0.004, 0.002, −0.001, 0.0006): consistent. So the earlier offset was
autocorrelation, not a bug. Z₂ with the rectangle is consistent too (0.63 ± 0.026 in the ordered phase, where plaquette and
rectangle are nearly collinear). The self-test now samples every 4 sweeps.

**Flow integrator.** Euler at ρ = 0.1 against RK3 (ε = 0.05), 8 configurations, 8⁴, β = 2.3: t²E is 3.2 ± 0.3 % high at t = 1 and
2.8 ± 0.4 % high at t = 2, linear in ρ. The blocking is defined with Euler ρ = 0.1, so this is part of its definition. For α_GF it is
a stated, near-constant +3 % systematic. The self-test reports it with a 10 % alarm (one 6⁴ configuration gives 5 %). An earlier 5 %
threshold had been arbitrary, and I changed it, saying so.

**Pipeline test** (`analysis.log`). All six run types at 6⁴, b ∈ {1, 2}, 2 chains × 24 measurements: 43 s, then the analysis.
Everything runs, and every verdict, gate and table is produced. The numbers are not physics: b = 2 is L√σ = 0.7. The controls behave
as designed:
- photon OUTSIDE at every f and b;
- deconfined Z₂ OUTSIDE (W1, D′);
- confined Z₂ INSIDE at b = 2 (β_P = 0.0065 ± 0.0017, W1 and D′ INSIDE): the method can click;
- confined U(1) at β = 0.9 not yet inside at b = 2 (β₁ 0.10 to 0.25), as expected at that size;
- every SU(2) point OUTSIDE (b_F ≈ 0.66 to 2.7);
- α_GF increasing.

The pipeline test also shows that the adjoint coupling of a smoothed blocked action can come out negative (SU(2) β = 2.3, b = 2,
f = 1/2: β_A = −0.13 ± 0.03). This is why the criteria use |β| and the exact oscillation, not a sign assumption.

## 3. Expected runtime

**About 3.7 h of GPU time, ±50 %** (before the review; now about 4.5 h with the addendum, section 8).

| step | minutes |
|---|---|
| U(1) photon control | 21 |
| SU(2) β = 2.3, including the GF extension | 96 |
| two Z₂ controls | 16 |
| confined U(1) control | 21 |
| SU(2) β = 2.4 | 61 |
| selftest and bench | 5 |

Peak GPU memory is about 4 GB. Basis: the fused heat bath at 0.45 µs per site and sweep (Leg B's own log: β = 2.6, 22⁴, 4 chains,
0.5 µs including measurement). The flow traffic was counted exactly and converted at an effective 300 GB/s: 0.115 s per SU(2) flow
step per 36⁴ configuration, 106 steps per configuration in run 2 and 49 in run 6. The coarse measurements are launch-bound but
small, under 1 s per configuration. The queue's `bench` step logs the measured projection before the long runs; if it is far off, the
coordinator can cut as listed in PREREG. Disk: about 1 MB per run (per-configuration SD matrices, not configurations).

## 4. What the coordinator must decide

1. **Start the queue after Leg B** (`pwsh -File queue_blocked_gpu.ps1` in this folder). It waits by itself for "BOUNDARY DONE" in
   Leg B's queue log and for no `boundary.py run` process. Outputs go to `runs-gpu/` here. There is no `.gitignore` entry for it;
   the files are small.
2. **Budget, about 3.7 h.** Cuts in PREREG: the GF extension (−35 min), the β = 2.4 scaling run (−61 min).
3. **Optional, not in the plan:** β = 2.4 on 48⁴ with b = 8, 12, 16 (L√σ 2.06, 3.10, 4.13), one chain per run, about 2.5 h more,
   for a second β at L√σ ≈ 4.
4. **r3-monotone's request (section 6): not included.** It needs new GPU kernel code and about 11 h at the requested grid.
5. **Before reading the SU(2) results, expect** (from C's stand-in, PREREG): W1 crossing at 3.3 to 3.9, D′, S′ and BE failing
   at every L ≤ 4.2. Neither the stand-in nor this expectation is a criterion.

## 5. Unit tests of the design (RULES round 2 and 3)

- **Photon.** A gate run first. If the primary block variable puts Coulomb U(1) inside any window at any b, the queue stops before
  SU(2). The pipeline test shows the gate has teeth: it discriminates between block variables (f = 0 against f = 1/2).
- **Z₂.** W1 and D′ are confinement-type, so deconfined Z₂ must stay OUTSIDE. S′ is gap-only: it may hold for Z₂ and is not read
  as an area law. Confined Z₂ is the positive control.
- **Triviality test** (existence-type claims): not applicable. Nothing here claims a continuum limit exists; the measurement is at
  fixed β, and every verdict is about a fitted lattice action.

## 6. The step-scaling coupling and r3-monotone's request

**On the same configurations, free:** the gradient-flow coupling α_GF(√(8t)) (Luescher 2010), on the grid t = 0.5, 1.0, ...:
- to √(8t)√σ = 3.15 at β = 2.3 and 1.55 at β = 2.4;
- monotonicity reading pre-registered: no successive drop beyond 2σ, plus a strict-increase reading.

This is an infinite-volume running coupling, neither RP-controlled nor a twist scheme. A monotone α_GF supports "the running
coupling reaches order one" in one scheme. It does not supply r3-monotone's NFP margin δ.

**r3-monotone's request** (`../r3-monotone/NOTE.md` §7) is the twist free energy by Kovacs–Tomboulis interpolation: a sheet of
plaquettes with coupling β′ ∈ [−β, β] at 20 nodes, ≥ 2000 measurements × 5 sweeps, 5 β × ℓ ∈ {4, ..., 16}. **Not feasible inside
this job.**
- **Code.** The fused kernel (copied unchanged from GUID v7) has one coupling per chain, not per plaquette, so the request needs a
  new kernel or a slow array-code heat bath.
- **Cost.** With a modified fused kernel the requested grid costs about 11 h, dominated by ℓ = 16 (about 1.6 h per β) and
  ℓ = 12 (about 0.5 h per β). A reduced grid (β ∈ {2.3, 2.5}, ℓ ∈ {4, 6, 8, 12}, 12 nodes, 500 × 3 sweeps) would be well under 1 h,
  but its statistics are r3-monotone's call.

My recommendation: a separate pre-registered job with its own kernel and tests, after this one.

## 7. Honest status

- **Proved:** nothing new. This is an instrument.
- **Tested:** every formula against independent code or known actions; the CPU pipeline end to end.
- **Untested here:** the GPU code path. The queue gates on its own selftest first, with an array-code fallback.
- **Single most promising next step:** run the queue. The first number that matters is the photon gate for f = 1/2. The second is
  β_A(L√σ = 3.15) against C's stand-in value of 0.50.

## 8. Amendments after the round-3 review (2026-11-21, 23:00–23:20, before any GPU data)

The full record, change by change, is in PREREG.md, last section ("Changes before data"). In short:
- **Noisy variants of the block variable** (r3-wp's Wilson-type kernel, β_n = 16 and 64) are measured as reported variants. The
  verdict text says what a deterministic block variable does and does not imply.
- **Verdicts renamed** NOT_EXCLUDED (on the truncated fit) / EXCLUDED, with the false-positive bias of truncation stated.
- **Pair and factor tables per coarse torus.** The verdicts use the infinite-volume tables; on 3⁴ and 4⁴ wrap-around merges pairs.
  This was checked in a new 3⁴ self-test.
- **A coarse-volume run** (addendum).
- **A Creutz-ratio signal check.** A point counts only if it passes; "fundamental channel resolved" is reported separately.
- **A quantitative photon gate** (flat q1 coupling in b, Coulomb level), plus a second Coulomb β (addendum).
- **Non-abelian negative controls.**
  - Deconfined SU(2) at matched L cannot be done on coarse tori: it would need L√σ < 0.48.
  - 2I in the frozen phase needs new update code and about 40 min of GPU; it is specified but not queued.
- **A deconfinement-edge flag** below L√σ = 1.45.

**Mechanics.** The running main queue script is unchanged. It calls the amended Python files fresh, with identical command lines,
so it picks everything up without a restart. New runs are in `queue_blocked_gpu_addendum.ps1`. Self-test now 16/16 (59 s); the
pipeline test was rerun on all eight run types (88 s).

**Runtime:** about 4.5 h in total (main queue 4.0 h, addendum 35 min), ±50 %.

## References (ideas only; nothing copied)

- Luescher, JHEP 08 (2010) 071 (gradient flow; SU(N) t²E normalisation; RK3 integrator), recalled.
- Morningstar and Peardon, PRD 69 (2004) 054501 (stout smearing), recalled.
- Falcioni, Martinelli, Paciello, Parisi, Taglienti, Nucl. Phys. B265 (1986) 187; Gonzalez-Arroyo and Okawa, PRD 35 (1987) 672;
  Takaishi, PRD 54 (1996) 1050 (Schwinger–Dyson inverse Monte Carlo, blocked effective actions). Recalled, not re-read: citations
  for the method's idea, to be checked before any write-up. Hasenbusch, Pinn and Wieczerkowski (demon methods): the alternative not
  used, recalled.
- Besag (1975), pseudo-likelihood, recalled.
- C, B, r3-robust, r3-monotone: the notes cited at point of use.
