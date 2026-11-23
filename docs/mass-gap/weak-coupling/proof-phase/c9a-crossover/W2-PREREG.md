# Pre-registration (design only, NOT run): the quenched constrained Dobrushin coefficient across the last doublings of the crossover (c9a-crossover, W2, 2026-11-23)

**Status: written, not run.** No code was written and no GPU was touched in this workstream. Running it needs (1) the owner's
explicit OK, (2) the new code listed in section 6, (3) a CPU pipeline test, and (4) one timed GPU job and the projection of
section 8 shown to the owner before the full run. Rules of `weak-coupling/attempts/RULES.md` apply (photon and finite-group
unit tests, claim discipline, CPU-only pilot).

Theory: `WL.md` (the two forms `WL-Q` and `WL-S` of the weakest link; section 5 there for the two numbers measured here);
`W1-CHAIN.md` (stage two is the Lean consumer); `NOTE.md` 5 (W2 as first proposed).

## 1. Question

At the non-perturbative end of the crossover (Wilson `β` from 3.5 down to 2.3, about 4 to 6 doublings), for one doubling step
of a soft good blocking:

* **(Q1, the good-box number `c(t)`):** is the conditional box law of the fine field, given the block field and the outside,
  Dobrushin-Shlosman contracting on good boxes, worst case over good boundaries (`WL-S` clause (G))?
* **(Q2, the rarity number):** are bad cells (threshold `t`) subcritical after merging (`WL-S` clause (R))?
* **(Q3, the quenched form):** does any adversarial block field (flat, random, twisted, large-field, bulk-transition proxy)
  give a conclusive box influence `≥ 1` (`WL-Q` refuted for that blocking)?

Q3 alone was `NOTE.md`'s W2. Under M1's move (`WL.md` 3, 4) a Q3 failure only maps the bad set; the route is decided by Q1
and Q2 together.

## 2. Objects

* **Fine theory:** SU(2) Wilson action at `β ∈ {2.3, 2.6, 3.0, 3.5}`, periodic `16⁴` lattices for the equilibrium outsides
  (existing heat-bath generator, `lattice/boundary.py`, `c3b-refit/goodblock.py`).
* **Blocking (one doubling, factor 2):** the good blocking of `c3b-refit/goodblock.py` (`smearBlock w`, `w = 0.5`) one level,
  **unprojected**: `Φ̃_l(U)` = straight 2-link path plus `w` times the 2-link staples, as a quaternion sum (no projection).
  Each fine link enters each `Φ̃_l` at most once, so `Re tr(Y† Φ̃_l(U))` is linear in every single link.
* **Soft constraint (noisy blocking):** `P(Y | U) = Π_l exp(κ ½ Re tr(Y_l† Φ̃_l(U))) / z(κ |Φ̃_l(U)|)`, with `z` the SU(2)
  normaliser (a Bessel ratio). `κ ∈ {4, 16}`. The joint law has the Wilson measure as its `U`-marginal exactly (law
  preserving, the M1 requirement).
* **Proxy caveat (fixed now).** M1's crossover state is `(SO(3), closed Z2)` with Balaban's average; this test uses SU(2)
  links and the c3b good blocking. It answers the question for that blocking. Transfer to M1's blocking is qualitative; to
  see whether the centre layer drives a failure, every influence is measured on fundamental **and** adjoint (centre-blind)
  observables.
* **Box:** the links based at the sites of a cube of side `ℓ` fine sites, `ℓ ∈ {4, 6}` (two and three blocks), with the
  block variables `Y` of every block meeting the box fixed. Its conditional law given the outside fine links `σ` and `Y` has
  density `∝ exp(β S_W(U_B, σ)) Π_{l meets B} exp(κ ½ Re tr(Y_l† Φ̃_l)) / z(κ |Φ̃_l|)`.
* **Good and bad cells:** a block (fine `2⁴` cube) is **bad at threshold `t`** if one of its fine plaquettes or one of the
  block plaquettes built from `Y` has `1 − ½ tr U_p > t`. `t ∈ {0.5, 1.0, 1.5}` (the maximum is 2). A box is good if every
  block within one block of it is good.

## 3. Measured quantities

* **Box influence, upper side (coupled chains).** Two chains of the box law with boundary `σ` and `σ^z` (one outside link
  `z` rotated by a fixed SU(2) element of angle `θ ∈ {π/2, π}`), coupled link by link: heat-bath proposal with the linear
  staple `β A_W + κ A_Y`, **maximal coupling of the two proposals** (c8b `decisive.py coupled`), then a Metropolis correction
  for the normaliser ratio `z(old)/z(new)` with a **shared acceptance uniform**. Running gauge alignment as in c8b. Output:
  `k̂_up(z)` = stationary expected number of disagreeing box links (weighted by the geodesic distance, W₁ form). This is an
  upper estimate of the influence only if the coupled pair has reached its stationary disagreement (two starts agree);
  it can be vacuous even when the true influence is small (c8b: the Markov coupling contracts only up to `β ≈ 0.25`
  unconstrained).
* **Box influence, lower side (observables).** `k̂_low(z)` = largest shift, over a fixed family of gauge-invariant box
  observables (all plaquettes, the `1×1` and `2×2` loops of the box, fundamental and adjoint), of `E_σ[F] − E_{σ^z}[F]`
  divided by the observable's oscillation bound. A lower bound of the TV influence; conclusive for a fail.
* **Column sums.** The condition of `WL.md` 2.2 (G) is a per-site column condition over a covering family of boxes.
  * For the **sampled** (statistically homogeneous) instances, the expected column sum at a site equals the one-box sum of
    the translation-averaged influences (Lean `gdsw_of_oneBox` in the translation-invariant case), so we measure
    `R_up(t) = (Σ_z k̂_up(z)) / |B|` and `R_low(t) = (Σ_z k̂_low(z)) / |B|` over outside links `z` within one plaquette of the box
    (`λ = 0`; `|B| = 4ℓ⁴` links), estimated from 32 randomly sampled shell links per instance and scaled to the shell size
    (unbiased; its sampling error is part of the jackknife).
  * For the **adversarial** (inhomogeneous) instances the one-box sum does not imply the column condition, so we measure the
    column directly: fix a site `z` next to the adversarial feature and sum `k̂(z)` over the box translates `t` whose shell
    contains `z` (all such translates for `ℓ = 4`; 32 sampled for `ℓ = 6`), divided by the coverage `|Λ₀|`: `C_up(z)`,
    `C_low(z)`.
* **Upper side without a Markov coupling (diagnostic).** Whole-box TV upper estimate by Pinsker,
  `TV(q_σ, q_{σ^z}) ≤ (½ KL)^{1/2}`, with `KL = E_σ[log q_σ/q_{σ^z}]` from the explicit density ratio and the ratio of
  normalisers by thermodynamic integration along `σ_s` interpolating `σ` to `σ^z`. It bounds `k(z) ≤ |B| · TV`, which is
  conservative; it is a statistical estimate, not a bound. It is reported next to `k̂_up` and enters no verdict.
* **Conditional mass of good regions** `m`: the disagreement profile of the coupled pair as a function of the distance from
  `z` into the box, fitted to `e^{−m d}` on sampled good instances (it sets the collar width of `WL.md` 10.2).
* **Influence-bad blocks** (`WL.md` 10.4): a block is influence-bad if the local column sum `R_low` of the `ℓ = 4` box centred
  on it exceeds `½`. Measured on the 16 sampled instances per `β` (not on the whole `16⁴` lattice: it costs one box
  measurement per block); reported as a density with jackknife errors and compared with the field-size classification.
* **Block-variable influence** `k̂_Y`: the same with one block variable `Y_l` rotated instead of an outside link (8 sampled
  per instance). It measures the quasi-locality of the projection (stage two (a), (b)), not clause (G).
* **Rarity.** On the equilibrium `16⁴` configurations with `Y` sampled from `P(Y | U)`: the fraction `η(t)` of bad blocks,
  and the **cluster-size distribution and connectivity function** of bad blocks merged at range 1 and range 3 blocks
  (probability that the origin's merged cluster reaches distance `r`, `r = 1..4` blocks).
* **Content check (photon):** blocked-plaquette two-point function of `Y` at block distances 1..6, compared with the massless
  form.

## 4. Instances

| run | theory | coupling | block fields `Y` | outsides `σ` | role |
|---|---|---|---|---|---|
| 0 | all | | | | selftests (section 6) and the timing job (section 8) |
| 1 | SU(2) | `β ∈ {2.3, 2.6, 3.0, 3.5}` | **sampled**: 16 draws from `P(Y | U₀)`, `U₀` equilibrium (then `U₀` restricted to the box is an exact draw of the conditional law: chain 1 starts at equilibrium) | the matching `U₀` outside | Q1, Q2 (annealed and good-class) |
| 2 | SU(2) | same | **adversarial**: A1 flat `Y = 1`; A2 Haar-random `Y`; A3 twisted (a stack of block plaquettes `= −1` through the box, centre twist); A4 one block plaquette at angle `π` on the box boundary; A5 `Y` from pure SO(3) (adjoint) Wilson configurations at `β_A ∈ {2.0, 2.5, 3.0}` (the bulk-transition region, recalled near `β_A ≈ 2.5`; the three points bracket it); A6 sampled `Y` with a **twisted outside**: `σ` carries a thin centre-vortex sheet that ends on the box boundary (the `UV-TV.md` 3 example, which makes the quenched form fail at weak coupling) | equilibrium `σ` matched by the heat bath of the joint law, and the **worst of a pool of 8** (greedy: the pool member with the largest pilot `k̂_low`); for A6 the twisted `σ` itself | Q3, and the bad-set map |
| 3 | U(1) | `β = 1.1` (Coulomb phase) | sampled (8) and A1, A2; U(1) version of the blocking | as run 1, 2 | **photon control** |
| 4 | 2I | `β = 6` (frozen, ordered) | sampled (8) and A3 | as run 1, 2 | **finite-group control** |

Common to all: `κ ∈ {4, 16}`, `ℓ ∈ {4, 6}`, `θ ∈ {π/2, π}`; two independent starts per coupled pair; jackknife over `Y`
draws.

## 5. Gates and verdicts (fixed now)

**Gates.**
* **G0 (gauge):** rotating the boundary data by a random gauge transformation at the boundary sites, **with the block
  variables `Y` co-rotated at those boundary sites that are coarse sites** (`Φ̃` is covariant under fine gauge
  transformations: rotations at intermediate sites of a path cancel along it), changes no gauge-invariant box observable
  beyond 2σ. Else stop: the instrument is wrong.
* **G1 (coupling sanity):** identical boundaries give zero disagreement at all times.
* **G2 (photon, run 3):** (a) content: fit the `Y` plaquette two-point function at block distances 3..6 with a power law
  `A r^{−4}` and with `A e^{−m_Y r}`; the gate fails if the exponential fit has `χ²` smaller by more than 4 **and**
  `m_Y > 0.3` per block at 2σ (the blocking lost long-wavelength content, noise-limit trap); (b) at `κ = 16`, `R_low < 1` (photon expected to pass `WL-S`, `WL.md` 7). If (a) fails, every SU(2) pass is
  **void** (fake uniqueness possible). If (b) fails, the instrument or the constraint is too weak to see conditional
  decorrelation where it must exist: SU(2) verdicts become INCONCLUSIVE.
* **G3 (stationarity):** the two starts of each coupled pair agree on `k̂_up` within 2σ after the pre-registered length
  `T` (set by the pilot, section 8). Pairs that fail G3 report `k̂_up` as "not stationary" and enter no upper-side verdict.

**Definitions.** A merged bad cluster **spans** if it wraps the torus (contains a non-contractible loop) or its extent in
some direction is at least half the block lattice (4 blocks on the `8⁴` block lattice of a `16⁴` fine lattice). A **good
adversarial instance** is an adversarial instance whose box is good at the threshold `t` considered.

**Reach of the pass side (stated before running).** SUPPORTED needs `R_up < 1`, i.e. a Markov coupling that contracts. For
the unconstrained theory that coupling saturates above `β ≈ 0.25` (c8b). Whether the soft constraint makes it contract at
`β ≥ 2.3` is untested. The likely outcomes of this design are therefore FAILS or UNRESOLVED; a SUPPORTED verdict would be
a surprise, and an UNRESOLVED one reports `R_low` and the Pinsker diagnostic as the evidence.

**Verdicts per `β` (SU(2), `κ = 16`, `ℓ = 6`; `κ = 4` and `ℓ = 4` reported as trends):**
* **`WL-S` SUPPORTED:** some `t` in the grid with (i) `R_up(t) < 1` on all sampled good boxes and on the good adversarial
  instances, with G3 passed, and (ii) merged bad clusters (range 1) with a connectivity function falling at least by a factor
  10 from `r = 1` to `r = 4` blocks and no spanning cluster on the `16⁴` lattice in more than 5 % of configurations.
* **`WL-S` FAILS (kill):** for **every** `t` in the grid, either `R_low(t) ≥ 1` (conclusive, observable level) on sampled good
  boxes at 2σ, or bad clusters at range 1 span the lattice in more than 50 % of configurations. Reading: the iterated route
  with this blocking fails as stated at that `β`; a different blocking or a coarser cell is the only way on.
* **`WL-S` UNRESOLVED:** every other outcome (for example upper bounds `≥ 1` or not stationary with lower bounds `< 1`, or
  spanning fractions between 5 % and 50 %). Reading: the instrument cannot decide; the numbers to report are `R_low`, the
  Pinsker diagnostic, `m`, and the field-size and influence-bad cluster statistics.
* **Containment reading (`WL.md` 10, reported, not a verdict):** the relative-sparseness ratio
  `η_infl · (2w + l_B)^4` with `w = log(2 × 10³)/m` from the measured `m`; `≪ 1` is what containment without absolute rarity
  needs.
* **`WL-Q` REFUTED for this blocking:** some adversarial instance (run 2) with `C_low(z) ≥ 1` at 2σ. Reported with the
  instance class. Under `WL.md` 3 this closes the per-scale quenched route to `P4Star` for this blocking and **not** the
  stage-two route. Caveat: the adversarial block fields are not checked to be realisable under a law of the class `C`; A6
  (twisted outside) and A3 (twisted `Y`) are, as rare configurations of any law with positive density.
* **A6 (twisted outside), expectation, not a gate:** `R_low` grows with `β` (the forced sheet is costlier and its position
  flatter). A fail at 3.5 and a pass at 2.3 would locate where the quenched form recovers along the crossover.
* **2I (run 4), expectation, not a gate:** sampled fields pass (frozen fine field, short conditional correlations), A3 may
  give `R_low ≥ 1` (a twisted block field in an ordered finite-group phase can leave a domain wall free inside the box). If
  seen, it is a direct example of `WL-Q` failing while `WL-S` holds.

## 6. Code needed (none written)

* `constrained.py` (new, in a new run folder): the box sampler of section 2 (linear staple plus normaliser correction), the
  coupled pair (proposal coupling from c8b `decisive.py coupled`, shared acceptance uniform), the observables, `R_up`, `R_low`,
  `k̂_Y`, the bad-cell classifier and cluster analysis (union-find with merge range). Reuses `lattice/boundary.py` and
  `c3b-refit/goodblock.py` and `c8b-decisive/decisive.py` read-only.
* **Selftests (CPU, before any GPU):** (a) normaliser `z(κr)` against numerical quadrature, 1e-10; (b) single-link
  conditional law of the sampler against direct numerical integration on one link (KS test); (c) G1; (d) the
  Metropolis-corrected heat bath preserves the conditional law (detailed balance check on a 2-link toy); (e) U(1) and 2I paths
  run.

## 7. What this cannot show

* A pass is "no violation found among the instances tried", never the worst case over good boundaries (finitely many
  outsides; greedy adversary only).
* One blocking (c3b's), factor 2, one step; the crossover needs every step and M1's blocking.
* Rarity on `16⁴` only (connectivity up to 4 blocks); volume uniformity is not tested.
* Nothing here bears on the landing or the closure, which carry the gap (`WL.md` 7). A clean `WL-S` pass is evidence for
  stage two at these couplings, not for the gap.

## 8. Timing plan (fixed now; the full run waits for the owner)

> **Amendments A1-A5 (2026-11-23, before any production data; `w2/PIPELINE.md`):** both angles `θ` per job (160 pairs per
> job); launch batches of 3 jobs (`ℓ = 6`) or 6 jobs (`ℓ = 4`); start 1 = equilibrium interior heated by 20 sweeps at κ = 0;
> one timed job only (owner's scope, hard cap 45 minutes); the sampler's proposal linearises the normaliser (full
> Metropolis-Hastings). **Pilot result (CPU):** `T(2.3) = 300`, `T(3.5) = 600` by the rule of step 1; coupled-pair
> disagreement saturates at 86 % (β = 2.3) and 83 % (β = 3.5) of the box links. Timing and projection: `w2/PROJECTION.md`.

> **Amendment A6 (2026-11-23, owner's decision, before any production data).** The owner, after the first projection:
> "For the GPU thing: Lets combine it into a custom GPU routine for SU(2) only, that should bring it down to under 3h!"
> * **Scope (narrow run):** SU(2) only; β = 2.3 and 3.5; κ = 16; `ℓ = 6`; `θ = π` only (40 pairs per start, 80 per job);
>   sampled `Y` = 8 per β; adversarial A1-A4 with the equilibrium outside and the worst of a pool of 8, A6 once; A5 dropped
>   (no adjoint generator); no U(1), no 2I, no `κ = 4`, no `ℓ = 4`, no β = 2.6, 3.0. Mixed packing: jobs of one β share
>   launches (6 jobs, 480 pairs, per launch). Target: the whole narrow run in under 3 GPU-hours.
> * **Speed:** one fused GPU kernel per colour-class update (SU(2) only). The existing array path stays as the reference;
>   the fused path must agree with it (section 6, amended in `w2/PIPELINE.md`).
> * **What it can deliver:** the lower side `R_low` (observable-level influences, conclusive for a fail), the adversarial
>   column sums `C_low` (the `WL-Q` test), the conditional-mass profile `m`, the field-size bad-cell statistics, and saved
>   configurations from which the two-level influence-bad classification (`../INFLUENCE-BAD.md`) can be computed on the CPU
>   afterwards.
> * **What it cannot deliver:** a `WL-S` SUPPORTED verdict. The coupled-chain upper side `R_up` saturates (pilot: 83-89 % of
>   the box links disagree), so the pass side is out of reach with this instrument. Without the photon control (U(1)) the
>   content gate G2 cannot be run, so any SU(2) pass-like number would be unguarded against fake uniqueness; the run reports
>   numbers, not a `WL-S` verdict. The possible verdicts are therefore `WL-S` FAILS (kill), UNRESOLVED, and `WL-Q` REFUTED or
>   not refuted for this blocking.

**Unit of work.** One *job* = one (theory, `β`, `κ`, `ℓ`, `Y` instance, `σ` choice) with 40 coupled pairs (32 shell links plus
8 block variables), two starts each, `T` sweeps per pair (both chains), plus the observables.

**Job count.** SU(2): run 1: 4 `β` × 2 `κ` × 2 `ℓ` × 16 `Y` × 1 `σ` = 256; run 2: 4 × 2 × 2 × (7 instances × 2 `σ` + A6 × 1) = 240
(plus the greedy pool's pilot: 8 short pilots per adversarial job, counted as 1 job each at `T/10`); U(1): at most
2 × 2 × 10 × 2 = 80 (cheap, CPU-able); 2I: at most 2 × 2 × 9 × 2 = 72. Rarity: 4 `β` × 2 `κ` × 200 configurations of `16⁴` (generation only, no coupled chains).

**Procedure.**
1. **Pilot (CPU):** `ℓ = 4`, `κ = 16`, one sampled `Y`, at `β = 2.3` **and** `β = 3.5`; record disagreement against sweeps; fix
   `T(β)` as the first multiple of 50 sweeps after which both starts agree within 2σ, times 2; for `β = 2.6, 3.0` use the
   larger of the two. If no plateau by 2000 sweeps at either `β`, stop: report and redesign (do not move to GPU).
2. **Time one job on the GPU at each end:** `ℓ = 6`, `κ = 16`, A3 twisted, worst-of-pool `σ`, all 40 pairs, both starts, at
   `β = 2.3` with `T(2.3)` and at `β = 3.5` with `T(3.5)`. Record wall times `t₁(2.3)`, `t₁(3.5)` and GPU memory. Which end
   is slower is measured, not assumed.
3. **Project:** `t_total = Σ_jobs t₁(β_job) × (|B_job| / |B_{ℓ=6}|) × (T(β_job) / T(β_ref))`, with `t₁(β)` interpolated
   linearly between the two timed points and `β_ref` the timed point used, plus the influence-bad box measurements (16 per
   `β`, one `ℓ = 4` job each), plus the measured generation time per `16⁴` configuration × 1600 for rarity. Report the projection to the owner with the job table. **A-priori guide only,
   not a plan:** the c7b dry run projected 4 h and overran about 100-fold (`PROOF-BLUEPRINT.md`, cycle 7); this design times a
   full-size job precisely to avoid that.
4. **Budget cap:** 20 GPU-hours total. If the projection exceeds it, cut in this pre-registered order until it fits: (i) `κ = 4`
   only at `β = 2.3` and 3.5; (ii) `ℓ = 4` only at `β = 2.3`; (iii) sampled `Y` from 16 to 8; (iv) `θ = π` only; (v) A5 at
   `β_A = 2.5` only. If it still does not fit, ask the owner.
5. **Abort rule during the run:** if any job takes more than twice its projected time, stop the queue after that job and report
   (no silent continuation).
6. **Order of the queue:** gates first (G0, G1 on one job each; G2 photon jobs on CPU in parallel), then `β = 2.3` (the decisive
   end), then 3.5, 2.6, 3.0. A G2(a) failure stops the SU(2) queue.

**Outputs:** one `.npz` per job, `analysis.json` with every number of section 3 and the verdicts of section 5, and a
`RESULT.md` that scores the verdicts exactly as written here.
