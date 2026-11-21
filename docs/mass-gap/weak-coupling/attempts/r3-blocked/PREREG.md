# Pre-registration: does the blocked SU(2) action land in a proven strong-coupling window? (Leg C, the "click" test, 2026-11-21)

**Status: pre-registered 2026-11-21 by round 3, attempt 4 (r3-blocked), before any GPU run.** Only the CPU pipeline test (6⁴, a few
minutes, marked as such below) has been run. The coordinator's addition of r3-robust's criterion D′ (received during preparation,
before any data) is part of the criteria below. Runs: `queue_blocked_gpu.ps1`, to be started by the coordinating session after Leg B.
Any change after the first GPU data must be marked as such, as in `../../../lattice/PREREG-BOUNDARY.md`.

**Why.** Round 2 left the crossover as the open core (`../ROUND-2.md`): does the theory, blocked to a physical scale L₁, sit in a
window where a strong-coupling criterion is proven? Attempt C (`../r2-curvature/NOTE.md`) could only compare its windows with a
two-coupling *stand-in* (fundamental coupling from σ, adjoint from the glueball mass), whose model error it could not quantify, and
proposed this measurement (its §9). Attempt B's Theorem S′ (`../r2-coupling/NOTE.md` §3.4) and attempt 1 of round 3 (r3-robust,
`../r3-robust/NOTE.md` §1, §4: the reduction closes, in Lean, once the blocked theory satisfies D′_λ) give further criteria on the
same object. This measurement replaces the stand-in by the fitted blocked action, with an error bar, at L√σ ∈ {2, 3, 4}.

## Question

For SU(2) blocked to physical block sizes L√σ ≈ 2.1, 3.15, 4.2 (and 1.55, 2.32, 3.10 at a second β), what are the couplings of the
effective action (fundamental and adjoint plaquette, with spin-3/2 and 1×2-rectangle extensions), and at which L does that action
first lie inside each criterion's window, with the photon outside every window at every L?

## The instrument (`blocked.py`, `analyse_blocked.py`; self-tests and the pipeline test below)

- **Ensembles.** Periodic 36⁴ lattices, Wilson action. SU(2): the fused CUDA heat bath and overrelaxation of `../../../lattice/gpu/`
  through `../../../lattice/boundary.py` (imported unchanged, all links dynamic). U(1) and Z₂: boundary.py's array code. 4 chains,
  200 thermalisation sweeps, then 80 measurements, 4 sweeps (1 heat bath + 3 overrelaxation) between measurements: 320
  configurations per run.
- **Block variables.** The configuration is smoothed by the gradient (Wilson) flow (Luescher 2010), Euler steps of ρ = 0.1 aligned
  to multiples of 0.1, then the coarse link V(X, μ) is the product of the b flowed links along the block edge. Coarse links are group
  elements, covariant under gauge transformations at the coarse sites. Smoothing radius √(8t) = f·b lattice units:
  - **f = 1/2, primary.** Per direction the flow's rms radius is √(2t) = b/4. That is close to the transverse spread b/√12 ≈ 0.29b of
    a Balaban-type average over the block cross-section, which is the block variable C's analysis assumes (C §1).
  - **f = 1/4** (weaker smoothing) and **f = 0** (raw path product): variants, reported. C §4 item 2 predicted the dependence: raw
    products tend to Haar, which makes every window trivially reachable. Expectation stated now: at f = 0 the photon's blocked
    coupling falls with b (perimeter suppression, already β₁ 1.1 → 0.53 at b = 2 in the pipeline test), so f = 0 should fail the
    photon gate at large b, while f = 1/2 should keep β₁ ≈ 1.1 at every b (scale invariance of the free field).
  - Sixteen coarse lattices per configuration (origins {0, b/2}⁴), Z₂: f = 0 only (no flow for a discrete group; for the deconfined
    control the raw product is the hardest case, since smoothing can only order it further).
- **Fit (inverse Monte Carlo by Schwinger–Dyson equations;** idea from Falcioni, Martinelli, Paciello, Parisi and Taglienti 1986 and
  Gonzalez-Arroyo and Okawa 1987, used on blocked configurations by Takaishi 1996; recalled, not re-read; derivation and code ours).
  For an action S = Σᵢ βᵢFᵢ the identity Σᵢ βᵢ⟨∇Fⱼ·∇Fᵢ⟩ = −⟨ΔFⱼ⟩ holds for every link and every j, so βₛ solves a linear system.
  Basis per plaquette p: **fund** ½tr V_p, **adj** χ₁(V_p)/3 (C's normalisation: exp((β_A/3)Σχ_A)), extensions **spin-3/2**
  χ_{3/2}(V_p)/4 and **rect** ½tr of the 1×2 loops. U(1): cos θ_p, cos 2θ_p, cos 3θ_p, cos θ_R. Z₂: pseudo-likelihood (Besag) for
  plaquette and rectangle couplings. Base fit {fund, adj} ({q1, q2}; Z₂ {plaq}); extension fits add spin-3/2, rect, or both.
- **Errors.** Jackknife over at least 20 blocks of measurements (blocks within chains). Y = (β_F, β_A) of the base fit, with error
  hypot(stat, trunc), where trunc is the largest change under the extensions. **Closure**: for each unfitted basis function the
  relative violation of its SD identity by the base fit, reported as the residual of the truncation.

## Lattices, β and physical sizes

a√σ from our TTL scan (`../../../results/ttl_summary.json`, as `analyse_boundary.py` reads it): β = 2.3: 0.3503(61); β = 2.4: 0.2579(29).

| β | N | b (coarse lattice N/b) | L√σ = b·a√σ | box N·a√σ | role |
|---|---|---|---|---|---|
| 2.3 | 36 | 6 (6⁴), 9 (4⁴), 12 (3⁴) | 2.10, 3.15, 4.20 | 12.6 | the click table |
| 2.4 | 36 | 6, 9, 12 | 1.55, 2.32, 3.10 | 9.3 | scaling check at 2.32 and 3.10 |

36⁴ with 4 chains: peak GPU memory about 4 GB (generator 1.7 GB in 2×2 complex form, links in quaternion form 0.9 GB, flow working
set below 1 GB), within the 8 GB laptop GPU once Leg B has finished. The controls use the same lattice and the same b (in lattice
units; U(1) and Z₂ have no σ there).

## Runs (`queue_blocked_gpu.ps1` = `blocked.py`'s `PLAN`, in this order)

| # | run | β | start | blocks, f | flow to t | role | est. minutes |
|---|---|---|---|---|---|---|---|
| 0 | `selftest --gpu`, `bench` | | | | | gate: GPU = CPU on flow, blocking, SD sums; timings | 5 |
| 1 | U(1) | 1.1 (Coulomb) | cold | 6, 9, 12; 0, ¼, ½ | 4.5 | **photon gate** | 21 |
| 2 | SU(2) | 2.3 | cold | 6, 9, 12; 0, ¼, ½ | 10.125 (√(8t) = 9) | **the click table**; α_GF to 3.15/√σ | 96 |
| 3 | Z₂ | 0.6 (deconfined) | cold | 6, 9, 12; 0 | | Z₂ control | 8 |
| 4 | U(1) | 0.9 (confined) | hot | 6, 9, 12; 0, ¼, ½ | 4.5 | positive control (reported) | 21 |
| 5 | Z₂ | 0.3 (confined) | hot | 6, 9, 12; 0 | | positive control (reported) | 8 |
| 6 | SU(2) | 2.4 | cold | 6, 9, 12; 0, ¼, ½ | 4.5 | scaling check | 61 |

**GPU time: about 3.7 h, ±50 %.** Basis: the fused heat-bath kernel at 0.45 µs per site and sweep (Leg B's logged runs: β = 2.6,
22⁴, 4 chains, 0.5 µs including its measurement; `gpu/README.md` 0.39 µs); the flow and blocking are cupy array code, whose
memory traffic was counted exactly on the CPU (a counting array type: 19.4 kB per site per SU(2) flow step with the fused quaternion
kernel, 316 launches), converted at an effective 300 GB/s: 0.115 s per SU(2) flow step per 36⁴ configuration, U(1) a quarter of
that. The queue's `bench` step measures the real numbers first and logs the projected total. Hot starts for the confined controls:
β = 0.9 lies 10 % below the U(1) transition, and a cold 36⁴ start could stay metastably in the Coulomb phase. Cheapest cuts: the
GF extension in run 2 (−35 min), run 6 (−61 min; loses the scaling check).

The queue stops before any SU(2) run if the GPU selftest fails on both code paths (fused kernel; array code with
`BLOCKED_FUSED=0`), or if the photon gate fails for the primary blocking.

## Criteria (the X side), evaluated on every fit (`analyse_blocked.py` docstring is the reference)

| criterion | source | form (SU(2)) | pure fund. window | pure adj. window | what INSIDE means |
|---|---|---|---|---|---|
| **W1** (C, linearised single-link coarse curvature) | `../r2-curvature/NOTE.md` 2.2–2.4 | γ = 18(k_F\|β_F\| + (8/3)k_A\|β_A\| + k_T\|β_T\|) + 90 k_F\|β_R\| < 1; k_F = 8/(9π); k_A ∈ [0.0531, 0.0722]; k_T ∈ [0, 0.144] | β_F < 0.196 (proved: 0.124) | β_A < 0.289 (hi) to 0.392 (lo) | the action sits in C's curvature window at the linearised level; no theorem at that coupling (except the proved fundamental strip); next step would be C's certified sup computation for this action |
| **D′** (r3-robust, worst-case Dobrushin) | `../r3-robust/NOTE.md` 1, 4 | Σ_{i≠z} tanh(S_iz/2) < 1, S_iz = n_P o_P + n_R o_R, o the oscillation of the factor, counts enumerated (18 plaquette pairs, each also sharing 2 rectangles; 2 pairs sharing 6 rectangles; 42 rectangle-only pairs) | 0.0556 (α_s > 5.72) | 0.0834 | **proved (Lean)**: the fitted action satisfies Dobrushin's condition for every boundary; with H1-local the reduction closes for that action. Weighted D′_λ: λ* = sup{λ : D′_λ < 1}, the proved decay rate λ*/L |
| **S′** (B, soft swap) | `../r2-coupling/NOTE.md` 3.4 | max over factor types of Σ n(X meets Y) δ_Y, δ = 1 − exp(−2 osc); n enumerated (plaquette: 20 P, 64 R; rectangle: 32 P, 86 R) | 0.0128 | 0.0192 | **proved**: torus decay (a gap-only statement) for the fitted action |
| **BE** (Bakry–Emery / Otto–Reznikoff) | C 2.1 | (24\|β_F\| + 76\|β_A\|)/2 < 1, base fit only | 0.0833 | 0.0263 | **proved**: positive curvature of the Langevin dynamics, W-GDS for the fitted two-coupling action |

Strictness: S′ is the strictest (S′ ⇒ D′, r3-robust §1); D′ is stricter than BE in the fundamental channel and weaker in the adjoint
channel; W1 is the weakest and the only one not proved at the coupling. U(1): W1 γ = 18(2/π)(|β₁|+|β₂|+|β₃|) + 90(2/π)|β_R| (window
π/36), D′ and S′ with the U(1) oscillations, no BE. Z₂: W1 γ = 18 tanh|β_P| + 90 tanh|β_R|, D′, S′.

**Verdict per point, criterion and fit:** INSIDE if value_hi + 2·stat < 1, OUTSIDE if value_lo − 2·stat > 1, else UNDECIDED. A point
is INSIDE (OUTSIDE) for a criterion only if the base fit **and every extension fit** say so (the truncation test; BE: base only);
otherwise UNDECIDED. (Changed during the pipeline test, before any GPU data: a first draft added the extensions' shift in quadrature
as an error. That is wrong for S′ and D′, where an extension adds factor types, so their value jumps by construction.)

## Decision rules and readings (the Y side against the X side)

For SU(2), primary blocking f = 1/2, at each L√σ:

- **CLICK(criterion, L)**: the point is INSIDE. Preconditions: the photon gate passed for f = 1/2; for W1 and D′ (confinement-type,
  `../RULES.md` round 2) also the Z₂ control passed.
- **NO CLICK(criterion, L)**: OUTSIDE.
- **Entry scale** per criterion: the smallest measured L√σ with CLICK, and the log-linear interpolation of the value's crossing of 1
  between measured points (reported with the bracketing points; extrapolation beyond 4.2 is reported only as "> 4.2").
- **Scaling check** (β = 2.4 against β = 2.3 interpolated log-linearly in L): β_F and β_A agree within 2 combined errors at L√σ =
  2.32 and 3.10. If not, the numbers are lattice-artefact dominated at these b, and the click table is read as indicative only.

What each outcome means:

| outcome at L√σ ≤ 4.2 | meaning |
|---|---|
| D′ CLICK at L | the fitted, truncated blocked action at L satisfies a criterion that r3-robust's Lean chain turns into the gap, given H1-local. The remaining gap is then exactly H1 (the true blocked theory is close to the fitted one in local sup norm) plus the truncation, whose size the closure residuals and the extension fits measure. The strongest possible outcome. |
| S′ or BE CLICK | the same with B's torus engine (S′, gap-only) or curvature (BE); S′ implies D′. |
| W1 CLICK, D′ NO CLICK | C's linearised window is reached, the worst-case ones are not: the crossover is located where C's stand-in put it, but a proof needs either C's certified (non-linearised) sup computation or a block criterion (C §2.5). |
| NO CLICK for all criteria | no single-site criterion reaches the measured action by L√σ = 4.2. The hand-over needs larger L (more running for H1 to carry) or block criteria. The measured couplings still give the gap factor (Y/X) that replaces C's unquantified stand-in. |
| UNDECIDED | reported with the band; the truncation (extensions disagreeing) or statistics decide it, and the report says which. |

Expectations from C's stand-in (stated before the data, not criteria): β_A ≈ 1.17, 0.50, 0.21 at L√σ = 2, 3, 4 (band ±20 %);
β_F ≈ 0.07, 5·10⁻⁴, 5·10⁻⁷. Hence W1 crossing at 3.3–3.9; D′ (needs β_A < 0.083) not before L√σ ≈ 4.8, so D′ is expected to fail
at every measured L; S′ and BE likewise. The stand-in's model error was not quantified; the measured action may differ by more
than these bands, in either direction, and with a blocking dependence (f) the stand-in does not have.

The couplings are also reported as α: α_F = 1/(πβ_F) and the tree-level α_eq = 1/(π(β_F + 8β_A/3)) (C's convention, the owner's α
pointer, `../../PREP.md` last section; α_eq is not a physical coupling, C §3.4).

## Controls

- **Photon gate (U(1), β = 1.1, Coulomb).** For f = 1/2 at every b ∈ {6, 9, 12}: W1, D′ and S′ all OUTSIDE. **If not, the queue
  stops before SU(2)**, and f = 1/2 is not an instrument that can tell a massless theory from a gapped one. The gate is also reported
  for f = 0 and 1/4: a variant that fails it is disqualified, and its SU(2) numbers are not evidence.
- **Z₂ control (β = 0.6, deconfined, gapped).** W1 and D′ are confinement-type (they give boundary-uniform decorrelation, H2): both
  must be OUTSIDE at every b. S′ is gap-only (torus decay): reported; it may hold (Z₂ has a gap) but must not be read as an area law.
- **Positive controls (reported, not gates).** Confined U(1) (β = 0.9) and confined Z₂ (β = 0.3) at b = 12: expected INSIDE for W1
  (and D′ for Z₂). If they do not click, a SU(2) "no click" says little about SU(2), and the report says so.

## Gradient-flow coupling (for r3-monotone; same configurations)

g²_GF(t) = (128π²/9)·t²⟨E(t)⟩ (Luescher 2010, SU(2)), E = 24(1 − plaquette) (plaquette discretisation), α_GF = g²/(4π) at scale
√(8t)·a√σ, on the flow-time grid t = 0.5, 1.0, ... (lattice units): to √(8t)√σ = 3.15 at β = 2.3 and 1.55 at β = 2.4. Reported:
the table with jackknife errors; **monotone** if no successive difference is below −2σ, and whether it is strictly increasing at 2σ;
the β comparison at matched √(8t)√σ (reported, lattice artefacts at small t are large). Stated systematic: the Euler flow at ρ = 0.1
overestimates t²E by 3.2 ± 0.3 % (t = 1) and 2.8 ± 0.4 % (t = 2) against RK3 (measured on 8 configurations, 8⁴, β = 2.3), a
near-constant factor that cannot change a monotonicity reading. Finite volume: √(8t) ≤ 9 against a box of 36. This coupling is not
RP-controlled and not r3-monotone's twist scheme (its request, `../r3-monotone/NOTE.md` §7, needs a sheet coupling the GPU kernel
does not have; `NOTE.md` here, section 6).

## What this measurement cannot show

1. Anything rigorous about the **true** blocked theory: every verdict is about the fitted, truncated action. The difference is H1
   (`../ROUND-2.md`), and only partly visible here (closure residuals, extension shifts, two β).
2. The **supremum** over configurations of C's W1 sum: W1 is linearised (only the fundamental strip β_F < 0.124 is proved). D′, S′
   and BE are worst-case and proved, but are evaluated on fitted couplings with statistical errors.
3. **Uniqueness of the block variable**: the couplings depend on f (that is why three are measured). A CLICK at f = 1/2 is a statement
   about that variable. Whether it is the variable for which H1 holds is not decided by any measurement.
4. **Range**: only plaquettes and 1×2 rectangles (and one higher character). Longer loops, chairs and twisted loops are absent;
   the closure residuals bound their effect only on the measured identities.
5. **The continuum limit**: two β, three block sizes in lattice units, no extrapolation. Finite coarse lattices (3⁴ at b = 12).
6. **L√σ > 4.2** at β = 2.3 and > 3.1 at β = 2.4: not measured. A crossing beyond is reported as "> 4.2", not extrapolated.

## Self-tests and the pipeline test (CPU, 2026-11-21; part of the instrument, not results)

`python blocked.py selftest` (one process, `CUDA_VISIBLE_DEVICES=-1`, 58 s): staples identical to boundary.py's; the rectangle
staples are exact derivatives (one-link changes against an independent loop computation, 8·10⁻¹⁵); gauge covariance of flow,
blocking and SD sums (SU(2), U(1), 10⁻¹⁵); the SU(2) flow on a U(1)-subgroup field equals the U(1) heat-equation step (4·10⁻¹⁶),
which fixes the flow's normalisation; the SD fit recovers Wilson β = 2.3 (2.2999 ± 0.0091, adjoint −0.002 ± 0.007) and U(1) β = 1.1
from boundary.py's heat bath, Z₂ β = 0.3 and 0.6 by pseudo-likelihood, and **known mixed actions** generated by an independent
Metropolis: SU(2) (β_F, β_A) = (1.0, 0.8) → (1.0009 ± 0.006, 0.7929 ± 0.0047), U(1) (0.6, 0.4) → (0.6005, 0.3993). With `--gpu` it
also compares the fused GPU product, and flow, blocking and SD sums, GPU against CPU.

Pipeline test (pre-registered as a pipeline test only; 6⁴, b ∈ {1, 2}, 2 chains × 24 measurements, all six run types, 43 s in total,
then the analysis): every stage runs and every verdict is produced. At this size the numbers are not physics (b = 2 is L√σ = 0.7).
For the record: the photon gate passes at all f; f = 1/2 keeps the U(1) coupling at b = 2 (1.10 ± 0.23), while f = 0 halves it
(0.53); deconfined Z₂ stays OUTSIDE; confined Z₂ clicks at b = 2 (W1 and D′ INSIDE); α_GF rises monotonically; every SU(2) point is
OUTSIDE.
