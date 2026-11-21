# The assembly (proof phase, readiness step P7.1, 2026-11-22)

Lean: `../../formal/ProofPhase/Objects.lean` (the objects, the gap, what already follows) and `../../formal/ProofPhase/Assembly.lean`
(the open pieces and the assembly theorems). Built in `~/formal-phase-asm` (Lean 4.34.0, Mathlib v4.34.0) with
`build-asm.sh ProofPhase.Assembly`; `axioms-asm.sh` prints the axioms of 15 headline theorems: all `propext, Classical.choice,
Quot.sound`; no `sorry`, no `native_decide`, no new axioms. Inputs taken into account: the round-3 review (`../attempts/r3-review/REVIEW.md`)
and the coordinator's relay of the round-4 review (first pass and "missed approaches", 2026-11-22).

## The top-level statement

`ProofPhase.yang_mills_assembly : OpenPieces T → MassGap T ∧ LimitRP T ∧ NonTrivial T`

for a `Tuning T` = (physical unit `L₁`, resolution `ℓ_k` lattice steps per `L₁`, bare coupling `β_k`) of **SU(2) lattice Yang–Mills with
the Wilson action on 4D tori** `(ℤ/2(j+1)ℓ_kℤ)⁴` (physical side `2(j+1)L₁`, spacing `a_k = L₁/ℓ_k`). Yang–Mills is inside every
hypothesis: each field is a statement about `wilsonMeasure SU2 2 β_k` on these tori, about its correlations, or about its transfer
operator.

**`MassGap T`** (precise): there is `m > 0` such that for every family of slab observables (measurable, gauge invariant, `|F| ≤ 1`,
supported in the time slab `[0, s]` and on finitely many links), every physical time `τ ≥ 0`, every choice of infinite-volume limit
points `h_k` of the reflected correlation `Cov(F∘S_n, F∘Θ)` at `n = ⌊τ/a_k⌋`, and every limit point `g` of `h_k` as `k → ∞`:
`|g| ≤ 2 e^{-mτ}`. Order of limits: volume first, then spacing; every limit point, no uniqueness assumed.
* Not vacuous: correlations are bounded by 2 (`abs_wcorr_le`), limit points always exist; the free photon fails it.
* Not stronger than the Clay gap: the limit functional is reflection positive (`limitRP`, proved) and time-translation invariant, so it
  reconstructs (OS) a Hilbert space with `e^{-τH}`; the reflected correlation is `⟨ΘFΩ, e^{-τH}(1−P_Ω)FΩ⟩ ≤ ‖F‖²e^{-Δτ}` if `H` has
  gap `Δ`. Conversely `spectral_gap_of_decay` (proved: a finite measure on `[0,∞)` whose Laplace transform decays like `e^{-mt}`
  gives no mass to `[0,m)`) turns `MassGap` into the spectral gap on the span of slab vectors, which is dense. So `MassGap` is the
  spectral gap of the reconstructed theory, modulo the reconstruction itself (P6.5).
* `LatticeGap T` (the lattice-uniform form, from some level on, slightly stronger than Clay) implies `MassGap T` when `a_k → 0`
  (`massGap_of_latticeGap`).

## The fields of `OpenPieces` and their blueprint pieces

| field | statement (about the objects above) | blueprint | used by the proof | pure noise (`β = 0`) |
|---|---|---|---|---|
| `lcp.resolution` | `ℓ_k → ∞` | P6.6 | yes (`a_k → 0`) | can hold |
| `lcp.running` | `β_k / log ℓ_k → 11/(3π²)` (one-loop SU(2) asymptotic freedom, `β = 4/g²`) | P6.6, short-distance agreement with perturbation theory | no (identification only) | **fails** (`not_trivial`) |
| `lcp.scheme` | act number of the box of side `L₁`, `z_k = ℓ_k·E_e(β_k, ℓ_k) → z⋆ > 0`, `E_e` the flux energy of the temporal-gauge transfer operator on Gauss-law (gauge-invariant) states | P6.6 (renormalisation condition), contains P1.7 (strict `E_e > 0`, eventually) | route B only | not checked |
| `nontrivial` | some slab correlation at some `τ > 0` has all continuum limit points `≥ c > 0` in modulus | P6.2 (non-triviality half) | no (passed to the conclusion) | fails (on paper: product measure, zero covariance; not formalised) |
| `crossover`, route A: `SlabDecay` | reflected slab correlations decay as `C_k e^{-m n a_k}` on every torus, one physical rate `m`, constant depending on the level only, from some level on | P4.1 restated in gap strength (round-4 review, "missed approaches" 1) | yes | holds (infinite gap) |
| `crossover`, route B: `ConjW` | `z(β_k, 2^{j+1}ℓ_k) ≥ (1+δ)² z(β_k, 2^jℓ_k)` for all levels and box sizes | P4.2 (doubling form; P4.3–P4.5 inside it) | yes | not checked |
| `crossover`, route B: `SectorTransfer` | `FluxGrowth T → MassGap T` | P5.1 | yes | holds (consequent true) |

`not_trivial` (proved): the family with `β_k = 0` at every level, i.e. product Haar measure, the zero potential at every scale, does not
satisfy `OpenPieces`; more generally every family with bounded bare coupling (strong coupling included) fails `lcp.running`
(`not_onLCP_of_bounded`). This closes round-3 finding 2 at the level of the hypotheses: decay alone is satisfied by pure noise (it has
an infinite gap), so the identification with Yang–Mills is carried by P6.6 and P6.2, which are therefore fields.

Consistency: only `lcp.resolution` + `lcp.running` have a proved witness (`bareRunning_witness`). No witness is given for
`lcp.scheme`, `NonTrivial`, `SlabDecay`, `ConjW`, `SectorTransfer`; strong coupling satisfies `SlabDecay`-type decay at fixed `β`
(`AreaLaw.Reach`, `OneScale.LinkDist.wilson_singleLink_timeDecay`) but that has not been put in this form. Joint consistency of all
fields is the open problem itself.

## The two routes do not compose; they are joined by a disjunction

* **Route A** (`assembly_routeA : OnLCP T → SlabDecay T → MassGap T ∧ LatticeGap T ∧ LimitRP T`). Lean content: Theorem C on the
  torus (reflection positivity, Hankel identity, doubling) removes the level constant; the infinite-volume limit; the continuum limit.
  D′ is a sufficient condition, proved as a lemma: `slabDecay_of_uniformGDS` (fine-level worst-case Dobrushin with thin cubes of
  physical size `L₀` ⇒ `SlabDecay` at rate `log(1/γ)/(4L₀)`), which is the project's old `UniformGDS` and is strictly stronger than the
  gap (and likely false at fine level, ROUND-1's free-field obstruction).
* **Route B** (`assembly_routeB : OnLCP T → ConjW T → SectorTransfer T → MassGap T ∧ LimitRP T`). Lean content: only
  `fluxGrowth_of_conjW` (W + the renormalisation condition give geometric growth of the act number, uniformly in the level). **P5.1
  carries the whole vacuum-sector content**; it is stated as an implication because no weaker precise form is known. Route B shares
  no Lean with route A.
* The top-level theorem takes `SlabDecay T ∨ (ConjW T ∧ SectorTransfer T)` and proves the conclusion by cases.

## The blocked route at L₁ (round 3's chain on the real blocked laws; last link missing)

`Assembly.lean`, section "blocked route": `RPBlocking` (any blocking commuting with the time reflection and respecting the closed
positive half; `blocked_wilson_rp` proves every such blocked layer reflection positive, generalising `decimated_wilson_rp`),
`H1Local` (P3.2/P3.3, lattice-uniform: blocked laws are Gibbs with coarse potentials converging locally to a limit, uniformly in the
volume), `LimitDprime` (P4.1, D′_λ at `L₁`), `ObsTransfer` (P5.2, H1-fine: conditional decoupling and quasi-locality of `E[F|Φ]`,
stated with `condExp`; the choice `f = g = 0` is excluded). Proved: `blockGap_of_blockedRoute` (H1Local + LimitDprime ⇒ decay of block
observables `f∘Φ` of the real Wilson measure, uniform in the level and the volume). This closes round-3 finding 2's "no file imports
both": R3's chain now runs on blocked SU(2) Wilson laws. **Missing Lean link L1:** `H1Local ∧ LimitDprime ∧ ObsTransfer ⇒ SlabDecay`
(law of total covariance plus fine/coarse slab geometry, `r3-robust/NOTE.md` §6) is on paper only; this route is therefore not a
disjunct of `OpenPieces`.

## Proved here, no longer open (what already follows)

* `limitRP`: reflection positivity of every continuum limit point, for bounded measurable functions of the closed positive half
  (the positivity half of P6.3), from lattice RP at every level and closedness.
* `blocked_wilson_rp`: RP of every blocked layer for every reflection-respecting blocking (P1.6 as a property of the blocking).
* `spectral_gap_of_decay`: the spectral reading of the decay.
* Time-translation invariance at every level is in `OneScale.TimeShift` (`integral_tShift`); the Hankel identity is proved there
  (`hankel_identity`, `hankel_corr`), so the header of `OneScale/CorollaryB.lean` (lines 26-30, "not formal") is stale.

## Missing or mis-stated pieces found

1. **P6.4 (Euclidean invariance) cannot be stated about the current objects**: rotations act on continuum fields, the lattice has only
   the hypercubic group, and a hypercubically invariant lattice observable can contain spin-4 parts, so "limit two-point functions are
   O(4) invariant" is false as a statement about lattice observables. It needs a new object first: **P6.7, renormalised local
   gauge-invariant fields as distributions with the OS regularity bound** (round-4 review). Not a field; the conclusion does not claim it.
2. **P6.5 (OS reconstruction, Wightman)** needs the limit as a state on a field algebra (P6.7) before it is "known"; `MassGap` is
   equivalent to the spectral gap only through it.
3. **Uniqueness of the limit (half of P6.2)** cannot be stated for arbitrary observable families (`SlabObs` lets `F` change with the
   level); it needs "the same observable at every level", i.e. P6.7 again. Only non-triviality is a field.
4. **The infinite-volume limit as its own piece**: the gap here is stated for every infinite-volume limit point at fixed spacing
   (volume first); existence and uniqueness of the infinite-volume state and the opposite order (continuum at fixed physical volume,
   the OpenAI order) are not addressed.
5. **A blocking with a non-trivial limit is missing** (P1.5/P1.6): decimation at fixed physical `L₁` has a pure-noise continuum limit
   (perimeter divergence of the straight Wilson line), so it cannot be route A's blocking; a blocking that averages inside each time
   slice and decimates in time keeps RP (`RPBlocking`) but is not constructed. The act transport identities (`act_conserved_per_layer`)
   hold for every measurable map and are not used.
6. **The flux energy** is defined through the transfer operator with Gauss-law states (`fluxE`); the identification `Z = tr(P_G Tⁿ)`
   with the 4D Wilson measure is not formalised, and a definition from the 4D measure (Polyakov-loop correlator, log-convexity) needs
   **anisotropic tori** (spatial box fixed, time extent to infinity), which `LatticeLink d N` does not provide. The per-move form of W
   needs anisotropic boxes too.
7. **Gauge group**: everything is SU(2); the Clay problem asks for every compact simple G. The generic objects (`wilsonMeasure`,
   `GaugeInvariant`, `RPBlocking`, `corr_le_of_decay`) are stated for any compact group with a continuous unitary representation;
   the line of constant physics (one-loop slope `11N²/(12π²)` for SU(N), centre `Z_N`) and the scheme are SU(2)-specific.
8. **P4.1 as written in the blueprint is stronger than the chain consumes** (round-4 review): the assembly uses `SlabDecay` (gap
   strength); D′ is now a sufficient condition (lemma), not the open piece.
9. **P4.6 and P4.7** are not on the critical path of either assembly; P4.7's assumption (U) is false as literally stated (universality
   only up to `O(a²)`).
10. **P1.7** is absorbed into `lcp.scheme` (`z⋆ > 0` gives `E_e > 0` eventually); strict `E_e > 0` at every level is not needed.

## Build

```
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/setup-asm.sh
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/build-asm.sh ProofPhase.Assembly
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/axioms-asm.sh
```
