# The assembly (proof phase, readiness step P7.1; updated in cycle 2 by workstream C, 2026-11-22)

Lean: `../../formal/ProofPhase/Objects.lean` (the objects, the gap, what already follows), `../../formal/ProofPhase/Assembly.lean`
(the open pieces, the route theorems) and `../../formal/ProofPhase/Torus/Top.lean` (the top-level theorems; cycle 2), with
`../../formal/ProofPhase/Torus/Local.lean` (the transfer counted in physical size, torus decay, both orders of limits). Built in
`~/formal-c2c` (Lean 4.34.0, Mathlib v4.34.0) with `c2c-torus/build.sh ProofPhase.Torus.Top`; `c2c-torus/axioms.sh` prints the
axioms of 27 headline theorems: all `propext, Classical.choice, Quot.sound`; no `sorry`, no `native_decide`, no new axioms. Inputs
taken into account: the round-3 review (`../attempts/r3-review/REVIEW.md`), the round-4 review relay, and the cycle-1 workstream
notes (`ws1-routeA`, `ws2-routeB`, `ws3-quantum`, `ws4-existence`). Cycle-2 details: `c2c-torus/NOTE.md`.

## The top-level statement

`ProofPhase.yang_mills_assembly : OpenPieces T → MassGapLoc T ∧ LimitRP T ∧ NonTrivial T` (module `ProofPhase.Torus.Top`)

and, for the preferred route, both orders of limits:

`ProofPhase.yang_mills_assembly_torus : OnLCP T → NonTrivial T → BlockedTorusRoute T →`
`OpenPieces T ∧ TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T`

for a `Tuning T` = (physical unit `L₁`, resolution `ℓ_k` lattice steps per `L₁`, bare coupling `β_k`) of **SU(2) lattice Yang–Mills with
the Wilson action on 4D tori** `(ℤ/2(j+1)ℓ_kℤ)⁴` (physical side `2(j+1)L₁`, spacing `a_k = L₁/ℓ_k`). Yang–Mills is inside every
hypothesis: each field is a statement about `wilsonMeasure SU2 2 β_k` on these tori (or on the anisotropic tori `ℤ/Tℤ × (ℤ/Lℤ)³` of the
flux energy), about its correlations, or about its blocked laws.

**`MassGap T`** (precise): there is `m > 0` such that for every family of slab observables (measurable, gauge invariant, `|F| ≤ 1`,
supported in the time slab `[0, s]` and on finitely many links), every physical time `τ ≥ 0`, every choice of infinite-volume limit
points `h_k` of the reflected correlation `Cov(F∘S_n, F∘Θ)` at `n = ⌊τ/a_k⌋`, and every limit point `g` of `h_k` as `k → ∞`:
`|g| ≤ 2 e^{-mτ}`. Order of limits: volume first, then spacing; every limit point, no uniqueness assumed.

**`MassGapLoc T`** (cycle 2): the same for every slab observable family of **bounded physical extent** (`SlabObs.Extent O R`: at every
level and volume any two links of the support are at physical distance `≤ R`; any number of fine links), one rate `m` for all `R`.
`MassGap → MassGapLoc` (`massGapLoc_of_massGap`). **`MassGapMFLoc T.toV`**: the same in the opposite order (spacing first at fixed
physical volume, then volume along any increasing sequence of tori; the OpenAI construction's order, workstream 4's `MassGapMF`).

* Not vacuous: correlations are bounded by 2 (`abs_wcorr_le`), limit points always exist; the free photon fails it (bounded-extent
  observables, e.g. a Wilson loop of physical size, have power-law connected correlations).
* Not stronger than the Clay gap, and equivalent to it as far as the gap is concerned: the limit functional is reflection positive
  (`limitRP`, proved) and time-translation invariant, so it reconstructs (OS) a Hilbert space with `e^{-τH}`; the reflected
  correlation is `⟨ΘFΩ, e^{-τH}(1−P_Ω)FΩ⟩ ≤ ‖F‖²e^{-Δτ}` if `H` has gap `Δ`. Conversely `spectral_gap_of_decay` (proved) turns the
  decay of one vector into "no spectral mass in `[0, m)`" for that vector. The vectors `FΩ` of local observables of **bounded physical
  extent** are dense in the reconstructed space (local fields are by definition localised in bounded regions; observables of unbounded
  extent enter only as limits), so `MassGapLoc` already gives the spectral gap `≥ m`, modulo the reconstruction itself (P6.6). What
  `MassGapLoc` does not cover, and why it does not matter: families whose physical extent is unbounded (volume averages over the whole
  torus, loops winding around it, families spreading as `k → ∞`); they are not local fields of the infinite-volume continuum theory.
  Lattice-scale families (a single plaquette at every level) have extent `→ 0` and are covered.
* `LatticeGap T` (the lattice-uniform form, from some level on, slightly stronger than Clay) implies `MassGap T` when `a_k → 0`
  (`massGap_of_latticeGap`).

## The fields of `OpenPieces` and their blueprint pieces

| field | statement (about the objects above) | blueprint | used by the proof | pure noise (`β = 0`) |
|---|---|---|---|---|
| `lcp.resolution` | `ℓ_k → ∞` | P6.7 | yes (`a_k → 0`) | can hold |
| `lcp.running` | `β_k / log ℓ_k → 11/(6π²)` (one-loop SU(2) asymptotic freedom in this project's `β = 2/g²`) | P6.7, short-distance agreement | no (identification only) | **fails** (`not_trivial`) |
| `lcp.scheme` | 4D act number of the box of side `L₁`: for **every** choice of flux time limits `h_k` (time extent `T → ∞` of the centre-odd Polyakov correlation of SU(2) Wilson on `ℤ/Tℤ × (ℤ/ℓ_kℤ)³`), `ℓ_k · fluxRate h_k → z⋆ > 0` (cycle 2: replaces the transfer-operator `actZ`) | P6.7 (renormalisation condition), contains P1.7 (strict `E_e > 0`, eventually) | route B only | not checked |
| `nontrivial` | some slab correlation at some `τ > 0` has all continuum limit points `≥ c > 0` in modulus | P6.2 (non-triviality half) | no (passed to the conclusion) | fails (on paper: product measure, zero covariance; not formalised) |
| `crossover`, route A torus form: `BlockedTorusRoute` | a reflection-respecting blocking family onto `L₁` cells, `λ > 0`, `H1Local ∧ LimitDprime ∧ ObsTransferPhys` | P3.2/P3.3, P4.1′ (D′ at `L₁`), P5.2 in physical size | yes | expected to hold (infinite gap); not checked in Lean |
| `crossover`, route A slab form: `BlockedSlabRoute` | the same with `ObsTransfer` (coarse support counted against fine links) | P3.2/P3.3, P4.1′, P5.2 | yes | expected to hold; not checked in Lean |
| `crossover`, route B: `ConjW` | for all flux time limits `h, h'` of boxes `2^jℓ_k`, `2^{j+1}ℓ_k`: `(1+δ)² actRate(h) ≤ actRate(h')`, all levels and box sizes | P4.2 (doubling form; P4.3–P4.5 inside it) | yes | not checked |
| `crossover`, route B: `SectorTransfer` | `FluxGrowth T → MassGap T` | P5.1 | yes | holds (consequent true) |

`not_trivial` (proved, re-checked after cycle 2 as `not_trivial_top`): the family with `β_k = 0` at every level, i.e. product Haar
measure, the zero potential at every scale, does not satisfy `OpenPieces`; more generally every family with bounded bare coupling
(strong coupling included) fails `lcp.running` (`not_onLCP_of_bounded`). Pure noise satisfies every decay-type statement (it has an
infinite gap), so the identification with Yang–Mills is carried by P6.7 and P6.2, which are therefore fields.

Numbering: the Lean docstrings call the line of constant physics P6.6 (blueprint version 1); blueprint version 2 numbers it P6.7
(tuning), P6.6 being the Wightman reconstruction and P6.8 the fields. This file uses version 2.

Consistency: only `lcp.resolution` + `lcp.running` have a proved witness (`bareRunning_witness`). No witness is given for
`lcp.scheme`, `NonTrivial` or any crossover option. Flux time limits exist (`exists_fluxLimitSU2`), so the "for every limit"
quantifiers of `lcp.scheme` and `ConjW` are never empty. Joint consistency of all fields is the open problem itself.

## The routes are joined by a disjunction

* **Route A, torus form** (preferred; `ProofPhase.Torus.torusDecayLoc_of_blockedRoute`, cycle 2): `H1Local ∧ LimitDprime ∧
  ObsTransferPhys ⇒ TorusDecayLoc T.toV` (one physical rate `min(λ/(4L₁), m)`, one constant per slab thickness and physical extent,
  independent of level, volume and fine-link count), then `bothOrdersLoc_of_torusDecayLoc` gives `MassGapLoc ∧ MassGapMFLoc`.
* **Route A, slab form** (`ProofPhase.RouteA.slabDecay_of_blockedRoute`, workstream 1; an independent proof is
  `ProofPhase.Quantum.slabDecay_of_blockedRoute`, workstream 3): `H1Local ∧ LimitDprime ∧ ObsTransfer ⇒ SlabDecay`, then
  `assembly_routeA` (Theorem C on the torus removes the level constant; volume limit; continuum limit) gives `MassGap ∧ LatticeGap`.
  `SlabDecay` itself is no longer a field: its other sufficient condition, fine-level D′ (`slabDecay_of_uniformGDS`), is likely false.
* **Route B** (`assembly_routeB : OnLCP T → ConjW T → SectorTransfer T → MassGap T ∧ LimitRP T`). Lean content: only
  `fluxGrowth_of_conjW` (W + the renormalisation condition give geometric growth of the 4D act number, uniformly in the level and over
  all flux time limits; `OnLCP.eventually_actRate`). **P5.1 carries the whole vacuum-sector content**; workstream 2 found that it lands
  on route A (`RouteB/Sector.lean`). Route B shares no Lean with route A.
* The top-level theorem takes `BlockedTorusRoute T ∨ BlockedSlabRoute T ∨ (ConjW T ∧ SectorTransfer T)` and proves the common
  conclusion `MassGapLoc` by cases.

## The transfer hypothesis: three forms compared (cycle 2)

| form | coarse support / oscillation of the approximant | observables covered | gives |
|---|---|---|---|
| `ObsTransfer` | `≤ K (#fine links + 1)(1 + D/L₁)⁴` coarse links | all | `SlabDecay` (constant grows with the level) |
| `ObsTransferU` (workstream 1) | oscillation sum `≤ 2K_V (1 + D/L₁)⁴`, uniform in the level | every fine-link bound `V` | `TorusDecay` (all observables) |
| `ObsTransferCell` (literal "counted in L₁ cells") | `≤ K (1 + R/L₁)⁴ (1 + D/L₁)⁴` coarse links, one `K` | physical extent `≤ R` | via `ObsTransferPhys` |
| **`ObsTransferPhys`** (in `OpenPieces`) | oscillation sum `≤ 2K_R (1 + D/L₁)⁴`, uniform in the level | physical extent `≤ R` | `TorusDecayLoc`, both orders |

Proved: `ObsTransferU ⇒ ObsTransferPhys` (`obsTransferPhys_of_U`, via the counting lemma `card_le_of_siteDist`: a link set of `ℓ^∞`
diameter `≤ r` has at most `4(2r+1)⁴` elements) and `ObsTransferCell ⇒ ObsTransferPhys` (`obsTransferPhys_of_cell`); `TorusDecay ⇒
TorusDecayLoc` (`torusDecayLoc_of_torusDecay`). `ObsTransfer` and `ObsTransferPhys` are incomparable. `ObsTransferPhys` is the weakest
hypothesis known to give a level-uniform constant, and it asks nothing of observables spread over the torus (workstream 1's hard case
for `ObsTransferU`).

## Proved here, no longer open (what already follows)

* `limitRP`: reflection positivity of every continuum limit point, for bounded measurable functions of the closed positive half
  (the positivity half of P6.3), from lattice RP at every level and closedness.
* `blocked_wilson_rp`: RP of every blocked layer for every reflection-respecting blocking (P1.6 as a property of the blocking).
* `spectral_gap_of_decay`: the spectral reading of the decay.
* The blocked route's last link (law of total covariance plus slab geometry), twice (P7.4), and its torus form (cycle 2).
* The flux energy as a property of the 4D measure (`fluxEnergy_props`, workstream 2), now the one used by `OnLCP` and `ConjW`.
* Time-translation invariance at every level is in `OneScale.TimeShift` (`integral_tShift`); the Hankel identity is proved there
  (`hankel_identity`, `hankel_corr`), so the header of `OneScale/CorollaryB.lean` (lines 26-30, "not formal") is stale.

## Missing or mis-stated pieces found

1. **P6.4 (Euclidean invariance) cannot be stated about the current objects**: rotations act on continuum fields, the lattice has only
   the hypercubic group, and a hypercubically invariant lattice observable can contain spin-4 parts, so "limit two-point functions are
   O(4) invariant" is false as a statement about lattice observables. It needs a new object first: renormalised local gauge-invariant
   fields as distributions with the OS regularity bound (P6.8). Not a field; the conclusion does not claim it.
2. **P6.6 (OS reconstruction, Wightman)** needs the limit as a state on a field algebra (P6.8) before it is "known"; `MassGap` and
   `MassGapLoc` are equivalent to the spectral gap only through it.
3. **Uniqueness of the limit (half of P6.2)** cannot be stated for arbitrary observable families (`SlabObs` lets `F` change with the
   level); it needs "the same observable at every level", i.e. P6.8 again. Only non-triviality is a field.
4. **The infinite-volume limit as its own piece**: existence and uniqueness of the infinite-volume state are not addressed. The order of
   limits is no longer missing for the torus route: `MassGapMFLoc` is the opposite order (cycle 2).
5. **A good blocking** is constructed (`ProofPhase.RouteA.Blocking`, `goodBlocking_rp`); its non-trivial limit at fixed `L₁` is power
   counting plus a one-loop check (paper).
6. **The flux energy** (cycle 2, closed for the assembly): `OnLCP.scheme` and `ConjW` now use the decay rate of the centre-odd
   Polyakov correlation of the 4D measure on anisotropic tori (`IsFluxLimitSU2`, `actRate`), so no transfer operator, Gauss-law
   projection or `Z = tr(P_G Tⁿ)` is needed. Uniqueness of the time limit is not proved (Perron–Frobenius for the finite-box transfer
   matrix, standard), so both are stated for every time limit; the old `fluxE`/`actZ` remain in `Objects.lean`, unused. The per-move
   form of W (anisotropic spatial boxes) is statable with `RouteB.Chain` but not yet in the assembly.
7. **Gauge group**: everything is SU(2); the Clay problem asks for every compact simple G. The generic objects (`wilsonMeasure`,
   `GaugeInvariant`, `RPBlocking`, `corr_le_of_decay`) are stated for any compact group with a continuous unitary representation;
   the line of constant physics, the scheme and the blocked route are SU(2)-specific.
8. **P4.1 as written in the blueprint is stronger than the chain consumes**: the assembly's route A asks D′ at `L₁` for the limit
   potentials (`LimitDprime`), not at the fine level; fine-level D′ is a sufficient condition only.
9. **P4.6 and P4.7** are not on the critical path of either assembly; P4.7's assumption (U) is false as literally stated.
10. **P1.7** is absorbed into `lcp.scheme` (`z⋆ > 0` gives `fluxRate > 0` eventually, for every flux time limit).
11. **Observables**: the conclusion is about bounded slab observables; the bridge to unbounded local fields (P6.12) is open.

## Build

```
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c2c-torus/setup.sh
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c2c-torus/build.sh ProofPhase.Torus.Top
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c2c-torus/axioms.sh
```

(`axioms-asm.sh` in this folder imports only `ProofPhase.Assembly`; since `yang_mills_assembly` moved to `ProofPhase.Torus.Top`, its
first line no longer resolves. Use `c2c-torus/axioms.sh`.)
