# Proof blueprint, version 4 (draft by the c4-fable session, 2026-11-22)

A proposal, not the map of record: `../../PROOF-BLUEPRINT.md` is unchanged. Reasons and file references for every change are
in `REVIEW.md` next to this file. Statuses as in version 2 (**Lean**, **Lean (definitional)**, **paper**, **known**,
**external**, **numerical**, **open**), plus **proposed** for statements written here and not yet in Lean. Verdict marks
CONFIRMED / LIKELY / SPECULATIVE as in the review.

---

## 0. The map in plain words

The Clay statement for SU(2) splits into three layers, and only one of them is the Millennium problem.

* **ID (identification and existence).** The lattice theories are Yang-Mills on a line of constant physics, the limit exists,
  is reflection positive, is not noise, and carries fields. Mostly external (the OpenAI construction) plus our bridge.
* **UV (from the lattice spacing to a weak-coupling scale L_*).** Every fine observable can be traded for an observable of
  the L_* block field, with errors that decay at the block scale, uniformly in the lattice spacing. Perturbative in kind
  (asymptotic freedom keeps every scale below L_* weakly coupled); large, of the kind constructive field theory has done.
* **IR (one statement).** The lattice theory seen at L_* has exponentially decaying correlations of block observables,
  uniformly in the volume and stably under the small changes of the action that UV leaves open. This is the lattice mass gap
  at one intermediate coupling. It is of gap strength, nobody can prove it beyond strong coupling, and every route in this
  project ends at it.

Version 2/3 cut the proof at L1 = 2.8/sqrt(sigma) with a lossy block variable and a Dobrushin condition there. That put a
second non-perturbative input (Lemma X, `CondMassAnn` at order-one coupling) next to the Dobrushin condition, and at that L1
the second input is the gap (review 2.2). Version 4 cuts at L_*, where the transfer is ultraviolet, and keeps everything
between L_* and infinity as **one** hypothesis with several candidate proofs. The Dobrushin condition at L1 becomes
strategy (a) for IR instead of the spine.

The owner's DMP readings give a second, finite-volume shape for the same three layers (section 6). It does not remove IR. It
states IR better and shrinks UV, and I recommend carrying it as the co-main line.

```
                 ID                          UV(L_*)                              IR(L_*)
   OnLCP', NonTrivial, limit RP   +   ObsTransferPhysTW at L_*      +      BlockGapUnifW at L_*
   existence, fields (external)       (Lemma UV; BIJ-type)                 (the gap of one lattice theory)
                                                                             |
                 strategies for IR:  (a) lossy block to L1 + W1 Dobrushin + Lemma X   [versions 2, 3]
                                     (b) lossless cells of size L1, Dobrushin-Shlosman on cells
                                     (c) Dobrushin with rare defects (annealed), for (a) or (b)
                                     (d) finite volume: two act numbers and a doubling law   [DMP-native]
                                     (e) Langevin / log-Sobolev on the torus
```

---

## 1. What is proved (the spine; unchanged)

| piece | statement | status |
|---|---|---|
| objects | SU(2) Wilson measure on 4D tori along a tuning; slab observables; both orders of limits | Lean (`Objects.lean`, `Torus/Local.lean`) |
| positivity | reflection positivity at every level, of every blocked layer of a reflection-respecting blocking, and of every limit point | Lean (`limitRP`, `blocked_wilson_rp`, `goodBlocking_rp`) |
| the cut | **`BlockGapUnifW T B λ` (λ > 0) ∧ `ObsTransferPhysTW T B` ⇒ `TorusDecayLoc`** ⇒ `MassGapLoc ∧ MassGapMFLoc` | Lean (`V3.torusDecayLoc_of_blockGapUnifW`, `Torus.bothOrdersLoc_of_torusDecayLoc`) |
| bookkeeping of conditioning | total covariance, tower, two-stage split, information bound | Lean (`UV/Split.lean`) |
| Dobrushin machinery | sup form with exponential weights; W1 form, finite range; openness; two-type; cells | Lean (`R3/`, `Certified/AdjointW.lean`, `V3/CondMass.lean`) |
| Kotecky-Preiss | hard-core gas with configuration-dependent activities, volume-uniform | Lean (`Seg1/KP.lean`) |
| certified windows | single-link W1 column for two-coupling actions and for the fitted actions | certified + Lean under named hypotheses (c3c, c4d) |
| spectral reading | decay of one vector ⇒ no spectral mass below m; prefactors removed on the torus | Lean (`spectral_gap_of_decay`, Theorem C) |
| not noise | pure noise and bounded couplings fail the inputs | Lean (`not_trivial_v3`) |

---

## 2. The top theorem of version 4

Plain: the same Lean lemmas as version 3, with the unit of the tuning read as L_* and the Dobrushin condition replaced by
what it was used for.

**Proposed statement** (a few lines on existing theorems; not built):

```
theorem yang_mills_assembly_v4 {T : Tuning} (hL : OnLCP' T) (hN : NonTrivial T) (B : BlockingFamily T) {lam : ℝ}
    (hlam : 0 < lam) (hIR : BlockGapUnifW T B lam) (hUV : ObsTransferPhysTW T B) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T
```

with `T.L₁ := L_*` (a scale where the running coupling is a small fixed number) and `B` a noisy local blocking onto L_*
cells. Proof: `torusDecayLoc_of_blockGapUnifW`, `bothOrdersLoc_of_torusDecayLoc`, `limitRP`.

**Recursion lemma** (proposed, Lean, small): every version-3 input set at a larger scale L1 = 2^r L_*, stated for the L_*
theory, implies `BlockGapUnifW T B lam` at L_*. This keeps all of cycles 2 to 4 as a proved strategy for IR (it is
`twoStage_blocked` plus `torusDecayLoc_of_blockGapUnifW` applied to block observables).

What the hypotheses are, exactly:

* `BlockGapUnifW T B lam` (`V3/W1Route.lean:65`): `∃ C ≥ 0, ∃ k₀, ∀ k ≥ k₀, ∀ j`, for bounded `f` (single-link oscillations
  `vf`, depending on `A`) and Lipschitz `g` (constant `Lg`, depending on `Sg`) on the coarse torus with `linkDist ≥ R` between
  the supports: `|Cov_{T.ym k j}(f∘B, g∘B)| ≤ C (Σ_A vf) Lg e^{−lam R}`.
* `ObsTransferPhysTW T B` (`V3/W1Route.lean:156`): for gauge-invariant `|F|, |G| ≤ 1` of physical extent `≤ R` at time
  distance `≥ D`: coarse approximants `f, g` (oscillation sum `≤ 2K(1 + D/L₁)⁴`, `g` Lipschitz, supports at distance
  `≥ D/2`), `‖E[F|Φ] − f∘Φ‖₁, ‖E[G|Φ] − g∘Φ‖₁ ≤ c e^{−mD}`, and `|E[FG] − E[E[F|Φ]E[G|Φ]]| ≤ c e^{−mD}`, uniformly in
  `k ≥ k₀`, `j`.

Claim check: `BlockGapUnifW` **is** a decay statement for (block) observables of the Wilson measure. It is of gap strength
and is named as such. That is the point of the version: one input openly carries the gap; the others must not.

---

## 3. Every open input

"Gap" column: **G** = of gap strength or stronger; **N** = non-perturbative but should hold for the photon; **P** =
perturbative in kind (weak coupling at every scale involved); **B** = bookkeeping or statement repair.

### 3.1 ID

| input | statement | status, evidence | gap |
|---|---|---|---|
| `OnLCP'` (proposed; replaces `OnLCP`) | `ℓ_k → ∞`; `β_k / log ℓ_k → 11/(6π²)`; and a renormalisation condition as a two-sided bound, e.g. the segment-1 running coupling at L_* stays in `[ḡ/2, 2ḡ]` from some level on (or: the tuning is defined by it). The present `scheme` clause (convergence of `ℓ_k · fluxRate` for every choice of time limits; `Assembly.lean:96`) is stronger than anything uses | resolution and running have a witness (`bareRunning_witness`); the renormalisation condition is open and is tied to UV1 below | P (with UV1) |
| `NonTrivial T` | `Assembly.lean:109`: some slab correlation at some `τ > 0` has all continuum limit points `≥ c > 0` in modulus | open for our objects; external for the OpenAI limit (trace two-point asymptotics) | P |
| existence, Euclidean invariance, fields, reconstruction (P6.1, P6.4 to P6.9) | as blueprint version 2, P6 | external (OpenAI, statements read, proofs per the committee's audit); bridge Lean for the laws and tori; observable bridge P6.12 open | P (their construction is ultraviolet) |
| uniqueness of the limit | not needed for the gap as stated (every limit point); needed for "the" theory | open; follows from the gap on paper (sketch) | — |
| other compact simple groups | objects generic; tuning, scheme, certificates SU(2) | open | — |

### 3.2 UV(L_*)

| input | statement | status, evidence | gap |
|---|---|---|---|
| **UV1** `UVRep(L_*)` (proposed; replaces `PolymerRepW`) | for a noisy local blocking `B_*` onto L_* cells: the blocked laws have densities `exp(−S_{k,j})` with respect to Haar, and there is a random set of bad cells (a local function of the block field) with conditional probability `≤ p₀` given everything outside a fixed range, such that off the bad set `S_{k,j}` is a sum of local terms with exponential tails within `ε₀` (in a C¹ norm) of the Wilson action at a fixed `β_*`; constants independent of `k`, `j` | open. Target form of Balaban CMP 109, 116, 119, 122 (not read in full text) and of the OpenAI `Rep.eval` (`YM/RG/History.lean:166-181`, `Activities.lean:98-132`, read). The defect form needs only probability bounds on large fields, which both sources have; the vacancy-1 form of c4b needs lower bounds they do not state. Lean available: `Seg1.kotecky_preiss`, `envelopeW_of_polymerRep` for the vacancy-1 case | P |
| **UV2** `ObsTransferPhysTW T B_*` (Lemma UV at L_*) | section 2. Parts (a), (b): quasi-locality of `E[F|Φ_*]`; part (c): `CondMassAnn T B_*` (`V3/CondInputs.lean:54`) | open. Not in the literature for non-abelian fields (the abelian Higgs model in 2 to 3 dimensions is Balaban-Imbrie-Jaffe). Gaussian level: holds in time, uniformly in the resolution, for the staple kernel (c3a, numerical, checked against brute force); spatial direction defective for w = 0.5, 1. With a noisy local blocking, (a), (b) follow from conditional mixing on paper (c4a 2.2) | P at L_* (the constraint mechanism works: slow modes exist and are pinned). This is where `CondMassAnn` is honestly gap-free |
| UV3 kernel | a block kernel whose linearised symbol is bounded below on the whole coarse zone (time is enough for the route; all directions for any Dobrushin form) | open; c3a found the defect, heat-kernel-type transverse smearing proposed, untested | B/P |

### 3.3 IR(L_*)

| input | statement | status, evidence | gap |
|---|---|---|---|
| **IR** `BlockGapUnifW T B_* lam`, `lam > 0` | section 2. In words: the L_*-blocked Wilson theories have a mass gap for block observables, at a rate `lam / L_*` in physical units, with constants uniform in level and volume | **open; the core.** Proved only at strong coupling (the project's `SingleLink` window; others claim certified W1 block row sums up to beta about 0.42, unrefereed). Numerical: the lattice theory at beta 2.3 to 2.5 has a gap with a correlation length of about one lattice spacing or less | **G** (equal to the gap for block observables; with UV2 equivalent to the conclusion) |

Strategies for IR (each is a set of sufficient conditions; none is proved):

| strategy | its inputs | status, evidence | remark |
|---|---|---|---|
| (a) lossy block to L1 = 2^r L_*, Dobrushin there | `LevelDprimeW` at L1 (after repair: weighted, general support, noisy blocking); `CondMassAnn` and `ObsQuasiLocTW` for the step L_* → L1 (Lemma X) | Lean for the implications (version 3). Evidence: fitted action at L1 sqrt(sigma) = 2.80 inside the single-link W1 window for the truncations fitted (0.73, 0.76, 0.96; 0.9999 inconclusive). Lemma X: no evidence; LIKELY the gap itself at this L1 (review 2.2) | two **G/N** inputs with no small parameter each; keep as a proved reduction, not as the plan |
| (b) lossless cells | a Dobrushin-Shlosman (finite-volume, boundary-layer discounted) condition for the L_* theory on cells of side L1: the influence of a neighbouring cell's configuration on a cell's law, measured away from a boundary layer, sums to `γ < 1` | proposed (c3a's Route A′; `CellDobrushin` in `V3/CondMass.lean` is the right Lean shape, applied to the unconditioned law). One finite-volume condition; no Lemma X; no content question | **G**; the form to state IR in when a Dobrushin proof is meant |
| (c) rare defects | a Dobrushin theorem for specifications whose bad sites are dominated by a subcritical Bernoulli field (disagreement percolation) | proposed Lean module; a known kind of theorem (van den Berg-Maes; Liggett-Schonmann-Stacey for the domination) | **B** for IR (a tool), but the only form compatible with UV1 and with measured actions |
| (d) finite volume, doubling | section 6 | proposed | **G**; needs only per-volume UV |
| (e) log-Sobolev on the torus | a volume-uniform spectral gap of the Langevin dynamics of the L_* theory | SPECULATIVE; one reading | **G**; one-sided condition, no boundary conditions |

### 3.4 Statement repairs (needed before any W1 theorem can be fed; review section 1)

| repair | where | size |
|---|---|---|
| weighted W1 Theorem A; remove `D₁` from `LevelDprimeW` | `Certified/AdjointW.lean`, `V3/W1Route.lean` | Lean module, medium |
| limit and level potentials of general support with exponential weights; "eventually `≤ ε₀`" | `H1LocalLipW`, `LimitDprimeW` | Lean, medium (or delete the pair, S5) |
| noisy local `BlockingFamily` with reflection positivity | `Objects.lean`, `RouteA/Blocking.lean` | Lean, medium |
| gauge-reduced cells for `CellDobrushin` | `V3/CondMass.lean` | Lean, medium; only for strategy (b) |

---

## 4. What is gap content and what is bookkeeping

| | content |
|---|---|
| gap strength | **IR**, in whichever form. In version 3 terms at L1 = 2.8/sqrt(sigma): `CondMassAnn`/Lemma X (the glueball gap) and `LevelDprimeW` (loops of size L1 are small for every coarse boundary condition: confinement-type) together |
| perturbative but large | UV1, UV2, the renormalisation condition, existence and fields. This is real mathematics at the scale of the constructive programme; a complete proof of "ID ∧ UV ⇒ (IR ⇔ continuum gap)" would itself be a result: the continuum problem reduced to a lattice problem at one scale |
| bookkeeping, done | the cut, both orders of limits, positivity, total covariance, two-stage split, Kotecky-Preiss, openness, the certified windows as statements about given actions |
| bookkeeping, to do | section 3.4; one top theorem instead of four generations; wiring `Seg1/` and `twoStage_blocked` into the top |
| evidence only | fitted actions, content checks, act numbers |

---

## 5. Unit tests for version 4

| test | ID ∧ UV | IR |
|---|---|---|
| photon | hold (Gaussian; UV2 is the Kalman case) | fails (power law at L_*) |
| Z2 weak coupling | hold | holds (gap), implies no area law: correct for a gap-type input |
| deconfinement | no claim at any scale | IR is a torus statement about symmetric tori; no claim about boxes one block thick. Strategy (a), (b) in worst-case form fail below 1/T_c, as they must |
| mixture, Heller endpoint | UV may hold | fails (no decay; massless scalar visible at L_*) |
| Banks-Zaks | hold at every scale | fails |
| triviality | no existence claim made by us | — |
| pure noise | fails `OnLCP'` | — |
| noise-limit trap | cannot occur at L_* in UV2 (the block field is informative at weak coupling); occurs inside strategy (a) at L1 | — |

---

## 6. The DMP-native line

### 6.1 Verdict in plain words

There is a proof shape native to the DMP objects. It is different from blocking plus Dobrushin and in two respects better: its
ultraviolet half needs control in one finite box at a time, which is what the published constructive results and our own
per-volume theorem give, and its infrared half is one sentence about two numbers. It is not a shorter proof: the sentence is
a law that compares a box with the box of twice the size, which is the same two-sided cross-volume step that stopped
Tomboulis (Ito-Seiler), round 3's monotonicity attempt and round 4's Conjecture W. DMP names that step exactly (a minted
value that both halves must sign, against a standing that one half can tighten); it does not supply it.

So: not the replacement of the main line, but the recommended **statement of IR** and a co-main line, because it removes
volume-uniform locality from UV and makes the remaining law measurable.

### 6.2 The decomposition by DMP's objects

DMP's own gap is `mg_reach_existence_floor` (as inventoried in `round4-prep/DMP-SCOUT.md`): the act identity (existence times
extent equals one quantum) and a reach bound give a floor for the existence. `floor_every_layer_of_minting` (r4-minting, toy
Lean) carries it to every layer from a root and one exact step rule. Read on Yang-Mills in a periodic box of side L, in the
continuum limit at fixed L:

| DMP object | Yang-Mills object | status |
|---|---|---|
| the act number of the flux sector | `z_e(L) = E_e(L) · L` (centre flux energy; `fluxRate` in Lean) | Lean object; values on disk (about 3.6, 7.8, 12.2 at L sqrt(sigma) = 2.1, 2.8, 3.5) |
| the act number of the vacuum sector (new) | `z_0(L) = E_0(L) · L`, `E_0` the gap of the box in the centre-neutral sector | proposed; definable from the same Hankel machinery as `fluxRate` with a centre-even observable (`RouteB/FluxEnergy.lean`) |
| inward reach, tie to G0 | asymptotic freedom: in a small box both act numbers are small and computable (`z_0 ~ g(L)^{2/3}`, Luescher's small-volume expansion, recalled; `z_e` by the half-instanton, r4-conjw) | known at physics level; rigorous finite-volume ultraviolet control is the published setting (Balaban; Magnen-Rivasseau-Seneor, both unread here) |
| the existence boundary, dimension swap | `z_e = 1` near L = 1/T_c (self-dual point; `tHooft_rotation` in Lean) | numerical/heuristic |
| outward reach | `z_e` grows like `σ L²` (confinement), `z_0` grows like `m L` (the gap) | open |
| "something must run" | a scale-invariant theory has both act numbers constant; **the gap is exactly: `z_0(L)/L` stays bounded below** | definitional once `z_0` is defined in the order "spacing first" |
| the step rule (minted, two-sided) | the doubling law (below) | open; the core |
| sector transfer, "how existence is built" | a low state of the box 2L either restricts to a low state of the sub-boxes, or threads centre flux through a cut (pays `E_e(L)`), or is a long-wavelength gluonic mode (centre-neutral, colour-adjoint) | the third case is the adjoint half; the centre cannot see it (ws2's counterexample, c2b's small loops) |
| the centre through the causal round trip | the commutator term `[A_i, A_j]²` is what gives the zero-momentum gluonic modes their energy in a small box, and is absent for the photon | physics-level; this is where "−1 is a commutator" is more than a necessary condition |

**The DMP-native blueprint:**

```
  D-ID   continuum limit at fixed physical box exists (spacing first; the OpenAI order), with z_0(L), z_e(L) defined
  D-UV   in a small box the act numbers are positive and run:  z_0(L), z_e(L) as functions of g(L)   [per volume only]
  D-S    start: at one box L_0 (about 2 to 3 / sqrt(sigma)):  z_0(L_0) ≥ ζ_0  and  z_e(L_0) ≥ ζ_e
  D-T    doubling law: above the thresholds,  z_0(2L) ≥ 2 z_0(L) (1 − η(L)),  Σ_n η(2^n L_0) < ∞,  and the thresholds persist
  ⇒      E_0(2^n L_0) ≥ m > 0 for all n   ⇒   MassGapMFLoc (after a monotone interpolation in L and the observable bridge)
```

### 6.3 Where it clicks

1. **UV shrinks to one volume at a time (CONFIRMED as a structural fact).** c3d: "per volume, D′ from a level `k₀(j)`; the
   whole gap is volume-uniformity". On this line volume-uniform quasi-locality (`EnvelopeW`, `H1LocalLipW`, the exact-cover
   problem, `NearStable`) is never asked. `Quantum/PerVolume.lean` and Lemma T are the right tools and become used again.
2. **The order of limits is the one existence is proved in** (spacing first at fixed volume: `MassGapMFLoc`, the OpenAI order).
3. **The two halves of D′ are the two act numbers (LIKELY).** c2a 4(c): the centre half is controlled by `e^{−σ L1²}`, i.e.
   by `z_e(L1)`; the adjoint half by `e^{−m L1/4}`, i.e. by `z_0(L1)`. The halves criterion `γ_A + γ_C < 1` at L1 is a
   threshold statement in `(z_0, z_e)`, and the Dobrushin route (strategy (a) or (b)) is one proposed proof of D-T above
   those thresholds. The measured point has `z_e` about 7.8 and `z_0` about 10.
4. **The sector transfer gets its exact form.** ws2 showed flux growth alone cannot give the gap. The doubling form says what
   must be added: the vacuum act number at the same scale. Conjecture S's break ("small flux does not pay the confinement
   price") is the statement that `z_0` is a second, independent number.
5. **A conformality gauge with two needles** (extends READING click C5): photon `z_e = 2πα`, `z_0 = 2π` frozen; Banks-Zaks both
   frozen at the fixed point; Z2 deconfined `z_e → 0`, `z_0` linear; Yang-Mills both growing. All unit tests become readings
   of two curves.
6. **One-sided against two-sided, in DMP's own words.** Reflection positivity, decimation and chessboard inequalities are
   standings (one half can tighten them): they give monotonicity, never conservation (`standing_can_drop_to_zero`,
   `monotone_not_enough`). D-T needs a minted rule. That is the precise content of "the one-sided step every route meets".

### 6.4 Where it is only a relabelling

* D-T is IR. Given a gap, D-T holds with exponentially small `η` (finite-size corrections of Luescher type, recalled); without
  one, nothing known gives it. No universal threshold in `z_0` alone can exist: a free massless field has `z_0 = 2π` at every
  L, so D-T must use dynamics (no infrared fixed point for pure Yang-Mills, P4.6) or both act numbers and a growth margin.
* "The act is conserved per layer" stays definitional (round-4 review); the hosting gives per-level existence only (r3-dmp).
* The act identity as an equality is true for the photon only. For Yang-Mills it is an inequality whose content is D-T.
* D-S is a non-perturbative statement in one finite box. It is at least a finite problem, and it is the one place where the
  bootstrap (`../../../bootstrap/`) or a certified computation could in principle speak; at present far out of reach.

### 6.5 What to do with it

Define `z_0` in Lean next to `fluxRate`; state D-T and D-S as named hypotheses and prove (Lean, small)
`D-ID ∧ D-S ∧ D-T ⇒ E_0(2^n L_0) ≥ m`; state "IR ⇐ D-T ∧ D-S ∧ per-volume UV" on paper and find out whether the per-volume
theorem really suffices. Measure `z_0(L)` and `z_e(L)` together (torus spectroscopy at beta 2.3 to 2.5; standard, and the
flux part is on disk). This is the measurement the act-number queue should become.

---

## 7. The plan, by value for the full proof

| # | step | establishes | kind and size |
|---|---|---|---|
| 1 | **Re-cut the assembly at L_***: `yang_mills_assembly_v4` (section 2), the recursion lemma, `OnLCP'`; retire Route B and the sup family from the top | one top theorem with exactly one input of gap strength, named as such; cycles 2 to 4 kept as strategy (a) | Lean, one small module |
| 2 | **Measure the content at L1 as a number**: explained variance `Var(E[F|Φ])/Var(F)` of smeared glueball-type observables for b = 2, 4, 8 at beta 2.3 to 2.5, by conditional replicas (c4c's instrument) or a regression lower bound | decides review 2.2: whether Lemma X at L1 can be anything but the gap; decides whether strategy (a) is kept or replaced by (b) | GPU pre-registration; new code (conditional sampling); a regression lower bound from saved configurations first, CPU |
| 3 | **Make the W1 inputs satisfiable**: weighted W1 Theorem A, general-support potentials, noisy local blocking family | the preferred route's hypotheses become statements the true theory can meet; parts (a), (b) and the envelope reduce to conditional mixing | Lean, two to three medium modules |
| 4 | **Fix the segment-1 supplier**: read the OpenAI `Rep` statements against UV1 in defect form; read Balaban CMP 109 section 1 and CMP 122 II in full text; write UV1 exactly | UV1 as a citation plus a translation lemma, or the precise missing bound | reading, one to two sessions; then a small Lean lemma |
| 5 | **Dobrushin with rare defects** (strategy (c)) | one theorem in which published large-field bounds, fitted actions and the route meet; ends the sup-against-annealed mismatch | Lean, large module |
| 6 | **The DMP-native line**: `z_0` in Lean, D-S and D-T as hypotheses, the doubling theorem; joint measurement of `z_0`, `z_e`; photon gate by the exact formula (owner's decision) | IR in its cleanest form; a finite-volume route whose UV half is published in kind | Lean small; GPU pre-registration (mostly existing code) |
| 7 | Certified Gaussian Lemma UV for a kernel with a symbol bounded below on the whole zone | the photon instance of UV2, and the kernel (UV3) | certified computation, CPU, small |
| 8 | Strategy (b) stated in Lean (`CellDobrushin` for the unconditioned L_* law ⇒ `BlockGapUnifW`) | the honest Dobrushin form of IR, without Lemma X | Lean, medium |
| 9 | Lemma UV for SU(2) (conditional expansion with two observables) | UV2 | paper-sized or more; only after 1 to 5 |
| 10 | One reading on log-Sobolev along the Polchinski flow for lattice gauge measures | whether strategy (e) is a real alternative form of IR | reading |

What this plan does not contain: a step that proves IR. I do not see one in the map, in the alternatives, or in the DMP
readings, and the blueprint should say so on its first page. What the project can reach is a machine-checked theorem
"ID ∧ UV ∧ IR ⇒ the gap in both orders of limits" with IR being exactly the lattice gap at one scale, the published-kind
inputs pinned to sources, and pre-registered evidence for IR in the forms (b) and (d).
