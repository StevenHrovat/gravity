# Proof phase, cycle 3, workstream D (c3d-h1): `H1Local`, the quantum half at L₁ uniform in the lattice (2026-11-22)

Brief: state exactly what remains of `H1Local` after cycle 1's per-volume theorem; locate where it breaks (large fields,
the running through the crossover, or both); prove whatever reduction is honest. Rules: `../../attempts/RULES.md` (proof
phase section, claim discipline, all unit tests incl. Banks–Zaks and triviality). Map: `../../PROOF-BLUEPRINT.md` (P3, P4.1′,
P7).

Lean: two new files under `../../../formal/ProofPhase/H1/` (`Split.lean`, `Level.lean`), built in `~/formal-c3d` (Lean
4.34.0, Mathlib v4.34.0) against the current `Assembly.lean`, `Torus/`, `RouteA/`. Both build; `axioms.sh` prints
`propext, Classical.choice, Quot.sound` for all 15 headline theorems; no `sorry`, no `native_decide`, no new axioms.
Nothing outside `ProofPhase/H1/` and this folder was edited.

```
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c3d-h1/setup.sh
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c3d-h1/build.sh ProofPhase.H1.Level
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c3d-h1/axioms.sh
```

Marks: **S** substantive, **D** definitional or elementary. "YM" names what is Yang–Mills-specific in a hypothesis.

## 0. Result in one paragraph

`H1Local` is exactly four things (Lean, `h1Local_iff_split`): a Gibbs **representation** of every blocked law, and for the
sup distances `η` of the coarse potentials from the limit's: **bounded pair sums** at each level, **small tails** and
**uniformly vanishing near parts**, all uniform in the volume. Cycle 1's per-volume theorem (with a noisy blocking) supplies
the representation and convergence in each volume separately; everything uniform in the volume is missing. Lean proves
`H1Local` from four named hypotheses on the blocked SU(2) Wilson laws (`h1Local_of_quasiLocal`): the representation, a
**uniform envelope** (quasi-locality of the effective action at L₁, uniform in level and volume), **per-volume
convergence**, and **volume stabilisation** of the near parts. The second finding is structural and also in Lean: the route
uses `H1Local ∧ LimitDprime` **only** through D′ for the blocked lattice laws themselves (`LevelDprime`), so the
convergence half of `H1Local` (a limit effective action at L₁, its existence and uniqueness) is **not needed for the gap**
(`yang_mills_assembly_level`: `OnLCP ∧ NonTrivial ∧ LevelDprime ∧ ObsTransferPhys ⇒` the gap in both orders of limits).
That is not a discharge: `LevelDprime` absorbs `H1Local`'s hard part (depth-uniform locality at coupling of order one)
together with `LimitDprime`. **Where it breaks: (c), both, and in the same place.** Large fields are harmless per volume
(compact group plus noise) and harmless at weak coupling (Balaban's suppression); the uniform envelope is cheap while the
coupling is small and has no small parameter in the last, fixed number of blocking steps where α_s grows to order one.
There the large-field problem and the crossover are one problem: a cluster expansion of the fine field conditioned on the
block field at intermediate coupling.

## 1. The exact gap between per-volume and lattice-uniform

### 1.1 What `H1Local` says, clause by clause (Lean, `Split.lean`)

`H1Local T B λ Vk Vinf` (Assembly) = (R) `∀ k j, blockedLaw = gibbsMeasure haar (V_{k,j})` ∧ (P) every `V_{k,j}` is a
bounded local potential ∧ `LocalConvergenceW`: there are `η_k(x) ≥ sup|V_{k,j}(x) − V_{∞,j}(x)|` with weighted pair sums
`P_{k,j}(z) = ∑_{i≠z} (∑_{x ∋ i,z} η_k(x)) e^{λ d(z,i)} ≤ ε_k → 0`, one `ε` for all volumes.

Split each pair sum by factor diameter (`linkDiam`, the `ℓ^∞` diameter in coarse units, `linkDist_le_linkDiam`) into the
near part (diameter `≤ r`) and the far part (diameter `> r`).

| Lean | exact statement | mark |
|---|---|---|
| `pairSum_eq_near_add_far` | `P = near_r + far_r` | D |
| `exists_seq_of_unif` | a family bounded at each index and eventually uniformly `≤ ε` is dominated by one null sequence | D |
| `localConvergenceW_iff` | `LocalConvergenceW ↔ ∃ η ≥ 0, η ≥ |ΔV|, PairSumBdd ∧ TailSmall ∧ NearUniform` (any family of finite Gibbs systems) | D |
| **`h1Local_iff_split`** | `H1Local T B λ Vk Vinf ↔ (R) ∧ (P) ∧ ∃ η ≥ |ΔV|, PairSumBdd ∧ TailSmall ∧ NearUniform` on the coarse SU(2) tori | D |

Here `PairSumBdd`: at each level, `sup_{j,z} P_{k,j}(z) < ∞`; `TailSmall`: for `ε > 0` there are `r`, `K` with
`far_r ≤ ε` for `k ≥ K`, every volume and site; `NearUniform`: for every `r`, `near_r → 0` uniformly in volume and site.

### 1.2 What the per-volume theorem gives, and what it does not

Cycle 1 (`Quantum/PerVolume.lean`, `Attempts/R3/WpNoise.lean`) works with a **noisy** blocking (`l1Law`). Per volume `j` it
gives: a positive bounded density of the L₁ law (so (R) and (P) hold with one global factor `V(univ) = log ρ`), and
uniform convergence of the log-densities along a subsequence of every subsequence (noise lemma + Prokhorov), hence along the
full sequence if the mesh limit point is unique.

Per volume, (R) + convergence of `log ρ_{k,j}` in sup norm already gives `LocalConvergenceW` *in that volume* (paper, D): put
the difference into the global factor; its pair sums are `≤ |Λ_j| e^{λ diam_j} sup|Δ log ρ|`, finite and `→ 0`. The same
computation gives the **per-volume form of `LevelDprime`** from H2-all (paper, S elementary): every mesh limit point is a D′
Gibbs measure, the level potential `V_∞ + Δ_k·1_{univ}` changes the weighted oscillation sums by at most
`2|Λ_j| e^{λ diam_j} sup|Δ_k|`, so for `k ≥ k₀(j)` the level satisfies D′ with `(1+γ)/2`; the subsequence principle removes
the subsequence. **The whole difference to the lattice-uniform statement is that `k₀(j)` grows like the volume** (the factor
`|Λ_j| e^{λ diam_j}`): a global factor is not local. Making `k₀` volume-independent needs the difference `Δ_k` written as a
sum of local terms with summable, volume-uniform tails — which is `H1Local`'s tail clause.

### 1.3 The extra properties, as named hypotheses on the real objects (Lean)

| Lean | statement | mark |
|---|---|---|
| `EnvelopeW csupp crad λ' h` | **uniform quasi-locality**: `∃ M, ∀ j z, ∑_{i≠z} ∑_{x ∋ i,z} h_j(x) e^{λ' diam x} ≤ M` | named hypothesis (open at L₁) |
| `tailSmall_of_envelope` | `0 ≤ η ≤ h`, `EnvelopeW` at `λ' > λ ≥ 0` ⇒ `far_r ≤ M e^{-(λ'−λ) r}`, hence `TailSmall` | S (elementary) |
| `pairSumBdd_of_envelope` | the same ⇒ `PairSumBdd` | S (elementary) |
| `nearUniform_of_stable` | per-volume convergence `η_k(x) → 0` for every volume and factor, and `near_r ≤ b_k + ζ_j` with `b → 0`, `ζ → 0` along the cofinite filter ⇒ `NearUniform` (Moore–Osgood step) | S (elementary) |
| `NearStable λ Vk Vinf` | **volume stabilisation**: for every `r`, the near parts of `supDist(V_{k,j}, V_{∞,j})` are `≤ b_k + ζ_j` | named hypothesis (open) |
| **`h1Local_of_quasiLocal`** | (R) ∧ (P) ∧ `|V_{k,j}|, |V_{∞,j}| ≤ h_j` with `EnvelopeW` at `λ' > λ` ∧ per-volume sup convergence of every coarse potential term ∧ `NearStable` ⇒ `H1Local T B λ Vk Vinf` | S (elementary given the hypotheses); YM: all hypotheses are about the blocked SU(2) Wilson laws along `T` |
| `flatW_far_le` | `FlatCriterionW d λ S γ`, `S ≥ 0`, `λ' ≤ λ` ⇒ far pair-oscillation sums (distance `> r`) at rate `λ'` are `≤ γ e^{-(λ−λ') r}` | D |

So, precisely: **per-volume theorem + `EnvelopeW` (λ' > λ) + `NearStable` + full-sequence per-volume convergence (uniqueness
of the mesh limit at fixed volume) + a blocking with noise ⇒ `H1Local`**. Of these, uniqueness and `NearStable` are
convergence statements; `EnvelopeW` is the locality statement.

### 1.4 Which known result supplies which part

| part | supplied by | status |
|---|---|---|
| (R), (P): blocked law has a bounded positive log-density | one noisy blocking step (`WpNoise`, `noise_uniform`); OpenAI's kernel is noisy (frames + heat-kernel noise, reading) | free with noise. **Not** available for the assembly's `BlockingFamily`, which is deterministic (`RPBlocking`): for the deterministic good blocking (`projSU2` of smeared paths) the image density is not known to be bounded above and below (critical points of the projection; paper, open). Proposal in §5 |
| per-volume convergence, subsequential | compactness (Lean, cycle 1) | done |
| per-volume convergence, full sequence | uniqueness of the mesh limit at fixed volume: OpenAI `Winter.convergence` at their unit (reading, conditional on the `Rep.eval` continuity check, `r3-wp` §2.2), then Lemma T per volume to L₁ (Lean) | reduced to a reading check; **not needed** for the gap (§2) |
| `EnvelopeW` at weak-coupling scales | Balaban's small-field effective actions (quasi-local, exponential tails; CMP 109, 116, 119) with large-field regions suppressed by `e^{-c p(g)²}` (CMP 122); OpenAI's E/K budgets with `exp(κ·cover)` weights, **uniform in the volume** | plausible (paper): an envelope needs only **upper** bounds, which both have; passing from polymer activities to log-potentials is a Kotecký–Preiss expansion, convergent because the activities are small there. Not a published statement for the full log-density |
| `EnvelopeW` at L₁ | nobody | **open: this is the crossover** (§2) |
| `NearStable` | follows from `EnvelopeW` plus an infinite-volume effective action at L₁ (finite-size corrections `≤ e^{-c j}` by the tails) | open; the infinite-volume effective action at L₁ is again a uniqueness statement |
| lower bounds on large-field activities (ratio bounds) | nobody (`r3-wp` §2.2) | needed only for **volume-uniform convergence** of the near parts, which the gap does not need |

Correction to the record (`r3-wp` §2.2 row "W_p, volume-uniform"): ratio bounds are needed for uniform *convergence*, not
for uniform *locality*. The envelope uses upper bounds only.

## 2. The route does not need the limit: `LevelDprime` (Lean, `Level.lean`)

`blockGap_of_blockedRoute` (Assembly) uses `H1Local ∧ LimitDprime` only through `Attempts.R3.levelFlat_of_local`: from some
level on, the **level** potentials satisfy D′. The limit is a vehicle.

| Lean | statement | mark |
|---|---|---|
| `LevelDprime T B λ` | `∃ γ ∈ [0,1), ∃ k₀, ∀ k ≥ k₀, ∀ j, ∃ V`: `blockedLaw T B k j = gibbsMeasure haar V`, `V` bounded local, pair oscillations `S` with `FlatCriterionW linkDist λ S γ` | named hypothesis (open); YM: blocked SU(2) Wilson laws along `T` |
| `levelDprime_of_h1Local` | `H1Local ∧ LimitDprime ⇒ LevelDprime` (with `(1+γ)/2`) | D |
| `BlockGapUnif T B λ` | block covariances `≤ (1−γ)⁻¹ (∑ v_f) L_g e^{-λR}` for all `k ≥ k₀`, all volumes | definitional interface (a block-level gap statement) |
| `blockGapUnif_of_levelDprime` | `LevelDprime ⇒ BlockGapUnif` (Theorem A with weights on each blocked law) | S |
| `torusDecayLoc_of_blockGapUnif` | `BlockGapUnif (λ > 0) ∧ ObsTransferPhys ⇒ TorusDecayLoc` (cycle 2's proof, block gap as input) | S |
| `levelTorusRoute_of_blockedTorusRoute` | `BlockedTorusRoute ⇒ LevelTorusRoute` | D |
| **`yang_mills_assembly_level`** | `OnLCP T → NonTrivial T → LevelTorusRoute T → TorusDecayLoc ∧ MassGapLoc ∧ MassGapMFLoc ∧ LimitRP ∧ NonTrivial` | S (assembled; one theorem) |

**Strength.** `LevelDprime` is weaker than or equal to `H1Local ∧ LimitDprime` (Lean), and strictly weaker for fixed potentials in the abstract
setting (paper: two D′ theories alternating with the level satisfy `LevelDprime` and have no local limit; on the real objects
the existential choice of representation makes strictness harder to state, not checked). It is stronger than
`BlockGapUnif` (worst-case Dobrushin) and stronger than the gap; false below `1/T_c` like every D′ at L₁. It is equal in
difficulty to "`LimitDprime` plus depth-uniform closeness of the levels to the limit in the D′ norm": it **contains**
`H1Local`'s hard part. What it drops is only the convergence of the effective action (`NearUniform`, uniqueness): not needed.

**Which form the crossover needs.** The route needs `BlockGapUnif`. `LevelDprime` is the Dobrushin way to it. `EnvelopeW`
(uniform locality of the effective action) is **weaker** than `LevelDprime` in its oscillation part (`flatW_far_le`: D′ at
rate λ contains uniform tails at every λ' < λ), and **strictly** weaker: it holds for the photon and for Banks–Zaks theories
(§4), where `LevelDprime` fails. `NearStable` and full-sequence convergence are **incomparable** with `LevelDprime` and not
needed. So the honest summary: `H1Local` = (needed, weaker than the crossover's D′ and implied by it) uniform locality +
(not needed) convergence; after `yang_mills_assembly_level`, `H1Local` is no longer an open input of the torus route.

## 3. Where it really breaks: (a), (b) or (c)

Write the blocking from `a_k` to `L₁` as two segments. Choose a scale `L_*` with running coupling `g(L_*) = ḡ` small (fixed,
physical). Segment 1 is `a_k → L_*`, about `log₂(L_*/a_k)` steps, growing with `k`; segment 2 is `L_* → L₁`,
`n = log₂(L₁/L_*)` steps, **fixed, independent of `k`**.

* **Representation (R).** Per `(k, j)` and finite: no large-field problem on a compact group once one step is noisy. Not (a),
  not (b); a typing issue (deterministic `BlockingFamily`).
* **Segment 1, `EnvelopeW` at `L_*` uniform in `k` and `j`.** Large fields exist but cost `e^{-c p(g)²}` per large-field cube
  (Balaban's R operation, Dimock II); the conditional fine field given the block field is a massive Gaussian at the block scale
  up to small corrections (Balaban's background-field propagators). Locality with upper bounds only: plausible from the
  literature, not published in this form (paper). **(a) is handled here by small g.** Not (b).
* **Segment 2, from `L_*` to `L₁`, a fixed number of steps.** Quasi-locality of the effective action after the RG map at
  intermediate coupling requires the fine field **conditioned on the coarse field** to be in a uniqueness regime, uniformly in
  the volume (the classical condition for an RG map to keep Gibbsianness; van Enter–Fernández–Sokal give the failures). At
  α_s of order one there is no small parameter: large fields are not rare (every plaquette is "large" in Balaban's sense when
  g ~ 1), and the compact group bounds each factor but not the decay. **Here (a) and (b) are the same obstruction**: no cluster
  expansion of the conditioned system at intermediate coupling. Verdict: **(c)**, located in segment 2, with (a) and (b)
  coinciding there.
* **Convergence (`NearUniform`, uniqueness).** Needs ratio bounds on large-field activities for volume-uniform convergence
  (open everywhere, segment 1 included). Not needed for the gap (§2).

**The good blocking.** Spatial smearing within time slices plus temporal decimation (P1.8) does not change the picture in
kind: it removes the linear self-energy divergence, so the block variable keeps the slow modes and the conditional fine field
is massive at the block scale in the free (photon) limit — the precondition for segment 1's locality and the mechanism c3a-uv
tests numerically (`../c3a-uv/PREREG.md`). Temporal decimation keeps reflection positivity at every layer but leaves the
time-direction fluctuations between kept slices unsmoothed; for the conditioned system that is a transfer-matrix (slab)
problem, which in segment 2 is again strongly coupled. Plain decimation would be worse: its block variable is noise-dominated
(ws1 one-loop check), the effective action converges to the trivial one and `LevelDprime` becomes cheap for the wrong reason
(the noise-limit trap, P4.1″).

**What asymptotic freedom (b₀ > 0) must do here.** (1) Make segment 1 uniform in depth: along `OnLCP` the bare coupling goes
to zero like `1/(slope·log ℓ_k)` and the coupling at every scale `≤ L_*` stays `≤ ḡ` for all `k`; so the number of strongly
coupled steps is the fixed `n`, independent of the cutoff. Without it there is no depth-uniform statement at all. (2) Fix the
physics of segment 2: `OnLCP(iii)` (act number `→ z⋆ > 0`) pins the coupling at `L₁` to order one, so segment 2 is never empty.
(3) It does **not** control segment 2: b₀ > 0 is a one-loop UV statement; whether the coupling continues to grow and the
conditioned system stays in a uniqueness regime is non-perturbative.

## 4. Unit tests

| test | claim tested | result |
|---|---|---|
| photon (U(1), weak) | `EnvelopeW`, `NearStable`, `H1Local` | expected to **hold** (Gaussian effective actions under a smearing blocking with noise are quasi-local in block units; Balaban, Gawedzki–Kupiainen, recalled), and they must not give a gap: they do not; `LevelDprime` fails (no gap), so `yang_mills_assembly_level` says nothing. Pass |
| Banks–Zaks | the same | with a small IR fixed point g⋆ the coupling stays small at every scale, segment 2 is weak coupling, `H1Local` is expected to hold perturbatively, the theory is gapless, and `LevelDprime` fails. So `H1Local` contains no gap information and the gap sits in `LevelDprime`. Pass; it also shows that the difficulty of `H1Local` at L₁ is tied to the coupling growing to order one, i.e. to the absence of an IR fixed point |
| triviality (φ⁴₄) | `H1Local` as an existence statement | for the opposite sign of the running a family with fixed coupling at `L₁` does not exist (Landau pole); the families that exist have `g(L₁) → 0` and a Gaussian limit, for which `H1Local` holds with a free limit. Nothing here claims non-triviality (that is `NonTrivial`, `OnLCP`). Pass |
| Z₂ (weak) | gap-only and confinement-type claims | no claim of mine asserts any property of a given theory; the Lean theorems are group-blind consequences of the named hypotheses. Pass (vacuous) |
| finite subgroups | — | group-blind proofs; hypotheses typed on SU(2). Pass (vacuous) |
| deconfinement (L₁ < 1/T_c) | `LevelDprime` | a strong-coupling (Dobrushin) condition at L₁: must fail there, and nothing here claims it holds. Pass |
| pure noise (β = 0) | `yang_mills_assembly_level` | pure noise would satisfy `LevelDprime` (if its blocked law has a bounded log-density) and has a gap; it fails `OnLCP`, which is a hypothesis of the theorem (`not_onLCP_of_bounded`). Pass |
| mixture | `BlockGapUnif` | a block-level decay statement for every level, so an RP mixture without a gap cannot satisfy it (decay of reflected covariances). Pass |

## 5. Proposed changes (for the assembly's owner; not made here)

1. **Crossover option.** Add `H1.LevelTorusRoute` (`LevelDprime ∧ ObsTransferPhys`) as a disjunct of `OpenPieces.crossover`,
   or replace `BlockedTorusRoute` by it (`levelTorusRoute_of_blockedTorusRoute` shows the old option implies the new one).
   The top theorem is then `yang_mills_assembly_level`.
2. **Open-input list of the torus route:** `LevelDprime` (P4.1/P4.1′, the crossover in depth-uniform form: D′ at the levels,
   adjoint half as before), `ObsTransferPhys`, the line of constant physics, `NonTrivial`. `H1Local` moves from "open input"
   to "one sufficient condition for `LevelDprime` together with `LimitDprime`", split by `h1Local_iff_split`.
3. **Noisy blockings.** `BlockingFamily` is deterministic, so `H1Local` (R) and `LevelDprime` (R) are not even known per
   `(k, j)` for the good blocking. Let a blocking carry an independent product noise on coarse links (a class-function heat
   kernel around the deterministic prediction, as in OpenAI and cycle 1's `NoisyBlocking`), i.e. a deterministic map on
   (fine links × noise). Reflection positivity survives if the noise is a product over coarse links with a reflection-invariant
   law (paper sketch: integrate the noise of each half separately, then use the fine RP for each value of the noise on the
   reflection plane, then average). `ObsTransfer(Phys)` then conditions on the noisy block field.
4. **Blueprint rows** (proposed text):

| piece | was | now |
|---|---|---|
| P3.5 (new) | — | `H1Local` split: Lean (`h1Local_iff_split`, `h1Local_of_quasiLocal`): representation ∧ `EnvelopeW` (λ' > λ) ∧ per-volume convergence ∧ `NearStable` ⇒ `H1Local`; `EnvelopeW` at weak-coupling scales plausible from Balaban/OpenAI upper bounds (paper), open at L₁ |
| P4.1′ | open: `H1Local`, `LimitDprime`, `ObsTransfer(U)` | open: **`LevelDprime`** (D′ at the levels, depth-uniform; contains `H1Local`'s locality and `LimitDprime`), `ObsTransferPhys`; Lean `yang_mills_assembly_level`; the convergence half of `H1Local` is not needed |
| P7.1/P7.2 | torus route `H1Local ∧ LimitDprime ∧ ObsTransferPhys` | add `LevelTorusRoute` (weaker or equal) |

## 6. Clicks

* **"The act conserved through lossy layers because it runs" (PREP, round 4).** The reading said: what is lost from layer to
  layer is the description (the effective action), not the act. `Level.lean` is that statement made exact for the route: the
  gap needs a depth-uniform bound at every finite depth (`LevelDprime`, the act's certificate), not the convergence of the
  description (`NearUniform`, a limit effective action at L₁). The same shape appeared in ws4 ("what exists is the
  finite-depth family with depth-uniform bounds"; `bothOrders_of_torusDecay`) and in the existence proof itself (budgets
  uniform in the volume, limits by compactness). Three times now the limit object is avoidable and the uniform finite-depth
  bound is what carries the content.
* **Tie to G0 = inward reach = asymptotic freedom.** In the two-segment picture inward reach is exactly what turns "infinitely
  deep" into "finitely many strongly coupled layers": b₀ > 0 makes segment 1 uniform in the cutoff and leaves a fixed segment 2.
  Banks–Zaks has the same inward reach and no segment 2 (the coupling never grows): reach alone does not give the gap, and
  `H1Local` is easy precisely there. What pure Yang–Mills must add is that the running does not stall, and that is where
  `H1Local` and `LimitDprime` meet.
* **With c3a-uv (one property seen twice).** `EnvelopeW` (locality of the effective action) and `ObsTransferPhys`(c)
  (conditional decoupling of fine observables) both follow from one property: the fine field **conditioned on the block
  field** has a uniform mass at the block scale. In the Gaussian case they are literally the same operator: the effective
  action's kernel is `Cov(Ψ,Ψ)⁻¹` and the conditional covariance is `C − Cov(·,Ψ) Cov(Ψ,Ψ)⁻¹ Cov(Ψ,·)`, both quasi-local exactly
  when the block-constrained fluctuation operator has a gap (Balaban's propagator bounds). Suggested for cycle 4: one named
  hypothesis `CondMass` (the conditioned fine system satisfies a Dobrushin or log-Sobolev condition at the block scale,
  uniformly in the level) feeding both `ObsTransferPhys` and `EnvelopeW`; c3a's photon run is its free-field test. Not done
  here, to avoid duplicating c3a.

## 7. Next step

Prove `EnvelopeW` (or `CondMass`) in segment 1 from published bounds: take Balaban's (or OpenAI's) small-field effective
action at a scale with g ≤ ḡ, and show by a Kotecký–Preiss expansion that the log-density of the noisy L_* law is a sum of
local terms with `e^{κ·diam}` tails uniform in the cutoff and the volume (upper bounds only, no ratio bounds). That would
leave, for route A, exactly one non-perturbative statement: `LevelDprime` across the fixed segment 2 (n blocking steps from
`L_*` to `L₁`), which is a finite-depth statement about a strongly coupled lattice system with a cutoff-independent input.

## Files

- `../../../formal/ProofPhase/H1/Split.lean`: `pairSum`, `nearSum`, `farSum`, `pairSum_eq_near_add_far`, `PairSumBdd`,
  `TailSmall`, `NearUniform`, `exists_seq_of_unif`, `localConvergenceW_iff`, `EnvelopeW`, `tailSmall_of_envelope`,
  `pairSumBdd_of_envelope`, `nearUniform_of_stable`, `flatW_far_le`, `linkDiam`, `linkDist_le_linkDiam`, `supDist`,
  `h1Local_iff_split`, `NearStable`, `h1Local_of_quasiLocal`.
- `../../../formal/ProofPhase/H1/Level.lean`: `LevelDprime`, `levelDprime_of_h1Local`, `BlockGapUnif`,
  `blockGapUnif_of_levelDprime`, `blockGapUnif_of_blockedRoute`, `torusDecayLoc_of_blockGapUnif`, `LevelTorusRoute`,
  `levelTorusRoute_of_blockedTorusRoute`, `bothOrdersLoc_of_levelRoute`, `yang_mills_assembly_level`.
- Here: `setup.sh`, `build.sh`, `axioms.sh`. No numerics; no commit, push or GPU.
