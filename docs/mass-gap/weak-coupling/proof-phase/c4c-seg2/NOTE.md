# Cycle 4, workstream 3 (c4c-seg2): segment 2 (L_* -> L1) as filter stability (2026-11-22)

Brief: decide whether segment 2's content (Lemma X of `../c3a-uv/NOTE.md` section 2.2: conditional decoupling and observable
transfer across the fixed number of steps from L_* to L1 at coupling of order one) can be obtained as a **filter-stability**
statement under an **observability** condition (van Handel and related work); set up the dictionary, find the matching theorems,
run the unit tests, formalise what is honest, state the remaining hypothesis and whether it can be tested.

Claim levels as in `../../attempts/RULES.md`: **Lean**, **Lean (D)** (definitional or elementary), **paper**, **heuristic**,
**literature** (cited; "checked" = abstract or summary read this session, "recalled" = not re-read). Lean: one new file
`../../../formal/ProofPhase/Seg2/Filter.lean`, built in `~/formal-c4c` (Lean 4.34.0, Mathlib v4.34.0); `axioms.sh` prints 14
headline theorems, all `propext, Classical.choice, Quot.sound`; no `sorry`, no `native_decide`, no new axioms (`axioms.log`).
Nothing outside `ProofPhase/Seg2/` and this folder was edited. No numerics were run; `PREREG.md` is a GPU test design, written, not
run.

```
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c4c-seg2/setup.sh
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c4c-seg2/build.sh ProofPhase.Seg2.Filter
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c4c-seg2/axioms.sh
```

---

## 0. Result in one paragraph

**Filter stability is the exact language of part (c) in the time direction, but it cannot carry segment 2 by itself.** The
dictionary is exact and the reduction is in Lean: with Euclidean time as the HMM time, the fine slice field as hidden state and the
good blocking's coarse links as observations, the conditional decoupling defect is bounded by the **smoother-stability defect**
`∫|E[F | blocks, slices] − E[F | blocks]|` (`abs_condDefect_le_smoother`), and an annealed step-wise contraction of the conditional
chain bounds that defect by `2 E[∏ θ_i]` (`smoother_chain_of_steps`); on the Wilson measure this gives part (c) of
`ObsTransferPhys` for separated pairs from a named hypothesis `SmootherStable` (`condDecouple_of_smootherStable`). The literature
then says three things, and together they settle the brief's question. (1) Observability is what makes a filter stable **without
signal ergodicity**: a rigorous mechanism that does not use the gap, and the one that makes the photon pass (Kalman: unstable but
detectable signal, exponentially stable smoother; c3a's Gaussian rate 4.5/L1). (2) Observability theorems are qualitative or
finite-dimensional; the only **dimension-free** (volume-uniform) stability theorems are Dobrushin-type conditions on the
conditional space-time system (Rebeschini–van Handel), i.e. exactly c4a's `CondMass`. (3) In infinite dimension, observability and
signal ergodicity are **neither sufficient nor inherited**: Rebeschini–van Handel (EJP 2015) give an i.i.d. signal (infinite gap)
whose filter has a phase transition precisely in the strong-observation regime. So the route reduces Lemma X (time form) to a
conditional uniqueness statement at order-one coupling (no hidden phase transition of the fine field given the block field), which
is **gap-free** (the photon satisfies it) and is the same thing as `CondMass` seen from the filtering side. **Where the gap sits
afterwards:** if observability carries Lemma X, the gap content sits entirely in `LevelDprime` (W1 form) at L1, the condition
c3b found reached at L1 sqrt(sigma) = 2.80; Lemma X keeps the non-perturbative but gap-free problem of conditional uniqueness at
the crossover. New unit test: an exact symmetry that the blocking does not observe and that breaks in some phase (centre symmetry
in the deconfined phase, for a centre-blind blocking) must make (c) fail there; it does, by the Rebeschini–van Handel mechanism.

## 1. The dictionary

### 1.1 Two candidate "times", and the choice

**(i) Renormalisation scale (r = log2(L1/L0) steps, fixed).** Hidden chain X_0 (L0 field) -> X_1 -> ... -> X_r (L1 field), each
step the deterministic smeared map. The reversed chain is Markov (each X_{i+1} is a function of X_i), and `condDefect_tower`
(c3a) telescopes part (c) into r one-step defects:
`condDefect_{σ(X_r)}(F,G) = Σ_{i<r} condDefect_{σ(X_{i+1})}(E[F|X_i], E[G|X_i])` (Lean (D) by iterating `condDefect_tower`; the
two-step case is c3a's `twoStage`). With a **finite horizon there is nothing to forget**: "stability" over r fixed steps means only
that errors add with r-dependent constants. Each one-step defect is a conditional decoupling for one blocking step at the coupling
of that scale, and the last ones are at order one. **Verdict: bookkeeping, not a mechanism.** The scale direction does not touch
the obstruction.

**(ii) Euclidean time (the transfer-matrix chain). Chosen.** Coarse time step = L1.
* **Hidden state** X_t: the fine field on the spatial slice at fine time t·ℓ_k (all spatial links of that slice).
* **Signal kernel**: the law of X_{t+1} given X_t, the Wilson transfer matrix over physical time L1 (temporal links integrated:
  e^{−L1 H} with the Gauss projection). Its mixing rate is the mass gap.
* **Observations** Y_t: the coarse links of the good blocking attached to coarse time t: coarse spatial links at t (functions of
  X_t: spatial staples stay in the slice) and coarse temporal links over the strip [t, t+1] (functions of the strip's fine links:
  temporal decimation, spatial staples inside the strip). A **pairwise HMM with deterministic observations** (Y depends on the
  transition and the strip interior); `RouteA/Blocking.lean` (`smearSum`, `transverse`) fixes this structure.
* **Smoother**: the conditional law of the fine field given all Y on the torus. Part (c) for a time-separated pair is the
  annealed covariance under the smoother, `condDefect = E_Y Cov(F, G | Y)`.

### 1.2 What "stability" means here

Filter stability: the conditional law forgets its initial condition. For the smoother on a time circle, the relevant form is: the
conditional expectation of F given all observations changes little if one also learns the hidden state far from F,
`∫|E[F | Y, X_{t1}, X_{t2}] − E[F | Y]| ≤ c e^{−m D}` (slices t1, t2 at distance ≥ D/2 from supp F on both arcs). This is the
**smoother-stability defect**. It is annealed (averaged over Y), as c3a recommended for large fields.

### 1.3 The Markov split (paper, elementary)

Every Wilson plaquette lies in one fine time strip [s, s+1] or one slice. Remove two fine slices at coarse times t1, t2 that cut
the time circle between supp F and supp G: no plaquette meets both remaining arcs, so the density factorises and
`U_A ⫫ U_B | (X_{t1}, X_{t2})`. Each coarse variable is a function of one arc and the slices (spatial coarse links at t1, t2 are
functions of the slices; every coarse temporal link lies in one strip). Conditional independence survives conditioning on
functions of (arc, slices), so `F ⫫ G | σ(Y) ∨ σ(X_{t1}, X_{t2})`, hence `condDefect_K(F, G) = 0` for `K = σ(Y) ∨ σ(slices)`.
The same argument gives the Markov property along a chain of slice pairs moving away from F. Not formalised (slice
sigma-algebras on `GaugeConnection` do not exist yet; proposed below); in the Lean hypothesis these are explicit clauses.

### 1.4 The candidate theorem

> **Candidate (filter-stability form of Lemma X, time direction).** For the good blocking at L1 and every R there are c, m > 0 and
> k0 such that for all levels k ≥ k0, volumes j and gauge-invariant F, G (|·| ≤ 1, physical extent ≤ R, time separation ≥ D):
> `∫|E[F | Y, X_{t1}, X_{t2}] − E[F | Y]| d(Wilson) ≤ c e^{−mD}` (`SmootherStable`). Then part (c) of `ObsTransferPhys` holds for
> these pairs (`condDecouple_of_smootherStable`, Lean).

Hypotheses one would want from the filtering literature: (H1) a signal with a strictly positive, locally bounded transition
density (Doeblin-type), or (H2) observability (distinct initial laws give distinct observation laws) / uniform observability,
(H3) non-degenerate observation noise, (H4) finite-dimensional (or locally compact, tight) state space, (H5) for
dimension-free rates: a weak-interaction (Dobrushin) condition. Section 2 checks each against our setting.

## 2. Literature: what is proved, under which assumptions, and whether we meet them

| result | assumptions | conclusion | our setting |
|---|---|---|---|
| Kalman–Bucy stability (linear Gaussian); recovered as a special case of van Handel AAP 2009 (checked: abstract) | linear Gaussian, detectable (observable) and stabilisable | exponential stability of the filter, signal may be unstable | **the photon at Gaussian level**: c3a's computation is this case (rate ≈ 4.5/L1 in time, uniform in ℓ). Not SU(2) |
| van Handel, "Observability and nonlinear filtering", PTRF 145 (2009) 35, arXiv:0708.3412 (checked: abstract via the AAP paper's summary) | observability; the signal **tight** (stable) | filter stability, no rate | qualitative only; tightness in a volume-uniform sense is the gap; no rate |
| van Handel, "Uniform observability of hidden Markov models and filter stability for unstable signals", Ann. Appl. Probab. 19 (2009) 1172, doi 10.1214/08-AAP576 (checked: abstract) | **uniform** observability; white-noise-type (non-degenerate) observations | stability without stability assumptions on the signal; Kalman–Bucy as a special case | our observations are **deterministic** (H3 fails; the soft blocking restores it); constants are not dimension-free (H4) |
| Chigansky, van Handel, "A complete solution to Blackwell's unique ergodicity problem for hidden Markov chains", AAP 20 (2010) 2318 (checked: abstract) | finite or countable state space, observations a function of the chain allowed | necessary and sufficient conditions for unique ergodicity of the filter | covers deterministic observations, but finite state (H4 fails) |
| van Handel, "The stability of conditional Markov processes and Markov chains in random environments", Ann. Probab. 37 (2009) 1876 (recalled) | general | the smoother (signal given the whole observation path) is a Markov chain in a random environment; its ergodicity is tied to filter stability | the right object (our smoother); qualitative |
| Tong, van Handel, "Conditional ergodicity in infinite dimension", Ann. Probab. 42 (2014) 2243, arXiv:1208.3182 (checked: abstract) | infinite-dimensional chains with **local mixing** or asymptotic couplings of the signal | conditional ergodicity, filter stability (qualitative) | infinite dimension is ours; the input is signal-side mixing (the gap: circular), no rates |
| Rebeschini, van Handel, "Can local particle filters beat the curse of dimensionality?", AAP 25 (2015) 2809, arXiv:1301.6585 (checked: summary of Thm 2.1) | local transition densities ε ≤ p ≤ 1/ε with ε > ε0 (ε0 depends only on local geometry), local observation densities κ ≤ g ≤ 1/κ | **dimension-free** decay of correlations of the filter (spatial and temporal), by Dobrushin comparison | ε near 1 means the signal is close to a product (weak interaction): the continuum-limit transfer kernel over L1 at order-one coupling is not; this is a **signal-side** Dobrushin condition. Observability plays no role |
| Rebeschini, van Handel, "Phase transitions in nonlinear filtering", EJP 20 (2015) no. 7, arXiv:1401.6450 (checked: summary of sections 1–5) | i.i.d. spins on Z × time, noisy observations of **products** of neighbouring spins in space and time (flip probability p) | filter **not** stable for small p (strong observations), stable for p above a Dobrushin threshold; the conditional law is a random-bond Ising model; also: spatial mixing is not inherited by conditional random fields in general; monotone models do inherit it (their Thm 5.12) | the counterexample that decides the brief (section 4.1) |

Related on the gauge side (checked: abstract): Shen, Zhu, Zhu, "A stochastic analysis approach to lattice Yang–Mills at strong
coupling", CMP 400 (2023) 805, arXiv:2204.12737: Bakry–Émery with the Ricci curvature of the group gives log-Sobolev and a mass gap
at strong coupling. Its conditional version (Bakry–Émery for the fine field given soft block variables) is one concrete way to
prove `CondMass` where it applies; at the couplings of segment 2 the Wilson Hessian is not dominated by the group's Ricci
curvature, so it does not apply as is (paper, short: the Hessian of `β Re tr U_p` is of order β in some directions).

**Verdict on the assumptions.** Non-degenerate noise (H3): fails for the deterministic good blocking, restored by the soft
blocking (Lemma X's soft form, c3a section 8). Finite dimension (H4): fails, and this is fatal for every observability theorem:
none gives volume-uniform rates. Dimension-free results (H5) need a Dobrushin condition, which in the published form is on the
signal (weak interaction) and in the form we can hope for is on the **conditional** system: that is `CondMass`.

## 3. Lean (`ProofPhase/Seg2/Filter.lean`)

`condDefect μ m F G := ∫FG − ∫E[F|m]E[G|m]` (c3a). `Bdd1 μ F`: a.e. strongly measurable and |F| ≤ 1 a.e.

| Lean | exact statement | mark | Yang–Mills |
|---|---|---|---|
| `condDefect_comm` | `condDefect μ m F G = condDefect μ m G F` | D | no |
| `abs_condDefect_le_dev` | `m ≤ mX`, `Bdd1 f`, `Bdd1 g` ⇒ `|condDefect μ m f g| ≤ ∫|f − E[f|m]|` | S (small) | no |
| `condDefect_eq_of_condUncorr` | `m ≤ K ≤ mX`, `condDefect μ K F G = 0` ⇒ `condDefect μ m F G = condDefect μ m E[F|K] E[G|K]` | D | no |
| **`abs_condDefect_le_smoother`** | `m ≤ K ≤ mX`, `Bdd1 F, G`, `condDefect μ K F G = 0` ⇒ `|condDefect μ m F G| ≤ ∫|E[F|K] − E[F|m]|`; primed version with `G` | S (small; the dictionary in one line) | no |
| `approx_of_smoother` | `E[F|K] = E[F|K']` a.e. ⇒ `∫|E[F|m] − E[F|𝒩]| ≤ ∫|E[F|K] − E[F|m]| + ∫|E[F|K'] − E[F|𝒩]|` (part (b): far observations forgotten) | D | no |
| **`smoother_chain_of_steps`** | `m ≤ K i ≤ mX`; `θ i` m-strongly measurable in [0,1]; Markov `E[E[F|K i]|K (i+1)] = E[F|K (i+1)]`; step `E[|E[u_i|K(i+1)]| | m] ≤ θ_i E[|u_i| | m]` a.e. for `u_i = E[F|K i] − E[F|m]` ⇒ `∫|E[F|K n] − E[F|m]| ≤ 2 ∫ ∏_{i<n} θ_i` | S (annealed contraction; the Dobrushin argument in conditional L1 form) | no |
| `CondContract`, `smoother_chain` | model-level step contraction (every K-measurable centred `u`, |u| ≤ 2) ⇒ the same bound | S | no |
| `abs_condDefect_le_chain`, `abs_condDefect_le_chain_const` | the chain plus the Markov split at its end ⇒ `|condDefect m F G| ≤ 2∫∏θ_i`; constant θ0: `≤ 2 θ0^n` | S | no |
| `CondDecouple T B Sep` | part (c) of `ObsTransferPhys` (same quantifiers, constants) for pairs with `Sep k j A₀ B₀ D` | definition | the SU(2) Wilson measure `T.ym k j`, blocking family `B` |
| `condClause_eq` | the (c) clause of `ObsTransferPhys` is `|condDefect (T.ym k j) (blockSigma T B k j) F G|` | D (rfl) | yes |
| `SmootherStable T B Sep` | for each admissible separated pair: `∃ K`, `σ(B) ≤ K ≤ pi`, `condDefect K F G = 0`, `∫|E[F|K] − E[F|σ(B)]| ≤ c e^{−mD}` | **named hypothesis** | Wilson measure, `B` |
| **`condDecouple_of_smootherStable`** | `SmootherStable T B Sep → CondDecouple T B Sep` | S (reduction) | yes (group-blind proof) |
| `AnnealedContraction T B Sep` | for each pair: a chain `K i` above `σ(B)`, weights `θ i` (functions of the block field, in [0,1]), the step bounds of `smoother_chain_of_steps` for F, the Markov clauses, `condDefect (K n) F G = 0`, `2∫∏θ ≤ c e^{−mD}` | named hypothesis (sufficient for the previous one) | yes |
| `smootherStable_of_annealedContraction`, `condDecouple_of_annealedContraction` | `AnnealedContraction → SmootherStable → CondDecouple` | S (reduction) | yes |

`Sep` is a parameter (`SepPred T`); time separation by two coarse slices gives c3a's `ObsTransferPhysT`, part (c). Not vacuous:
`K = pi` makes the Markov clause trivial but the stability defect is then `∫|F − E[F|σ(B)]|`, of order one; `K = σ(B)` makes the
stability defect zero but requires `condDefect σ(B) F G = 0`, stronger than the conclusion. The intended `K` is
`σ(B) ∨ σ(two slices)`, where the Markov clause is a theorem (section 1.3, paper). No theorem here estimates anything for an
interacting theory; none distinguishes SU(2) from U(1) or Z₂, by design.

## 4. Why filter stability cannot carry segment 2 alone, and what it does carry

### 4.1 The decisive paragraph (negative result)

Stability of a filter has two known sources: **ergodicity of the signal** (for us: the gap; circular) and **observability**
(the observations pin the directions the signal does not forget; for us: the constraint mechanism of c3a). In finite dimension
observability suffices without any ergodicity (van Handel 2009; Kalman–Bucy), which is why the idea is attractive and why the
photon passes. In our setting the hidden state is a whole time slice of a lattice whose volume and resolution go to infinity, and
there (a) observability theorems give no rates and no volume uniformity, (b) the dimension-free theorems need a Dobrushin
condition (Rebeschini–van Handel 2015, AAP), and (c) **conditioning can create long-range order that neither the signal nor the
observation model has**: an i.i.d. signal (every correlation zero, "infinite gap") observed through noisy products of neighbouring
spins has an unstable filter when the observations are strong (Rebeschini–van Handel 2015, EJP; the conditional law is a
random-bond Ising model at low temperature). Our block variables are deterministic, gauge-invariant composites: the
strongest-observation, product-type case. So "observable ⇒ stable" is false in infinite dimension, and what a proof of Lemma X
needs is a **conditional uniqueness** statement: the fine field given the block field has no (hidden) phase transition and mixes
at the block scale, uniformly in the volume and the resolution, at order-one coupling. That is c4a's `CondMass`. Filter stability
gives the exact statement (Lean) and the right reason to expect it (observability pins the slow modes), not a proof.

### 4.2 A trap in the naive formulation (paper, short)

The tempting model-level hypothesis "each step of the conditional chain contracts in total variation by θ < 1" (`CondContract`
with constant θ for every function of the whole slice) **cannot hold uniformly in the volume**: for a slice made of V nearly
independent regions, each step's total-variation coefficient is at least `1 − a^V` with `a < 1` the Hellinger affinity of one
region's two conditional laws (Hellinger affinity tensorises), which tends to 1. This is the curse of dimensionality of filter
stability. Hence the Lean hypothesis `AnnealedContraction` asks for contraction of **F's own** smoother defect
(`smoother_chain_of_steps`), and the volume-uniform sufficient condition must be **local**: a Dobrushin interdependence matrix on
space-time super-sites (L1 cells × coarse times) of the conditional system, whose comparison theorem bounds the influence of a slice
at time distance D on F by `|supp F| γ^{D/L1}/(1 − γ)` (Dobrushin 1970; Foellmer, J. Funct. Anal. 46 (1982) 387; Rebeschini–van
Handel, J. Stat. Phys. 157 (2014) 234: recalled). That condition is `CondMass` in Dobrushin form.

### 4.3 Observability and `CondMass` (c4a): the same thing seen twice

* **Gaussian (exact).** For a Gaussian field with precision A and linear observations Q (soft, noise variance s), the conditional
  precision is `A + Q*Q/s`. Uniform observability = `A + Q*Q/s ≥ c > 0` uniformly (no slow mode invisible to Q), which with the
  finite range of A and Q gives exponential decay of the conditional covariance (Demko–Moss–Smith, Math. Comp. 43 (1984) 491,
  recalled; Combes–Thomas): observability **is** conditional mass. For the hard blocking it is c3a's coercivity on ker Q, and
  decimation loses it (`Var(Q) ∝ ℓ`).
* **Interacting (our case).** `CondMass` (Dobrushin or log-Sobolev for the conditioned fine system at the block scale) ⇒
  `SmootherStable` in the time direction (comparison theorem, paper). `SmootherStable` is weaker: time direction only, annealed,
  gauge-invariant observables only. Observability is the mechanism that should make `CondMass` true; it is not a separate input.
* **Recommendation to c4a.** State `CondMass` (i) **annealed** (averaged over the block field: large fields are not rare at order
  one), (ii) **local** (Dobrushin matrix on super-sites, not a global contraction; section 4.2), and (iii) **modulo exact
  symmetries the blocking does not observe** (gauge); a quenched `CondMass` for all observables may be false through the
  Rebeschini–van Handel mechanism. The good blocking observes the centre (centre-covariant coarse temporal links), which is what
  the deconfinement test needs (section 5).

### 4.4 A click (lead, heuristic): conditional phase transitions are decoding thresholds

The Rebeschini–van Handel conditional law (i.i.d. spins given noisy bond products) is the random-bond Ising model on the Nishimori
line; the same structure for Z₂ plaquette observations is the random-plaquette gauge model of Dennis, Kitaev, Landahl, Preskill
("Topological quantum memory", J. Math. Phys. 43 (2002) 4452, recalled), whose ordered conditional phase is the regime where
the code protects the unobserved (logical, non-contractible) sector. Read for us: Lemma X asks that the block field "decode" the
fine field **locally**; a conditional ordered phase is harmful only for observables odd under an unobserved symmetry (the logical
sector, the global flip, the centre sign for a centre-blind blocking), and for invariant observables only at the conditional
critical point (heuristic; plausible from the RBIM, where energy-type correlations stay short-ranged away from criticality).
The owner's "Gauss's law as internal verification" reading fits: what the block field must certify is exactly the set of
symmetry sectors that could order conditionally.

## 5. Unit tests

| test | verdict | where it bites |
|---|---|---|
| **Photon** (4D U(1), weak coupling) | `SmootherStable` **holds** (linear Gaussian, unstable but detectable signal: the Kalman case; c3a's Gaussian computation: conditional decay ≈ 4.5/L1 in time, uniform in ℓ, for the good blocking). **No gap follows**: difficulty conservation (`condDefect_eq`) puts the power-law covariance into the coarse side, where `LevelDprime` fails. Decimation fails `SmootherStable` as ℓ → ∞ (loss of observability = the noise-limit trap). | PASS (holds, carries no gap) |
| **Deconfinement** (box one block thick, L1 < 1/T_c) | (a) The time direction has no room: on a time circle of one coarse step there are no two slices between separated supports, so the time-form statement is vacuous. (b) In space, the order parameter (Polyakov loop) is observed by the centre-covariant coarse temporal links, so the conditional system does not carry the broken centre symmetry; (c) can hold; the test bites on `LevelDprime`, as before. (c) **For a centre-blind blocking** (adjoint-type block variables, `RouteA/CentreBlind.lean`) the centre sign is an unobserved exact symmetry that is broken in the deconfined phase: the conditional law inherits the ordering, centre-odd F, G (Polyakov loops) stay conditionally correlated, `SmootherStable` **fails**: the Rebeschini–van Handel mechanism, as it must. No gap is produced in the deconfined phase in any case. | PASS; new sub-test below |
| **Z₂** (weak coupling: gap, no confinement) | gap-type claim: must hold. Signal ergodic and conditional system at weak coupling with dilute excitations: `SmootherStable` holds (heuristic: low-temperature expansion of the conditioned system). Implies no area law (no confinement statement anywhere). | PASS |
| **Mixture** ½(μ1 + μ2) | the component label is a non-ergodic hidden variable: the textbook case where observability is necessary. If the block field identifies the label (large volume), the smoother is stable and the between-component covariance sits in the coarse covariance: no gap. If it did not, `SmootherStable` would fail (the label is the unforgotten initial condition). | PASS |
| **Heller endpoint** (massless 0++, finite string tension) | the massless scalar is observed by coarse plaquette traces, so (c) can hold and the coarse side is gapless; `LevelDprime` must fail. If it were unobserved, (c) would fail. No gap either way. | PASS |
| **Banks–Zaks** | gapless conformal theory: (c) can hold photon-like, gap fails on the coarse side. | PASS |
| **Triviality** | no existence claim. | PASS |
| **Finite subgroups** | group-blind statements, conditional. | PASS |

**The theorems here are group-blind and gap-free: they pass every unit test and prove nothing about Yang–Mills.** This is the
intended outcome for a statement whose job is to make part (c) small without using the gap; the Yang–Mills content must enter
through `SmootherStable`/`CondMass` (proved for the SU(2) Wilson measure with the good blocking) and through `LevelDprime`.

**New unit test proposed (unobserved-symmetry test):** for any claim of conditional decoupling (part (c), `CondMass`), take a
blocking that does not observe an exact symmetry which is spontaneously broken in some phase (centre symmetry in the deconfined
phase with a centre-blind blocking; global spin flip with product observations in Rebeschini–van Handel's model): the claim must
fail there for observables odd under that symmetry.

## 6. The remaining hypothesis, and testing it

**Remaining hypothesis (named, sharp):** `SmootherStable T goodBlocking TimeSep` (Lean), i.e. for the good blocking at L1 the
smoother-stability defect of every gauge-invariant local F decays exponentially in the time distance to the cutting slices,
annealed, uniformly in the level and the volume. Sufficient: `CondMass` in local Dobrushin form for the soft blocking (paper,
comparison theorem). Observability (content) is its mechanism, not a separate input.

**Testable on the GPU: yes, at one size.** `PREREG.md` (written, not run): soft blocking (exact conditioning of an equilibrium
configuration by drawing Y given Φ(U0)), a second conditional replica by HMC with autograd forces through the smearing and the
projection, the replica estimator `E_Y Cov(F,G|Y) = E[F^a G^a − F^a G^b]` of exactly the Lean quantity, photon (positive) and
decimation (negative) gates, the c3b scaling pair 2.80/2.92, κ ∈ {2, 8, 32}, verdicts fixed in advance (MASSIVE-CONDITIONAL /
NOISE-LIKE / SLOW-CONDITIONAL). A follow-on, cell-local conditional Dobrushin–Shlosman test is sketched: it is the certifiable
(computer-assisted) form of `CondMass`.

## 7. Where the gap content sits now (difficulty conservation)

`Cov(F,G) = condDefect + Cov(E[F|Y], E[G|Y])` (c3a, Lean). Filter stability bounds the first term without the gap **if**
observability carries it. Then: **the gap content sits entirely in the coarse covariance, i.e. in `LevelDprime` (W1 form,
`LimitDprimeW` with `H1LocalLip`) at L1**, which c3b's refit found inside the linearised W1 window at L1 sqrt(sigma) = 2.80
(not yet certified for the anisotropic action). Lemma X becomes a **gap-free** statement (it holds for the photon) whose
difficulty is conditional uniqueness at order-one coupling: a Gibbsianness-type (no hidden phase transition) problem, the same as
`CondMass` and as c3d's "fine field conditioned on the block field in a uniqueness regime". If instead the block variable is
near noise in some channel (the measured adjoint content at 2.80 is at 3.7σ only), observability fails there and Lemma X is the
gap in that channel (c3a's trap). The test of `PREREG.md` decides between the two at one size.

## 8. Blueprint and assembly changes (proposed; `PROOF-BLUEPRINT.md`, `Assembly.lean`, `Objects.lean` not edited)

* **P5.2 / `ObsTransferPhys`, Lemma X:** add "filter-stability form (Lean, `ProofPhase/Seg2/Filter.lean`): part (c) ≤ the
  smoother-stability defect under the Markov split at two slices (`abs_condDefect_le_smoother`); annealed chain bound
  (`smoother_chain_of_steps`); `SmootherStable ⇒` part (c) for separated pairs on the SU(2) Wilson measure
  (`condDecouple_of_smootherStable`). Literature: observability gives stability without ergodicity only in finite dimension;
  dimension-free stability needs a Dobrushin condition (on the conditional system: `CondMass`); conditional phase transitions
  exist even for i.i.d. signals (Rebeschini–van Handel 2015). If observability carries Lemma X, it is gap-free and the gap content
  is wholly in `LevelDprime` (W1)."
* **Unit tests:** add the unobserved-symmetry test (section 5).
* **For c4a (`Objects`/`Assembly v3`):** (1) slice sigma-algebras `sliceSigma k j t := comap (restriction to the spatial links
  at fine time t)` and a Lean proof of the Markov split (section 1.3) would turn `SmootherStable`'s Markov clauses into
  theorems; (2) `CondMass` annealed, local, modulo gauge (section 4.3); (3) `ObsTransferPhysT` (c3a) with its part (c) supplied
  by `condDecouple_of_smootherStable` at `Sep := TimeSep`.

## 9. Next step

1. **Run `PREREG.md`** after a CPU pipeline test (photon gate first): it measures the exact Lean quantity at the counted point
   and decides "observability carries the conditional mass" against "near-noise channel".
2. **Gaussian base case, provable:** observability ⇒ conditional mass for the linearised good blocking at w = 2 (positivity of
   `A + Q*Q/s` per coarse momentum on the whole zone, then Demko–Moss–Smith / Combes–Thomas decay), uniform in ℓ; this is c3a's
   next step 2 phrased as the photon instance of `SmootherStable`, and finite-dimensional per momentum (Lean-able with interval
   bounds).
3. **Lean bridge to the existing Dobrushin machinery:** for the soft blocking the conditional law has a density, so the R3
   Dobrushin theorem with exponential weights (`R3/TailDecay.lean`, `theoremA_w`) on super-sites would prove `SmootherStable` from
   a super-site conditional Dobrushin condition: the formal link `CondMass ⇒ SmootherStable` (with c4a).

## References

Filtering (bibliographic data checked this session unless marked): R. van Handel, Ann. Appl. Probab. 19 (2009) 1172–1199,
doi 10.1214/08-AAP576, arXiv:0804.2885; R. van Handel, Probab. Theory Relat. Fields 145 (2009) 35–74, arXiv:0708.3412 (recalled
details); R. van Handel, Ann. Probab. 37 (2009) 1876 (recalled); P. Chigansky, R. van Handel, Ann. Appl. Probab. 20 (2010)
2318–2345, arXiv:0910.3603; X. T. Tong, R. van Handel, Ann. Probab. 42 (2014) 2243–2313, arXiv:1208.3182; P. Rebeschini,
R. van Handel, Electron. J. Probab. 20 (2015) no. 7, arXiv:1401.6450; P. Rebeschini, R. van Handel, Ann. Appl. Probab. 25 (2015)
2809–2866, arXiv:1301.6585; P. Rebeschini, R. van Handel, J. Stat. Phys. 157 (2014) 234 (recalled). Gauge side: H. Shen, R. Zhu,
X. Zhu, Commun. Math. Phys. 400 (2023) 805–851, arXiv:2204.12737. Recalled: Dobrushin (1970) comparison; H. Foellmer, J. Funct.
Anal. 46 (1982) 387; S. Demko, W. Moss, P. Smith, Math. Comp. 43 (1984) 491; E. Dennis, A. Kitaev, A. Landahl, J. Preskill,
J. Math. Phys. 43 (2002) 4452; van Enter, Fernandez, Sokal (RG pathologies; `../c3d-h1/NOTE.md`). Project: `../c3a-uv/NOTE.md`,
`../c3d-h1/NOTE.md`, `../c3b-refit/PREREG.md` (Result), `../c2a-adjoint/NOTE.md` section 5, `../../PROOF-BLUEPRINT.md`.
