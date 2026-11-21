# Proof blueprint (the map of the proof phase; first version 2026-11-22)

The Clay statement for SU(2) (Jaffe–Witten): a quantum Yang–Mills theory on ℝ⁴ exists (satisfying the Osterwalder–Schrader or Wightman
axioms) and has a mass gap Δ > 0. This file lists every piece a proof along our route needs, with its exact status. Statuses: **Lean**
(machine-checked, named theorem), **paper** (proved on paper in a note, not formalised), **known** (in the literature, cited, not
reproduced), **open**. Every phase result names the piece it changes. Claim discipline: `attempts/RULES.md` (round 4 and the phase
section); the review that set it: `attempts/r3-review/REVIEW.md`.

## The route in one paragraph

Build the lattice theory (Wilson action, SU(2), 4D torus), block it scale by scale towards a physical scale L₁ where the coupling is of
order one, and show that the blocked theory there has a gap that survives the removal of the cutoff and of the volume. The weak-coupling
side (blocking from the cutoff to a fixed weak scale) is the **quantum half** H1; the strong-coupling side (the gap at L₁) is the
**classical half** H2; between them lies the **crossover**, where α_s grows through order one. The owner's DMP reading organises it:
existence is an act asserting itself (existence × extent = one quantum), the act is conserved through every lossy layer because it runs
(Callan–Symanzik), the tie to G0 is reach (inward: asymptotic freedom; outward: confinement), and an existence boundary is an inversion
('t Hooft duality).

## Pieces

### P1. The lattice theory and its structure

| piece | statement | status | where |
|---|---|---|---|
| P1.1 | Wilson measure on the 4D torus, SU(2) and general compact G | Lean | `formal/AreaLaw/ConcreteSUn.lean`, `formal/OneScale/` |
| P1.2 | reflection positivity, site and link | Lean | `formal/Positivity/` |
| P1.3 | transfer matrix (temporal gauge), flux sectors via 't Hooft's centre transformation, E_e ≥ 0, flux-correlator decay | Lean (kernel); paper (kernel = 4D path integral, standard) | `formal/Attempts/R4/LayerKernel.lean`, `LayerTwisted.lean` |
| P1.4 | 't Hooft duality F_e = dual(F_m), unique self-dual point log(1+√2) | Lean | `LayerTwisted.lean` (`freeFlux_eq_dual`), `R4/ConjW.lean` |
| P1.5 | blocking (decimation) gauge covariant, centre- and reflection-commuting; the act conserved per layer | Lean | `R4/LayerDecimation.lean`, `LayerTransport.lean` (`act_conserved_per_layer`) |
| P1.6 | reflection positivity of every decimated layer (T38) | Lean (decimation); open (averaging blockings, Balaban's) | `decimated_wilson_rp_SU2` |
| P1.7 | strict E_e > 0 in finite volume; centre elements beyond z² = 1 (SU(N)) | paper / open | `r4-layer/NOTE.md` |

### P2. Decay machinery (classical half, conditional)

| piece | statement | status | where |
|---|---|---|---|
| P2.1 | Dobrushin uniqueness with exponential weights for finite Gibbs systems (Theorem A, weighted) | Lean | `R3/TailDecay.lean` (`theoremA_w`) |
| P2.2 | local flatness criterion D′ ⇒ single-site GDS; openness under local perturbation | Lean | `R3/FlatFactors.lean`, `R3/Robust.lean` |
| P2.3 | gap of block observables from D′ at L₁, uniform in volume and spacing | Lean (abstract Gibbs systems) | `gap_of_localFactorsW`, `continuum_decay` |
| P2.4 | Corollary B: decay in physical units | Lean | `formal/OneScale/CorollaryB*.lean` |
| P2.5 | strong-coupling gap (any compact group), soft swap | Lean / paper | `AreaLaw.Clustering`, `R2/CouplingSwap.lean` |

Caveat (review): D′ is a worst-case condition, strictly stronger than the gap, and false for L₁ < 1/T_c.

### P3. Quantum half (weak coupling)

| piece | statement | status | where |
|---|---|---|---|
| P3.1 | one noisy blocking step gives a large-field lower bound; per volume W_p by compactness | Lean (core) | `R3/WpNoise.lean` |
| P3.2 | Lemma T (relative closeness survives blocking, uniformly in the boundary) | paper | `r2-stepscaling/NOTE.md` §4 |
| P3.3 | per-volume gap theorem joining P3.1 to P2.3 | paper (reviewer: correct in the order mesh, volume, observable) | `r3-wp/NOTE.md`, `r3-review/REVIEW.md` |
| P3.4 | ultraviolet stability, small-field control, one-loop running | known (Balaban; the OpenAI construction, read at stage level) | `H1-OPENAI.md` |

### P4. The crossover (open; the core)

| piece | statement | status | where |
|---|---|---|---|
| P4.1 | form (a): every limit theory blocked to L₁ satisfies D′ (stronger than the gap) | open | `ROUND-3.md` |
| P4.2 | Conjecture W: the act number z(L) = E_e·L grows by a margin per doubling (flux-sector confinement) | open; photon marginality and finite-group failure proved | `r4-conjw/NOTE.md`, `R4/ConjW.lean` |
| P4.3 | (B1) minimal action on T³×ℝ is 4π²/g² (half-instanton) | known numerically; certifiable | `r4-conjw/NOTE.md` |
| P4.4 | (B2) the fluctuation prefactor grows like (L/a)^{11/3} along the line of constant physics (where b₀ enters) | open; needs constructive renormalisation | `r4-conjw/NOTE.md` |
| P4.5 | (B3) order of limits: time to infinity before doubling | open | `r4-conjw/NOTE.md` |
| P4.6 | no infrared fixed point for pure SU(2) (the owner's "something must run") | open; perturbatively true; selection principle in toy Lean | `r4-minting/NOTE.md`, `R4/MintingScale.lean` |
| P4.7 | assumption (U): each blocked layer is the original action at another coupling (collapse) | open; tested by the act-number run | `r4-minting/NOTE.md` |

The one-sided step every route meets: comparing the blocked measure with the original on the same box (`r4-layer/NOTE.md`).

### P5. From the flux sector to the vacuum gap

| piece | statement | status |
|---|---|---|
| P5.1 | sector transfer: growth of z (flux-sector gap) ⇒ a gap in the vacuum (glueball) sector | open; no known route |
| P5.2 | relation of block observables at L₁ to all local gauge-invariant observables | paper with a stated gap (`r3-robust/NOTE.md`: H1-fine) |

### P6. Existence, identification and the axioms

| piece | statement | status |
|---|---|---|
| P6.1 | existence of the continuum limit (subsequential) | known (OpenAI construction, read at reading level); our compactness lemma P3.1 |
| P6.2 | identification: the limit is non-trivial (not free, not pure noise) and unique along the line of constant physics | open (review finding 2: a pure-noise limit satisfies P2.3's hypotheses) |
| P6.3 | reflection positivity of the limit (OS positivity) | partial: per layer (P1.6); the limit open |
| P6.4 | Euclidean (rotation) invariance of the limit | open |
| P6.5 | infinite-volume limit and the Wightman reconstruction | known given the OS axioms (Osterwalder–Schrader) |
| P6.6 | tuning / line of constant physics inside the hypotheses | open (absent from every round-3 hypothesis) |

### P7. Assembly

| piece | statement | status |
|---|---|---|
| P7.1 | one Lean theorem: Yang–Mills in the hypotheses (SU(2), 4D torus, Wilson measure, tuning), the open pieces above as named hypotheses, the gap (and the OS-type properties proved so far) as conclusion | to be built (readiness step) |

## Unit tests (every claimed discharge)

Photon (U(1) at weak coupling gets no gap), Z₂ (no area law at weak coupling; gap-only claims must hold for it), finite subgroups of
SU(2) (frozen), deconfinement (no strong-coupling condition below 1/T_c), triviality (no non-trivial φ⁴₄), Banks–Zaks (nothing that
would gap the conformal window).

## The owner's readings that organise the map

Act identity (P4.2), the act conserved per layer because it runs (P1.5, P4.7), tie to G0 = inward reach (P3.4), outward reach =
confinement (P4.2), inversion = 't Hooft duality (P1.4), something must run (P4.6), the centre reached through the causal round trip
("−1 is a commutator", P4.2), Gauss's law as internal verification (P1.3). All in `PREP.md`.
