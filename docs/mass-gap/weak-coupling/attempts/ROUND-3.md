# Attempt round 3: summary (2026-11-21)

Five attempts under `RULES.md` (round-3 additions: aim at the full piece; the triviality test for existence claims), started from the
three-piece map of `ROUND-2.md`. The owner: "the full proof is within reach in round 3, if we set the ambitions high enough; and if we
fail, we are sure to learn something interesting for a better round 4." Notes in each folder; Lean in `../../formal/Attempts/R3/`, all
verified by the coordinating session (builds, no `sorry`, axioms within propext, Classical.choice, Quot.sound; certificates and counts
re-run where named in the commits).

| attempt | folder | commit | Lean | one line |
|---|---|---|---|---|
| 1, close the chain | `r3-robust/` | 70ffb65 | `FlatFactors`, `TailDecay`, `Robust`, 40 theorems | closed: a worst-case Dobrushin condition D′ at L₁ gives the gap, uniform in the spacing; no torus lemma needed |
| 2, crossover by running | `r3-monotone/` | 31e6a45 | `MonotoneCrossing`, `MonotoneTwistEater`, 21 | "no fixed point" is enough and finitely certifiable; the monotonicity breaks at one named step |
| 3, W_p | `r3-wp/` | 2973c92 | `WpNoise`, 9 | per volume, W_p is compactness once one blocking step adds noise; the large-field problem moves into the crossover |
| 4, Leg C (data) | `r3-blocked/` | 8144373 | none | the click test pre-registered and CPU-tested; GPU run queued after Leg B |
| 5, the owner's DMP route | `r3-dmp/` | c2bb2ab | `DmpBridge`, `DmpFlow`, `DmpBalance`, `DmpDuality`, 34 | "YM ⊂ DMP" made precise; not a shorter route to analytic existence; one transfer kept (T38) |

## Verdict

**The proof is not complete; it now has exactly one open piece, in two exact forms, each backed by a proved theorem.** The quantum half
(W_p) and the robustness piece of `ROUND-2.md` are closed or reduced to classical formalising work; what is left is the crossover, the
stretch where α_s grows through order one, which is where the problem was always expected to live.

## The reduction after round 3

**Gap of the continuum theory at scale L₁, uniform in the volume** ⇐
1. **One noisy blocking step** at some scale up to L₁ (attempt 3: then W_p holds per volume along a subsequence by compactness;
   Lean: `noise_uniform`, `noise_subseq`; still to formalise: Theorem A with exponentially weighted influences (Dobrushin; Kuensch),
   attempt D's Lemma T, the per-volume gap theorem), and
2. **Crossover-D′**: every limit theory, blocked to L₁, has one-site conditional laws satisfying the weighted Dobrushin condition
   Σ_{i≠z} tanh(S_iz/2)·e^{λ·dist(z,i)} ≤ γ < 1 with one γ (attempt 1; Lean: `gds_of_flat`, `theoremA_w`, `continuum_decay`,
   `gap_of_localFactorsW`).

The lattice-uniform version (attempt 1, route B) replaces 1 by local H1 and needs the effective action to stay quasi-local through the
crossover. The second exact form of the crossover is attempt 2's: the continuum step-scaling function has no fixed point on [u*, U];
then the coupling reaches u* within a bounded number of doublings, uniformly in the bare coupling (`reach_of_noFixedPoint`), and a
finite certified grid of step-scaling values with one Lipschitz bound suffices (`grid_certificate`).

## What each attempt established

**1. The chain closes by local flatness.** B's soft-swap condition S′ is a worst-case condition, so it implies Dobrushin's condition D′
for every boundary; the torus-versus-boundary distinction only exists for B's chessboard variant. The right shape of H1 is local
(sup-norm closeness of local potentials gives one-site closeness with no volume factor, `specDist_site`); D′ is an open condition, so
under local H1 every fine enough level satisfies it (`levelFlat_of_local`). Price: D′ is strict. For a Wilson-form action it needs SU(2)
α_s > 5.72; on round 2's two-coupling stand-in at L₁√σ ≈ 3 it misses by a factor of about 6. Leg C measures it directly. Unit tests: the
photon's power-law correlations exclude D′ at every scale; deconfined Z₂ fails D′ (its blocked factors sharpen); D′ holds for every
boundary, so by Chatterjee's theorem it is confinement-strength and cannot cover gap-without-confinement.

**2. The crossover by running.** Monotone running alone is not enough (`monotone_not_enough`: a non-decreasing coupling can stall below
the target, as the photon's does); no fixed point is. 't Hooft duality is an order-reversing involution between the twist and electric
flux free energies. The non-abelian content is exact: abelian twists always cost action (`no_flat_twist_comm`), while SU(2)'s −1 is a
commutator, so twist eaters make the twisted torus flat (`su2_twist_eater`). **Where the monotonicity breaks:** doubling the box compares
two volumes, and reflection positivity never relates two volumes; the scale-comparing inequalities (decimation, chessboard) are
one-sided and hold for every group. This is the step of Tomboulis's 2007 argument that Ito and Seiler showed unproven. A new unit test:
the finite subgroups of SU(2) are non-abelian and have twist eaters, yet their twist free energy is frozen at large β (exact counts:
Q8 2.04, 2T 4.11, 2O 3.89, 2I 5.07), so any argument resting only on RP, compactness and "the centre is a commutator" proves too much.
Getting past it needs a two-sided cross-volume inequality that uses twist eaters, the continuum of fluctuations (b₀ > 0) and both
directions at once.

**3. W_p.** With one noisy blocking step (as in the OpenAI construction's blocking), the coarse density is bounded below on every
configuration, which is the large-field lower bound listed as missing; per volume W_p is then equivalent to weak convergence of the
prediction laws, which holds along a subsequence by compactness (Prokhorov). Balaban's large-field papers (Commun. Math. Phys. 122,
1989) give ultraviolet stability (upper bounds), not ratio bounds; W_p does not need ratio bounds, and the volume-uniform form that would
is not needed for the gap. The price: H2 must hold for every limit point with one constant, so the running, the large-field control at
order-one coupling and uniqueness all sit in the crossover. A certified single-block test (2D SU(2) heat-kernel block, interval
arithmetic) shows the relative error falling like ℓ⁻⁴ (≤ 9.4·10⁻⁴ at ℓ = 8).

**4. Leg C** (the data side; results pending). The blocked SU(2) action at L√σ = 2.10, 3.15, 4.20 (β 2.3) and 1.55, 2.32, 3.10 (β
2.4), fitted with fundamental and adjoint couplings plus extensions for the error bar, judged against four criteria: S′ (B), D′
(attempt 1), Bakry–Émery, and C's W1 window, with a photon gate before any SU(2) run. Attempt 2's twist free-energy grid needs a new
GPU kernel (about 11 h) and is not in this run; the gradient-flow coupling is measured instead, as a different scheme.

**5. The owner's DMP route.** "YM ⊂ DMP" is made precise as a hosting (one recipe per cutoff and volume; root = the bare measure;
Duality = the two halves of a reflection; lines = blocked levels; the ledger = per-level bounds with uniform constants). DMP's own
existence is provable completeness at finite depth; the Clay question asks for the limit object, the root at infinite depth, which DMP
excludes (the owner's reading, `../PREP.md`, "Which existence"). The bridge "DMP-complete ⇒ continuum limit" fails as stated (alternating
sequences) and with compactness its hypothesis is exactly the OpenAI estimates, so the route is not shorter. Admissibility (DMP's balance
rule) is harmless at the cutoff but blocking regrows large fields (a sharp factor 4 per step), and balance at every layer contradicts the
strong-coupling area law. The one transfer the chain needs is T38, "every layer has its own Duality" (reflection positivity of each
blocked layer), proved for coarse variables on one side of the reflection plane. Triviality, photon and Z₂ tests pass: φ⁴₄ hosted the
same way comes out free, because what Yang–Mills has and φ⁴ lacks is the sign of the running (asymptotic freedom), not self-charge alone.

## The owner's readings this round

Which existence (DMP-existence at finite depth versus the limit object; the uniform-in-depth gap as the DMP-native statement); compactness
is not collapse, and where entropy and black holes do enter (the crossover: confinement as entropy beating energy; holographic
deconfinement as black-hole formation, a guide, not a proof). Both in `../PREP.md`.

## Proposed next steps

1. **Leg C** (queued): does the blocked action at L₁ land inside D′, S′, Bakry–Émery or W1?
2. **Formalise the classical rest of the quantum half**: Theorem A with exponential tails, Lemma T, the per-volume gap theorem; then H1
   leaves the list of open hypotheses.
3. **The crossover, both forms**: a certified step-scaling grid (attempt 2) needs the twist free-energy measurement (new GPU kernel,
   about 11 h, pre-registered); the D′ form needs Leg C first.
4. **T38 in full**: reflection positivity of a blocked layer including coarse links that cross the reflection plane, for a blocking built
   to respect the reflection.
5. **Adversarial review** of the round-3 chain by an independent reviewer given the code and notes, not the conclusions.
