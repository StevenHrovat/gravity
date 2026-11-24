# c7c-onebox: the one-box, worst-case-boundary criterion (cycle 7, workstream 1, 2026-11-22)

Task: state the one-box criterion (Dobrushin-Shlosman / Martinelli-Olivieri type, strategy (b) "lossless cells" of blueprint v4),
prove in Lean that it gives the gap input in every volume, handle gauge invariance honestly, name what the numerics should measure,
and run the unit tests (photon, SU(2)xU(1), 2I at weak coupling, Z2 both phases, mixture, strong-coupling SU(2)).

Lean: `formal/ProofPhase/OneBox/{Restricted,Criterion,Torus,Fine,Tests}.lean`, built in `~/formal-c8a` (`build.sh`), axioms
checked (`axioms.sh`, `axioms.log`: only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`, no new axiom).

## 0. Results in one paragraph

The criterion is a **finite-volume condition on one box under every boundary condition**: the influence of one outside cell on the
law of the box interior, measured as the expected number of box cells that must differ (modulo gauge transformations of the box
interior) when the two boundary conditions are coupled optimally, summed over all outside positions, is at most `gamma < 1` times the
box volume. **Proved (Lean, S-level):** this criterion for the SU(2) Wilson measure at the physical cell scale, uniform in the level,
gives decay of gauge-invariant correlations in every volume and, with the weakened line of constant physics, the full assembly
conclusion **without a blocking family and without the ultraviolet transfer input** (`yang_mills_assembly_onebox`). The same criterion
stated for the `L_*`-blocked laws gives `LawGapBddW`, hence `BlockGapBddW`, and plugs into `yang_mills_assembly_v4_bdd`
(`yang_mills_assembly_v4_onebox`). Gauge handling: the box influences are needed only on gauge-invariant test functions of the box with
frozen boundary (a restricted Theorem A, new); and for a gauge-covariant box specification the gauge-blind and the gauge-invariant
influences coincide (Haar alignment, section 3), so the literature workstream's worry does not apply to the criterion itself, only to
Markov-chain couplings used to estimate it. Unit tests: the two failure mechanisms are theorems (power-law correlations;
"the boundary decides", by telescoping); photon, U(1) factor, mixture fail by the first, 2I and Z2 at weak coupling by the second;
strong-coupling SU(2) passes (anchored at `OneScale.SingleLink.wilson_singleLink_decay`). **Open:** the criterion itself for SU(2)
(gap strength), and its uniformity in the lattice spacing.

## 1. The criterion

### 1.1 Objects

* Fine torus at level `k`, volume `j` (side `T.side k j`), SU(2) Wilson measure `T.ym k j`.
* **Cells** (as in `V3.CondMass`): every fine link belongs to the cell of one coarse link, `cell k j : fine links -> coarse links of
  (Z/M)^4`, `M = coarseSide j`; cells have physical size `L_1` (`CellGeometry`: two-sided comparison of physical and coarse distances).
  The fine configuration regrouped by cells (`cellLift`) has one "super-site value" per coarse link: the configuration of that cell.
* **Box**: a set `Lambda_0` of coarse sites (in practice a cube of side `ell`, `|Lambda_0| = ell^4`). Its translates
  `Lambda_0 + t` (all `t` in the coarse torus) are the blocks; the block owns all cells based at its sites (`boxBlock`, `4 |Lambda_0|`
  cells). Every coarse site is covered exactly `|Lambda_0|` times (`coverage_box`).
* **Box specification**: the conditional law of the box cells given everything outside (for the Wilson measure: the DLR formula,
  `exp(beta sum over plaquettes touching the box) x Haar`). It is gauge covariant (`SpecCovariant`).

### 1.2 The influence numbers

For a box `B = Lambda_0 + t`, an outside cell `z` (based at relative position `u = z.site - t`), a boundary condition `sigma` and a new
value `s` of the cell `z`:

    k_B(z) = sup over sigma, s, and over test functions F of the box that are
               (i)  bounded and measurable,
               (ii) invariant under every gauge transformation that fixes the boundary condition off B
                    (the gauge transformations of the box interior, and the global centre ones),
               (iii) of oscillation <= 1 under the change of any single box cell,
             of | E[F | boundary sigma] - E[F | boundary sigma with z := s] |.

By Kantorovich duality this is the Wasserstein distance, for the "number of differing cells modulo interior gauge" metric, between the
two box laws: **the expected number of box cells that must differ when the two boundary conditions are coupled as well as possible.**
`kappa(u)` is any bound of `k_{Lambda_0 + t}(z)` over all `t` and the cells `z` at relative position `u` (one number per position; by
translation invariance of the Wilson specification it does not depend on `t`).

### 1.3 The one-box sum

    OneBoxSum:   sum over relative positions u outside Lambda_0 of  kappa(u) exp(lambda E(u))  <=  gamma |Lambda_0|,    gamma < 1,

`E(u)` = distance from `u` to the far side of the box (`boxReach`). The Wilson specification has range one cell, so `kappa(u) = 0`
except on the one-cell shell around the box, and the weighted sum follows from the **unweighted check**
`sum_u kappa(u) <= gamma_0 |Lambda_0|`, `gamma_0 < 1`, with `gamma = gamma_0 exp(lambda (ell + 1))` for small `lambda > 0`
(`oneBoxSum_of_finiteRange`). In words: **the boundary influence summed over the outside of one box is less than the box volume** (the
margin beats the surface count: `~ 8 ell^3` shell positions against `ell^4` sites, so each boundary cell may disturb at most about
`ell/8` box cells in total). The decay rate obtained is `lambda / L_1`.

### 1.4 The two Lean forms

* **`FineOneBox T`** (`Fine.lean`): cells of physical size `L_1`, constants `lambda > 0`, `0 <= gamma < 1`, `D_0`, `n_max`, level
  `k_0`; for every level `k >= k_0` and volume `j`: a box of at most `n_max` coarse sites and diameter `<= D_0`, numbers `kappa`, and a
  block specification of the lifted Wilson measure whose blocks are the translates of the box, gauge covariant, with the restricted
  influences `<= kappa(z.site - t)`, and `OneBoxSum`. **Unconditioned** Wilson measure; gauge-correct; uniform in the level.
* **`OneBoxLaw rho lambda`** (`Torus.lean`): the same for any family of laws on tori (coarse links as sites, box influences tested on
  all bounded functions), used for the `L_*`-blocked laws `blockedLaw T B`.

Why "one box": the numbers `kappa(u)` are a statement about one box and its one-cell shell, under all boundary conditions; translation
invariance makes every block the same box. The criterion for `FineOneBox` is one such finite statement per level `k` at a **fixed
physical box size** `ell L_1`; the number of fine links in it grows as the spacing shrinks, so uniformity in `k` is part of the
condition (this is where asymptotic freedom has to enter; section 6).

## 2. What the numerics (c7b-onebox-num) should measure

**Granularity.** The influencer is one **cell** of physical size `L_1` (all its fine links changed at once), and disagreements are
counted in cells. A single lattice link as the boundary cell is the wrong scale: the sum beats the surface count only for cells of
the order of the correlation length (c7b's PREREG notes this correctly). Translate c7b's "patch of side b" into "one cell of side
`n = b` fine sites"; then the patch is one influencer and **no division by the number of cells in the patch** (the `S_est` formula's
linear-response division is a heuristic, not the criterion).

**The quantity.** For box side `ell` (in cells), coupling `beta`, cell side `n`:

    Q(ell) = (1 / ell^4) * sum over shell positions u of kappa(u),       criterion: Q(ell) <= gamma_0 < 1.

`kappa(u)` is a supremum over boundary conditions and over the cells at `u`; a simulation samples extremes, so a pass is "no violation
among the extremes tried". Two rigorous directions are measurable:

1. **Lower bound (conclusive failure).** For any two boundary conditions `sigma, sigma'` that differ on a set `Z` of shell cells with
   at most one cell per shell position, and any gauge-invariant observables `O_x` localised in the box cells `x`, normalised to
   oscillation `<= 1` (range divided by its width, e.g. `(1 - ReTr P/2)/2` for a plaquette, Wilson loops of the cell):

       sum over u of kappa(u)  >=  sum over z in Z of k(z)  >=  sum over box cells x of | E_sigma O_x - E_sigma' O_x |

   (telescoping: `influence_telescope`, stated in Lean for the unrestricted influence; closed loops are invariant under every gauge
   transformation, so they are admissible at every intermediate boundary condition and the restricted version follows the same way;
   the test function `F = sum_x (sign) O_x` has oscillation `<= 1` per cell). So **if `sum_x |Delta E O_x| > ell^4` for some pair, the criterion fails at that box size.** Normalise by the
   oscillation (range), not by the standard deviation, for this bound; the standard-deviation normalisation `0.4 J` of c7b is a TV
   estimate, useful but not a bound. Sum over **all** interior cells (the whole depth profile weighted by the number of cells at each
   depth), not only the centre. Whole-face and patch flips with c7b's backgrounds are exactly this measurement.
2. **Upper bound (evidence for a pass).** Two coupled heat-bath chains in the box, boundary `sigma` and `sigma` with one shell cell
   changed, run to stationarity: the expected number of box cells that differ is an upper bound for `kappa` (any coupling bounds the
   Wasserstein distance). Use the **gauge-aligned maximal coupling** (section 3.4), not plain common random numbers: a plain Markov
   coupling lets gauge mismatches persist and spread (each interior site can drift by a gauge rotation that the maximal coupling of the
   two staples cannot undo), which inflates the count without any physical influence. c7b's earlier link-level `k_hat` growing with
   `ell` (3.4, 8.9, 21 at `ell = 4, 6, 8`, beta 2.3) is consistent with that artefact plus the link granularity; it is not a test of
   this criterion.

**Backgrounds to add**: "tie" backgrounds (section 5, 2I and Z2): a boundary condition that forces a centre vortex sheet with two
symmetric minimal positions, and a single shell cell that breaks the tie. That is the configuration where a frozen-sector theory fails;
c7b's twist background is one sheet with a unique position, which tests something else.

**Gate.** c7b's G0 (a pure-gauge boundary change must not move closed gauge-invariant loops) is the right instrument check and
matches section 3.2: a pure-gauge change of the boundary moves the box law only at the links touching the transformed sites.

## 3. Gauge invariance

### 3.1 The restricted Theorem A (`Restricted.lean`, new)

In the proof of Theorem A (`Attempts.R3.theoremA_w`) the box influence is only applied to the functions `xi -> h(sigma outside B,
xi in B)`, with `h` an iterate of the test function `g` under the averaged block operator. So it suffices to know the influence on an
**admissible class** containing these functions. `theoremA_on`: if `g` lies in a class `Inv` closed under the averaged block
operator, and members of `Inv` frozen off a block are admissible for that block (`AdmData`), Theorem A holds with influences tested
only on admissible functions. `admData_of_covariant` (`Criterion.lean`): for a coordinatewise action (the gauge group acts on each link
separately) and a covariant specification, `Inv` = invariant functions, `Adm` = functions invariant under every group element fixing the
boundary condition off the block, satisfy this.

### 3.2 Pure-gauge boundary changes are harmless (exact)

If the boundary condition is changed by a gauge transformation `g` at outside sites, then the box law with the new boundary is the old
box law transformed by `g` on the box links touching those sites (the Wilson weight and the Haar prior are gauge invariant). Under the
coupling `U -> U^g` only those links differ: the influence of a pure-gauge change of one outside cell is the handful of box cells
touching it, a boundary-layer term. **Not** "about the box volume".

### 3.3 Gauge-blind = gauge-invariant influence (Haar alignment; paper proof)

Let `K` be the compact group of gauge transformations of the box interior (they fix every boundary condition), acting coordinatewise
and bijectively on box cells, and `q, q'` two box laws invariant under `K` (true for the DLR box laws under any two boundary
conditions). Let `d_H` count differing cells and `d~(xi, xi') = min_{h in K} d_H(xi, h xi')`. Then

    W_{d_H}(q, q') = W_{d~}(q, q').

Proof: `>=` since `d~ <= d_H`. `<=`: take an optimal coupling `(xi, xi')` for `d~`, a measurable minimiser `h*(xi, xi')`, and an
independent Haar `g`; set `X = g xi`, `X' = g h* xi'`. Given `(xi, xi')`, `g` and `g h*` are both Haar, so `X ~ q` and `X' ~ q'` by
invariance; and `d_H(X, X') = d_H(xi, h* xi') = d~(xi, xi')` because `g` acts coordinatewise and bijectively. QED. By duality
`W_{d~}` is the influence tested on `K`-invariant functions. Consequence: the gauge-blind criterion (`OneBoxLaw`, all bounded test
functions) and the `K`-restricted one coincide; the Lean `FineOneBox` restricts further to functions invariant under the whole
boundary stabiliser (interior gauge plus the global centre elements that fix the boundary), which is weaker still, hence implied.
So gauge invariance costs nothing in the criterion; no gauge fixing and no orbit metric are needed. (Formalising 3.3 needs couplings
and Kantorovich duality, not in the library; it is not used by the Lean theorems, which take the restricted form directly.)

### 3.4 Where the warning is right: Markov couplings

A coupled pair of Monte-Carlo chains is a Markov coupling, not an optimal one, and it does not use the Haar freedom. Gauge mismatches
then look like physical disagreements. **Gauge-aligned maximal coupling** (for the upper bound of section 2): keep a gauge label `h_x`
per interior site (start at 1); to update link `e = (x, y)` with staples `S` (chain 1) and `S'` (chain 2), align `S'' = h_y^{-1} S' h_x`
(in the convention where the weight is `exp(beta/2 ReTr(U_e S_e))`), draw `(U, U~)` from the maximal coupling of the heat-bath laws for
`S` and `S''`, and set `U'_e = h_x U~ h_y^{-1}`. Chain 2 keeps exactly its own heat-bath law for any choice of labels (the Haar prior and
the weight are invariant), gauge-related staples give gauge-related links, and the count "cells containing a link with
`U'_e != h_x U_e h_y^{-1}`" bounds `d~` from above. The labels may be re-chosen at any time as a function of the current pair (for
example to the value that aligns most links at that site).

## 4. The Lean theorems (exact statements)

Generic layer (group-blind):

* `theoremA_on` (`Restricted.lean`): `|Cov_mu(f, g)| <= b/(c_-(1-gamma)) (c_+ sum_A v_f) L_g e^{-lambda(R - D_0)}` for `g` in an
  invariant class, under `AdmData`, restricted influences `IsInfluenceBoundOn`, and `GDSw` (as `theoremA_w`).
* `abs_cov_le_of_oneBox` (`Criterion.lean`): for a block specification whose blocks are the translates of one box (`IsBoxFamily`,
  `|Lambda_0| >= 1`, block sizes `<= b`, diameters `<= D_0`), covariant under a coordinatewise measurable action, with restricted
  influences `<= kappa(rel j z)`, reach `E`, and `OneBoxSum kappa E Lambda_0 lambda gamma`:
  `|Cov(f, g)| <= b/(1 - gamma) (sum_A v_f) L_g e^{-lambda(R - D_0)}` for `g` invariant.
* `gdsw_of_oneBox`, `coverage_box`, `sum_box`: the one-box sum **is** the weighted Dobrushin-Shlosman condition for the box family.
* `oneBoxSum_of_finiteRange` (`Torus.lean`): unweighted check plus finite range gives the weighted sum.

The real objects:

* `fineDecayInv_of_fineOneBox : FineOneBox T -> FineDecayInv T`, where `FineDecayInv T` = one rate `m > 0`; for every physical
  extent `R` a constant `c` and a level `k_0` such that for `k >= k_0`, every volume, bounded measurable `F`, `G` (`G` gauge invariant,
  `F` of physical extent `<= R`) at physical distance `>= D`: `|Cov_{T.ym k j}(F, G)| <= c e^{-m D}`. Rate `lambda/L_1`, constant
  `4 n_max/(1-gamma) * 2 K_R * 2 * e^{lambda (c_0 + D_0)}`, `K_R = 4(2 floor(R/L_1 + c_1) + 1)^4`.
* `torusDecayLoc_of_fineDecayInv : FineDecayInv T -> TorusDecayLoc T.toV`.
* **`yang_mills_assembly_onebox (hL : OnLCP' T) (hN : NonTrivial T) (h : FineOneBox T) : TorusDecayLoc T.toV ∧ MassGapLoc T ∧
  MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T`.**
* `lawGapBddW_of_oneBoxLaw (hlam : 0 <= lambda) (hrho : all laws probability) (h : OneBoxLaw rho lambda) : LawGapBddW rho lambda`
  (constant `2 * 4 n_max e^{lambda D_0}/(1 - gamma)`).
* `blockGapBddW_of_oneBoxLaw : OneBoxLaw (blockedLaw T B) lambda -> BlockGapBddW T B lambda`.
* **`yang_mills_assembly_v4_onebox (hL : OnLCP' T) (hN : NonTrivial T) (B) (hlam : 0 < lambda)
  (hIR : OneBoxLaw (blockedLaw T B) lambda) (hUV : ObsTransferPhysTW T B)`: the v4 conclusions** (via `yang_mills_assembly_v4_bdd`).

**Extra premises, named.** Beyond `CellDobrushin`'s content (which is the global DS condition) the one-box route needs nothing of
physical substance: the translation structure is proved (`IsBoxFamily` for torus boxes), the coverage is exact. The only premises
that are properties of the specification rather than numbers are (a) the existence of a box specification of the lifted Wilson
measure (standard: the DLR formula) and (b) its gauge covariance (`SpecCovariant`, standard). Neither is constructed in Lean here
(constructing the lifted DLR specification is a mechanical follow-up: `OneScale.productBlockSpec` with plaquette weights, pushed
through `cellLift`). For **Chatterjee's Definition 2.3** (decay under arbitrary boundary conditions in every cube, uniform constants;
literature workstream) the same proof applies to the cube measure with its outside frozen, with the blocks cut by the cube's walls;
the extra premise is **the one-box sum for the box cut by walls** (the influences on `(Lambda_0 + t)` intersected with a cube are also
`<= kappa`; finitely many cut shapes). Coverage stays `|Lambda_0|`. Not formalised.

## 5. Unit tests

Two mechanisms, both theorems (`Tests.lean`):

* **(P) power-law or persistent correlations**: `not_oneBoxLaw_of_power`: covariances `>= c R^{-p}` at arbitrarily large distance
  `R` exclude `OneBoxLaw` at every `lambda > 0` (`not_lawGapBddW_of_power`); `not_fineOneBox_of_not_torusDecayLoc` for the fine form.
  The generic theorem `abs_cov_le_of_oneBox` is group-blind, so the contrapositive applies to any group.
* **(T) the boundary decides**: `influence_telescope`: the influence sum over the boundary is at least the distance of the box laws
  under any two boundary conditions. A model with two boundary-selected states of the interior (phases, sectors) has
  `sum_u kappa(u) >= theta * (cells of the box)`, `theta` the fraction of cells moved; the criterion fails once that exceeds
  `gamma |Lambda_0|`. This mechanism fails models whose local correlations **do** decay: the criterion is strictly stronger than decay.

| model | verdict | reason in the criterion's own terms |
|---|---|---|
| photon (free U(1)) | fails at every box size | (P): `<F F> ~ |x|^{-4}`. Own terms: the boundary-anchored phases (admissible: invariant under interior gauge) respond to boundary data through the Poisson kernel `P(x, z)`, and **harmonic measure sums to one**: `sum_z P(x, z) = 1` for every interior `x`. With a response amplitude `A = (boundary change)/(fluctuation) >= 1` (weak coupling, or unbounded data for the non-compact photon) the per-cell TV is `>~ min(1, A P(x, z)) >= P(x, z)`, so `sum_z kappa(z) >= sum_x sum_z P(x, z) = ` box volume: `gamma >= 1` independent of `ell`. A massive field has `sum_z P_m(x, z) ~ e^{-m dist(x, boundary)}`, total `~ xi * surface`, and passes once `ell >> xi log A` (classical estimate, not a proof) |
| SU(2) x U(1) | fails | product measure: covariances of U(1) observables are covariances of the product; (P) through the U(1) factor (Coulomb phase of compact U(1) for `beta > ~1.01`; at all `beta` for the free photon) |
| 2I at weak coupling | fails, uniformly in the cell size | (T), frozen sectors: a vortex sheet of a discrete group costs `>= c beta` per unit area at every thickness (c6c 2.3), so a boundary forcing a sheet with two symmetric minimal positions is a sharp tie; one shell cell breaks it and moves the cells along the swept region (`~ ell^3` of them, at every shell position) : `sum_u kappa(u) ~ ell^6 >> ell^4`. Local correlations still decay (2I's frozen theory is gapped in lattice units), so (P) does not see this: the worst-case boundary is what separates 2I from SU(2), where thick vortices get cheaper as they widen and no sharp ties survive at scales `>> xi` (continuity). Classical estimate |
| Z2 gauge, confined (small beta) | passes | strong coupling: single-link Dobrushin as for SU(2) below; at larger boxes up to the transition, but the needed `ell` grows near the first-order point (metastable deconfined droplets in small boxes) |
| Z2 gauge, deconfined (large beta) | fails | (T) as 2I (discrete group, sharp sheet ties); local correlations decay (perimeter-law, gapped), so again only the worst-case boundary sees it. c7b's pilot (beta 0.6, calm/twist) shows only boundary-layer influence because it has no tie background |
| mixture of two phases | fails | (P) with `p = 0`: `Cov(f, f o shift_R) -> (E_1 f - E_2 f)^2/4`. Own terms (T): boundary conditions from phase 1 and phase 2 move the interior by `theta * volume`, telescoped over the shell: `gamma >= theta(1 - O(1/ell))` |
| Ising (calibration) | high T passes, low T fails | DS 1985 / Martinelli-Olivieri; low T by (T) with `theta -> 1` |
| SU(2), strong coupling | passes | anchor: `OneScale.SingleLink.wilson_singleLink_decay` is Theorem A with the box a single link: `18 tanh(2 beta) < 1`, i.e. `beta < ~0.0278`, is the one-box sum for that box (coverage 1). For cubic boxes of cells: a boundary cell disturbs only adjacent cells (correlation length below one lattice unit), `kappa(u) <= c` with `c` a few cells, so `Q(ell) ~ 8c/ell < 1` for `ell > 8c`, uniformly in the cell size. Paper (block influences from single-link Dobrushin by the comparison argument, standard) |

Claim level: the two mechanisms are proved; the model verdicts are classical estimates except the photon/U(1)/mixture verdicts,
which follow from the proved (P) and the known power-law or persistent correlations of those models.

## 6. Relation to the rest, and next steps

* **Versus `CondMass` (c4a):** `CondMass` is the same DS form for the fine field **conditioned on the block field**; it holds for the
  photon in the time direction and is not the gap. `FineOneBox` is the unconditioned version: gap strength, and the photon fails it.
* **What the fine route removes:** no blocking family, no `ObsTransferPhysTW` (Lemma UV): `yang_mills_assembly_onebox` has the single
  input `FineOneBox` besides identification. What it does not remove: uniformity in the level. At fixed physical box size the box has
  `(ell L_1 / a_k)^4` fine links; the influence counts cells, so the criterion is a dimensionless statement at the cell scale (the TV
  of a whole cell under a smooth boundary response is governed by the response's action in the cell, scale invariant classically), and
  its uniformity in `a_k` is where asymptotic freedom must enter. A computer-assisted check is per level, not one finite check.
* **The `L_*` law route** is one finite statement if the `L_*` theory is fixed, but its box specification is not explicit (conditional
  law given blocked variables); numerically it would need simulations constrained on block variables. The fine route is the one the
  numerics can test now.
* **Next steps.** (1) c7b: measure section 2's lower bound with osc-normalisation and full-depth sums, cell-sized influencers, and tie
  backgrounds; then the gauge-aligned coupled upper bound at one box size (`ell ~ 8` cells of size `~ xi`). (2) Lean: construct the
  lifted DLR box specification and prove `SpecCovariant` (mechanical), so `FineOneBox` refers to the actual Wilson specification
  rather than an existential one; then the strong-coupling instance of `FineOneBox` for boxes of cells (block influences from
  single-link Dobrushin). (3) The wall-cut version for Chatterjee's Definition 2.3 (unbroken centre, area law downstream).
  (4) Mathematics: the uniformity in the level, i.e. a proof that `kappa` at the cell scale does not grow as `a -> 0` (perturbative at
  short distances, where the boundary response is the free one; the cell count makes the free response's harmonic-measure total
  depend only on the response amplitude in units of the cell fluctuation).

## 7. Files and commands

* Lean: `formal/ProofPhase/OneBox/Restricted.lean` (restricted Theorem A), `Criterion.lean` (gauge and translation layers, the
  one-box theorem), `Torus.lean` (torus boxes, finite range, law route, v4 assembly), `Fine.lean` (lifted gauge action, fine route,
  assembly), `Tests.lean` (failure mechanisms).
* Build: `wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c7c-onebox/build.sh
  ProofPhase.OneBox.Tests` (one-time `setup.sh` copies `~/formal/.lake` to `~/formal-c8a`); axioms: `axioms.sh` -> `axioms.log`.
