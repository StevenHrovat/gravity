# Part III. Yang-Mills: the gap mechanism reduces to one box of fixed physical size

*Draft 6. Prose, with every result marked. Lean paths relative to `docs/mass-gap/formal/ProofPhase/` (the modules of the earlier
attempt rounds R2 to R4 live under `docs/mass-gap/formal/Attempts/`); notes relative to `docs/mass-gap/weak-coupling/`; the crossover notes are in
`proof-phase/c9a-crossover/`. The full chain with all 51 pieces is in `PROOF-BLUEPRINT.md`. Claim labels (III.n) are listed in
`../CLAIMS.md`.*

**Plug in here.** Gives: the SU(2) lattice mass gap reduced to one criterion on one box of fixed physical size, O1.
Needs: II.4.1, the ledger (II.1) and the tools of II.12. Route: the exact route, stop 3. VIBE coefficient: the boxes double from level
to level, and the doubling law with a fixed loss gives the gap on all larger dyadic boxes (an implication, III.3.7) **[Lean]**;
rigorously log mu_4 >= log 4 = 2 log 2 **[classical]**; III.5.6 reads O1's familiar form as dropping a momentum term, as R.12n reads
E = mc^2 **[reading]**.

**Contracted.** Sections and labels this part names but does not print are in the full Draft 6, the git tag `d6-full`, and in Draft 5 section by section; every label is a row of `../CLAIMS.md` with its status and evidence.

**As a statement checked step by step (II.4.1).** The steps are the lattice levels from a first level k0 of one box of fixed
physical size; the statement checked at each level is the level criterion, the box's best one-box ratio within the margin. For some
cell geometry and margin this holds at every level exactly when O1 holds in its Lean form **[Lean]** (`FineOneBox`,
`fineOneBox_iff_complete`, III.12). Here the inductive step, from each level to the next, carries the content; the split into the
first level and the step is exact (`route_iff`), not a method of proof. The card's own box (`YMOneBox`) checks the chain form at every
step, so there the open part is the base case.

## III.0 What is proved and what is not

**The Clay statement** (Jaffe-Witten, official problem description): for every compact simple gauge group G, a non-trivial quantum
Yang-Mills theory exists on R^4 and has a mass gap Delta > 0, that is, the Hamiltonian has no spectrum in (0, Delta). Existence
includes axiomatic properties at least as strong as the Wightman and Osterwalder-Schrader axioms, with local gauge-invariant fields;
the description also asks that the short-distance correlation functions of those fields agree with asymptotic freedom and
perturbative renormalisation.

**This part does not prove it.** For SU(2) it proves two things.

1. **The minting half** (I.5): from a gap certificate at one box scale to the mass gap of the lattice theory in both orders of
   limits, with reflection positivity of the limit **[Lean]**, conditional on stated inputs (III.2). The Lean gap is a decay
   statement for slab correlations of bounded physical extent along a tuning; the step to a gap of the Hamiltonian on a Hilbert
   space is III.2.7 (**[paper]**).
2. **The global structure of the pressing half**: a per-box rate in one of two channels, a conserved carrier that no collar can
   screen, superadditivity along a chain, uniformity along it, and the conversion to physical units. Together they reduce the
   **gap mechanism** to one statement about one box **[Lean]** + **[classical]** (III.3). Sections III.4 and III.5 show why that box
   statement is harder for a grid of boxes than for a chain, and sharpen it to one number.

It leaves four things open.

* **(O1) The one-box statement** (III.5.6). In its Lean form O1 is `FineOneBox` (III.5.9): one box of fixed physical size whose
  influence bounds, under every boundary condition, satisfy a one-box sum below one, uniformly in level and volume. The number
  attached to it is path counting (**[paper]**, III.5.9): the electric flux free energy must exceed the path entropy of the
  four-dimensional lattice after the neutral excess act, **F_e(L) - 2C > log mu_4 = 1.91**, with C a bound on the excess act c(L)
  on every multiple of L (III.3, III.5.8). That is a sufficient route to the one-box sum, not a necessary one, and F_e(L) in it is
  the torus free energy of III.3; "uniformly over every well-defined outside" is the content of the Lean form, and for the number it
  is a heuristic (III.5.7). The familiar
  form drops the excess act and reads F_e(L) > 1.91 (twist ratio r(L) > 0.74); it is weaker and alone does not give the chain
  (III.5.8). In effective-string units the familiar form asks for a box of side L sqrt(sigma) of about 1.7 to 1.8 (III.7.4,
  model evaluation, **[numerical]**); the full form asks for at least that.
* **(O2) The identification inputs**: the line of constant physics (OnLCP) and non-triviality, the two hypotheses that make the
  lattice family Yang-Mills and not some other gapped family (III.9). The gap itself needs of the line of constant physics only its
  resolution clause (III.9.5, **[Lean]**). Per box, the reflected correlation at even time is a reflection-positivity square, hence
  non-negative for observables of the positive half (III.9.5a, **[Lean]**). That is not non-triviality: pure noise has correlation
  zero and passes it too. Non-triviality needs a scale-uniform lower bound c > 0. That lower edge and the scheme clause (III.9.5b)
  are what remains; they are the opposite edge to O1's decay, independent of O1 in the spectral model, and **[open]**. On the
  first author's reading they are not a second assumption: the ODP ends only at a dimensionless 1, so a running, DMP-complete system carries
  the lower edge by construction, and III.9.5b is the lower edge of the one assumption, beside O1's upper edge, placed at the ODP's
  end, the certified start `{infinity, 2, 3}` (Part X 4.4, X.64a, **[reading]**). Under that reading nothing more is to be
  shown at the start, and the direction of every later tick is **[conditional]** on the one assumption (X.66).
* **(O3) The continuum field theory**: Euclidean invariance, local fields as distributions, uniqueness of the limit, Wightman
  reconstruction, and short-distance agreement with asymptotic freedom. The external construction this project uses (III.9: a Lean 4
  submission of 28 October 2026 and the hosting group's assessment of 10 November 2026, not refereed) is assessed there, as the
  assessors' opinion, to give a Wightman theory as a scaling limit of Wilson lattice gauge theory, in a selected phase, along a
  subsequence in the volume, with fields smeared against tests away from coincident points **[external]**. Its sources say it does
  not prove uniqueness of the infinite-volume limit or a mass gap, so uniqueness of the limit is **[open]** for it as for this
  project's own objects. For this project's own objects, rotation invariance cannot yet be stated, since the lattice has only the
  hypercubic group **[open]**.
* **(O4) Other groups**: the Lean setting has a tuning for SU(2) only. The SU(N) package and the audit of what generalises are
  partial (`General/`, `proof-phase/GENERALISE-AUDIT.md`).

The title's "one box" is exact for the gap mechanism (O1). It is not true of the Clay statement as a whole, which also needs O2 to
O4.

## III.5 Containment: the requirement moved inside one box

The first author's correction ("the saturation has to be proven inside confinement and absent outside that confinement, as a containing
existence", `PREP.md`) reverses the direction of the attack. Instead of building the inside of a box from outside data, prove three
things: outside, saturation is absent; the container ends; inside, saturation makes the influence run in tubes, and tubes are chains,
where III.3 closes. The first two close. The third closes negatively at the duality floor and positively above a sharp threshold.

The steps between, outside absence (III.5.1), the container's ends (III.5.2), what the law gives (III.5.3), what the cost must give
(III.5.4, with the path-sum threshold log mu_4) and what the action adds (III.5.5), are in the full text.

**III.5.6 The one-box statement (O1).** Combining III.5.3 and III.5.4: law (structure) plus cost above entropy (dominance) gives tubes,
and tubes are chains, where III.3 applies. What remains is:

> **(O1)** At one box of fixed physical size, F_e(L) - 2C > log mu_4 = 1.91, with C a bound on the neutral excess act c(kL) of III.3
> on every multiple of L; in its Lean form, `FineOneBox` (below), uniformly over every boundary condition. **[open]**

The familiar form F_e(L) > 1.91 (equivalently r(L) > 0.74) drops the excess act, as E = mc^2 drops the momentum term of
E^2 = p^2 c^2 + m^2 c^4 (a **[reading]**). The drop is only seeming: c >= 0, so the full form implies the familiar one, but the
familiar one alone does not give the chain criterion (III.5.8, examples in Lean). The number 1.91 is a series estimate for log mu_4 **[numerical]**; rigorously it lies between 1.39 and 1.95 (III.5.4). It is path counting (**[paper]**, III.5.9);
it is a sufficient route to the one-box sum and is stated for the torus free energy F_e of III.3, not for every outside.

This is the grid requirement log 8 = 2.08 of III.4.1 refined from column sums to path counting. Containment moves the requirement
inside the box but does not lower it to the chain value 0.881.

**Care points.**
* **O1 in one form.** The Lean form of O1 is `FineOneBox` (`OneBox/Fine.lean`); reading the number above as its one-box sum is
  path counting (**[paper]**, III.5.9). `FineOneBox` is one box at the physical cell scale, influence bounds under every
  boundary condition, uniform in level and volume. `WilsonOneBox` and `FineOneBoxSplit` imply it, and it feeds
  `yang_mills_assembly_onebox`; `BlockGapBddW` belongs to the separate blocking route (III.5.9, **[Lean]**).
* **O1 in the one-box test.** In the one-box test (II.4, the rotation API) O1 is exactly DMP-completeness of the Yang-Mills box:
  the chain form holds exactly when some margin makes every chain of outsides DMP-complete, and `FineOneBox` holds exactly when the
  Yang-Mills box, with its geometry fixed across levels, is DMP-complete from its start level **[Lean]** (III.12). Both
  directions are proved, so the general test carries exactly O1, no more and no less: a restatement by construction, which proves
  no new bound. That the box is DMP-complete is O1 itself
  **[open]** (III.10e).
* **Per-box costs multiply.** In that per-outside form the composition of the per-box influences is a theorem, so no annealed
  quantity enters the gap; the annealed-to-quenched identification is needed only to read a torus measurement of F_e as evidence
  about O1 (III.5.7, **[Lean]**).
* **Chain and tube.** In the transfer-matrix model the chain criterion F_e(L) > 2C (C bounding c(kL) on the multiples of L) and the tube threshold F_e(L) > log mu are
  independent, with examples both ways; the joint form gives both (III.5.8, **[Lean]**, model).

| # | Result | Status | Source |
|---|---|---|---|
| III.5.1a | r < 1, r = (1 - e^{-F_e})/(1 + e^{-F_e}) <= F_e, F_e >= 0 | **[Lean]** | `Crossover/Containment.lean`, `twist_ratio_eq`, `twist_ratio_le_elecF`, `elecF_nonneg` |
| III.5.1b | Small box: F_e = O(g(L)^2) | **[classical]** (recalled) | `CONTAINMENT.md`, 1 |
| III.5.2a | At fixed cross-section F_e(T) grows without bound | **[Lean]** core + **[classical]** (Jentzsch) + **[paper]** (centre invariance) | `Containment.lean`, `elecF_lower_of_gap`, `exists_elecF_ge`; `CONTAINMENT.md`, 2 |
| III.5.2b | Cubic boxes: F_e(L) >= 0.881 at some L | **[open]**; near L = 4 at beta 2.3 **[numerical]** | `CONTAINMENT.md`, 2 |
| III.5.3 | Gauss's law makes influence path-like (no sources, unscreenable) | **[Lean]** pieces + **[paper]** | III.3.2, III.3.3; `CONTAINMENT.md`, 6.1 |
| III.5.4a | Path sums converge iff F > log mu; 0.881 loses for mu >= 3 | **[Lean]** | `Containment.lean`, `path_sum_summable_iff`, `tube_threshold`, `path_entropy_beats_handover` |
| III.5.4b | log mu_4 in [1.39, 1.95] (rigorous); mu_4 = 6.77 (series estimate, numerical) | **[classical]** (recalled) | `CONTAINMENT.md`, 3 |
| III.5.5 | Bogomolny floor helps outside only and loses to entropy as a -> 0 | **[classical]** (bound) + **[paper]** (sketch) | `CONTAINMENT.md`, 6.2 |
| III.5.6 | **(O1)** F_e(L) - 2C > log mu_4 at one box of fixed physical size, C bounding the excess act on the multiples of L (Lean form `FineOneBox`, III.5.9; familiar form F_e(L) > log mu_4, the excess act dropped) | **[open]** | `CONTAINMENT.md`, 0 and 5; `docs/OPEN-QUESTIONS-DMP.md`, 0 |
| III.5.7 | Per-box costs multiply over the lattice in O1's per-outside form; annealed to quenched only for reading measurements | **[Lean]** | `OneBox/Fine.lean`, `fineDecayInv_of_fineOneBox`; `Closures/OneBoxForm.lean` |
| III.5.8 | Chain criterion and tube threshold independent in the model; the joint form gives both | **[Lean]** (model) | `Closures/ChainJoint.lean`, `joint_gives_both`, `tube_not_chain`, `chain_not_tube` |
| III.5.9 | O1 in one Lean form: `FineOneBox`, with the other forms linked; reading the number of III.5.6 as its one-box sum is path counting, **[paper]** | **[Lean]** | `OneBox/Fine.lean`; `Closures/OneBoxForm.lean` |

## III.11 What would close it

O1 first: a worst-case argument, for one box of fixed physical size, that the one-box sum of `FineOneBox` holds under every boundary
condition (by the number F_e(L) - 2C > log mu_4, the electric cost per box exceeding the path entropy of the four-dimensional lattice, if
path counting is the route), together with the per-box product structure along paths (III.5.7). Then O2:
its scale-uniform lower edge (III.9.5b), open and part of the one assumption by a reading, beside O1 (Part X 4.4); the per-box half is proved and the gap uses only the resolution clause. Then O3: an observable bridge from this project's bounded slab
observables to local fields, or adoption of the external construction's field notion with its audit. Then O4: a tuning for general G.
O1 is the mathematical core; O2 to O4 are the remaining distance from the gap mechanism to the Clay statement.

## III.12 The box in the one-box test

**The box.** For a tuning T and a cell geometry g (a cell map at every level and volume with physical cell size L_1, constants
n_max and D_0, and a positive rate), the Yang-Mills box `ymBox T g theta` has the lattice levels k from k_0 as its ticks, floor 0,
margin theta < 1 and the marker "inside" at every level. Its gate factor at level k is `ymFac T g k`: the best one-box ratio gamma
for which the level criterion holds in every volume, and 1 when no ratio below 1 works. The level criterion (`LevelBox`) asks for a
box Lambda_0 of at most n_max sites and diameter at most D_0, a gauge-covariant block specification on it, an influence bound on
it from every outside cell, and the one-box sum of those bounds below gamma **[Lean]** (`ETM/RotationInstances.lean`, `LevelBox`,
`ymFac`, `ymBox`).

**What the test gives.** For a fixed geometry the box is DMP-complete from k_0 for some margin exactly when one ratio gamma < 1
satisfies the level criterion at every level from k_0 (`ym_complete_iff`); over all valid geometries this is exactly `FineOneBox`
(`fineOneBox_iff_complete`); and a DMP-complete box gives the one-box assembly, decay, the gap in both orders of limits and
reflection positivity, with the line of constant physics and non-triviality as inputs (`ym_assembly_of_complete`) **[Lean]**
(claims III.10c, III.10d). The chain form has its own box, `o1Box`, with gate factor min(1, e^-F_e) along a chain of outsides; it is
DMP-complete for some margin exactly when the chain-form bound holds (`o1_iff_complete`) **[Lean]**. Because `ymFac` is defined as
the best ratio, both equivalences are restatements by construction and prove no new bound. That the box is DMP-complete is O1
itself **[open]** (claim III.10e).

## III.13 O1 as a Perelman-typed interface

*New in Draft 6.* The first author reads O1 as constructable as a PP (Perelman-Poincare) typed, Yang-Mills shaped interface API
(R.11e). Draft 6 builds it **[Lean]** (`ProofPhase/API/Perelman.lean`, axioms in `docs/unified/perelman-axioms.log`). It is called
the counting ledger below, to keep it apart from the ledger law of II.1 and the claims ledger.

**Two toys first.** Take a sequence of numbers and the statement "at step k the number is at most Γ", with Γ < 1. The sequence
1 - 1/(k + 2) tends to 1, so it exceeds every such Γ from some step on: the statement fails at arbitrarily late steps, and the
interface rejects it (`gapless_rejected`). A constant sequence at most its bound never fails, and the interface accepts it
(`gapped_accepted`) **[Lean]**. These sequences are called one-box sums only for the illustration; the free photon of R.11e is not
modelled in the Lean.

**The counting ledger as a type (claim III.13a).** Perelman's finite-surgery argument counts: each surgery removes at least a definite
volume, the volume is bounded, so on a finite interval [0, T] there are finitely many surgeries (A.1, the row "number of steps").
The interface takes exactly that count. Along the steps there is a quantity W, non-decreasing and bounded above, and a quantum q > 0
that W gains at every step where the statement fails, a boundary event (`Ledger`). From these, the statement holds at every step from
some step on (`Ledger.eventually`) **[Lean]**. Care: in Perelman's proof the count runs on [0, T] and on volume, a different quantity
from the monotone W-entropy (A.1c); here W plays the role of the cumulative volume removed, over all steps. The type accepts exactly
the statements that hold from some step on and rejects those that fail at arbitrarily late steps (`no_ledger`) **[Lean]**; the two
toys above are one of each.

**Typed for the Yang-Mills box (claim III.13b).** The steps are the lattice levels, and the statement at level k is the one-box
criterion of `FineOneBox` in every volume, with the shared cell geometry and constants (`BoxAt`, `Interface`) **[Lean]**:

* an instance gives O1 in its one form (`o1Form_of_interface`);
* with the resolution clause of the line of constant physics it gives torus decay, the gap in both orders of limits and reflection
  positivity (`gap_of_interface`, through III.9.5);
* O1 gives an instance, with W a counter of the levels before the box holds, one quantum each (`interface_of_o1Form`);
* so the interface is exactly O1 (`interface_iff`).

Like III.12, it is a restatement and proves no new bound. Since W may be a counter, the ledger is equivalent to the box holding from
some level on; the open content is the ledger together with the choice of cell geometry and constants that makes it hold **[open]**
(claim III.13d).

**What the reading asks, and where it stops (claim III.13c).** The first author: the question being assigned `+` and `-` is the
proof of the eigenvalue O1, from which all else is constructable through this interface **[reading]** (R.11e). Exact parts: as for
O1 itself (III.9.5), an instance gives the gap **[Lean]**; the interface supplies no instance, and assigning `+` and `-` is `?`, not
`!` (R.11e). Perelman's monotone W-entropy buys a sign, not a rate (A.2), and his count runs on volume. In four dimensions the
coefficient a is larger at the ultraviolet end of a renormalization group flow than at the infrared end (the a-theorem;
Komargodski-Schwimmer 2011, a field-theoretic argument); it compares the endpoints and is not shown to decrease monotonically along
the flow **[classical]**. Neither supplies the quantum per failing level that the interface asks for.
