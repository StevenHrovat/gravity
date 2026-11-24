# Part IV. Yang-Mills: the gap mechanism reduces to one box of fixed physical size

*Draft 2, 2026-11-23. Prose, with every result marked. Lean paths relative to `docs/mass-gap/formal/` (the modules of the earlier
attempt rounds R2 to R4 live under `Attempts/`); notes relative to `docs/mass-gap/weak-coupling/`; the crossover notes are in
`proof-phase/c9a-crossover/`. The full chain with all 91 pieces is in `PROOF-BLUEPRINT.md`. Claim labels (III.n) are listed in
`../CLAIMS.md`.*

## IV.0 What is proved and what is not

**The Clay statement** (Jaffe-Witten): for every compact simple gauge group G, a quantum Yang-Mills theory on R^4 exists, satisfying
the Osterwalder-Schrader or Wightman axioms with local gauge-invariant fields, and has a mass gap Delta > 0.

**This part does not prove it.** For SU(2) it proves two things.

1. **The minting half** (I.5): from a gap certificate at one box scale to the mass gap of the lattice theory in both orders of
   limits, with reflection positivity of the limit **[Lean]**, conditional on stated inputs (IV.2).
2. **The global structure of the pressing half**: a per-box rate in one of two channels, a conserved carrier that no collar can
   screen, superadditivity along a chain, uniformity along it, and the conversion to physical units. Together they reduce the
   **gap mechanism** to one statement about one box **[Lean]** + **[classical]** (IV.3). Sections IV.4 and IV.5 show why that box
   statement is harder for a grid of boxes than for a chain, and sharpen it to one number.

It leaves four things open.

* **(O1) The one-box statement** (IV.5.6). There is a box of fixed physical size at which the electric flux free energy exceeds
  the path entropy of the four-dimensional lattice after the neutral excess act, **F_e(L) - 2c(L) > log mu_4 = 1.91**, uniformly
  over every well-defined outside. As E = mc^2 is E^2 = (pc)^2 + (mc^2)^2 with the momentum term dropped, the familiar form drops the
  excess act and reads F_e(L) > 1.91 (twist ratio r(L) > 0.74); it is weaker and alone does not give the chain (IV.5.8). In
  effective-string units the familiar form asks for a box of side L sqrt(sigma) of about 1.7 to 1.8 (IV.7.4, **[numerical]**); the
  full form asks for at least that.
* **(O2) The identification inputs**: the line of constant physics (OnLCP) and non-triviality, the two hypotheses that make the
  lattice family Yang-Mills and not some other gapped family (IV.9). The gap itself needs of the line of constant physics only its
  resolution clause (IV.9.5, **[Lean]**). Non-triviality holds per box by construction: the reflected correlation at even time is a
  reflection-positivity square, so it is at least zero at every level (IV.9.5a, **[Lean]**). What remains is the scale-uniform
  lower edge and the scheme clause (IV.9.5b, **[open]**), the opposite edge to O1's decay. It is not a second assumption: the
  ODP ends only at a dimensionless 1, so a running, DMP-complete system carries the lower edge by construction, and IV.9.5b is the
  lower edge of the one assumption, beside O1's upper edge (Part III 4.4, **[reading]**). It is placed exactly at the ODP's end, the
  certified start `{infinity, 2, 3}`; from there it follows for a DMP-complete system with nothing more to show, so it is
  **conditional** on the one assumption, as the direction of every later tick is (III.66).
* **(O3) The continuum field theory**: Euclidean invariance, local fields as distributions, uniqueness of the limit and Wightman
  reconstruction. For the external construction this project uses (IV.9) these are claimed there **[external]**. For this project's
  own objects, rotation invariance cannot yet be stated, since the lattice has only the hypercubic group **[open]**.
* **(O4) Other groups**: the Lean setting has a tuning for SU(2) only. The SU(N) package and the audit of what generalises are
  partial (`ProofPhase/General/`, `proof-phase/GENERALISE-AUDIT.md`).

The title's "one box" is exact for the gap mechanism (O1). It is not true of the Clay statement as a whole, which also needs O2 to
O4.

**What changed since draft 1.** Draft 1 stated O1 as "the loss rate of one box is below one". The crossover rounds of the same day
showed that the per-box rate 0.881 suffices for a chain of boxes but not for a grid (IV.4), and that it suffices for a grid exactly
when the influence runs in tubes, which needs a larger electric cost per box (IV.5). O1 is now one number at one scale.

## IV.1 The lattice theory and its positivity (G0 by construction)

Yang-Mills is the one problem of the three whose starting positivity is given. The Wilson weight e^{-S} is positive and local, and
from those two facts reflection positivity follows. Everything in this section is machine-checked.

| # | Result | Status | Source |
|---|---|---|---|
| IV.1.1 | Wilson measure on the 4D torus for SU(2) and general compact G | **[Lean]** | `AreaLaw/ConcreteSUn.lean`, `OneScale/` |
| IV.1.2 | Reflection positivity, site and link | **[Lean]** | `Positivity/Wilson.lean` (`wilson_rp`), `Positivity/LinkWilson.lean`, `Positivity/Concrete.lean` (`wilson_rp_SU2`) |
| IV.1.3 | Temporal-gauge transfer kernel; centre flip of one row is a symmetry; sector identity Z_e = (Z + Z_tw)/2 | **[Lean]** (identity definitional) | `Attempts/R4/LayerKernel.lean`, `LayerSector.lean` |
| IV.1.4 | 't Hooft duality: the lattice rotation maps the temporal twist to the spatial twist on the symmetric box | **[Lean]** | `ProofPhase/RouteB/Duality.lean`, `tHooft_rotation` |
| IV.1.5 | A good blocking: centre-covariant and reflection-positive at every level | **[Lean]**; non-trivial limit at fixed L1 **[paper]** | `ProofPhase/RouteA/Blocking.lean`, `goodBlocking_rp`; `proof-phase/ws1-routeA/NOTE.md` |
| IV.1.6 | Strict flip bound Z_tw < Z for every beta != 0, every box, every twist position ("existence = non-existence + 1", I.7) | **[Lean]** | `ProofPhase/Flip/Strict.lean`, `su2_Ztw_lt_Z` |
| IV.1.7 | The one-step transfer kernel at fixed cross-section is strictly positive | **[Lean]** | `ProofPhase/Flip/Bound.lean`, `stepK_pos` |

## IV.2 The minting half: from a certificate to the gap

Suppose one box, at one scale, is known to forget its outside at a fixed rate. Then the whole lattice theory has a mass gap, in
both orders of limits, and the reconstructed Hilbert space carries a transfer operator with a spectral gap. That implication is the
minting half, and it is done.

| # | Result | Status | Source |
|---|---|---|---|
| IV.2.1 | Dobrushin uniqueness with exponential weights; D' gives decay of block observables at one rate (abstract Gibbs systems) | **[Lean]** | `Attempts/R3/TailDecay.lean` (`theoremA_w`), `Attempts/R3/Robust.lean` (`gap_of_localFactorsW`) |
| IV.2.2 | Block decay converted to physical units (Corollary B) | **[Lean]** | `OneScale/CorollaryB.lean`, `corollaryB_lattice` |
| IV.2.3 | OS route: a windowed block gap gives MassGapLoc and the transfer operator's gap on the reconstructed space | **[Lean]** | `ProofPhase/OS/GapLoc.lean` (`massGapLoc_of_UVTVBlockGap`), `ProofPhase/M1/UVTVOS.lean` (`gap_of_RP`) |
| IV.2.4 | The top-level assembly: OpenPieces implies MassGapLoc, LimitRP and NonTrivial; reflection positivity of the limit is proved, not assumed | **[Lean]** | `ProofPhase/Torus/Top.lean` (`yang_mills_assembly`), `ProofPhase/Assembly.lean` (`OpenPieces`) |
| IV.2.5 | The gap in both orders of limits (torus route) | **[Lean]** | `ProofPhase/Torus/Top.lean` (`yang_mills_assembly_torus`); `ProofPhase/Existence/Bridge.lean` (`bothOrders_of_torusDecay`) |
| IV.2.6 | Non-triviality of the hypotheses: pure noise and every bounded coupling fail OpenPieces | **[Lean]** | `ProofPhase/Assembly.lean`, `not_trivial` |
| IV.2.7 | MassGapLoc implies a spectral gap of the continuum Hamiltonian (needs density of local vectors and the reconstruction) | **[paper]**; spectral bridge **[Lean]** | `ProofPhase/Bridge/Spectral.lean`, `ProofPhase/Bridge/OSLink.lean` |
| IV.2.8 | Strong-coupling gap for any compact group (widest window 18 tanh(n beta) < 1) | **[Lean]** / **[paper]** | `OneScale/SingleLink.lean` |

**The crossover needs no description of its content.** Between the weak-coupling scale L_* (where M1 controls the law, IV.9) and
the box scale of O1 lie finitely many blocking steps, each of finite range. The assembly uses only a block gap at one scale; it never
needs to know what happens inside the crossover. So the certificate can be checked directly on the actual blocked law at that scale,
with no assumption about how the law got there **[paper]** (`PREP.md`, "The crossover is constrained by making no statement about its
content"). The price is the quantifier: since nothing is said about the content, the certificate must hold for every content the
crossover could have produced, that is, uniformly over every well-defined outside. That quantifier is already part of O1.

## IV.3 The pressing half: what one box gives, and how a chain carries it

This section collects what holds for every box, and what carries it along a line of boxes.

**A strict sign gives a rate (II.13).** By the strict flip bound (IV.1.6) and 't Hooft's duality F_e = -log tanh(F_tw/2), at every box
size max(F_tw, F_e) >= log(1 + sqrt 2) = 0.881. Rarity's rate is F_tw, the free energy of a forced centre sheet; disorder's rate is
F_e, the per-box decay of a centre-charged signal. They cannot both be small. **[Lean]** (`su2_handover`).

**A flux-carrying outside forces at least one sheet.** The flux cells of a box are even in number (Gauss's law mod 2), so a flux
carrying outside forces a sheet through the box, crossing the boundary at every flux cell. This is the quantum: "at least something"
always crosses. **[Lean]** (`exists_sheet_of_flux`, `even_card_fluxCells`).

**The law is the same on both sides.** The flux through a box's boundary computed from inside equals the one computed from outside,
and the total flux out of a box is even. **[Lean]** (`cob_restrict_eq_cob_restrict_compl`, `sum_cob_restrict_eq_zero`). Electric
influence therefore has no sources inside a box: it propagates along connected paths of boxes (IV.5.3).

**Superadditivity along the chain.** With the transfer matrix along a chain of boxes, F_e(a + b) >= F_e(a) + F_e(b) - c(a) - c(b), and
F_e(kL) >= k(F_e(L) - 2C). The boundary term c(L) = log(Z_0(L)/lambda_0^L) is the neutral excess act, the weight of the neutral
excitations over one box length. The per-box rate multiplies if F_e(L) > 2c(L) at one scale (superadditivity up to the excess terms; the converse is not proved). **[Lean]** in abstract transfer-matrix
form (`flux_superadd`, `flux_superadd_iter`).

**Uniformity along the chain.** Every DB applies the same transfer step (translation invariance in Euclidean time), so the loss rate
is the same at every step: a homogeneous Markov chain **[classical]**; its contraction eta^n is **[Lean]** (`contracts_kpow`, II.12).

**Physical units.** A one-box contraction eta <= eta_0 < 1 at a fixed physical box size l_* = L_* a, uniform in the lattice spacing a,
gives a physical mass m_phys >= -log eta_0 / l_* **[Lean]** (`phys_rate_of_uniform`). For a family of blocked kernels with one floor
eps_* for every spacing, the influence at physical distance D is at most exp(-m D) with m = -log(1 - eps_*)/l_* **[Lean]**
(`rdoeblin_physical_decay`).

| # | Result | Status | Source |
|---|---|---|---|
| IV.3.1 | Per-box hand-over rate: max(F_tw, F_e) >= 0.881 at every box size | **[Lean]** (0 < Z_tw a hypothesis) | `ProofPhase/Crossover/HandOver.lean`, `su2_handover` |
| IV.3.2 | A flux-carrying outside forces at least one sheet | **[Lean]** | `ProofPhase/Crossover/FluxRate.lean`, `exists_sheet_of_flux`, `even_card_fluxCells` |
| IV.3.3 | The flux law is the same seen from inside and outside; no sources | **[Lean]** | `ProofPhase/Crossover/Dichotomy.lean`, `cob_restrict_eq_cob_restrict_compl`, `sum_cob_restrict_eq_zero` |
| IV.3.4 | Superadditivity up to the excess terms; the rate multiplies along a chain if F_e(L) > 2c(L) at one scale | **[Lean]** (abstract) | `ProofPhase/Crossover/CompositeHTF.lean`, `flux_superadd`, `flux_superadd_iter` |
| IV.3.5 | Uniformity along the chain | **[classical]**; eta^n **[Lean]** | translation invariance; `ProofPhase/Mixing/Chain.lean`, `contracts_kpow` |
| IV.3.6 | A one-box contraction at fixed physical size gives a physical mass | **[Lean]** | `ProofPhase/Crossover/Neighbours.lean`, `phys_rate_of_uniform`; `ProofPhase/Crossover/RDoeblin.lean`, `rdoeblin_physical_decay` |
| IV.3.7 | The doubling law with a fixed loss gives the gap on all larger dyadic boxes | **[Lean]** (implication) | `ProofPhase/Flip/Floor.lean`, `su2_gap_of_doubling_defect` |
| IV.3.8 | Uncontained sheets weigh nothing (dichotomy part b) | **[Lean]** | `ProofPhase/Crossover/Dichotomy.lean`, `measure_uncontained` |

So along a chain, one box at one scale is enough. The question is what a four-dimensional grid of boxes needs.

## IV.4 Why a grid is harder than a chain

In a chain, flux entering a box has one way out. In a grid it can leave through any of the other 2d - 1 faces, so a box has 2d
channels to its neighbours, and Dobrushin's condition needs the **sum** of the influences over all channels below one (II.12).

**The hand-over covers two channels, not eight.** The per-box ratio sqrt 2 - 1 = 0.414 keeps a column sum below one for at most two
channels **[Lean]** (`handover_column_sum_iff`). A grid in d dimensions needs a per-box suppression F > log(2d), that is log 8 = 2.08
in d = 4, more than twice the duality floor **[Lean]** (`column_requirement`).

**A per-box floor (Doeblin) cannot supply it.** Doeblin's mass per box is at most e^{-K}/(1 - e^{-K}) with K = C beta L_*^{d-1}, which
goes to zero as the lattice spacing does **[Lean]** (`neg_log_one_sub_le`, `doeblin_mass_tendsto_zero`). For a grid the floor exponent
must stay below log(8/7) = 0.134 (column form) **[Lean]** (`floor_column_requirement`), or below -log(1 - p_c), about 0.22 in the
disagreement-percolation form (the requirement `floor_disagreement_requirement` is **[Lean]** for any p; the value 0.22 uses the
site-percolation threshold of Z^4, p_c about 0.197, **[classical]** (recalled), claim IV.4.3c). At the weak-coupling scale it is in the tens
**[paper]** (`RDOEBLIN.md`). It misses by orders of magnitude, and a larger box at fixed coupling makes it worse.

**Duality gives no floor above log(2d).** For n independent Z/2 sectors 't Hooft's Fourier relation reads (1 + S_tw)(1 + S_e) = 2^n
**[paper]** (`TRANSFER.md`). The smaller sum is then forced only below the self-dual value sqrt(2^n) - 1 **[Lean]**
(`min_le_of_sector_product`), which is at least one as soon as n >= 2 **[Lean]** (`selfdual_sector_ge_one`). Duality allows both
summed weights to be large and forces no summable suppression. What the summed form does give is the requirement as a quantitative
't Hooft criterion: the summed electric weight is below one iff the summed twist weight exceeds 2^{n-1} - 1 **[Lean]**
(`electric_sum_lt_one_iff`). That is a dynamical statement (near-saturated twists), not supplied by any duality.

**A gauge-covariant frame carries nothing.** A composite Higgs-type field built from the collar's covariant Laplacian exists on every
collar **[paper]**. But conditioning on a gauge-covariant frame leaves the law of every gauge-invariant observable unchanged **[Lean]**,
finite analogue (`weight_fiber_eq`, `weight_fiber_mul_card`); **[paper]** for compact groups. The frame changes nothing (`HTF.md`).

| # | Result | Status | Source |
|---|---|---|---|
| IV.4.1 | The hand-over keeps a column below one for at most two channels; a grid needs F > log(2d) = 2.08 | **[Lean]** | `ProofPhase/Crossover/Neighbours.lean`, `handover_column_sum_iff`, `column_requirement` |
| IV.4.2 | Doeblin's mass per box goes to zero in the continuum | **[Lean]** | `Neighbours.lean`, `neg_log_one_sub_le`, `doeblin_mass_tendsto_zero` |
| IV.4.3 | A grid needs floor exponent below 0.134 (or 0.22, with the recalled threshold p_c = 0.197); at L_* it is in the tens | **[Lean]** (requirement) + **[paper]** (estimate) | `ProofPhase/Crossover/RDoeblin.lean`, `floor_column_requirement`, `floor_disagreement_requirement`; `RDOEBLIN.md` |
| IV.4.4 | Multi-sector duality forces nothing for n >= 2; the quantitative 't Hooft criterion | **[Lean]** (the relation itself **[paper]**) | `ProofPhase/Crossover/Runs.lean`, `min_le_of_sector_product`, `selfdual_sector_ge_one`, `electric_sum_lt_one_iff` |
| IV.4.5 | A gauge-covariant frame carries no gauge-invariant information | **[Lean]** (finite) + **[paper]** | `ProofPhase/Crossover/CompositeHTF.lean`, `weight_fiber_eq`, `weight_fiber_mul_card`; `HTF.md` |
| IV.4.6 | At typical fields the summed boundary influence drops below one at about 7 cells from the boundary (box of about 15 cells) | **[numerical]** (typical, not supremum) | `NEIGHBOURS.md`, 0.2 |

## IV.5 Containment: the requirement moved inside one box

The owner's correction ("the saturation has to be proven inside confinement and absent outside that confinement, as a containing
existence", `PREP.md`) reverses the direction of the attack. Instead of building the inside of a box from outside data, prove three
things: outside, saturation is absent; the container ends; inside, saturation makes the influence run in tubes, and tubes are chains,
where IV.3 closes. The first two close. The third closes negatively at the duality floor and positively above a sharp threshold.

**IV.5.1 Outside, absence (lemma).** For every box, the twist ratio r = Z_tw/Z satisfies r < 1 and
r = (1 - e^{-F_e})/(1 + e^{-F_e}) <= F_e **[Lean]** (`twist_ratio_eq`, `twist_ratio_le_elecF`, `elecF_nonneg`). The twist is rare
exactly where electric flux is cheap. In a physically small box small-volume perturbation theory makes F_e of order g(L)^2
**[classical]** (Luescher; van Baal; recalled, not re-checked), so r = O(g^2). The mechanism outside is cheap electric flux, seen
from the other side of the duality as a rare twist.

**IV.5.2 The container ends, in long boxes.** At fixed cross-section the transfer kernel is strictly positive (IV.1.7). By
Jentzsch's theorem **[classical]** the vacuum is the unique top state; it is centre-invariant **[paper]**, so the flux sector lies a
factor mu < 1 below it per unit length. Then F_e(T) >= -T log mu - log C grows without bound **[Lean]** (`elecF_lower_of_gap`,
`exists_elecF_ge`). In every long enough box the rarity branch fails, and by the hand-over the electric channel carries the
suppression. What this does not give: mu depends on the cross-section and may tend to one as it grows. In the cubic geometry the end
needs F_e(L) >= 0.881 at one L, that is g^2 of order one, beyond perturbative or M1 control **[open]**; measured near L = 4 at
beta = 2.3 (F_e = 0.91, **[numerical]**, preliminary).

**IV.5.3 Inside: what the law gives.** Gauss's law makes electric influence a conserved line with no sources that no collar can
screen (IV.3.2, IV.3.3). That is the whole structural content of "tube", derived from the law without assuming tubes **[Lean]** for
the pieces, **[paper]** for the conclusion. The law does not say which path carries the influence: it allows every path and every
branching.

**IV.5.4 Inside: what the cost must give.** Bound the influence between two boxes at distance D by a sum over paths of boxes, each
box costing e^{-F}. With mu continuations per step the sum is a geometric series in mu e^{-F}, which converges iff F > log mu **[Lean]**
(`path_sum_summable_iff`, `tube_threshold`). Self-avoiding paths on Z^d have connective constant mu_d >= d, and for mu >= 3,
mu (sqrt 2 - 1) >= 1 **[Lean]** (`path_entropy_beats_handover`). **So in every d >= 3 the duality floor 0.881 loses to path entropy:
the cheapest chain does not dominate.** For d = 4, mu_4 = 6.77 and log mu_4 = 1.91 **[classical]** (recalled); rigorously log mu_4
lies between log 4 = 1.39 and log 7 = 1.95. Equivalently, the single-sector twist ratio must exceed (mu - 1)/(mu + 1) = 0.74.

**IV.5.5 What the action adds and what it does not.** The Bogomolny bound S >= 8 pi^2 |Q| / g^2 **[classical]** gives, on a twisted
torus with odd twist product, the floor S >= pi^2 beta for admissible fields **[classical]** (Luescher's admissibility). It strengthens
IV.5.1 for multi-plane twist sectors **[paper]**. It does not help the single-plane twist used here (that sector contains flat
configurations, so its floor is zero), nor inside (it bounds twists from above, while O1 needs them high) **[paper]**. At a fixed
physical box size the position entropy 4 log(L/a) of a fractional instanton beats its action pi^2 beta = (11/3) log(1/(a Lambda)) as
a -> 0 **[paper]**, one-loop sketch (determinants and measure not checked).

**IV.5.6 The one-box statement (O1).** Combining IV.5.3 and IV.5.4: law (structure) plus cost above entropy (dominance) gives tubes,
and tubes are chains, where IV.3 applies. What remains is:

> **(O1)** At one box of fixed physical size, F_e(L) - 2c(L) > log mu_4 = 1.91, uniformly over every well-defined outside, with c(L)
> the neutral excess act of IV.3. **[open]**

The familiar form F_e(L) > 1.91 (equivalently r(L) > 0.74) drops the excess act, as E = mc^2 drops the momentum term of
E^2 = (pc)^2 + (mc^2)^2. The drop is only seeming: c(L) >= 0, so the full form implies the familiar one, but the familiar one alone
does not give the chain criterion (IV.5.8, examples in Lean).

This is the grid requirement log 8 = 2.08 of IV.4.1 refined from column sums to path counting. Containment moves the requirement
inside the box but does not lower it to the chain value 0.881.

**Care points, settled in draft 3.**
* **O1 in one form.** O1 is `FineOneBox` (`OneBox/Fine.lean`): one box at the physical cell scale, influence bounds under every
  boundary condition, uniform in level and volume. `WilsonOneBox` and `FineOneBoxSplit` imply it, and it feeds
  `yang_mills_assembly_onebox`; `BlockGapBddW` belongs to the separate blocking route (IV.5.9, **[Lean]**).
* **O1 in the one-box test.** In the test of Part I (I.8, the rotation API) O1 is exactly DMP-completeness of the Yang-Mills box:
  the chain form holds exactly when some margin makes every chain of outsides DMP-complete, and `FineOneBox` holds exactly when the
  Yang-Mills box, with its geometry fixed across levels, is DMP-complete from its start level **[Lean]** (IV.10c, IV.10d). Both
  directions are proved, so the general test carries exactly O1, no more and no less. That the box is DMP-complete is O1 itself
  **[open]** (IV.10e).
* **Per-box costs multiply.** In that per-outside form the composition of the per-box influences is a theorem, so no annealed
  quantity enters the gap; the annealed-to-quenched identification is needed only to read a torus measurement of F_e as evidence
  about O1 (IV.5.7, **[Lean]**).
* **Chain and tube.** In the transfer-matrix model the chain criterion F_e(L) > 2c(L) and the tube threshold F_e(L) > log mu are
  independent, with examples both ways; the joint form gives both (IV.5.8, **[Lean]**, model).

| # | Result | Status | Source |
|---|---|---|---|
| IV.5.1a | r < 1, r = (1 - e^{-F_e})/(1 + e^{-F_e}) <= F_e, F_e >= 0 | **[Lean]** | `ProofPhase/Crossover/Containment.lean`, `twist_ratio_eq`, `twist_ratio_le_elecF`, `elecF_nonneg` |
| IV.5.1b | Small box: F_e = O(g(L)^2) | **[classical]** (recalled) | `CONTAINMENT.md`, 1 |
| IV.5.2a | At fixed cross-section F_e(T) grows without bound | **[Lean]** core + **[classical]** (Jentzsch) + **[paper]** (centre invariance) | `Containment.lean`, `elecF_lower_of_gap`, `exists_elecF_ge`; `CONTAINMENT.md`, 2 |
| IV.5.2b | Cubic boxes: F_e(L) >= 0.881 at some L | **[open]**; near L = 4 at beta 2.3 **[numerical]** | `CONTAINMENT.md`, 2 |
| IV.5.3 | Gauss's law makes influence path-like (no sources, unscreenable) | **[Lean]** pieces + **[paper]** | IV.3.2, IV.3.3; `CONTAINMENT.md`, 6.1 |
| IV.5.4a | Path sums converge iff F > log mu; 0.881 loses for mu >= 3 | **[Lean]** | `Containment.lean`, `path_sum_summable_iff`, `tube_threshold`, `path_entropy_beats_handover` |
| IV.5.4b | mu_4 = 6.77, log mu_4 in [1.39, 1.95] | **[classical]** | `CONTAINMENT.md`, 3 |
| IV.5.5 | Bogomolny floor helps outside only and loses to entropy as a -> 0 | **[classical]** (bound) + **[paper]** (sketch) | `CONTAINMENT.md`, 6.2 |
| IV.5.6 | **(O1)** F_e(L) - 2c(L) > log mu_4 at one box of fixed physical size, uniformly over outsides (familiar form F_e(L) > log mu_4, the excess act dropped) | **[open]** | `CONTAINMENT.md`, 0 and 5; `docs/OPEN-QUESTIONS-DMP.md`, 0 |
| IV.5.7 | Per-box costs multiply over the lattice in O1's per-outside form; annealed to quenched only for reading measurements | **[Lean]** | `OneBox/Fine.lean`, `fineDecayInv_of_fineOneBox`; `Closures/OneBoxForm.lean` |
| IV.5.8 | Chain criterion and tube threshold independent in the model; the joint form gives both | **[Lean]** (model) | `Closures/ChainJoint.lean`, `joint_gives_both`, `tube_not_chain`, `chain_not_tube` |
| IV.5.9 | O1 in one Lean form: `FineOneBox`, with the other forms linked | **[Lean]** | `OneBox/Fine.lean`; `Closures/OneBoxForm.lean` |

## IV.6 The one box from inside: saturation and the dichotomy

**Saturation from what we have.** Configuration by configuration the twist changes the weight by at least e^{-2 beta N}, N = L^2
flipped plaquettes, so Z_tw/Z >= e^{-2 beta L^2} **[Lean]** (`ratio_floor_of_pointwise`, `exp_floor_ge_iff`). That saturates the twist
only for beta L^2 <= 0.42: strong coupling in tick units, vanishing in the continuum. Conversely a large electric free energy forces a
saturated twist **[Lean]** (`twist_ratio_of_elecF`), so saturation is a consequence of O1, not an independent input.

**Bond-moving bounds localise Tomboulis's step, they do not avoid it.** Rigorous one-sided bounds on Z and on the even sector Z^+ exist,
and the upper decimation flows to strong coupling for every beta in d <= 4 **[classical]** (Ito). A lower bound on the twist ratio
needs the two normalisations matched; the upper one is at least one **[Lean]** (`jensen_normalization`) and extensive in the box
volume. In the one-box form the mismatch is finite but vanishes at fixed physical box size **[paper]**, sketch. So the step needed is a
lower bound on the box partition function matched to the upper decimation's normalisation within O(1): Tomboulis's interpolation step
(2007; gaps pointed out by Ito and Seiler; not accepted as a proof **[classical]**), now localised to one box.

**The dichotomy inside one box.** Part (a), that a sheet plaquette always costs something, fails uniformly: at the SO(3) cut
(tr U_p = 0) a sheet plaquette is free **[paper]**. What survives: for every outside, the box contracts, or one of two bad events holds
(near-degenerate spanning surfaces for a flux-carrying outside; an SO(3) cut along a would-be sheet) **[paper]**. Rarity and
saturation are disjoint, with a window between them of about 0.18 to at least 1.79 nats per plaquette **[Lean]** (`window_gap`) +
**[paper]** (numbers).

| # | Result | Status | Source |
|---|---|---|---|
| IV.6.1 | Tick-unit floor Z_tw/Z >= e^{-2 beta L^2}; saturates only for beta L^2 <= 0.42 | **[Lean]** | `ProofPhase/Crossover/Saturation.lean`, `ratio_floor_of_pointwise`, `exp_floor_ge_iff` |
| IV.6.2 | A large electric free energy forces a saturated twist | **[Lean]** | `Saturation.lean`, `twist_ratio_of_elecF` |
| IV.6.3 | Bond-moving: the one-box form localises the interpolation step (Tomboulis) to one box | **[paper]** (sketch); Jensen normalisation **[Lean]** | `SATURATION.md`, 0; `Saturation.lean`, `jensen_normalization` |
| IV.6.4 | Kanazawa's bracket 1/2 < Z^+/Z < 1 is the non-strict form of IV.1.6 | **[classical]**; strict form **[Lean]** | `SATURATION.md`, 0 |
| IV.6.5 | Dichotomy part (a) fails uniformly at the SO(3) cut | **[paper]** | `DICHOTOMY.md`, 0.2 |
| IV.6.6 | Reduction to two bad events | **[paper]** | `DICHOTOMY.md`, 0.4 |
| IV.6.7 | Window between rarity and saturation, 0.18 to >= 1.79 nats per plaquette | **[Lean]** (disjointness) + **[paper]** (numbers) | `ProofPhase/Crossover/Dichotomy.lean`, `window_gap`; `DICHOTOMY.md`, 0.3 |
| IV.6.8 | Y2 to Y5: inside residue, hand-over through the window, condition A uniformly (m about 4 measured on typical fields), uniformity in volume | **[open]** (pieces of O1); per-volume gap **[Lean]** conditional on H2-all | `docs/OPEN-QUESTIONS-DMP.md`, 2; `ProofPhase/Quantum/PerVolume.lean`, `perVolumeGap` |
| IV.6.9 | IR column at L1: W1 column certified at 0.99988 at L sqrt(sigma) = 2.80 (computer-assisted certificate as a named hypothesis) | **[open]**; implication **[Lean]** | `ProofPhase/Certified/Measured.lean`; `proof-phase/c9b-adjoint/ROUTE3.md` |

## IV.7 Measured: what the numbers say about O1

Measurements can refute O1, never establish it (provability rule, `proof-phase/c9b-adjoint/REDESIGN.md`, section 8). Every error bar
is max(statistical floor, resolution floor), the resolution floor of an energy read over Euclidean extent T being 1/T in lattice
units; ad-hoc floors are not used; a change of floor after data is reported beside the pre-registered result (`attempts/RULES.md`,
last section).

**IV.7.1 Small tori (preliminary).** At beta = 2.3 the cubic twist ratio crosses the tube threshold between L = 4 (r = 0.42, at the
self-dual value) and L = 6 (r = 0.86, F_e = 2.6). Central values pass O1 at L = 6, but the one-sided 95 % lower bound of F_e is 1.26
statistically and 0.96 with the resolution floor: **not certified** **[numerical]** (`CONTAINMENT.md`, 1 and 3; `SATURATION.md`, 0).
At beta = 3.5, L = 2: r = 0.018, F_e = 0.035, as IV.5.1 predicts.

**IV.7.2 The chain criterion at a large cross-section.** The pre-registered check of F_e(L) > 2c(L) on chains of cross-section 16^3
refuted it at beta = 3.5, L = 1, at 99 % **[numerical]**. Re-scored post hoc under the universal floor, the refuted range grows to
L <= 2 (both levels) and L = 3 (95 % only). At beta = 2.3 no test was possible (no flux bound). This geometry is not the cubic one of
O1, so it bears on O1 neither way; it says only that at that cross-section and coupling the electric multiplication needs L >= 4
(`ONEBOX-CHECK.md`, 4, 5, 7).

**IV.7.3 The cubic one-box geometry is untested by saved data**; a small-torus simulation is pre-registered (`ONEBOX-CHECK.md`, 8).

**IV.7.4 The mirror reading.** The identity 8 pi^2 = -4 zeta(2)/zeta(-1) is derived in Lean from Mathlib's functional equation
**[Lean]** (`GRH/Mirror.lean`, `eight_pi_sq_mirror`, `zeta_neg_one_val`); it is the k = 1 member of a classical family. In Yang-Mills it
brackets F_e(L) between two asymptotic ends: the Luescher term (zeta(-1)) at the infrared end, fractional instantons (4 pi^2/g^2) at
the ultraviolet end. In effective-string terms O1 becomes L sqrt(sigma) > 1.72 (Luescher) or 1.80 (Arvis), just above the string's
breakdown at 1.45 **[numerical]**, using the effective string as a model. The mirror does not constrain F_e between the two ends, where
O1 sits **[reading]** for "brackets" (`docs/rh-guide/MIRROR.md`, 0.2).

| # | Result | Status | Source |
|---|---|---|---|
| IV.7.1 | Small tori at beta 2.3: F_e(6) = 2.6 centrally, lower bound 0.96 with the floor; not certified | **[numerical]** (preliminary) | `CONTAINMENT.md`, 1, 3; `SATURATION.md`, 0 |
| IV.7.2 | Chain criterion refuted at cross-section 16^3, beta 3.5, L = 1 (pre-registered); L <= 2 post hoc | **[numerical]** | `ONEBOX-CHECK.md`, 4, 7 |
| IV.7.3 | The universal error-bar floor max(statistical, 1/T) | project rule | `attempts/RULES.md`, last section |
| IV.7.4a | 8 pi^2 = -4 zeta(2)/zeta(-1); zeta(-1) = -1/12 | **[Lean]** | `ProofPhase/GRH/Mirror.lean`, `eight_pi_sq_mirror`, `zeta_neg_one_val` |
| IV.7.4b | O1 in effective-string units: L sqrt(sigma) > 1.72 to 1.80 | **[numerical]** (model-based) | `docs/rh-guide/MIRROR.md`, 0.2 |

## IV.8 "It runs": the formal target shared with GRH

Both Yang-Mills and GRH ask about an evolution that does not increase a positive norm. If T is a contraction on a normed space, the
GRH-type conclusion is that every mirrored mode is a phase; the Yang-Mills conclusion is that, with ||T x|| <= eta ||x|| on the neutral
sector and eta < 1, there is no phase mode there, and iterates decay as eta^n **[Lean]** (`no_phase_mode`, `iterate_contraction`,
`runs_two_targets`; GRH side `GRH/Tate.lean`, `runs_and_mirror_on_line`). The open steps are complementary: Yang-Mills has the positive
norm for free (reflection positivity) and lacks the margin eta < 1; GRH lacks the positive norm (Weil positivity) and needs no margin
(Part III).

| # | Result | Status | Source |
|---|---|---|---|
| IV.8.1 | "It runs" in two targets: phases (mirror) and no phase mode under a margin | **[Lean]** | `ProofPhase/Crossover/Runs.lean`, `no_phase_mode`, `iterate_contraction`, `runs_two_targets` |

## IV.9 The weak-coupling side and the continuum (inputs from outside the gap mechanism)

| # | Result | Status | Source |
|---|---|---|---|
| IV.9.1 | UV stability, small-field control and one-loop running at the weak-coupling unit scale (a recent construction by others) | **[external]** | `H1-OPENAI.md` |
| IV.9.2 | Balaban's large-field control preserves partition functions, not laws | **[classical]**, read in full | `proof-phase/c5d-supplier/BALABAN-READING.md` |
| IV.9.3 | M1: the law-preserving large-field step, at weak coupling up to L_* | **[paper]**, complete at paper level; Lean parts | `ProofPhase/M1/Assembly.lean` (`m1_assembly`); `proof-phase/m1-tools/M1-PLAN.md` |
| IV.9.4 | The continuum limit exists (mesh limit at fixed volume, then volume along a subsequence) | **[external]** | `H1-OPENAI.md`; `ProofPhase/Existence/Bridge.lean` (`plaqLaw_eq_wilsonMeasure`) |
| IV.9.5 | (O2) Line of constant physics (one-loop slope 11/(6 pi^2)) and non-triviality, as inputs of the assembly | **[open]** | `ProofPhase/Assembly.lean` (`OnLCP`, `NonTrivial`); `ProofPhase/V4/LCP.lean` |
| IV.9.6 | (O3) Euclidean invariance, local fields as distributions, uniqueness of the limit, Wightman reconstruction | **[external]** for the external construction; **[open]** for ours | `PROOF-BLUEPRINT.md`, P6.4 to P6.9, P7.6 |
| IV.9.7 | (O4) Every compact simple group: existence external; this project's tuning SU(2) only | **[external]** / **[open]** | `PROOF-BLUEPRINT.md`, P6.10 |

M1 hands over at a weak-coupling scale: the coupling becomes of order one only after the crossover. So the floor M1 supplies at L_*
is uniform in the spacing but tiny, and it gives a physical-units gap only along a chain at fixed cross-section (IV.3.6), not on a
grid (IV.4.3) **[paper]** (`RDOEBLIN.md`, 0).

## IV.10 DMP readings attached to this part (all [reading])

* **Outside, non-existence keeps existing through assertion.** The twist is rare because electric flux costs almost nothing: one fact
  seen from the two sides of the duality (IV.5.1).
* **The container must end, and does, along the run.** "It can never catch up" in exact form: Z_1/Z_0 <= C mu^T, mu < 1 (IV.5.2).
* **Inside, existence has to outrun possibility.** Of the mu continuations per step only one is the tube; the tube dominates only if
  its cost per step exceeds log mu. The balanced state (0.881) is not enough (IV.5.4). This is "existence = non-existence + 1" in
  counting form.
* **IM is both sides.** Gauss's law is the same statement on both sides of every DB; it makes every tube possible, and the action has
  to make one tube cheaper than all others combined (IV.5.3, IV.5.4).
* **The pressing as the instanton of the first act.** The Bogomolny bound is a worst-case floor proved before any dynamics runs; it
  prices the rare side and loses logarithmically to entropy as the tick shrinks (IV.5.5).
* **The duality is never alone while running.** The 't Hooft relation is kinematic and chooses no branch; the action selects it
  (IV.4.4).
* **The crossover is confined by making no statement about its content** (IV.2).
* WHKs: group plus one scale fix everything (dimensional transmutation, **[classical]**); mass gap = the arrow of causality exists
  (I.7); only 3+1 transmutes, g^2 being dimensionless only in d = 4 **[classical]**.

## IV.11 What would close it

O1 first: a worst-case argument, for one box of fixed physical size, that the electric cost per box exceeds the path entropy of the
four-dimensional lattice for every well-defined outside, together with the per-box product structure along paths (IV.5.7). Then O2:
its scale-uniform lower edge (IV.9.5b), conditional on the one assumption beside O1 (Part III 4.4); the per-box half is proved and the gap uses only the resolution clause. Then O3: an observable bridge from this project's bounded slab
observables to local fields, or adoption of the external construction's field notion with its audit. Then O4: a tuning for general G.
O1 is the mathematical core; O2 to O4 are the remaining distance from the gap mechanism to the Clay statement.
