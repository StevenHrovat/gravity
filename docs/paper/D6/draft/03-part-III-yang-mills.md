# Part III. Yang-Mills: the gap mechanism reduces to one box of fixed physical size

*Draft 6. Prose, with every result marked. Lean paths relative to `docs/mass-gap/formal/ProofPhase/` (the modules of the earlier
attempt rounds R2 to R4 live under `docs/mass-gap/formal/Attempts/`); notes relative to `docs/mass-gap/weak-coupling/`; the crossover notes are in
`proof-phase/c9a-crossover/`. The full chain with all 51 pieces is in `PROOF-BLUEPRINT.md`. Claim labels (III.n) are listed in
`../CLAIMS.md`.*

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

**Why O1 is one number at one scale.** "The loss rate of one box is below one" is not enough: the crossover rounds
showed that the per-box rate 0.881 suffices for a chain of boxes but not for a grid (III.4), and that it suffices for a grid exactly
when the influence runs in tubes, which needs a larger electric cost per box (III.5). O1 is one statement about one box at one scale.

**Convention for beta.** In the Lean, beta = 2/g^2: the plaquette weight is exp(beta Re tr U_p) (`Assembly.lean`), and the
one-loop slope is 11/(6 pi^2). The notes behind III.5.5, III.6 and III.9 (the floor e^{-2 beta N}, S >= pi^2 beta = 4 pi^2/g^2,
beta_eff = 4/g^2 in `RDOEBLIN.md`) were written with the standard beta = 4/g^2, the weight exp((beta/2) tr U_p). Where this part
writes a bare beta in a formula it says which one. The simulations of III.7 (beta = 2.3 and 3.5) use the standard beta = 4/g^2: their SU(2)
heat bath draws each link with weight exp(beta (1/2) tr(U A)) for the staple sum A (Kennedy-Pendleton and Creutz updates;
`proof-phase/c9a-crossover/w2/smalltorus.py`, `sample_w0`, `heatbath`) **[paper]** (read from the code).

## III.1 The lattice theory and its positivity (G0 by construction)

Yang-Mills is the one problem of the first three whose starting positivity is given. The Wilson weight e^{-S} is positive and local, and
from those two facts reflection positivity follows. Everything in this section is machine-checked.

| # | Result | Status | Source |
|---|---|---|---|
| III.1.1 | Wilson measure on the 4D torus for SU(2) and general compact G | **[Lean]** | `AreaLaw/ConcreteSUn.lean`, `OneScale/` |
| III.1.2 | Reflection positivity, site and link | **[Lean]** | `Positivity/Wilson.lean` (`wilson_rp`), `Positivity/LinkWilson.lean`, `Positivity/Concrete.lean` (`wilson_rp_SU2`) |
| III.1.3 | Temporal-gauge transfer kernel; centre flip of one row is a symmetry (`top_parity`, any probability space); sector identity Z_e = (Z + Z_tw)/2 (`twist_centre_transform`, finite configuration spaces; for the SU(2) measure it is the definition of `elecF`, `Flip/Floor.lean`) | **[Lean]** (identity definitional) | `Attempts/R4/LayerKernel.lean`, `LayerSector.lean` |
| III.1.4 | 't Hooft duality: the lattice rotation maps the temporal twist to the spatial twist on the symmetric box | **[Lean]** | `RouteB/Duality.lean`, `tHooft_rotation` |
| III.1.5 | A good blocking: centre-covariant and reflection-positive at every level | **[Lean]**; non-trivial limit at fixed L1 **[paper]** | `RouteA/Blocking.lean`, `goodBlocking_rp`; `proof-phase/ws1-routeA/NOTE.md` |
| III.1.6 | Strict flip bound Z_tw < Z for every beta != 0, every box, every twist position ("existence = non-existence + 1", I.7) | **[Lean]** | `Flip/Strict.lean`, `su2_Ztw_lt_Z` |
| III.1.7 | The one-step transfer kernel at fixed cross-section is strictly positive | **[Lean]** | `Flip/Bound.lean`, `stepK_pos` |

## III.2 The minting half: from a certificate to the gap

Suppose one box, at one scale, is known to forget its outside at a fixed rate. Then the whole lattice theory has a mass gap, in
both orders of limits, and the reconstructed Hilbert space carries a transfer operator with a spectral gap. That implication is the
minting half, and it is done.

| # | Result | Status | Source |
|---|---|---|---|
| III.2.1 | Dobrushin uniqueness with exponential weights; D' gives decay of block observables at one rate (abstract Gibbs systems) | **[Lean]** | `Attempts/R3/TailDecay.lean` (`theoremA_w`), `Attempts/R3/Robust.lean` (`gap_of_localFactorsW`) |
| III.2.2 | Block decay converted to physical units (Corollary B) | **[Lean]** | `OneScale/CorollaryB.lean`, `corollaryB_lattice` |
| III.2.3 | OS route: a windowed block gap gives MassGapLoc and the transfer operator's gap on the reconstructed space | **[Lean]** | `OS/GapLoc.lean` (`massGapLoc_of_UVTVBlockGap`), `M1/UVTVOS.lean` (`gap_of_RP`) |
| III.2.4 | The top-level assembly: OpenPieces implies MassGapLoc, LimitRP and NonTrivial (NonTrivial is itself a field of OpenPieces, so it is an output only trivially); reflection positivity of the limit is proved, not assumed | **[Lean]** | `Torus/Top.lean` (`yang_mills_assembly`), `Assembly.lean` (`OpenPieces`) |
| III.2.5 | The gap in both orders of limits (torus route) | **[Lean]** | `Torus/Top.lean` (`yang_mills_assembly_torus`); `Existence/Bridge.lean` (`bothOrders_of_torusDecay`) |
| III.2.6 | Non-triviality of the hypotheses: pure noise and every bounded coupling fail OpenPieces | **[Lean]** | `Assembly.lean`, `not_trivial` |
| III.2.7 | MassGapLoc implies a spectral gap of the continuum Hamiltonian (needs density of local vectors and the reconstruction) | **[paper]**; spectral bridge **[Lean]** | `Bridge/Spectral.lean`, `Bridge/OSLink.lean` |
| III.2.8 | Strong-coupling gap for any compact group (widest window 18 tanh(n beta) < 1) | **[Lean]** / **[paper]** | `OneScale/SingleLink.lean` |

**The stated inputs.** `OpenPieces` (`Assembly.lean`) consists of the line of constant physics `OnLCP` (resolution,
one-loop running, scheme clause), non-triviality `NonTrivial`, and a route through the crossover (for the torus form
`BlockedTorusRoute`: `H1Local`, `LimitDprime`, `ObsTransferPhys`). In the one-box form (III.5.9) the gap needs only the resolution
clause and `FineOneBox`; `NonTrivial` and the running and scheme clauses are separate hypotheses that identify the family as
Yang-Mills (pure noise also has a gap, III.2.6). III.2.7 and III.9 name the rest.

**The crossover needs no description of its content.** Between the weak-coupling scale L_* (where M1 controls the law, III.9) and
the box scale of O1 lie finitely many blocking steps, each of finite range. The assembly uses only a block gap at one scale; it never
needs to know what happens inside the crossover. So the certificate can be checked directly on the actual blocked law at that scale,
with no assumption about how the law got there **[paper]** (`PREP.md`, "The crossover is constrained by making no statement about its
content"). The price is the quantifier: since nothing is said about the content, the certificate must hold for every content the
crossover could have produced, that is, uniformly over every well-defined outside. That quantifier is already part of O1.

## III.3 The pressing half: what one box gives, and how a chain carries it

This section collects what holds for every box, and what carries it along a line of boxes.

**A strict sign gives a rate (II.13).** By the strict flip bound (III.1.6) and 't Hooft's duality F_e = -log tanh(F_tw/2), at every box
size max(F_tw, F_e) >= log(1 + sqrt 2) = 0.881. Rarity's rate is F_tw, the free energy of a forced centre sheet; disorder's rate is
F_e, the per-box decay of a centre-charged signal. They cannot both be small. **[Lean]** (`su2_handover`; hypotheses beta != 0,
even time extent, and 0 < Z_tw). For the SU(N) twisted Wilson partition functions the rate holds with no hypothesis on Z_tw, for every N >= 2, every nontrivial
sector, beta != 0 and even time extent, since there 0 < Z_tw < Z is proved **[Lean]** (`General/SUNHandOver.lean`, `sun_handover`, from
`sunZtw_pos`, `sunZtw_lt`); that the `Flip` object of `su2_handover` is the k = 1 case of that package is the identification
`General/SUNTwistInstances.lean` names, not proved (claim III.3.1b).

**All N sectors at once (III.3.1c).** The full turn over the centre Z_N (II.2.7) turns the N twisted partition functions into N
electric sectors, Z_el(e) = (1/N) sum over k of cos(2 pi k e / N) Z_tw,k, the real form of 't Hooft's electric-flux projection
('t Hooft 1979; real because Z_tw,-k = Z_tw,k for even time extent, `sunZtw_neg`). One turn gives the sum of the electric sectors as Z and N Z_el(0) as the
sum of the twisted ones, and the balance II.13.3 turns these into the rate log(1 + sqrt N): some nontrivial twist free energy or some
nontrivial electric free energy of the SU(N) Wilson box is at least log(1 + sqrt N) **[Lean]**, given that the electric sectors are
positive (`General/SUNFullTurn.lean`, `sunZel_sum`, `sunZel_zero`, `sun_handover_full_turn`), and the same holds for the mean over the
N - 1 nontrivial sectors of one type (`sun_handover_full_turn_mean`, II.13.4). For N = 2 the positivity is proved for beta != 0 and
even time extent, the sectors being (Z + Z_tw)/2 and (Z - Z_tw)/2 (`sunZel_pos_two`), and the rate is the log(1 + sqrt 2) above. For N >= 3 it is a stated
hypothesis: each electric sector is the weight of one flux sector of the transfer matrix, positive in the transfer-matrix picture
**[classical]**, not formalised here (claim III.3.1c). The rate grows with N; III.5.4 says what that does and does not give.

**A flux-carrying outside forces at least one sheet.** The flux cells of a box are even in number (Gauss's law mod 2), so a flux
carrying outside forces a sheet through the box, crossing the boundary at every flux cell. This is the quantum: "at least something"
always crosses. **[Lean]** (`exists_sheet_of_flux`, `even_card_fluxCells`).

**The law is the same on both sides.** The flux through a box's boundary computed from inside equals the one computed from outside,
and the total flux out of a box is even. **[Lean]** (`cob_restrict_eq_cob_restrict_compl`, `sum_cob_restrict_eq_zero`). Electric
influence therefore has no sources inside a box: it propagates along connected paths of boxes (III.5.3).

**Superadditivity along the chain.** With the transfer matrix along a chain of boxes, F_e(a + b) >= F_e(a) + F_e(b) - c(a) - c(b), and
F_e(kL) >= k(F_e(L) - 2C). The boundary term c(L) = log(Z_0(L)/lambda_0^L) is the neutral excess act, the weight of the neutral
excitations over one box length; C is a bound on c(kL) for every multiple kL of L (the Lean needs this bound on all multiples, not
only c(L)), and the model assumes lambda_0^n <= Z_0(n) and Z_1 submultiplicative. The per-box rate multiplies if F_e(L) > 2C
(superadditivity up to the excess terms; the converse is not proved). **[Lean]** in abstract transfer-matrix form (`flux_superadd`,
`flux_superadd_iter`).

**Uniformity along the chain.** Every DB applies the same transfer step (translation invariance in Euclidean time), so the loss rate
is the same at every step: a homogeneous Markov chain **[classical]**; its contraction eta^n is **[Lean]** (`contracts_kpow`, II.12).

**Physical units.** A one-box contraction eta <= eta_0 < 1 at a fixed physical box size l_* = L_* a, uniform in the lattice spacing a,
gives a physical rate m_phys = -log eta / l_* >= -log eta_0 / l_* **[Lean]** (`phys_rate_of_uniform`, an inequality between the two
rates; the decay itself is `contracts_kpow` above). For a family of blocked kernels with one floor
eps_* for every spacing, the influence at physical distance D is at most exp(-m D) with m = -log(1 - eps_*)/l_* **[Lean]**
(`rdoeblin_physical_decay`).

| # | Result | Status | Source |
|---|---|---|---|
| III.3.1 | Per-box hand-over rate: max(F_tw, F_e) >= 0.881 at every box size | **[Lean]** (0 < Z_tw a hypothesis) | `Crossover/HandOver.lean`, `su2_handover` |
| III.3.1b | The same rate for every SU(N) sector of the twisted Wilson partition functions, unconditionally | **[Lean]** | `General/SUNHandOver.lean`, `sun_handover` |
| III.3.1c | Over all N centre sectors by the full turn: some nontrivial twist or electric free energy >= log(1 + sqrt N), and so does the mean over the nontrivial sectors of one type | **[Lean]** (positive electric sectors a hypothesis for N >= 3; proved for N = 2) | `General/SUNFullTurn.lean`, `sun_handover_full_turn`, `sun_handover_full_turn_mean`, `sunZel_pos_two` |
| III.3.2 | A flux-carrying outside forces at least one sheet | **[Lean]** | `Crossover/FluxRate.lean`, `exists_sheet_of_flux`, `even_card_fluxCells` |
| III.3.3 | The flux law is the same seen from inside and outside; no sources | **[Lean]** | `Crossover/Dichotomy.lean`, `cob_restrict_eq_cob_restrict_compl`, `sum_cob_restrict_eq_zero` |
| III.3.4 | Superadditivity up to the excess terms; the rate multiplies along a chain if F_e(L) > 2C, C bounding the excess act c(kL) on every multiple of L | **[Lean]** (abstract) | `Crossover/CompositeHTF.lean`, `flux_superadd`, `flux_superadd_iter` |
| III.3.5 | Uniformity along the chain | **[classical]**; eta^n **[Lean]** | translation invariance; `Mixing/Chain.lean`, `contracts_kpow` |
| III.3.6 | A one-box contraction at fixed physical size gives a physical rate (decay at the distances n l_*) | **[Lean]** | `Crossover/Neighbours.lean`, `phys_rate_of_uniform`; `Crossover/RDoeblin.lean`, `rdoeblin_physical_decay` |
| III.3.7 | The doubling law with a fixed loss gives the gap on all larger dyadic boxes | **[Lean]** (implication) | `Flip/Floor.lean`, `su2_gap_of_doubling_defect` |
| III.3.8 | Uncontained sheets weigh nothing (dichotomy part b) | **[Lean]** | `Crossover/Dichotomy.lean`, `measure_uncontained` |

So along a chain, one box at one scale is enough. The question is what a four-dimensional grid of boxes needs.

## III.4 Why a grid is harder than a chain

In a chain, flux entering a box has one way out. In a grid it can leave through any of the other 2d - 1 faces, so a box has 2d
channels to its neighbours, and Dobrushin's condition needs the **sum** of the influences over all channels below one (II.12).

**The hand-over covers two channels, not eight.** The per-box ratio sqrt 2 - 1 = 0.414 keeps a column sum below one for at most two
channels **[Lean]** (`handover_column_sum_iff`). A grid in d dimensions needs a per-box suppression F > log(2d), that is log 8 = 2.08
in d = 4, more than twice the duality floor **[Lean]** (`column_requirement`).

**A per-box floor (Doeblin) cannot supply it.** Doeblin's mass per box is at most e^{-K}/(1 - e^{-K}) with K = C beta L_*^{d-1}, which
goes to zero as the lattice spacing does: the calculus is **[Lean]** (`neg_log_one_sub_le`, `doeblin_mass_tendsto_zero`), the floor e^{-K} of the Wilson kernel with K = C beta L_*^{d-1} is **[paper]** (`RDOEBLIN.md`, 0). For a grid the floor exponent
must stay below log(8/7) = 0.134 (column form) **[Lean]** (`floor_column_requirement`), or below -log(1 - p_c), about 0.22 in the
disagreement-percolation form (the requirement `floor_disagreement_requirement` is **[Lean]** for any p; the value 0.22 uses the
site-percolation threshold of Z^4, p_c about 0.197, **[classical]** (recalled), claim III.4.3c). At the weak-coupling scale it is in the tens
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
| III.4.1 | The hand-over keeps a column below one for at most two channels; a grid needs F > log(2d) = 2.08 | **[Lean]** | `Crossover/Neighbours.lean`, `handover_column_sum_iff`, `column_requirement` |
| III.4.2 | Doeblin's mass per box goes to zero in the continuum | **[Lean]** (the calculus) + **[paper]** (the floor e^{-C beta L^{d-1}}) | `Neighbours.lean`, `neg_log_one_sub_le`, `doeblin_mass_tendsto_zero` |
| III.4.3 | A grid needs floor exponent below 0.134 (or 0.22, with the recalled threshold p_c = 0.197); at L_* it is in the tens | **[Lean]** (requirement) + **[paper]** (estimate) | `Crossover/RDoeblin.lean`, `floor_column_requirement`, `floor_disagreement_requirement`; `RDOEBLIN.md` |
| III.4.4 | Multi-sector duality forces nothing for n >= 2; the quantitative 't Hooft criterion | **[Lean]** (the relation itself **[paper]**) | `Crossover/Runs.lean`, `min_le_of_sector_product`, `selfdual_sector_ge_one`, `electric_sum_lt_one_iff` |
| III.4.5 | A gauge-covariant frame carries no gauge-invariant information | **[Lean]** (finite) + **[paper]** | `Crossover/CompositeHTF.lean`, `weight_fiber_eq`, `weight_fiber_mul_card`; `HTF.md` |
| III.4.6 | At typical fields the summed boundary influence drops below one at about 7 cells from the boundary (box of about 15 cells) | **[numerical]** (typical, not supremum) | `NEIGHBOURS.md`, 0.2 |

## III.5 Containment: the requirement moved inside one box

The first author's correction ("the saturation has to be proven inside confinement and absent outside that confinement, as a containing
existence", `PREP.md`) reverses the direction of the attack. Instead of building the inside of a box from outside data, prove three
things: outside, saturation is absent; the container ends; inside, saturation makes the influence run in tubes, and tubes are chains,
where III.3 closes. The first two close. The third closes negatively at the duality floor and positively above a sharp threshold.

**III.5.1 Outside, absence (lemma).** For every box, the twist ratio r = Z_tw/Z satisfies r < 1 and
r = (1 - e^{-F_e})/(1 + e^{-F_e}) <= F_e **[Lean]** (`twist_ratio_eq`, `twist_ratio_le_elecF`, `elecF_nonneg`). The twist is rare
exactly where electric flux is cheap. In a physically small box small-volume perturbation theory makes F_e of order g(L)^2
**[classical]** (Luescher 1983; van Baal 1984; recalled, not re-checked: that these works contain the statement was not read), so r = O(g^2). The mechanism outside is cheap electric flux, seen
from the other side of the duality as a rare twist.

**III.5.2 The container ends, in long boxes.** At fixed cross-section the transfer kernel is strictly positive (III.1.7). By
Jentzsch's theorem **[classical]** (Jentzsch 1912) the vacuum is the unique top state; it is centre-invariant **[paper]**, so the flux sector lies a
factor mu < 1 below it per unit length. Then F_e(T) >= -T log mu - log C grows without bound **[Lean]** (`elecF_lower_of_gap`,
`exists_elecF_ge`). In every long enough box the rarity branch fails, and by the hand-over the electric channel carries the
suppression. What this does not give: mu depends on the cross-section and may tend to one as it grows. In the cubic geometry the end
needs F_e(L) >= 0.881 at one L, that is g^2 of order one, beyond perturbative or M1 control **[open]**; measured near L = 4 at
beta = 2.3 (F_e = 0.91, **[numerical]**, preliminary).

**III.5.3 Inside: what the law gives.** Gauss's law makes electric influence a conserved line with no sources that no collar can
screen (III.3.2, III.3.3). That is the whole structural content of "tube", derived from the law without assuming tubes **[Lean]** for
the pieces, **[paper]** for the conclusion. The law does not say which path carries the influence: it allows every path and every
branching.

**III.5.4 Inside: what the cost must give.** Bound the influence between two boxes at distance D by a sum over paths of boxes, each
box costing e^{-F}. With mu continuations per step the sum is a geometric series in mu e^{-F}, which converges iff F > log mu **[Lean]**
(`path_sum_summable_iff`, `tube_threshold`). Self-avoiding paths on Z^d have connective constant mu_d >= d, and for mu >= 3,
mu (sqrt 2 - 1) >= 1 **[Lean]** (`path_entropy_beats_handover`). **So in every d >= 3 the duality floor 0.881 cannot meet the path-sum
criterion: the cheapest chain does not dominate the sum over paths** (a sufficient criterion fails; that is not a proof that influence
does not decay). For d = 4, mu_4 = 6.77 and log mu_4 = 1.91 is a series estimate **[numerical]** (Clisby-Liang-Slade 2007, recalled);
rigorously log mu_4 lies between log 4 = 1.39 and log 7 = 1.95 **[classical]** (sharper rigorous lower bounds exist, Hara-Slade-Sokal 1993). Equivalently, the single-sector twist ratio must exceed (mu - 1)/(mu + 1) = 0.74.

**With all N sectors (III.5.4d).** The full-turn rate log(1 + sqrt N) of III.3.1c grows with N, and it holds for the mean over the
N - 1 nontrivial sectors of one type, not only for their maximum (`sun_handover_full_turn_mean`). The boxes are copies of one another,
so the type is the same along a whole path, and a path that turns once through the sectors pays log(1 + sqrt N) per box on average:
the first author's refinement (II.13.4) **[Lean]** for the mean. The rate exceeds the series value log mu_4 = 1.91 from N = 34 on
(1 + sqrt 34 = 6.83) and the rigorous bound log 7 from N = 37 on. Not shown, and needed before it bounds the influence between two
boxes:

* that the influence travels along paths whose boxes turn through the sectors in this way (the sector a box passes on is set by the
  dynamics, not chosen);
* that the sector labels add no entropy of their own to the path count. This one fails by naive counting: labelling each box with one
  of its N - 1 sectors costs log(N - 1) per box, which equals log(1 + sqrt N) at N = 4 and exceeds it for every N >= 5. It holds only
  if the rotation itself fixes the sector sequence, as the first author's refinement reads it;
* that the per-box mean multiplies along a path with the excess act of III.3.4 paid, so that F(L) - 2C, not F(L), exceeds log mu;
* that the one-box reduction, formalised for SU(2), carries over to SU(N) for the N >= 34 the comparison needs;
* for N >= 3, the positivity of the electric sectors.

So for large N the grid gap is reduced to these steps, one of which fails unless the rotation fixes the labels; it is not closed
**[paper]** (claim III.5.4d).

**III.5.5 What the action adds and what it does not.** The Bogomolny bound S >= 8 pi^2 |Q| / g^2 **[classical]** gives, on a twisted
torus with odd twist product, the floor S >= pi^2 beta (beta = 4/g^2, the standard convention) for admissible fields **[classical]**
('t Hooft 1979; Luescher 1983, admissibility; Bogomolny 1976). It strengthens
III.5.1 for multi-plane twist sectors **[paper]**. It does not help the single-plane twist used here (that sector contains flat
configurations, so its floor is zero), nor inside (it bounds twists from above, while O1 needs them high) **[paper]**. At a fixed
physical box size the position entropy 4 log(L/a) of a fractional instanton beats its action pi^2 beta = 4 pi^2/g^2 = (11/3) log(1/(a Lambda)) (standard beta) as
a -> 0 **[paper]**, one-loop sketch (determinants and measure not checked).

**III.5.6 The one-box statement (O1).** Combining III.5.3 and III.5.4: law (structure) plus cost above entropy (dominance) gives tubes,
and tubes are chains, where III.3 applies. What remains is:

> **(O1)** At one box of fixed physical size, F_e(L) - 2C > log mu_4 = 1.91, with C a bound on the neutral excess act c(kL) of III.3
> on every multiple of L; in its Lean form, `FineOneBox` (below), uniformly over every boundary condition. **[open]**

The familiar form F_e(L) > 1.91 (equivalently r(L) > 0.74) drops the excess act, as E = mc^2 drops the momentum term of
E^2 = (pc)^2 + (mc^2)^2 (a **[reading]**). The drop is only seeming: c >= 0, so the full form implies the familiar one, but the
familiar one alone does not give the chain criterion (III.5.8, examples in Lean). The number is path counting (**[paper]**, III.5.9);
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

## III.6 The one box from inside: saturation and the dichotomy

**Saturation from what we have.** Configuration by configuration the twist changes the weight by at least e^{-2 beta N}, N = L^2
flipped plaquettes, so Z_tw/Z >= e^{-2 beta L^2} (weight exp((beta/2) tr U), the standard beta; with the Lean beta it is e^{-4 beta L^2}) **[Lean]**
(`ratio_floor_of_pointwise`, `exp_floor_ge_iff`; the pointwise weight bound for the Wilson action is an input of the Lean theorem, not
proved there). That saturates the twist, in the sense of a twist ratio of at least 3/7 (the threshold of
`proof-phase/c9a-crossover/SATURATION.md`), only for beta L^2 <= (1/2) log(7/3) = 0.42 (standard beta; 0.21 with the Lean beta);
with the self-dual threshold 0.414 of III.5 the bound is 0.44, with the tube threshold 0.74 it is 0.15: strong coupling in tick units, vanishing in the continuum. Conversely a large electric free energy forces a
saturated twist **[Lean]** (`twist_ratio_of_elecF`), so saturation is a consequence of O1, not an independent input.

**Bond-moving bounds localise Tomboulis's step, they do not avoid it.** Rigorous one-sided bounds on Z and on the even sector Z^+ exist,
and the upper decimation flows to strong coupling for every beta in d <= 4 **[classical, recalled]** (Ito 1985, for hierarchical lattice gauge theories of Migdal-Kadanoff type; its record was read, not the
bounds). A lower bound on the twist ratio
needs the two normalisations matched; the upper one is at least one **[Lean]** (`jensen_normalization`) and extensive in the box
volume. In the one-box form the mismatch is finite but vanishes at fixed physical box size **[paper]**, sketch. So the step needed is a
lower bound on the box partition function matched to the upper decimation's normalisation within O(1): Tomboulis's interpolation step
(Tomboulis 2007, arXiv:0707.2179; gaps pointed out by Ito and Seiler 2007 to 2009; not accepted as a proof **[classical]**), now localised to one box.

**The dichotomy inside one box.** Part (a), that a sheet plaquette always costs something, fails uniformly: at the SO(3) cut
(tr U_p = 0) a sheet plaquette is free **[paper]**. What survives: for every outside, the box contracts, or one of two bad events holds
(near-degenerate spanning surfaces for a flux-carrying outside; an SO(3) cut along a would-be sheet) **[paper]**. Rarity and
saturation are disjoint, with a window between them of about 0.18 to at least 1.79 nats per plaquette **[Lean]** (`window_gap`) +
**[paper]** (numbers).

| # | Result | Status | Source |
|---|---|---|---|
| III.6.1 | Tick-unit floor Z_tw/Z >= e^{-2 beta L^2} (standard beta; e^{-4 beta L^2} with the Lean beta); saturates only for beta L^2 <= 0.42 | **[Lean]** (pointwise weight bound an input) | `Crossover/Saturation.lean`, `ratio_floor_of_pointwise`, `exp_floor_ge_iff` |
| III.6.2 | A large electric free energy forces a saturated twist | **[Lean]** | `Saturation.lean`, `twist_ratio_of_elecF` |
| III.6.3 | Bond-moving: the one-box form localises the interpolation step (Tomboulis) to one box | **[paper]** (sketch); Jensen normalisation **[Lean]** | `SATURATION.md`, 0; `Saturation.lean`, `jensen_normalization` |
| III.6.4 | Kanazawa's bracket 1/2 < Z^+/Z < 1 (strict as printed, Z^+ = (Z + Z_tw)/2; Kanazawa 2009, Eq. 33) is the same statement as III.1.6, 0 < Z_tw < Z | **[classical]**; Lean form III.1.6 **[Lean]** | `SATURATION.md`, 0 |
| III.6.5 | Dichotomy part (a) fails uniformly at the SO(3) cut | **[paper]** | `DICHOTOMY.md`, 0.2 |
| III.6.6 | Reduction to two bad events | **[paper]** | `DICHOTOMY.md`, 0.4 |
| III.6.7 | Window between rarity and saturation, 0.18 to >= 1.79 nats per plaquette | **[Lean]** (disjointness) + **[paper]** (numbers) | `Crossover/Dichotomy.lean`, `window_gap`; `DICHOTOMY.md`, 0.3 |
| III.6.8 | Y2 to Y5: inside residue, hand-over through the window, condition A uniformly (m about 4 measured on typical fields), uniformity in volume | **[open]** (pieces of O1); per-volume gap **[Lean]** conditional on H2-all | `docs/OPEN-QUESTIONS-DMP.md`, 2; `Quantum/PerVolume.lean`, `perVolumeGap` |
| III.6.9 | IR column at L1: W1 column certified at 0.99988 at L sqrt(sigma) = 2.80 (computer-assisted certificate as a named hypothesis) | **[open]**; implication **[Lean]** | `Certified/Measured.lean`; `proof-phase/c9b-adjoint/ROUTE3.md` |

## III.7 Measured: what the numbers say about O1

Measurements can refute O1, never establish it (provability rule, `proof-phase/c9b-adjoint/REDESIGN.md`, section 8). Every error bar
is max(statistical floor, resolution floor), the resolution floor of an energy read over Euclidean extent T being 1/T in lattice
units; ad-hoc floors are not used; a change of floor after data is reported beside the pre-registered result (`attempts/RULES.md`,
last section).

**III.7.1 Small tori (preliminary).** At beta = 2.3 the cubic twist ratio crosses the tube threshold between L = 4 (r = 0.425, at the
self-dual value) and L = 6 (r = 0.86, F_e = 2.6). Central values pass the familiar form F_e > 1.91 at L = 6 (the excess act c(L) was not measured, so O1 itself is untested), but the one-sided 95 % lower bound of F_e is 1.26
statistically and 0.96 with the resolution floor: **not certified** **[numerical]** (`CONTAINMENT.md`, 1 and 3; `SATURATION.md`, 0).
At beta = 3.5, L = 2: r = 0.018, F_e = 0.035, as III.5.1 predicts.

**III.7.2 The chain criterion at a large cross-section.** The pre-registered check of F_e(L) > 2c(L) on chains of cross-section 16^3
refuted it at beta = 3.5, L = 1, at 99 % **[numerical]**. Re-scored post hoc under the universal floor, the refuted range grows to
L <= 2 (both levels) and L = 3 (95 % only). At beta = 2.3 no test was possible (no flux bound). This geometry is not the cubic one of
O1, so it bears on O1 neither way; it says only that at that cross-section and coupling the electric multiplication needs L >= 4
(`ONEBOX-CHECK.md`, 4, 5, 7).

**III.7.3 The cubic one-box geometry is untested by saved data**; a small-torus simulation is pre-registered (`ONEBOX-CHECK.md`, 8).

**III.7.4 The mirror reading.** The identity 8 pi^2 = -4 zeta(2)/zeta(-1) is derived in Lean from Mathlib's functional equation
**[Lean]** (`GRH/Mirror.lean`, `eight_pi_sq_mirror`, `zeta_neg_one_val`); it is the k = 1 member of a classical family. In Yang-Mills it
brackets F_e(L) between two asymptotic ends: the Luescher term (zeta(-1)) at the infrared end, fractional instantons (4 pi^2/g^2) at
the ultraviolet end. In effective-string terms the familiar form of O1 becomes L sqrt(sigma) > 1.72 (Luescher) or 1.80 (Arvis), just
above the string's breakdown at 1.45 **[numerical]** (an evaluation of the model formulas, not a measurement), using the effective
string as a model, and using sigma > 0, which is confinement, the property being proved. The mirror does not constrain F_e between the two ends, where
O1 sits **[reading]** for "brackets" (`docs/rh-guide/MIRROR.md`, 0.2).

| # | Result | Status | Source |
|---|---|---|---|
| III.7.1 | Small tori at beta 2.3: F_e(6) = 2.6 centrally (familiar form only; c(L) not measured), lower bound 0.96 with the floor; not certified | **[numerical]** (preliminary) | `CONTAINMENT.md`, 1, 3; `SATURATION.md`, 0 |
| III.7.2 | Chain criterion refuted at cross-section 16^3, beta 3.5, L = 1 (pre-registered); L <= 2 post hoc | **[numerical]** | `ONEBOX-CHECK.md`, 4, 7 |
| III.7.3 | The universal error-bar floor max(statistical, 1/T) | **[paper]** (a design rule) | `attempts/RULES.md`, last section |
| III.7.4a | 8 pi^2 = -4 zeta(2)/zeta(-1); zeta(-1) = -1/12 | **[Lean]** | `GRH/Mirror.lean`, `eight_pi_sq_mirror`, `zeta_neg_one_val` |
| III.7.4b | Familiar form of O1 in effective-string units: L sqrt(sigma) > 1.72 to 1.80 (evaluation of the model; uses sigma > 0) | **[numerical]** (model-based) | `docs/rh-guide/MIRROR.md`, 0.2 |

## III.8 "It runs": the formal target shared with GRH

Both Yang-Mills and GRH ask about an evolution that does not increase a positive norm. If T is a contraction on a normed space, the
GRH-type conclusion is that every mirrored mode is a phase; the Yang-Mills conclusion is that, with ||T x|| <= eta ||x|| on the neutral
sector and eta < 1, there is no phase mode there, and iterates decay as eta^n **[Lean]** (`no_phase_mode`, `iterate_contraction`,
`runs_two_targets`; GRH side `GRH/Tate.lean`, `runs_and_mirror_on_line`). The open steps are complementary: Yang-Mills has the positive
norm for free (reflection positivity) and lacks the margin eta < 1; GRH lacks the positive norm (Weil positivity) and needs no margin
(Part X).

| # | Result | Status | Source |
|---|---|---|---|
| III.8.1 | "It runs" in two targets: phases (mirror) and no phase mode under a margin | **[Lean]** | `Crossover/Runs.lean`, `no_phase_mode`, `iterate_contraction`, `runs_two_targets` |

## III.9 The weak-coupling side and the continuum (inputs from outside the gap mechanism)

| # | Result | Status | Source |
|---|---|---|---|
| III.9.1 | UV stability, small-field control and one-loop running at the weak-coupling unit scale (the OpenAI submission of 28 October 2026 and the `yang-mills-group` assessment of 10 November 2026, not refereed; see below) | **[external]** | `H1-OPENAI.md`; `references.md` (OpenAI submission) |
| III.9.2 | Balaban's large-field control preserves partition functions, not laws (Balaban 1987 to 1989, five papers in CMP) | **[classical]**, read where it bears on the claim | `proof-phase/c5d-supplier/BALABAN-READING.md` |
| III.9.3 | M1: the law-preserving large-field step, at weak coupling up to L_* | **[paper]**, complete at paper level; Lean parts | `M1/Assembly.lean` (`m1_assembly`); `proof-phase/m1-tools/M1-PLAN.md` |
| III.9.4 | The continuum limit exists (mesh limit at fixed volume, then volume along a subsequence; selected phase; fields smeared away from coincident points) | **[external]** | `H1-OPENAI.md`; `Existence/Bridge.lean` (`plaqLaw_eq_wilsonMeasure`) |
| III.9.5 | (O2) The gap needs of the line of constant physics only its resolution clause (l_k -> infinity); with O1 in its one form it gives torus decay, the gap in both orders of limits and reflection positivity; the running clause (one-loop slope 11/(6 pi^2), Lean beta), the scheme clause and non-triviality are not used | **[Lean]** | `Closures/OneBoxForm.lean` (`tendsto_a_of_resolution`, `gap_of_o1Form`, `yang_mills_assembly_onebox_of_resolution`); `Assembly.lean` (`OnLCP`, `NonTrivial`) |
| III.9.5a | (O2) Per box, by construction: the reflected correlation at even time is a reflection-positivity square, hence non-negative for observables of the positive half; this is not non-triviality (strict positivity is not claimed); the running clause holds by construction on the one-loop line | **[Lean]** | `Closures/NonTrivialSplit.lean` (`wcorr_even_eq_rpForm`, `wcorr_even_nonneg`, `nonTrivial_of_uniformLower`, `oneLoopTuning`, `running_oneLoop`) |
| III.9.5b | (O2) The scale-uniform lower bound c > 0 on a slab correlation at a fixed physical time and the scheme clause: the lower edge of the window whose upper edge is O1's gap (independent of O1 and compatible with it in the spectral model, **[Lean]**); placed at the ODP's end, a reading | **[open]**; part of the one assumption by the first author's reading (X.64a) | `Closures/NonTrivialSplit.lean` (`lower_of_spectral_weight`, `gap_not_lower`, `gap_and_lower_compatible`); X.64a |
| III.9.6 | (O3) Euclidean invariance, local fields as distributions, Wightman reconstruction, short-distance agreement: claimed for the external construction in its selected phase and for its fixed-stencil fields (partial); uniqueness of the limit is not claimed there | **[external]** (partial) for the external construction; **[open]** for ours, and uniqueness of the limit **[open]** for both | `PROOF-BLUEPRINT.md`, P6.2, P6.4 to P6.9, P7.6 |
| III.9.7 | (O4) Every compact simple group: existence external; this project's tuning SU(2) only | **[external]** / **[open]** | `PROOF-BLUEPRINT.md`, P6.10 |

**The external construction.** III.9.1, III.9.4, III.9.6 and III.9.7 rest on one source: the Lean 4 submission of 28 October 2026 by
OpenAI to the pure Yang-Mills problem, posted with the hosting group's checks and its Assessment 1 (dated 10 November 2026) in the
public repository of the group `yang-mills-group` (`references.md`). In the assessors' stated opinion it proves that a relativistic
quantum field theory satisfying the Wightman axioms can be constructed as a scaling limit of four-dimensional Wilson lattice gauge
theory for any simple compact gauge group; they state that it does not prove that the infinite-volume limit is unique or that there
is a mass gap. This project read the repository's description of the package and its own study of it (`H1-OPENAI.md`) and did not
rebuild the package. The repository says that posting is not endorsement or certification, and no refereeing is stated there; the
mark **[external]** here means "others' result, read, not rebuilt", not "accepted". The scope that matters for this part: the
construction controls the flow only down to a reference coupling deep in the perturbative regime, far from order-one coupling; the
reconstruction is for a selected phase; the volume limit is along a subsequence; the fields are smeared against tests supported away
from coincident points; the independent check of the Osterwalder-Schrader bridge covers a selected scalar family; and it does not
establish an intrinsic continuum mass (`H1-OPENAI.md`, 1, 2 and 5).

M1 hands over at a weak-coupling scale: the coupling becomes of order one only after the crossover. So the floor M1 supplies at L_*
is uniform in the spacing but tiny, and it gives a physical-units gap only along a chain at fixed cross-section (III.3.6), not on a
grid (III.4.3) **[paper]** (`RDOEBLIN.md`, 0).

## III.10 DMP readings attached to this part (all [reading])

* **Outside, non-existence keeps existing through assertion.** The twist is rare because electric flux costs almost nothing: one fact
  seen from the two sides of the duality (III.5.1).
* **The container must end, and does, along the run.** "It can never catch up" in exact form: Z_1/Z_0 <= C mu^T, mu < 1 (III.5.2).
* **Inside, existence has to outrun possibility.** Of the mu continuations per step only one is the tube; the tube dominates only if
  its cost per step exceeds log mu. The balanced state (0.881) is not enough (III.5.4). This is "existence = non-existence + 1" in
  counting form.
* **IM is both sides.** Gauss's law is the same statement on both sides of every DB; it makes every tube possible, and the action has
  to make one tube cheaper than all others combined (III.5.3, III.5.4).
* **The pressing as the instanton of the first act.** The Bogomolny bound is a worst-case floor proved before any dynamics runs; it
  prices the rare side and loses logarithmically to entropy as the tick shrinks (III.5.5).
* **The duality is never alone while running.** The 't Hooft relation is kinematic and chooses no branch; the action selects it
  (III.4.4).
* **The crossover is confined by making no statement about its content** (III.2).
* WHKs: group plus one scale fix everything (dimensional transmutation, **[classical]**); mass gap = the arrow of causality exists
  (I.7); only 3+1 transmutes, g^2 being dimensionless only in d = 4 **[classical]**.

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
