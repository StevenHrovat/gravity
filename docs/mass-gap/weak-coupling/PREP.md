# The weak-coupling region: preparation (2026-11-21)

Prepared for the next phase (the owner, 2026-11-21: "tackle the weak coupling region, as that seems to be the final frontier").
Companion file: `SURVEY-LEAN.md` (what existing Lean projects contain in this region; reference only, nothing is reused). Our rule:
central parts are built by us from scratch; others' work is reference and a check (memory "build vs reuse").

## 1. The problem in one picture

Three regions of the same lattice theory, from fine grid to coarse grid (README §4):

| region | coupling | status | our formal tools |
|---|---|---|---|
| short distances (fine grid) | g small, β large | a continuum theory exists along a subsequence (OpenAI's Lean construction, validated 10 Nov 2026 by the committee of Gross, Douglas, Jaffe, Klebanov, Nekrasov); "no evidence for or against a mass gap" | none of ours |
| **middle range** | g ~ 1 | **open: the bridge** | none yet |
| long distances (coarse grid) | g large, β small | gap, confinement, reflection positivity: proven (1978 on); now also ours in Lean | `AreaLaw.Clustering` (gap, any group), `AreaLaw.Twist*` (area law, SU(n)), `AreaLaw.Reach` (reach, existence floor), `Positivity` (site and link RP), `Influence` (sharper Dobrushin) |

**The Bridge** (README §4.C), as one lemma: there are a physical length L₀ and q < 1 such that, along the scaling sequence, the theory
block-averaged to cells of size L₀ satisfies a contraction of the kind our strong-coupling theorems use, with the same q for every
lattice spacing and every volume. With it, our clustering theorem gives the gap uniformly; without it, nothing. The Bridge is as hard
as the problem: it localises the difficulty, it does not reduce it.

**The photon test** (README §3.2) constrains every route: a valid argument must fail for four-dimensional U(1) at weak coupling,
which is massless. Our layer computation (README §5) puts a number on it: in the tree picture light drifts towards confinement by
10⁻⁵ to 10⁻¹³ per layer, so a layered proof must control effects of that size and must use non-commutativity.

## 2. What the literature offers (references, for ideas and checks)

### Rigorous renormalisation group (the direct attack on the middle range)
- **Balaban's programme** (1983–1989): renormalisation group for lattice gauge theories in 3 and 4 dimensions, small-field effective
  actions and coupling renormalisation in 4D, cluster expansions (Commun. Math. Phys. 116 (1988) and the series around it). Ultraviolet
  stability for pure Yang–Mills in d = 3, 4 in finite volume; it does **not** reach the infrared (large distances, where confinement and
  the gap live). Whether the 4D UV stability is complete is debated in secondary sources.
- **Dimock's exposition** "The renormalization group according to Balaban": I small fields (arXiv:1108.1335), II large fields
  (arXiv:1212.5562), III convergence (arXiv:1304.0705, on φ⁴₃); QED₃ (arXiv:2009.01156). The readable entry point to Balaban's method.
- **Magnen, Rivasseau, Sénéor** (1993): SU(2) Yang–Mills in 4D with a fixed infrared cutoff and the UV cutoff removed, in a
  regularised axial gauge. Again UV only.
- **`balaban-lean`** (Lean, Apache-2.0): Balaban's low-temperature RG for the **O(N) spin model**, not gauge theory; about 1.09M lines,
  unfinished (its two main theorems are frozen `sorry` placeholders, six mathematical blockers recorded). No Lean formalisation of
  Balaban's gauge-theory RG exists (`SURVEY-LEAN.md`). The OpenAI construction uses a Balaban-style RG map for the short-distance end.

### Probabilistic and analytic routes (strong-coupling side, pushing outward)
- **Chatterjee**, "A probabilistic mechanism for quark confinement" (Commun. Math. Phys. 2021, arXiv:2006.16229): exponential decay of
  correlations of local operators under **arbitrary boundary conditions** plus a nontrivial centre implies the area law. Mass gap (in
  that strong sense) ⇒ confinement. Relevant for us: it is the converse direction of "confinement ⇒ gap" and uses the centre, like our
  twist proof.
- **Shen, Zhu, Zhu** (arXiv:2204.12737; SZZ23 on SO(N), SU(N)): gap by Bakry–Émery curvature of the group, β < 1/(16(d−1)); Langevin
  dynamics. Best SU(N) strong-coupling window by a soft method.
- **Cao, Nissim, Sheffield** (arXiv:2505.16585): expanded regimes of the area law for U(N), large N.
- **Survey**: "Lattice gauge theory and Wilson-loop confinement: a statistical-mechanical survey" (arXiv:2605.02156): area law and
  mass gap are related but distinct.
- **Stochastic quantisation**: Chandra, Chevyrev, Hairer, Shen (2D; 3D Yang–Mills–Higgs Langevin dynamics, Inventiones 2024,
  arXiv:2201.03487; review Chevyrev, J. Math. Phys. 2022, arXiv:2202.13359). The 3D pure Yang–Mills measure is open even in finite
  volume; local existence of the 4D dynamics is a major open problem.
- **Tomboulis** (arXiv:0707.2179) and **Ito–Seiler** (arXiv:0711.4930, 0803.3019): the bracketed decimation attempt and why it fails the
  photon test (README §5).
- **3D**: Nair's outline of a 3D proof (arXiv:2608.10133, unreviewed).

### Numerical bridges (non-rigorous, but they are exactly the middle range, measured)
- **Step scaling** (Luescher, Weisz, Wolff 1991; Luescher, Narayanan, Weisz, Wolff, Schroedinger functional; ALPHA collaboration): define a
  coupling at box size L, double the box, measure the new coupling, iterate; the step-scaling function σ(s, u) is the measured layer map
  from weak to strong coupling. SU(2) quenched studies (e.g. hep-lat/9411017, hep-lat/9407028). **This is the numerical version of the
  owner's layer picture and of the Bridge lemma**, with the real lattice instead of the Migdal–Kadanoff tree.
- **Gradient (Wilson) flow** (Luescher, arXiv:1006.4518): a continuous smoothing that defines renormalised observables at every scale;
  the modern standard for running couplings and scale setting. A continuous version of "restoration one layer per round".
- **Bootstrap** (Kazakov–Zheng 2203.11360, 2404.16925; SU(3) 2502.14421; abelian 2404.17071; loop equations 2601.04316): rigorous
  bounds from consistency at every β, including the middle range. Our own bootstrap is running now.

### 2026 claims (unrefereed; checked only by abstract)
Several Zenodo/ResearchGate preprints of November 2026 claim strong-coupling gaps with explicit constants and state that the
intermediate-coupling step remains open (e.g. "A conditional continuum theorem and anisotropic terminal gap bounds for SU(3) lattice
Yang–Mills", Zenodo 24105658; "The Yang–Mills mass gap from one bound at one scale", Zenodo 24178376/24200747). None shows a rigorous
bridge. Some claim full proofs; none is validated.

## 3. Our tools, as of today (all built here, Lean 4.34, verified)

- **Gap / reach at strong coupling** for any compact group (`wilson_clustering`, SU(2), U(n), SU(n), SU(3)), window
  (16d)²(1 − e^{−4n|β|}) < 1; uniform in the volume; the two-copies identity `cov_two_copies`.
- **Area law** by the centre twist for SU(n), U(n) (window 2(d−1)(1 − e^{−2n|β|}) < 1, d = 4: standard β < 0.091) and by cluster
  expansion (tiny window); `twist_term_vanish` (MG3).
- **Reflection positivity** for site and link reflections, Gram matrices, Cauchy–Schwarz; Haar inversion invariance for compact groups.
- **Influence bounds** (TV lemma, tanh(nβ) per link).
- **DMP side**: `Reach.lean` (existence floor), `MassGap.lean`, `Gauge.lean` (dictionary, `contraction_decay`).
- **Numerics**: validated SU(2)/U(1) GPU code (100× CPU), plateau analysis, TTL scan β = 2.3–2.7 with continuum extrapolation, vortex
  code, strong-coupling scan (running), Luescher runs, the bootstrap (running), Migdal–Kadanoff flow (exact).

## 4. Candidate routes for the voyage (for discussion after the restart; not decided)

1. **A finite-size bridge, rigorous at one scale ("one bound at one scale").** The Bridge only needs a contraction at *one* block
   scale L₀, uniformly in the lattice spacing. Our strong-coupling theorems give the contraction once the blocked theory is at strong
   coupling. Route: (a) measure the step-scaling flow from the 2.3–2.7 region down to the region where our window holds (how many
   layers, how large the blocked coupling); (b) bound the blocked theory rigorously at that one scale, with computer-assisted bounds
   (bootstrap-style certificates, interval arithmetic) instead of perturbation theory. Realistic outcome: a sharp, quantified statement
   of what one bound at one scale would have to show, and a numerical certificate that it holds on our lattices; not a proof.
2. **Push the strong-coupling side outward.** Our windows (β_std < 0.09 for the area law; much smaller for clustering) are far below
   the physical β ≈ 2.3. Better counting (walks instead of animals), better single-link bounds (`Influence`), block (Dobrushin–Shlosman)
   conditions, and the bootstrap's rigorous bounds can move the proven region. Each factor is a theorem; the gap to β ≈ 2.3 is large.
3. **Reflection positivity + clustering ⇒ transfer-matrix gap, then a uniform version.** We now have both ingredients at strong
   coupling. Assembling them into a spectral-gap theorem for the transfer matrix (finite volume, uniform in the volume) closes the loop
   of the reading (reach in space = TTL in time, `mg_space_time_certificate`), and gives the object a weak-coupling argument would have
   to bound.
4. **Centre symmetry route (Chatterjee).** Gap under arbitrary boundary conditions + centre ⇒ confinement. Our twist machinery is the
   same mechanism. A formal version would tie confinement and gap together in both directions at strong coupling, and isolate what a
   weak-coupling proof must supply (the boundary-uniform decay).
5. **The DMP reading as a guide.** In DMP terms the Bridge says: the reach of an IM act is the same at every layer. Our layer picture
   failed the photon test because it kept only "the coupling grows"; the non-abelian content (gluons carry the charge they transmit;
   `nonabelian_loop_value_moves`) must enter the per-layer bound. A candidate DMP-native quantity to track per layer: the centre-vortex
   density (the MG3 twists) or the twist free energy ('t Hooft), which is known numerically to signal confinement at all couplings, and
   which vanishes for U(1)'s Coulomb phase (passes the photon test by construction).

Honest frame for the voyage: nobody has crossed the middle range; the realistic aim is a new, precise, checkable piece (a theorem, a
certificate, or a sharp reduction), reported at its true claim level.
6. **DMP-admissible Yang–Mills (the owner's idea, 2026-11-21).** The owner: DMP "doesn't allow any not DMP complete system to exist",
   so "there may be some configurations in Yang–Mills that simply are not DMP complete", and DMP "settles the question of existence for
   any system that can be described in it". In physics this is a selection rule on configurations, legitimate if it is local and gauge
   invariant, keeps reflection positivity, and does not change the continuum limit (universality). Physics has such rules: Luescher's
   **admissibility condition** (every plaquette's shortfall ‖1 − U_p‖ below a bound: DMP's balance rule, "shortfall per loop stays
   bounded", word for word), used for topology and chiral gauge theory with the same continuum limit; and the Gribov–Zwanziger
   restriction of gauge copies. Admissibility removes **large fields** by construction, the part where Balaban's programme (and
   `balaban-lean`'s open blockers) are stuck. Checks built in: admissible U(1) keeps a massless photon (the rule alone does not make a
   gap: photon test passed); the MG3 twists must be admissible, since removing them removes confinement (our vortex test). Plan:
   (a) prove reflection positivity of the admissible measure with our `Positivity` tools; (b) measure the fraction of plaquettes above
   the bound at β = 2.3–2.7 on the GPU (if it vanishes as the grid is refined, the rule is physically free); (c) re-examine the
   weak-coupling attack (route 1, route 3) on the admissible theory, where the large-field problem is absent. References to read:
   Luescher, "Topology of lattice gauge fields" (Commun. Math. Phys. 85 (1982) 39) and the admissibility literature on lattice chiral
   gauge theories; Zwanziger on the Gribov horizon.

## Guiding principle for the open hypothesis (the owner, 2026-11-21)

The one open hypothesis of the reduction (`UniformGDS`: a box of fixed physical size forgets its boundary by the same margin at every
grid fineness) is, in DMP terms, Axiom 1's reach at every layer: inevitable inside DMP, to be proven for Yang-Mills hosted as content.
The owner's reading of *why*: "What light does not have is existence/mass, which is the part of the duality that is affected by the need
to assert itself. Information without existence has no causality, so by itself there is no path prescribed. [...] Since they [gluons] are
IM, they exist, so they are bound to it."

Physics translation: light's carrier has no charge (no self-interaction, free superposition, nothing pins its paths: massless); a gluon
carries the colour charge it transmits (a source of its own field, bound by it). In gauge theory "the carriers carry charge" and "the
order of transports matters" (`nonabelian_loop_value_moves`) are the same property, so "the path is prescribed" and "gluons exist" are one
fact seen from two sides (finding MG5). Precision: gluons have no mass of their own; their "existence" in this reading is their
self-charge, and the mass appears in the bound states, which is the gap to be proven. Chain to be made a theorem: self-charge (existence)
⇒ bound to its own field (prescribed path) ⇒ bounded reach, the same at every layer ⇒ mass of the bound states.

Use: the **layer inequality** (if a box forgets its boundary at spacing a, it does at a/2 without loss) must use the self-charge, since it
must fail for U(1) (photon test). Leg B's data across β show how the boundary influence actually changes from one fineness to the next:
the numerical shape of that inequality, to look at before any proof attempt.

Refinement (the owner, 2026-11-21): "Inside confinement they [gluons] possess inherent existence and can thus be massless, in the case of
the (non-photon) Bosons, they leave confinement and are thus imbued with an inherent existence/mass." Three cases, matching physics:
gluons (inside the bound state, existence guaranteed: massless, never alone); W and Z (act on their own, outside any bound state: massive,
80 and 91 GeV, short range); photon (payload, no existence: massless, free). Precision: in physics W and Z get their mass from the Higgs
mechanism (electroweak symmetry breaking) and the weak force does not confine; "leaving confinement requires an inherent existence" is
the owner's reading of why a carrier acting on its own must carry mass. It matches the outcome of the Higgs mechanism, not its derivation.

Stated generally (the owner, 2026-11-21): "To exist outside of confinement requires an inherent existence/mass." Checkable form: every
particle that exists (is not payload) and is not confined has mass. Against the Standard Model: quarks and gluons (confined: existence
guaranteed inside); charged leptons, neutrinos (tiny but nonzero mass, from oscillations), W, Z, Higgs (unconfined, massive); photon
(payload, massless): consistent throughout. Edge case outside this work: a hypothetical massless graviton; in the GUID reading gravity is
the existence field itself and needs its own classification (GUID series, not here).

## Decision rule for the layer-inequality attempts (fixed 2026-11-21, before any SU(2) result of Leg B exists)

The owner: "If the Leg B data is halfway promising, I'd at least want to throw a couple attempts at it, see what sticks, and what ideas
might pop out." Leg B counts as halfway promising if at least one holds (`../lattice/PREREG-BOUNDARY.md`, SU(2) phase):
1. the boundary-influence length in physical units (Q1, typical against calm) is consistent with a constant over β = 2.3–2.7, or drifts
   by less than a factor 1.5 with no growing trend;
2. at the larger box (ℓ·a√σ ≈ 4.2) the twisted boundary is seen as a random vortex, not a spread field (Q2(b) passes there);
3. at the same physical box size, the influence at the finer grid is never larger than at the coarser one within errors (the numerical
   shadow of the layer inequality).
None holding: the data argue against a fixed reach, and that is written up as the result.

If promising: one round of independent proof attempts in parallel, each with an adversarial check and each required to fail for U(1):
(a) the twist route (centre twists, as in `AreaLaw/Twist*`), (b) the positivity route (reflection positivity, chessboard estimates,
comparing spacing a/2 with a), (c) the admissible route (route 6: a Balaban-style single step without large fields), (d) the self-charge
route (the guiding principle above: non-commuting transport bounding the reach). Each ends in a precise lemma (proved or reduced) or a
documented failure; the ideas that come out go into the record either way.

## Lead route for the attempt round: a flow for the influence, read as a root swap (2026-11-21)

**The approach (proposed by the coordinating session, adopted by the owner).** Do not track the coupling from layer to layer (the
Migdal–Kadanoff tree and Tomboulis's decimations did that and failed the photon test). Track the quantity the reduction needs: the box
influence κ(ℓ) on boxes of growing side ℓ at a fixed grid, and look for a recursion κ(2ℓ) ≤ f(κ(ℓ)) (a box of twice the size given its
eight sub-boxes). Then: (1) uniformity in a becomes a fixed-point property of f (more doublings inside a box of physical size L₀ only help
if f contracts); (2) the photon test is built in (for U(1), κ(ℓ) grows like ℓ: no contracting fixed point; Leg B feasibility shows the flux
passing through); (3) f is local (one box and its sub-boxes: DMP's restoration one layer per round, applied to the disturbance instead of
the coupling), so it can be measured and possibly certified at bounded size; (4) the proof engine is reflection positivity (proven,
`Positivity`): by chessboard estimates, an influence crossing a large box needs a "bad event" spanning it, bounded by the single-block
probability to the power of the number of blocks. Deliverables: κ(ℓ) at several ℓ (Leg B's two box sizes first, then more sizes at one β
if the decision rule says go); a Lean theorem "a contracting recursion for κ implies `UniformGDS`"; the chessboard bound as the attempt.

**The owner's reading of the bad event (2026-11-21).** "The confinement is, in DMP terms, an existence boundary. [...] the causal chain,
which ties something to existence, switches at that boundary. [...] everything that exists within it is tied to that G0 by the causal chain,
with the mass bosons tied to it through the Higgs field. Once something crosses an existence boundary, like when entering a black hole or
entering confinement, the definition of existence, so the G0 that is defined as root for that node, swaps over."

Physics translation (the root swap): by Gauss's law a charge exists only anchored by a field line (a dressing, a Wilson line) to
something that absorbs its charge. Electromagnetism anchors at infinity cheaply (the global root): free charges exist. In the confined
phase anchoring colour to infinity costs σ per unit length (infinite), so colour anchors locally, to an anticharge in the node: **the node
is its own root**. At high temperature (deconfined) a global colour root reappears. The order parameter for "is there a global root" is the
Polyakov loop (zero when confined: unbroken centre symmetry, no global colour root; nonzero when deconfined); the centre symmetry is the MG3
twist, a change of the root's frame no local check sees, and it is the extra ingredient in Chatterjee's theorem (decay + unbroken centre ⇒
confinement). Applied to the lead route: the **bad event** is "a block lets an anchoring line through: the outside root leaks across the
existence boundary"; the chessboard bound needs this to be rare in a single block, and the root swap is the reason it should be (crossing
an existence boundary forces a root swap, which a cheap line cannot carry). Photon test: light is anchored at infinity cheaply, so its lines
pass every box. Observable already recorded by Leg B: the straight lines across the box from face to face (anchoring lines from the outside
root through the node); how their cost grows with box size is a direct numerical look at the root swap. The black-hole part of the reading
is outside what this work can test and is not used here (GUID series).

**Attempts started before the data (the owner, 2026-11-21, 16:50).** "Is there any harm in just going ahead with the proof attempts and
just using the tests that run now to test it later on?" No: the decision rule above was a resource gate, not a scientific one. The attempt
round starts now, before any SU(2) Leg B result exists; the attempts therefore cannot be tuned to the data. The rule's role changes: it
now decides how the attempts' results are weighed (if the data argue against a fixed reach, an attempt that claims one must contain an
error, which is used as an adversarial check). Five routes in parallel: the lead route and (a)-(d), outputs in `attempts/<route>/`.

## The effective-theory split in DMP terms (the owner, 2026-11-21)

`gap_of_effective_W` (`../formal/OneScale/Effective/Physical.lean`) replaces the uniform one-box hypothesis by (H1) `EffectiveConvergence`
(the theory zoomed out to blocks of physical size L₁ converges as the grid is refined) and (H2) `LimitGDS_W` (that single limiting theory
satisfies the one-box bound), glued by a proven robustness lemma. The owner: "H1 is the definition of how something can exist and H2 is
the definition of what existence is." Reading: H1 is the path from the fine grid up to the node's scale, the causal chain through the
layers along which an existence is built; H2 is the certificate at one scale, a node that forgets its outside by a fixed margin.

Refinement (the owner, 2026-11-21): "That also splits it neatly into H1 as the quantum half and H2 as the classical half, both only valid
together." Physics: H1 is where the quantum (loop) effects live: the running of the coupling (asymptotic freedom) is a one-loop quantum
effect, without which the theory generates no scale; H2 is a statement about one fixed effective theory at one scale, a strongly coupled
statistical system of block variables (classical statistical mechanics, no running, no limit). H1 alone gives a theory without gap
information; H2 alone concerns some coarse lattice system unconnected to continuum Yang-Mills; only the pair gives the gap. Mirrors the
duality: the information half and the existence half, neither sufficient alone. Precision: on the lattice both halves are probability
measures; "quantum" means the regime governed by loop corrections, "classical" the regime where the effective theory behaves as a classical
strongly coupled system.

## Tools for H2 from the existence half's language: curvature (the owner, 2026-11-21)

The owner: "Since GR fits perfectly as the existence half of DMP, we can use the already highly developed tools that come with that
'language' to use it in our approaches, wherever H2 needs tools." The mathematical core of GR is curvature, and curvature does what H2
needs: positive Ricci curvature bounds the diameter (Bonnet–Myers: bounded reach) and gives a spectral gap (Lichnerowicz). These tools
exist beyond smooth spaces: Ollivier's coarse Ricci curvature of Markov chains (2009) is positive exactly when the chain contracts in
Wasserstein distance, which is the W form of the one-box bound; Dobrushin's condition is a special case, and Ollivier treats spin-system
Glauber dynamics as examples; Bakry–Émery and Lott–Sturm–Villani curvature belong to the same family (Shen–Zhu–Zhu's strong-coupling gap
uses the curvature of SU(N)). Restatement of H2: the block dynamics of the effective theory at scale L₁ has positive coarse Ricci
curvature. Fit with round 1: route (d) found the group curvature swamped at weak coupling at the lattice scale; at L₁ the effective theory
is strongly coupled, where curvature can dominate. DMP reading: existence as positive curvature (a node closes on itself: bounded
diameter, a gap; light is flat). Precision: this uses the mathematics of GR (curvature, comparison geometry, optimal transport), not
Einstein's equations; the gap does not depend on gravity.

## Why the reverse fails: existence boundaries (the owner, 2026-11-21)

`H2-CURVATURE.md`: W-form GDS implies positive coarse curvature, the converse fails (curvature takes the worst boundary once for the whole
system; GDS per block). The owner: "That is exactly why the forces split. The classical side is horrible at asserting itself so takes the
first opportunity to erect an existence boundary so that it does not have to be lossy. (VIBE coefficient in prior work)" Reading:
curvature is a global existence certificate, GDS a per-node one; the difference between them is the existence boundaries; global
assertion over large regions is lossy (the VIBE coefficient: keeping an act existing costs h·(1/c)·α per h, Balance paper), so the system
splits into nodes that certify themselves locally. Physics: stretched colour flux costs energy proportional to its length (string tension
σ, measured in the TTL scan), so the field closes into bound states (glueballs: closed flux loops); "the first opportunity" is the length
where the flux cost reaches one quantum, 1/√σ (the earlier reach reading, README §3.1b), which is the confinement scale L₁ where H2
switches on in the effective-theory split. Light (no self-charge) has no flux cost and no reason to close; the weak carriers acquire
existence (mass) outside confinement; the strong force closes into nodes.

## Pointer: the coupling between the halves (the owner, 2026-11-21)

The owner: the coupling between the existence and the information field is expressed as the fine-structure constant α, "so anywhere
where alpha happens to show up is a good point to poke". Here: the strong coupling α_s = g²/4π is what H1 tracks (its running with
distance), and L₁, the border between H1 and H2, is where α_s reaches order one: where information and existence couple strongly enough to
erect an existence boundary. For light, α ≈ 1/137 is small and decreases at large distances (screening): it never reaches order one, so
light never erects an existence boundary; α_s grows with distance (asymptotic freedom), reaches order one at L₁, and nodes form. Places to
poke later: the value of α_s (or the Schroedinger-functional coupling) at L₁ ≈ 3/√σ (attempt C of round 2 computes it), and any appearance
of α in the GUID series' existence rules.

## Which existence: the root at infinite depth (the owner, 2026-11-21, after round 3, attempt 5)

The owner: "Doesn't DMP have a theorem that every invalid state is automatically excluded? If DMP requires finite and the root were to
move infinitely deep, it would no longer exist / have an existence boundary spanned to it." And: "my existence for free assumed the wrong
'existence' was in question." Reading: DMP does exclude (a recipe that is not well formed is out of spec and refused, `evidence/Dmp/
Complete.lean`, `verdict_outOfSpec_iff`; a pressed root collapses the chain, `Theory.lean`), and every DMP object is finite. The Clay
question asks for exactly the object DMP excludes: the continuum limit is the theory with the root moved infinitely deep (the lattice
spacing to zero). Two notions of existence meet here. **DMP-existence** of a configuration is provable completeness at finite depth;
**analytic existence** (Osterwalder–Schrader, the OpenAI construction) is a limit object. In DMP terms what exists is the family of
finite-depth theories, and what matters physically must hold the same at every depth (Axiom 1: "this holds at every layer"); that is a
gap **uniform in the lattice spacing**, which is what the reduction proves conditionally (round 3, attempt 1: `gap_of_localFactorsW`, the
same rate and constant for every fine enough level and every volume). The two views do not conflict: uniform bounds at every finite depth
give the limit object by compactness (attempt 5, proved in the abstract form), so the DMP-native statement carries the analytic one as a
by-product. The same split is familiar in physics: Yang–Mills as an effective theory with a physical cutoff (the root at finite depth),
the continuum as its idealisation. Attempt 5 made the difference between the two existences exact, and kept what transfers (T38: every
blocked layer has its own Duality, i.e. reflection positivity of each layer).

## Compactness is not collapse; where black holes do enter (the owner's question, 2026-11-21, after round 3, attempt 3)

The owner asked whether W_p's reduced form (compactness) is why energy can collapse into a kugelblitz, so that black-hole models could
supply the compactness and Hawking radiation its entropy. Answer: the word is shared, the thing is not. **Compactness** in attempt 3 is
the mathematical property that nothing escapes to infinity: every link is an element of SU(2), a bounded space (a 3-sphere), so a
sequence of probability laws on it always has a convergent subsequence (Prokhorov). It needs no physics and is already free; no
collapse is involved, and large gauge fields in Yang–Mills are suppressed exponentially, not concentrated. What the noisy blocking step
adds is a **floor**: every coarse configuration keeps a positive weight, as in a heat bath, so nothing is ever completely forbidden; in the
owner's terms, blocking with noise is coarse-graining that radiates detail away without erasing any possibility. **Where entropy and black
holes do enter is the crossover**, not W_p: (1) confinement in the vortex picture ('t Hooft; Mack–Petkova) is entropy beating energy: the
twist free energy F = E − TS falls to zero because the entropy of placing a centre vortex pays for its action, and the Dobrushin
condition D′ of attempt 1 is the local form of "entropy wins"; (2) in the holographic (gauge/gravity) picture, deconfinement of a
Yang–Mills-like theory is the formation of a black hole in the dual geometry (the Hawking–Page transition, Witten 1998), and both
confinement and black-hole entropy obey area laws. That duality is a conjecture for SU(2) Yang–Mills in four dimensions, so it can guide
(where to look, what to measure) but cannot prove; a black-hole entropy argument would have to be rebuilt inside the lattice theory to
count.

## The act identity as the core (the owner, 2026-11-21, choosing the direction for round 4)

The owner: "The act identity, maybe combined with our universal quantum and the tick rate, seems like the most promising approach.
Existence asserting itself, which an act is, seems to be the core principle on which everything stands, so it would be the logical
choice." The family is `evidence/Dmp/Reach.lean`: existence times extent is one quantum (x·e = Q·k²), its floor on every grid, the same
at every layer, the existence TTL (x·τ = Q·k², a bounded time to live is a gap) and 3s1t (space reach and time to live certify the same
existence). Candidate physics counterpart, to be checked by the round-4 scout: in a twisted box of side L the energy of one unit of
electric flux times L is dimensionless and runs with the coupling (existence × extent = coupling × quantum, which joins the α pointer to
the act identity); confinement makes it grow like σL²; the crossover in form (b) becomes "it has no plateau"; the TTL side is the transfer
matrix that reflection positivity provides, and 3s1t is the space-time symmetry relating spatial decay to the temporal gap.

## G0, lossy causality, and the existence boundary as an inversion (the owner, 2026-11-21, round 4)

The owner: "At G0, there is all the information and all the existence at once in the perfect duality, as well as the WHKs to give it its
initial settings. That is the only state where the entirety of existence can be faithfully described. From there, once lossy causality
began, existence no longer completely contains itself and its entire information. An existence boundary can be seen as a complete
inversion of what existence means: when transitioning, one goes from existing by definition to simply not existing by definition, while
still existing in itself during the transition." Candidate physics reading, for round 4 to check: G0 is the bare theory at the root, the
only level that holds every scale's information (the full lattice measure); each blocking step is lossy (information never increases
under blocking: round 3, attempt 5's data-processing reading of "a sublayer only tightens"), so no coarse layer contains the whole. The
existence boundary as an inversion matches 't Hooft's electric–magnetic duality (round 3, attempt 2: an order-reversing involution between
the twist and the electric-flux free energies): in the confined phase a centre vortex exists freely (twist free energy → 0) while a lone
electric flux does not (its energy grows like σL), and across a transition the roles swap. "Still existing in itself during the
transition" is the crossing point, where the flux costs about one quantum: the act number z = E_e·L crossing 1 (3s1t: box size equals time
to live), which sits near the deconfinement length 1/T_c.

What is conserved (the owner, same evening): "What is conserved, in my view, seems to be the act, so the assertion of existence, or at
least the existence that the assertion can be made on." Candidate reading: under an exact gauge-covariant, centre-respecting blocking the
**flux sector** is conserved (the centre flux is topological: local blocking can neither create nor destroy it; the twist survives exact
blocking, round 3, attempt 2), and with it the **act number**: z(2L) of the fine theory equals z(L) of the blocked theory (round 4,
attempt 2 is proving this exact per-layer transport). So the act, and the existence it is asserted on, passes unchanged through every
lossy step; what is lost from layer to layer is the description (the effective action), not the act. What is not conserved, and carries
the open problem, is how the blocked action compares with the original on the same box (the running).

Why it is conserved (the owner): "It is conserved by the simple fact that it IS running. If it runs, it has to belong to the same
definition of existence, which satisfies its tie to G0." Reading: this is the Callan–Symanzik equation in words. Along one
renormalisation trajectory the coupling g(μ) changes with the scale μ in exactly the way that keeps one scale Λ fixed
((μ∂/∂μ + β(g)∂/∂g)Λ = 0): the running is the conservation, not an exception to it; every point of the trajectory describes the one
theory fixed at the root. The tie to G0 then has a sharp test: follow the running back towards the root (infinite depth, the cutoff
removed). For Yang–Mills the coupling goes smoothly to zero there (asymptotic freedom, Gross, Wilczek, Politzer 1973): the trajectory
reaches G0, the tie holds. For φ⁴ in four dimensions and, as far as is known, for QED, the coupling blows up before the root is reached
(Landau pole): the trajectory cannot be traced back to G0, and the continuum theory is trivial (proved for φ⁴₄ by Aizenman and
Duminil-Copin 2021). So "it runs and stays tied to G0" is asymptotic freedom, the very feature that separates Yang–Mills from φ⁴ in the
triviality test. What it does not settle by itself: that the same trajectory continues, without stalling, from weak coupling through
α_s of order one (the crossover); the identity holds along whatever trajectory exists.

Tie to G0 is reach (the owner: "Isn't tie to G0 simply reach?"). Reading: yes, with two directions. **Inward reach** is how far the running
can be traced back towards the root; **outward reach** is Axiom 1's R, how far an act can extend (the floor Q/R, `Reach.lean`). One sign
trades them: the sign of the running (b₀). Yang–Mills (b₀ > 0, asymptotic freedom): unlimited inward reach (the coupling vanishes at the
root) and, if the gap holds, limited outward reach (confinement, R of order 1/√σ). QED and φ⁴ (the opposite sign): limited inward reach
(the Landau pole) and unlimited outward reach (the photon's long range; free massless behaviour). In these terms the mass gap problem
reads: unlimited inward reach forces limited outward reach. A sharp warning, and a new unit test: that implication is false in general.
Gauge theories with enough massless matter (QCD with roughly 9 to 16 flavours, the conformal window; Banks and Zaks 1982) are
asymptotically free yet flow to an infrared fixed point: unlimited reach in both directions, no gap. So unlimited inward reach alone does
not force a floor; what pure Yang–Mills must add is that its running does not stall at an infrared fixed point (round 3's "no fixed
point", here as the condition that turns inward reach into outward limit). **Banks–Zaks test:** any argument for the gap that would
also apply to an asymptotically free theory in the conformal window is wrong.

Something must run (the owner): "DMP demands that something inside of it DOES exist, so something must be able to run and thus not stall."
Reading: an infrared fixed point is long-distance scale invariance, and a scale-invariant theory has no act with a floor: if existence
times extent is one quantum at every scale, nothing fixes an existence, so nothing exists in DMP's sense (it behaves like payload). So
DMP's demand is exactly the missing condition of the reach reading: **a DMP-hostable theory has no infrared fixed point**, and the
conformal-window theories (Banks–Zaks) are excluded by it, which is the difference the Banks–Zaks test asks for. Claim level: on the DMP
side this is an axiom (DMP requires existence); for the proof it is a selection principle, not yet a derivation, because showing that
pure Yang–Mills is hostable with a non-trivial act is the same as showing its running does not stall. What it gives is the cleanest target
so far: **exclude an infrared fixed point for pure SU(2)** (in physics: the trace anomaly, proportional to β(g)·F², cannot vanish at long
distances), weaker and more natural than round 3's worst-case condition D′, and exactly what the conformal window violates. Known:
perturbatively pure Yang–Mills has no such zero (its first two running coefficients have the same sign); non-perturbatively it is open,
and lattice data show none.

The centre reached through the chain of causality (the owner, on round 4, attempt 3's finding that the separating property is "−1 is a
commutator"): "This, at least in DMP, is done through the chain of causality, so the in/out reach." Reading: a commutator is literally a
causal round trip, a b a⁻¹ b⁻¹: out along a, out along b, back along a, back along b. Outward reach then inward reach. In an abelian group
the round trip always closes on the identity: going out and coming back changes nothing, the root is never reached. In SU(2) the round trip
can end on −1, the other half of the root (the root swap): the twist eater is a closed causal loop, out and back, whose net result is the
centre. The order-12 binary dihedral group is non-abelian, yet no round trip in it ends on −1: self-charge alone is not enough, the
causal loop must reach the root. So the separating property, read in DMP terms, is that the in/out reach of the self-charge spans to the
root.

Internally verifiable messages, bounded locality (the owner, 2026-11-22): "In my original DMP proposal, IM was always meant to be
internally verifiable in DMP, so that only correct messages could be sent. Transferring it to YM, the reach spans to the root since it is
defined by it. In physics this is done through confinement or mass, which both give a bounded locality to existence." Reading: the
physics form of "only correct messages can be sent" is **Gauss's law**: a physical state must satisfy the gauge constraint at every point,
a local check any part can make; on the twisted box the states that pass split into the electric-flux sectors by how they respond to
gauge transformations twisted by the centre (the root), so the sectors are defined by the root, as the owner says. The difference between
light and gluons is in what the check covers: QED's law ∇·E = ρ does not count the photon (it carries no charge: payload, unverified,
unbounded locality), while Yang–Mills' law D·E = ρ includes the gluons' own colour (the field is checked by its own law: self-charge). That
self-verification is the candidate reason for bounded locality; confinement (a flux costs σ per length) and mass (range 1/m) are the two
physical forms it can take. Claim level: this is the DMP-side reason and a precise physics dictionary; that Yang–Mills' self-verifying
Gauss law forces bounded locality is the open problem itself.

## Guiding principle for the proof phase (the owner, 2026-11-22)

"In the past it was highly beneficial to generalize and try to fit everything that seems to belong together into one neat DMP-complete
picture; this approach has worked surprisingly well, so be ambitious, sniff out what seems related, and then see what clicks." Recorded
in `attempts/RULES.md` as the phase's guiding principle, next to the claim discipline that keeps the clicks honest.
