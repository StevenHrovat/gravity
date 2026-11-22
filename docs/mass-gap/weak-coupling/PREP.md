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

Exclusion must stay possible (the owner, on round 4's "conservation" holding even for a blocking onto a single point): "Blocking onto a
single point needs to be valid, so it's good we caught it. It plays into that exclusion from a DMP-complete system always has to be an
option." Reading: the blocking onto a point is the total refusal, the inert configuration DMP always admits (`evidence/Dmp/Refute.lean`:
under refusing judges nothing is performed and every theorem holds; the empty recipe counts as proven). So a conservation law that holds
for every blocking, the trivial one included, is the DMP-consistent form, and it cannot carry content by itself: that is safety (the
bounds), which T3d ranks first. Content comes from the balance, the one commitment that asks for something to happen ("a system that does
nothing keeps the bounds and fails the balance"). In the proof the balance is the non-degeneracy requirements: a good blocking with a
non-trivial continuum limit (blueprint P1.8), identification of the limit as non-trivial (P6.2), and the assembly's lemma that the
pure-noise theory fails its hypotheses (P7.3). Exclusion is always available; existence has to be shown.
History (checked in the DMP repository): the exclusion is DMP 0.9.8 (2026-10-27, `45d3822`, the G0 mission): "R136a1 is always a
DMP-complete answer over IM and excludes anything from being contained inside a DMP-complete system", the total refusal that the blocking
onto a point mirrors. 0.9.9 made the publication state provisional G0 (`4400cce`): the instance stands until revoked by a DMP-complete
act, existence asserted at the ground. The balance clause itself ("a system that does nothing keeps the bounds and fails the balance") is
older, from the reduction to three axioms (2026-10-26).

## The sector transfer as "how existence is built" (the owner, 2026-11-22, after phase cycle 1)

The owner (dictated): an existence boundary always inverts existence into exactly non-existence, which is not defined, since nothing can be
defined about the content; what can be defined is how existence asserts itself, how it is built. In our systems that is the flux
inversion, and it should give the correct sector transfer. Reading, checked against workstream 2 (`proof-phase/ws2-routeB/NOTE.md`): the
flux inversion alone does not give it. Every twist or flux argument (Kanazawa, Tomboulis–Yaffe, 't Hooft duality) sees only the centre-charged
sector, and the SU(2)×U(1) product theory has growing SU(2) flux energy and still no gap. But the owner's second half names exactly what
that counterexample lacks: the photon is **not built from the SU(2) flux**; it is payload, an existence of its own. So the missing
hypothesis is "every neutral excitation is built from the flux". For a simple gauge group without matter this has a precise form: the
gauge-invariant observables are generated by Wilson loops (Giles 1981), so every glueball-sector state is built from closed flux. That turns
the reading into a sharp target, **Conjecture S (sector transfer for simple groups):** in pure Yang–Mills with a simple gauge group, flux
confinement (an area law, or the act number growing) implies a mass gap, because every neutral excitation is a closed flux loop and pays
the flux cost. It fails exactly where it must: SU(2)×U(1) (an abelian factor: payload not built from the flux), theories with matter
(Banks–Zaks: screened). Status: as far as known open ("confinement implies a gap" is the converse of Chatterjee's direction); to be
checked against the literature before work.

## Swapping G0 by switching dimensions (the owner, 2026-11-22)

The owner: "Existence is inherently linked to G0. Since everything that is has to interact through IM, every force has to belong inherently
to G0. The only way for some node to swap G0 is by keeping the forces, but switching the dimensions, to get a non-existence that can still
be interacted with, for the crossover." Reading: keeping the forces while switching the dimensions is **Euclidean rotation symmetry**: the
Wilson action is unchanged when the roles of a spatial direction and of time are exchanged. Under that exchange an existing state in time
(the electric flux, an energy, a state of the transfer matrix) becomes a twist across a spatial direction (the magnetic flux, a boundary
condition with a free energy: not a state, "a non-existence that can still be interacted with"). This is exactly 't Hooft's duality
proper, now in Lean as `tHooft_rotation` (workstream 2: the lattice rotation maps the temporal twist to the spatial twist on the symmetric
box, T = L). The same exchange turns a box of spatial side L into a system at temperature 1/L, and below L = 1/T_c that system is
deconfined: the crossover sits where switching dimensions turns the existence boundary (confinement) into its absence (deconfinement),
which is the deconfinement length the unit tests already use and where the act number's self-dual point was found (L√σ ≈ 1.4–1.55,
1/T_c ≈ 1.41–1.45/√σ). For the proof, the formal pieces are the lattice rotation (Lean), the symmetric box T = L (where round 4's blocking
step B3 sits), and rotation invariance of the limit (blueprint P6.4); the reading suggests using the dimension swap to move between the
temporal gap (an existence in time) and spatial decay (the slab and block statements of Route A).

## A universal rate per tick, binary existence, a stateless information layer (the owner, 2026-11-22, during phase cycle 5)

The owner, on the one remaining corner (the gap at one scale L_*, uniformly in the volume): "There was a universal decay rate, I think
something with 1/e for the tick rate in the information half. Inside confinement, in DMP, it was a field, spanned logically inside a
volume, where existence is binary, linked to the root through tick rate, so that the information layer can reorganize itself on top of
the existence, while never holding any state, but always optimizing itself. In DMP CMOS never holds any actual data, just information
about data, and is made infinitely flexible by it, while never being visible, or distinguishable between deploys of the same config,
other by the fact that it is working."

Reading (coordinator):
- **A universal rate per tick, 1/e** is the definition of a relaxation time: one tick is the time over which any deviation shrinks by
  the factor 1/e. A rate that is universal (the same for every volume) is exactly the ∃∀ form the corner needs. Its precise form is a
  **volume-uniform spectral gap or log-Sobolev constant** of the local dynamics (heat bath / Langevin) — the v4 draft's strategy (e).
  For spin systems with finite-range interactions, a volume-uniform log-Sobolev constant is known to be equivalent to strong spatial
  mixing (Stroock–Zegarlinski; Martinelli–Olivieri); for lattice gauge theory the analogue is not established.
- **Binary existence inside the volume** fits SU(2)'s **centre Z₂**: the only binary datum a configuration carries is its centre
  (vortex) content; everything else is the adjoint SO(3) = SU(2)/Z₂ part. "The information layer reorganises on top of the existence,
  never holding state" then says: **the adjoint layer is stateless (it mixes at a universal rate), and all binding content sits in the
  binary centre layer.** This matches the measured split exactly: at L√σ = 2.80 the adjoint half of the W₁ column is 0.0036 (holds no
  state) and the centre half 0.673 binds (c3b, c4d). The corner then reduces to the centre layer, coupled to a stateless adjoint layer;
  this is the centre-vortex route (Tomboulis' vortex free energy), which stalled at the two-sided cross-volume step.
- **"Never holds data, only information about data; indistinguishable between deploys of the same config, other than by working"** has
  two precise readings: (i) **gauge redundancy** (gauge degrees of freedom are never observable, and gauge copies are indistinguishable);
  (ii) **uniqueness of the equilibrium state** (every run of the same configuration ends in the same state: no memory, no phase
  coexistence), which is the Dobrushin/mixing statement itself. Reading (ii) is the one that touches the corner.
- For the proof: state the corner as "the centre layer's dynamics has a volume-uniform relaxation rate, given a stateless adjoint layer"
  and test it against the photon (U(1) has no binary centre layer of this kind: the statement must fail or be vacuous there) and against
  deconfinement (where the centre layer orders and the rate must go to zero). Sent to the cycle-5 DMP-native workstream.
- **Correction by the owner (same day): "The 1/e is the universal information tick, the existence tick is still gravitational."** So
  there are two clocks. The **information clock** is universal: per tick every deviation shrinks by 1/e, in every box — the stateless
  adjoint layer. The **existence clock** is not universal: it is "gravitational", which in the earlier reading of this file (coarse Ricci
  curvature, the round-2 section above: "existence as positive curvature; light is flat"; mathematics of GR, not Einstein's equations)
  means its rate is set by curvature. In Ollivier's form, positive coarse Ricci curvature κ of a Markov step is a W₁ contraction by
  1 − κ per step — the W₁ Dobrushin condition itself. Read that way, the measured centre half 0.673 at L√σ = 2.80 is a contraction of
  about 0.67 per block step, a coarse curvature κ ≈ 0.33 of the existence layer at that scale. The corner restated in these terms: **the
  existence layer's curvature stays positive, uniformly in the volume, once the information layer has relaxed**; light is flat (κ = 0),
  so the photon test is passed by construction, and in the deconfined phase the curvature must vanish. The existence clock being
  non-universal is consistent with dimensional transmutation: its tick is set by the generated scale (about 1/√σ), not by the lattice.
- **Confinement in this picture (the owner, same day):** "That also fits well into confinement. In that picture, confinement is a state
  where the existence boundary has contracted so far that existence is forced into a binary state, at which point a boundary is spanned
  and the perturbance isolated." Reading: as the scale grows the coupling grows (the existence boundary contracts), the continuous
  (adjoint) part becomes stateless noise, and only the binary centre datum survives — **centre dominance**. A centre vortex sheet or flux
  tube is the spanned boundary; a colour charge is the perturbance, isolated behind it (only singlets propagate; an isolated perturbance
  with a boundary costs energy growing with its size, hence a gap). In proof terms the endpoint is an effective **Z₂ gauge theory at
  strong coupling** (4D Z₂ lattice gauge theory is confined and gapped for β below 0.4407; deep inside, a convergent expansion proves
  it), plus a stateless adjoint layer. This describes the endpoint we already see: at L√σ = 2.80 the measured fundamental couplings are
  0.054 / 0.171, the adjoint layer is stateless, and the W₁ column is certified below 1 for the fitted action. The corner is the **path**:
  that the blocked SU(2) theory reaches the binary regime without losing its content on the way. Speculative but testable: the scale at
  which existence is "forced binary" should coincide with the deconfinement length 1/T_c ≈ 1.4/√σ, where the act number's self-dual point
  was found (round 4); a check is the effective Z₂ (centre-projected) coupling of the blocked field as a function of L, read off the
  existing refit data, crossing the Z₂ confinement threshold there.

## Crossing an existence boundary: only existence crosses, information is radiated as loss (the owner, 2026-11-22, cycle 5)

The owner (dictated): "In DMP, crossing an existence boundary is something that has already been explored. [...] Information is unable to
cross an existence boundary. When something interacts with an existence boundary, only its existence is transported across it, and the
information is stripped away, and it's radiated away as loss. That's also how it works with switching over the root. At an existence
boundary, only the existence is asserted, and only the assertion of existence is transported across it. That also, as far as I know,
works for quantum mechanics: a massive packet interacts with it, and that existence and its associated assertion of existence is
transported across the boundary, and only that is then used." Earlier readings it continues: the root swap at the confinement boundary
(2026-11-21, above), "what is conserved is the act, the assertion of existence" (round 4), the binary existence layer and the stateless
information layer (cycle 5).

Reading (coordinator):
- **Physics: N-ality.** In SU(2) the only datum of a colour source that survives at long distances is its centre charge (binary: a
  fundamental source has it, an adjoint source does not). Adjoint sources are screened: their flux tube breaks by gluon pair creation and
  the energy leaves as glueballs ("information stripped and radiated as loss"); fundamental sources stay confined. This is established
  lattice physics (Casimir scaling at intermediate distances, N-ality at long distances).
- **Blocking: the conserved part is exactly the binary flux sector.** Under an exact centre-respecting blocking the centre flux through a
  boundary is topological and crosses intact; everything else is lossy (data-processing). So across the boundary between a box and its
  doubled box, the only thing transported faithfully is the binary sector; the rest is the doubling law's loss η.
- **Proof hook (candidate, not established): a binary channel.** If inside and outside of a box were conditionally independent given the
  binary flux data on the boundary, the cross-volume step would reduce to a two-state transfer: correlations contract by |1 − 2p| per
  crossing, with p the probability that the binary datum flips across the crossing (physically: a centre vortex pierces the boundary).
  Then (i) confinement (vortices percolate, p bounded away from 0 and 1) gives a contraction per crossing; (ii) deconfinement (p → 0)
  gives none (long-range order, as it must); (iii) light has no binary layer and its information crosses boundaries freely: no stripping,
  no contraction (photon test passed); (iv) the owner's universal 1/e per tick would read |1 − 2p| = 1/e. The approximation "only the
  binary datum crosses" is not exact; its error is exactly the open content (Lemma X / the stage-two step), so this restates the corner as
  "the stripped information is radiated away, not passed on", and the loss must be summable for the doubling law.
- **Quantum mechanics:** the decoherence picture (a which-outcome record crosses into the environment, phase information is radiated
  away); an analogy, not used in the proof.

**The owner's precise version (written, same day; supersedes the dictated wording above, which "did not fit in the model").** "An
existence boundary swaps the dimensions, thus flipping from existence to non-existence. We had already established that the information
side keeps its compatibility across this swap. Anything that crosses the boundary does need to be something that actually exists (a
duality), anything else (light) asserts its existence at its boundary and has nothing more to do/be. The only thing that is normally
transported across this boundary is its existence (see event horizons). In a still state, it's only its place in space, when i.e.
spinning, more information has to be provided, which is a lossy process (higher efficiency for rotating BHs). When outside reach
interacts with a boundary, the amount of existence it carries over is equal to the information it carries. For the information loss,
Hawking–Penrose information radiation is entropy."

Reading (coordinator; candidate, to be checked):
- **The swap is the dimension swap already in this file** (Euclidean rotation; 't Hooft duality, `tHooft_rotation`): an electric flux (an
  existence in time, an energy) becomes a magnetic twist (a non-existence that can still be interacted with, a free energy). The
  information side stays compatible: the rotation is an exact symmetry of the action, so every correlation maps to a correlation.
- **"The existence carried over equals the information it carries" is the act number read across the swap.** A box of side L becomes,
  after the swap, a system at temperature T = 1/L, so z = E·L = E/T, and the weight of that state is e^{−E/T} = e^{−z}: **the act number
  is information in nats** (the surprisal of the state). Existence (E·L) and information (−ln of the weight) are one number across the
  boundary. The owner's universal information tick "1/e" is then **one nat per tick**: a contraction by 1/e is the act growing by 1.
- **Light "asserts its existence at its boundary and has nothing more to do":** the free photon's vacuum act number is exactly 2π at every
  box size (c5e, `photon_exact`): one full turn, a single assertion, never minted further. That is the frozen act that the Lean doubling
  theorem already excludes (a frozen act needs loss ≥ 1/2 per step). Only something that actually exists as a duality (SU(2): electric
  and magnetic sides both present, a centre) can carry more across.
- **No hair: only existence crosses; still = place, spinning = more information, lossy.** For a black hole only mass, charge and spin
  cross (no-hair). In Yang–Mills the counterpart is that only conserved, topological data cross a blocking boundary: the centre flux
  sector, and the act (energy times extent). A still object carries only its place: the lowest state, 0⁺⁺. Spinning states (2⁺⁺ and up)
  need more information and are heavier: the extra cost is the lossy part.
- **The loss is entropy** (Hawking–Penrose radiation). For the doubling law the per-step loss η is then entropy production per doubling,
  and "summable loss" reads: **the total entropy radiated while the box grows without bound is finite**. That is a concrete, checkable
  form for the open step D-T, and it fails for light correctly (light's act is frozen at 2π, so the whole gain would have to be lost each
  step).
- Open question for the owner (asked, not yet answered): can the asserted existence flip or be lost while crossing (a vortex piercing the
  boundary), or does it always arrive intact? The binary-channel candidate above needs occasional flips.

## The possibility space, binary existence, and the reflected assertion (the owner, 2026-11-22, cycle 5, after the flip question)

The owner (written): "This seems to be the link between the existence half, which describes the dimension of existence and locality,
with the information half, which describes how to exist and, crucially, also WHERE something CAN exist. The possibility space spanned by
the quantum nature of the information half is what gives rise to causality because something might happen, but it does not have to,
establishing proper causality, because it is not a forced act. This possibility space (might (probably is) be inflation) extends into
existence space. If it is fully confined within a boundary, like inside confinement, existence is binary, thus stripping the locality and
prohibiting a true act by information. In our universe, the possibility space does not extend to the dimension boundary, so we can not
assert outward, but inward assertion has to be possible. [...] The assertion at a boundary 'reflects', asserting the boundary from the
inside and the outside, which would put a limit on conversion of 50%-Entropy, roughly."

Context: the coordinator's flip picture (a ±1 existence passed across nested box boundaries; a flip with probability p at each crossing;
the signal after n crossings is (1 − 2p)ⁿ; p = 0 is long-range order (deconfined), 0 < p is exponential fading (the gap); a flip is a
centre vortex piercing the boundary).

Reading (coordinator; candidate):
- **"Might happen, but does not have to" is 0 < p < 1.** p = 0 is a forced act (the existence always arrives: order, no gap); the
  possibility space is exactly what makes the per-crossing contraction |1 − 2p| < 1. Causality in this sense and the gap are one
  condition. Confinement makes existence binary and strips locality: colour has no location of its own, only singlets propagate.
- **The flip probability is a measured quantity: the twist (vortex) free energy.** The chance that the binary flux sector of a box of size
  L is inverted is the weight of the twisted sector, p(L) = Z_tw / (Z_tw + Z_0) = 1 / (1 + e^{F_tw(L)}), with F_tw the 't Hooft twist free
  energy (round 3: r3-monotone's twist free energy, Leg B's twist data). Confined: F_tw → 0, so p → ½; deconfined: F_tw grows, p → 0.
- **"The assertion reflects, giving a 50 % limit":** reflection positivity gives Z_tw ≤ Z_0 (as recalled: Tomboulis–Yaffe 1985), i.e.
  F_tw ≥ 0 and **p ≤ ½**: a crossing can scramble the binary existence at most halfway. The deficit from ½ is set by F_tw, a free energy
  (an entropy-type quantity): "50 % minus entropy". The black-hole counterpart the owner's earlier remark points to: Hawking's area
  theorem bounds the energy radiated when two maximally rotating black holes merge by about 50 % (29 % for non-rotating ones), the
  limit coming from entropy (area) not decreasing.
- **Outward vs inward:** "we cannot assert outward, inward assertion has to be possible" is the earlier inward reach = asymptotic freedom
  (G0), outward reach = confinement, now with the reason: the possibility space ends before the dimension boundary.
- **For the proof:** the corner in this language is "p(L) stays bounded away from 0 as L grows", i.e. the twist free energy stays
  bounded — Tomboulis' vortex criterion, whose small-L → large-L step stalled. What the reading adds is the two-sided structure: the
  reflection bound p ≤ ½ (proved, from reflection positivity) and a lower bound from "inward assertion must be possible" (open).

## Mass gap = the arrow of causality exists (the owner, 2026-11-22, end of phase cycle 5)

The owner: "In our reading mass gap = arrow of causality exists." Reading (coordinator): reflection positivity gives a positive transfer
matrix T = e^{−H} (one step of Euclidean time). The mass gap m says T, restricted to everything orthogonal to the vacuum, is a strict
contraction: after a time 1/m every correlation with the past has shrunk by the factor 1/e. That is a definite rate of forgetting the
past, a built-in clock: **the owner's universal information tick 1/e has length 1/m** (the Compton time of the lightest glueball). Without
a gap (light) correlations still fade, but only as a power law: no intrinsic tick, no definite rate, so no arrow with a clock. In the
flip picture: 0 < p (the possibility space) makes the binary existence forget across each box; the gap is that this forgetting happens at
a fixed rate per tick at every scale.

## Why the floor holds: causality, accumulated acts, the most efficient existence within a boundary (the owner, 2026-11-22, cycle 6)

The owner: "The reason the floor holds is simple causality. Something has existed, so there must be existence. This accumulation of acts
asserts existence by the sheer fact that it exists. [...] By definition anything within a boundary contributes the most efficient
existence possible, so both the confinement is a logical flow, and primordial black holes are a fully valid answer, because that is the
most stable state achievable, which has accumulated other existence to this state over time, simply because it is optimal/gravitational."
(The owner adds this is also their leading dark-matter theory; outside this work, not used here.)

Reading (coordinator; candidate):
- **Two ingredients, both needed.** (1) *Persistence* ("something has existed, so there must be existence"): the act never decreases as
  the box grows, z₀(2L) ≥ z₀(L). (2) *Extensivity* ("anything within a boundary contributes the most efficient existence possible"):
  each part of a box contributes its own full act, so the act of a box is at least the sum of the acts of its parts:
  **z₀(L₁ + L₂) ≥ z₀(L₁) + z₀(L₂) (super-additivity)**. Persistence alone is not enough: the free photon's act is constant (2π), which
  never decreases, yet it has no gap. Extensivity is what excludes light (2π < 2π + 2π) and the frozen 2I act numbers.
- **Super-additivity gives the floor by a classical lemma** (Fekete): z₀(L)/L then converges to its supremum, so E₀(L) = z₀(L)/L stays
  above z₀(L₀)/L₀ > 0 for every larger box along the chain: **the gap**, with m ≥ z₀(L₀)/L₀. In the doubling language this is D-T with
  zero loss. Physically plausible: at small L the act grows with the running coupling (asymptotic freedom), at large L it grows like mL.
- **Where it is open:** proving that the two halves of a doubled box cannot "share" existence to lower the total act is the two-sided
  cross-volume step again. The reading now names the mechanism (no sharing across a spanned boundary: each confined region asserts its
  own existence). A concrete mathematical lead: reflection positivity's chessboard estimates are themselves sub-/super-multiplicativity
  statements for partition functions with insertions in sub-boxes; whether they give super-additivity of z₀ (or which side they give)
  is the next question. Sent to cycle-6 workstreams c6a-flip and c6c-floor.
- **"The most stable state achievable" is a variational statement**: the confined vacuum minimises the free energy (Gibbs variational
  principle); the gap as the stability margin of that minimum.
- **"Not lowering" through DMP (the owner, same day):** "We should be able to prove the not lowering through DMP. To be DMP-complete
  even one box must not lower its existence." Reading (coordinator): the DMP evidence already contains the rule in abstract form:
  `evidence/Dmp/Standing.lean` (T24): **one witness alone never loosens; loosening needs both witnesses** (`one_witness_never_loosens`,
  `loosening_needs_both`), and `evidence/Dmp/Complete.lean`: in a proven configuration **a sub-layer only tightens**
  (`Recipe.proven_sublayer_only_tightens`); `evidence/Dmp/Reach.lean`: Axiom 1's two witnesses = the two halves of a layer, each with full
  reach, gated only by the other, give an existence floor on every grid. The dictionary candidate: **DMP's two witnesses = the two halves
  exchanged by the reflection** (reflection positivity: inside and outside of the reflected boundary). In reflection positivity the
  cross term between the halves is bounded by the halves' own terms (Cauchy–Schwarz, chessboard); "one box cannot lower its existence on
  its own; lowering needs both halves" would then read as a chessboard inequality for the act, which is the super-additivity needed above.
  What is not yet there, and is the content: those DMP theorems are about DMP's own model (whole-number standings), and Reach.lean says
  plainly it proves nothing about Yang–Mills; "proving through DMP" means proving the dictionary — that SU(2) Yang–Mills satisfies the
  premises (Axiom 1's two-witness structure with full reach, i.e. the reflection halves plus a reach bound) — and the reach bound is
  confinement. The dictionary must also use something the finite group 2I lacks (cycle 5: DMP objects so far are group-blind). Sent to
  c6a-flip (Lean: does the chessboard estimate give "one box does not lower the act") and c6c-floor.
- **Correction (coordinator, after c6c-floor, same day):** the translation "super-additivity of the vacuum act z₀" in the section "Why
  the floor holds" above is **false as stated**: in every exactly gapped model checked (2D Ising strips against Onsager's value; a
  massive scalar with Dirichlet walls) the box gap approaches m from **above**, so z₀(L₁+L₂) < z₀(L₁) + z₀(L₂) for all pairs; SU(2)'s box
  gap also blows up in small boxes (Luescher). What survives: (i) the repaired form **z₀(2L) ≥ 2z₀(L) − c** (a fixed loss per doubling,
  bounded by what light can hold, 2π), which from one box gives m ≥ (z₀(L₀) − c)/L₀ — c5e's doubling law with loss, still the open
  cross-volume step; (ii) the **flux act** z_e = E_e·L is super-additive with a large margin in the data (≈ (L√σ)² − 0.9), so the owner's
  "accumulation of existence" fits the flux (the confining string) better than the vacuum. Reflection positivity gives the vacuum side
  only subadditivity. Details: `proof-phase/c6c-floor/NOTE.md`.
- **The fixed loss (the owner, same day):** "The fixed loss sounds like exactly what we need. It is the inefficiency created by the
  assertion of existence by the expansion of possibility space that it required. Also why inside confinement is most efficient."
  Reading (coordinator): in z₀(2L) ≥ 2z₀(L) − c the loss c is the price of asserting existence over the doubled possibility space. Two
  conditions make it a proof: (a) **c does not grow with L** — a candidate mechanism is that what is newly chosen per doubling is a fixed,
  finite set of binary centre-flux sectors (their number does not depend on L), not the bulk; (b) **one start box carries more act than
  the loss**, z₀(L₀) > c; then m ≥ (z₀(L₀) − c)/L₀ > 0. Light: its whole act (2π) is eaten by the loss (c up to 2π), so nothing is left:
  no gap. Confinement: the act grows (≈ m·L) while the loss stays fixed, so the net is positive — "inside confinement is most
  efficient". Both c and z₀(L) are directly measurable: the pre-registered joint z₀/z_e measurement (c5e, `PREREG-JOINT.md`) gives z₀ at
  doubling pairs, hence the per-doubling loss c(L) = 2z₀(L) − z₀(2L), and whether it stays bounded.
- **"More than loss is given by the universal quantum / cost of assertion" (the owner, same day, as a question).** Reading
  (coordinator): with ħ = 1 the photon's act is exactly 2π = h, **one universal quantum**: light asserts its existence once. The quantum
  sets both sides: the act of anything that exists is at least one quantum (the DMP floor, `evidence/Dmp/Reach.lean`), and the loss per
  doubling can reach one quantum (light's whole act). That gives act ≥ loss, i.e. a net ≥ 0, not > 0: light sits exactly at equality,
  which is why it has no gap. "More than loss" needs **strictly more than one quantum** in some start box. The owner's earlier reading
  (only something that actually exists as a duality crosses; the assertion reflects, inside and outside) suggests an existing thing
  asserts twice: act ≥ 2 quanta = 4π, so with loss ≤ 2π the net is ≥ 2π > 0. Checkable: in SU(2) small boxes the lowest centre-even state
  is a flux pair (z₀ ≈ 2z_e; c6b: z_e = 3.59 at L√σ = 2.1, so z₀ ≈ 7.2 > 2π), and at L√σ ≈ 3.5 the glueball gives z₀ ≈ m·L ≈ 13 > 4π. Open:
  that SU(2)'s loss per doubling is bounded by one quantum (known only for the photon), and the 4π floor itself. Both are read off the
  joint z₀/z_e measurement.
- **The smallest box is a true act (the owner, same day):** "One quantum is only light, which, by definition, does not exist, so it, by
  itself, is not DMP-complete. Only a true act, something attached to an arrow of causality, so a duality, can be the smallest box. A
  single assertion of existence by light gives only a point and not an arrow of existence/causality." Reading (coordinator): this fixes
  the start condition of the doubling law with loss (Lean, `su2_gap_of_doubling_defect`, c6a): the loss per doubling is at most what a
  single assertion carries (one quantum, 2π, light's point), and the smallest admissible box must hold a true act — an arrow, two
  assertions — so z₀(L₀) ≥ 2 quanta = 4π > 2π ≥ c, hence m ≥ (z₀(L₀) − c)/L₀ ≥ 2π/L₀ > 0. In SU(2)'s smallest boxes the lowest vacuum state
  is indeed a pair (two flux strings, one each way: an arrow), while light's lowest state is a single photon (a point). It agrees with
  c6a's finding that only vacuum-side (centre-even) statements separate confinement from the gap: the flip probability is centre-odd and
  carries no arrow. Open, as before: that SU(2)'s loss per doubling stays within one quantum; measurable with the joint z₀/z_e run.
- **Existing vs having existence (the owner, same day, more precise):** "Light / not dualistic parts only exist, they do not have
  existence. Existence requires a duality, so that an internal causality can be established." Reading (coordinator): the act number
  measures *having* existence (an internal arrow: a state that propagates in time between two assertions); light only *exists* (a
  point, one assertion). In the doubling law with loss this is the start condition: an admissible start box must contain a duality
  (internal causality), and only such a box carries act beyond the single-assertion loss. The owner approved running the joint z₀/z_e
  measurement with the exact photon formula as control (option A).

## Each node must carry all building blocks of existence (the owner, 2026-11-22, cycle 6/7)

The owner: "The box doubling comes from the inherent duality. For something to keep existing, while splitting, each node has to have all
the basic building blocks for existence. Where something is not a duality, so does not have total internal causality, while possessing
the ability to assert itself against its non-existence, there can be no existence."

Reading (coordinator; candidate): splitting a box must leave each half a complete unit of existence on its own: internal causality (a
gap inside the half) **and** the ability to assert itself against its non-existence, i.e. against **whatever is outside** — every
boundary condition, including the empty/frozen one. In mathematics this is the **worst-case-boundary (Dobrushin–Shlosman /
Martinelli–Olivieri type) finite-volume criterion**: one box of fixed size whose interior is insensitive to its boundary, uniformly over
all boundary conditions, with a margin beating the surface count; for spin systems such a one-box condition is known to give decay in
all volumes (strategy (b) of blueprint v4, "lossless cells"; `CellDobrushin` in `ProofPhase/V3/CondMass.lean` is the right Lean shape;
Chatterjee 2021 uses decay under every boundary condition for gauge theories). Light fails it: inside any box the boundary's influence on
the centre falls only as a power of the size, so at no size does it beat the surface count — light cannot assert itself against its
non-existence. SU(2)×U(1) fails it through its U(1) part. 2I would have to fail it at weak coupling (frozen sectors make the interior
depend on the boundary). Proposed as the next cycle: state and prove the one-box criterion ⇒ `BlockGapBddW` in Lean, and test the
criterion numerically at one box size with extreme boundary conditions.
- **Why one box can be enough (the owner, same day):** "In the end, our entire existence, through G0, can be described by the duality
  and the settings, so anything that describes it only needs, since it can only, at most have, that, with everything building from it."
  Reading (coordinator): the lattice theory at one scale is generated by a finite local rule — the group (the duality) and the coupling
  (the settings) — repeated everywhere; the infinite volume contains nothing beyond copies of that rule. That is why a single finite box
  can certify the whole (the one-box criterion is a statement about the rule, checked where the rule is fully present), and why such a
  certificate can in principle be computer-assisted: it is a finite statement. The owner affirmed the one-box route ("This fits very
  well"); cycle 7 starts on it.
