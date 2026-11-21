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
