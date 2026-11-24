# Y1: a composite Higgs-type field (HTF) on every collar, as the carrier of the per-box certificate (2026-11-23)

Task (owner's last three PREP entries, via the coordinator): the HTF is a **description**, not an added field, so take it as a
composite field built from the gauge configuration, defined on the collars (the DBs) of the box grid. Then:
1. define one or two composite HTF candidates, measurable in the scale filtration and gauge covariant;
2. does conditioning on the HTF on all collars give the collar a uniform conditional mass (condition A for every well-defined
   outside), the "Higgs regime" of complementarity for the pure theory?
3. with the HTF fixed on the collars, is the centre-flux free energy superadditive along a chain of boxes, so that the per-box
   `0.881` of `HandOver.lean` multiplies into decay over distance?
4. where the HTF is ill-defined (degeneracies, Gribov-type ambiguities): null or small? Name the mechanism if it works.

Claim marks: **Lean** (built, standard axioms), **paper**, **sketch**, **citation** (recalled, not re-checked here), **open**.
Lean: `formal/ProofPhase/Crossover/CompositeHTF.lean` (5 theorems), built in `~/formal-dy`; `axioms-dy.log` now lists all 27
Crossover theorems (`propext`, `Classical.choice`, `Quot.sound` only). No GPU, no new numerics: no CPU measurement on the saved
configurations would decide step 2 (section 2 shows why), and step 3 needs the twisted ensemble, which is not in the saved data.

## 0. Verdict in plain words

* **Step 1: yes.** The lowest eigenvector of the collar's covariant Laplacian gives a composite HTF on every collar. It is a
  function of the collar links only, gauge covariant, and defined except on a null set (paper).
* **Step 2 does not close, and the HTF changes nothing.** A gauge-covariant frame carries **no** gauge-invariant information:
  conditioning on it leaves the law of every gauge-invariant observable unchanged (Lean, finite analogue; paper for compact
  groups, same proof). So "the HTF fixed on all collars" either means the frame alone, which conditions on nothing, or the frame
  together with its invariant content, the unitary-gauge links `W = φ̂† U φ̂`. That is the whole collar configuration up to
  gauge. Conditioning on it decouples the boxes exactly (Markov property), but it leaves condition A to be proved over all
  collar configurations: the same open condition as before. The "Higgs regime" of a collar (`W ≈ 1`, small lowest Laplacian
  eigenvalue) is an event of positive weight, not a uniform property. The mass of the Higgs regime comes from the hopping term
  `κ Σ Re tr W` in the action, and a composite HTF has `κ = 0`. Making the field composite removes the step of taking the
  auxiliary coupling to zero, and with it the small parameter (`1/κ`) that the Higgs-region analysis uses. **First step that
  does not close: step 2.**
* **Step 3 closes abstractly, without the HTF (Lean).** With the transfer matrix along the chain, the electric-flux free energy
  is superadditive up to a boundary term: `F_e(a + b) ≥ F_e(a) + F_e(b) − c(a) − c(b)`, and `F_e(kL) ≥ k (F_e(L) − 2C)`. The
  boundary term `c(L) = log(Z₀(L)/λ₀^L)` is the **neutral excess act**, the weight of the neutral excitations over one box
  length. The per-box rate multiplies **iff `F_e(L) > 2c(L)` at one scale**. Three limits: the multiplied channel is the
  centre-charged (electric) one, not the neutral sector of the mass gap; the twist channel of the hand-over does not multiply
  (it decays along long chains); and `c(L)` is small only if the neutral sector is already gapped at scale `L`, and it grows
  with the cross-section (extensive). So the boundary term is where the mass gap sits.
* **Step 4: exact degeneracies are null (paper); near-degeneracies have positive weight.** Near-degeneracies are rarity again,
  but they are irrelevant once step 2 has shown that the frame carries no content. Laplacian gauge has no Gribov copies away
  from the degeneracies (citation).
* **Mechanism.** If a composite HTF worked, the name would be the composite (gauge-invariant) Higgs mechanism of
  complementarity. It does not work as a source of mass: the composite field has no hopping term. What survives is a different
  mechanism, flux transport by the transfer matrix (step 3). It is gapped exactly when the neutral excess act at one box scale is
  below half the electric free energy at that scale.

## 1. Composite HTF candidates (paper)

Collars: for the box grid of side `L_b`, the collar `C_b` of box `b` is the set of links within the interaction range of `∂b`
(the DB of the one-box condition; the cells whose state enters the box law).

**H1, fundamental Laplacian frame.** On the subgraph `C_b`, the covariant Laplacian
`(Δ_U φ)(x) = Σ_{y ~ x} (φ(x) − U_{xy} φ(y))` acts on `φ : sites(C_b) → ℂ²`. For SU(2) the fundamental representation is
pseudoreal, so `Δ_U` commutes with an antiunitary `J`, `J² = −1`, and every eigenvalue is doubly degenerate (Kramers). Read `ℂ²`
as the quaternions `ℍ`: `Δ_U` is a quaternion-Hermitian operator. Let `φ_U` be a unit lowest eigenvector, unique up to right
multiplication by a unit quaternion when the lowest quaternionic eigenvalue is simple. The HTF is the frame
`φ̂_U(x) = φ_U(x)/|φ_U(x)| ∈ SU(2)` where `φ_U(x) ≠ 0`. Its properties:
* *measurable in the scale filtration*: a function of the links of `C_b` only (the eigenvector of a matrix whose entries are the
  collar links, chosen measurably);
* *gauge covariant*: `φ̂_{g·U}(x) = g(x) φ̂_U(x)` (up to the global right factor), because `Δ_{g·U} = g Δ_U g⁻¹`;
* *its gauge-invariant content*: `|φ_U(x)|`, the lowest eigenvalue `λ₀(U) = Σ_{links} |φ_U(x) − U_{xy} φ_U(y)|²` (the composite
  Higgs field's own hopping energy), and the unitary-gauge links `W_{xy} = φ̂(x)† U_{xy} φ̂(y)`. Given `φ̂` and `W` the collar
  links are recovered exactly.

**H2, adjoint Laplacian frame** (for M1's split into the centre layer and the SO(3) field). The same construction with the adjoint
Laplacian on `φ : sites → ℝ³`: the three lowest eigenvectors, orthonormalised site by site, give an SO(3) frame. It is centre
blind, so it describes the SO(3) field `V` and leaves the centre layer `τ` untouched. Real symmetric, so degeneracies have
codimension 2 instead of 5.

**Not taken: maximal centre gauge.** Its projection is a maximiser over a non-convex landscape with many Gribov copies, and no
measurable canonical choice is known that does not reintroduce ties of positive weight. Recorded as a candidate, not developed.

## 2. Conditioning on the HTF (Lean: frame independence; paper: the rest)

**Theorem (Lean, finite analogue).** A group `G` acts on configurations `Ω` with an invariant weight `w`; `F : Ω → X` is
equivariant and `G` acts transitively on `X`; `O : Ω → Y` is invariant. Then the weight of `{F = x, O = y}` does not depend on `x`
(`weight_fiber_eq`), and `#X · weight(F = x, O = y) = weight(O = y)` (`weight_fiber_mul_card`). So the conditional law of every
invariant observable given the frame is its unconditional law.

**For SU(2) (paper).** The gauge group `SU(2)^{sites}` acts on configurations preserving the Wilson measure (Haar invariance), acts
transitively on frames `SU(2)^{sites}` (modulo the global right factor), and `φ̂` is equivariant. The proof above goes through
with sums replaced by integrals and the bijection `ω ↦ g·ω` by the measure-preserving gauge transformation. Hence **conditioning on
the H1 (or H2) frame on every collar leaves the law of every gauge-invariant observable unchanged**: no conditional mass is gained
or lost.

**What "the HTF fixed" can then mean (paper).**
* *The frame alone*: no information (above).
* *The frame and its full invariant content `W` on the collars*: this is the full collar configuration up to gauge. Conditioning on
  it is the Markov conditioning on the collars, under which the boxes are exactly independent (the Wilson measure is a Markov field
  for the plaquette interaction). Condition A for every well-defined outside is then exactly condition A over all collar
  configurations, which is the open condition of `DICHOTOMY.md` 8 and `ROUTE3.md` 7 (measured at typical fields, about 4 per block;
  Lemma C needs the supremum). The HTF did not change it.
* *Partial invariants* (`λ₀`, `|φ|` on the collars): conditioning on a gauge-invariant collar event that neither decouples the boxes
  nor carries a mass mechanism.

**The Higgs regime for the pure theory (paper, citation).** In the gauge-Higgs model the Higgs regime is where `W ≈ 1` on all links,
enforced by the hopping term `κ Σ Re tr W` of the action; the mass comes from `κ` (Osterwalder and Seiler 1978, Fradkin and Shenker
1979: the Higgs and confinement regions are analytically connected for a fundamental Higgs field; citation, recalled). For a
composite HTF the analogue of `κ` is zero: `W ≈ 1` on a collar is the event "small `λ₀`", which has positive weight and no
energetic enforcement. The pure theory sits at `κ = 0` of that phase diagram, the edge where the Higgs-region expansion (large `κ`)
has no small parameter. **So the composite HTF trades the removal step for the absence of the small parameter; it does not give a
uniform conditional mass.** This is the first step that does not close.

## 3. Ill-defined set of the HTF (paper, citation)

* **Exact degeneracy** of the lowest quaternionic eigenvalue of `Δ_U` on a collar: a real-analytic condition on the links. It is not
  identically satisfied (at `U ≡ 1` the lowest eigenvalue is `0` with the constant eigenvector, simple on a connected collar), so its
  zero set is a proper analytic subset, and Haar measure gives it weight zero. Codimension 5 for quaternion-Hermitian matrices
  (von Neumann and Wigner; citation), 2 for H2.
* **A zero of the eigenvector** at a collar site (`φ_U(x) = 0`, where the frame is undefined): again a proper analytic subset
  (`φ ≡ const ≠ 0` at `U ≡ 1`), null; codimension 4.
* **Gribov copies**: the Laplacian gauge is unique up to the global factor away from these degeneracies (Vink and Wiese 1992;
  citation, recalled). So the ill-defined set is **null**.
* **Near-degeneracies** (small spectral gap of `Δ_U`, small `|φ_U(x)|`): positive weight. There the frame's dependence on the links
  has Lipschitz constant of order 1/gap and 1/|φ|. Any statement that used the frame's regularity would have to pay for them, which
  is rarity again (`DICHOTOMY.md` 8.2: exact sets are null, nearby sets are not). Since the frame carries no invariant content
  (section 2), nothing in the one-box condition uses its regularity, so this residue does not enter.

## 4. The carrier: superadditivity of the flux free energy (Lean, abstract)

Chain of boxes along one axis ("time"), fixed spatial torus `L_s³`. Transfer matrix `T ≥ 0` (reflection positivity), commuting
with the centre-sector projections `P₀, P₁`. `Z_e(n) = tr(P_e Tⁿ)`, so `Z = Z₀ + Z₁` and `Z_tw = Z₀ − Z₁` (`Attempts/R4/LayerSector`),
`F_e(n) = log Z₀(n) − log Z₁(n)`, the electric-flux free energy of `Flip/Floor.lean` 1 at time extent `n`. `λ₀` = vacuum eigenvalue.

| statement | Lean name | mark |
|---|---|---|
| nonnegative spectrum: `Σ xᵢ^{a+b} ≤ (Σ xᵢ^a)(Σ xᵢ^b)`, i.e. `Z₁(a + b) ≤ Z₁(a) Z₁(b)` | `sum_pow_add_le` | Lean (finite spectrum; the trace-class case is the same inequality, paper) |
| `F_e(a + b) ≥ F_e(a) + F_e(b) − c(a) − c(b)`, `c(n) = log(Z₀(n)/λ₀ⁿ) ≥ 0` | `flux_superadd` | Lean |
| `c ≤ C` on multiples of `L` ⟹ `F_e(kL) ≥ k (F_e(L) − 2C)`, `k ≥ 1` | `flux_superadd_iter` | Lean |

**What this gives (paper).** The binary-channel product of `RATE.md` 5.2 holds exactly for the torus traces, in transfer-matrix form,
with an explicit boundary term. If at one box length `L`

    F_e(L) > 2 c(L),

then the electric free energy grows linearly along the chain, at rate at least `(F_e(L) − 2c(L))/L` per unit length. The HTF plays no
role (the flux free energy is gauge invariant, and section 2 shows the frame conditions on nothing). Combined with `su2_handover`: at
the box length `L` either `F_tw(L) ≥ 0.881` or `F_e(L) ≥ 0.881`. In the second case the per-box rate multiplies when `c(L) < 0.44`.

**Why this does not close the open step (paper, sketch).**
* **Wrong sector for the gap.** The multiplied quantity is the centre-charged (electric-flux) channel: the energy of a flux
  winding the spatial torus, a confinement quantity. The mass gap concerns the neutral sector. It enters only through the
  boundary term: `c(L) = log(1 + Σ_{neutral excited} e^{−L(E_i − E₀)})` is small iff the neutral spectrum is gapped with
  `L · gap` larger than the log of the number of low excitations. That is the mass gap at scale `L`, the same kind of quantity as
  the gluing deficit of `Floor.lean` 5. The step is circular in the neutral gap.
* **Extensive boundary term.** Independent low excitations in a cross-section of volume `L_s³` contribute about
  `L_s³ e^{−mL}` to `c(L)` (sketch). Keeping `c(L) < 0.44` uniformly in the spatial volume needs `L ≳ 3 log(L_s)/m`, so box
  lengths must grow with the volume. That is not a fixed-scale certificate.
* **The twist channel does not multiply.** `F_tw = dual(F_e)` decreases when `F_e` grows. Along a long chain the strong channel is
  always eventually the electric one, so the rarity half of the hand-over cannot be carried this way.

## 5. Status

| step | result | mark |
|---|---|---|
| 1. composite HTF on every collar (H1 fundamental Laplacian frame; H2 adjoint) | defined; measurable on the collar, gauge covariant | paper |
| 2a. conditioning on the frame leaves every gauge-invariant law unchanged | yes | Lean (finite), paper (compact group) |
| 2b. frame + invariant content = full collar configuration up to gauge; boxes decouple; condition A unchanged | | paper |
| 2c. uniform conditional mass from the HTF ("Higgs regime" of the pure theory) | **no; first open step** (`κ = 0`: no hopping term, no small parameter) | paper, citation |
| 3. flux free energy superadditive up to the neutral excess act; per-box rate multiplies iff `F_e(L) > 2c(L)` | closed abstractly | Lean (abstract), paper (identification) |
| 3'. `c(L)` small uniformly in the volume | open; equivalent in kind to the neutral gap at scale `L`; extensive | sketch |
| 4. exact degeneracies, eigenvector zeros, Gribov copies of the Laplacian frame | null | paper, citation |
| 4'. near-degeneracies | positive weight (rarity), not used once 2a holds | paper |

## 6. DMP reading

The owner: "In the end a HTF is just a DMP-compatible description of existence from provability/empty set theory."

* **Exact sense in which the HTF is a description.** `weight_fiber_mul_card` says the frame is independent of every
  gauge-invariant observable. It can be constructed over the entire boundary (H1 exists on every collar outside a null set), and
  what it adds is a choice of coordinates, carrying no content. This matches the PREP entry on `{∅}`: the minimal construction
  always exists. Existence, in the proof's sense of weight on gauge-invariant events, is entirely in the invariant content `W`,
  which is the configuration itself.
* **So the ODP question moves.** "Can an HTF be constructed over the entire boundary?" has the answer yes, trivially. It cannot
  be the criterion for the gap. The criterion has to be on what the description describes: is the described collar Higgs-like
  (`W ≈ 1`) over the whole boundary? That is an event of positive weight, so rarity again, with no energetic enforcement in the
  pure theory.
* **Where the reading does land.** A conserved quantity carried without loss is the photon entry's carrier. In section 4 it is the
  centre flux, and its free energy adds up box by box exactly, with one remainder: the neutral excess act `c(L)`. The carrier
  loses nothing, and what is left over is the neutral sector. The certificate the chain needs is "the remainder is below half the
  carried rate at one scale" (`F_e(L) > 2c(L)`). That is the place where the gap would have to be shown, and the HTF does not
  reach it.

## 7. Files

* `HTF.md` (this note).
* `formal/ProofPhase/Crossover/CompositeHTF.lean` (new; 5 theorems); `axioms-dy.sh` extended; `axioms-dy.log` (27 theorems,
  standard axioms).
