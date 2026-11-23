# The integer-flux route to a rate (2026-11-23)

Task (owner's "Go with it!", via the coordinator): PREP's last three entries ("The cost lower bound comes from the inevitability
of the balanced state" and the corollary "at least something has to exist / be provable"). A uniform minimum plaquette cost does
not exist (it vanishes at the SO(3) cut, `DICHOTOMY.md` 8.2), but the centre flux is integer and conserved. Build the rate from
**(integer part) x (average cost per sheet)** instead of (number of plaquettes) x (minimum cost):
1. a flux-carrying outside forces a sheet, with a minimal area set by the box geometry;
2. the average cost per sheet plaquette: uniformly bounded below? annealed or quenched, which does the one-box condition need?
   does the strict flip bound plus the measured conditional mass give it?
3. does the integer part give the hand-over between rarity (isolated near-cut set) and disorder (percolating) a rate?

Claim marks: **Lean** (built, standard axioms), **paper** (argued here, not formalised), **sketch**, **citation** (recalled, not
re-checked here), **numerical**, **open**. No GPU; CPU numbers from the saved `16⁴` W2 equilibrium configurations.

Lean: `formal/ProofPhase/Crossover/FluxRate.lean` (8 theorems) and `Crossover/HandOver.lean` (3 theorems); built in `~/formal-dy`
(`build-dy.sh`), axioms in `axioms-dy.log` (all 22 Crossover theorems: `propext`, `Classical.choice`, `Quot.sound` only).

## 0. Verdict in plain words

* **Step 1 closes (Lean).** A flux-carrying outside forces sheet plaquettes in the box, for free: the flux cells are even in
  number, so at least two; each plaquette lies in `c = 2(d − 2) = 4` cubes, so the forced sheet has at least `ℓ/4` plaquettes in
  the box (`ℓ` = number of flux cells), at least one; and it crosses the box boundary at every flux cell.
* **Step 2 answers itself the wrong way round.** The average cost per sheet plaquette *is* bounded below, annealed (numbers) and
  even quenched, uniformly in the outside for a fixed finite box (compactness, paper). But (integer part) x (average cost) bounds
  the sheet's *expected energy*, and by Jensen `E[e^{−C}] ≥ e^{−E[C]}`: an average cost gives a **lower** bound on the weight of a
  forced sheet, never the upper bound a rate needs. The quantity that does give a rate is the sheet's **free energy**,
  `−log E[e^{−C}] ≤ E[C]`, and for a sheet forced through a periodic box that is the twist free energy `F_tw = −log(Z_tw/Z)`. The
  one-box condition needs this in its **annealed** half (the weight of bad patterns is a probability under the full measure),
  where the essential-infimum obstruction does not bite. The strict flip bound gives `F_tw > 0` at every box size (sign); the
  conditional mass (about 4 per block) is a disorder-side quantity and does not bound `F_tw`.
* **Step 3 closes at the level of one box (Lean), and this is the "something that has to exist".** 't Hooft's duality
  `F_e = −log tanh(F_tw/2)` is a decreasing involution with fixed point `log(1 + √2) ≈ 0.881`. With the strict bound
  `0 < Z_tw < Z` it gives, **at every box size, `max(F_tw, F_e) ≥ log(1 + √2)`** (`su2_handover`). Rarity's rate is `F_tw` (the
  forced sheet's free energy), disorder's rate is `F_e` (the per-box decay of a centre-charged signal); they cannot both be small.
  The hand-over has a uniform per-box rate of `0.881` in one channel or the other, sharp at the self-dual point.
* **First step that does not close: the product over boxes.** A rate in distance `D` needs `D/L` box crossings at a fixed box
  size `L` to multiply: on the electric side this is the binary-channel model (`Flip/Floor.lean` section 3, a model, not a theorem
  about the measure); on the twist side it would be a chessboard estimate for the box event "the box boundary carries centre
  flux", whose disseminated weight would have to be bounded by `e^{−F_tw(L)}`, and that identification is open (section 5). Behind
  it: the torus free energies are annealed; the per-outside (quenched) influence bounds of the one-box condition are not touched by
  integrality.

## 1. A flux-carrying outside forces a sheet (Lean, `FluxRate.lean`)

Setting of `Dichotomy.lean`: `τ : P → ℤ/2` the centre layer on plaquettes, cells `q` (cubes) with face sets `inc q`, a box `R ⊆ P`.
**Flux cells** `fluxCells inc τ R`: cells where the restriction of `τ` to `R` has nonzero coboundary; for closed `τ` they are
boundary cells and the flux is a function of the outside (`cob_restrict_eq_cob_restrict_compl`). **Sheet plaquettes in R**
`sheetIn τ R`: plaquettes of `R` with `τ p ≠ 0`.

| statement | Lean name | mark |
|---|---|---|
| a flux cell has a sheet face in `R` | `exists_sheet_of_flux` | Lean |
| closed `τ`: a flux cell has a sheet face in `R` **and** one outside (the sheet crosses `∂R` there) | `exists_sheet_both_sides` | Lean |
| `#(flux cells) ≤ c · #(sheet plaquettes in R)` if each plaquette is a face of at most `c` cells | `card_fluxCells_le` | Lean |
| the number of flux cells is even if each plaquette is a face of an even number of cells | `even_card_fluxCells` | Lean |
| nonempty flux ⟹ at least 2 flux cells ⟹ `2 ≤ c · #(sheet plaquettes in R)` | `two_le_card_fluxCells`, `two_le_mul_card_sheetIn` | Lean |
| `ε · #{p ∈ S : cost p ≥ ε} ≤ Σ_{p ∈ S} cost p` (nonnegative costs) | `cost_ge_threshold_count` | Lean |
| every sheet plaquette in `R` costs `≥ ε ≥ 0` and the flux is nonempty ⟹ `2ε ≤ c · (sheet cost in R)` | `sheet_cost_ge` | Lean |

**Geometry (paper).** On the periodic hypercubic lattice in `d = 4` a plaquette is a face of `2(d − 2) = 4` cubes, so the
hypotheses hold with `c = 4` and even incidence. The forced area is at least `ℓ/4`, `ℓ ≥ 2`, so at least one plaquette. The forced
sheet is **boundary-attached**, never closed: a closed sheet lying inside `R` has zero flux (its coboundary vanishes on every
cell), so integrality forces nothing about closed sheets. If the flux cells on `∂R` separate two boundary faces at distance `D`
(a closed flux curve of diameter at least `D`), then `ℓ ≥ 2D` and the forced area is at least `D/2` (paper, lattice curve length).
Only this linear bound is claimed; the isoperimetric `~ D²` for a flat flux loop is not needed below and not proved.

**What step 1 gives and does not give.** The integer part is exact and free; its size is linear in the flux length. It turns
"number of plaquettes x minimum cost" into "number of *forced* plaquettes x cost of *those* plaquettes", but the cost of those
plaquettes is still whatever the configuration makes it: `sheet_cost_ge` needs `ε` on the sheet plaquettes actually present, and
`WellDefined.lean` shows no positive `ε` holds on a full-measure set.

## 2. Average cost per sheet plaquette: annealed, quenched, and why neither is the rate

### 2.1 The average is bounded below (annealed: numerical; quenched: paper)

* **Annealed (numerical, `w2/pastcut.py`, `w2/runs/pastcut.json`).** In the sign representation (sheet plaquette = past the cut,
  `q₀ = ½ tr U_p < 0`; M1's split layer is not simulated, so this is a proxy), the per-plaquette weight `w = P(sheet)/P(no sheet)`
  on the blocked variables of `COARSE-TEST.md` (same blocking and offsets; 4 configurations per β):

  | β | factor | past-cut share | largest past-cut cluster share | spanning | `w` | `6w` | `54w` |
  |---|---|---|---|---|---|---|---|
  | 2.3 | 1 | 0.051 | 0.0003 | 0 | 0.054 | 0.32 | 2.9 |
  | 2.3 | 2 | 0.106 | 0.084 | 1 | 0.119 | 0.71 | 6.4 |
  | 2.3 | 4 | 0.286 | 0.286 | 1 | 0.401 | 2.4 | 22 |
  | 3.5 | 1 | 0.0031 | 0.00001 | 0 | 0.0031 | 0.019 | 0.17 |
  | 3.5 | 2 | 0.0004 | 0.00005 | 0 | 0.00043 | 0.0026 | 0.023 |
  | 3.5 | 4 | 0.0003 | 0.0003 | 0 | 0.00035 | 0.0021 | 0.019 |

  `6 = 2(d − 1)` is the lower bound for the surface entropy constant `K'` used in `window_gap`, `54` the crude plaquette-animal value
  of `DICHOTOMY.md` 8.3. If sheet plaquettes were independent, `K'w < 1` would be the annealed Peierls condition for forced sheets
  (correlations are ignored here, so this is a **sketch**). At β = 3.5 it holds at every factor even with `K' = 54`. At β = 2.3 it
  fails with `K' = 54` already at the fine scale and fails with `K' = 6` at factor 4; the past-cut set itself spans from factor 2
  on (cube adjacency, a proxy for surface percolation). The near-cut set (`|q₀| < δ_P`) of `COARSE-TEST.md` spans at β = 2.3 at
  every factor; the past-cut set is a thinner set and is isolated at the fine scale.
* **Quenched in the outside, for a fixed finite box (paper).** The Wilson action is local, so the conditional law of the box links
  given the outside depends only on the finitely many links of the collar, a compact set; its density with respect to Haar measure
  is positive and jointly continuous in the box links and the collar links. Hence `σ ↦ E[2β|q₀(p)| ; q₀(p) < 0 | σ]` and
  `σ ↦ P(q₀(p) < 0 | σ)` are continuous and positive on a compact set, and the conditional average cost per sheet plaquette at `p`
  has a positive minimum over all outsides. **The average is uniformly bounded below; the obstruction of `DICHOTOMY.md` 8.2 is a
  statement about the minimum over configurations, which integration over the box removes.** The bound is non-constructive and
  depends on the box size, the position and β; it is not a rate.

### 2.2 Why (integer part) x (average cost) is not a rate (paper: Jensen)

A rate is an upper bound on the weight of a forced sheet, `E[e^{−C}]` with `C` its cost. Jensen (convexity of `exp`):
`E[e^{−C}] ≥ e^{−E[C]}`. So `(forced area) x (average cost per plaquette) = E[C]` gives `weight ≥ e^{−E[C]}`, the wrong direction.
The upper bound needs the **free energy** `F = −log E[e^{−C}]`, which satisfies `F ≤ E[C]` and can be much smaller when the cost
has a heavy lower tail, which is exactly the near-cut situation: rare near-cut plaquettes dominate `E[e^{−C}]` while hardly moving
`E[C]`. "Average cost" in PREP's corollary has to be read as **free energy per forced plaquette**; with that reading the route is
right, and the object it produces for a sheet forced through a periodic box is `F_tw = −log(Z_tw/Z)`, the energy and the entropy of
all ways the sheet can run included.

### 2.3 Annealed or quenched: which the one-box condition needs (paper)

The pattern-conditioned assembly (`FineOneBoxPat`, `Adjoint2/PatternAssembly.lean`) has two halves:
* the **weight of bad patterns** `≤ c e^{−mD}`: a probability under the full measure, i.e. **annealed**. This is where the integer
  flux enters: a pattern in which flux is carried across distance `D` forces a sheet of area at least `D/2` (section 1), and its
  weight is bounded by the free energy of forced sheets. The essential-infimum obstruction concerns pointwise bounds and does not
  apply to an annealed weight;
* the **per-pattern influence bounds**: required on a set of full measure, i.e. **quenched** in the outside. Integrality says that a
  flux-carrying outside forces a sheet, but not that the inside law is insensitive to where the outside puts its flux; it does not
  help this half.

So the integer-flux route is a route to the annealed half, with the free energy of forced sheets as its rate.

### 2.4 The strict flip bound and the conditional mass (paper)

* **Strict flip** (`Flip/Strict.lean`, `su2_Ztw_lt_Z`): `Z_tw < Z` for every `β ≠ 0`, every `L`, every even `T`, so `F_tw(L) > 0`
  at every box size. A sign, with no uniformity in `L`.
* **Conditional mass about 4 per block** (`c9b-adjoint/ROUTE3.md` 7): the decay of the inside's response at typical block fields,
  a disorder-side quantity (it bounds how fast a disturbance dies inside a block, not how much a forced sheet costs). It does not
  bound `F_tw`, and it is measured only at typical fields (Lemma C needs the supremum).
* **Together** they do not give an `L`-uniform lower bound on `F_tw`. They are not expected to: in the confined phase `F_tw(L) → 0`
  as `L` grows (vortex condensation; 't Hooft's criterion, which `Floor.lean` encodes as `flipSat_iff`; citation: Tomboulis and
  Yaffe's inequality relating the twist free energy to Wilson loops, and lattice measurements of the SU(2) vortex free energy
  decaying with `L`, both recalled, not re-checked here). An `L`-uniform lower bound on `F_tw` would contradict confinement. The
  annealed table of 2.1 shows the same tendency at β = 2.3 (`w` grows with the block factor) and the opposite at β = 3.5.

## 3. The quenched minimum: a first-passage reading (sketch)

Given the outside, the cheapest forced sheet has energy `min_S Σ_{p ∈ S} 2β|q₀(p)|` over the surfaces `S` in `R` spanning the flux.
By `cost_ge_threshold_count` this is at least `ε` times the least number of plaquettes with `|q₀| ≥ ε/(2β)` that any spanning
surface must use: a **surface first-passage time** through the near-cut set. It grows linearly in `D` if and only if the near-cut
set contains no surfaces spanning the box (surface percolation of the near-cut set fails): the β = 3.5 situation (isolated, at every
blocking factor), not the β = 2.3 one (spanning at every factor; cube-adjacency spanning is a proxy for surface percolation). This
is the rarity mechanism restated, with the integer part supplying "some surface must span"; it adds no rate where the near-cut set
percolates, and it is the energy, not the free energy (entropy of the surfaces not counted).

## 4. The hand-over has a uniform per-box rate (Lean, `HandOver.lean`)

| statement | Lean name | mark |
|---|---|---|
| `0 < Z_tw < Z` ⟹ `Z_tw/Z ≤ √2 − 1` or `(Z − Z_tw)/(Z + Z_tw) < √2 − 1` | `handover_ratio` | Lean |
| `0 < Z_tw < Z` ⟹ `log(1 + √2) ≤ max(F_tw, F_e)` | `log_one_add_sqrt_two_le_max` | Lean |
| SU(2) Wilson, every `β ≠ 0`, `L`, even `T`, background twist, plane: `log(1 + √2) ≤ max(F_tw, F_e)`, given `0 < Z_tw` | `su2_handover` | Lean (hypothesis `0 < Z_tw`: true, positive integrand; `ProofPhase.Flip` proves only `0 ≤ Z_tw`) |

Here `F_tw = twistF Z Z_tw = −log(Z_tw/Z)` and `F_e = elecF Z Z_tw = −log((Z − Z_tw)/(Z + Z_tw))` (`Flip/Floor.lean` 1). The bound
is sharp: at `Z_tw/Z = √2 − 1` both equal `log(1 + √2) ≈ 0.881`.

**Reading (paper).** The two mechanisms of the dichotomy are the two channels of 't Hooft's duality:
* **rarity**: a flux-carrying configuration through a box must carry a forced sheet (section 1), and the weight of that, all
  sheets summed, is `e^{−F_tw}`. Large `F_tw`: flux through a box is rare;
* **disorder**: a centre-charged `±1` signal crossing a box keeps the factor `Z_{e=1}/Z_{e=0} = e^{−F_e}` (`Floor.lean` 1,
  `one_sub_two_flipP_exp`). Large `F_e`: the box scrambles the signal (vortex condensation, `F_tw → 0`, gives `F_e → ∞`).

`su2_handover`: **at no box size are both channels weak.** Whatever happens to `F_tw` with scale, at every `L` one of the two
channels removes at least `0.881` per box crossing. This is the owner's corollary in exact form: something (one of two dual
suppressions, each at least `log(1 + √2)`) has to exist at every scale, and it is provable from the integer, conserved flux
(through `Z_tw`, a sum over forced sheets) and reflection positivity (through `Z_tw < Z`). It is a per-box statement.

**How it would become a rate (sketch).** Fix one box size `L`; tile a distance `D` by `D/L` boxes of that size. If the channel that
is strong at `L` multiplies over the boxes, the influence across `D` is at most `e^{−0.881 D/L}`: exponential, with mass at least
`0.881/L`. Tiling at a fixed size avoids `Floor.lean`'s `not_exponential` (that theorem concerns nested dyadic boxes, where a floor
gives only a power law).

## 5. The first step that does not close: multiplying over boxes (open)

1. **Twist channel (open).** "The boundary of box `B` carries centre flux" is an event of the links near `B` (in the sign
   representation, local). Reflection positivity is in the project (`Positivity.config_rp`), so a chessboard estimate (citation:
   Froehlich, Israel, Lieb and Simon) would bound the probability of the event in `n` boxes by `z^n`, `z` the disseminated weight
   (the event in every reflected copy of `B`, to the power `1/(number of copies)`). The rate needs `z ≤ e^{−F_tw(L)}`, or any
   `z ≤ e^{−κ}` with `κ` tied to `max(F_tw, F_e)`. The disseminated event, flux through every reflected box, is not the torus twist
   that defines `Z_tw` (one sheet through the whole torus); I do not see the identification, and it is the first step I cannot
   close.
2. **Electric channel (open, known).** The product `∏ e^{−F_e(L)}` over crossings is the binary-channel model of `Floor.lean` 3,
   flagged there as a model, not a theorem about the measure.
3. **Quenched half (open, behind 1-2).** Even with 1 or 2, the result is annealed (torus free energies, full measure). The one-box
   condition's influence half needs per-outside bounds; integrality does not reach it.
4. **Which channel at which `L` (numerical, open).** `F_tw(L)` and `F_e(L)` are not measured here (no GPU; the twisted ensemble is
   not in the W2 data). The past-cut table of 2.1 suggests the twist channel at β = 3.5 and the electric channel at β = 2.3, and a
   change of channel with scale at β = 2.3 between block factors 2 and 4; that is a proxy reading, not a measurement of either free
   energy.

## 6. Status

| step | result | mark |
|---|---|---|
| 1. flux forces a boundary-attached sheet; even flux, at least 2 flux cells; area `≥ ℓ/4`, `≥ D/2` for flux across `D` | closed | Lean (combinatorics), paper (lattice geometry) |
| 2a. average cost per sheet plaquette bounded below, annealed | yes | numerical (proxy) |
| 2b. the same, quenched in the outside, fixed finite box | yes, non-constructive, box-dependent | paper (compactness) |
| 2c. (integer part) x (average) is not a rate; the rate is the free energy per forced plaquette, i.e. `F_tw` | | paper (Jensen) |
| 2d. the one-box condition needs it in the annealed half (bad-pattern weight) | | paper |
| 2e. strict flip + conditional mass give an `L`-uniform `F_tw` bound | no (sign only; mass is disorder-side, typical fields); not expected in the confined phase | Lean (sign), citation |
| 3. quenched minimum = surface first-passage time; linear iff the near-cut set does not surface-percolate | | sketch |
| 4. at every `L`: `max(F_tw, F_e) ≥ log(1 + √2)` (sharp) | closed | Lean (`0 < Z_tw` as hypothesis) |
| 5. multiply over `D/L` boxes (twist: chessboard identification; electric: binary channel) | **first open step** | open |
| 5'. from annealed torus quantities to per-outside influence | open | open |

## 7. Files

* `RATE.md` (this note).
* `formal/ProofPhase/Crossover/FluxRate.lean`, `formal/ProofPhase/Crossover/HandOver.lean` (new); `axioms-dy.sh` extended to them;
  `axioms-dy.log` (22 theorems, standard axioms).
* `w2/pastcut.py` (CPU, 1 min 38 s), `w2/runs/pastcut.json`.
