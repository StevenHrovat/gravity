# Generalisation, phase 1: the generic layer over any gauge group and dimension (2026-11-23)

Phase 1 of `../GENERALISE-PLAN.md`, built on the audit `../GENERALISE-AUDIT.md`. New folder `formal/ProofPhase/General/`
(11 files); **no existing `.lean` file is edited**, nothing in `vendor/dmp` is touched. Every new module builds with no
warning; the axioms of every declaration are in `axioms.log` (`axioms.sh` regenerates it). Count: 62 theorems and 41 definitions, classes, structures and instances in the
source (145 constants in the environment with the generated projections); all 145 depend only on `propext`,
`Classical.choice` and `Quot.sound` (one, `eq_of_cyc_le_one`, on a subset); 19 `example` checks are part of the build.

## What is built

| Module | Content |
|---|---|
| `Counting` | The counting facts in `d`: at most `3^d` sites within distance 1 (`card_near_le`); a set of links of `l^inf` diameter `<= r` has at most `d (2r+1)^d` elements (`card_le_of_siteDist`); the growth tail `(1+x)^d e^{-2ax} <= (d!/a^d) e^a e^{-ax}` (`poly_exp_le`) and its bounded form `poly_exp_bound`. |
| `Torus` | Boxes on the torus `(Z/M)^d` for any link alphabet `G`: `boxBlock`, `boxReach`, `isBoxFamily_torus`, and the block bound `card_boxBlock : card <= d * card Lambda0`. The law route in `d`: `LawGapBddW c rho lam`, `OneBoxLaw rho lam`, `lawGapBddW_of_oneBoxLaw` (constant `2 d n_max e^{lam D0}/(1-gamma)`), for laws on `GaugeConnection G d (M j)` and any cost distance `c` on `G` (the proof never uses the Lipschitz hypothesis). |
| `GaugeGroup` | The gauge-group package (below). |
| `SU2Instance` | SU(2) as an instance of every class of the package. |
| `Combined` | `area_law_of_mixture`: the centre-comparison area law (`Centre/Combined`) for any group `G` with a matrix representation, with the bound `B` on `Re tr` and the weight bound `M` as parameters. |
| `Noisy` | The family layer of `Repair/Noisy` and `Repair/MulNoise` for any `G`, `d`: `NoisyBlockingFamily`, its noise, joint and blocked laws, `noisyFamily_rp` (reflection positivity of every layer), `KernelDensity`, `noisy_blockedLaw_gibbs`, `mulNoiseFamily`, `mulNoise_rp`. |
| `Filter` | The Yang-Mills layer of `Seg2/Filter` for any `G`, `d`: `PhysExtent`, `BlockingFamily`, `blockSigma`, `SepPred`, `CondDecouple`, `SmootherStable`, `AnnealedContraction` and the three reductions. |
| `Local` | `siteDist_le_floor` and `card_le_of_physExtent` in `d`: a set of physical extent `<= R` has at most `d (2 floor(R/a_k) + 1)^d` links. |
| `PerVolume` | `Quantum/PerVolume` for any `G`, `d`: `NoisyBlocking`, its laws, `LimitDprimeAll`, `perVolumeGap`, `perVolumeGap_eventually`, `exists_blockLimit`, `blockLimit_gap`. |
| `Instances` | The `d = 4` counting and one-box statements re-derived (below). |
| `Top` | Imports all of the above. |

## The gauge-group package (`GaugeGroup`, `SU2Instance`)

The repository already had the *data* classes (`Group G`, `HasGaugeTrace G n` = matrix representation of dimension `n`,
`HasHaarProbability G`). What the generic files repeated in every binder list were the *facts*; they are now two `Prop`
classes, with the instances they imply:

* `GaugeGroupBase G`: `IsTopologicalGroup`, `SecondCountableTopology`, `BorelSpace`, `CompactSpace`, and left and
  inversion invariance of `haarG G`. The instances come from the class (priority 100).
* `GaugeRep G n`: the representation is continuous and unitary. Consequences, proved generically: the bounded class
  function of the Wilson action `|Re tr g| <= n` (`abs_gaugeReTr_le`), `Re tr 1 = n`, `Re tr` is a class function
  (`gaugeReTr_conj`), and the Wilson measure of any `G`, `d`, torus side and coupling is a probability measure
  (`isProbabilityMeasure_wilsonMeasure`, the generic `ym_prob`).
* A generic theorem takes `[Group G] [TopologicalSpace G] [MeasurableSpace G] [HasHaarProbability G]
  [HasGaugeTrace G n] [GaugeGroupBase G] [GaugeRep G n]` and `[NeZero d]`.
* `GaugeSubst G n` (the **`subst` layer**, declared, not proved for general `G`): a cost distance `geodDist` (replacing
  `geodSU2`, non-negative, takes a positive value), the centre as a set of central elements acting as scalars, and a
  projection of `n x n` matrices onto `G` that is a left inverse of the representation. These are fields an instance must
  prove; there is no `axiom`. `SU2Instance` proves all of them for SU(2) from facts already in the repository
  (`geodSU2`, `{1, -1}`, `projSU2`).
* Not in the package (phase 3): the 2x2 identities (adjugate, Mandelstam), the characters and trace bounds beyond
  `Re tr`, the strict flip bound.

## The old SU(2), `d = 4` statements, re-derived as instances (20)

Each old theorem is re-proved in one line from the generic one, and **the two types are checked identical** by
`example : @old = @new := rfl` (it typechecks exactly when the statements are definitionally the same proposition; the
examples are in the instance files and are part of the build).

| Old statement | From |
|---|---|
| `OneBox2.card_near_le` (`<= 81`) | `card_near_le` at `d = 4` (`3^4 = 81`) |
| `Torus.card_le_of_siteDist` (`4 (2r+1)^4`) | `card_le_of_siteDist` at `d = 4` |
| `RouteA.poly_exp_le` (constant `24`) | `poly_exp_le` at `d = 4` (`4! = 24`, `factorial_four`) |
| `Quantum.poly4_exp_bound` | `poly_exp_bound` at `d = 4` |
| `OneBox.card_boxBlock` (`<= 4 * card`) | `card_boxBlock` at `d = 4` (`boxBlock_four`: the blocks agree) |
| `OneBox.lawGapBddW_of_oneBoxLaw` | `lawGapBddW_of_oneBoxLaw` at `SU2`, `d = 4`, `c = geodSU2` (`oneBoxLaw_iff`, `lawGapBddW_iff`) |
| `Centre.su2_area_law_of_mixture` | `area_law_of_mixture` at `SU2`, `n = 2`, `B = M = 2` |
| `Repair.noisyFamily_rp` | `noisyFamily_rp` (the old family converts field by field, `NoisyBlockingFamily.ofOld`) |
| `Repair.noisy_blockedLaw_gibbs` | `noisy_blockedLaw_gibbs` |
| `Repair.goodNoisy_rp` | `mulNoise_rp`; also `goodNoisyFamily_eq : ofOld (goodNoisyFamily ..) = mulNoiseFamily (goodBlocking ..) tau` by `rfl` |
| `Seg2.condDecouple_of_smootherStable` | generic reduction (`condDecouple_iff`, `smootherStable_iff`, `annealedContraction_iff` are `Iff.rfl`) |
| `Seg2.smootherStable_of_annealedContraction` | generic reduction |
| `Seg2.condDecouple_of_annealedContraction` | generic reduction |
| `Torus.siteDist_le_floor` | `siteDist_le_floor` at `d = 4` |
| `Torus.card_le_of_physExtent` | `card_le_of_physExtent` at `d = 4` |
| `Quantum.NoisyBlocking.perVolumeGap` | generic `perVolumeGap` (`NoisyBlocking.ofOld`; `limitDprimeAll_iff` is `Iff.rfl`) |
| `Quantum.NoisyBlocking.perVolumeGap_eventually` | generic |
| `Quantum.NoisyBlocking.exists_blockLimit` | generic |
| `Quantum.NoisyBlocking.blockLimit_gap` | generic |

## Findings

* **The cores were already generic, as the audit said.** Of the five files it named, only a thin layer named SU(2) and
  `d = 4`: the family structures over a `Tuning` (which is itself group-free), the Wilson law `T.ym`, and the statements.
  The new layer replaces `T.ym k j` by `wilsonMeasure G n (T.beta k) d (T.side k j)` (`ymLaw`, `vmLaw`) and keeps the proofs.
* **Phase 2 has a head start.** `AreaLaw/Concrete.lean` already has `Un n` (the unitary group `U(n)`) with compactness,
  second countability, `HasGaugeTrace (Un n) n`, Haar probability, left invariance and the area law `wilson_area_law_Un`
  (through the abstract centre element `negOneUn n`, which is the centre of order 2 inside `U(n)`).
* The `d = 4` in `Combined` is the physical `4 d` of the strong-coupling bound, which was already generic in `d`.
* Stale comment (audit): `RouteB/Chain.lean:23` still cites a non-existent `su2Weight`; not touched (no edits to existing files).

## What is left

**Not ported in phase 1** (the `inst` files whose generic core is thinner, or whose statement chain is long):
`OneBox/Fine`, `OneBox2/Cube`, `OneBox2/Anchor` (the numerical anchor `kapAnchor`), `Torus/Local` (the transfer
statements, only the counting is ported), `V3/CondMass`, `V3/TimeSep`, `V3/W1Route`, `V4/Gap`, `V4/Recursion`,
`H1/Level`, `Interface/*`, `Quantum/BlockedRoute`, `RouteA/BlockedSlab`, `Assembly`, and the families of `Saturation`,
`Existence`, `Defects`, `OS/GapLoc`, `UV/Split`. The counting pieces they need are now available in `d`
(`card_le_of_physExtent`, `poly_exp_le`, `card_boxBlock`); what remains is restating their theorems over a generic
`Tuning`/`BlockingFamily` the way `Filter` and `Noisy` do. For `RouteB/Duality` (`Fin 4` rotation, 4D plane pairing) the
d-dependence is geometric, not a count.

**Phase 2: the SU(N) instance.** `GaugeGroupBase` and `GaugeRep` for `Matrix.specialUnitaryGroup (Fin N) ℂ` (compactness
as `isCompact_SU2` for `SU2`, which is `isCompact_unitaryGroup` plus a closed condition `det = 1`; Haar probability and its
invariances as for `Un`),
and `GaugeSubst`: the geodesic cost, the centre `Z_N` (scalars `ω I` with `ω^N = 1`), the projection onto `SU(N)`. The
projection is the real work: `projSU2` is the explicit `A / sqrt |det A|`; for `SU(N)` it needs a polar decomposition
or another construction, and `proj_rep` is then a one-line check.

**Phase 3: the `subst` facts.** The 20 `subst` files (audit): the 2x2 identities in `Flip/Strict`, `FluxVac/Branches`,
`SectorS/Loops`, `RouteA/Blocking`, `Saturation/Tests`, `Flip/Bound`, `M1/Vortex`, `Certified/AdjointW`; the Z2 centre
layer to a `Z_N` layer (`Adjoint/CentreSplit`, `DMP/VacuumAct`, `Flip/Bound`, `RouteB/FluxEnergy`, `RouteA/CentreBlind`,
`Repair/WeightedW`, `Objects`); characters and trace bounds beyond `Re tr` (`Book/KernelDensity`, `Certified/*`); the
fundamental dimension 2 in `OneBox2/Wilson`; and the five time-slice files that write the spatial dimension 3 (`d - 1`).
The mixture hypothesis of `Combined` (the `U = sigma V` disintegration) is a Z2 statement for SU(2); for `SU(N)` it is a
mod-`N` version, a paper-level input.

## Build

`axioms.sh` builds `ProofPhase.General.Top` in a private WSL folder, recompiles each file to count warnings (0 for all),
prints the axioms of every theorem, definition and instance of the folder and greps the new files for `sorry`, `admit`,
`native_decide` and `axiom` declarations (none). `axioms.log` is its output.
