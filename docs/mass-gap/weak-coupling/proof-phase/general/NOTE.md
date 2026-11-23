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

---

# Phase 2: the SU(N) instance (2026-11-23)

New files (6, all in `formal/ProofPhase/General/`, nothing existing edited): `SUN`, `Centre`, `Projection`, `Meas`,
`SUNSubst`, `TopSUN` (imports phase 1 and these). Axioms of the new declarations: `axioms-sun.log` (`axioms-sun.sh`
regenerates it); every new file builds with 0 warnings. Count: 46 theorems and 19 definitions, abbreviations and instances in the
source, 75 constants in the environment, all on `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`, `admit`, `native_decide`, `axiom`.

| Module | Content |
|---|---|
| `SUN` | `SUN N` = `Matrix.specialUnitaryGroup (Fin N) ℂ` for every `N` (`SUN 2` is `SU2` by unfolding). Topological group, compactness (`isCompact_SUN`), second countability, the defining representation `HasGaugeTrace (SUN N) N`, the Haar probability measure and its left invariance, and the package instances `GaugeGroupBase (SUN N)`, `GaugeRep (SUN N) N`. Consequences: `|Re tr g| <= N` (`abs_gaugeReTr_le_SUN`) and the Wilson measure of SU(N) is a probability measure on every torus, in every dimension, at every coupling (`isProbabilityMeasure_wilsonMeasure_SUN`). |
| `Centre` | The centre `Z_N`. `centreElt N w h` = the scalar matrix `w I` for `w^N = 1` (`|w| = 1` is derived, `det (w I) = w^N = 1`); `centreHom N : rootsOfUnity N ℂ →* SUN N`, injective (`centreHom_injective`), central (`centreHom_central`), with `N` elements (`card_centre`). It acts on the fundamental representation as `ζ` (`centreHom_rep`; `tr (ζ I) = N ζ`). `N`-ality: `HasNality ρ k` means `ρ (ζ I) = ζ^k`; proved for the fundamental (`k = 1`, `hasNality_fundamental`) and its complex conjugate (`k = -1`, `hasNality_conj`). For `N = 2`, `w = -1` the element is `negOneSU2` (`centreElt_two_neg_one`). The cost distance `geodSUN a b = arccos (Re tr (a b⁻¹) / N)`: non-negative, `<= pi`, zero on the diagonal, positive on some pair for `N >= 2` (`exists_geodSUN_pos`, on `(e^{2 pi i/N} I, 1)`), and equal to `geodSU2` at `N = 2` (`geodSUN_two`). |
| `Projection` | The projection of matrices onto SU(N) by polar decomposition: `polarFactor A = A (A* A)^{-1/2}` (with `CFC.sqrt`), the phase correction `phaseFix` (multiply by `e^{-i arg(det U)/N}`), and `projSUN N A` = the result if it lies in SU(N), `1` otherwise. **Identity on SU(N)** (`projSUN_coe`, the package field `proj_rep`). **Defined on all invertible matrices**: the polar factor of an invertible matrix is unitary (`polarFactor_mem_unitary`) and the corrected matrix has determinant 1 (`projVal_mem_of_det_ne_zero`), so the "constant elsewhere" clause only concerns singular matrices (`projSUN_val_of_det_ne_zero`). |
| `Meas` | `projSUN N` is **measurable** (`measurable_projSUN`; the square root is measurable by `CFC.measurable_sqrt`, the inverse is `(det)⁻¹ adj`, `arg` is measurable). |
| `SUNSubst` | `instGaugeSubstSUN N` for `N >= 2` (`[Fact (2 <= N)]`): cost distance, centre = range of `centreHom`, projection = `projSUN`; every field proved. Agreement with phase 1 at `N = 2` (below). The strong-coupling area law for SU(N) with `N` even. Two examples of the phase 1 generic layer at SU(N), any `N`, any `d`. |

## Agreement with the SU(2) instance of phase 1 (item 4)

* `GaugeGroupBase`, `GaugeRep`: `instGaugeGroupBaseSUN 2 = instGaugeGroupBaseSU2` and `instGaugeRepSUN 2 = instGaugeRepSU2` by `rfl` (propositions).
* Cost distance: `geodDist_two` (from `geodSUN_two`). Centre: `centre_two`, from `range_centreHom_two : range (centreHom 2) = {1, negOneSU2}`.
* Projection: `projSUN_two_eq_on_SU2`: the two projections agree on SU(2), where both are the identity. **They are different maps off SU(2)**: `RouteA.projSU2` rescales by `|det A|^{-1/2}` and falls back to `1`, `projSUN` is the polar factor with a phase correction. The package only uses the identity on the group, so the instance field is the same statement.
* A phase 1 statement re-derived from the SU(N) one at `N = 2`: `su2_area_law_of_mixture_SUN` has the same type as `su2_area_law_of_mixture_general` and is proved from `area_law_of_mixture_SUN` (general `N`: bound `B = M = N`).
* The SU(2) instance fields of phase 1 are not themselves *defined* from the SU(N) instance (the data differ in the projection and in how the centre set is written); the statements are tied together by the theorems above.

## New result along the way

`wilson_area_law_SUN_even`: the strong-coupling area law (the bound of `wilson_area_law_SU2` with `2` replaced by `N`) for SU(N)
with `N` **even**, from `wilson_area_law_explicit` with the central element `-I`. The repository had it only for SU(2) and `U(n)`.
`-I` lies in SU(N) exactly when `N` is even, so for **odd `N` the order-two centre does not exist** and the same argument
does not apply; there the centre is `Z_N` with `N` odd and the Z2 comparison layer has to become a `Z_N` layer (phase 3).

## What was not done

* No regularity of `projSUN` beyond measurability (no continuity statement; none is a package field).
* `N`-ality is proved for the fundamental and its conjugate only (`k = ±1`). Other representations (adjoint, `k`-index
  tensors) need those representations to be constructed first.
* `GaugeSubst` needs `N >= 2` (`geodDist_pos`); `SUN N` and the package instances `GaugeGroupBase`, `GaugeRep` are for every `N`.

## The remaining `inst` files that now port mechanically (item 5)

Classification from the audit table plus a reading of the statements; not checked file by file. "Mechanical" means: restate
over a generic `Tuning` / `BlockingFamily` / `VTuning` the way `Filter`, `Noisy`, `PerVolume` did, replace `T.ym` by
`wilsonMeasure G n (T.beta k) d (T.side k j)`, `4` by `d`, `geodSU2` by `GaugeSubst.geodDist` (now available for SU(N)),
and use the `d`-counting of phase 1 (`card_le_of_physExtent`, `poly_exp_le`, `card_boxBlock`).

* **Mechanical, counting-type (`needs4`):** `OneBox/Fine`, `OneBox2/Cube`, `V3/CondMass`, `Torus/Local` (the transfer
  statements; the counting is done), `RouteA/BlockedSlab`, `Quantum/BlockedRoute`, `H1/Level`, `V3/TimeSep`, `V3/W1Route`,
  `V4/Gap`, `V4/Recursion`, `Assembly`, `Crossover/P4Chain` (the `(1 + D/L1)^4` and `24/a^4` are `poly_exp_le` and
  `d!/a^d`).
* **Mechanical, statement-type (`fixed4`):** `Adjoint2/PatternAssembly`, `Book/TwoSize`, `Defects/Supplier`,
  `Existence/Bridge`, `H1/Split`, `OS/GapLoc`, `OneBox2/Concrete`, `OneBox2/CubeAnchor`, `Quantum/LemmaT`,
  `Quantum/LimitStates`, `Saturation/Reduction`, `SectorS/ConjS`, `Seg1/Envelope`, `UV/Split`, `V3/CondInputs`, `V3/Top`,
  `V4/Top`, `V4/UV`.
* **Mechanical given the cost distance (`geodSU2` in statements):** `Interface/DenseTransfer`, `Interface/MeasBlocking`,
  `Interface/RandBlocking`, `OneBox/Tests`; and the `geodSU2_*` uses of `Repair/GeneralSupport`, `Repair/V4Bridge`,
  `Repair/WeightedW` (`exists_geodSU2_pos` is the package field `geodDist_pos`).
* **Not mechanical even with SU(N):** `Flip/Floor` (SU(2) gap constants), `OneBox2/Anchor` (the numerical anchor
  `24 tanh(2 beta)` is an SU(2) estimate; the counting `3^d` is done), `OneBox2/Wilson` (the dimension-2 fundamental and
  its kernel bounds), `V4/LCP` (flux limit with the centre layer), `Book/SU2Inst` (SU(2) instances only, replaced by `SUN`).
  The `subst` files of phase 3 are untouched.
* Order of work suggested: the `Tuning`-based chain first (`UV/Split`, `Assembly`, `V3/*`, `V4/*`, `H1/*`), since the
  others restate their results.

---

# Phase 1b: the `inst` files ported to the generic form (2026-11-24)

New files (11, all in `formal/ProofPhase/General/`, nothing existing edited): `Setting`, `CondMass`, `Fine`, `Wilson`,
`Concrete`, `Anchor`, `Cube`, `Gap`, `Recursion`, `PortSUN`, `TopPort` (imports phases 1, 2 and these). Axioms of the new
declarations: `axioms-port.log` (`axioms-port.sh` regenerates it). Every file builds with 0 warnings. Count: 125 theorems and 39 definitions, abbreviations and instances in the source, 175 constants in the environment, all on `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`, `admit`, `native_decide`, `axiom`; 21 `example` checks are part of the build.

**Method.** Each generic statement is the old text with `SU2` replaced by `Gr` (any group with the package: `GaugeGroupBase`,
`GaugeRep Gr nr`), `4` by `d` (`[NeZero d]`), the representation dimension `2` by `nr`, the Wilson law `T.ym k j` by
`ymLaw nr d T k j`, `geodSU2` by a cost distance parameter, and the counting constants by the `d`-counting of phase 1. The
old theorem is then re-derived as `X_su2`, proved from the generic theorem at `SU2`, `nr = 2`, `d = 4`, and **checked
identical** by `example : @old = @X_su2 := rfl` (definitions by `Iff.rfl`).

## What is ported

| Module | Old file | Ported |
|---|---|---|
| `Setting` | `Assembly`, `RouteA/BlockedSlab`, `Torus/Local`, `V3/TimeSep`, `V3/CondMass` | `blockedLaw`, the transfer hypotheses `ObsTransfer`, `ObsTransferPhys`, `ObsTransferU`, `ObsTransferCell`, `ObsTransferPhysT`, `ObsQuasiLocT` and the reductions `obsTransferPhys_of_cell`, `obsTransferPhys_of_U`, `obsTransferPhysT_of_phys`, `obsQuasiLocT_of_obsTransferPhysT` |
| `CondMass` | `V3/CondMass` | `CellGeometry`, `CondMass`, `CondMassDecay`, `condMassDecay_of_condMass` (cell count `d (2 floor(R/L1 + c1) + 1)^d`), `obsTransferPhysT_of_condMassDecay`, `obsTransferPhysT_of_condMass` |
| `Fine` | `OneBox/Fine` | `gaugeAct`, `FineOneBox`, `FineDecayInv`, `fineDecayInv_of_fineOneBox` |
| `Wilson` | `OneBox2/Wilson` | gauge covariance of the Wilson box kernel (`xp_gauge`, `prod_map_act`, `locSpec_covariant`, `gaugeSpec_covariant`, `measurable_gaugeSpec`); `haar_map_mul_right` (right invariance from left and inversion invariance) |
| `Concrete` | `OneBox2/Concrete` | `wilsonBoxSpec`, `wilsonBlockSpec`, their covariance, `WilsonOneBox`, `fineOneBox_of_wilsonOneBox` |
| `Anchor` | `OneBox2/Anchor` | `influence_block`, `lifted_influence_id`, `kexact_le`, `oneBoxSum_anchor`, `wilsonOneBox_strong`, `wilsonOneBox_strong_const` with `anchorK d = d 2(d-1)` (24 for `d = 4`) and `anchorG d = 3^d anchorK d` (1944) |
| `Cube` | `OneBox2/Cube` | `cubeLaw`, `cutSpec`, `cubeBoxSpec`, `cubeLifted`, `WallCutOneBox`, `CubeDecay`, `cubeDecay_of_wallCutOneBox` |
| `Gap` | `V4/Gap` | `LawGapW`, `LevelDprimeWOn`, `lawGapW_of_levelDprimeWOn`, `lawGapBddW_of_lawGapW` (`LawGapBddW` is the one of `Torus.lean`) |
| `Recursion` | `V4/Recursion` | `BlockGapBddW`, `StageTwoW`, `blockGapBddW_of_stageTwo`, `blockGapBddW_of_levelDprimeWOn` (tail `d!/r^d` for `24/r^4`) |
| `PortSUN` | none | the decay from the one-box criterion, the SU(N) anchor, the cube decay and the recursion lemma at `SUN N`, any `N`, any `d` |

**Re-derived old statements** (each `rfl`-checked): `OneBox2.gaugeSpec_covariant`, `prod_map_act`, `xp_gauge`,
`measurable_gaugeSpec`; `OneBox2.wilsonBoxSpec_covariant`, `fineOneBox_of_wilsonOneBox`; `OneBox2.influence_block`,
`lifted_influence_id` (and `kexact_le`, `oneBoxSum_anchor`, `wilsonOneBox_strong`, `wilsonOneBox_strong_const`, proved
from the generic ones with `anchorK 4 = 24`, `anchorG 4 = 1944`); `OneBox.fineDecayInv_of_fineOneBox`;
`OneBox2.cubeDecay_of_wallCutOneBox`; `V3.condMassDecay_of_condMass`, `obsTransferPhysT_of_condMassDecay`,
`obsTransferPhysT_of_condMass`; `Torus.obsTransferPhys_of_cell`, `obsTransferPhys_of_U`; `V3.obsTransferPhysT_of_phys`,
`obsQuasiLocT_of_obsTransferPhysT`; `V4.lawGapW_of_levelDprimeWOn`, `lawGapBddW_of_lawGapW`,
`blockGapBddW_of_stageTwo`, `blockGapBddW_of_levelDprimeWOn`. Definitions agree by `Iff.rfl`: `ObsTransfer`,
`ObsTransferPhys`, `ObsTransferU`, `ObsTransferCell`, `ObsTransferPhysT`, `ObsQuasiLocT`, `CondMass`, `CondMassDecay`,
`CellGeometry`, `FineOneBox`, `FineDecayInv`, `WilsonOneBox`, `WallCutOneBox`, `CubeDecay`, `LawGapW`,
`LevelDprimeWOn`, `BlockGapBddW`, `StageTwoW`.

## Findings

* **The "fundamental dimension 2" and the constants were not subst facts.** In `OneBox2/Wilson`, `Concrete`, `Anchor` the `2`
  is the bound `|Re tr| <= n` (`nr`), and the numbers `24` and `1944` are `d` links per site times `2(d-1)` plaquettes
  per link, and `3^d` neighbouring sites (`OneScale.SingleLink.card_plaqsAt_le`, `card_near_le`). With `anchorK`,
  `anchorG` the anchor holds for every `d` and for every group of the package. So `OneBox2/Wilson` and `Anchor` move
  from "subst?" in the audit to ported. For SU(N) the anchor window is `3^d d 2(d-1) tanh(N beta_k) <= g < 1`.
* **Right invariance** of the Haar measure (needed for the gauge covariance of the box kernel) is derived from left and
  inversion invariance (`haar_map_mul_right`), so no field was added to `GaugeGroupBase`.
* **`Cube` needs `[T2Space Gr]`** (for `MeasurableEq`, in `measurableSet_eq_fun`); the package does not carry it.
  `T2Space` is an extra hypothesis of the cube declarations; SU(2), SU(N), U(N) are Hausdorff.
* **Cost distance.** `Gap` and `Recursion` take a cost distance `cost`; the theorems using Dobrushin decay take the two
  facts about it that they use (`0 <= cost <= P`, `P = pi` for `geodSU2` and `geodSUN`: `geodSUN_nonneg`, `geodSUN_le_pi`).
* No ported file needed a `subst` fact of phase 3.

## RouteB/Duality (`Fin 4` rotation, plane pairing)

`RouteB/Duality` is already generic in the group (`G`, `n`: any compact group with continuous unitary representation). The
dimension is intrinsic: the rotation `(0 2)(1 3)` exchanges the plane `(0,1)` with the plane `(2,3)`, so the temporal
twist and the spatial twist of the plaquette type are dual only because `4 = 2 + 2` (a plaquette twist is a
codimension-2 object; it is again a plaquette twist only in `d = 4`). For `d != 4` the statement `tHooft_rotation` has no
analogue of this form (in `d = 3` the dual of a plaquette twist is a link twist). Only the first part, `twistZ_perm`
(the partition function is invariant under a permutation of the axes), holds in every dimension; it is stated for `Fin 4`
and was not ported. Not forced.

## Where the port stopped, and what is left

The ported chain ends at a clean point: everything that does not need the **slab-observable layer** or the **flux/LCP layer**.
What is left depends on one of two things:

1. **The slab-observable layer** of `Objects` and `Torus/Local`: `SlabObs`, `Tuning.wcorr`, `LatticeGap`, `MassGap`,
   `TorusDecayLoc`, `MassGapMFLoc` (observables supported on a time slab, correlations `Cov(F o S_n, F o Theta)`). It is
   mechanical to generalise (`timeSlab`, `tShift`, `thetaConn` are already generic in `G`, `d`) but it is a layer of its
   own and was not started. It unlocks: `Torus/Local` (the rest: `torusDecayLoc_of_blockedRoute`, `gapVF_of_family`,
   `gapMF_of_family`, `bothOrdersLoc_*`), `V3/TimeSep` (`torusDecayLoc_of_blockGapUnifT`, the level routes), `V3/W1Route`,
   `V3/CondInputs`, `V3/Top`, `V4/Gap` (the second half), `V4/UV`, `V4/Top`, `H1/Level` (`torusDecayLoc_of_blockGapUnif`
   with `24/a^4`), `H1/Split`, `RouteA/BlockedSlab` (`wcorr_le_blocked`), `Quantum/BlockedRoute`, `Quantum/LemmaT`,
   `Quantum/LimitStates`, and then `Interface/MeasBlocking`, `RandBlocking`, `DenseTransfer` (which import `V4/Top`).
2. **`OnLCP`, `NonTrivial`, the flux limit** (`Assembly`, `V4/LCP`, `IsFluxLimitSU2` of `Objects`): the line of constant
   physics and the flux layer name SU(2) in substance (centre `Z2`, 2x2 matrices) and wait for phase 3. This blocks the
   assembly theorems (`yang_mills_assembly_*`).

Also untouched: `Adjoint2/PatternAssembly`, `Book/TwoSize`, `Defects/Supplier`, `Existence/Bridge`, `OS/GapLoc`,
`Saturation/Reduction`, `SectorS/ConjS`, `Seg1/Envelope`, `UV/Split`, `Crossover/P4Chain` (all restate over `Tuning`,
`BlockingFamily`, `VTuning` and the slab layer; same method), and `Flip/Floor` (SU(2) gap constants, not mechanical).
**Suggested next step:** port the slab-observable layer (`Setting`-style, one file), after which the `V3/V4/H1` torus-decay
reductions and `Interface/*` follow with the same method.
