# c8c-concrete: the one-box route made concrete in Lean (cycle 8, workstream 3, 2026-11-22)

Lean: `formal/ProofPhase/OneBox2/{Lift,Wilson,Concrete,Anchor,Cube,CubeAnchor}.lean` (about 1580 lines), built in `~/formal-c9c`
(`build.sh ProofPhase.OneBox2.<Module>`), axioms in `axioms.log` (only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`,
no `native_decide`, no new axiom). `OneBox/` is untouched and imported.

## 1. The box law, constructed (task 1): done in full, not only for the finite lattice

* `OneScale.Gauge.gaugeBlockSpec` already gave the DLR box kernel `gaugeSpec` as a `BlockSpec` of the Wilson measure (blocks of
  fine links). Missing: regrouping by cells, measurability of the kernel, gauge covariance.
* `Lift.lean`: `liftSpec` / `liftBlockSpec` turn a fine `BlockSpec` into a `BlockSpec` of the lifted law `mu . cellLift^-1`
  (blocks of cells; cut cells get frozen values `rho`). DLR of the lift is the fine DLR applied to `h . cellLift`
  (`lift_splice_eq`); measurable block averages need the kernel to be measurable as a measure-valued map
  (`measurable_integral_spec`); `liftSpec_covariant`: a covariant fine kernel gives a covariant lifted kernel.
* `Wilson.lean`: `measurable_gaugeSpec`; `xp_gauge`, `plaqProd_gauge` (plaquette weight is gauge invariant);
  **`gaugeSpec_covariant`**: `q_B(g.sigma) = g_* q_B(sigma)` as measures, for every gauge transformation `g` of the whole torus
  (via `prod_map_act`: product Haar is invariant under `U_l -> g(site) U_l g(target)^-1`).
* `Concrete.lean`: **`wilsonBoxSpec`** (the conditional law of the Wilson measure on a box of cells given the outside),
  **`wilsonBlockSpec`** (the `BlockSpec`: DLR is a field, so it is the conditional law), **`wilsonBoxSpec_covariant`**,
  **`WilsonOneBox T`** (= `FineOneBox` with the actual box law, no existential spec, no assumed covariance),
  **`fineOneBox_of_wilsonOneBox`**, `yang_mills_assembly_wilsonOneBox`.

Removed from the one-box route: premises (a) existence of a box specification of the lifted Wilson measure and (b) its gauge
covariance. Not removed: the numbers `kappa` and the one-box sum (the substance), and uniformity in the level.

## 2. The strong-coupling anchor (task 2)

`influence_block`: for a block `B` and a link `z` outside it, `|q_B^U(F) - q_B^{U[z:=s]}(F)| <= D tanh(m(B,z) 2 beta)` for `F` of
range `<= D`, `m(B,z)` = number of plaquettes through `z` touching `B` (the single-link TV lemma applied to the whole box as one
Gibbs measure; no Dobrushin comparison needed for a box of one site). `lifted_influence_id`: the same for the box law regrouped
by cells that are single links.

**`wilsonOneBox_strong`**: if `T.l k = 1` for all `k` (cells = single links, fixed spacing), `0 <= beta_k` and
`1944 tanh(2 beta_k) <= g < 1`, then `WilsonOneBox T`, hence `FineOneBox T`. Box: one site (`Lambda_0 = {0}`, `n_max = 1`, `D_0 = 0`);
influence of an outside link at the `<= 81` positions within distance 1 is `<= 24 tanh(2 beta)` (box of 4 links times at most 6
plaquettes through a link); `gamma = g e^lambda < 1`.
**Range: `beta < artanh(1/1944)/2`, about `2.57e-4`** (`wilsonOneBox_strong_const`: constant coupling, `1944 tanh(2 beta) < 1`).
Crude: the single-link Dobrushin window is `beta < 0.0278`; a box of 4 links with the TV bound loses a counting factor of about
100. A sharper count (plaquettes shared per neighbour, 80 not 81) would gain a small constant only.

Scope, said plainly: the anchor tuning has one lattice step per cell, so the spacing is fixed; it shows the criterion is
non-empty, not that it holds along a continuum line. Cells with many links (`l_k -> infinity`) at strong coupling need the
Dobrushin comparison argument for box influences with link-level decay (named next step).

## 3. Wall-cut version and confinement (task 3)

* `cubeLaw beta Q sigma0`: Wilson measure on the links of a region `Q` (a cube, or any finite link set) with the links outside frozen
  at `sigma0` (Chatterjee's boundary condition).
* `cubeBlockSpec`: for blocks `B_j` inside `Q`, the kernels `tau -> q_{B_j}(splice Q sigma0 tau)` form a `BlockSpec` of the cube law:
  **DLR consistency inside the cube** (`dlr_locSpec` for the weight `W(splice Q sigma0 .)`, `locSpec_cut`). `cubeLifted`: lifted to
  cells, with `sigma0` the frozen reference on cut cells; every cell is covered `|Lambda_0|` times, so the frozen part needs no extra blocks.
* **`WallCutOneBox T`**: `WilsonOneBox` with the influence bounds required for the cut box laws `cubeBoxSpec` of every region `Q` and
  every boundary condition `sigma0`; the influence is the unrestricted (gauge-blind, all bounded test functions of the box) one,
  because the decay in Definition 2.3 is for non-gauge-invariant local functions. By the Haar-alignment argument (NOTE c7c section 3.3,
  paper proof, not formalised) it equals the gauge-invariant one. `Q = univ` is the uncut criterion (`cubeBoxSpec_univ`).
* `abs_cov_le_of_oneBox_unres`: the one-box theorem without covariance and invariance. **`cubeDecay_of_wallCutOneBox`**:
  `WallCutOneBox T -> CubeDecay T`: one rate `lambda/L_1`, for every extent `R` a constant, from some level on, every torus, every region
  `Q`, every boundary condition, bounded measurable `F`, `G` (not nec. gauge invariant) at physical distance `>= D`:
  `|Cov| <= c_R e^{-mD}`. Uniform in level, volume, region, boundary condition.
* **`wallCutOneBox_strong`**: the wall-cut criterion is non-empty under the hypotheses of `wilsonOneBox_strong`
  (`lifted_influence_cut_id`: the influence on the cut block `Q cap b` is the block TV bound at the cut boundary; a link outside `Q` has
  influence 0).
* **`ChatterjeeTheorem24 T := CubeDecay T -> AreaLaw T`**: named external theorem. Citation: S. Chatterjee, *A probabilistic mechanism
  for quark confinement*, Commun. Math. Phys. 385 (2021), arXiv:2006.16229 (v5), Definition 2.3 and Theorem 2.4 (numbers as in
  `c7d-onebox-lit/LITERATURE.md`, row 19; not re-read here). Caveats of the transcription: the cited theorem is infinite-volume, lattice
  units, one coupling; ours is torus limit points, physical units, level-uniform. Whether the string tension extracted from the decay constants
  keeps its physical-unit uniformity must be read off the paper's proof.
* **`areaLaw_of_wallCutOneBox : ChatterjeeTheorem24 T -> WallCutOneBox T -> AreaLaw T`** (`SectorS.AreaLaw`).

Torus regions versus cubes of `Z^4`: a cube of side below half the torus side embeds isomorphically, so uniformity over all regions of all
tori contains Definition 2.3 for every cube (stated here for regions of tori; not formalised as an embedding).

## 4. Next steps

1. Dobrushin comparison for box influences with link-level decay, to make the anchor hold with cells of many links (continuum direction).
2. Read Chatterjee's proof of Theorem 2.4 and make `ChatterjeeTheorem24` the quantitative statement it proves (rate of the area law in terms of
   the decay constants), then check physical-unit uniformity.
3. Formalise Haar alignment (Kantorovich duality) to replace the unrestricted influence by the gauge-invariant one.
4. Gap-strength input: `kappa` summed over the shell below the box volume for SU(2) along a continuum line (numerics of c7b / c8).

## Files and commands

`setup.sh` (copies `~/formal/.lake`), `build.sh <module>` (shows errors only), `axioms.sh` (`axioms.log`). Run with
`wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c8c-concrete/<script>.sh`.
