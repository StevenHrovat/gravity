# Cycle 6, workstream 5 (c6e-bookkeeping): two bookkeeping gaps closed in Lean (2026-11-22)

Lean: `formal/ProofPhase/Book/{SU2Inst,NoiseLaw,KernelDensity,Cells,TwoSize}.lean`, built in `~/formal-c6e`
(`build.sh`, `check.sh`, `axioms.sh`; `axioms.log`: 32 headline theorems, all `propext, Classical.choice, Quot.sound`
(two use only `propext, Quot.sound`); no `sorry`, no `native_decide`, no new axiom). No existing file edited.

## 1. KernelDensity (task 1)

**Law used.** Any noise law `tau = h . Haar` with `h` measurable and `0 < m <= h <= M` (`Book.NoiseDensity`), and as the concrete
instance the von Mises-Fisher type law `h = exp(kappa Re tr g) / Z`, `Z = int exp(kappa Re tr) dHaar` (`Book.vmf kappa`, every
real `kappa`): continuous (`continuous_vmfDensity`), strictly positive (`vmfDensity_pos`), in `[e^{-2|kappa|}/Z, e^{2|kappa|}/Z]`.
The heat kernel on SU(2) is not in Mathlib or the project (no Laplace-Beltrami operator or heat semigroup on a compact Lie
group), so it is not used. It is not needed: the route needs only a density in `[m, M]` with `m > 0` (`gibbs_of_density`).
The paper argument of c5c 3.2 used class-function and inversion symmetry; the Lean proof uses neither (on a negative
temporal link the density is `h(b phi^-1)` instead of `h(b^-1 phi)`; only left translation and inversion invariance of Haar).

**Results.**
* `mulNoise_kernel` (S): for the multiplicative noisy blocking of ANY `RPBlocking P` and any `NoiseDensity ND`, there is a
  jointly measurable `kappa(U, phi) = prod_l linkKernel h l (b_l(U)) (phi_l)` in `[m^E, M^E]` (`E` = number of coarse links)
  such that the law of `mulNoise (P.B U) eta` under `pi tau x pi tau x pi tau` is `kappa(U, .) . productHaar`.
* **`goodNoisy_kernelDensity`** (S): `KernelDensity (goodNoisyFamily T w n hn ND.law) k j` for every `T w n hn`, `k`, `j`.
* **`goodNoisy_gibbs`** (S): `exists V : CoarsePot j, Potential (fun A => A) V and noisyBlockedLaw (goodNoisyFamily T w n hn ND.law) k j
  = gibbsMeasure (haarG SU2) V`, every `k j`; `goodNoisy_gibbs_all` is the `forall k j` form; `goodNoisyVMF_gibbs kappa` is the same for
  `ND = vmf kappa`, with no hypothesis at all.
* Supporting (S): `rawNoise_law` (the noise variable on each link is i.i.d. `tau`: `linkSplit` is a bijection),
  `mulNoise_eq` (`mulNoise` acts coordinatewise on the link variables), `mulNoise_law`, `pi_withDensity` (product of bounded
  densities is the density of the product), `map_mul_left_withDensity`, `map_inv_withDensity`, `map_inv_mul_withDensity`.

**Removes:** the named hypothesis `KernelDensity` (c5c NOTE 3.2 / table 5: "P") for the noisy good blocking. Combined with
`noisy_gibbs_clause` (V4Bridge) the Gibbs clause of every weighted D' input is automatic for this family; only the
weighted column of the representing potentials remains (the content, untouched). Constants `m^E, M^E` depend on the volume
(through `E`) and the noise law, not on the level `k` or the fine field. Not done here: gauge covariance in law of the noisy
blocked law (paper, c5c 3.2).

## 2. Two-size cells (task 2)

**Finding: the existing statements do not assume equal cells.** `StageTwoW`, `blockGapBddW_of_stageTwo`,
`blockGapBddW_of_levelDprimeWOn/WwOn` and `yang_mills_assembly_v4_strategyA` take any `M : N -> N` with `NeZero (M j)` and any
measurable `B2 k j`; no reflection structure on `B2` is asked. So the gap was only the existence of `B2` for every volume, and
no generalisation of an existing statement is needed. (The scale constant `s` is a free positive parameter: `s = 2^r` for
uniform cells, `s = 2^(r+1)` covers the nonuniform ones, whose side is at most `2 * 2^r`. The reading "cells of side floor/ceil of
`n/2^r`" in the brief is the cell COUNT: `m = floor(n/2^r)` cells per side, each of side `floor(n/m)` or `ceil(n/m)`.)

**Construction (`Book/Cells.lean`, `Book/TwoSize.lean`).**
* `cutPt n m i = floor(i n / m)`, `cellLen n m i = cutPt (i+1) - cutPt i`. `cellLen_two_sizes`: for `0 < m`, `cellLen = n/m` or
  (`~ m | n` and `cellLen = n/m + 1`); `cellLen_of_dvd`: exactly `n/m` if `m | n`; `sum_cellLen`: lengths add up to `n`;
  `exists_unique_cell` and `exists_unique_cell_sites`: every site of the periodic torus `(Z/n)^d` lies in exactly one product cell.
* `blockMap n m : GaugeConnection G d n -> GaugeConnection G d m`: link `(x, mu)` = ordered product of the fine links on the
  straight line from the corner of cell `x` to the corner of cell `x + e_mu` (periodic, any `n, m`). `measurable_blockMap`,
  `continuous_blockMap`, **`blockMap_gauge`** (gauge covariant: `blockMap (g . U) = (g o corner) . blockMap U`).
* `cellCount r j = max 1 (coarseSide j / 2^r)`, `twoSizeB2 r j = blockMap (coarseSide j) (cellCount r j)`: for EVERY `j` and `r`;
  `twoSizeB2_measurable`, `twoSizeB2_gauge`. Sizes: `twoSizeCell_bounds` (`2^r <= n` gives side in `[2^r, 2*2^r]` and the two-size
  statement with `m = cellCount`), `twoSizeCell_uniform` (`2^r | n` gives all cells exactly `2^r`: the old uniform blocking),
  `twoSizeCell_small` (`n < 2^r`: one cell, the whole torus).
* **Plugged in** (S): `blockGapBddW_twoSize` (`LawGapBddW` of the `L1` laws + `StageTwoW` => `exists lam > 0, BlockGapBddW T B1 lam`),
  **`yang_mills_assembly_v4_strategyA_twoSize`** (`OnLCP'`, `NonTrivial`, `LevelDprimeWOn` of `(blockedLaw T B1 k j).map (twoSizeB2 r j)`,
  `StageTwoW` for `twoSizeB2 r`, `ObsTransferPhysTW T B1` => `OpenInputsV4 T` and the conclusion) and
  `yang_mills_assembly_v4_strategyA_Ww_twoSize` (same with c5c's `LevelDprimeWwOn`). Statements are for all volumes `j`,
  with `M = cellCount r`.

**Removes:** the "Volumes" limitation of c5a NOTE 3 (B2 for every `j`). The hypotheses `LevelDprimeWOn/WwOn`, `StageTwoW` are
still open content, now about this concrete `B2`.

**Reflection positivity.** Not constructed: nothing in V4 or Repair requires `B2` to be an `RPBlocking` (`hB2` is `Measurable`).
If a later statement does need it (e.g. strategy (b) on cells), one would take `M j` even and symmetrise the cut points
(`floor` cuts are not reflection symmetric when `m` does not divide `n`); not needed now.

## Next step
Put the content hypotheses in terms of this `B2`: `StageTwoW` for `twoSizeB2 r` (what conditional mixing must give for
Wilson-line blocks of side `2^r..2^(r+1)`), and `NoisyObsTransferPhysTW` (c5c 3.3, option A) so the noisy good blocking reaches
`TorusDecayLoc`. Proposed change to existing files (not made): V4/Top.lean strategy (a) could quote `twoSizeB2` instead of an
abstract `B2`; `V4/Recursion.lean`'s "Volumes" paragraph can point to `Book/TwoSize.lean`.
