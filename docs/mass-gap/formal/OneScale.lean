/-
The one-scale reduction (2026-11-21). Released under Apache 2.0.

Formalisation of the Lean-ready parts of `docs/mass-gap/weak-coupling/PROOF-NOTE.md` (section 12.2), in the framework of
`AreaLaw` (lattice, connections, product Haar measure), `Influence` (total variation, the single-link TV lemma) and
`Positivity` (reflection positivity). Everything here is written for this project; other formalisations were not used.

Standard background, reproved here in our setting: Dobrushin's uniqueness theorem and covariance decay (Dobrushin 1968,
1970), Foellmer's comparison argument (Foellmer 1982), the block form of Dobrushin–Shlosman (1985), reflection positivity
of lattice gauge theory and the doubling argument (Osterwalder–Seiler 1978). New in the proof note and formalised here:
the block telescoping proof of Theorem A without a frozen set (correction C1), its uniformity in the number of blocks,
the multiplicity-weighted single-link GDS (valid for every torus size), and the bookkeeping of Corollary B.
The uniform hypothesis of Corollary B (`OneScale.CorollaryB.UniformGDS`) is OPEN: it is stated, not proved.

- `OneScale.Blocks`: splicing, oscillation bounds, Lemma 2.3 (telescoping), block specifications, Lemma 2.2, Lemma 2.6.
- `OneScale.Comparison`: Lemma 2.5 (propagation), Step 1 (contraction).
- `OneScale.Decay`: Theorem A, H variant (`BlockSpec.cov_le_weighted`, `BlockSpec.theoremA_H`).
- `OneScale.Lipschitz`: Theorem A, W variant (`BlockSpec.theoremA_W`).
- `OneScale.Product`: product measures with factorised density, Lemma 2.1 (DLR), `productBlockSpec`.
- `OneScale.OscTV`: Lemma 2.4 (oscillation against total variation).
- `OneScale.Gauge`: block specifications of torus gauge measures under (Φ) (`gaugeBlockSpec`).
- `OneScale.SingleLink`: non-vacuity at strong coupling (Proposition 8.1, `gds_single`, `wilson_singleLink_decay`).
- `OneScale.Doubling`: Lemma 6.2, Theorem C (abstract), Corollary C1 (`prefactor_free`).
- `OneScale.TorusRP`: Theorem C on the finite torus from site reflection positivity (`torus_theoremC`).
- `OneScale.CorollaryB`: Corollary B.1, lattice part, physical units; the open hypothesis `UniformGDS`.
- `OneScale.LinkDist`: a concrete link distance (`ℓ^∞` cyclic distance of base sites), the time-slab separation, and
  the unconditional strong-coupling decay in time (`wilson_singleLink_timeDecay`).
- `OneScale.TimeShift`: time translation, invariance of the torus measure under it and under `Θ`,
  `S_k ∘ Θ = Θ ∘ S_{-k}`, the Hankel identity (Lemma 6.1), Theorem C with `hH` discharged (`torus_theoremC_corr`,
  `torus_theoremC_hankel`).
- `OneScale.CubeChain`: Theorem A with the thin-cube family on the torus for slab observables, Theorem C under GDS for
  thin cubes, a finite-volume decay bound uniform in `N`, and `corollaryB_of_uniformGDS`: Corollary B.1 with
  `UniformGDS` (on a sequence of tori per level) as the only open hypothesis.
-/

import OneScale.Blocks
import OneScale.Comparison
import OneScale.Decay
import OneScale.Lipschitz
import OneScale.Product
import OneScale.OscTV
import OneScale.Gauge
import OneScale.SingleLink
import OneScale.Doubling
import OneScale.TorusRP
import OneScale.CorollaryB
import OneScale.LinkDist
import OneScale.TimeShift
import OneScale.CubeChain
