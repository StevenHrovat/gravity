/-
The one-scale reduction, effective-theory layer, root import (2026-11-21). Released under Apache 2.0.
-/

import OneScale.Effective.Robust
import OneScale.Effective.Reduction
import OneScale.Effective.Physical
import OneScale.Effective.Curvature

/-!
# Effective-theory reduction: two hypotheses at one physical scale in place of `UniformGDS`

* `OneScale.Effective.Robust`: distances between block specifications (`SpecDist`, `TVClose`, `InfluenceDev`,
  `InfluenceDevW`) and the **robustness lemma**: an influence bound `κ` for `q` gives `κ + 2δ` for `q'` when
  `SpecDist q q' ≤ δ` (H form; `κ + δ` for the pairwise and W forms), and GDS(γ) gives GDS(γ + 2rδ) for local
  specifications (`r` the shell-to-coverage ratio).
* `OneScale.Effective.Reduction`: Theorem A for specifications near a limit with GDS(γ_∞), `γ_∞ < 1`, and the abstract
  reduction theorems `effective_reduction` (H) and `effective_reduction_W` (W): from some level on, GDS with
  `γ = (1 + γ_∞)/2` and uniform exponential decay.
* `OneScale.Effective.Physical`: the open hypotheses **(H1) `EffectiveConvergence`** and **(H2) `LimitGDS`** (and their
  W forms), and **`gap_of_effective`** (also `_W`, `_fine`): (H1) ∧ (H2) give exponential decay of block-observable
  covariances at a physical rate bounded below uniformly in the lattice spacing and the volume.
-/
