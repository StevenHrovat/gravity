# Renormalized Doeblin: the density floor set in physical units (2026-11-23)

Task (owner: "An extension of Doeblin, so that it shares the same floor as DMP, seems very feasible"; via the coordinator). Plain
Doeblin's mass per box vanishes as `a → 0` (`doeblin_mass_tendsto_zero`), because the floor `e^{−Cβ L^{d−1}}` is set in tick
units. Set it at the hand-over scale instead, where the box has a fixed physical size:
1. Doeblin for the **blocked** kernel at the M1 hand-over scale `L_*` (box of physical size `ℓ_*`): a floor `ε_*` uniform in `a`?
   Which M1 results give it, with which corrections?
2. The abstract theorem in Lean.
3. The `2d`-neighbour requirement: is `1 − ε_*` small enough per channel? By how much does it miss, and does a larger box help?
4. Large fields: null, small (rarity), or boundary term?

Marks: **Lean** (`Crossover/RDoeblin.lean`, 5 theorems, reusing `Mixing/Doeblin.lean` and `Chain.lean`; `axioms-dy.log` now
37 Crossover theorems, standard axioms only), **paper**, **sketch**, **citation**, **open**.

## 0. Verdict in plain words

* **A correction to the premise first.** M1 hands over at a **weak-coupling** scale: from the lattice spacing to `L_*` the
  effective coupling `ḡ` is small (`PROOF-BLUEPRINT.md`, P3.5 and the M1 paragraph). The coupling becomes of order one only at
  `L₁`, after the crossover `L_* → L₁`, and that crossover (P4) is the open core. So the floor at `L_*` is uniform in `a` but
  set by a **small** coupling, so it is a tiny `ε_*`.
* **Steps 1 and 2 close: a floor uniform in `a` gives a physical rate along a chain** (Lean, abstract; paper for the M1 input).
  For a family of blocked transfer kernels with the same floor `ε_*` for every spacing, the chain contracts by `(1 − ε_*)^n`, and
  the influence at physical distance `D` is at most `exp(−m D)` with `m = −log(1 − ε_*)/ℓ_*`, the same for all `a`
  (`rdoeblin_physical_decay`). What it buys: **for a fixed physical cross-section, a gap uniform in the lattice spacing**,
  conditional on M1's uniform floor. That is the finite-physical-volume statement, now in physical units.
* **Step 3 fails, and this is the first step that does not close.** A grid needs the per-channel bound summed over `2d = 8`
  faces to stay below 1. That requires the floor exponent `C < log(8/7) ≈ 0.134` (`floor_column_requirement`), or
  `C < −log(1 − p_c) ≈ 0.22` in the disagreement-percolation form (`floor_disagreement_requirement`, with the site-percolation
  threshold of `ℤ⁴`, `p_c ≈ 0.197`, citation). At `L_*` the floor exponent is of order `2 β_eff N_∂` (`N_∂` = plaquettes coupling
  the box to its collar, `β_eff = 4/ḡ²` large), at least in the tens even for a one-block box. **It misses by orders of
  magnitude.** A larger box at fixed physical coupling **hurts**: `C` grows like the box surface, `n^{d−1}`. A smaller box stops at
  one block. Only a strongly coupled blocked theory (`β_eff N_∂ ≲ 0.1`) passes, and there the gap is already known by other
  means.
* **Step 4: large fields are a small set (rarity) plus a boundary factor, not a null set.** But since step 3 fails for the
  small-field boxes already, they do not change the verdict.

## 1. The floor of the blocked kernel at `L_*` (paper, sketch; M1 input)

**Which M1 results** (`PROOF-BLUEPRINT.md`, M1 paragraph; `m1-tools/M1-PLAN.md` §0):
* *Law preservation and the inductive form at `L_*`*: the law of the block variables at `L_*` is given exactly, in inductive
  form, as a small-field part at coupling `ḡ(L_*)` plus R-terms (released large fields) and labels.
* *R-term bounds*: activities with a kept slack `e^{−c p₀²}` per birth-scale cube, and a positive label gas with a one-box
  contraction; Kotecký–Preiss convergence (segment 1, `Seg1/`, cluster bound `≤ log 2`, uniform in level and volume).
* *Uniformity in `a`*: `ḡ(L_*)` is fixed by the hand-over condition, so the blocked description at `L_*` is the same for every
  spacing, up to corrections that are uniformly small (the M1 claim, at paper level, with its named readings and adaptations).

**The floor (sketch).** Take as reference `ν` the box law at one fixed outside. The density of the box law at any other outside,
relative to `ν`, is a ratio of Boltzmann factors of the plaquettes coupling the box to its collar (worst case
`e^{−2 β_eff N_∂}`), times the ratio of R-term factors touching the box (worst case `e^{−2 Σ_{X ∋ box} |R(X)|}`, finite and
uniform in `a` when the polymer sum converges). So

    ε_* ≥ exp(−2 β_eff(ḡ) N_∂(n) − 2 K_R),

uniform in `a`, with `K_R` the R-term sum through one box. **Named gap:** this needs the R-term bounds two-sided (absolute values),
which M1's activity bounds are. The blocked state space is the continuum (SO(3) × closed Z₂ layer); the finite-state Lean
theorem below is the model of it (the measure version is standard and not formalised).

## 2. The abstract theorem (Lean, `RDoeblin.lean`)

| statement | Lean name | mark |
|---|---|---|
| family `K a` with floor `ε ν_a ≤ K a`, `ε` independent of `a`: `Contracts (K a ^ n) ((1 − ε)^n)` for every `a` | `rdoeblin_family` | Lean |
| `(1 − ε)^n = exp(−m · nℓ)`, `m = −log(1 − ε)/ℓ` | `one_sub_pow_eq_exp` | Lean |
| for every `a`: influence at physical distance `D = nℓ` is `≤ exp(−m D)` | `rdoeblin_physical_decay` | Lean |
| `k (1 − e^{−C}) < 1 ↔ C < log(k/(k − 1))` (`k ≥ 2`) | `floor_column_requirement` | Lean |
| `1 − e^{−C} < p ↔ C < −log(1 − p)` | `floor_disagreement_requirement` | Lean |

With `phys_rate_of_uniform` (`Neighbours.lean`), the rate per physical length is `≥ −log(1 − ε_*)/ℓ_* ≥ ε_*/ℓ_*`, uniform in `a`.

**What it gives (paper).** Apply it to a chain whose step is one slab of the blocked lattice: cross-section `n³` blocks (physical
size `nℓ_*`), length one block. The slab kernel has a floor `e^{−C_slab}`, `C_slab ≈ 2 β_eff · 3 n³ + 2K_R`, uniform in `a`. So
on a spatial torus of **fixed physical size** the transfer-matrix gap is at least about `e^{−C_slab}/ℓ_*`, uniformly as `a → 0`.
That is a real gain over plain Doeblin, whose rate per physical length vanishes. It degrades as `e^{−c n³}` with the physical
cross-section, so it says nothing about infinite volume.

## 3. The `2d`-neighbour requirement (Lean core; paper numbers)

* **Column-sum form** (Dobrushin): per-channel `1 − ε_*` summed over `2d = 8` faces `< 1` iff `C < log(8/7) ≈ 0.134`.
* **Disagreement-percolation form** (van den Berg–Maes, citation; already used in M1's pattern gas): the probability that a box
  disagrees under a maximal coupling of two outsides is `≤ 1 − ε_*`, and uniqueness with exponential decay follows if this is
  below the site-percolation threshold of the box graph, `p_c(ℤ⁴) ≈ 0.197` (citation, recalled). That needs `C < 0.22`.
* **At `L_*`:** `C ≈ 2 β_eff N_∂ + 2K_R`. For a single block in `d = 4`, `N_∂` is of order 24 plaquettes (each of 6 planes
  through the block's faces, counted crudely). With `β_eff` of order the W2 couplings (2.3 to 3.5), `C` is of order 100. **The
  requirement is missed by a factor of several hundred in the exponent:** the per-channel bound is `1 − e^{−100}`, against `1/8`
  needed.
* **Larger box at fixed physical coupling:** `N_∂ ∝ n^{d−1}`, so `C` grows and the per-channel bound gets **closer to 1**. It
  hurts. **Smaller box:** stops at one block, still `C ≫ 0.13`.
* **Where it would pass:** a blocked theory with `β_eff N_∂ ≲ 0.1`, deep strong coupling. There a cluster expansion gives the gap
  anyway (Osterwalder–Seiler, citation). Renormalized Doeblin does not bridge the window between weak and strong coupling.
* **Why the summed condition cannot come from a floor (paper).** A floor is a worst case over each outside separately; the
  `2d` sum needs the influence to shrink with the number of channels. Doeblin bounds each channel by the same `1 − ε`, and that
  is sharp (`doeblin_sharp`). A joint floor for all `2d` channels gives the same bound on the joint change, not a sum below 1.
  This is `pnp/CHAIN.md` 4, restated at the renormalized scale.

## 4. Large fields (paper)

* **Not null.** M1 releases every large field into R-terms. A large-field region is an event of positive weight: about
  `e^{−c p₀²}` per birth-scale cube, the kept slack.
* **Small (rarity) for the floor.** In a box without large fields the floor is the one of section 1. A box meeting a large-field
  region still has a positive floor (compact group: the crude floor `e^{−2 β N_∂}` at the fine scale), but a much worse one. In
  the disagreement-percolation form such boxes count as bad sites, with probability `≲ e^{−c p₀²}` times the number of cubes per
  box, added to the percolation parameter. At weak coupling that is small.
* **A boundary term through the R-term factor.** R-terms that touch the box but lie mostly outside enter the floor as the factor
  `e^{−2K_R}`, a bounded multiplicative correction (uniform when the polymer sum converges).
* **Verdict:** small set plus boundary factor. Neither repairs step 3, which fails already for small-field boxes.

## 5. Status

| step | result | mark |
|---|---|---|
| premise: M1's `L_*` is weak coupling (`ḡ` small); order-one coupling only at `L₁` after P4 | correction | citation (blueprint) |
| 1. blocked floor `ε_* ≥ exp(−2β_eff N_∂ − 2K_R)`, uniform in `a` | closes at paper level, conditional on M1 (two-sided R-term bounds) | sketch |
| 2. uniform floor ⟹ chain contraction `(1 − ε_*)^n` and physical decay `exp(−mD)`, `m` independent of `a` | closed | Lean |
| 2'. gap uniform in `a` on a spatial torus of fixed physical size | follows from 1 + 2 | paper |
| 3. `2d`-neighbour sum: needs `C < 0.134` (column) or `< 0.22` (disagreement percolation); at `L_*`, `C` is of order 100; larger boxes hurt | **fails; first open step** | Lean (requirements), paper (numbers), citation (`p_c`) |
| 4. large fields | small set (rarity) plus a boundary factor; not null | paper |

## 6. Files

* `RDOEBLIN.md` (this note); `formal/ProofPhase/Crossover/RDoeblin.lean` (new, 5 theorems); `axioms-dy.sh` extended,
  `axioms-dy.log` (37 theorems, standard axioms); `~/formal-dy` deleted.
