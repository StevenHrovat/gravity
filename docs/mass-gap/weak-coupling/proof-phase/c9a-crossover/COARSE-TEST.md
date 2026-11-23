# EXPLORATORY: the near-cut set at coarser scales (plan fixed before any coarse number was computed), 2026-11-23

**Status: EXPLORATORY.** Not part of any pre-registered verdict. Requested by the owner ("Please run the coarse scale test"); the
owner's reading (PREP, "Every running act sits between a spanned, unsaturated existence and a well-defined non-existence")
predicts that, at the scale where acts run, the bad set consists of finite clusters with an exponential size tail inside a spanning
good set. At the fine scale (DICHOTOMY.md 8.6) the near-cut set is isolated at β = 3.5 and spans the box in every snapshot at
β = 2.3. Question: **does the spanning at β = 2.3 disappear at a coarser scale?** CPU only; no new simulation.

## 1. Data (fixed)

* **Primary:** the saved equilibrium configurations of W2, `w2/runs/conf_b2.3.npz` and `conf_b3.5.npz`: 4 configurations each,
  periodic `16⁴`, SU(2) Wilson action, 300 heat-bath sweeps from a hot start (exact samples of the Wilson measure up to
  thermalisation). These are the right objects for the owner's statement about the system's own law (annealed).
* **Not used:** the conditional snapshots (chain-A box links): their box is `6⁴`, which blocks to `3⁴` at factor 2, too small for
  a spanning criterion.
* **Statistics:** 4 configurations per β. For block factors 2 and 4 the fine configuration is shifted by 16 offsets before
  blocking from the origin (factor 2: offsets `{0, 1}⁴`; factor 4: offsets `{0, 2}⁴`), giving 64 coarse configurations per β and
  factor; they are correlated (same fine configurations), so errors are quoted over the 4 independent configurations.

## 2. Coarse variables (fixed)

* **Blocking:** the W2 one-step good blocking (`constrained.py`, `Geometry`): the coarse link `(y, μ)` is the straight 2-link path
  plus `w = 0.5` times the six 2-link staples, summed as quaternions, **projected to SU(2)** (normalised), on the periodic lattice.
  Factor 4 = the same step applied twice (to the factor-2 lattice). Factor 1 = the fine links (reference, on the same configurations).
* **Lattices:** fine `16⁴`; factor 2: `8⁴`; factor 4: `4⁴` (very small; its spanning criterion is weak, stated with the result).

## 3. Near-cut criterion (fixed)

* Coarse plaquette `q₀ = ½ tr` of the coarse plaquette holonomy.
* **Primary threshold:** `δ_P(b) = log 6 / (2 β_eff(b))`, with the effective coupling of block factor `b` matched by the plaquette
  deficit: **`β_eff(b) = β · (1 − ⟨q₀⟩_fine) / (1 − ⟨q₀⟩_b)`**, averages over all plaquettes of the 4 configurations (at `b = 1` this
  is `β`). Limitation stated now: blocked variables are not Wilson-distributed, and this matching is a heuristic; it lowers `β_eff`
  when the coarse plaquettes are rougher, which raises `δ_P`.
* **Secondary (to show that the conclusion does not hinge on the threshold):** the fixed thresholds `δ ∈ {0.05, 0.1, 0.2, 0.3, 0.4}`
  at every factor, and the fine threshold `δ_P(1) = log 6/(2β)` applied unchanged to the coarse plaquettes.

## 4. Measures (fixed)

* Clusters: near-cut plaquettes connected when they are faces of a common cube (the adjacency of a dual sheet), on the periodic
  coarse lattice.
* Per coarse configuration: fraction of near-cut plaquettes; largest cluster as a share of all plaquettes; **spanning** = some
  cluster wraps the torus in some direction (its sites cover every value of one coordinate); the cluster-size list.
* Cluster-size distribution, pooled per (β, factor): complementary CDF `P(size ≥ s)`; **exponential tail** = a least-squares line of
  `log P(size ≥ s)` against `s` over `s ≥ 2` with negative slope and `R² ≥ 0.9`, *and* no spanning cluster in more than 10 % of the
  coarse configurations.

## 5. What counts as an answer (fixed)

At the primary threshold, per (β, factor):
* **spanning disappears** at factor `b`: spanning fraction `≤ 0.1` and largest-cluster share `< 5 %`;
* **spanning persists**: spanning fraction `≥ 0.9`;
* otherwise **partial**.

The owner's prediction is supported at β = 2.3 if spanning persists at factor 1 (already seen in the box) and disappears at
factor 2 or 4 with an exponential tail; it is contradicted at β = 2.3 if spanning persists at every factor; anything else is
inconclusive. At β = 3.5 the prediction expects no spanning at any factor.

## 6. Limits (stated now)

* Four independent configurations per β; factor 4 gives a `4⁴` lattice, on which wrapping is easy: a "persists" there is weak
  evidence, a "disappears" there is stronger.
* The near-cut criterion of the coarse variables is a proxy for the centre-layer flip cost at that scale (the coarse SO(3) cut);
  M1's centre layer is not simulated.
* The coarse lattice is not the scale where the theory is "run" in any controlled sense: block factors 2 and 4 of a lattice at
  β = 2.3 and 3.5, nothing more.

Code: `w2/coarse_test.py` (written after this plan).

---

## 7. Result (computed after this plan was fixed; `w2/coarse_test.py`, CPU 1 min 49 s, `w2/runs/coarse_test.json`)

Sanity checks of the code before the run (no coarse data looked at): an identity configuration blocks to the identity; coarse
plaquettes are invariant under a random fine gauge transformation to `3 × 10⁻¹⁵`.

**Primary threshold** (`δ_P = log 6 / (2 β_eff)`, `β_eff` matched by the plaquette deficit), per (β, factor), over the 4
independent configurations: every spanning fraction is exactly 0 or 1 in each configuration, and the standard deviation of the largest
cluster share is at most 0.005:

| β | factor | `⟨q₀⟩` | `β_eff` | `δ_P` | near-cut share | largest cluster share | spanning | tail fit (slope, `R²`) | verdict |
|---|---|---|---|---|---|---|---|---|---|
| 2.3 | 1 | 0.602 | 2.30 | 0.39 | 0.197 | 0.195 | 1.00 | none (`R²` 0.03) | **persists** |
| 2.3 | 2 | 0.507 | 1.86 | 0.48 | 0.367 | 0.367 | 1.00 | none (0.07) | **persists** |
| 2.3 | 4 | 0.255 | 1.23 | 0.73 | 0.794 | 0.794 | 1.00 | none (0.10) | **persists** |
| 3.5 | 1 | 0.768 | 3.50 | 0.26 | 0.018 | 0.00002 | 0.00 | −0.73, 0.98 | **disappears**, exponential tail |
| 3.5 | 2 | 0.826 | 4.65 | 0.19 | 0.002 | 0.0001 | 0.00 | −2.36, 1.00 | **disappears**, exponential tail |
| 3.5 | 4 | 0.829 | 4.74 | 0.19 | 0.002 | 0.0007 | 0.00 | too few clusters | **disappears** |

**Secondary thresholds** (same verdicts where it matters):
* the fine threshold `δ_P(1)` applied unchanged to the coarse plaquettes: β = 2.3 persists at factors 2 and 4 (near-cut 0.28 and
  0.43); β = 3.5 disappears at both.
* fixed `δ`: at β = 2.3, `δ = 0.05` and `0.1` give isolated clusters with an exponential tail at the fine scale and at factor 2, but
  at factor 4 `δ = 0.05` is already partial (spanning in 53 % of the coarse configurations) and `δ = 0.1` persists; every `δ ≥ 0.2`
  persists at every factor. At β = 3.5 every `δ` up to 0.4 disappears at every factor, with exponential tails where there are enough
  clusters to fit.

**Scored by the plan (section 5):** at β = 2.3 spanning persists at every factor: **the owner's prediction is contradicted at
β = 2.3 for factors 1, 2, 4**. At β = 3.5 spanning is absent at every factor with an exponential size tail: **the prediction is
supported at β = 3.5**.

## 8. Reading (exploratory; not part of any verdict)

* **The two couplings flow in opposite directions under blocking.** At β = 2.3 every blocking step makes the plaquettes rougher
  (`⟨q₀⟩` 0.60, 0.51, 0.26): the blocked theory moves towards strong coupling, the near-cut set grows (20 %, 37 %, 79 %) and spans.
  At β = 3.5 the first steps make the plaquettes smoother (0.77, 0.83, 0.83): at two blocking steps the smoothing of the staple
  average dominates, and the near-cut set thins out. One-loop running would take β = 3.5 to the β = 2.3 region only after about five
  doublings, more than this `16⁴` lattice allows.
* **What spanning at β = 2.3 means.** Near the cut everywhere, at every scale, is the strong-coupling side: there the centre layer's
  sheets are cheap and condense. That is the side where contraction is expected from disorder (the saturation regime, `H_sat`, c8a),
  not from rarity of bad sets. So the coarse test does not find a scale at which β = 2.3 shows "finite bad clusters inside a spanning
  good set"; it finds that β = 2.3 is already on the far side of the window of `DICHOTOMY.md` 3.4, where the bad set of the rarity
  picture is typical and the other mechanism would have to take over. In the owner's words, β = 2.3 at these scales looks like
  saturated (spanned) non-existence rather than isolated non-existence inside spanned existence. This is a reading, not a test of it.
* **Where the crossover between the two pictures lies.** Fine scale: between β = 2.3 (spanning) and 3.5 (isolated), near β ≈ 3.0
  (DICHOTOMY.md 8.6, crude). Under blocking, the β = 2.3 side moves further into spanning and the β = 3.5 side further into isolation,
  so the transition is not a blocking artefact of one scale; it separates two regimes that blocking pushes apart, as one would expect
  if β ≈ 3 (fine) sits near the scale at which the centre layer's sheets change from costly to condensed for this blocking.

## 9. Limits (as fixed, plus what the data showed)

* Four configurations per β; factor 4 is a `4⁴` lattice. The β = 2.3 "persists" at factor 4 is weak evidence by itself, but factors
  1 and 2 persist too, and the near-cut share grows monotonically.
* The plaquette-matched `β_eff` is biased by the smoothing of the blocking (it reads β = 3.5 as 4.7 after two steps); the fixed-`δ`
  scans do not depend on it and give the same verdicts.
* The near-cut criterion is a proxy for the centre-layer flip cost; M1's centre layer is not simulated.
