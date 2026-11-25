# The worst-case dichotomy for Yang-Mills (c9a-crossover, 2026-11-23)

Task (coordinator, owner's "Go on all three"): make precise and push the owner's dichotomy (PREP, "Yang-Mills: the worst case is
collapse into CMOS"): for every outside `σ`, either the box contracts (`κ_b(σ) < c₀`), or the non-contracting region is (a)
contained in a sheet attached to the boundary, with weight at most `e^{−c|sheet|}`, or (b) uncontained, with zero weight;
uniformly in `σ`. Start from `WL.md` 10, `INFLUENCE-BAD.md` and M1's mechanisms; every step marked; stop at the first step that
cannot be closed.

Lean: `formal/ProofPhase/Crossover/Dichotomy.lean` (new; 8 theorems, 5 definitions), built in `~/formal-dy` with `build-dy.sh`
(no warnings), axioms `axioms-dy.sh` -> `axioms-dy.log` (each theorem: `propext`, `Classical.choice`, `Quot.sound` only).

Claim marks as in `NOTE.md`.

---

## 0. Verdict in plain words

1. **Part (b) is exact** (Lean). In M1's closed centre layer an "uncontained" sheet, one that ends inside the box, is not in the
   state space: its weight is zero under every law carried by closed configurations. Every sheet piece in a box either closes
   inside or ends on the box boundary (attachment), the flux it must carry there is fixed by the outside alone, and it enters
   and leaves an even number of times.
2. **Part (a) cannot hold uniformly in `σ`** (paper; first unclosable step). The weight bound `e^{−c|sheet|}` needs a lower bound
   on the cost of one sheet plaquette, uniform over every outside and every SO(3) field. In M1's split the cost of flipping one
   plaquette of the centre layer is `β|tr U_p|`, which vanishes where the SO(3) field sits at its cut (`tr U_p = 0`). So the
   uniform cost is zero: along a surface of cut plaquettes a sheet is free, and no `e^{−c|S|}` bound uniform in `σ` exists. This
   is M1's ROUTE-B obstruction (iii) seen from the crossover side.
3. **Two further gaps behind it** (paper, one Lean piece):
   * **Forced sheets.** If the outside carries flux through the box, every box configuration contains a sheet (conditional weight
     1); Peierls can only bound its excess over a minimal spanning surface. Near-degenerate minimal surfaces leave a positional
     tie, which is a non-contracting part with conditional weight of order one. Its smallness can only be annealed: the probability
     that the outside carries such flux, i.e. a 't Hooft-loop (twist) weight, which the strict flip bound gives only as `< 1` with
     no rate, and which has an area law only where the centre layer is ordered (sheets costly).
   * **The window.** Sheets are suppressed (Peierls) when their minimal cost beats the entropy, and they saturate
     (`vortex_saturation`) when their cost oscillation is below the entropy threshold. These regimes are disjoint (Lean,
     `window_gap`), and the crossover must pass through the gap between them: at `L_*` a block-plaquette sheet costs about
     `(π²/2) β_* ≥ 20` nats; at `L₁` the centre half needs less than `0.06` nats (`H_sat`, c8a). In the gap, `E_min` between about
     `0.18` and at least `1.79` nats per plaquette (`d = 4`), neither mechanism gives the weight bound or the contraction.
4. **What survives is a reduction, not a proof.** The dichotomy becomes: for every `σ`, the box contracts, or `σ` (with the box
   configuration) lies in one of two explicit bad events: *flux-carrying outsides with near-degenerate spanning surfaces* (an
   outside-measurable event) or *SO(3) cut along a would-be sheet* (an adjoint large-field event). Both are exactly the bad events
   of the two-level set of `INFLUENCE-BAD.md`, and their smallness is the rarity of conditions B/C (`WL.md` 10). The owner's
   dichotomy does not remove rarity; it names the two places where it is needed.
5. **W2's A3 finding** (the fine field did not take up a twisted block field) suggests that, under the soft constraint, coarse data
   cannot force a sheet into the fine field; only a fine outside can (Lean: the boundary flux is a function of the outside
   configuration). That shrinks the worst case to flux-carrying fine outsides, which is where the forced-sheet gap lives. Whether
   the non-adoption is equilibrium (sheets cost more than the constraint mismatch) or kinetics (no nucleation in 150-300 sweeps) is
   not decided by W2.

---

## 1. Setting and the precise statement

* **Scales and states** (`WL.md` 1): scale-`i` state `X_i = (V_i, τ_i)`, `V_i` the SO(3) field, `τ_i` the closed `ℤ/2` centre
  layer (a plaquette cochain with `δτ_i = 0` on cubes: M1's decoder plus mod-2 Stokes); coarse state `X_{i+1}`; reverse kernel
  `K_i`. A box `b` (a set of scale-`i` cells, plaquette set `R_b`), outside `σ = X_i` off `b`.
* **Contraction:** `κ_b(σ)` is the local column sum of `b` at the outside `σ` (`INFLUENCE-BAD.md` 2); "contracts" means
  `κ_b(σ) < c₀ < 1`.
* **Sheets in the box** (definitions, made exact in Lean): the restriction `τ|_b` (`restrictTo`); its coboundary
  `δ(τ|_b)` on cubes (`cob`). A sheet piece is **attached** if its relative coboundary is nonzero at some boundary cube of `b`
  (`BoundaryCell`: faces in and outside `b`), **closed inside** if it has no relative coboundary, and **uncontained** if its
  relative coboundary is nonzero at an interior cube (`Uncontained`). The **boundary flux** of `σ` is
  `φ(σ) := δ(τ|_b)` restricted to boundary cubes.
* **The dichotomy (D), uniform in `σ`:** for every outside `σ` in the support and every coarse state,
  (i) `κ_b(σ) < c₀`; or
  (ii) every non-contracting part of the box law `q_b^x(σ, ·)` lies in attached sheets, and the conditional weight of an attached
  sheet `S` beyond what `σ` forces is at most `e^{−c|S|}`, with `c` independent of `σ`; or
  (iii) the non-contracting part is uncontained, and then it has weight zero.

## 2. What is exact (Lean, `Crossover/Dichotomy.lean`)

| theorem | statement |
|---|---|
| `cob_restrict_eq_zero_of_interior`, `_of_exterior` | a closed cochain restricted to a region has zero coboundary at every cell whose faces lie all inside, or all outside, the region |
| `boundaryCell_of_cob_restrict` | **attachment:** nonzero relative coboundary only at boundary cells |
| `not_uncontained`, `measure_uncontained` | **part (b):** an uncontained sheet is impossible for a closed layer; under any law carried by closed configurations its event has measure zero |
| `cob_restrict_eq_cob_restrict_compl` | **the flux a box must carry is fixed by the outside:** for a closed cochain, `δ(τ|_b) = δ(τ|_{bᶜ})` |
| `sum_cob_restrict_eq_zero` | **flux in = flux out:** if every plaquette has an even number of cofaces (`2(d − 2)` cubes on the hypercubic lattice), the total relative coboundary vanishes mod 2 |
| `window_gap` | **the two mechanisms are disjoint:** `K' e^{−E_min} < 1` (Peierls, `K' ≥ 2(d − 1)`), `satQ d E < 1` (saturation) and `E_min ≤ E` are contradictory |

These are generic and exact. They use one Yang-Mills input, closedness of the layer, which M1 supplies (paper, M1:
`CLOSING.md`, `DECODER-LOCAL.md`, `UV-TV.md` 37).

**Consequence for (iii)** (Lean plus M1): the uncontained alternative has weight exactly zero, uniformly in `σ`. The owner's
"an uncontained collapse simply ceases to exist" is a theorem about the closed layer.

**Consequence for (ii), structural part** (Lean): every sheet piece in the box is closed inside or attached, and an attached piece's
boundary data is `φ(σ)`, a function of the outside alone. In the owner's terms, "attached to the boundary that carries it"
means its boundary is the outside's flux through `∂b`.

## 3. Part (a): where the weight bound comes from, and where it fails

### 3.1 The weight of one sheet plaquette (paper)

In M1's split (ROUTE-B, `m1-tools/ROUTE-B.md`), the plaquette weight factorises as `exp((β/2) τ_p |tr U_p|)` times SO(3) terms, so
flipping `τ_p` costs `E_p = β |tr U_p|`. For SU(2), `|tr U_p| ∈ [0, 2]`, so `E_p ∈ [0, 2β]`, and `E_p = 0` exactly at the SO(3)
cut (`tr U_p = 0`). Along a sheet `S` the cost is `Σ_{p ∈ S} E_p` (plus the SO(3)-field adjustment, which the effective action at
scale `i` carries).

### 3.2 Uniformity in `σ` fails (first unclosable step; paper)

A bound "conditional weight of an attached sheet `S` beyond the forced part `≤ e^{−c|S|}`, uniform in `σ`" needs
`inf_{σ, V} E_min > log K'` (surface Peierls, `K'` the surface entropy). But `inf E_p = 0`: for outsides and box SO(3) fields with
`tr U_p ≈ 0` on a surface, a sheet along it costs nothing. These configurations are in the support (the SO(3) field is continuous,
and the cut is a codimension-one set). So **(ii) is false uniformly in `σ`** for the bare coupling form, and at every scale whose
effective centre coupling inherits the factor `|tr|` of the adjoint field.

* What is true instead (paper): conditional on the SO(3) field being regular on the would-be sheet, `|tr U_p| ≥ δ` there,
  `E_min ≥ βδ`, and Peierls gives `e^{−(βδ − log K')|S|}` when `βδ > log K'`.
* So the uniform statement reduces to **rarity of the SO(3) cut along surfaces**, an adjoint large-field event (M1's ROUTE-B (iii):
  "typical `τ = −1` plaquettes sit at the SO(3) cut"). That is condition (B)/(C) of `WL.md` 10, for the event "adjoint field at the
  cut", not something the dichotomy supplies.

### 3.3 Forced sheets and ties (paper)

* If `φ(σ) ≠ 0` (the outside carries flux through `∂b`), every box configuration contains an attached sheet spanning `φ(σ)`
  (`sum_cob_restrict_eq_zero` says the flux enters and leaves; closedness forces a spanning surface). Its conditional weight is
  one, not `e^{−c|S|}`. Peierls (where 3.2 allows it) bounds only the excess area over the minimal spanning surfaces.
* If the minimal spanning surfaces are near-degenerate, the box law is multimodal in the sheet's position, and a boundary site
  near the tie moves it: a non-contracting part with conditional weight of order one. This is M1's sub-block vortex mechanism
  (`UV-TV.md` 3) in the closed-layer picture.
* Its smallness can only be **annealed**: the probability under the law that the outside carries flux through `∂b` with minimal
  spanning area `n`. That is a twist ('t Hooft loop) weight:
  * the **strict flip bound** (`Flip/Strict.lean`, `su2_Ztw_lt_Z`) gives `Z_tw < Z` for every `β ≠ 0`: each wrapping sheet has
    relative weight `< 1`, **with no rate**, so no `e^{−c n}`;
  * an **area law for twists** (`e^{−σ_tw n}`) holds where the centre layer is ordered, i.e. sheets costly: the weak end, given 3.2's
    adjoint regularity. The repo's twist area law (`AreaLaw/TwistAreaLaw.lean`) is the Wilson-loop area law at strong coupling, the
    opposite regime, and does not bound sheet weights.

### 3.4 The window (Lean `window_gap`, numbers paper)

* **Sheets suppressed (Peierls):** `K' e^{−E_min} < 1`; with `K' ≥ 2(d − 1) = 6` in `d = 4`, `E_min > log 6 ≈ 1.79` (a crude surface
  entropy `K' ≈ 54`, from 20 edge-neighbours per plaquette, gives `E_min > 4`; crude).
* **Sheets saturated (`vortex_saturation`, c8a):** cost oscillation `E < log(6/5) ≈ 0.18`; the quenched centre Dobrushin form
  `H_sat` asks the block-plaquette flux free energy `J̄_P < 0.0556`.
* **Disjoint** (`window_gap`), and the crossover traverses the gap: `J̄_P(L_*) ≈ (π²/2) β_* ≥ 20` nats (`NOTE.md` 4) down to
  `< 0.06` at `L₁`. In the gap neither mechanism holds: sheets are neither rare enough for Peierls nor cheap enough for the centre
  layer to contract. Where in the crossover the gap sits is the running of the vortex free energy (Tomboulis' programme, `NOTE.md` 4),
  open.

## 4. What the dichotomy becomes

**(D′) (paper, exact as a reformulation):** for every outside `σ` and coarse state, either `κ_b(σ) < c₀`, or one of:
* `F`: `φ(σ) ≠ 0` with a near-degenerate minimal spanning surface (an event of the outside variables: measurable in the scale
  filtration, by `cob_restrict_eq_cob_restrict_compl`);
* `C`: the SO(3) field at the cut along a surface meeting the box (an adjoint large-field event of `(X_i, X_{i+1})` near `b`);
* `U`: uncontained, weight zero (Lean).

`F` and `C` are instances of the coarse-bad and fine-bad sets of `INFLUENCE-BAD.md` 2. The dichotomy names them; their rarity
(conditions B/C, annealed) is still needed, and in the window of 3.4 there is no small parameter for it.

## 5. What W2's A3 finding suggests

* **Observation** (numerical, `w2/SETTLING-RESULT.md`): with a twisted block field (A3) the fine field's alignment with the flipped
  coarse links stayed near zero at `T/2`, against 0.96 elsewhere; the fine field did not form the sheet.
* **Reading** (sketch): the boundary flux a box must carry is a function of the **fine** outside (Lean,
  `cob_restrict_eq_cob_restrict_compl`), not of the block field. Under the soft constraint, a twisted block field is a mismatch the
  fine field can pay for rather than a flux it must carry. So the worst case for the coarse-conditioned box law comes from fine
  outsides with flux (the A6 type: a sheet in the frozen outside attached to the box), the event `F` above, not from twisted
  coarse data. The owner's "contained or ceases to exist" fits: the coarse twist is not contained by any fine boundary and does
  not appear in the fine field.
* **Not decided:** whether this is equilibrium (sheet cost above the constraint mismatch at β = 2.3-3.5 and κ = 16) or kinetics (no
  nucleation within 150-300 sweeps). A CPU test on the saved data cannot tell; a run started from a fine configuration that
  already carries the sheet (does it leave?) would (GPU; not proposed without an OK).
* **Related W2 numbers** (lower bounds only): the A6 boxes, which do carry an attached fine sheet from the outside, showed
  observable-level column sums `R_low_diff = 0.006 ± 0.008` (β = 2.3) and `0.042 ± 0.027` (β = 3.5). The attached sheet did not
  produce a large observable-level influence at these couplings. This refutes nothing and confirms nothing (`RESULT.md`).

## 6. Status table

| step | level |
|---|---|
| attachment of sheet pieces; flux fixed by the outside; parity | Lean |
| (b) uncontained has zero weight | Lean (given M1's closed layer: paper, M1) |
| (a) weight `e^{−c|S|}` uniformly in `σ` | **false** for the bare coupling form (cost vanishes at the SO(3) cut): first unclosable step |
| (a) conditional on adjoint regularity, excess-area Peierls | paper (standard), needs `βδ > log K'` |
| forced sheets: annealed smallness from the strict flip bound | only `< 1`, no rate (Lean bound exists; rate open) |
| the two mechanisms leave a gap that the crossover crosses | Lean (`window_gap`) + paper (numbers) |
| (D′): reduction to the two bad events `F`, `C` with rarity needed | paper |
| A3 reading | sketch; equilibrium vs kinetics open |

## 7. Files

* `formal/ProofPhase/Crossover/Dichotomy.lean` (new).
* `build-dy.sh`, `axioms-dy.sh`, `axioms-dy.log` (new). The build folder `~/formal-dy` is deleted at the end of the round.

---

## 8. The owner's refinement: "uniform over every well-defined outside" (2026-11-23)

The owner, after part (a) failed: "That part a fails is actually expected, since it was too general. The correct statement is
that the weight bound is uniform over every well-defined outside, which in the systems forces it into non-existence.
Everything that does not bound to a well-defined outside is not DMP-complete and can thus be disregarded, since it can not have
existence, which is what the weight is."

Lean: `formal/ProofPhase/Crossover/WellDefined.lean` (new; 3 theorems). Numbers: `w2/nearcut.py` on the saved W2 snapshots
(CPU, 49 s) -> `w2/runs/narrow/nearcut.json`.

### 8.1 The definition

For a box `b`, a threshold `δ ≥ 0` (distance from the SO(3) cut) and a threshold `δ' ≥ 0` (gap from degeneracy):
* `C_δ`: some plaquette of `b` or of its collar (the cells whose state enters `b`'s box law) has `|q₀| < δ`, `q₀ = ½ tr U_p`, so
  that one centre-layer flip there costs `2β|q₀| < 2βδ`;
* `F_δ'`: the outside carries flux through `∂b` (`φ(σ) ≠ 0`, outside-measurable by `cob_restrict_eq_cob_restrict_compl`) and the
  two cheapest spanning surfaces have cost gap `< δ'` (cost `Σ_{p ∈ S} 2β|q₀(p)|`);
* **well-defined at `(δ, δ')`**: `W_{δ,δ'} := (C_δ ∪ F_δ')ᶜ`. It is an event of the outside and the collar, measurable in the scale
  filtration (the subset rule). `C_δ` involves box plaquettes too, so it is a two-level event (fine-bad in the sense of
  `INFLUENCE-BAD.md`), not purely outside-measurable.

At `δ = δ' = 0` the excluded sets are "exactly at the cut" (`q₀ = 0` somewhere) and "an exact tie between spanning surfaces". Both
are **null** (paper: zero sets of nonconstant real-analytic functions of the link variables, under a law with a density), so
disregarding them is free: `FineOneBoxPat` needs its bounds only on a set of full measure.

### 8.2 Null or only small? (exact answer)

**A uniform weight bound over a full-measure set does not exist.**
* **Lean** (`no_uniform_lower_bound_on_full`, `not_exists_full_with_bound`): if a cost has `μ{cost < c} > 0` for every `c > 0`,
  then every set of full measure contains points with cost `< c`, for every `c > 0`; no full-measure set carries a uniform positive
  lower bound.
* **Paper (the Yang-Mills input):** the sheet cost `2β|q₀|` has this property under the Wilson measure and under every conditional
  box law of it. The densities are positive and continuous with respect to Haar measure, the set `{|q₀(p)| < c}` contains a
  nonempty open set, and Haar measure charges open sets (the fact `Flip/Strict.lean` uses for `∫ (Re tr P)² > 0`). The same holds
  for the cost gap of spanning surfaces.
* **So:** the null part of the obstruction (exactly at the cut, exact ties) can be disregarded for free, but what remains still
  contains configurations of arbitrarily small cost on a set of positive measure. Any "well-defined" set on which the weight bound
  is uniform must exclude a set of **positive** weight (`C_δ ∪ F_δ'` with `δ, δ' > 0`), and then the smallness of the excluded set
  is a rarity statement, not a null-set statement.

In the owner's terms: what "cannot have existence" in the proof's sense is what has weight zero, and that is only the exact cut and
the exact ties. Near-cut configurations have positive weight, so they exist in the measure, and the bound has to pay for them.

### 8.3 The bound as a function of the thresholds, and what the excluded set must satisfy (paper)

* **On `W_{δ,δ'}`** every centre-layer flip in the collar costs at least `2βδ`. With a surface entropy `K'` (at least `2(d − 1) = 6`;
  a crude plaquette-animal value about 54), Peierls bounds the excess sheet area beyond the minimal spanning surface:
  `weight(excess area ≥ n | σ) ≤ C (K' e^{−2βδ})^n / (1 − K' e^{−2βδ})`, uniformly on `W_{δ,δ'}`, provided
  **`δ > δ_P := log K' / (2β)`** (paper, `energy_entropy` with `p = e^{−2βδ}`). The positional tie of a forced sheet has relative
  weight at most `e^{−δ'}`, so its contribution to the influence is `≲ |S| e^{−δ'}`, and `δ' ≳ log(|S|/c₀)` makes it negligible
  (sketch).
* **The excluded set must be rare** in the sense of `WL.md` 10.2 (B), (C): cells meeting `C_δ ∪ F_δ'`, merged at the collar range,
  must form subcritical clusters. Crude thresholds per cell from `WL.md` 10.3: about `10⁻⁶` to `10⁻⁵` (percolation-type), `10⁻¹³`
  to `10⁻¹⁰` (min-trick Peierls).

### 8.4 What the excluded set weighs at the W2 couplings (numerical; sampled boxes, 256 snapshots per β)

| | β = 2.3 | β = 3.5 |
|---|---|---|
| `δ_P = log K'/(2β)` for `K' = 6` (`K' = 54`) | 0.39 (0.87) | 0.26 (0.57) |
| fraction of plaquettes with `|q₀| < δ_P` (`K' = 6`) | 0.20 | 0.019 |
| fraction of blocks containing such a plaquette | **1.00** | **0.81** |
| the same at `δ = 0.05` (plaquettes; blocks) | 0.020; 0.85 | 0.0024; 0.20 |
| plaquettes past the cut (`q₀ < 0`) | 0.051 | 0.003 |
| density at the cut, per unit `δ` (two-sided) | 0.41 | 0.048 |

At both couplings the excluded set `C_{δ_P}` is not rare; it is typical: every block at β = 2.3 and four in five at β = 3.5
contain a plaquette closer to the cut than the Peierls threshold allows. It is still common at `δ = 0.05`, far below the
threshold.

**Where it would become rare** (numerical extrapolation from these two points only; crude): the density at the cut falls like
`e^{−1.8 (β − 2.3)}`. With 96 plaquettes per block, the per-block weight of `C_{δ_P}` is about `5 × 10⁻²` at β = 5, `2 × 10⁻⁴` at
β = 8, `4 × 10⁻⁶` at β = 10 and `6 × 10⁻⁷` at β = 11 (`K' = 6`; about twice that for `K' = 54`). It reaches the percolation-type
threshold near fine-lattice **β ≈ 10-11**. So the well-defined set has a rare complement only deep in the weak-coupling regime,
which is where Balaban and M1 already work (their small-field condition is this restriction: near-cut plaquettes are large fields
there, with probability about `e^{−p₀}`), and not in the non-perturbative end of the crossover.

### 8.5 Verdict on the refinement

| step | level |
|---|---|
| "well-defined outside" as an event (`C_δ ∪ F_δ'` excluded), measurable in the scale filtration | paper (definition; flux part outside-measurable by Lean) |
| at `δ = δ' = 0` the excluded set is null and can be disregarded | paper (zero sets of analytic functions under a density) |
| no uniform weight bound over any full-measure set | **Lean** (generic) + paper (SU(2): sublevel sets of the cost have positive measure) |
| uniform bound on `W_{δ,δ'}` with `δ > δ_P = log K'/(2β)`: excess sheet area `≤ (K' e^{−2βδ})^n`, ties `≤ |S| e^{−δ'}` | paper (Peierls), sketch (ties) |
| the excluded set's probability per cell must be below about `10⁻⁶` to `10⁻⁵` | paper (from `WL.md` 10), crude |
| measured at β = 2.3 and 3.5: 100 % and 81 % of blocks excluded | numerical |
| rare only near fine-lattice β ≈ 10-11 | numerical extrapolation (two points), crude |

**In one sentence:** the refinement removes the null part of the obstruction for free, but no "well-defined" set of full measure
carries the uniform bound; any set that does excludes positive weight, whose smallness is the rarity again, and at the
non-perturbative end of the crossover the excluded set is typical, not rare.

**Open:** a different choice of variables in which the obstruction becomes null rather than small. M1's decoder already moves cut
configurations into released large-field regions; a crossover analogue would have to remove near-cut plaquettes from the centre
layer's cost by a change of variables, not by exclusion. No such change of variables is known here.

### 8.6 Zero inherent weight but lossy: attenuation behind a collar instead of rarity (the owner's second answer)

The owner: "It has zero inherent weight, but keeping it outside is lossy, since it generates acts, which, by their taking place,
generate remnants that influence existence through the DB where they were generated." The coordinator's reading to test: the
excluded events need not be rare; it suffices that their effect on the box enters only through the boundary where they sit, as a
boundary term attenuated by the collar (condition A), not as a bulk term.

Numbers: `w2/nearcut_clusters.py` on the saved snapshots (CPU, 67 s) -> `w2/runs/narrow/nearcut_clusters.json`.

**(1) Events outside the box, behind a collar.**
* **Exact:** the box law depends on the outside only through the collar's outer layer (Markov property of the finite-range
  specification). An excluded event located beyond the collar enters the box law only through the collar.
* **Paper:** for an event that is a local field configuration (the SO(3) cut along a surface outside the box, `C` outside), its
  influence on the box law is bounded by Lemma C's inequality (`WL.md` 6.2): `TV ≤ e^{2M} − 1`, `M ≲ Σ_{z ∈ ∂(event)} e^{−m d(z, b)}`,
  i.e. `≲ |∂ event| e^{−m w}` for a collar of width `w`, **provided the collar decorrelates (condition A, conditional mass `m > 0`)**.
  So for `C` outside the box, rarity is replaced by attenuation, as the reading says. Condition A itself is open (not measured in
  W2; the single-link proxy saturates, which says nothing about the multi-link mass `m`).
* **Exact exception: flux.** For `F` (an outside that carries flux through `∂b`), the flux the box must carry equals the outside's
  coboundary (Lean, `cob_restrict_eq_cob_restrict_compl`) and enters and leaves the box (Lean, `sum_cob_restrict_eq_zero`). This is a
  conservation law: no collar screens it. If the outside's sheet crosses the box, the box carries a sheet whatever the collar does;
  only the details of where it enters are attenuated. If the outside's sheet does not cross the box (`φ(σ) = 0` on `∂b`), it is an
  ordinary local event behind the collar and is attenuated. In the owner's words: the remnant of a flux act is carried through the
  DB intact, not worn down.

**(2) The same events inside the box: the residue.**
* **Exact (by (1)):** what is not attenuated is (i) crossing flux, the forced sheet inside the box with its positional ties
  (`F` inside), and (ii) cut surfaces inside the box (`C` inside). That is exactly the forced-sheet and cut residue of sections
  3.2-3.3, now restricted to the box.
* **How large (numerical, sampled boxes; near-cut = `|q₀| < δ`; plaquettes connected when faces of a common cube, the adjacency of a
  dual sheet):**

| | β = 2.3, `δ = δ_P = 0.39` | β = 2.3, `δ = 0.1` | β = 3.5, `δ = δ_P = 0.26` | β = 3.5, `δ = 0.1` |
|---|---|---|---|---|
| near-cut plaquettes | 19.9 % | 4.1 % | 1.9 % | 0.5 % |
| largest near-cut cluster (fraction of box plaquettes) | **18.7 %** | 0.12 % | **0.07 %** (about 5 plaquettes) | 0.03 % |
| snapshots with a near-cut cluster spanning the box | **100 %** | 0.4 % | **0 %** | 0 % |

* **Reading:** with about 20 cube-neighbours per plaquette the near-cut set percolates above roughly 5 % density (crude: `1/19`). At
  β = 2.3 it is far above (one spanning network along which a sheet is nearly free): the cut residue fills the box. At β = 3.5 it is
  far below (isolated clusters of a few plaquettes): a sheet across the box must cross regular plaquettes, each costing at least
  `2βδ_P = log 6`, so the cut residue is small there. Interpolating the two points (crude), the near-cut set at the Peierls threshold
  crosses the percolation density near **β ≈ 3.0**. The single-plaquette frequency of section 8.4 (81 % of blocks at β = 3.5) overstated the
  residue: what matters for sheets is the connectivity of the near-cut set, not its presence.
* **Not measured:** the crossing-flux residue (it needs the centre layer of M1's split; W2 simulated SU(2) links). Its weight per box
  is a twist weight: small where the centre layer is ordered, of order one where sheets condense.

**(3) The reformulated dichotomy (D″) (paper):** for every outside `σ` and coarse state, either
* the box contracts; or
* the obstruction lies **behind the collar** and is local (`C` outside, `F` without crossing): its effect is a boundary term
  `≲ |∂| e^{−m w}`, attenuated, needing **condition A** only (rarity not needed); or
* the obstruction is **inside the box**: crossing flux with near-degenerate spanning surfaces, or a near-cut surface inside the box.
  This residue still needs rarity, but now only for events inside one box, not for events anywhere within a merge range, and for
  the cut part the relevant event is **percolation of the near-cut set inside the box**, not the presence of near-cut plaquettes.

**Level of (D″):** the split into behind-collar and inside is exact (Markov property, flux conservation); the attenuation bound is
paper given condition A (open); the residue's smallness is numerical at two couplings: **small at β = 3.5, not small at β = 2.3**,
for the cut part; unmeasured for the flux part.

**What this changes:** the owner's reading removes rarity for the obstructions that sit behind a collar, which is most of the
excluded set at both couplings (near-cut plaquettes are spread through the lattice). Rarity remains for two inside events, and the
measured cut part of it holds at β = 3.5 and fails at β = 2.3. Together with 8.4 this places the point where the inside residue stops
being small inside the W2 window, near β ≈ 3.0 (crude), with condition A as the remaining open input for everything behind the
collar.
