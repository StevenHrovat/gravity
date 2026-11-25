# R6: the global decoder is local, cluster by cluster (m1-tools, 2026-11-22)

Brief (coordinator, item 1): the global decoder of `CLOSING.md` (nearest closed Z2 layer) equals a local, clustered
one away from dense clusters; make the clustering locality precise, since the counting rests on it. Claim marks as in
`NOTE.md`.

## 0. Result in plain words

**Proved (paper, exact; no "away from dense clusters" needed).** Group the bare flips (plaquettes with `tr U_p < 0`)
into clusters by a deterministic merging rule. Two groups are merged when their distance is at most four times the sum
of their sizes, and this is repeated until nothing merges. Then **every optimal remainder decomposes into one optimal
remainder per cluster, each supported within distance `2|K|` of its cluster `K`**. The tie-break can be chosen
cluster by cluster, which makes the global decoder literally equal to the product of local decoders. The clusters are
deterministic and measurable functions of the flips. A cluster of `n` flips has diameter at most `C n`, and has
probability at most `C^n e^{-(β - c) n}`. So clusters are small with overwhelming probability, and a large cluster is
an ordinary large-field event, paid by its own flips. The counting of `CLOSING.md` 2 used exactly this per-component
inequality (`|τ ∩ σ_α| > |σ_α|/2`), which now holds cluster by cluster.

## 1. Setting

* `τ` = set of flipped plaquettes (a 2-cochain over Z2).
* `σ` = a closed 2-cochain (`dσ = 0`).
* The decoder picks `σ` minimising `|τ + σ|`; ties go first to smaller `|σ|`, then to a fixed rule.
* **Components:** two plaquettes are adjacent if they lie on a common 3-cube; a component of `supp σ` is a connected
  class. Since `(dσ)(c)` only involves the faces of the cube `c`, **each component of a closed cochain is closed**.
* **Distance between plaquette sets:** the length of the shortest chain of adjacent plaquettes joining them.

## 2. The clusters

Start with the components of `supp τ` (same adjacency). Repeatedly merge two groups `K, K'` with
`dist(K, K') ≤ 4(|K| + |K'|)`, where `|K|` is the number of flips in the group. Stop when no pair qualifies. The result
is deterministic: the final partition is the finest one closed under the rule, independent of the merging order.
It is a measurable function of `τ`, and `τ_p = sign tr U_p` is measurable.

## 3. The lemma

**Lemma (clustering locality).** Let `σ*` be an optimal remainder for `τ`. Every component `σ_α` of `σ*` meets at most
one cluster, and satisfies `|τ ∩ σ_α| > |σ_α|/2`. Hence `σ* = Σ_K σ*_K`, where `σ*_K` is an optimal remainder for
`τ_K := τ|_K` alone, supported within distance `|σ*_K| < 2|K|` of `K`.

*Proof.*
* **No component can be dropped or added profitably.** Since `σ*` is optimal and components are closed,
  removing a component `σ_α` gives another closed `σ`. The change in `|τ + σ|` is
  `|σ_α| - 2|τ ∩ σ_α|`, which must be `≥ 0`. Ties go to the smaller `|σ|`, so it must be `> 0`; that is,
  `|τ ∩ σ_α| > |σ_α|/2`. In particular every component meets `τ`.
* **A component meeting several clusters costs more than it gains.** Suppose `σ_α` meets clusters
  `K_1, …, K_m` (`m ≥ 2`). Being connected, it contains a Steiner tree joining them in the plaquette graph, and a
  Steiner tree is at least half a minimal spanning tree of the pairwise distances. In such a spanning tree (`m - 1`
  edges) the edge joining `K_a, K_b` has length `≥ dist(K_a, K_b) > 4(|K_a| + |K_b|)` (the clusters did not merge),
  and every cluster appears in at least one edge. Hence
  `|σ_α| ≥ ½ Σ_edges dist > 2 Σ_{a=1}^m |K_a| ≥ 2 |τ ∩ σ_α|`, contradicting the previous step. So `m ≤ 1`.
* **Optimality splits by cluster.** `|τ + σ*| = Σ_K |τ_K + σ*_K|`, where `σ*_K` collects the components meeting `K`;
  plaquettes of `τ` met by no component count once in either form. So `σ*` is optimal iff each `σ*_K` is optimal for
  `τ_K`, with ties broken cluster by cluster.
* **Support:** a component meeting `K` has `|σ_α| < 2|τ ∩ σ_α| ≤ 2|K|`, and is connected and meets `K`, so it lies
  within distance `2|K|` of `K`. ∎

**The decoder as a product of local decoders.** Define the residual tie-break (iii) cluster by cluster, for example by
a fixed order of plaquettes within each cluster's `2|K|`-neighbourhood. Then the global decoder equals the product of
the per-cluster decoders, each a function of `τ` inside the cluster's `2|K|`-neighbourhood only.

## 4. Sizes and probabilities

* **Diameter:** a cluster of `n` flips is connected under links of length `≤ 4(|K| + |K'|)`, so its diameter is at most
  `Σ` over links `≤ C n²`, and `≤ C n` along any minimal chain (each link is paid by the flips it joins). Its
  decoding neighbourhood has radius `≤ 2n` beyond that.
* **Probability:** at least `n` flips, each costing `β = 4/g_0²` up to `O(1)` normalisation (R7). The number of
  clusters of `n` flips through a given plaquette is at most `C^n` times a polynomial in `n` (the shapes of a connected
  set of `n` points with links of length `≤ C n`). So the probability is `≤ C'^n e^{-β n}`: exponentially small in `n`
  at weak coupling. Large clusters are large-field events; each large-field region of Balaban's representation is
  enlarged by the decoding neighbourhoods of the clusters it contains (radius `≤ 2|K|`). Since each flip pays `β`,
  the enlargement costs at most a constant factor in the entropy.

## 5. Effect

* `CLOSING.md` 2 (the count) and 3 (release) hold with the local decoder; Balaban's factorisation over components of
  the large-field region holds after the enlargement in section 4.
* R6 in `M1-PLAN.md`: **paper** (exact lemma; no density assumption).

## 6. Addendum: the global sector (owner's reading "The decoder is not local, because G0 is not")

**The split, stated.** On the periodic box the Z2 information is the closed remainder `σ*`, which has two parts:
* **(1) local:** the components of `σ*` inside clusters that do not wrap the torus;
* **(2) global:** the homology class `[σ*] ∈ H²(T⁴; Z2)` (6 bits), the remainder's share of the 't Hooft twist sector.

The total twist of the SU(2) configuration is the sum of `[σ*]` and the lift class of the SO(3) field (`w_2` of the
regular SO(3) block field: the ordered product of the canonically lifted plaquettes over each non-contractible plane).

**What is proved, and where.**
1. **The local part has decaying influence.**
   * **Deterministic locality:** the lemma of section 3 holds on the torus as stated; its proof never used that `σ*` is
     exact. Every component of `σ*` lies within distance `2|K|` of its cluster, so the decoder output at a plaquette
     depends only on the flips of the cluster containing its neighbourhood.
   * **Probabilistic locality:** `P(output at q depends on flips at distance ≥ r) ≤ Σ_{n ≥ r/C} C^n e^{-(β - c) n}`,
     which decays exponentially in `r`. This is what E4 and the polymer expansion need: clusters enter Balaban's
     large-field polymers with their decoding neighbourhoods (section 4).
2. **The global part sits only in huge clusters.** A wrapping component of `σ*` has at least `N_min²` plaquettes
   (`N_min` the shortest torus side, in plaquettes). By the lemma it overlaps the real flips on more than half of
   them, so its cluster contains `> N_min²/2` flips and has probability `≤ C^{N_min²} e^{-(β - c) N_min²/2}`. The
   decoder never decides a twist bit from small local data; a non-zero `[σ*]` requires a real wrapping thin sheet.
   Separation from the local part is exact: non-wrapping clusters never produce wrapping components.
3. **The physical twist sector is carried by the SO(3) layer, deterministically.** Thick flux (including the
   flat twisted connections of the twisted box) has `τ = +1`. Its twist is the lift class of the regular SO(3) field,
   which is locally constant on the space of regular fields. Under small-field averaging it is conserved, because the
   coarse plaquettes are the products of the fine ones up to `O(ε²)` (Stokes, [12] (48)-(50)), so the ordered product
   over each non-contractible plane keeps its sign. No decoder decides it; it is a function of the configuration,
   transported by the blocking.
4. **Summing over sectors.** The law at each scale is the sum over the twist sectors of its restrictions. Within a
   sector, Balaban's expansions are local: the fluctuation integrals are small and cannot change the sector, and the
   backgrounds are regular in local gauges, as his analysis requires. Sector-changing events need a wrapping large
   field, whose weight is `≤ exp(-c N_k²/g_k²)` with `N_k` the torus side in scale-`k` cells. The existing tools give
   the cruder `P(twisted) ≤ 1/2` (`su2_flipProb_le_half`) and `Z_tw < Z` (`su2_Ztw_lt_Z`). They are not needed for the
   estimates, but confirm that the twisted sectors never dominate.

**Dense clusters.** They hide global information only when they wrap the torus, which is item 2: suppressed by
`e^{-β N²/2}`. A dense cluster that does not wrap is a local large-field event, as before. So the exception is
local-rare, except for the wrapping case, which is area-suppressed.

**Status:** the split holds. The local part is section 3's lemma (paper, exact, valid on the torus). The global part is
conserved deterministically (paper). Nothing in the local correction depends on the sector choice.

**Update (REVIEW-2 G3, N2):** the probabilistic parts of sections 0, 2, 4 and 6.1 are withdrawn. The merging rule percolates in large volume and its `C^n` shape count is wrong. They are replaced by the conflict-graph Peierls bound of `REVIEW2-RESPONSE.md` 1. Section 3's deterministic lemma stays true (with the doubling-walk form of the Steiner step) but is no longer used. Section 6.4 (sum over twist sectors) is withdrawn: it is not volume-uniform, and nothing uses it.

**Update (REVIEW-3 H2; `REVIEW3-RESPONSE.md` 5):** the decoder is now local by definition. It decodes per connected
union of Balaban's scale-0 `M R_0`-cubes that contain a bare flip, using closed sets inside that union. The text above,
including section 0, describes withdrawn or superseded rules.
