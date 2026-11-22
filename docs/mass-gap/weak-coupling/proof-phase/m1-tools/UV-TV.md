# Lemma UV-TV (i): the Dobrushin route (m1-tools, 2026-11-22)

> **Status (part 2, sections 7-13 below):** Lemma UV-TV (i) is restated in averaged form (section 8). The good-boundary Theorem A is restated in site-level Dobrushin-Shlosman coupling form, with bad clusters as nodes (section 9, paper sketch). Section 3.1's independent-percolation hypothesis is withdrawn. Next: the multi-scale crossing estimate (section 12).

> **Status (part 3, sections 14-20):** the reviewers' dynamic fix of Theorem A_good saturates inside bad clusters (section 15). The repair is static: composite boxes (cluster plus good collar) with Lemma C, Dobrushin-Shlosman per `ω` worst case over the support, then an average over `ω` (section 16, paper sketch). H2 is quenched in the coarse field (17). Section 12 has not started and waits on the reviewers' check of section 16.

> **Status (part 4, section 21):** the merging cascade is repaired by a fixed merge range per scale (collar `w_j` set by the scale), localisation around `B` with truncation of scale-`j`-born clusters at `n_j = C log|Λ''_j|/log(1/η_j)`, and isolation of inherited regions at their birth scale (paper sketch). The fixable items and section 12 follow.

> **Status (part 5, section 22 and section 12 continued):** the fixable items are written: links as edges; Lemma C without the interface factor; constant multiplicity with overlapping good boxes; coverage by rounding; the coupling-form Dobrushin-Shlosman theorem (no off-support hybrids); the cut-off check. Section 12 has started with the pointwise fibre normalisation, checked up to one reading (12.1).

Brief (coordinator):
* Attack Lemma UV-TV (i) of `REVIEW3-RESPONSE.md` 13.4 by the Dobrushin route first, reusing the one-box Lean layer
  (`formal/ProofPhase/OneBox`, `OneBox2`). Finite-range decomposition only if that fails.
* Cover the large-field per-scale normalisation at every scale, and say whether the Z2 layer needs anything beyond
  the standard low-temperature expansion.
* Stop at the first real obstruction.

The owner's reading ("CMOS reading of Lemma UV-TV", `../../PREP.md`) is the target statement: given the coarse state
near `B`, the fine layout on `B` is realised the same way whatever the coarse state does far away ("redeploy the
cluster"). Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **The Dobrushin route, as stated, meets a real obstruction, and I stop here as asked.** The one-box Lean theorem
   (`abs_cov_le_of_oneBox`, via `IsInfluenceBoundOn`) needs the influence bound for **every** boundary configuration
   `σ`. The fine-given-coarse kernel fails that, for two reasons:
   * **(a) Low temperature in total variation.**
     * A single fine site is a narrow Gaussian-like variable, of width `g_j` in its own units.
     * A change of a neighbouring site moves its conditional mean by an amount of the size of the neighbour's change,
       up to `ε_j = g_j p(g_j)` in small field, so the total-variation influence is `O(p(g_j))`, not small.
     * Single-site Dobrushin fails.
     * A block version can still work on **small-field** boundaries (section 2): the influence of one boundary site
       on a box is about `(log p(g_j))^d`, so boxes of side `≫ (log p(g_j))^d` give the one-box sum below `γ |Λ₀|`.
   * **(b) Worst-case boundaries.**
     * The sup over `σ` includes large-field boundary configurations.
     * Among them are boundaries that force a sub-block vortex or monopole structure through the box, whose position
       inside the box the coarse data do not fix.
     * One boundary site can then shift that structure across the whole box: an influence of the order of the box
       volume. **The one-box sum fails for every box size.**
2. **What would repair it: a good/bad-box version of Theorem A.**
   * Influence bounds are needed only on **good** boundaries (small field near the box), and the **bad** boxes
     (Balaban's large-field regions of the conditional measure) are rare.
   * This is the Dobrushin–Shlosman argument combined with disagreement percolation (van den Berg–Maes type): a
     disagreement either crosses good boxes, where it contracts, or uses bad boxes, which costs their rarity.
   * It is new analysis, of moderate size, and it does **not** follow from the current Lean layer, whose hypotheses
     quantify over all `σ`.
3. **Finite-range decomposition (route 2) does not remove (b).** It addresses the Gaussian part (a), which the block
   version already handles. The large-field part needs rarity in every route.
4. **Large-field part, per-scale normalisation (moderate risk).**
   * The rarity of bad boxes given the coarse field is the scale-`j` version of section 7's crossing estimate, with
     `V_{j+1}` as the fixed top variable.
   * Its normalisation is the same adaptation as at scale `K` (the top variables paid from the large-field budget, as
     in Balaban's next step), with scale-uniform constants.
   * No new difficulty beyond that adaptation, but it is needed at every `j < ℓ` (section 3).
5. **Z2 layer: nothing beyond the standard low-temperature expansion**, plus two local inputs: the per-component
   decoder constraint, and the fact that weak Z2 couplings occur only on SO(3) bad boxes (section 4).
6. **Status.** Lemma UV-TV (i) stays **open**, now reduced to one generic theorem (Theorem A on good boundaries, with
   bad boxes as a rare percolation) and two inputs, both scoped below. No Lean was written: the generic theorem's form
   is the decision to take first.

## 1. The object

* At scale `j` the reverse kernel `K_j(dV_j | V_{j+1})` is the fibre measure of `ρ_j`: `ρ_j` restricted to
  `{block(V_j) = V_{j+1}}`, normalised.
* The fine-given-coarse law on `B` is the composition of these kernels from scale `ℓ` down to `0`
  (`REVIEW3-RESPONSE.md` 13.4).
* Lemma UV-TV (i) asks for a coupling of `K_j(· | V)` and `K_j(· | V')`, with `V = V'` on the `r`-neighbourhood of `B`,
  that agrees on `B` except with probability `≤ C|B| e^{−κ r}`.

In Dobrushin–Shlosman form this is: the measure `K_j(· | V_{j+1})` on scale-`j` variables, with a block
specification `q_J^σ` (the conditional law of a box `J` given the rest, `σ`), has influences `k_J(z)` with
`Σ_{z ∉ J} k_J(z) e^{λ E(z)} ≤ γ |J|`, `γ < 1`. Then `abs_cov_le_of_oneBox` gives covariance decay for bounded
measurable observables, and the same contraction gives the boundary-influence bound. `IsInfluenceBound(On)` asks:
`|∫F dq^σ − ∫F dq^{σ^{z→s}}| ≤ k_J(z) · L` for all `σ`, `s` and all `F` with per-site oscillation `≤ L`. Here
`k_J(z)` is the Hamming-Wasserstein distance between the two box laws.

## 2. Small-field boundaries: the block condition holds

**Setting.**
* Let the box `J` be a cube of side `ℓ_B` in scale-`j` units, and let `σ` be small field on the `2ℓ_B`-neighbourhood of
  `J`.
* There the kernel is Balaban's fluctuation measure: Gaussian with covariance `g_j² Γ`, where `Γ` is massive in
  scale-`j` units (the block constraint, Poincaré, `POINCARE.md`), times small analytic local terms ([III] (2.23)-(2.42)).

**One boundary site.**
* A change of `σ_z` within the small-field set moves the conditional mean of `J`'s variables by
  `Δ_y ≤ C ε_j e^{−m|y − z|}`, with `m` the fluctuation mass in scale-`j` units ([13] decay of the propagators,
  [15] (190)).
* A coupling of the two conditional laws (shift coupling for the Gaussian part, perturbation for the analytic terms)
  makes site `y` differ with probability `≤ min(1, C Δ_y/g_j) = min(1, C p(g_j) e^{−m|y−z|})`.
* Summed over `y`:
  `k_J(z) ≤ C (log p(g_j)/m)^d + C Σ_{y} p(g_j) e^{−m|y−z|} 1{|y − z| > log p/m} ≤ C' (log p(g_j)/m)^d`.
* **(a), the single-site version:** `k_{{y}}(z) ≈ min(1, C p(g_j))`, which is not small, so the single-site Dobrushin
  sum diverges with `p(g)`.

**The one-box sum.**
* Only sites `z` within `O(log p/m)` of `J`'s boundary have a non-negligible influence. So
  `Σ_{z ∉ J} k_J(z) e^{λ Ê(z)} ≤ C ℓ_B^{d−1} (log p/m)^{d+1} e^{λ C log p/m}`.
* This is `≤ γ ℓ_B^d` once `ℓ_B ≥ C (log p(g_j)/m)^{d+1}/γ` and `λ ≤ m/(C log p)`.
* `p(g_j)` is polylog in `g_j^{-1}`, so `log p` is `O(log log g_j^{-1})`. The boxes are only slightly larger than one
  scale-`j` cube, and the decay rate is `λ ≈ m/log log g_j^{-1}` per scale-`j` unit. That is enough for the composition
  of 13.4 (ii): at scale `ℓ` the bound is `e^{−c t/(ℓ log log g_ℓ^{-1})} → 0`.
* **Status: paper sketch.** The shift coupling with the analytic perturbation, and the uniformity over small-field `σ`,
  need writing. They use only Balaban's small-field bounds, with no large-field input.

## 3. Worst-case boundaries: the obstruction

* `IsInfluenceBound(On)` quantifies over **all** `σ`, including boundaries that are large field next to `J`. The
  conditional law of `J` given such a `σ` need not be Gaussian-like anywhere in `J`.
* **Example (sub-block vortex).**
  * The coarse data `V_{j+1}` fix only block averages. A boundary `σ` can carry a non-trivial SO(3) twist (or, with
    the Z2 layer, a flux) through `J`.
  * Then every configuration of `J` consistent with `σ` and the coarse data has a deep structure (a vortex sheet or
    monopole line) crossing `J`.
  * The coarse data do not fix its position inside `J`, so the conditional law spreads it over `J`.
  * Changing one boundary site `z` near where the structure meets `∂J` changes the distribution of that position, and
    with it the configuration on a positive fraction of `J`.
  * So `k_J(z)` can be of order `|J|`. One such `z` already breaks `Σ_z k_J(z) ≤ γ|J|`, for every `ℓ_B`.
* **This is a real obstruction to the route as stated:** the Lean theorem's hypothesis cannot be verified for this
  kernel.
* The obstruction is about **worst-case** boundaries only. Under the measure such boundaries are Balaban large-field
  regions, rare at every scale (`≤ e^{−c p0}` per cube, section 3.2).

### 3.1 What would repair it

**Theorem A on good boundaries (generic, new).**
* Let a set `𝒢_J` of good boundaries be given for each box `J`, with the influence bound and the one-box sum holding
  for `σ ∈ 𝒢_J`.
* Let the bad set `𝔅 := {(J, σ): σ ∉ 𝒢_J}` be dominated by a subcritical independent percolation of boxes: probability
  `≤ η` per box, `η` small, with exponential decay of connected clusters.
* Then for bounded measurable `F` on `A` and `G` on `S` at distance `R`:
  `|Cov(F, G)| ≤ C (|A| + |S|) ‖F‖ ‖G‖ (e^{−λ R} + (C η)^{R/ℓ_B})`, and the boundary-influence analogue holds.

**Proof idea.**
* This is disagreement percolation: couple the two laws box by box.
* A disagreement moves from box to box either through a good box, where it contracts by the one-box sum, or through a
  bad box, which happens with probability `≤ η`.
* Paths of length `R/ℓ_B` cost `(γ + Cη)^{R/ℓ_B}`.
* This is close to van den Berg–Maes, "Disagreement percolation in the study of Markov fields" (1994), and to the
  Dobrushin–Shlosman constructive criteria, but it has to be written with gauge-invariant test functions (the
  admissible class of `Restricted.lean`).
* **In Lean:** a new generic layer next to `OneBox/Restricted.lean` (`theoremA_on` with a good-set hypothesis and a
  domination hypothesis). Moderate size. It does not follow from the present theorem, whose iteration of block
  averages uses the influence bound at every `σ`.

### 3.2 The input it needs: bad boxes are rare given the coarse field (the large-field part)

* **The bad event** for a box `J` at scale `j`: the fine field near `J` is not small field. That is a large-field
  region of the scale-`j` representation, given the fixed coarse `V_{j+1}`.
* **Its conditional probability** is the ratio (forced large-field polymer) to (all), at fixed top variable `V_{j+1}`.
  This is section 7's crossing estimate at scale `j` instead of `K`:
  `P(bad near J | V_{j+1}) ≤ e^{−2p0(g_j)} e^{−(κ − C) d_j}`, with the normalisation of the scale-`j` variables on the
  region paid from the large-field budget, as in Balaban's step `j → j + 1` (13.3).
* **At every scale:** the constants of the induction are scale-uniform (`S1-INDUCTION.md` 1), and the adaptation is the
  same at each `j`. So the estimate holds uniformly in `j`, given the adaptation once.
* **One point to check.** The conditional probability is given `V_{j+1}`, and `V_{j+1}` may itself be large near `J`
  (a coarse large-field region). There the bad event is certain. Those boxes are bad by fiat, and their rarity comes
  from the coarse law, one scale up. The domination by independent percolation then needs Balaban's polymer bounds to
  give a product-type bound over boxes: true for his activities (polymer expansion with `e^{−κ d}`), given the
  adaptation.
* **Status:** unchecked adaptation, the same as R10's at scale `K`. Moderate risk, as stated in 13.4. No new
  difficulty found beyond it.

## 4. The Z2 layer

* Given the bare SO(3) field, `τ` is a Z2 lattice gauge theory with couplings `J_p = (β/2)|tr U_p| ∈ [0, β]`
  (`REVIEW3-RESPONSE.md` 1.1). The reference measure for the lift signs `s_b` is a **product** measure, so the
  standard low-temperature polymer expansion admits measurable observables: closed flip sets, activity
  `Π e^{−2J_p}`.
* **Good boxes** (SO(3) small field): `J_p ≥ β(1 − O(ε²))`. The expansion converges for `β ≥ β_min`. Total-variation
  locality and covariance decay for bounded measurable functions of `τ` are standard, with the Peierls bound of
  `REVIEW2-RESPONSE.md` 1.
* **Bad boxes** (SO(3) large field): `J_p` can be near 0 at the SO(3) cut, so Z2 is not controlled there. Those boxes
  are already bad for the SO(3) part, so they need no separate treatment.
* **The conditioning on `τ'`** (labels): the decoder is local per flip-cube component (section 5). Given `τ'`, the
  constraint is a product over components, so it enters as local factors of the polymer expansion.
* **Answer:** nothing beyond the standard low-temperature expansion, plus the per-component decoder constraint and the
  bad-box overlap with SO(3).

## 5. Why route 2 (finite-range decomposition) does not remove the obstruction

* A finite-range decomposition (Brydges–Guadagni–Mitter, Bauerschmidt) writes the fluctuation Gaussian as a sum of
  finite-range-dependent fields plus an exponentially small remainder. That helps with (a): it gives a product-like
  reference over blocks, and the total-variation remainder is small.
* (a) is already handled by the block version (section 2). (b) is about worst-case boundaries in the large-field part,
  which no Gaussian decomposition touches.
* Route 2 would need the same good/bad structure and the same rarity input.

## 6. Status and the decision to take

| part | level |
|---|---|
| single-site Dobrushin (TV) | **fails** (a): influence `≈ p(g_j)`, not small |
| block version on small-field boundaries | **paper sketch**: one-box sum `≤ γ` for boxes of side `≫ (log p(g_j))^{d+1}`, rate `m/log log g^{-1}` |
| one-box theorem with sup over all `σ` (the Lean hypothesis) | **fails** (b): sub-block deep structures give influences of order `|J|` |
| Theorem A on good boundaries + bad-box percolation | **new, open**: generic, moderate size, Lean-able next to `Restricted.lean` |
| rarity of bad boxes given the coarse field, every scale | **unchecked adaptation**, the same as R10's normalisation |
| Z2 layer | standard low-temperature expansion plus local inputs |

**Decision for the coordinator or the owner.** Proceed with the good-boundary Theorem A, first on paper with its exact
hypotheses, then in Lean as a generic layer next to `OneBox/Restricted.lean`; or try another route. I recommend the
first: it reuses the one-box machinery in spirit and isolates the large-field input as a separate rarity hypothesis.

# Part 2 (2026-11-22): the corrected route, after REVIEW-2 (fourth follow-up) and REVIEW-3 (follow-up 3)

Brief:
* restate UV-TV (i) in averaged form;
* write the good-boundary Theorem A on paper, with exact hypotheses;
* then the multi-scale crossing estimate (section 12, next round);
* check the owner's reading "Inward and outward reach" (unimodality after matching the discrete data; irreducibility
  of the fibre).

Report after Theorem A. Corrections to part 1, accepted:
* (b)'s sliding-sheet example does not give influence `~ |J|`. The obstruction is the **absence of control** on
  large-field boundaries: Balaban gives only upper bounds there, and the box law may be multimodal (REVIEW-3).
* (a)'s rate is `λ ≈ 1/ℓ_B`, about `(m/log p)^{d+1}`, not `m/log log g^{-1}`.
* Boxes are unions of `L`-blocks (the fibre constraint).
* Independent-percolation domination is withdrawn: badness is inherited.
* UV-TV (i) as stated in 13.4 is false uniformly in the coarse field.

## 7. Result of part 2 in plain words

1. **UV-TV (i), averaged** (section 8).
   * The statement is about a coupled pair of coarse states, each distributed by the law. In (A) the comparison state
     is a resample of the far coarse data from the law; in (B) it is the same block state with fresh randomness on the
     mirror side.
   * The fine states can be coupled so that the expected number of disagreeing sites on `B` is bounded by an annealed
     chain sum from the source region to `B`. Good boxes carry Dobrushin-Shlosman influence weights; clusters of boxes
     that are bad in either copy (Balaban's pattern indices at that scale, or coarse bad boxes) are single nodes.
2. **Theorem A_good** (section 9) is stated with exact hypotheses H0-H4:
   * H0, finite range and specification agreement given the discrete data;
   * H1, a mixture-first pattern coupling;
   * H2, an annealed Peierls bound per copy, including long links;
   * H3, a good-box influence bound in Hamming-Wasserstein form with the one-box sum `≤ γ|Λ_0|`, required only on boxes
     that the pattern makes small field;
   * H4, smallness of the bad gas.

   Its conclusion is `E[#disagreeing sites on B] ≤ C|B| e^{−λ dist(B, D)}`.
   * **A first draft failed:** a cell-by-cell disagreement percolation cannot close for continuous fields (an adjacent
     disagreement transmits with probability close to 1).
   * **The form that works** counts expected disagreeing sites, as Dobrushin-Shlosman does, through a coupled block
     dynamics with bad clusters as nodes.
   * Proof at paper-sketch level.
3. **Where each hypothesis comes from in M1** (section 10).
   * H0 and the Markov property: from Balaban's localised action, with the long tails turned into positive "long links"
     by a positive decomposition. Paper.
   * H3: from the small-field nested coupling, far to near, which realises the Hamming-Wasserstein influence
     `k_J(z) ≲ (log p(g_j)/m)^d`. It is possible because pattern-goodness forces small field on the box's
     surroundings. The one-box sum holds for boxes of side `≫ (log p/m)^{d+1}`, with rate `λ ≈ 1/ℓ_B` (REVIEW-3's
     correction). Paper sketch with the estimates.
   * H1 and H2: properties of Balaban's pattern gas given the coarse field. They are inputs for section 12, the
     multi-scale crossing estimate, with the pointwise fibre normalisation as the key adaptation.
4. **The owner's reading** (section 11).
   * Given matched discrete data (patterns, labels, Z2 excitations, long links), the remaining law on good boxes is
     small field and **unimodal**: a positive-definite Gaussian on the linearised fibre times `exp` of small analytic
     terms, with a unique background ([15]).
   * The multimodality REVIEW-3 found lives on large-field backgrounds, so in the discrete data. **Confirmed**, on good
     boxes.
   * Irreducibility: Wilson weights are strictly positive (`stepK_pos`), so every box law has a Doeblin floor. Its
     constant is `e^{−C β_0 L^{dj} |J|}`, so it rules out frozen box laws and nothing more.
5. **No obstruction so far; one correction of my own.** The first proof of Theorem A_good, cell by cell, fails for
   continuous fields. The site-level form replaces it, at paper-sketch level. What remains is
   section 12: H1 and H2 for Balaban's patterns as conditional statements given the coarse field, and the multi-scale
   composition.

## 8. UV-TV (i), averaged

**Objects at scale `j`.**
* **State and kernel.** `X_j = (V_j, τ'_j)` plus noise. `K_j(dX_j | X_{j+1})` is the fibre measure of `ρ_j`.
* **Positive mixture.** `ρ_j = Σ_ω ρ^ω_j` (Balaban's representation at scale `j`, before any Mayer expansion; long tails
  decomposed into links, section 10.1). So `K_j(· | X_{j+1}) = Σ_ω w_ω(X_{j+1}) K^ω_j(· | X_{j+1})`, with
  `w_ω(y) := ∫_{fibre(y)} ρ^ω_j / ∫_{fibre(y)} ρ_j`.
* **`ω` collects the discrete data:**
  * the domain history `(Ω_i, Λ_i, Z_i)_{i ≤ j}`;
  * unreleased regions (including regions born at finer scales and not yet released);
  * released labels and unreleased label patterns;
  * Z2 low-temperature excitations;
  * long links.
* **Boxes.** Unions of `L`-blocks of side `ℓ_B` (in scale-`j` units). `Bad_j(ω)` is the set of boxes meeting a
  large-field domain, an unreleased region, a labelled domain or a Z2 excitation of `ω`, or the coarse bad set
  `Bad^c(X_{j+1})` (boxes whose block field `X_{j+1}` is not small field). Both are attached to each term.

**Statement (UV-TV (i)_avg, one scale).**
* Let `(X_{j+1}, X'_{j+1})` be a coupled pair whose marginals are both the law of `X_{j+1}`, or both the law
  conditioned on a common σ-algebra `𝓗`. Let them agree outside a source set `D_{j+1}`.
* Then `K_j(· | X_{j+1})` and `K_j(· | X'_{j+1})` can be coupled, measurably in the pair, so that the expected number
  of sites of `B` where `X_j ≠ X'_j` (modulo gauge) is at most a sum over chains from `D_j` (the image of `D_{j+1}`,
  enlarged by one box) to `B`. Each link of a chain is one of:
  * a cluster of boxes bad in either copy (`Bad_j(ω)` or `Bad_j(ω')`), a single node;
  * a good box, carrying the influence weight of H3;
  * a long link of either copy.
* That sum, **averaged over the pair**, is bounded as in Theorem A_good, with H2 taken under the law (annealed).

**The tower** (for (A) and (B) of 13.4). Iterate from scale `ℓ` down to 0. The source at scale `j` is the disagreement
set inherited from scale `j + 1`. The failure event is a **multi-scale chain**: bad clusters and good-box influences at
scale `j`, joined to coarser ones. Its probability is the multi-scale crossing estimate of section 12. It is not a
union bound over scales, since bad regions of coarser scales are inherited.

**Comparison states.**
* **(A):** `X'_ℓ` = the block state near `F` (the σ-algebra `𝓗`) kept, with the far block data **resampled** from the
  law given `𝓗`. Both copies are then law-distributed given `𝓗`, so the annealed bounds apply.
* **(B):** one block state, two runs of the reverse kernels with shared randomness except fresh randomness in the
  mirror region. Both runs are law-distributed given `𝓕_ℓ`.
* An arbitrary `X'` is not allowed: it would bring back the uniformity over coarse data.

## 9. Theorem A_good (generic, exact hypotheses)

**A first draft failed.** It used a cell-by-cell disagreement percolation (van den Berg-Maes style). For continuous
fields that cannot close: a cell next to a disagreeing cell disagrees with probability close to 1, because the field
difference at the shared face is `O(ε)` against a width `g`. A buffer condition on whole cells cannot be used by a
cell-by-cell exploration. The form below counts **expected disagreeing sites** (Dobrushin-Shlosman influences), so a
disagreement at a face costs only the few sites near it. It treats bad clusters as single nodes. This is the coupling
(dual) form of the one-box iteration, with good/bad added.

**Data.**
* A finite set `Λ` of sites (scale-`j` bonds), with a configuration space `Ω = Π_x S_x` (measurable) and a distance.
* Boxes `J`: unions of `L`-blocks, side `ℓ_B`, forming a box family as in `IsBoxFamily`, with coverage `|Λ_0|`.
* Two probability measures, as positive mixtures over discrete data: `μ = Σ_ω w_ω μ_ω`, `μ' = Σ_ω w'_ω μ'_ω`.
* For each `ω`: a bad set `Bad(ω)`, a union of boxes, and long links `Lk(ω)`.
* A source set `D ⊂ Λ`.

**Hypotheses.**
* **(H0) Range and agreement.** Given `ω`, the specification of `μ_ω` on a box `J` (the law of `J` given the rest)
  depends only on the configuration within range `r_int ≤ ℓ_B` of `J`, plus the endpoints of links of `ω` meeting
  `J`. If `ω = ω'` near `J` and `J` is at distance `> r_int` from `D`, the two specifications on `J` coincide.
* **(H1) Pattern coupling.** There is a coupling `Π` of `(w, w')` under which `ω = ω'` on every box not joined to
  `N(D)` by a chain through `Bad(ω) ∪ Bad(ω')` and links.
* **(H2) Annealed Peierls, per copy.** For every finite set `A` of boxes and set `ℓ` of links:
  `w(A ⊂ Bad(ω), ℓ ⊂ Lk(ω)) ≤ η^{|A|} Π_{ℓ} e^{−κ s}`, and the same for `w'`.
* **(H3) Good-box influence (Hamming-Wasserstein).** Call `J` good for `(ω, ω')` if the boxes meeting the
  `r_int`-neighbourhood of `J` are outside `Bad(ω) ∪ Bad(ω')`, carry no links, and `ω = ω'` there. For a good `J` and
  every pair of outside configurations `σ, σ'` in the supports (small field near `J`, in the common gauge of `ω`) that
  differ on a set `Z`, the two box laws admit a coupling with
  `E[#{y ∈ J : Y_y ≠ Y'_y}] ≤ Σ_{z ∈ Z} k_J(z)`.
  The `k_J(z)` satisfy the one-box sum `Σ_{z ∉ J} k_J(z) e^{λ Ê_J(z)} ≤ γ |Λ_0|`, with `γ < 1` and `Ê` as in
  `OneBoxSum`.
  * For a single site `z` this is a statement about boundaries in the support.
  * For several sites it follows by changing one site at a time. Every hybrid boundary is again small field with a
    constant `C` (both are within `ε` of the same background in the same gauge), so H3 is required for boundaries
    within `C ε` (pair-good, as REVIEW-3 asks).
* **(H4) Smallness of the bad gas.** `C_d η^{1/2} e^{λ C ℓ_B} ≤ ½` and `Σ_s #{boxes at distance s} e^{−(κ/2 − λ) s} ≤ C_L`.

**Conclusion.** There is a coupling of `μ` and `μ'` with
`E[#{x ∈ B : Y_x ≠ Y'_x}] ≤ C |B| (1 + C_L) e^{−λ dist(B, D)}`,
and hence `P(Y ≠ Y' on B) ≤` the same bound.

**Proof.**
1. **Mixture first.** Draw `(ω, ω')` from `Π`, then couple `μ_ω` and `μ'_{ω'}` as below. A mixture of couplings has
   the right marginals.
2. **Coupled block dynamics.**
   * For fixed `(ω, ω')`, run the random-sequential block heat bath for each copy: pick a box uniformly, resample it
     from the copy's specification. `μ_ω` and `μ'_{ω'}` are stationary.
   * Couple the two updates of a box `J`: on good `J`, by the coupling of H3; on bad `J`, near `D`, or at link
     endpoints, arbitrarily.
   * The state space is compact (SO(3), Z2, noise) and the kernels are Feller on the support, so the coupled chain has
     a stationary measure. Both of its marginals are stationary for the single-copy chains, which are uniquely ergodic
     (Doeblin floor, section 11). So the marginals are `μ_ω` and `μ'_{ω'}`.
3. **The Dobrushin-Shlosman inequality in stationarity.** Let `d(x) := P(Y_x ≠ Y'_x)` under the stationary coupling.
   Stationarity of one update gives:
   * if every box containing `x` is good: `c(x) d(x) ≤ Σ_{J ∋ x} Σ_{z ∉ J} k_J(z, x) d(z)`, where `c(x)` is the
     coverage and `k_J(z, x)` splits `k_J(z)` by site;
   * if `x` lies in a bad box, near `D`, or at a link endpoint: `d(x) ≤ 1`.
4. **Bad clusters as nodes.**
   * Let `𝒦` be a connected component of `Bad(ω) ∪ Bad(ω') ∪ link endpoints`, enlarged by `r_int`. Inside it, use only
     `d ≤ 1`.
   * Its outgoing influence is at most `C ℓ_B^d |𝒦|`: the sites of `𝒦` within `r_int` of good boxes, each with
     influence `≤ 1` times the box factor.
   * A cluster is "activated" only if a disagreement reaches its boundary.
5. **Path sum.**
   * Iterating the inequality, `d(x)` for `x ∈ B` is at most a sum over chains from `N(D)` to `x`. Each chain
     alternates good segments, which carry weights `k` with total weight `≤ γ^n e^{−λ·length}` by the one-box sum, and
     bad clusters, which carry weight `C ℓ_B^d |𝒦|` and are traversed once (first passage).
   * Goodness is decided by `(ω, ω')` before the dynamics runs, and the dynamics' randomness is independent of it. So
     the average over `Π` factorises over the clusters of a chain. By H2 with the min-trick (split each cluster between
     the copies), a set of clusters of total size `a` costs `≤ 2^a η^{a/2}`.
   * Clusters are counted as lattice animals, `≤ C_d^{|𝒦|}`. With H4 the sum over cluster sequences converges, and the
     good segments give `e^{−λ dist}`. Links are included through `e^{−κ s}`, half for the min-trick and half for the
     decay. ∎

**What is new against the Lean layer, and what is not.**
* The good-box part (H3, step 3) is the Dobrushin-Shlosman iteration of `OneBox`, restricted to good boxes. Its coupling
  form is standard.
* **New:**
  * mixture-first coupling of the discrete data;
  * bad clusters as nodes, traversed once, averaged with the annealed Peierls bound;
  * the min-trick for two copies.
* **No uniformity over arbitrary fine content is used.**
  * H3 is required only on boxes whose surroundings the **pattern** forces to be small field (the support), with
    boundaries within `C ε` of each other.
  * Bad clusters need no influence bound, only their marginal (annealed) rarity.
* **Level: paper sketch.**
  * Steps 1, 3 and 5 are paper.
  * Step 2 (existence of the stationary coupling, unique ergodicity via the Doeblin floor) is standard.
  * Step 4's first-passage bookkeeping for revisited clusters is standard in form but should be written in full before
    Lean.
* **Lean:** a coupling-form layer next to `OneBox/Restricted.lean`, once this form is checked.

## 10. The hypotheses for M1's kernels

### 10.1 H0: Markov structure from Balaban's localised action (paper)

* After Balaban's localisation, the action of a term at scale `j` is a sum of local terms `E(X)`. This holds for the
  background-dependent ones too ([V] (1.59)-(1.63); [15] (190) decay), each analytic and real for real fields, with
  `|E(X)| ≤ C e^{−κ d_j(X)}`.
* **Positive decomposition of the tails.** For terms with `d_j(X) > r_int`, write `e^{E(X)} = e^{m_X}(1 + h_X)` with
  `m_X := inf E(X)` over the support and `0 ≤ h_X ≤ e^{osc E(X)} − 1 ≤ C e^{−κ d_j(X)}`.
  * Expanding `Π (1 + h_X)` gives a positive mixture over link sets `{X : link X chosen}`, with weights `Π h_X`.
  * Add these to `ω` as long links (endpoints = the boxes met by `X`).
  * The remaining interaction has range `≤ r_int`. The fibre constraints and gauge-fixing δ-functions are internal to
    the `L`-blocks, hence to boxes.
  * So, given `ω`, the specification of a box depends only on its `r_int`-surroundings and its links, which is H0.
* **Agreement.** The two kernels differ only through the coarse data, which agree outside `D`. The background's
  dependence on far coarse data is in the long terms, hence in the links. So given equal `ω` near `W`, the
  specifications on `W` agree.

### 10.2 H3: the good-box influence (paper sketch, with estimates)

* **A good box** `J`: its `r_int`-surroundings are pattern-good in both copies, with the same `ω` there.
  * There the term's small-field characteristic functions force `V_j` to be small field ([III] (2.17)), and there are
    no large-field domains, labels, excitations or links.
  * The box law given any outside `σ` in the support is the fibre-restricted fluctuation measure: a Gaussian with
    covariance `g_j² Γ_J` (massive: block constraint, Poincaré) times `exp` of small analytic local terms. Boundary
    data enter through the interactions within `r_int` of `∂J`, confined to the small-field set.
* **One boundary site `z`.** Two boundary data differing at `z` (both within `C ε_j` of the background) move the
  conditional mean in `J` by `Δ_y ≤ C ε_j e^{−m|y − z|}`.
* **Far-to-near coupling.**
  * Order the sites of `J` by decreasing distance from `z`.
  * For each radius `r`, the marginals of the two laws on `{y : |y − z| ≥ r}` are close in total variation:
    `TV_r ≤ C (Σ_{|y−z| ≥ r} p(g_j)² e^{−2m|y−z|})^{1/2} ≤ C p(g_j) r^{(d−1)/2} e^{−m r}` (Gaussian mean shift over
    width, Pinsker; the analytic perturbation changes constants only).
  * Couple the far sets maximally first, then extend inward conditionally. Then
    `E[#disagreeing sites] ≤ Σ_r #(sites at distance r) · TV_r`.
  * This gives `k_J(z) ≤ C (log p(g_j)/m)^d`, with no dependence on `ℓ_B`. These are REVIEW-3's numbers, now with exact
    agreement at far sites.
* **One-box sum.**
  * Only `z` within `r_int + O(log p/m)` of `∂J` contribute.
  * `Σ_{z ∉ J} k_J(z) e^{λ Ê_J(z)} ≤ C ℓ_B^{d−1} (log p/m)^{d+1} e^{λ(ℓ_B + C)}`, with `Ê_J(z) ≤ ℓ_B + C` (distance to
    the far side).
  * This is `≤ γ ℓ_B^d` for `ℓ_B := C (log p(g_j)/m)^{d+1}/γ` and `λ := 1/ℓ_B`.
* **Rate.** `λ ≈ γ (m/log p(g_j))^{d+1}` per scale-`j` unit, which is REVIEW-3's corrected rate. It is harmless for the
  composition: `t/ℓ → ∞` beats any power of `log log g^{-1}`.
* **To write in full:** the Pinsker step with the analytic perturbation, uniformly over boundary data within `C ε_j`.
  It uses Balaban's small-field bounds only.

### 10.3 H1, H2: properties of Balaban's pattern gas given the coarse field (inputs for section 12)

* **H2 (annealed Peierls per copy).** Under the law given the coarse field `X_{j+1}`:
  `w(A ⊂ Bad(ω), links ℓ) ≤ η^{|A|} Π e^{−κ s}`, with `η = e^{−c p0(g_j)}`.
  * This is Balaban's polymer bound for the history, (1.80)-(1.89) with the activities `e^{−p0 − κ d}`, at fixed top
    variable `X_{j+1}`.
  * It needs the **pointwise lower bound for the fibre normalisation** `∫_{fibre(X_{j+1})} ρ_j` relative to the
    small-field Gaussian fibre integral. That is the unchecked adaptation, now pointwise in the conditioning and at
    every scale.
  * It must include unreleased regions born at finer scales and the coarse bad set. The coarse bad set is fixed given
    `X_{j+1}`; its rarity is annealed from the scale-`(j+1)` law.
* **H1 (pattern coupling).** The pattern weights `w_ω` form a positive polymer gas with small activities whose
  dependence on the coarse data is local up to links.
  * Coupling two such gases so that they agree away from chains of polymers joined to `D` is a standard property of
    positive polymer gases with small activities. Possible routes: the clan or ancestor representation of
    Fernández-Ferrari-Garcia, or disagreement percolation on the polymer configuration itself.
  * It must be checked for Balaban's gas, whose polymers interact through the exponentiated boundary terms, not only
    by a hard core. Plausible, since those interactions are positive and small.
* **Both belong to section 12.** Section 12 must also run them across scales: the source at scale `j` is inherited,
  and the chains join bad regions of different scales.

## 11. The owner's reading, checked

**Unimodality after matching the discrete data.** The statement, in the form the owner asks for ("Competing states at
the boundary are required", `../../PREP.md`): **given the full discrete index `ω`, the remaining law is unimodal and
small field** on pattern-good regions.
* The box law itself is **not** claimed unimodal. It is the mixture over `ω`. Where competing fine states exist around
  a large-field boundary, they are distinct values of the index: patterns, labels, sectors.
* That structure is required, not a defect. It is kept as summation indices of the positive mixture, with total
  weight one, and no single state is ever forced. This is also why the coupling matches the indices first (Theorem
  A_good, step 1).
* Given `ω` (patterns, labels, Z2 excitations, links), on a pattern-good region the law is the fibre-restricted
  fluctuation measure.
* Its log-density is a positive-definite quadratic form on the linearised fibre (massive, Poincaré), plus analytic
  terms of size `O(g_j)` relative to it on the small-field domain.
* So it is strictly log-concave up to a small perturbation, with a unique maximum: the background minimiser, unique by
  [15].
* Labels on good boxes are factors `a_ℓ e^{L_ℓ}` with `L_ℓ` small, which add no modes. The Z2 field given SO(3) is a
  low-temperature Z2 gauge theory; its excitations are discrete data in `ω`.
* What can be multimodal (large-field backgrounds with unstable directions, Nielsen-Olesen, the charged quartic mode of
  `MILESTONE-1.md`) lies inside large-field domains, which are pattern-bad boxes. **The multimodality lives entirely in
  the discrete data**, as the reading says.
* In the theorem this is why H3 can quantify over all outside configurations on pattern-good neighbourhoods, and why
  bad boxes need no influence bound.

**Uniform local mixing ("every subset must be able to establish an arrow of causality through two nodes interacting
via a shared G0"; the owner's correction, `../../PREP.md`).**
* **In proof terms**, this is uniform local mixing: every box's conditional law contracts with a rate below one, the
  same rate for all boxes, because they share one coupling. That is Theorem A_good's **H3**: the one-box sum
  `Σ_{z ∉ J} k_J(z) e^{λ Ê_J(z)} ≤ γ |Λ_0|` with one `γ < 1` for every box (10.2), not an irreducibility statement.
* **On good boxes it holds**, box by box, uniformly in the scale, the volume and the spacing. Section 10.2 gives
  `k_J(z) ≲ (log p(g_j)/m)^d`, with boxes of side `ℓ_B ≈ (log p/m)^{d+1}`.
* **On bad boxes it is not available box by box.** On large-field backgrounds the box law has no uniform contraction:
  it may be multimodal, with competing states kept as indices of `ω`. There it is **restored on average**: bad
  clusters are nodes of the chain sum, and their rarity under each copy (H2) together with the smallness of the bad
  gas (H4) gives the same exponential decay overall (Theorem A_good, steps 4-5).
* **Side remark (irreducibility, qualitative only).** The bare Wilson weights are strictly positive (`stepK_pos`), so
  every box law, given any boundary, has a Doeblin floor `≥ e^{−C β_0 L^{dj} |J|}`.
  * It needs no connectivity of the fibre.
  * It rules out frozen box laws and gives the unique ergodicity used in step 2 of Theorem A_good.
  * It gives no estimate uniform in `a`, and plays no role in the contraction.

## 12. Next: the multi-scale crossing estimate (started in part 5, at the end of this note)

* H1 and H2 for Balaban's patterns, given the coarse field, at every scale, with the pointwise fibre normalisation
  checked.
* Then the multi-scale chain sum for the tower, using his history-summed bounds ((1.80)-(1.85)), including unreleased
  regions born at finer scales.

The adaptation to check first: the pointwise lower bound `∫_{fibre(X_{j+1})} ρ_j ≥ c^{#boxes} × (small-field Gaussian
fibre integral)` near small-field boxes. It is the same as R10's scale-`K` normalisation (13.3), now pointwise.

## 13. Status after part 2

| piece | level |
|---|---|
| UV-TV (i)_avg statement (section 8) | paper (statement) |
| Theorem A_good (section 9) | **paper sketch**: site-level (Dobrushin-Shlosman) coupling form with bad clusters as nodes; the cell-level draft failed for continuous fields. Lean pending review of this form |
| H0 for M1 (10.1) | paper |
| H3 for M1 (10.2) | paper sketch with estimates: `k_J(z) ≲ (log p/m)^d`, `ℓ_B ≈ (log p/m)^{d+1}`, `λ ≈ 1/ℓ_B` |
| H1, H2 for M1 (10.3) | open: section 12, with the pointwise fibre normalisation as an unchecked adaptation |
| unimodality after matching (11) | confirmed: given the full discrete index, the remaining law is unimodal and small field on good boxes (the box law is a mixture; competing states are kept as indices) |
| Doeblin floor (11) | positive, `e^{−O(β_0 L^{dj}|J|)}`; qualitative only, but it gives the unique ergodicity used in step 2 of Theorem A_good |

# Part 3 (2026-11-22): Theorem A_good repaired, after REVIEW-2 (fifth follow-up) and REVIEW-3 (follow-up 4)

Brief:
1. Fix steps 3-5 of Theorem A_good. The reviewers propose: identical coupling on agreeing bad boxes; start from
   agreement; take the minimal solution; pass to the limit in time.
2. Use H2 conditional on the coarser data (quenched in the coarse field).
3. The coarse bad set.
4. Small items.

Report after 1-4, then section 12. Stop at the first real obstruction.

## 14. Result of part 3 in plain words

1. **The proposed fix does not close.** With identical coupling on agreeing bad boxes and the minimal solution, a
   bad cluster still **saturates**. Its boxes re-infect each other with gain `≥ 1`, so any positive input drives the
   minimal solution to 1 on the whole cluster. Every cluster gets positive input, because good boxes pass on a small
   but non-zero disagreement. The bound is again of order the bad-box density, not decay (section 15).
   * The cause is structural. A dynamic coupling with arbitrary couplings on bad boxes accumulates activation over
     time, while the true marginals on a far bad cluster differ only by the tiny influence that reaches it.
   * **This is a real obstruction to the dynamic route, and I stop before section 12**, as instructed.
2. **The repair is static** (section 16). Each bad cluster, together with a good collar of width
   `w(𝒦) ≈ (2/m) log(|𝒦| p(g_j))`, becomes **one composite box**. Its influence bound (Lemma C) comes from a
   partition-function ratio:
   * the outer boundary acts on the cluster only through the collar's Gaussian;
   * the cross term between outer data and the cluster's inner collar is `p² e^{−m w}` per pair of sites;
   * so the cluster's marginal moves in total variation only in proportion to the input. There is no saturation, and
     no bound on the multimodal inside of the cluster is needed.
3. **With composite boxes, every box of an `ω`-dependent block family has a proper influence bound**, for **all**
   boundaries in the support, because the collar is a buffer that the pattern forces to be small field. That is the
   Dobrushin-Shlosman condition **worst case over the support**, as in the existing Lean theorem.
   * **Theorem A_good** (static form): for each fixed `ω`, Dobrushin-Shlosman in a metric where each composite box
     counts as one step, then averaged over `ω` with the Peierls bound.
   * The dynamics, the stationary or limiting coupling and the Feller question all disappear.
4. **Items 2-4** are done (sections 17-19):
   * H2 quenched in the coarse field, pointwise only where the coarse field is small field;
   * the coarse bad set as an event, with its threshold outside the support of the small-field characteristic
     functions, and no joint mixture across scales;
   * the Pinsker or interpolation step for H3, written;
   * `r_int ≳ (2/κ) log p`;
   * (B) as a hybrid of two conditionally independent copies;
   * Balaban's block-axial gauge.

## 15. Why the dynamic fix saturates

* **Setting.** `(ω, ω')` fixed. `𝒦` is a cluster of bad boxes on which `ω = ω'`, far from `D`, with a good collar.
* **Coupled update of a bad box `J ⊂ 𝒦`:**
  * identical if `J`'s `r_int`-collar agrees (H0);
  * arbitrary otherwise.
  
  So `P(J disagrees after its update) ≤ P(its collar disagreed)`, with weight 1 per collar site.
* **Minimal solution of `d = min(1, M d + s)`.**
  * For two boxes `J_1`, `J_2 ⊂ 𝒦`, each in the other's collar: `d_1 ≥ |J_2 ∩ coll(J_1)| d_2` and the same the other way
    round, so the loop gain is `≥ 1`.
  * Even a single bad box with its good collar has loop gain `Σ_{collar} Σ_{y ∈ J} k(y, ·) ≳ |coll|`, which is `≥ 1`.
  * Iterating from 0, any positive input `ε` grows geometrically until it reaches the cap: the minimal solution is
    1 on the cluster.
* **Every cluster gets positive input.** Good boxes transmit with weights `k > 0` within range `r_int`, and the boxes
  form one connected graph. So every site reachable from `N(D)` has a positive value, and every cluster saturates.
  Then `d(x)` near `B` is about `Σ_{clusters near B} P(cluster) e^{−λ dist(cluster, B)}`, of order `η`, with no
  dependence on `dist(B, D)`.
* **What it means.** In the dynamics, an isolated cluster is activated as soon as a small input arrives, and the
  arbitrary bad-box coupling never needs to deactivate it. The optimal static coupling of the marginals on `𝒦` would
  disagree only with probability equal to the transmitted influence. Bad clusters must therefore be treated through
  their **marginal** law, not box by box in time.

## 16. The repair: composite boxes and the static Dobrushin-Shlosman form

**Composite boxes.**
* For a fixed pattern pair, let `𝒦` range over the `w`-connected components of `Bad(ω) ∪ Bad(ω')` (components after
  enlarging by `w`). Here `w = w(𝒦) := (2/m) log(C |𝒦| p(g_j))`, so clusters closer than `2w` merge.
* The composite box is `W(𝒦) := 𝒦 ∪ collar_w(𝒦)`. Its collar consists of good boxes, with `ω = ω'` there, unless `𝒦`
  is joined to `N(D)` (then `𝒦` is part of the source).
* **Block family `𝔅_ω`:** the good boxes not meeting any `W(𝒦)`, plus the composite boxes `W(𝒦)`.

**A bad box acts only through its boundary** (the owner's reading, `../../PREP.md`, "A bad box acts only through its
boundary"; the same rule as the reviewers' identical coupling).
* Given matched patterns (`ω = ω'` on the composite box and its surroundings) and agreeing surroundings, the two
  conditional laws of a bad box, and of a whole composite box `W(𝒦)`, coincide by H0's agreement clause. Their update
  is identical in both copies.
* So a bad cluster creates no disagreement: **disagreement enters a bad cluster only through its boundary.**
* Section 15 shows that this rule alone, used box by box in time, does not bound **how much** enters: inside the
  cluster the gain is `≥ 1` and the dynamics saturates.
* Lemma C supplies the quantitative form. Taken through the cluster's marginal, what crosses the boundary moves the
  cluster only in proportion to the input, `C |∂_in| p² Σ_z e^{−m d(z, ∂_in)}`. The cluster carries what crosses its
  boundary and amplifies nothing beyond the factor `|W|` counted in `k_W`.

**Lemma C (influence of a composite box).**
* Let `σ, σ'` be configurations outside `W = W(𝒦)`, in the supports, differing on a set `Z`. The two conditional laws
  of `W` admit a coupling with
  `E[#{y ∈ W : Y_y ≠ Y'_y}] ≤ Σ_{z ∈ Z} k_W(z)`, where
  `k_W(z) ≤ C (log p/m)^d + C |W| |∂_in W| p(g_j)² e^{−m dist(z, ∂_in W)}`.
* Here `∂_in W` is the interface between `𝒦` and its collar.

**Proof.**
1. **Marginal of the inner data.**
   * Write `c` for the configuration on `𝒦` and the inner layer of the collar (width `r_int`). The inner layer is
     pattern-good, hence small field.
   * By H0 (finite range), the law of `W` given `σ` is `w(c) Z(c, σ) / norm`, with `Z(c, σ)` the integral over the
     rest of the collar given `c` and `σ`.
   * On the collar the law is the fibre-restricted fluctuation measure: Gaussian with covariance `g_j² Γ`, massive,
     plus small analytic terms.
2. **The cross term.**
   * `log Z(c, σ) = Q_1(c) + Q_2(σ) + X(c, σ) + R`, with `X` the inner-outer cross term mediated by the collar's
     Green's function.
   * Its mixed variation is bounded by
     `|X(c, σ) − X(c, σ') − X(c', σ) + X(c', σ')| ≤ C Σ_{x ∈ ∂_in, z ∈ Z} (|Δc_x|/g)(|Δσ_z|/g) e^{−m d(x, z)}`.
     It involves only small-field data on both sides, so each factor is `≤ 2p`.
   * `R` (the analytic perturbation) has a mixed variation of the same form with smaller constants: Balaban's
     small-field bounds, through a cumulant expansion in the collar.
3. **Total variation of the inner marginal.**
   `TV(law(c | σ), law(c | σ')) ≤ e^{2 sup_{c, c'} |mixed variation|} − 1 ≤ C |∂_in| p² Σ_{z ∈ Z} e^{−m d(z, ∂_in)}`.
   * The multimodal inside of `𝒦` is integrated against its own weight `w(c)` and never bounded. Only the
     `c`-dependence of the collar's response enters, and it is small field.
4. **Coupling.**
   * Couple `c` maximally. If it differs, count all of `W` as disagreeing.
   * Given equal `c`, couple the collar by the far-to-near coupling of 10.2, which gives `C (log p/m)^d` per `z`.
   * Summing gives the bound. ∎

**The one-box sum with composite boxes.**
* **Metric.** Measure distances in `dist_ω`, in which each composite box has diameter 1: contract it to a point.
* **Composite box.** `Σ_{z ∉ W} k_W(z) e^{λ Ê_W(z)}`:
  * `z` on the outer boundary of the collar has `d(z, ∂_in) ≈ w`, so the second term of `k_W` is
    `≤ C |W|² p² e^{−m w}`, and `≤ |W|^{−1}` by the choice of `w`;
  * with `Ê_W ≤ 2` in `dist_ω`, the sum is `≤ C |∂W| (log p/m)^{d+1} + C`.
* **The condition.** The Dobrushin-Shlosman condition in `theoremA_w`'s weighted form compares this with
  `γ c_min(W)`, where `c_min` is the coverage of the block family.
* **Coverage.** Composite boxes cover their sites once, good boxes `|Λ_0|` times. Repeat each composite box in the
  family `⌈C |∂W| (log p)^{d+1}/γ⌉` times (allowed: a block family is a multiset of blocks with a coverage condition).
  Then its own coverage dominates its boundary influence.
* **Price:** the contraction factor `θ = 1 − c_min(1 − γ)/M` of `cov_le_weighted_on` gets closer to 1. That is
  harmless, since the decay rate comes from the weights `e^{λ Ê}`, not from `θ`.
* **This needs checking in detail**, as the precise form of the condition with variable blocks (section 16, check 1).

**Theorem A_good, static form.**
* **(i) For fixed `(ω, ω')`.**
  * On the agreeing region the two specifications coincide (H0). Every block of `𝔅_ω` has an influence bound for all
    boundaries in the support: H3 for good boxes, Lemma C for composite boxes.
  * The weighted Dobrushin-Shlosman condition holds with `λ` per step of `dist_ω`.
  * So the boundary influence of `N(D)` on `B` is `≤ C |B| e^{−λ dist_ω(B, N(D) ∪ 𝒮)}`, where `𝒮` is the union of
    composite boxes joined to `D` (part of the source).
  * The same holds for covariances: `|Cov_{μ_ω}(f, g)| ≤ C |A| e^{−λ dist_ω(A, S_g)}` (Lean: `theoremA_on`/`theoremA_w`
    with general blocks).
* **(ii) Averaging over `ω`.**
  * `dist_ω(B, D) ≥ dist(B, D) − Σ_{𝒦 on a geodesic} diam W(𝒦)`.
  * By H2 (now conditional, section 17) and the min-trick, the probability that composite boxes cover a fraction
    `≥ ½` of some path from `B` to `D` is `≤ C|B| Σ_{n ≥ dist/2} (C (log p)^d η^{1/2})^n`.
  * So `E_Π[C|B| e^{−λ dist_ω}] ≤ C|B|(e^{−λ dist/2} + (C' η^{1/2})^{dist/2})`.
* **(iii) The pattern-index covariance**, for covariance statements under the mixture,
  `Cov_w(μ_ω f, μ_ω g)`, is bounded by H1: the patterns decorrelate away from bad chains.

**What this changes.**
* **Gone:** the dynamics, the stationary or limiting coupling, the Feller question and unique ergodicity. The Doeblin
  floor stays only as the qualitative side remark of section 11.
* **The worst-case quantifier** of the existing Lean layer is now available per `ω`. That is the point of the collar
  as a buffer: the pattern forces the collar to be small field, so every boundary in the support is buffered.
* **Lean:** for (B), covariance under `μ_ω`, the present `theoremA_on`/`theoremA_w` apply per `ω`, given:
  * general blocks with multiplicities;
  * the specification extended off the support (it is only used `μ`-almost surely);
  * the metric `dist_ω`.
  
  For (A), comparison of two measures, a boundary-influence version is needed. It is the same iteration; new in Lean.

**To check before Lean:**
1. the weighted condition with variable blocks and multiplicities, in `theoremA_w`'s exact form (`GDSw`, coverage);
2. Lemma C's cross-term bound with the fibre constraint and Balaban's analytic perturbation in the collar;
3. merging clusters within `2w`, and the lattice-animal count for `w`-connected clusters, with `w` growing like
   `log |𝒦|`.

## 17. H2 conditional on the coarse data (item 2)

* **Agreed** (REVIEW-2). In the tower the source at scale `j` is the disagreement inherited from scale `j + 1`. It is
  random, correlated with the scale-`j` bad sets, and concentrated where the coarse field is bad. Theorem A_good
  must therefore be applied **conditionally on all coarser data** `𝒳_{j+1} := (X_{j+1}, ..., X_ℓ)`, with the source
  measurable with respect to it.
* **H2, quenched form.** For every finite set `A` of boxes **outside `Bad^c(X_{j+1})`**, and links `ℓ`:
  `P(A ⊂ Bad_j(ω), ℓ ⊂ Lk(ω) | 𝒳_{j+1}) ≤ η^{|A|} Π e^{−κ s}`, with `η = e^{−c p0(g_j)}`.
  * Pointwise in `𝒳_{j+1}`, but only for boxes where the coarse field is small field (REVIEW-3).
  * The kernel `K_j` depends on `𝒳_{j+1}` only through `X_{j+1}` (Markov in the scale), so this is a statement about
    the pattern weights `w_ω(X_{j+1})`.
* **What it needs: the pointwise fibre-normalisation lower bound.** For a box `J` outside `Bad^c(X_{j+1})`, the
  denominator `∫_{fibre(X_{j+1})} ρ_j` restricted to `J`'s neighbourhood is at least `e^{−C}` per box times the
  small-field Gaussian fibre integral. This is the unchecked adaptation, now pointwise and at every scale. It
  conditions only on coarse data, so no frozen region.
* **Where the coarse field is bad**, H2 says nothing. Those boxes are in the source or bad by fiat, and their rarity
  comes from scale `j + 1`, given `𝒳_{j+2}`. That is the chaining of section 12.
* **Reconciled.**
  * Sections 8 and 9: "annealed" now means annealed in the scale-`j` index `ω` only, and quenched in the coarse data.
  * The min-trick uses the quenched bound for each copy, given its coarse data. In (A) the two copies' coarse data
    differ far away, but both bounds are pointwise.

## 18. The coarse bad set (item 3)

* **Definition.** `Bad^c(X_{j+1})` := boxes whose block field `X_{j+1}` violates the small-field condition at scale
  `j + 1` with the **sharp** threshold `ε'_{j+1} := 2 ε_{j+1}`.
  * Balaban's smooth small-field characteristic functions at scale `j + 1` are supported where the field is
    `≤ (1 + δ) ε_{j+1}` with `δ < 1`. So the threshold lies **outside their support**.
  * A coarse box in `Bad^c` therefore lies in a large-field domain of every term of `ρ_{j+1}`'s representation, and
    its rarity comes only from the large-field pattern weights of `ρ_{j+1}` (REVIEW-2's first proviso).
* **No joint mixture across scales.**
  * The R-operation that builds `ρ_{j+1}` from `ρ_j` exponentiates and resums, so `ω_j` and `ω_{j+1}` are not
    indices of one positive mixture.
  * The tower carries coarse badness only as the event `Bad^c(X_{j+1})` of the conditioning variable, plus the
    unreleased regions that `ρ_j`'s own indices still hold (regions born at finer scales).
  * Each scale's index `ω_j` is drawn afresh, from `w_ω(X_{j+1})`, given the coarse data.

## 19. Small items (item 4)

**H3: the Pinsker (interpolation) step, written.**
* Good box `J`, boundary data `σ_t = σ + t(σ' − σ)`, `t ∈ [0, 1]`. Every `σ_t` is within `C ε_j` of the background in
  the block-axial gauge.
* The box law is `μ_t ∝ χ · exp(−½⟨φ, A φ⟩ + ⟨b(σ_t), φ⟩ + V(φ; σ_t))`, with:
  * `φ` the fluctuation in units of `g_j`, on the linearised fibre;
  * `A` positive-definite with mass `m`;
  * `b` linear in `σ/g`;
  * `V` analytic and small;
  * `χ` the small-field truncation at `p(g_j)` standard deviations.
* For bounded measurable `f` of the sites at distance `≥ r` from `z`:
  `d/dt μ_t(f) = Cov_t(f, ⟨Δb, φ⟩ + ∂_t V)`.
* Write `L := ⟨Δb, φ⟩ + ∂_t V`, supported within `r_int` of `z`, with `|Δb| ≤ 2p` at `z`. Then
  `|Cov_t(f, L)| ≤ 2‖f‖_∞ E_t|E_t[L | φ_F] − E_t L|`, with `F` the far set.
* For the Gaussian part, `E[L | φ_F]` is linear in `φ_F` with coefficients `≤ C p e^{−m r}`. The perturbation `V` and
  the truncation change this by factors `1 + O(δ)` and by `e^{−c p²}` (Balaban's small-field bounds; the truncation
  is at `p` standard deviations).
* Integrating over `t`: `TV(μ_σ|_F, μ_{σ'}|_F) ≤ C p |F|^{1/2} e^{−m r} + e^{−c p²}`. This is the far-marginal bound
  used in 10.2. The `e^{−c p²}` is far below the scales used.

**Long-link tails.** On small field the localised pieces of the main term are `~ p(g_j)² e^{−κ d}` (REVIEW-3), so the
link weights are `h_X ≤ C p² e^{−κ d(X)}`. Taking `r_int := (2/κ) log p + C` keeps links between boxes rare, at
`≤ e^{−κ s/2}`, and `r_int ≪ ℓ_B`.
* **Large-field regions** use the local bare Wilson action inside `T`, not the background, so they create no long tails
  of size `g^{−2}`.

**Unique ergodicity** is no longer needed: the static form uses no dynamics. The Doeblin floor stays a qualitative
side remark.

**(B) as a hybrid.**
* Let `Y` and `Y°` be two copies of the fine field, conditionally independent given `𝓕_ℓ`, with their randomness
  indexed by region.
* Build `H` with law `μ_{𝓕}` so that `H = Y` near `A` and `H = Y°` near `θA`, except on disagreement events. Theorem
  A_good, applied to the two regions with the source in between, gives them.
* Then `|Cov(f, g | 𝓕_ℓ)| ≤ ‖f‖ ‖g‖ (P(H_A ≠ Y_A) + P(H_{θA} ≠ Y°_{θA}))`.

**Gauge.** Balaban's **block-axial gauge** relative to the given coarse configuration: fully gauge-fixed once the
coarse data are equal near `J`. This replaces "modulo gauge" in sections 8-10.

## 20. Status after part 3

| piece | level |
|---|---|
| dynamic fix of steps 3-5 (the reviewers' proposal) | **fails**: saturation inside bad clusters (section 15). A real obstruction to that route |
| static form: composite boxes + Lemma C + Dobrushin-Shlosman per `ω` + averaging (section 16) | **paper sketch**; three checks listed before Lean |
| H2 quenched in the coarse field (17) | statement reconciled; needs the pointwise fibre normalisation (unchecked adaptation) |
| coarse bad set (18) | written |
| H3 Pinsker step, `r_int`, (B), gauge (19) | written |
| section 12 (multi-scale crossing) | **not started**: it builds on Theorem A_good, whose proof form changed. Waiting for the reviewers' check of section 16 |

# Part 4 (2026-11-22): the merging repair, after REVIEW-2 (sixth follow-up) and REVIEW-3 (follow-up 5)

Brief: repair the merging cascade first, by isolation at the creation scale with localisation and truncation as
needed. Then the fixable items, then section 12. Report after the merging repair. The owner's reading ("Disturbances
are isolated from the start", `../../PREP.md`): a bad region gets its collar at the scale where it is born, with a
width set by that scale, not growing with its later size.

## 21. The merging repair

### 21.0 Result in plain words

* **Agreed:** with a collar width growing like `log |K|` and merging within `2w`, composite boxes percolate in large
  volume at fixed spacing. Since `MassGapLoc` takes the volume limit first, volume uniformity fails.
* **The repair has three parts:**
  1. **Fixed merge range per scale.** Every composite box at scale `j` gets the same collar width
     `w_j := (3/m') log(C L^d n_j p(g_j))`, with `m' := min(m, κ')`. Merging happens only within the fixed distance
     `2w_j + ℓ_B`. With the range fixed, a cluster's reach no longer grows with its size, so the cascade cannot start.
  2. **Localisation and truncation.**
     * Theorem A_good is applied in a region `Λ''_j` around `B`, of the size of `dist(B, D)`, with the outside acting
       as an extra source at that distance.
     * Clusters **born at scale `j`** with more than `n_j := C_1 log|Λ''_j| / log(1/η_j)` boxes go into the failure
       event. Its probability is `≤ |Λ''_j|^{−C_2}` by the quenched H2.
     * `n_j` enters the collar width only through `log n_j`.
  3. **Isolation at the birth scale (the owner's reading).**
     * A region inherited from a coarser scale (coarse bad set, unreleased regions) is a composite box at scale `j`.
     * Its size is bounded by the truncation **at its own scale**, so `|K| ≤ L^d n_{j+1}`. Its rarity is charged at
       its own scale, in section 12.
     * Inherited regions are separated at their birth scale by their own collars, `2w_{j+1}` coarse boxes, that is
       `≥ 2L w_{j+1} ℓ_B` scale-`j` units. That is far more than the scale-`j` merge range, so they do not merge with
       each other at scale `j` except through scale-`j`-born bad boxes between them. Those are priced by H2.
* **The constants:**
  * the fixed merge range needs only `C w_j^d η_j^{1/2} < ½`;
  * with `w_j ≈ (3/m) log g_0^{-2}` (from `log n_j ≲ log log |Λ''_j| ≲ log g_0^{-2}`), that is
    `p0(g_j) ≫ d log log g_0^{-2}`, true for Balaban's `p0 = A0 (log g^{-2})^p` with any `p ≥ 1`;
  * REVIEW-3's stronger condition (`p ≥ 2`, or `c A0 > d`) is needed only if the merge range is allowed to grow up to
    `log |Λ''|`. With the fixed range it is not needed. To be checked by the reviewers.
* **Level: paper sketch.** No obstruction found. The pricing of inherited regions belongs to section 12.

### 21.1 Composite boxes with a fixed collar per scale

* **The bad set at scale `j`**, for a pattern pair:
  `𝔅_j := Bad_j(ω) ∪ Bad_j(ω') ∪ Bad^c(X_{j+1}) ∪ Bad^c(X'_{j+1})`, plus link endpoints. Links are **edges** of the
  cluster graph (fixable item, REVIEW-2 and REVIEW-3).
* `𝔅_j` splits into:
  * **born at `j`:** large-field domains, labels and Z2 excitations of `ω_j`, and links;
  * **inherited:** `Bad^c` of the coarse data, and the unreleased regions of `ω_j` born at finer or coarser scales.
    Regions born at finer scales are small at scale `j` and priced by `ω_j`'s weights, as in H2; the coarse bad set
    is priced one scale up.
* **Clusters:** components of `𝔅_j` under proximity `2w_j + ℓ_B` (fixed), with links as edges, rounded up to unions
  of boxes with pockets filled (REVIEW-3's coverage point).
* **Composite box:** `W(K) := K ∪ collar_{w_j}(K)`. The collars are pairwise disjoint by construction, and consist of
  good boxes.
* **Collar width:** `w_j := (3/m') log(C L^d n_j p(g_j))`, with `m' := min(m, κ')` and `n_j := max(n_j^{born}, n_{j+1})`.
  Lemma C then holds for every `K` with `|K| ≤ C L^d n_j`:
  * the cross term `C p² e^{−m' w_j} ≤ (C L^d n_j)^{−3} p^{−1}` beats the `|K|` factor;
  * the hard truncation contributes `e^{−c p²} e^{−m' w_j}`, not a flat `e^{−c p²}` (REVIEW-3).

### 21.2 Localisation and truncation

* **Region.** `Λ''_j :=` the scale-`j` boxes within distance `R'_j := dist_j(B, D)` of `B`. Apply Theorem A_good to the
  two conditional laws on `Λ''_j`, given the configurations outside.
* **The outside as a source.** The outside configurations of the two copies may differ. They enter only through
  `∂Λ''_j`, at distance `R'_j` from `B`, so they act as an extra source as far away as `D` is.
* **Truncation event** `F_j`: some scale-`j`-born cluster meeting `Λ''_j` has more than `n_j^{born}` boxes, with
  `n_j^{born} := C_1 log|Λ''_j| / log(1/η_j)`.
  * By the quenched H2 and the min-trick, given the coarse data,
    `P(F_j | 𝒳_{j+1}) ≤ |Λ''_j| Σ_{n > n_j} (C (2w_j + ℓ_B)^d η_j^{1/2})^n ≤ |Λ''_j|^{−C_2}`.
  * The count is of lattice animals under the fixed proximity `2w_j + ℓ_B`.
* **Inherited regions** are not truncated at scale `j`. Their size, `≤ C L^d n_{j+1}` scale-`j` boxes per coarse
  cluster, comes from the truncation `F_{j+1}` one scale up, with failure probability `|Λ''_{j+1}|^{−C_2}` there.
* **On `F_j^c ∩ F_{j+1}^c`:**
  * every cluster in `Λ''_j` has `|K| ≤ C L^d n_j`, so the collar `w_j` suffices for Lemma C;
  * the per-site column condition (REVIEW-3: `GDSw` per site) holds in `Λ''_j`, with the constant multiplicity
    `n_W := ⌈C ℓ_B^{d−1} (log p/m)^{d+1}/γ⌉` and `ℓ_B ≳ (log p/m)^{2d+1}/γ²`, the fixable item.

### 21.3 Why the cascade is gone (volume uniformity)

* **The merge range `2w_j + ℓ_B` is fixed** for the region, independent of cluster sizes. So a cluster's reach does not
  grow with its size, and the cascade of REVIEW-2 and REVIEW-3 has no mechanism.
* **Proximity clusters of scale-`j`-born boxes are subcritical** if `C (2w_j + ℓ_B)^d η_j^{1/2} < ½`.
  * `n_j ≤ C log|Λ''_j|`, and `|Λ''_j| ≤ (t/(L^j a ℓ_B))^d ≤ e^{C g_0^{−2}}` since `log(1/a) ≈ g_0^{−2}/(2b)`. So
    `log n_j ≲ log g_0^{−2}` and `w_j ≲ (3/m')(log g_0^{−2} + log p) + C`.
  * The condition becomes `c p0(g_j)/2 > d log(C log g_0^{−2})`.
  * `p0(g_j) = A0 (log g_j^{−2})^p ≥ A0 (log g_0^{−2})^p`, so this holds for `g_0 ≤ γ0(L)` with any `p ≥ 1`. It is
    added to condition 8 of `S1-INDUCTION.md`.
* **Every estimate depends on the localised region** (`|Λ''_j|`, `R'_j`), never on the total volume. So everything is
  uniform in the volume, and the volume limit can be taken first.

### 21.4 Isolation at the birth scale, across scales (the owner's reading, made precise)

* **A region born at scale `j'`** (a coarse bad cluster of `X_{j'}`, or an unreleased region) receives its collar at
  scale `j'`: width `w_{j'}` in scale-`j'` boxes.
* **At every finer scale `j < j'`** it is a composite box whose scale-`j` collar of width `w_j` lies inside the
  scale-`j'` collar, which is `≈ L^{j'−j} w_{j'} ℓ_B` scale-`j` units wide.
* **Two regions born at scale `j'`** are separated by at least `2w_{j'}` scale-`j'` boxes. At scale `j` this is far
  more than `2w_j + ℓ_B`, so they never merge at a finer scale through their own collars.
  * They can be bridged only by bad boxes born at the finer scales in between, which H2 prices at those scales.
* **So** each region keeps the collar of its birth scale, and the regions of different scales are separated by those
  collars. "Every transfer in has to happen through a DB" is Lemma C at each scale.
* **What remains, as the reading says:** that each scale's regions are sparse relative to their collars. Per scale this
  is the subcriticality of 21.3, from H2 at that scale. Chaining across scales is section 12.

### 21.5 The path cost, after the repair

* On `F_j^c`, a path of `R` scale-`j` units from `B` to `D` loses length in `dist_ω` only to composite boxes. Each has
  diameter `≤ C L (n_j)^{1/d} ℓ_B + 2w_j`, and the scale-`j`-born ones are subcritical.
* The probability that scale-`j`-born composite boxes cover half of the path is
  `≤ (C (2w_j + ℓ_B)^d η_j^{1/2})^{R/(4(ℓ_B + 2w_j))}`, exponential in `R/(ℓ_B + w_j)`.
* Inherited composite boxes on the path are priced at their own scale (section 12, REVIEW-2's item 3), not here.

### 21.6 Status

| piece | level |
|---|---|
| fixed merge range, collar `w_j` set per scale | paper |
| localisation (outside as source) and truncation `F_j` with `n_j = C log|Λ''_j|/log(1/η_j)` | paper sketch (quenched H2, lattice-animal count) |
| no cascade; volume uniformity; condition `p0 ≫ d log log g_0^{−2}` | paper sketch; weaker than REVIEW-3's `p ≥ 2` condition, to be checked |
| isolation at the birth scale for inherited regions | paper sketch; their pricing is in section 12 |

Next, after the report: the fixable items of the two reviews (Lemma C's interface factor, constant multiplicity with
overlapping good boxes, coverage by rounding, the coupling form instead of off-support hybrids, the cut-off in [III]
(2.17)), then section 12.

# Part 5 (2026-11-22): the fixable items, and the start of section 12

## 22. The fixable items (REVIEW-2 sixth follow-up, REVIEW-3 follow-up 5)

### 22.1 Long links as edges (Lemma C)

* **Cluster connectivity** uses chosen links as edges (21.1), so link endpoints belong to the cluster.
* A link-joined composite box may be non-contiguous: two pieces with their collars, joined by the link.
* Lemma C's proof is unchanged: `c` now lives on all pieces and their inner layers. Given `ω`, the only `c`-`σ`
  couplings left are through the collars, since every chosen link has both ends in `K`.
* `dist_ω` contracts the whole composite box. In the averaging, a link of length `s` costs `e^{−κ s}` (H2) against the
  `λ s` it saves, which is fine since `λ ≪ κ`.

### 22.2 Lemma C without the interface factor

* For fixed `z`, `Σ_{x ∈ ∂_in} e^{−m' d(x, z)} ≤ C_{m'} e^{−m' d(z, ∂_in)}` (REVIEW-2). So
  `TV(law(c | σ), law(c | σ')) ≤ C p² Σ_{z ∈ Z} e^{−m' d(z, ∂_in)} + C e^{−c p²} Σ_{z ∈ Z} e^{−m' d(z, ∂_in)}`.
  * The second term is the hard truncation, which also needs a correlation across the collar (REVIEW-3).
* If `c` differs, the disagreeing sites number `≤ |K| + C |∂_in| (log p/m)^d` (the cluster, plus the collar's
  near-inner layer). Hence
  `k_W(z) ≤ C (log p/m)^d + C (|K| + |∂_in| (log p/m)^d) p² e^{−m' d(z, ∂_in)}`.
* For `z` outside the collar, `d(z, ∂_in) ≥ w_j`. With `w_j = (3/m') log(C L^d n_j p)` (21.1) the second term is
  `≤ (C L^d n_j)^{−2} p^{−1}`, so negligible.

### 22.3 Constant multiplicity, good boxes overlapping the collar (per-site column condition)

* **Block family `𝔅_ω`:**
  * every good box (a translate of the side-`ℓ_B` box) at distance `≥ r_int + 1` from every cluster `K`, including
    good boxes overlapping collars;
  * each composite box `W(K)` with the **same** multiplicity
    `n_W := ⌈C ℓ_B^{d−1} (log p/m)^{d+1}/γ⌉`.
* **The condition**, per site `x` (Lean's `GDSw`):
  `Σ_{blocks B ∌ x} k_B(x) e^{λ E_B(x)} ≤ γ · coverage(x)`.
* **Sites of `K`:** no block other than its own `W` lies within `r_int` of `x` (good boxes keep distance `≥ r_int + 1`),
  so the column is 0 by finite range. The coverage is `n_W ≥ 1`.
* **Inner-layer sites** (collar sites within `r_int + 1` of `K`): they are covered by `W` only (`n_W` times). Their
  column is their influence on nearby good boxes, `≤ C ℓ_B^{d−1} (log p/m)^{d+1} e^{λ(ℓ_B + C)}` (the one-box estimate
  of 10.2). This is `≤ γ n_W` by the choice of `n_W` and `λ = 1/ℓ_B`.
* **Other collar sites and good sites** near `W`: coverage `≥ c_0 ℓ_B^d` (a positive fraction of the translates fit,
  after the rounding of 22.4). Their column is the good-box part `≤ γ c_0 ℓ_B^d / 2` (10.2), plus
  `n_W k_W(x) e^{λ E_W(x)} ≤ n_W · C (log p/m)^d · C`.
  * The second part is `≤ γ c_0 ℓ_B^d/2` if `ℓ_B ≥ C (log p/m)^{2d+1}/γ²` (REVIEW-3). Added to `S1-INDUCTION.md` 1
    (row 5).
* **Weights `E_W(x)`:** with `W` contracted in `dist_ω`, `E_W(x) ≤ 2`. Good boxes have `E ≤ ℓ_B + C`, so
  `e^{λ E} ≤ e^{1 + Cλ}`.

### 22.4 Coverage of gaps

* Composite boxes are rounded up to unions of grid boxes, and merged when closer than `ℓ_B + 2r_int + 2`.
* Then every site outside all `W` lies in a region in which some side-`ℓ_B` translate containing it stays
  `≥ r_int + 1` away from every cluster. So `coverage(x) ≥ 1`, and `≥ c_0 ℓ_B^d` at distance `≥ ℓ_B` from every `W`.
* This changes the proximity of 21.1 from `2w_j + ℓ_B` to `2w_j + ℓ_B + 2r_int + 2`. The lattice-animal entropy is
  still `(C(w_j + ℓ_B)^d)^n` and the subcriticality condition of 21.3 is unchanged in form.

### 22.5 The coupling form of Dobrushin-Shlosman (no hybrids off the support)

* **Coupling-form Theorem DS.**
  * Fix `(ω, ω')`, the block family `𝔅_ω`, and site weights `v(x) := e^{−λ dist_ω(x, B)}`.
  * Suppose each block `b` has, for every pair of boundaries **in the supports**, a coupling of its two laws with
    `E[#{y ∈ b : Y_y ≠ Y'_y} weighted by v] ≤ Σ_z k_b(z) v(z) e^{λ E_b(z)} 1{σ_z ≠ σ'_z}`.
  * Suppose the per-site column condition of 22.3 holds.
  * Then there is a coupling `π` of `μ_ω` and `μ'_{ω'}` with
    `Σ_x v(x) P_π(Y_x ≠ Y'_x) ≤ (1 − θ)^{−1} Σ_{x ∈ S} v(x)`, where `S` is the source (`N(D)`, non-agreeing boxes and
    `∂Λ''`).
  * In particular `P(Y ≠ Y' on B) ≤ C(1 − θ)^{−1} Σ_{x ∈ S} e^{−λ dist_ω(x, B)}`.
* **Proof.**
  1. Let `T` be the averaged block update on couplings: pick a block `b` at random, then resample both copies on `b`
     by its coupling given the current boundaries (sources arbitrary).
  2. `T` maps couplings of `(μ_ω, μ'_{ω'})` to couplings of the same pair (DLR for each copy).
  3. Both copies are always samples of their own laws, so only boundary pairs **in the supports** ever occur. No hybrid
     configuration is used.
  4. The column condition gives `Φ(Tπ) ≤ θ Φ(π) + (1 − θ) Σ_S v`, with `Φ(π) := Σ_x v(x) P_π(Y_x ≠ Y'_x)` finite
     (`Σ_x v(x) < ∞` in `d = 4`).
  5. Iterate from the product coupling, so `Φ(T^n π_0) ≤ θ^n Φ(π_0) + Σ_S v`.
  6. The configuration space is compact, so take a weak limit point. `{Y_x ≠ Y'_x}` is open, so `P(Y_x ≠ Y'_x)` is
     lower semicontinuous (portmanteau) and the bound passes to the limit. Its marginals are `μ_ω` and `μ'_{ω'}`. ∎
* **What it replaces:**
  * the oscillation iteration of `theoremA_on`, which passes through off-support hybrids (REVIEW-3);
  * the dynamics of part 3. This is a contraction on couplings of fixed marginals, not a time evolution from
    agreement, so nothing accumulates. Composite boxes carry Lemma C, so there is no saturation.
* **Lean:** a new generic layer, "coupling contraction on block families", routine. For (B), covariance from the
  hybrid of 19 uses the same theorem.

### 22.6 The cut-off in [III] (2.17), checked

* In the text layer of [III] (CMP 119, pp. 247-248 and 257), Balaban's decompositions of unity are
  `1 = χ(sup |…| ≤ α) + (1 − χ(…))` with `χ` the **characteristic function of the set** (e.g. (1.8),
  `χ_0(Q) χ_0(Q_1)`, and (2.17), `χ_k := χ(N sup |U_{k,□}(V_k, ∂p) − 1| < ε_k)` over the `L M² R_k`-cubes).
* No smoothing is visible in the text layer. Analyticity is used in the variables **within** the sets, not of `χ`.
* So the support of the small-field function is exactly `{sup ≤ ε_k}`.
* **The coarse threshold** `Bad^c(X_{j+1})`, defined with the same quantity (the cube-wise sup of the minimiser's
  plaquettes) at `2ε_{j+1}`, lies strictly outside that support.
* If a smoothed version is used anywhere, its reach is `(1 + δ)ε` with `δ < 1` by construction, and `2ε` is still
  strictly above. To be safe against the poor OCR, take `3ε_{j+1}`.
* **Status:** checked as far as the text layer allows.

### 22.7 Inherited coarse-bad regions

* As agreed (REVIEW-2), they are priced at their own scale, not in step (ii) of Theorem A_good at scale `j`.
* At scale `j` they are composite boxes whose sizes are bounded by `F_{j+1}^c` (21.2), with Lemma C. Their probability
  enters the multi-scale chain of section 12.

**Status of part 5's fixable items:** all written (paper). Lean: the coupling-contraction layer (22.5) is the generic
theorem to formalise, once section 21 and this part are checked.

## 12 (continued, part 5). The multi-scale crossing estimate (started)

**Route** (REVIEW-2): apply Theorem A_good (coupling form, 22.5) at each scale, conditionally on the coarser data
`𝒳_{j+1}`. The source at scale `j` is the disagreement inherited from `j + 1`. Chain the conclusions from `ℓ` down.

### 12.1 The pointwise fibre-normalisation lower bound, checked

**Statement needed (quenched H2).** For `X_{j+1}` small field on the `C w_j`-neighbourhood of a set `A` of scale-`j`
boxes:
`Σ_{ω : A ⊂ Bad_j(ω)} w_ω(X_{j+1}) ≤ η_j^{|A|}`, with `w_ω(X_{j+1}) = ∫_{fibre(X_{j+1})} ρ^ω_j / ρ_{j+1}(X_{j+1})`.

**The denominator is the coarse law.** The normalisation `∫_{fibre(X_{j+1})} ρ_j` is exactly `ρ_{j+1}(X_{j+1})`, by
exactness (`map_resample_eq`; the fibre integral of the fine law is the coarse density). It is a sum of non-negative
terms, so it is bounded below by any single family of terms.

**Comparison term by term.** For each `ω` with `A ⊂ Bad(ω)`, let `ω_0 := ω` modified on the `C w_j`-neighbourhood
`N_A` of `A` to be small field there (no large-field domain, label or excitation on `N_A`), the same elsewhere.
Admissibility is local, so `ω_0` is admissible. Then
`w_ω / w_{ω_0} = ∫_{fibre} ρ^ω_j / ∫_{fibre} ρ^{ω_0}_j`.
* **Numerator.** By (2.19) factorisation and locality, the integrand differs from the `ω_0` one only on `N_A`. There it
  is a product of `T`-activities, each bounded by `e^{−2(1+β)p0 − κ d}` ((1.89), with Balaban's normalisation constants
  "`O(1) log g^{−2}` per site" included), times `exp(boundary terms)`, bounded by `e^{C|∂N_A|}`.
* **Denominator.** On `N_A`, `ρ^{ω_0}_j` is the small-field term. Its action is within `O(1)` per cube of the
  quadratic form ([III] (2.23)-(2.42): E-terms `O(1) e^{−κ d}`). Its fibre integral over the small-field set
  around the background `U(X_{j+1})` is
  `≥ e^{−C|N_A|} × (Gaussian fibre normalisation on N_A)`.
  * This uses that `X_{j+1}` is small field on `N_A`, so the background is regular and the small-field set has
    Gaussian mass `≥ 1 − e^{−c p²}` per cube.
* **The ratio.** Balaban's `T`-activities are normalised by the same Gaussian constants (his normalisation terms
  `E_k(Z)` in (1.70)-(1.71)). So
  `w_ω/w_{ω_0} ≤ e^{−2(1+β)p0 #components(A) − κ d(A) + C|N_A|}`.
* **Summing.** Summing over the `ω`-restrictions on `N_A` (entropy `C^{|N_A|}`) and using `w_{ω_0} ≤ 1` gives
  `Σ_{ω : A ⊂ Bad} w_ω ≤ (C e^{−c p0})^{|A|}` per box, since `|N_A| ≤ C w_j^d |A|` and `p0 ≫ w_j^d`. That is
  `η_j^{|A|}` with `η_j := e^{−c' p0(g_j)}`.
* **Pointwise in `X_{j+1}`**, and at every scale `j` (constants scale-uniform).

**What is still a reading, not a citation.** That the normalisation constants inside Balaban's `T`-activities ((1.70)
`E_k(Z)`, "normalization terms ... with localizations intersecting the large field domain") are exactly the Gaussian
fibre normalisations of the small-field alternative on the same region, so that the comparison has no leftover factor
`(β^{3/2})^{#bonds}`.
* This is the same point as R10's scale-`K` normalisation (13.3), now term by term and pointwise.
* It is plausible by construction: Balaban normalises each step's Gaussian integral and subtracts it. It is not stated
  in this form in the text.
* **Status:** checked up to this one reading. It is **unchecked adaptation 4** of `M1-PLAN.md` 0, now localised to a
  precise statement.

### 12.2 Next (not yet done)

* **H1:** rewrite Balaban's pattern marginal as a positive gas with small local activities given the coarse data:
  * activities as in 12.1;
  * many-body interactions from the small-field fluctuation integral on the complement: Balaban's cluster expansion,
    bounded and decaying, with the single-polymer parts absorbed into the activities.
  
  Then a quantitative H1 from its convergent cluster expansion: local pattern marginals depend on far coarse data with
  decay.
* **The chaining** from `ℓ` down, with inherited regions priced at their own scale.
