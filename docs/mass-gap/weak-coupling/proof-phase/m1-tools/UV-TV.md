# Lemma UV-TV (i): the Dobrushin route (m1-tools, 2026-11-22)

> **Status (part 2, sections 7-13 below):** Lemma UV-TV (i) is restated in averaged form (section 8). The good-boundary Theorem A is restated in site-level Dobrushin-Shlosman coupling form, with bad clusters as nodes (section 9, paper sketch). Section 3.1's independent-percolation hypothesis is withdrawn. Next: the multi-scale crossing estimate (section 12).

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

## 12. Next: the multi-scale crossing estimate (not started)

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
