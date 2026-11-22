# Lemma UV-TV (i): the Dobrushin route (m1-tools, 2026-11-22)

> **Status (part 2, sections 7-13 below):** Lemma UV-TV (i) is restated in averaged form (section 8). The good-boundary Theorem A is restated in site-level Dobrushin-Shlosman coupling form, with bad clusters as nodes (section 9, paper sketch). Section 3.1's independent-percolation hypothesis is withdrawn. Next: the multi-scale crossing estimate (section 12).

> **Status (part 3, sections 14-20):** the reviewers' dynamic fix of Theorem A_good saturates inside bad clusters (section 15). The repair is static: composite boxes (cluster plus good collar) with Lemma C, Dobrushin-Shlosman per `ω` worst case over the support, then an average over `ω` (section 16, paper sketch). H2 is quenched in the coarse field (17). Section 12 has not started and waits on the reviewers' check of section 16.

> **Status (part 4, section 21):** the merging cascade is repaired by a fixed merge range per scale (collar `w_j` set by the scale), localisation around `B` with truncation of scale-`j`-born clusters at `n_j = C log|Λ''_j|/log(1/η_j)`, and isolation of inherited regions at their birth scale (paper sketch). The fixable items and section 12 follow.

> **Status (part 5, section 22 and section 12 continued):** the fixable items are written: links as edges; Lemma C without the interface factor; constant multiplicity with overlapping good boxes; coverage by rounding; the coupling-form Dobrushin-Shlosman theorem (no off-support hybrids); the cut-off check. Section 12 has started with the pointwise fibre normalisation, checked up to one reading (12.1).

> **Status (part 6, section 23 and section 12 completed):** the size-cap gap is closed by an annealed truncation of each scale's large set (persistence) and a bridge-count truncation; the condition uses `g_j`; the failure tail is polynomial (`C_2 > 1`). H1 follows from Dobrushin uniqueness of the dilute pattern gas. The chaining from `ℓ` down gives UV-TV (i) and N-2's key step at paper-sketch level, resting on one unchecked adaptation (Balaban's normalisation terms).

> **Status (part 7, sections 24-25):** Peierls bounds restated per `M R_j`-cube with rate `κ` (fixed condition on `κ`; no new reading); H1 replaced by a polymer-level cluster expansion and disagreement percolation. Verdict (25): complete argument at paper-sketch level; the normalisation reading is a single point of failure, with a named fallback (a per-cube `e^{−c p0}` margin); four write-outs owed.

> **Status (part 8, section 26 and 25 revised):** the strengthened induction (c) re-proves [V] (1.80)-(1.97) with a retained slack `e^{−c p0²}` per birth-scale cube, so reading (b) is no longer needed. (a) holds in substance as a citation-level reading. `κ` large is a citation. The single point of failure is now (c), a re-proof, with conditions (P0) and (P1) and a check list (26.4).

> **Status (part 9, sections 27-28):** checks of (c) folded in (slack renamed `ψ`; `(1+β_0)^{−2}` in `c'_ψ`; (P2) with `log β`; (P1) kept as insurance; constant-size smallness only, for write-outs 2 and 4). Write-out 1, the coupling-form Dobrushin-Shlosman theorem (the Lean target), is written (section 28). Verdict: Lemma UV-TV has a complete paper-sketch argument given (c), with (a) and admissibility as citation-level readings; write-outs 2-4 remain.

> **Status (section 29):** write-out 2 (Lemma C's cross term and the collar coupling, which is also H3's Pinsker step) is written with constant-size smallness only. All smallness comes from decay across the collar. It uses Balaban's machinery on a domain with Dirichlet data, a citation-level adaptation.

> **Status (sections 30-32):** write-out 3 (front advance; `P(differ on B) ≤ C (t/ℓ)^{−d C_2}`, uniform in spacing and volume) and write-out 4 (H1 by positive gas, Kotecký-Preiss and van den Berg-Maes on polymer configurations) are written. All four write-outs are done. Lemma UV-TV has a complete argument written at paper level, given (c) and the citation-level readings (32).

> **Status (section 33):** small fixes after the reviews of 28 and 29: truncation as a case split; numbering; (B) by conditioning on in-support content near `A`; (I) obtained directly per in-support pair, without hybrids; contraction only inside `Λ''_j`; Dirichlet layers as unions of `L`-blocks; `E_0(M)` named; `q0 ≥ p0`.

> **Status (section 34 and final, section 32):** final fixes after the reviews of 30-32: one coupling for all sites; link-length truncation; units in `M`-cubes; van den Berg-Maes along links; the last kernel to the bare field; (B) built from three towers across a slab; NITs; the adaptation's domain class named. **Lemma UV-TV is complete at paper level**, given (c) and the named readings and adaptation (section 32).

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

# Part 6 (2026-11-22): section 12 completed, after REVIEW-2 (seventh follow-up) and REVIEW-3 (follow-up 6)

## 23. Fold-ins to section 21 (before section 12 relies on it)

### 23.0 Result in plain words

* **The size-cap gap is closed by capping the actual large set of each scale's field, using the law (annealed).**
  * Every coarse state in the tower is law-distributed: in (A) after the resample, and in (B) trivially. So the set
    where `X_{j+1}` is not small field can be bounded under the law, by Balaban's bounds at scale `j + 1`, without
    conditioning on anything coarser.
  * The truncation `T_{j+1}` caps its clusters at `n'_{j+1}` boxes.
  * Inherited regions at scale `j` are, by definition, only that set. So they never exceed `L^d n'_{j+1}` boxes,
    whatever happened at coarser scales.
  * **Persistence does not compound.** A region that stays bad over many scales is re-capped at every scale by that
    scale's own law.
  * This avoids any control of the fine field under large coarse data, which Balaban does not provide.
* **Bridging** (two inherited regions chained by born boxes across their birth gap) is a further truncation `G_j`,
  priced by the quenched H2 (REVIEW-3). Bridges have a minimum length set by the birth collars, so their number is
  subcritical.
* **Items 2-6** are folded in:
  * the condition with `g_j`;
  * polynomial tails with `C_2 > 1`;
  * the global coupling with the outside as a source;
  * the extra collar width `≳ r_int (log p)^{2d}/γ²`;
  * finer-born unreleased regions treated as born boxes.

### 23.1 The large set of each scale's field, capped under the law (persistence)

* **Annealed Peierls for the large set (H2a).** Under the law of `X_i` (scale `i`), for every finite set `A` of
  scale-`i` boxes, `P_law(X_i is not small field on every box of A) ≤ η_i^{|A|}`.
  * **Source:** Balaban's representation of `ρ_i`. A non-small `V_i` on `A` lies in large-field domains of every term,
    with the threshold outside the support of the characteristic functions (22.6).
  * The normalisation is that of 12.1 one scale up, or equivalently the scale-`i` one-more-step normalisation of 13.3.
  * **Annealed**, so no conditioning on coarser data is needed. It rests on the same unchecked adaptation, in its
    averaged form.
* **Truncation `T_i`:** some (proximity `2w_i + ℓ_B`) cluster of the large set of `X_i` or `X'_i` meeting `Λ''_i` has
  more than `n'_i := C_1 log|Λ''_i| / log(1/η_i)` boxes.
  * `P(T_i) ≤ 2|Λ''_i| Σ_{n > n'_i} (C (2w_i + ℓ_B)^d η_i)^n ≤ |Λ''_i|^{−C_2}`.
  * This holds because both copies are law-distributed. [Corrected in 24.3: the remark that the bound also holds
    conditionally on `𝓗` is dropped; (A) needs only the probability under the joint law.]
* **On `T_{j+1}^c`:** inherited regions at scale `j` (the coarse bad set `Bad^c(X_{j+1})`, which is contained in the
  large set of `X_{j+1}`) have clusters of `≤ L^d n'_{j+1}` scale-`j` boxes.
  * No recursion: the scale-`(j+1)` clusters may be larger, through their own inherited parts, but only the large set
    of `X_{j+1}` itself passes down.
* **Pricing in the multi-scale chain:** `Σ_i P(T_i) ≤ Σ_i |Λ''_i|^{−C_2}`, summable (23.5).

### 23.2 Bridging (mixed clusters)

* **Birth gap.** Two inherited pieces from different scale-`(j+1)` clusters are at least `2w_{j+1} + ℓ_B` scale-`(j+1)`
  units apart, that is at least `ℓ_gap,j := L (2w_{j+1} + ℓ_B) ℓ_B^{(j+1)}/ℓ_B^{(j)}` scale-`j` units.
* **A bridge** joining them at scale `j` is a born component (scale-`j` patterns and links, outside the inherited set)
  spanning that gap. It has `≥ ℓ_br := ℓ_gap,j/(2w_j + ℓ_B)` boxes.
* **Truncation `G_j`:** some cluster meeting `Λ''_j` contains more than `n_j` bridges.
  * By the quenched H2 (born boxes, outside the coarse bad set) and the min-trick,
    `P(G_j | 𝒳_{j+1}) ≤ |Λ''_j| (C (2w_j + ℓ_B)^d η_j^{1/2})^{ℓ_br n_j} ≤ |Λ''_j|^{−C_2}`.
* **On `F_j^c ∩ G_j^c ∩ T_{j+1}^c`:** every cluster in `Λ''_j` has at most
  `N_j := n_j (L^d n'_{j+1} + n_j + 1)` boxes. That is `n_j` bridges and born components, each `≤ n_j`, plus at most
  `n_j + 1` inherited pieces, each `≤ L^d n'_{j+1}`. `N_j` is logarithmic in `|Λ''_j|`.

### 23.3 Collar width and constants (items 2 and 5)

* **Collar:** `w_j := (3/m') log(C N_j p(g_j)) + C r_int (log p(g_j))^{2d}/γ²` (REVIEW-3's correction for constant
  multiplicity with overlapping good boxes). Both terms are logarithmic or polylogarithmic, and independent of cluster
  sizes.
* **Scale-local region bound** (item 2): `log|Λ''_j| = d log(t/(L^j a ℓ_B)) ≤ (d/b) g_j^{−2} + C(t)`, from the running
  coupling. Hence `log n_j, log N_j ≲ log g_j^{−2}` and `w_j ≲ (3/m') log g_j^{−2} + polylog(p)`.
* **Subcriticality:** `C (2w_j + ℓ_B)^d η_j^{1/2} < ½` becomes `c p0(g_j)/2 > d log log g_j^{−2} + C log log p`. This
  holds for `p0 = A0 (log g^{−2})^p`, any `p ≥ 1`, at `g_j ≤ γ0(L)`: a fixed condition on `γ0`.
  * 21.3's derivation with `g_0` is withdrawn: it inverted `p0(g_j)` versus `p0(g_0)` (both reviews).
  * As REVIEW-2 notes, Balaban's own `p0 ≫ M^d R^{d+1}` with `r ≥ 2` already forces a large exponent `p`.
* The constant tables in `S1-INDUCTION.md` (conditions 5 and 8) are updated accordingly.

### 23.4 Wording and scope (items 4 and 6)

* **Global coupling, outside as source** (REVIEW-2). Theorem A_good (coupling form, 22.5) is applied to the **whole**
  configuration. Everything outside `Λ''_j`, and every box where the truncation events would be needed, counts as a
  disagreement source at distance `≥ R'_j` from `B`.
  * Nothing is conditioned on fine configurations outside `Λ''_j`, so no unpenalised fine content enters near
    `∂Λ''_j`.
  * The truncation events are events of the patterns and of the coarse data, both priced.
* **Unreleased regions born at finer scales** lie inside `ω_j` and are priced by its weights (quenched H2). For the
  truncation they are born boxes. Their own birth collars are smaller than `w_j`, so they give no isolation. **Only the
  coarse bad set is inherited from above** (REVIEW-3).

### 23.5 The failure tail (item 3)

* Conclusion of Theorem A_good at scale `j`, given the coarser data, for the source at distance `R'_j` (scale-`j`
  units, boxes):
  `E[#disagreeing sites on B_j] ≤ C |B_j| e^{−λ_j R'_j/2} + C|B_j| (C' η_j^{1/2})^{R'_j/(4(ℓ_B + 2w_j))} + P(F_j ∪ G_j ∪ T_j ∪ T_{j+1})`.
  * The last term is `≤ 4|Λ''_j|^{−C_2}`.
* **The tail is polynomial in `R'_j`**, not exponential. That is enough:
  * with `C_2 > 1`, the sum over scales converges (23.6, 12.4);
  * OS density needs only `o(1)` (13.4).
* UV-TV (i) and 13.4 are restated with this tail. Exponential failure would need a merge range `~ log|Λ''|` and bring
  back REVIEW-3's stronger condition.

## 12 (continued, part 6). The multi-scale crossing estimate

### 12.2 H1: the pattern marginal as a positive dilute gas, and its uniqueness

* **The pattern marginal** given the coarse field is `w_ω(X_{j+1}) = ∫_{fibre} ρ^ω_j / ρ_{j+1}(X_{j+1})`, positive.
* **Polymers** `γ`: connected components, under proximity `r_int`, of the union of the discrete data of `ω`:
  * the domain history at scales `≤ j` (large-field domains, unreleased regions);
  * labels and Z2 excitations;
  * links.
  
  Admissibility (nesting, unions of cubes) is local inside each `γ`.
* **Weights.** Integrating the small-field fluctuations on the complement of `∪γ`, Balaban's cluster expansion of the
  small-field part gives
  `w_ω ∝ Π_γ z(γ) · exp(−Σ_{X meets ≥ 2 polymers} E(X))`, where:
  * the polymer activities `z(γ)` contain the `T`-activity, the single-polymer boundary terms, and the ratio to the
    small-field alternative;
  * by 12.1's comparison, `z(γ) ≤ η_j^{|γ|} e^{C|∂γ|}`, pointwise where the coarse field is small near `γ`;
  * the many-body terms come from `E`-terms meeting several polymers. Since polymers are separated by `> r_int`, those
    terms have `d(X) > r_int` and size `≤ C p² e^{−κ d(X)}`, which is small.
  * Inside the coarse bad set the pattern is part of the inherited composite box and plays no role in H1.
* **H1 (quantitative):** a **Dobrushin-uniqueness** statement for this dilute positive gas.
  * As a Gibbs field of box variables (the pattern restricted to each box), the influence of box `b'` on box `b`, in
    total variation of `b`'s conditional pattern law, is `≤ C η_j^{1/2} e^{−κ' dist(b, b')}`. Here `η_j` bounds the
    probability that `b` carries a polymer, and the many-body interactions bound the influence of far boxes.
  * Dobrushin's sum `Σ_{b'} C η_j^{1/2} e^{−κ' d} ≪ 1`, so uniqueness holds, with a coupling of the two copies' pattern
    marginals in which `P(ω_b ≠ ω'_b) ≤ C Σ_{b' ∈ S} (C η_j^{1/2})^{dist(b, b')/r_int}`. Here `S` is where the two
    specifications differ: near `D` and outside `Λ''_j`.
  * This is Dobrushin's comparison theorem in coupling form, the discrete case of 22.5.
* **Use in Theorem A_good.** Pattern disagreements become additional sources, with weight `P(ω_b ≠ ω'_b)`. This
  replaces H1's "agreement off `D`-connected bad chains" by a quantitative bound of the same effect.
* **Status: paper sketch.** The inputs are:
  * 12.1, the pointwise activity bound (one reading of Balaban to check);
  * Balaban's small-field cluster expansion for the interactions;
  * positivity.
  
  The single-scale Dobrushin argument for a dilute gas is standard. The polymers carry a whole domain history, but they
  are finite local objects, which changes nothing in the argument.

### 12.3 One scale of the tower

* **Input:** `(X_{j+1}, X'_{j+1})`, both law-distributed given the common σ-algebra of (A) or (B). Their disagreement
  set `D_{j+1}` is measurable in the coarser data.
* **Conditionally on `𝒳_{j+1}, 𝒳'_{j+1}`:**
  1. couple the patterns by 12.2;
  2. build the block family of 21 and 23 (composite boxes with collar `w_j`, inherited pieces from the large set of
     `X_{j+1}`, born clusters, bridges);
  3. apply the coupling-form Dobrushin-Shlosman theorem (22.5), with H3 on good boxes and Lemma C on composite boxes.
* **Sources:**
  * the image of `D_{j+1}`, enlarged by one box;
  * pattern disagreements;
  * `Λ''_j`'s outside;
  * the truncation events.
* **Output:** a coupling of `(X_j, X'_j)`, with:
  * `E[#disagreeing sites in N_r(B_j) | coarser] ≤ C |N_r(B_j)| Σ_{y ∈ sources} e^{−λ_j dist_ω(y, N_r(B_j))}`
    plus the failure term;
  * where `dist_ω` contracts composite boxes.

### 12.4 Chaining from `ℓ` down, and the result

* **Distances.** In scale-`j` units the initial distance is `R_j := L^{ℓ−j} R_ℓ`, with `R_ℓ := t/ℓ` scale-`ℓ` boxes.
  * At each scale the disagreement front advances by at most `a_j := C λ_j^{−1} log(|Λ''_j|)` boxes, except on events
    of probability `≤ |Λ''_j|^{−C_2}`.
  * `λ_j ≈ 1/ℓ_B` and `log|Λ''_j| ≲ g_j^{−2}` give `a_j ≲ ℓ_B g_j^{−2}`, polylog in `R_j`.
* **Front after `ℓ − j` steps.** The front's remaining distance at scale `j` is `≥ R_j − Σ_{i ≥ j} L^{i−j} a_i`, which is
  `≥ R_j/2` once `R_ℓ ≥ C ℓ_B g_ℓ^{−2}`. That holds when `t/ℓ` is large.
* **Contracted distance.** Composite boxes on the path shrink `dist_ω`:
  * born ones are priced by the quenched H2;
  * inherited ones by the annealed H2a;
  * covering half the path has probability `≤ e^{−c R_j/(ℓ_B + w_j)}` (21.5), for both kinds.
* **Result (UV-TV (i)_avg, tower form).** For (A) and (B), with `B` the support region of the fine observable (physical
  extent `R`) and `t` its distance to the source:
  `P(the fine fields differ on B) ≤ C Σ_{j=0}^{ℓ} [ |B_j| e^{−c R_j/(ℓ_B + w_j)} + |Λ''_j|^{−C_2 + 1} ]`.
* **Each term.**
  * The first sum is dominated by `j = ℓ`: `|B_ℓ| e^{−c t/(ℓ(ℓ_B + w_ℓ))}`.
  * The second: `|Λ''_j| ≈ (t/(L^j a ℓ_B))^d` grows as `j` decreases, so the sum is geometric. It is dominated by
    `j = ℓ`, `≈ (t/ℓ)^{−d(C_2 − 1)}`, for `C_2 > 1`.
* **Uniformity:**
  * in the spacing `a`: the sum over `j` converges geometrically from the top, with constants depending on `g_j` only;
  * in the volume: every quantity is local to `Λ''_j`.
* **So** `P(the fine fields differ on B) ≤ C(R/ℓ)^d e^{−c t/(ℓ polylog)} + C (t/ℓ)^{−d(C_2−1)}`, which tends to 0 as
  `ℓ → 0` at fixed `t > 0`.
  * This gives (A) and (B) of 13.4, hence `‖F − f_ℓ‖_OS → 0`: N-2's key step.

### 12.5 Status of section 12 and of Lemma UV-TV

| piece | level |
|---|---|
| fold-ins: persistence by annealed truncation `T_i` (23.1), bridging `G_j` (23.2), collar and condition with `g_j` (23.3), global coupling and wording (23.4), polynomial tail (23.5) | paper sketch |
| 12.1 pointwise fibre normalisation (quenched H2) | checked up to one reading of Balaban's normalisation terms |
| H2a, annealed large-set Peierls under the law at every scale | same adaptation, averaged form |
| 12.2 H1 via Dobrushin uniqueness of the dilute pattern gas | paper sketch |
| 12.3 one scale: Theorem A_good, coupling form, composite boxes | paper sketch (22.5 written; Lemma C sketch) |
| 12.4 chaining and the result | paper sketch |

**Overall.** Lemma UV-TV, and with it N-2's key step, has a complete argument at **paper-sketch level**, resting on:
1. **the unchecked adaptation:** Balaban's normalisation terms `E_k(Z)` are the Gaussian fibre normalisations of the
   small-field alternative. It is used pointwise (12.1) and averaged (H2a, R10);
2. **Balaban's small-field bounds** (citation): E-terms, the propagators with block constraints ([13] Theorems 3.12,
   3.13), the localisation;
3. **standard probabilistic tools:**
   * Dobrushin uniqueness for a dilute gas (12.2);
   * the coupling contraction (22.5);
   * lattice-animal counts.

**To write in full before Lean:**
* Lemma C's cross term with the fibre constraint and the analytic perturbation;
* 22.5 with composite boxes and the exact column condition;
* the front-advance estimate of 12.4;
* the H2a / 12.1 reading of Balaban's normalisation.

**Lean:** the coupling-contraction layer (22.5) is the generic theorem to formalise first.

**Not obstructed.** No step met a real obstruction in this part. The weakest points are the normalisation reading
(item 1), and Lemma C's cross term, which has not yet been written line by line.

# Part 7 (2026-11-22): per-cube Peierls, H1 at polymer level, and the verdict, after REVIEW-2 (eighth follow-up) and REVIEW-3 (follow-up 7)

## 24. Corrections

### 24.0 Result in plain words

1. **Per-unit rarity (REVIEW-3's GAP): fixed without a new reading.**
   * All Peierls bounds, truncations and subcriticality conditions are restated **per `M R_j`-cube**, with rate `κ`.
   * They use Balaban's activities already summed over internal structure ((1.97)). So no per-box entropy
     `C^{|N_A|}` appears.
   * The merge range (polylog in `log g^{−2}`) fits inside one cube (`M R_j ≥ M (log g_j^{−2})²`).
   * Subcriticality becomes the **fixed** condition `C 3^d e^{−c κ/2} < ½` on Balaban's `κ`, which he allows to be
     taken large ([III] p. 260).
   * The condition `p0 ≫ d log log g^{−2}` of 23.3 is superseded.
   * One refinement of the existing reading is needed, and stated: the small-field alternative's fibre integral on a
     region is at least `e^{−δ_j |region|}` times the Gaussian normalisation that Balaban's activities are normalised
     by, with `δ_j → 0`. This is part of the same normalisation reading, not a second one.
2. **H1:** box-variable Dobrushin is withdrawn (both reviews: a polymer crossing a face forces its continuation). It is
   replaced by the cluster expansion of the positive dilute polymer gas (Kotecký-Preiss after Mayer-expanding
   `e^{E} − 1`), with the coupling built on **polymer configurations** by disagreement percolation. This is write-out 4.
3. **Smaller corrections** (items 3-5):
   * the remark "conditionally on `𝓗`" is dropped;
   * the band of width `C w_j` around inherited pieces belongs to the inherited composite box;
   * admissibility is checked at the level of Balaban's definitions: delete **whole** history components.
4. **Verdict:**
   * the normalisation reading is a **single point of failure** for H2, H2a and R10;
   * the fallback, if it fails, is a per-cube margin `e^{−c p0}` surviving Balaban's entropy induction (a second
     reading), with the condition `p0 ≫ (M R)^d log β`, which his `p0 ≫ M^d R^{d+1}` covers;
   * four write-outs remain.

### 24.1 Peierls per `M R_j`-cube

* **The unit.** `Q_j`-cubes of side `M R_j` (scale-`j` units), Balaban's large-field grid. Bad sets are unions of
  `Q_j`-cubes: large-field domains are unions of `M R_j`-cubes, and labels, excitations and links are enlarged to the
  cubes they meet.
* **Quenched H2, per cube.** For a set `A` of `Q_j`-cubes, with `X_{j+1}` small field on the one-cube neighbourhood
  `N_A` of `A`:
  `w(A ⊂ Bad_j(ω) | X_{j+1}) ≤ e^{−2 p0(g_j) #comp(A)} (C e^{−c κ})^{|A|}`.
* **Proof (12.1 restated).**
  1. **Admissible completion (item 5).** For each `ω` with `A ⊂ Bad(ω)`, let `ω_0` be `ω` with **every connected
     component of its domain history meeting `N_A` deleted**, at all scales of that component.
     * Balaban's admissibility conditions ([III] (2.1)-(2.17): shapes of components inside `100 M R`-cubes, ages,
       nesting of the domains across scales, distance conditions between small-field domains and large-field regions)
       are either properties of a single history component or distance conditions that only relax when large-field
       regions are removed.
     * So `ω_0` is admissible. Checked at the level of the definitions as read; the scan of (2.3)-(2.9) is poor.
  2. **Ratio.** `Σ_{ω : A ⊂ Bad} w_ω/w_{ω_0} ≤ Σ_{polymers covering A} |F(X')| · e^{C c1 |∂N_A|} · e^{δ_j |N_A|}`, where:
     * the polymer sum uses Balaban's activities summed over internal structure, (1.97):
       `|F(X')| ≤ c1 e^{−(1+β) κ d(X')}`, with `c1 = e^{−p0}` per polymer and `d` in `Q_j`-cube units, conservatively;
     * the boundary terms (B-terms) are `O(c1)` per cube;
     * the denominator's small-field fibre integral on `N_A` is `≥ e^{−δ_j |N_A|}` times the Gaussian normalisation.
       This is the **refined reading**.
  3. **Bound.** Since `|N_A| ≤ 3^d (M R_j)^d |A|` sites and `δ_j (M R_j)^d → 0`, this is
     `≤ e^{−p0 #comp} (C e^{−c κ})^{|A|}`. ∎
* **The refined reading, stated.** On a region where the coarse field is small field, Balaban's small-field action,
  with his vacuum and normalisation constants subtracted, differs from the Gaussian quadratic form by field-dependent
  terms of size `≤ δ_j` per site, `δ_j → 0`. So the small-field fibre integral is `≥ e^{−δ_j |region|}` times the
  Gaussian fibre normalisation, and his `T`-activities are normalised by the same constants.
  * It is the same reading as before (13.3, 12.1), now with its small-field side made explicit.
* **H2a (annealed, per cube):** `P_law(X_i not small field on every cube of A) ≤ (C e^{−c κ})^{|A|}`. Same proof, with
  the denominator the law's normalisation one scale up (13.3).
* **Truncations, restated.**
  * `F_j` (born clusters), `G_j` (bridges) and `T_i` (large set) count `Q`-cubes.
  * `n_j := C_1 log|Λ''_j| / (c κ)`, and `P(F_j), P(G_j), P(T_i) ≤ |Λ''_j|^{−C_2}`.
  * **Merge range:** `2w_j + ℓ_B + 2r_int + 2` is polylog in `log g_j^{−2}`, so `≤ M R_j` at small `g`. Clusters are
    therefore cube-adjacency components (links as edges), with lattice-animal entropy `(3^d)^n`.
* **Subcriticality:** `3^d C e^{−c κ/2} < ½` (min-trick). A **fixed condition on `κ`**, added to `S1-INDUCTION.md`
  row 5. The condition on `p0` in 23.3 is superseded.
* **Sizes in boxes.** A cluster of `N_j` cubes, with
  `N_j := n_j (L^d n'_{j+1} + n_j + 1) (C w_j/(M R_j) + 1)^d`, is `≤ N_j (M R_j/ℓ_B)^d` boxes.
  * The last factor of `N_j` is the inherited band of item 4.
  * **Collar:** `w_j := (3/m') log(C N_j (M R_j)^d p) + C r_int (log p)^{2d}/γ²`. Still `≪ M R_j`.
* **Path cost and the chaining.**
  * Covering half a path of length `D` (scale-`j` units) needs `≥ D/(C M R_j)` bad cubes. Its probability is
    `≤ (C e^{−c κ/2})^{D/(C M R_j)}`.
  * The chaining of 12.4 then gives `P(differ on B) ≤ C (R/ℓ)^d e^{−c κ t/(ℓ M R_ℓ polylog)} + C (t/ℓ)^{−d(C_2−1)}`. The
    rate carries `M R_ℓ`, as REVIEW-3 checked; harmless.

### 24.2 H1 at the polymer level (write-out 4)

* **The gas.** Polymers `γ` are connected components of the discrete data (domain history, labels, excitations,
  links) under `Q_j`-cube adjacency.
  * Activities: `z(γ) ≤ e^{−p0} (C e^{−c κ})^{#cubes(γ)}` (24.1), where the coarse field is small field. Near or inside
    the coarse bad set, the pattern belongs to the inherited composite box or the source (REVIEW-3).
* **The effective interaction** (REVIEW-3's correction). It is
  `log ∫ Π_γ (polymer measure) e^{Σ_X E(X)} − Σ_γ log z(γ)`, because the cluster terms meeting several polymers depend
  on boundary fields integrated inside the `T`-operations.
  * Mayer-expanding `e^{E(X)} − 1` for `X` meeting `≥ 2` polymers gives links of size `≤ C p² e^{−κ d(X)}`.
* **Tool.**
  * **Correlations:** Kotecký-Preiss for the hard-core gas of polymers plus Mayer links converges for `κ` large (the
    same condition as 24.1). It gives decay of local pattern correlations, and a comparison of two gases whose
    activities or interactions differ only on a set `S`, through clusters joining a box to `S`.
  * **The coupling:** disagreement percolation on polymer configurations. Couple the two gases polymer-cluster by
    polymer-cluster, from `S` inward. A disagreement can only propagate through a chain of polymers and Mayer links
    joined to `S`, each priced by its activity.
  * **Result:** `P(ω_b ≠ ω'_b) ≤ C Σ_{b' ∈ S} (C e^{−c κ/2})^{dist(b, b')/(M R_j)}`.
* **No supremum over boundary patterns is used**, so the forced-continuation problem does not arise.
* **Status:** standard tools; to be written out. This is write-out 4.

### 24.3 Smaller items

* **Item 3.** 23.1's remark that the annealed bound "applies conditionally on `𝓗` too" is **dropped**. (A) is an `L¹`
  statement, so the failure events need only their probability under the joint law.
  * The `T_i` are taken over the deterministic ball of radius `R_i` around `B`, which contains `Λ''_i`. Every coarse
    state in the tower is law-distributed by induction (REVIEW-3, follow-up 7 (1)).
* **Item 4.** Born boxes within `C w_j` of an inherited piece are not priced by the quenched H2. That band is part of
  the inherited composite box (factor in `N_j`, 24.1).
* **Item 5.** Admissibility: 24.1 step 1.
* **REVIEW-2's nit on `N_j`.** Born clusters attached to one inherited piece are bounded by the piece's boundary. So
  `N_j ≲ n_j² L^d n'_{j+1}` up to the band factor; only `log N_j` enters `w_j`.

## 25. The verdict for Lemma UV-TV and N-2 (superseded by "25 (revised)" in part 8 below)

**Argument.** N-2's key step, Lemma UV-TV, has a complete argument at paper-sketch level (`UV-TV.md` 8-12, 16, 21-24).

**Single point of failure.** The **normalisation reading** carries the quenched H2 (12.1, 24.1), the annealed H2a
(23.1, 24.1) and R10's scale-`K` normalisation (`REVIEW3-RESPONSE.md` 7, 13.3) at once. The reading:
* Balaban's normalisation terms `E_k(Z)` ((1.70)-(1.71)) are the Gaussian fibre normalisations of the small-field
  alternative;
* and the small-field alternative's fibre integral is `≥ e^{−δ|region|}` times them.

**Fallback if it fails.**
* Each region then loses the top variables' Gaussian normalisation, about `β^{3/2}` per bond, so
  `exp(C (M R_j)^d log β)` per `Q_j`-cube.
* Rate `κ` per cube cannot absorb that.
* It is absorbed only by a **per-cube margin** `e^{−c p0}` that survives Balaban's entropy induction ((1.80)-(1.89)),
  under the condition `c p0 ≥ C (M R_j)^d log β`. His choice `p0 ≫ M^d R^{d+1}` with `R ≥ log g^{−2} ≥ log β` covers
  this.
* That margin is a **second reading** of [V] (1.80)-(1.89): (1.89) states only a per-component `p0` and `κ` per unit
  of linear size.
* **So at least one of the two readings must hold.** The first is preferred and needs nothing more.

**Write-outs still owed** (before Lean):
1. Lemma C's cross term, with the fibre constraint and the analytic perturbation (16).
2. The coupling-form Dobrushin-Shlosman theorem with composite boxes and the exact per-site column condition (22.5).
3. The front-advance estimate of the chaining (12.4).
4. H1 by cluster expansion and disagreement percolation on polymer configurations (24.2).

**Lean:** the coupling-contraction layer (22.5) is the generic theorem to formalise first.

# Part 8 (2026-11-22): the strengthened induction (c), after `../m1-review/EK-DERIVATION.md`, REVIEW-2 (ninth follow-up) and REVIEW-3 (follow-up 8)

## 26. Balaban's [V] (1.80)-(1.97) with a retained slack

Brief: re-prove [V] (1.80)-(1.97) so that it keeps a slack `e^{−c p0²}` per birth-scale `M R`-cube. Go line by line
against the source, naming where (1.92)-(1.97) must give up less entropy. This replaces readings (a) + (b) as the main
route. Stop where it fails. Source: [V] pp. 383-390, text layer; `EK-DERIVATION.md` Q2 for equations read from the page
images.

### 26.0 Result in plain words

* **It goes through. No step fails.**
  * The creation gain of a large-field region is `γ_0 A_1² p0²(g_j)` per unit of linear size `d'_j` ([V] p. 381; (1.79),
    (1.82)).
  * Split it in two halves:
    * one half pays Balaban's own induction (`κ_j(Z)`), exactly as he does, under his condition after (1.82) with the
      constant doubled;
    * the other half is kept as a **slack** `ψ_j(Z)`, which is never spent.
* **The slack only adds:**
  * it is unchanged in (1.83), where no new large field appears;
  * in the merging step (1.85)-(1.88) it is the sum over the merged parts;
  * it is untouched by the costs, which Balaban charges to `κ` alone.
* **At release**, (1.89) becomes `T'_k(X) 1 ≤ e^{−ψ_k(X)} e^{−2(1+β_0)^{−1} p0(g_k)}`.
* **In the polymer step (1.92)-(1.97)** the factor `Π_h e^{−ψ_k(X_{j_h})}` is carried **outside** Balaban's entropy
  sums. He spends only `e^{−q p0/2}`, from the per-component `p0`, on the sum over `q` and the positions (1.96). So
  nothing of the slack needs to be given up.
* **Result** (1.97'): activities `F_A(X')` restricted to decompositions whose large-field regions cover a set `A` of
  current-scale cubes satisfy
  `|F_A(X')| ≤ c1 e^{−(1+β) κ d_k(X')} e^{−c_ψ p0²(g_k) |A|}`.
* **That replaces reading (b).** The denominator's `O(1)`-per-site loss in 12.1 and 24.1 (`[III]` Theorem 2) is
  `≤ C (M R_k)^d` per cube, and the slack absorbs it under (P2) below, which Balaban's own condition implies.
* **One added parameter condition (P1)**, for regions whose only gain is the preparatory `e^{−p0}`:
  `p0(g) ≥ C (κ + M^d) 100^d R(g)^d`. Same form as his condition after (1.94), `p0 ≳ 8κ 100^d R^d`, with `κ` replaced
  by `κ + C M^d`.
* **Level: paper (a re-proof).** Every change is local to a named equation.

### 26.1 The statement

* **Balaban's statement** (1.80), as read in `EK-DERIVATION.md` Q2: for a component `Z` of `Z_j`, write its factor in
  (1.79) as `exp(−κ_j(Z) − 2 p0(g_{j(Z)}))`. Then
  `κ_j(Z) ≥ Σ_{n=j+1}^{j+K} O(1) M^d R_n^{d+1} d'_n(S^{n−j}(Z))`,
  with `K` the number of further steps until `S^K(Z)` satisfies (i), (ii).
* **Strengthened statement (1.80').** Write the factor as `exp(−κ_j(Z) − ψ_j(Z) − 2 p0(g_{j(Z)}))`, with `ψ_j(Z) ≥ 0`.
  Then:
  * **(κ)** `κ_j(Z)` satisfies (1.80) as stated;
  * **(ψ)** `ψ_j(Z) ≥ c_ψ Σ_{b ∈ births(Z)} p0²(g_{j_b}) (d'_{j_b}(Z_b) + 1)`, summed over the large-field regions `Z_b`
    created by (1.76) at scales `j_b ≤ j` that were absorbed into `Z`. Here `c_ψ := ⅛ γ_0 (14)^{−d} A_1²`.
* The units of (ψ) are **birth-scale** `M R_{j_b}`-cubes (REVIEW-2, REVIEW-3, `EK-DERIVATION.md`).

### 26.2 The induction, equation by equation

1. **Creation** ([V] p. 381, (1.79)).
   * Each new component `Z_j^{(i)}` carries
     `exp(−½ γ_0 A_1² p0²(g_j)(d'_j(Z_j^{(i)}) + 1) − 2 p0(g_j))`.
   * Unchanged. It is the source of both halves.
2. **The first step, `j = 1`** ((1.82)).
   * Balaban: `κ_1(Z) ≥ ¼ γ_0 (14)^{−d} A_1² p0²(g_1)(d'_1(Z) + 1) − O(1) M^d R_1^{d+1} d'_1(Z)`. The `(14)^{−d}` comes
     from covering `Z` by the regions `(Z_1^{(i)})^{~3}` of (1.76).
   * **Split:** assign `c_ψ p0²(g_1)(d'_1(Z) + 1)` (half of the first term) to `ψ_1(Z)`, and the rest to `κ_1(Z)`. Then
     `κ_1(Z) ≥ ⅛ γ_0 (14)^{−d} A_1² p0²(g_1)(d'_1(Z) + 1) − O(1) M^d R_1^{d+1} d'_1(Z)`.
   * By (1.81), the right-hand side of (1.80) is `≤ O(1)(64)^d M^d L^{d+1} R_1^{d+2}(d'_1(Z) + 1)`.
   * **Condition (P0)** (Balaban's condition after (1.82), with the constant doubled):
     `⅛ γ_0 (14)^{−d} A_1² p0²(g_1) ≥ O(1) 2(64)^d M^d L^{d+1} R_1^{d+2}`.
     "Satisfied for `p0` large and `g_1` sufficiently small", as his is: both sides are powers of `log g^{−2}`, and his
     condition already makes the left exponent win.
   * (ψ) holds by definition.
3. **No new large field** ((1.83), first case).
   * `κ_{j+1}(Z) = κ_j(Z_0) − O(1) M^d R_{j+1}^{d+1} d'_{j+1}(Z)` with `Z = S(Z_0)`.
   * **Set `ψ_{j+1}(Z) := ψ_j(Z_0)`.** The births are the same, so (ψ) holds. (κ) holds as in Balaban.
4. **A new large field in the preparatory operations** ((1.83), second case).
   * `Z = S(Z_0)`, with `Z_0` satisfying (i), (ii). Balaban sets `κ_{j+1}(Z) := p0(g_j) − O(1) M^d R_{j+1}^{d+1} d'_{j+1}(Z)`
     from the factor `e^{−p0(g_j)}` of (1.79)'s last product. `Z` is small: contained in a `100 M R_{j+1}`-cube.
   * **Set `ψ_{j+1}(Z) := ψ_j(Z_0)`.** The old slack is kept, since `Z_0`'s factor `e^{−ψ_j(Z_0)}` is still in the
     product.
   * The preparatory large field brings only `e^{−p0}`, no `p0²`. This is the one place where condition (P1) of 26.3 is
     needed.
5. **Merging** ((1.84)-(1.88)).
   * Balaban (1.85) defines `κ_{j+1}(Z)` by summing:
     * the components' `κ_j(Z^{(n)}) + 2 p0(g_{j(Z^{(n)})})`;
     * the new regions' `γ_0 A_1² p0²(g_{j+1})(d'_{j+1}(Z^{(i)}_{j+1}) + 1) + 2 p0(g_{j+1})`;
     * minus `O(1) M^d R_{j+1}^{d+1} d'_{j+1}(Z)` and `2 p0(g_{j(Z)})`.
   * **Split the new regions' term:** `c_ψ p0²(g_{j+1})(d'_{j+1} + 1)` goes to `ψ`, the rest to `κ`. Set
     `ψ_{j+1}(Z) := Σ_n ψ_j(Z^{(n)}) + Σ_i c_ψ p0²(g_{j+1})(d'_{j+1}(Z^{(i)}_{j+1}) + 1)`, so (ψ) holds.
   * **The κ part.** Balaban's tree induction (1.86)-(1.88) uses:
     * the surplus `2p0(g_{j(X)}) + 2p0(g_{j(Y)}) − 2p0(g_{j(Z)}) ≥ 2(1+β_0)^{−1} p0(g_{j+1})`;
     * the `κ`'s of the parts;
     * the new regions' `p0²` terms, through their `κ_{j+1}(X)` for single new regions, as in the first step.
     
     With the new regions carrying half of the `p0²` term, the single-region case is the first step with condition
     (P0). The rest of (1.86)-(1.88) is unchanged, since it only adds the parts' `κ` and uses the `p0` surplus.
6. **Release** ((1.89)).
   * Balaban: `κ_k(X) ≥ 0`, hence `T'_k(X) 1 ≤ exp(−2(1+β_0)^{−1} p0(g_k))`.
   * **With the slack:** `T'_k(X) 1 ≤ exp(−ψ_k(X) − 2(1+β_0)^{−1} p0(g_k))`.
7. **Activities** ((1.90)-(1.97)).
   * (1.92) bounds each activity by a product over the `q` factors `T'_k(X_{j_h})`, each
     `≤ exp(−2(1+β_0)^{−1} p0(g_k) + 1)` by (1.89), times boundary and Mayer terms.
   * **Keep `Π_h e^{−ψ_k(X_{j_h})}` as an extra factor**, and do not use it in any of the following steps:
     * the bound (1.93) on the boundary terms;
     * the payment `2(100 R_k)^d` per factor (p. 389), which uses `−2(1+β_0)^{−1} p0 + 1 + 2(100R_k)^d ≤ −(3/2)p0`;
     * the sum (1.96) over `q` and positions, which spends `e^{−q p0/2}`.
   * Those steps spend only the per-component `p0`, never `p0²`. **This is where (1.92)-(1.97) "gives up less entropy":
     it gives up nothing of `ψ`.** The only change is that the factor `e^{−ψ}` passes through.
   * **Converting to the current scale.** For a decomposition whose regions `X_{j_h}` cover a set `A` of current-scale
     `M R_k`-cubes:
     * `|A| ≤ Σ_h #cubes_k(X_{j_h}) ≤ Σ_h (d'_k(X_{j_h}) + 1)`;
     * by (1.81)'s scaling, `d'_k(S^{k−j}(Z)) ≤ 2^{−(k−j)} d'_j(Z) + (64)^d`, so `#cubes_k ≤ C Σ_b (d'_{j_b} + 1)`;
     * `p0(g_{j_b}) ≥ p0(g_k)` since `g_{j_b} ≤ g_k`;
     * hence `Σ_h ψ_k(X_{j_h}) ≥ (c_ψ/C) p0²(g_k) |A|`.
   * **Result (1.97').** `|F_A(X')| ≤ c1 e^{−(1+β) κ d_k(X')} e^{−c'_ψ p0²(g_k) |A|}`, with `c'_ψ := c_ψ/C`.
   * The sup over admissible internal histories in (1.79) is harmless: every history inside a released component `X`
     creates the births that make `X`, and the bound on `|A|` holds for each.
8. **R- and B-terms** ((1.98)-(1.100)). Unchanged. The slack is needed only for the activities covering `A` in H2,
   H2a and R10, not for the exponentiated terms.

### 26.3 The conditions, and where the slack is spent in M1

* **(P0)** `⅛ γ_0 (14)^{−d} A_1² p0²(g) ≥ O(1) 2(64)^d M^d L^{d+1} R(g)^{d+2}`: Balaban's condition after (1.82), with the
  constant doubled.
  * As `EK-DERIVATION.md` corrects: the condition is on `p0²`, `A_1² p0² ≳ M^d L^{d+1} R^{d+2}`, not
    "`p0 ≫ M^d R^{d+1}`".
* **(P1)** `p0(g) ≥ C (κ + M^d) 100^d R(g)^d`, for the regions of step 4 (single small regions with gain `e^{−p0}`
  only). The denominator loss on such a region (`≤ 100^d` cubes) is `C 100^d (M R)^d`.
  * Same form as Balaban's p. 389 condition `p0 ≳ 8κ 100^d R^d`, which already forces the `log g^{−2}`-exponent of
    `p0` to be at least `r d`.
  * With that, (P1) holds for `g` small, or with `A0 ≥ C M^d`. `A0` is chosen after `M` ([III]: "`A0` much larger").
* **(P2)** `c'_ψ p0²(g_k) ≥ 2C 3^d (M R_k)^d`: absorbs the denominator loss `O(1)` per site on the one-cube
  neighbourhood `N_A` ([III] Theorem 2). It follows from (P0), since `L^{d+1} R^{d+2} ≥ R^d`.
* **Where the slack is spent:**
  * **12.1 and 24.1 (quenched H2):** the ratio is now `≤ e^{−p0 #comp} (C e^{−c κ})^{|A|} · e^{−c'_ψ p0² |A|} ·
    e^{C 3^d (M R)^d |A|}`, which is `≤ e^{−p0 #comp}(C e^{−c κ})^{|A|}` by (P2). The denominator uses only
    `[III]` Theorem 2's `O(1)` per site. **Reading (b) is no longer needed.**
  * **H2a (23.1, 24.1) and R10's scale-`K` normalisation (13.3):** the same, one scale up.
  * **Reading (a)** (what `E_k(Z)` is) is still used to know that the numerator's `T'_k` is normalised against the same
    constants as the small-field alternative. `EK-DERIVATION.md` Q1 confirms it in substance.

### 26.4 What the reviewers should check

1. The split in step 2: whether (1.82)'s first term can be halved, with (1.81) then needing (P0).
2. Step 5: that Balaban's tree argument (1.86)-(1.88) uses only the parts' `κ` and the `p0` surplus, so that halving the
   new regions' `p0²` term only invokes (P0) again.
3. Step 7: that no inequality in (1.92)-(1.96) uses (1.89)'s `κ_k ≥ 0` in a form that would need `ψ`.
4. The conversion to current-scale cubes, and the sup over internal histories (step 7).
5. (P1)'s compatibility with Balaban's exponent chain ([V] p. 383, `2p_1 − (d+5) r_0 > p_0`), which may need `p_1`
   raised with `p_0`.

## 25 (revised). The verdict for Lemma UV-TV and N-2

**Argument.** N-2's key step, Lemma UV-TV, has a complete argument at paper-sketch level (`UV-TV.md` 8-12, 16, 21-24,
26), **given the strengthened induction (c) of section 26**.

**What it rests on:**
* **(c) the strengthened induction** (section 26): a **re-proof** of [V] (1.80)-(1.97) with a retained slack
  `e^{−c p0²}` per birth-scale cube. It needs (P0) (Balaban's condition with the constant doubled) and (P1) (his
  p. 389 condition with `κ → κ + C M^d`). **This is now the single point of failure**, and it is a re-proof, not a
  reading.
* **(a) what `E_k(Z)` is: holds in substance**, as a citation-level reading (`EK-DERIVATION.md` Q1).
  * It is the small-field alternative's logged normalisation **and vacuum-energy** constants at background 1:
    * the constrained Gaussian determinant;
    * the Haar Jacobians;
    * the gauge-fixing and δ-elimination constants;
    * the non-Gaussian vacuum values;
    
    localised on domains meeting `Z`. "Gaussian fibre normalisation" was too narrow.
  * The `β^{3/2}`-per-bond factor is the Haar Jacobian `σ_0 g^{d(g)}`. It is inside `E_k(Z)` and already paid in (1.79),
    so **there is no leftover per bond**. The fallback analysis of the earlier section 25 ("each region loses about
    `β^{3/2}` per bond") is withdrawn.
* **(b) the lower bound `≥ e^{−δ|region|}` with `δ → 0`: not available from Balaban**. His field-dependent small-field
  terms are bounded only `O(1)` per site ([III] Theorem 2). **It is no longer needed**: the slack of (c) absorbs the
  `O(1)`-per-site loss (P2).
* **`κ` large for fixed `L`: a citation** ([I] Theorem 3; [III] p. 260). It costs a larger `M` (`M ≥ M(κ)`, `δ_0 M ≥ κ`
  for the Gaussian part) and a smaller coupling bound `γ`. The absolute constant `γ_0` is not affected
  (`EK-DERIVATION.md` Q3; REVIEW-2 ninth follow-up).
  * It enters every subcriticality condition, the Kotecký-Preiss condition of H1, and the tail. With the compatibility
    range of 26.5 the condition is `C 200^d e^{−c κ/2} < ½`.
  * Any M1 constant hiding `e^{O(κ)}` or `M^q` must be checked against the same `κ` (`EK-DERIVATION.md` Q3).
* **Admissibility** (24.1, step 1): checked against the definitions as read, from a poor scan of [III] (2.3)-(2.9). Low
  risk; listed with the readings.

**Wording** (27.10, updated 33.7): Lemma UV-TV has a complete argument given (c), with three citation-level
readings: (a), admissibility, and Balaban's machinery on non-admissible (thin, cluster-shaped) domains. The four
write-outs are done (28-31).

**Dependency added** (27.9): Lemma C's cross term and the Pinsker step use only Balaban's constant-size smallness
(`O(1)` per site, or a constant per `M`-cube from analyticity) and his cluster expansion, never `δ → 0`.

**Write-outs** (numbered as in 27.9 and 28-31; all four are now written):
1. The coupling-form Dobrushin-Shlosman theorem with composite boxes and the exact per-site column condition (28).
2. Lemma C's cross term, with the fibre constraint and the analytic perturbation (29).
3. The front-advance estimate of the chaining (30).
4. H1 by cluster expansion and polymer-level disagreement percolation (26.5, 31).

**Plus (c)'s check list (26.4)**, for the reviewers.

## 26.5 H1: the reviewers' NITs folded in

* **Compatibility range** (REVIEW-3). Balaban's admissibility includes distance conditions (component shapes inside
  `100 M R`-cubes, the merging rules). So two history components within about `100` cubes of each other are not freely
  compatible.
  * Define polymer compatibility at that range: two polymers are compatible only if they are more than `100` cubes
    apart.
  * The hard core's entropy is then `(C 200^d)^n`, absorbed by `κ`: the condition `C 200^d e^{−c κ/2} < ½`.
* **Positive split** (REVIEW-3). The many-body interactions are decomposed as `e^{E(X)} = e^{m_X}(1 + h_X)` with
  `h_X ≥ 0`, as for the long links (10.1), not Mayer-expanded into the signed `e^{E} − 1`.
  * Then the gas, including its links, is a **positive** mixture over link sets, and disagreement percolation on polymer
    configurations has positive weights throughout.
  * The cluster expansion for correlations may still use `e^{E} − 1`; the coupling uses the positive split.
* **Admissibility caveat:** the deletion argument (24.1, step 1) was checked against the definitions as read from a poor
  scan of [III] (2.3)-(2.9).

# Part 9 (2026-11-23): fold-ins after the checks of (c), and write-out 1

## 27. Fold-ins after the three checks of (c)

Sources:
* `../m1-review/EK-DERIVATION.md`, "Re-proof check" (independent reader, page images);
* REVIEW-2, tenth follow-up;
* REVIEW-3, follow-up 9.

All three: (c) goes through, with no step failing.

1. **The slack is renamed `ψ`** (it was `σ`, which clashes with Balaban's `σ` in (1.73)-(1.75) and `σ_0` in the Haar
   density). Section 26 now uses `ψ_j(Z)`, `c_ψ`, `c'_ψ` throughout.
2. **Step 5, the new regions' term.** It is `½ γ_0 A_1² p0²(g_{j+1})(d'_{j+1} + 1)`, matching the creation factor on
   p. 381. The source prints `γ_0` without the `½` in (1.85), which conflicts with p. 381. Half of it, `c_ψ`-sized, goes
   to `ψ`, as in step 2.
3. **Birth-scale versus current coupling.** [III] (2.6)-(2.7) give only `g_birth ≤ (1+β_0) g_k`. So
   `p0(g_birth) ≥ (1+β_0)^{−1} p0(g_k)`, not `≥ p0(g_k)`. Hence `c'_ψ := c_ψ (1+β_0)^{−2}/C` in (1.97'). The factor is a
   fixed constant, and (P2) absorbs it.
4. **Regions not yet released** (inside `T`-operations at scale `j`, used in H2a and in the band of 23.1) take their
   slack from (1.79) and (1.80'), the factor `e^{−ψ_j(Z)}` of the unreleased component, not from (1.97') (independent
   reader, REVIEW-3).
5. **(P1), kept as insurance**, with a note:
   * preparatory large fields carry only `e^{−p0}` (REVIEW-2);
   * but every region descends from a creation event and inherits that event's slack (REVIEW-3), so in the main case
     (P1) is not needed;
   * this rests on preparatory domains staying inside `S(Z_0)` ([V] p. 384; [IV] Sect. 1 not re-read).
6. **The deletion footprint** (REVIEW-3). In 24.1 step 1, the comparison deletes whole history components meeting
   `N_A`. The denominator loss then falls on their whole current footprint, not only on `N_A`.
   * It is covered by the deleted components' own slack, `c'_ψ p0²` per current cube of their footprint, against
     `C (M R)^d` per cube.
   * The `3^d` in (P2) covers the one-cube neighbourhood.
7. **The current top variables' Gaussian normalisation** (REVIEW-3). In the fibre integral over `V_j` on the region,
   the normalisation of the top variables, about `β^{3/2}` per bond, is the **next** step's constant, not part of
   `E_k`. (P2) is stated with an extra `log β` per site:
   `c'_ψ p0²(g_k) ≥ C 3^d (M R_k)^d (1 + log β_k)`.
   It still follows from (P0), since `R ≥ log g^{−2} ≥ log β` gives `(M R)^d log β ≤ M^d R^{d+1} ≤ M^d L^{d+1} R^{d+2}`.
   This replaces citing Balaban's reserve for the next step.
8. **Constants table** (`S1-INDUCTION.md` 1, REVIEW-3):
   * `ℓ_B` depends on `p(g)`, so its condition moves from row 5 to row 6, below the row where `p(g)` is fixed;
   * the Dobrushin-Shlosman contraction constant is renamed `γ_DS < 1`, so it is not confused with Balaban's coupling
     bound `γ`.
9. **Constant-size smallness only** (REVIEW-2). Lemma C's cross term (16) and the Pinsker step of H3 (19) may use only:
   * Balaban's constant-size smallness: `O(1)` per site ([III] Theorem 2), or a constant per `M`-cube from analyticity
     (`EK-DERIVATION.md` Q4);
   * the explicit `O(g^{1−β})` per site of the cubic Wilson terms ([V] (1.2));
   * his cluster expansion.
   
   They may **not** use a "`1 + O(δ)`, `δ → 0`" for the inherited E-terms. Write-outs 2 and 4 are written accordingly.
   This is now on the dependency list (25, revised).
10. **Verdict wording** (25, revised): "Lemma UV-TV has a complete paper-sketch argument given (c), with (a) and
    admissibility as citation-level readings; four write-outs remain."

## 28. Write-out 1: the coupling-form Dobrushin-Shlosman theorem (generic; the Lean target)

### 28.1 Statement

**Data.**
* A finite set `Λ` of sites, measurable spaces `(S_x)_{x ∈ Λ}`, and `Ω := Π_x S_x` with the product σ-algebra.
* Two probability measures `μ, μ'` on `Ω`, with measurable sets `Ω_0, Ω'_0` of full measure (the supports).
* A finite family (a multiset) of blocks `B_b ⊂ Λ`, `b ∈ 𝔅`, `N := |𝔅|`. The coverage `c(x) := #{b : x ∈ B_b}`
  satisfies `c(x) ≥ c_min ≥ 1`.
* A partition `𝔅 = 𝔅_good ⊔ 𝔅_src` (good blocks and source blocks).
* Site weights `v : Λ → (0, ∞)`.
* Numbers `K_b(z) ≥ 0` for `b ∈ 𝔅_good`, `z ∉ B_b`.
* A constant `γ ∈ [0, 1)` (this is `γ_DS`).

**Hypotheses.**
* **(S) Specifications.** For each block `b` there are probability kernels `q_b, q'_b : Ω → Prob(Ω)` such that:
  * `q_b(σ, ·)` is supported on `{ξ : ξ = σ off B_b}` and depends only on `σ` off `B_b`;
  * `μ q_b = μ` (DLR);
  * `q_b(σ, Ω_0) = 1` for `σ ∈ Ω_0`;
  * the same for `q'_b`, `μ'` and `Ω'_0`.
* **(C) Block couplings.** For each block `b` there is a kernel `Q_b : Ω × Ω → Prob(Ω × Ω)` whose marginals are
  `q_b(σ, ·)` and `q'_b(σ', ·)` for every `(σ, σ') ∈ Ω_0 × Ω'_0`.
* **(I) Influence on good blocks.** For `b ∈ 𝔅_good` and `(σ, σ') ∈ Ω_0 × Ω'_0`:
  `Σ_{y ∈ B_b} v(y) Q_b((σ, σ'), {ξ_y ≠ ξ'_y}) ≤ Σ_{z ∉ B_b} 1{σ_z ≠ σ'_z} K_b(z) v(z)`.
  * **In particular**, if `σ = σ'` off `B_b`, the updated pair agrees on `B_b` almost surely.
* **(K) The column condition.** For every site `z`: `Σ_{b ∈ 𝔅_good, z ∉ B_b} K_b(z) ≤ γ c(z)`.

**Conclusion.** For every `ε > 0` there is a coupling `π` of `μ` and `μ'` with
`Σ_x v(x) π(Y_x ≠ Y'_x) ≤ s/((1 − γ) c_min) + ε`, where `s := Σ_{b ∈ 𝔅_src} Σ_{y ∈ B_b} v(y)`.

**Consequence.** For bounded measurable `F` depending on the coordinates in `A ⊂ Λ`:
`|μ(F) − μ'(F)| ≤ 2‖F‖_∞ (min_A v)^{−1} s/((1 − γ) c_min)`.

### 28.2 Proof

1. **The averaged update.** For a coupling `π` of `μ, μ'` supported on `Ω_0 × Ω'_0`, define
   `T π := (1/N) Σ_b ∫ π(dσ, dσ') Q_b((σ, σ'), ·)`.
   * **Marginals.** The first marginal is `(1/N) Σ_b μ q_b = μ` by (S), the second `μ'`. So `T π` is again a coupling.
   * **Support.** By (S) and (C), `T π` is supported on `Ω_0 × Ω'_0`. So (I) applies at every later step, and **no
     configuration outside the supports is ever used**.
2. **One step.** Write `d(x) := π(Y_x ≠ Y'_x)` and `Φ(π) := Σ_x v(x) d(x)`. For a block `b`:
   * sites outside `B_b` keep their pair, contributing `Σ_{x ∉ B_b} v(x) d(x)`;
   * for `b ∈ 𝔅_good`, integrating (I) over `π`: `Σ_{y ∈ B_b} v(y) P(new pair differs at y) ≤ Σ_{z ∉ B_b} d(z) K_b(z) v(z)`;
   * for `b ∈ 𝔅_src`, at most `Σ_{y ∈ B_b} v(y)`.
3. **Average over blocks:**
   `Φ(Tπ) ≤ (1/N)[Σ_x v(x) d(x)(N − c(x)) + Σ_{b good} Σ_{z ∉ B_b} d(z) K_b(z) v(z) + s]`.
   By (K), the middle sum is `≤ Σ_z v(z) d(z) γ c(z)`, so
   `Φ(Tπ) ≤ Φ(π) − (1/N)(1 − γ) Σ_x c(x) v(x) d(x) + s/N ≤ θ Φ(π) + s/N`, with `θ := 1 − (1 − γ) c_min/N < 1`.
4. **Iterate.** Start from the product coupling `π_0 := μ ⊗ μ'`, which is supported on `Ω_0 × Ω'_0`. Then
   `Φ(T^n π_0) ≤ θ^n Φ(π_0) + s/((1 − γ) c_min)` and `Φ(π_0) ≤ Σ_x v(x) < ∞` (`Λ` is finite). Take `n` large. ∎
5. **Consequence.** `|μ(F) − μ'(F)| = |E_π[F(Y) − F(Y')]| ≤ 2‖F‖_∞ π(Y ≠ Y' on A)`, and
   `π(Y ≠ Y' on A) ≤ Σ_{x ∈ A} d(x) ≤ (min_A v)^{−1} Φ(π)`. Let `ε → 0`.

**Remarks.**
* **No limit in time and no topology.** The conclusion holds up to `ε` for a finite iterate. No weak limit, Feller
  property or ergodicity is needed, which removes REVIEW-3's portmanteau and Feller points. A limiting coupling exists
  for Polish `S_x` (tightness), but it is not needed.
* **No saturation.** Source blocks contribute only through `s`. Bad clusters enter as composite good blocks whose
  `K_b` comes from Lemma C, not as source blocks.
* **Where the decay comes from.** With `v(x) := e^{−λ dist_ω(x, A)}`, (I) and (K) are the influence bound weighted by
  `e^{λ E_b(z)}` (`K_b(z) ≤ k_b(z) e^{λ (diam B_b + dist(z, B_b))}`), as in 22.3. Then `s ≤ Σ_{y ∈ src} c(y) e^{−λ dist(y, A)}`
  gives `C e^{−λ dist(A, src)}`.
* **Covariance form, for (B).** [Replaced in 33.3: condition on the in-support content near `A` and treat `A` as a
  source.]

### 28.3 Instantiation for UV-TV (checks against sections 16 and 21-24)

* **Sites:** scale-`j` bonds, with the configuration `(V_j, τ'_j, noise)`, in the block-axial gauge.
* **Measures:** `μ_ω`, `μ'_{ω'}` given the patterns, coupled first by H1. Supports: the pattern supports.
* **Blocks:**
  * good boxes, at distance `≥ r_int + 1` from every cluster: in `𝔅_good`, with `K_b` from H3 (10.2, 19);
  * composite boxes `W(K)`, multiplicity `n_W`: in `𝔅_good`, with `K_b` from Lemma C (16, 22.2);
  * boxes meeting the source (the inherited disagreement, pattern disagreements, outside `Λ''_j`): in `𝔅_src`.
    [Corrected in 33.1: the truncation events are a case split made before the theorem, not source blocks.]
* **Column condition (K):** 22.3, with `γ_DS`.
* **Specifications (S):** the box laws of `μ_ω` (DLR by construction). Their supports are preserved, because the
  pattern's characteristic functions are part of the specification.
* **Block couplings (C):** H3's far-to-near coupling and Lemma C's coupling, measurable in the pair. The standard
  explicit maximal coupling, built from the densities with respect to a common reference, is measurable; Goldstein's
  nested version is measurable in the same way.

### 28.4 Lean target

A generic layer next to `OneBox/Restricted.lean`, with no gauge or physics content:
* `structure CouplingSpec`: the blocks, the kernels `q_b`, `q'_b`, `Q_b`, the supports, and (S), (C);
* `theorem couplingDS_bound`: under (I) and (K), for every `ε > 0`, there is a coupling with
  `Σ_x v x * π {Y x ≠ Y' x} ≤ s/((1 − γ) c_min) + ε`;
* `corollary`: `|∫ F dμ − ∫ F dμ'| ≤ 2 ‖F‖ (min_A v)⁻¹ s/((1 − γ) c_min)`.

The proof is finite-dimensional linear algebra on `Φ` plus kernel composition. I expect it to be routine in Mathlib
(`Measure.bind`, `ProbabilityTheory.Kernel`). The kernel and coupling API is the main work.

**Status of write-out 1: paper, written.**

## 29. Write-out 2: Lemma C's cross term, and the collar coupling, using constant-size smallness only

**Rule (27.9).** Only these inputs are used:
* Balaban's constant-size bounds: `O(1)` per site ([III] Theorem 2), or `O(1) e^{−κ d(X)}` per localised term ([I]
  (1.18));
* the explicit decay of his propagators and backgrounds;
* his cluster expansion.

Never "`1 + O(δ)`, `δ → 0`". All smallness comes from **decay across the collar**: from the width `w`, not from the
size of the terms.

### 29.1 Setting

* **Composite box** `W = K ∪ collar` at scale `j`, in the block-axial gauge relative to the coarse configuration.
  * `I` is the inner layer, the collar sites within `r_int` of `K`.
  * `O` is the outer layer, the collar sites within `r_int` of `∂W`.
  * The rest of the collar has width `≥ w − 2r_int` between `I` and `O`.
* **Inner and outer data.** `c` is the configuration on `K ∪ I`; `σ` the configuration outside `W`, which by finite
  range (H0) enters only through `O`.
* **The collar measure.** Given `(c, σ)`, the collar variables between `I` and `O` have the law
  `ρ_j|_{fibre} · χ / Z(c, σ)`.
  * `ρ_j = exp(A_j(V_j))` on the pattern-good collar, with `A_j(V) = −A(U_j(V))/g_j² + Σ_X E_j(X; U_j(V))` ([III]
    (2.23)).
  * `χ` is the product of the small-field characteristic functions on the collar.
  * The fibre constraint `block(V_j) = X_{j+1}` lies inside the `L`-blocks.
* **The law of `W`** given `σ` is `w(c) Z(c, σ)/norm(σ)`. Here `w(c)` collects everything depending only on `c`: the
  cluster's own `T`-operations and labels, which are never bounded.

### 29.2 The decomposition of `log Z(c, σ)`

This is Balaban's step `j → j + 1`, done on the domain `collar ∖ (I ∪ O)` with Dirichlet data `(c, σ)` instead of the
whole lattice. He constructs exactly this localisation: minimal configurations and determining sets restricted to a
domain with boundary data ([III] (2.13)-(2.15), "we localize ... to a domain `Ω`"), with [15]'s variational problem
on the domain.

1. **The constrained background.** `U_bg(c, σ)` is the minimiser of `A` on the collar with the block constraints and
   Dirichlet data `c`, `σ` ([15] Theorem 1, regular data). It is analytic in the data.
   * Its dependence on the data decays: `|∂U_bg(x)/∂(data at y)| ≤ C e^{−m d(x, y)}` ([15] (190); [13] Theorems 3.12,
     3.13 for the propagators with block constraints).
   * `m` is a fixed constant in scale-`j` units.
2. **The classical part** is `−A(U_bg(c, σ))/g_j²`. Its mixed variation is the cross term of the constrained Dirichlet
   energy. To second order it is `⟨Δc, G_{I,O} Δσ⟩/g_j²`, with `G_{I,O}` the constrained Green's function between the
   layers, `|G_{I,O}(x, y)| ≤ C e^{−m d(x, y)}`.
   * The data deviate by at most `|Δc|, |Δσ| ≤ 2C ε_j`: both are small field, in the same gauge, within `C ε_j` of the
     same background.
   * So the term is `≤ C Σ_{x ∈ I, y ∈ O} (ε_j/g_j)² e^{−m d(x, y)} = C p(g_j)² Σ e^{−m d}`.
   * Higher orders carry extra factors `ε_j` and the same decay (analyticity of `U_bg` in the data).
   * The only non-constant factor is `p²`, a polylog, the size of small-field data in units of the width `g`.
3. **The fluctuation part** is `log ∫ dB e^{−½⟨B, Δ(U_bg) B⟩ + (higher-order terms) + Σ E_j}` over the collar, with
   the block constraint.
   * Balaban's random-walk expansion of the constrained propagator and his cluster expansion write it as a sum of
     localised terms `Σ_X Φ(X; c, σ)`.
   * Each depends on the data only near `X`, with `|Φ(X; ·)| ≤ C_0 e^{−κ d(X)}`: constant size, the form of [I] (1.18)
     and [III] Theorem 2.
   * The inherited `E_j`-terms enter the same expansion as local factors of the same constant size.
4. **The characteristic functions.** Write `χ = Π_{cubes}(1 − χ^c_□)`.
   * Under the collar measure, `χ^c_□` has probability `≤ e^{−c p²}` per cube (Gaussian tail at `p` standard
     deviations).
   * Expanding the product puts the `χ^c` factors into the cluster expansion as local polymers of activity
     `≤ e^{−c p²}`.
   * The truncation contributes to `log Z` only through connected clusters, so its mixed variation also needs a cluster
     joining `I` to the `σ`-dependent part: `≤ C e^{−c p²} e^{−κ d}` (REVIEW-3), not a flat `e^{−c p²}`.

### 29.3 The mixed variation

`Mix(c, c'; σ, σ') := log Z(c, σ) − log Z(c, σ') − log Z(c', σ) + log Z(c', σ')`.
* **Cancellation.** Every term of 29.2 that depends only on `c`, or only on `σ`, cancels.
* **What remains:**
  * the classical cross term;
  * the localised terms `Φ(X)` whose domain meets both the `r_int`-neighbourhood of `I` and the
    `r_int`-neighbourhood of the sites `Z` where `σ ≠ σ'`;
  * the truncation clusters doing the same.
* **The bound:**
  `|Mix| ≤ Σ_{z ∈ Z} Σ_{x ∈ I} [C p² e^{−m d(x, z)} + 4 C_0 e^{−κ d(x, z)} + C e^{−c p²} e^{−κ d(x, z)}]
         ≤ C' (p² + C_0) Σ_{z ∈ Z} e^{−m' d(z, I)}`,
  with `m' := min(m, κ)/2`.
  * The sum over `x ∈ I` costs only a constant, since `Σ_x e^{−m d(x, z)} ≤ C_m e^{−m' d(z, I)}`, as REVIEW-2 corrected;
    there is no `|∂_in|` factor.
* **Constant-size inputs only:** `C_0 = O(1)` (Balaban), the decay rates `m` and `κ`, and `p²` from the data size.
  Smallness comes from `d(z, I) ≥ w − 2r_int` for `z` outside `W`.

### 29.4 Total variation of the inner marginal, and Lemma C

* **The ratio.** `law(c | σ)/law(c | σ') ∝ Z(c, σ)/Z(c, σ')`. Fix a reference `c_0`. Then
  `log [Z(c, σ)/Z(c, σ')] − log [Z(c_0, σ)/Z(c_0, σ')] = Mix(c, c_0; σ, σ')`.
  So the density ratio lies in `[e^{−2M}, e^{2M}]` after normalisation, with `M := sup_{c, c_0} |Mix|`.
* **Hence** `TV(law(c | σ), law(c | σ')) ≤ e^{2M} − 1 ≤ 4M` for `M ≤ ¼`, and
  `M ≤ C (p² + C_0) Σ_{z ∈ Z} e^{−m' d(z, I)}`.
* **Lemma C** (as in 22.2, now with constant-size inputs):
  `k_W(z) ≤ k_collar(z) + (|K| + C |I| (log p/m)^d) · 4 C (p² + C_0) e^{−m' d(z, I)}`,
  with `k_collar` from 29.5.
* **The collar width.** For `z` outside `W`, `d(z, I) ≥ w − 2r_int`. With
  `w ≥ 2r_int + (1/m') log(C N (M R)^d p²/ε_W)` and `|K| ≤ N (M R)^d` boxes (24.1), the second term is `≤ ε_W`.
  * That is the collar `w_j` of 24.1, with `m'` now `min(m, κ)/2`.
  * No `δ → 0` is used.

### 29.5 The collar coupling given equal inner data (H3's Pinsker step, redone)

* **Given `c = c'`**, couple the collar laws given `(c, σ)` and `(c, σ')`, far to near, as in 10.2 and 19.
* **The far-marginal bound.** Interpolate `σ_t := σ + t(σ' − σ)`. Every `σ_t` is small field in the common gauge
  (pair-good). For bounded measurable `f` of the collar sites `F` at distance `≥ r` from `Z`:
  `d/dt μ_t(f) = Cov_t(f, L_t)`, with `L_t := ∂_t log(weight)`, a local analytic function supported within `r_int` of
  `Z`.
* `|Cov_t(f, L_t)| = |Cov_t(f, E_t[L_t | φ_F])| ≤ 2‖f‖_∞ sup_{φ_F, φ'_F} |E_t[L_t | φ_F] − E_t[L_t | φ'_F]|`.
* **The conditional expectation `E_t[L_t | φ_F]`** is the expectation of a local analytic function under the collar
  measure with additional Dirichlet data `φ_F` (small field). By 29.2 applied to that domain:
  * its dependence on `φ_F` is a sum of localised terms joining `supp L_t` to `F`;
  * each has constant size `C_0 ‖L_t‖`, with `‖L_t‖ ≤ C p²` (linear in data deviations of size `≤ 2ε_j/g = 2p`, times
    fluctuations up to `p`);
  * each decays like `e^{−m' d}`.
* **So** `TV_r := sup_f |μ_σ(f) − μ_{σ'}(f)|/(2‖f‖_∞) ≤ C (p² + C_0) p² Σ_{z ∈ Z} r^{d−1} e^{−m' r}`, plus
  `C e^{−c p²} e^{−κ r}` from the truncation.
  * This replaces 19's "`C p |F|^{1/2} e^{−m r}` with the perturbation changing constants by `1 + O(δ)`". Prefactors
    are polylog in `p`, and there is no `δ`.
* **The coupling.** Far-to-near maximal coupling as in 10.2:
  `k_collar(z) ≤ Σ_r #(sites at distance r) TV_r ≤ C (log p/m')^d`. The polylog prefactor shifts the crossover
  radius only by `O(log p/m')`.
* **H3 for good boxes** is the same computation on a good box, so H3 also uses constant-size inputs only.

### 29.6 Status of write-out 2, and its citation-level inputs

**Written (paper):** the decomposition, the mixed variation, the total variation, Lemma C, and the collar coupling.

**Citation-level inputs** (Balaban's machinery used on a domain with Dirichlet data):
1. [15] Theorem 1 and (190): the constrained background on a domain, analytic in the data, with exponential decay.
2. [13] Theorems 3.12, 3.13: constrained propagators, the random-walk expansion.
3. [III] (2.13)-(2.15): localisation of determining sets and minimal configurations to a domain.
4. The cluster expansion of the fluctuation integral with localised terms `O(1) e^{−κ d}`, as in [I] (1.18) and [III]
   Theorem 2, run on a domain with fixed boundary data.
   * That Balaban's expansion runs on a domain with fixed boundary data, and not only on the whole lattice, is the
     adaptation. It is the same construction he uses in his localisations; this is a citation-level reading of it.

**Not used:** any `δ → 0` (27.9).

**Next:** write-out 3, the front advance.

## 30. Write-out 3: the front advance (the chaining of 12.4, written out)

### 30.1 Objects

* **Scales** `j = ℓ, ℓ−1, ..., 0`. At scale `j` the two coupled states are `X_j`, `X'_j`, and
  `D_j := {x : X_j(x) ≠ X'_j(x)}` (scale-`j` sites, block-axial gauge).
* **Target.** `B_j` is the image of the observable's support at scale `j`. The **front distance** is
  `Δ_j := dist_j(B_j, D_j)`, in scale-`j` units.
* **Start.**
  * (A): the far coarse data are resampled at physical distance `≥ t/2` from `supp F`, so `Δ_ℓ ≥ c t/ℓ`.
  * (B): fresh randomness on the mirror side at physical distance `≥ 2t`, so again `Δ_ℓ ≥ c t/ℓ`.
* **Regions.** `Λ''_j :=` the deterministic ball of radius `ρ_j := L^{ℓ−j} Δ_ℓ` (scale-`j` units) around `B_j`. Every
  truncation event is taken over `Λ''_j`. So `|Λ''_j| ≤ C (L^{ℓ−j} t/ℓ)^d / ℓ_B^d`.

### 30.2 One scale

At scale `j`, conditionally on all coarser data of both copies, the **sources** are:
* `src¹_j`: the boxes under the coarse sites of `D_{j+1}`, enlarged by one box;
* `src²_j`: boxes where the patterns of the two copies differ (write-out 4);
* `src³_j`: everything outside `Λ''_j`.

**Claim (front advance).** Let `a_j := C_F (λ_j^{−1} + M R_j/κ) log|Λ''_j| + N_j M R_j`. Here `λ_j` is the rate of 28 per
scale-`j` unit, `M R_j` the cube size, and `N_j` the composite-box cap in cubes (24.1). Then, except on an event
`E_j` with `P(E_j) ≤ C|Λ''_j|^{−C_2}`, `D_j ⊂ N_{a_j}(src_j)`.

**Proof.**
1. **Pointwise disagreement.** Theorem 28 with weights `v(·) := e^{−λ_j dist_ω(·, x)}` centred at a site `x` gives
   `P(x ∈ D_j | coarser) ≤ C_s Σ_{y ∈ src_j} e^{−λ_j dist_ω(x, y)}`.
   * `C_s := max_y c(y)/((1 − γ_DS) c_min)` is polylog: coverage `≤ n_W + ℓ_B^d`.
   * Union over the sites `x ∈ Λ''_j` with `dist_ω(x, src_j) > a`:
     `P(some such x ∈ D_j) ≤ C_s |Λ''_j| Σ_{s > a} s^{d−1} e^{−λ_j s} ≤ C |Λ''_j| e^{−λ_j a/2}`.
2. **From `dist_ω` to `dist`.** `dist_ω` contracts composite boxes. Let `E^{path}_j` be the event that some path in
   `Λ''_j` of length `≥ a'` has at least half its length inside composite boxes.
   * Count at the level of `M R_j`-cubes: a path of length `a'` crosses `≥ a'/(C M R_j)` cubes, and cube paths number
     `≤ (3^d)^{#cubes}`.
   * At least half of those cubes must be bad in one copy, priced by H2 (born) or H2a (inherited), with the min-trick.
   * So `P(E^{path}_j) ≤ |Λ''_j| Σ_{n ≥ a'/(C M R_j)} (3^d (C e^{−c κ/2})^{1/2})^n ≤ |Λ''_j| e^{−c' κ a'/(M R_j)}`.
   * On its complement, `dist(x, y) ≤ 2 dist_ω(x, y) + max diam(composite box) ≤ 2 dist_ω(x, y) + N_j M R_j`.
3. **Choose** `a := (2/λ_j)(C_2 + 1) log|Λ''_j|` and `a' := (M R_j/(c' κ))(C_2 + 1) log|Λ''_j|`. Then
   `E_j := {step 1 fails} ∪ E^{path}_j ∪ F_j ∪ G_j ∪ T_j ∪ T_{j+1}`, with `P(E_j) ≤ C|Λ''_j|^{−C_2}`, and
   `D_j ⊂ N_{a_j}(src_j)` on `E_j^c`. ∎

**The pattern sources** `src²_j` are themselves within distance `a^{pat}_j := C (M R_j/κ) log|Λ''_j|` of
`src¹_j ∪ src³_j`, except on an event of probability `≤ |Λ''_j|^{−C_2}` (write-out 4, 31.5). They are absorbed into
`a_j` by enlarging `C_F`.

### 30.3 The recursion

* **On `E_j^c`:**
  * the inherited sources lie within one box of the image of `D_{j+1}`, which is at distance `L Δ_{j+1} − L ℓ_B` from
    `B_j`;
  * the outside lies at distance `ρ_j` from `B_j`.
* **So** `Δ_j ≥ min(L Δ_{j+1} − C ℓ_B L, ρ_j) − a_j`.
* **By induction from `ℓ`**, with `ρ_j = L^{ℓ−j} Δ_ℓ`:
  `Δ_j ≥ L^{ℓ−j} Δ_ℓ − Σ_{i=j}^{ℓ−1} L^{i−j}(a_i + C ℓ_B L) = L^{ℓ−j}[Δ_ℓ − Σ_{k=1}^{ℓ−j} L^{−k}(a_{ℓ−k} + C ℓ_B L)]`.
* **Size of `a_{ℓ−k}`.** `log|Λ''_{ℓ−k}| ≤ d(k log L + log(t/ℓ))`, `N_{ℓ−k}` is polynomial in `log|Λ''|` (24.1), and
  `R_{ℓ−k} = (log g_{ℓ−k}^{−2})^r` with `g_{ℓ−k}^{−2} ≈ g_ℓ^{−2} + b k log L`. So
  `a_{ℓ−k} ≤ C M (R_ℓ + k)^{r} (k + log(t/ℓ))^q` for some fixed `q`: polynomial in `k` and in `log(t/ℓ)`.
* **The bracket.** `Σ_k L^{−k} a_{ℓ−k} ≤ C M R_ℓ^{r'} (log(t/ℓ))^q =: A_ℓ`, a geometric sum.
* **Condition** (front intact): `Δ_ℓ ≥ 2(A_ℓ + C ℓ_B L)`. With `Δ_ℓ = c t/ℓ` and `A_ℓ` polylog in `1/ℓ`, it holds for all
  `ℓ ≤ ℓ_0(t)` at fixed `t > 0`.
* **Then on `∩_j E_j^c`:** `Δ_j ≥ L^{ℓ−j} Δ_ℓ/2 > 0` at every scale. In particular `Δ_0 > 0`: the fine fields agree on
  `B`.

### 30.4 Result

* `P(the fine fields differ on B) ≤ Σ_{j=0}^{ℓ} P(E_j) ≤ C Σ_{k ≥ 0} (L^k t/ℓ)^{−d C_2} ≤ C' (t/ℓ)^{−d C_2}`.
  * The sum is geometric in `k`, dominated by the top scale.
  * Any `C_2 > 0` suffices here: the union over sites is already inside `P(E_j)`.
  * This replaces 12.4's two-term form, which counted the exponential tail separately, by the front argument.
* **Uniform** in the spacing (geometric in `k`, polylog constants depending on `g_ℓ` and `t/ℓ` only) and in the volume
  (only the balls `Λ''_j` enter).
* **For OS density** (13.4): `‖F − f_ℓ‖_OS → 0` as `ℓ → 0` at fixed `t`, at rate `(t/ℓ)^{−d C_2}`.
* **Status of write-out 3: paper, written.**

## 31. Write-out 4: H1 at the polymer level

### 31.1 The gas

* **Setting.** Fix scale `j`, the coarse data `X_{j+1}`, and a region `G` of cells (`M R_j`-cubes) on which `X_{j+1}` is
  small field. The rest of the region (inherited, coarse-bad cells) is handled in 31.6.
* **Polymers** `γ`: connected components, under cube adjacency, of the discrete data of the pattern `ω_j` inside `G`.
  The discrete data are:
  * the domain history at scales `≤ j`, with unreleased regions;
  * labels and Z2 excitations.
  
  Long-range interactions are handled by links (31.2).
* **Compatibility.** Two polymers are compatible iff they are more than `D_c := 100` cubes apart: Balaban's
  admissibility distances ([III] (2.3)-(2.9), poor scan; REVIEW-3). A pattern is a finite family of pairwise compatible
  polymers.
* **Activities.** `z(γ) := ∫_{fibre} ρ^{γ}_j / ∫_{fibre} ρ^{∅}_j`, the ratio of the term with `γ` to the small-field
  alternative on `γ`'s neighbourhood, given the rest. By 24.1 with the slack of (1.97') and (P2):
  `z(γ) ≤ e^{−p0(g_j)} (C e^{−c κ})^{#cubes(γ)}`.
* **Effective interaction.** Polymers interact through the small-field fluctuation integral on the complement. By the
  constant-size cluster expansion (29.2), `w(ω) ∝ Π_γ z(γ) · exp(Σ_X I_X(ω))`, where:
  * `I_X` is a localised term whose domain `X` meets at least two polymers. Since polymers are `D_c` apart, `X` has
    linear size `d(X) ≥ D_c`;
  * `|I_X| ≤ M_X := C (p² + C_0) e^{−κ d(X)}`: constant size times decay (27.9);
  * `I_X := 0` for every other `X` with `d(X) ≥ D_c`.

### 31.2 The positive split (REVIEW-3)

* For every domain `X` with `d(X) ≥ D_c` in the region, `e^{I_X(ω)} = e^{−M_X}(1 + h_X(ω))`, with
  `0 ≤ h_X(ω) ≤ e^{2M_X} − 1`.
* The factor `Π_X e^{−M_X}` is a **global constant**, independent of `ω`.
* So `w(ω) ∝ Σ_{ℒ} Π_γ z(γ) Π_{X ∈ ℒ} h_X(ω)`, summed over link sets `ℒ`: a **positive** measure on pairs `(ω, ℒ)`
  with product weights and the hard core `D_c`.
* **Links are objects.** A link `X ∈ ℒ` occupies the cubes of `X`, with weight `≤ e^{2M_X} − 1 ≤ C (p² + C_0) e^{−κ d(X)}`,
  `d(X) ≥ D_c`.
  * Vacuum links (where `I_X = 0`) carry `h_X = e^{M_X} − 1 ≤ C M_X`. Their density per cube is
    `≤ Σ_{X ∋ x} C M_X ≤ C (p² + C_0) e^{−κ D_c}`, which is tiny.
* **Markov structure.** The joint law of `(ω, ℒ)` is a positive product-form gas of objects (polymers and links) with a
  hard core of range `D_c`.
  * Each link's weight depends only on the polymers it meets.
  * As a field of cell states ("which objects occupy this cube"), it is Markov with respect to `D_c`-neighbourhoods,
    extended along occupied links.

### 31.3 Peierls per copy

For a set `A` of cubes:
`P(every cube of A is occupied by a polymer or a link) ≤ (C e^{−c κ/2})^{|A|}`.
* By positivity and the product form, the probability that given objects `o_1, ..., o_n` are present is
  `≤ Π_i weight(o_i) · sup Π (1 + h)` over the links touching them.
* The sum over the families of objects covering `A` (lattice animals in cubes, `(3^d)^{|A|}`, and links with
  `e^{−κ d}`) converges for `κ` large.
* This is the H2 of 24.1 together with the links.

### 31.4 Correlations (Kotecký-Preiss)

* The gas of 31.1-31.2, with Mayer bonds `e^{I_X} − 1` for the correlation expansion, satisfies the Kotecký-Preiss
  criterion `Σ_{γ ∋ cube} |z(γ)| e^{a #cubes(γ)} ≤ a` for `κ` large, with the compatibility entropy `(C 200^d)^n`.
* This gives decay of pattern correlations:
  `|Cov(φ_A(ω), φ_B(ω))| ≤ C ‖φ_A‖ ‖φ_B‖ |A| (C e^{−c κ/2})^{dist(A, B)/(M R_j)}`.
* That covers the pattern-index covariance term of (B) (`REVIEW3-RESPONSE.md` 13 (iii); Theorem A_good 16 (iii)).

### 31.5 The coupling: disagreement percolation on polymer configurations

* **Two gases.** The two copies' gases have the same objects and weights away from
  `S := N_{D_c}(D) ∪ (cells outside Λ''_j) ∪ (cells where the coarse data differ)`. Activities and link weights depend
  on the coarse data only near the object.
* **The coupling** (van den Berg-Maes, on cells, as in their hard-core gas case).
  * Reveal cells in an order adjacent to the current disagreement set, starting from `S`, and couple each cell's
    conditional laws maximally given what is revealed.
  * **Key property:** if both copies are vacuum at a cell, they agree there. So a disagreement at a cell implies that
    the cell is occupied in at least one copy. This is deterministic and needs **no conditional bound**, which is why
    forced continuation does no harm.
  * Agreement propagates: an unrevealed region surrounded by revealed agreeing cells, with equal weights, has the same
    conditional law in both copies (Markov, 31.2). So it is coupled identically.
* **Path bound.** A disagreement at cell `b` requires a chain `c_1, ..., c_n` from `S` to `b` of cells occupied in copy
  1 or in copy 2: adjacent within `D_c`, or joined by a link. Splitting the chain between the copies and using 31.3
  for each copy (min-trick):
  `P(chain) ≤ Σ_{A_1 ⊔ A_2} min(P_1(A_1 occ), P_2(A_2 occ)) ≤ 2^n (C e^{−c κ/2})^{n/2}`.
* **Result:**
  `P(ω_b ≠ ω'_b) ≤ C Σ_{b' ∈ S} (C' e^{−c κ/4})^{dist(b, b')/(D_c M R_j)}`.
  * This is the quantitative H1 used in 24.2 and 30.2.
  * With a union bound over `b ∈ Λ''_j`, pattern disagreements lie within `C (D_c M R_j/κ) log|Λ''_j|` of `S`, except
    with probability `≤ |Λ''_j|^{−C_2}`. That is 30.2's `a^{pat}_j`.

### 31.6 Cells where the coarse field is bad

* There the gas is not dilute: the patterns belong to inherited composite boxes.
* For the coupling, such cells count as **always occupied**: disagreement passes freely, as through composite boxes in
  28.
* Their rarity is priced by the annealed H2a and the truncation `T_{j+1}` (23.1), not by the gas. Paths through them
  are counted in 30.2's `E^{path}_j`.
* If the coarse data agree there and the surrounding patterns agree, the conditional pattern laws inside coincide, and
  they are coupled identically. A bad box acts only through its boundary (16).

### 31.7 Status of write-out 4

**Paper, written.** Inputs:
1. the activity bound of 24.1 with the slack of (1.97') (re-proof (c));
2. the constant-size cluster expansion for the interactions (29.2);
3. the compatibility range from Balaban's admissibility (citation, poor scan);
4. Kotecký-Preiss and van den Berg-Maes (standard).

## 32. Final status of Lemma UV-TV (updated after 33-34)

**Lemma UV-TV, N-2's key step: complete at paper level.** REVIEW-2's long-standing N-2 GAP is withdrawn (thirteenth
follow-up), and REVIEW-3 has no GAP (follow-up 12). The argument (sections 8-12, 16, 21-24, 26, 28-31, with the fixes of
27, 33 and 34) is complete at paper level **given**:

1. **(c), the strengthened induction:** a re-proof of [V] (1.80)-(1.97) with a retained slack `e^{−c p0²}` per
   birth-scale cube (26, 27), checked three ways (the independent reader and both reviewers). It needs (P0), Balaban's
   condition after (1.82) with the constant doubled; (P1) is insurance.
2. **Citation-level readings:**
   * (a), what `E_k(Z)` is: the small-field alternative's normalisation and vacuum-energy constants at background 1,
     confirmed in substance (`../m1-review/EK-DERIVATION.md`);
   * admissibility of the comparison pattern: delete whole history components (24.1), checked against a poor scan of
     [III] (2.3)-(2.9).
3. **Citation-level adaptation:** Balaban's small-field machinery on **shells** of width `≫ M`, thinner than one
   `M R_j`-cube, shaped by a cluster or a slab, with Dirichlet data on both sides, and his constants uniform in the
   shape (29.6, 33.7, 34.8).
4. **Citation:** `κ` large for fixed `L` ([I] Theorem 3; [III] p. 260), at the cost of a larger `M` and a smaller
   coupling bound `γ`.
5. **Standard tools:** the coupling contraction (28, with Corollary 34.1), Kotecký-Preiss, and van den Berg-Maes on
   object configurations (31, 34.4).

**Not needed:** reading (b), a lower bound with `δ → 0` (replaced by (c)); any `1 + O(δ)` with `δ → 0` (27.9).

**Result:** `P(the fine fields differ on B) ≤ C polylog(t/ℓ) (t/ℓ)^{−d C_2}`, uniformly in the lattice spacing and the
volume. Hence `‖F − f_ℓ‖_OS → 0` as `ℓ → 0` at fixed `t > 0`, for every bounded, measurable, gauge-invariant local `F`
(13.4). This is OS-norm density of the block observables, with `MassGapLoc`'s statement unchanged.

**Lean:** the coupling-form theorem (28.4, with Corollary 34.1) is with the separate worker
(`formal/ProofPhase/OneBox/CouplingDS.lean`).

## 33. Small fixes after the reviews of 28 (REVIEW-3 follow-up 10, REVIEW-2 eleventh) and of 29 (REVIEW-2 twelfth)

The Lean of 28 is with a separate worker (`formal/ProofPhase/OneBox/CouplingDS.lean`, notes in `m1-cds/`). These fixes
are to the paper text only.

### 33.1 Truncation events are a case split, not source blocks

* 28.3 listed "boxes meeting ... truncation events" among the source blocks. That is withdrawn.
* **The split.** The truncation and path events `F_j, G_j, T_j, T_{j+1}, E^{path}_j` (21-24, 30.2) are events of the
  patterns and the coarse data. They are split off **before** Theorem 28 is applied:
  `P(differ on B) ≤ P(E_j) + E[1_{E_j^c} P(differ on B | patterns, coarse data)]`, and Theorem 28 is used only on
  `E_j^c`.
* **Source blocks** are then only the blocks meeting:
  * the inherited disagreement `src¹_j`;
  * the pattern disagreements `src²_j`;
  * the outside of `Λ''_j` (`src³_j`).
* 30.2 already has this form: `E_j` is the union of the truncation events, and the sources are `src^{1,2,3}`.

### 33.2 Write-out numbering

Made consistent with 27.9 and 28-31:
1. the coupling-form theorem (28);
2. Lemma C (29);
3. the front advance (30);
4. H1 (31).

25 (revised) now uses the same order.

### 33.3 The covariance form (B), staying inside the supports

* **Withdrawn:** 19's and 28.2's "hybrid" route, because it is not shown that the hybrid stays in the supports.
* **Replacement.** For the conditional covariance given the block state `𝓕_ℓ`, of `f` near `A` and `g` near `θA`
  (bounded, measurable), condition on the content near `A`:
  `Cov(f, g | 𝓕_ℓ) = E[f(Y_A) (E[g | Y_A, 𝓕_ℓ] − E[g | 𝓕_ℓ])]`, so
  `|Cov| ≤ ‖f‖ E|E[g | Y_A] − E[g]| ≤ ‖f‖ E_{y, y'}|E[g | Y_A = y] − E[g | Y_A = y']|`,
  with `y, y'` independent samples of `Y_A`, hence **in the support** almost surely.
* **Applying Theorem 28.** For fixed in-support `y, y'`, the two conditional measures `μ(· | Y_A = y)` and
  `μ(· | Y_A = y')` on the complement:
  * have the same block specifications on every block not meeting the `r_int`-neighbourhood of `A` (DLR for the
    conditional measure; regular conditional probabilities exist on standard Borel spaces);
  * those blocks are good or composite as before, so (I) holds for their in-support boundaries;
  * the blocks meeting the neighbourhood of `A` are **source blocks**;
  * for the patterns, `N_{D_c}(A)` is part of the source set `S` of 31.5.
* **Result:** `|E[g | y] − E[g | y']| ≤ 2‖g‖ π(Y ≠ Y' on θA) ≤ C ‖g‖ e^{−λ dist(A, θA)}`. The two copies are always
  conditional samples, so nothing leaves the supports.
* **This is not a frozen region.** The content `y` is a sample of the law, averaged over, not a supremum over arbitrary
  content. The blocks next to `A`, which see `y`, need no influence bound because they are sources.

### 33.4 The influence hypothesis (I) without gluing over hybrids

* **The issue.** (I) for boundaries differing on a set `Z` was obtained in 10.2 and 22 by changing one site at a time
  and gluing the one-site couplings. That needs every hybrid boundary in the support, and measurable disintegrations.
  * Hybrids can leave the support. A site-by-site hybrid breaks the fibre constraints of the `L`-blocks it touches, and
    a mixed plaquette can exceed the sharp small-field threshold.
* **Replacement: (I) is obtained directly for each in-support pair `(σ, σ')`** (29.5). The box law `q_b(σ, ·)` is an
  explicit density in the boundary data: Balaban's effective density on the box, normalised, with the box's
  characteristic functions. It is defined for every boundary in the `C ε_j`-neighbourhood, whether or not that boundary
  lies in the global support.
* **Only `q_b` along the path is used.** 29.5 interpolates `σ_t := σ exp(t log(σ^{−1} σ'))` in the common block-axial
  gauge. Only `q_b(σ_t, ·)` is used along the path, never `σ_t` as a configuration of the measure.
  * The derivative of the log-weight is a sum of local terms over the sites of `Z`.
  * So the bound comes out per site, `Σ_{z ∈ Z} K_b(z)`, with no gluing.
  * The moving sharp constraints on straddling plaquettes contribute the boundary term `e^{−c p²}`, already in 29.5.
* **Measurability.** The nested far-to-near maximal coupling (Goldstein's construction for the monotone family of tail
  sets) is built from the densities of `q_b(σ, ·)` and `q'_b(σ', ·)` with respect to a common reference measure. Their
  disintegrations along the tail σ-algebras exist and are measurable on standard Borel spaces. So `Q_b` is a
  measurable kernel in `(σ, σ')`, as 28 (C) requires.

### 33.5 Composite boxes are contracted only inside the local region

* `dist_ω` contracts composite boxes **only inside `Λ''_j`**.
* Outside `Λ''_j` everything is a source (33.1), so no contraction is needed there.
* Untruncated, possibly huge, clusters far away therefore never enter the metric.

### 33.6 Fixes to 29 (REVIEW-2, twelfth follow-up)

* **Dirichlet layers.** The inner layer `I` and the outer layer `O` are taken as **unions of `L`-blocks**: the
  `r_int`-neighbourhoods are rounded up to whole blocks. Then every fibre constraint lies wholly inside the collar
  integration domain, or wholly inside the data. Without this, the Dirichlet problem would mix data and integration
  variables inside one constraint.
* **`E_0(M)`.** The constant-size bound of the localised terms is Balaban's `E_0`, which depends on `M` ([I] (1.18),
  Theorem 3), and `M ≥ M(κ)` grows with `κ`.
  * So the collar width of 29.4 is `w ≥ 2r_int + (1/m') log(C N (M R)^d (p² + E_0(M))/ε_W)`, with `C_0 := E_0(M)`
    named.
  * **Order of constants:** first `κ`, then `M(κ)` and `E_0(M)`, then `w`. Only `log E_0(M)` enters `w`, so there is no
    circularity. The `κ` condition (`C 200^d e^{−c κ/2} < ½`) does not involve `E_0`.
* **`q0 ≥ p0`.** The expansion of the characteristic functions (29.2, item 4) needs the analyticity domain to contain
  the small-field set: `α_{0,j} = g_j C_0 (log g_j^{−2})^{q0} ≥ ε_j = g_j A0 (log g_j^{−2})^{p0}` ([III] (2.28), OCR).
  So `q0 ≥ p0` (with `C_0 ≥ A0` at equality), as `EK-DERIVATION.md` Q4 notes is forced anyway. Stated as a condition
  in `S1-INDUCTION.md` row 6.

**Status:** all fixes are paper text. 28's Lean is with the separate worker. Waiting for the reviews of 29-32.

### 33.7 After REVIEW-3's check of 29 (follow-up 11)

* **Truncation tail, with constant-size terms.**
  * Under the collar measure, the Gaussian tail of the small-field cut is multiplied by the density ratio of the
    constant-size terms, `O(1)` per site.
  * So the probability of a `χ^c_□` event is `≤ e^{−c p² + C M^d}` per `M`-cube, not a pure `e^{−c p²}`.
  * The truncation terms of 29.2 item 4, 29.3 and 29.5 carry `e^{−c p² + C M^d}` in place of `e^{−c p²}`. That is still
    small, since `p² = A0² (log g^{−2})^{2 p0}` beats the fixed `M^d` for `g ≤ γ`.
  * Equivalently, cite Balaban's large-field factor for the complementary characteristic function directly ([V] (1.77)
    and p. 381, `exp(−γ_0 … p0²)` per cube, with his normalisation).
* **The background is non-local.** The mixed terms it carries (29.2 items 1-2) are written as sums of localised terms by
  Balaban's localisation of background-dependent expressions, [V] (1.59)-(1.63), with the decay of [15] (190). That is
  how the classical cross term becomes `Σ_{x ∈ I, y ∈ O} C p² e^{−m d(x, y)}`.
* **A further citation-level adaptation, listed explicitly.** Balaban's machinery is used on **thin, cluster-shaped
  collars with Dirichlet data on both sides**. These are non-admissible domains in his sense: they are not unions of his
  `M R`-cube domains with his shape and age conditions. The machinery includes:
  * the constrained background ([15]);
  * the propagators ([13] Theorems 3.12, 3.13);
  * the localisation ([III] (2.13)-(2.15), [V] (1.59)-(1.63));
  * the cluster expansion ([I] (1.18), [III] Theorem 2).
  
  It is plausible, because every estimate is local at scale `M ≪ w`. But it has real content: his constants must hold
  uniformly over such shapes. It joins the citation-level readings in 25 (revised) and 32:
  1. (a), what `E_k(Z)` is;
  2. admissibility (poor scan);
  3. **Balaban's machinery on non-admissible domains (thin, cluster-shaped collars with data on both sides).**

## 34. Final fixes after the reviews of 30-32 (REVIEW-2 thirteenth follow-up, REVIEW-3 follow-up 12)

Neither review has a FATAL or GAP finding. REVIEW-2 withdraws its N-2 GAP.

### 34.1 One coupling for all sites (Corollary of 28)

**Corollary.** The averaged update `T` of 28.2 does not depend on the weights `v`.
* For every family of weights `v_x(·) := e^{−λ dist_ω(·, x)}` (one for each centre `x`), (K) holds with the same `γ`, since
  `v_x(y)/v_x(z) ≤ e^{λ dist_ω(y, z)}` uniformly in `x`. So the **same** iterates `T^n(μ ⊗ μ')` satisfy
  `Φ_x(T^n(μ ⊗ μ')) ≤ θ^n Φ_x(μ ⊗ μ') + s_x/((1 − γ) c_min)` for every `x` at once.
* `Φ_x(μ ⊗ μ') ≤ Σ_y v_x(y) ≤ C` uniformly in `x`. So one `n`, independent of `x`, makes `θ^n C ≤ ε` for all `x`.
* Hence 30.2's union bound over the sites `x ∈ Λ''_j` refers to **one** coupling, and is well defined. (The Lean worker
  adds this corollary.)

### 34.2 Link-length truncation

* Add to `E_j` (30.2) the event `L_j`: some link meeting `Λ''_j` has linear size above
  `s_max,j := (C/κ)(log|Λ''_j| + log(p² + E_0(M)))`, in `M`-cubes.
* By 31.2, links of linear size `s` have weight `≤ C(p² + E_0(M)) e^{−κ s}`, so
  `P(L_j) ≤ |Λ''_j| Σ_{s > s_max} s^{d−1} C(p² + E_0) e^{−κ s} ≤ |Λ''_j|^{−C_2}`.
* **On `L_j^c`** the composite-box diameter bound becomes `N_j(M R_j + s_max,j)`, which enters `a_j` (30.2).

### 34.3 Units in 31 (REVIEW-2)

* Linear sizes `d(X)` of interaction domains and links are counted in **`M`-cubes**, Balaban's unit for `κ` ([I]
  p. 257).
* Polymers are compatible when more than `D_c = 100` cells (`M R_j`-cubes) apart, which is `100 R_j` `M`-cubes.
* So inter-polymer links have `d(X) ≥ 100 R_j`, with weight `≤ C(p² + E_0) e^{−100 κ R_j}`.
* Since `R_j ≥ (log g_j^{−2})^2` while `p² = A0² (log g_j^{−2})^{2 p0}` grows only polylogarithmically,
  `e^{−100 κ R_j}` beats `p²` for `g ≤ γ`.
* The vacuum-link density per cell is `≤ C(p² + E_0)(M R_j)^d e^{−100 κ R_j}`, also tiny. 31.2-31.3 are read with
  these units.

### 34.4 van den Berg-Maes with links

* After the positive split (31.2), links are **objects** of the configuration, together with polymers. A link occupies
  every cube of its (connected) domain `X`. Links may overlap each other; polymers have a hard core of range `D_c`.
* **The cell state** is the set of objects meeting the cell.
* **Markov property.** The conditional law of an unrevealed region, given the revealed cells, depends only on:
  * the revealed cells within `D_c` of the region;
  * the objects already revealed that cross into it.
  
  A link's weight depends only on the polymers its domain meets, and every such polymer meets a cell of the link.
* **The revealing proceeds along occupied cells, including link cells.** When a revealed cell carries a link, the
  link's further cells are next in line.
* A disagreement chain therefore runs through cells occupied in one copy, contiguously, since link domains are
  connected. The path bound of 31.5 applies with cube adjacency within `D_c`, and no jumps are needed.

### 34.5 The last kernel: from the scale-0 state to the bare field

* The tower ends at the scale-0 state `(V_0, τ'_0) = (Ad U, σ*(τ))`. The bare SU(2) field needs one more reverse kernel:
  `K_{−1}(dU | V_0, τ'_0)`.
* **What it is.** Given `V_0`, write `U = s Û` with lift signs `s` (1.1). The Z2 layer `τ = (ds) τ̂` is determined by
  `V_0` and `τ'_0`, up to the decoder's choices:
  * per flip-cube component (H2's local decoder), `τ = τ'_0 + a`, where `a` is a filling of the monopole boundary
    `dτ̂(V_0)` that the decoder maps back to `τ'_0`;
  * the minimal filling is unique except at **ties**.
* So `K_{−1}` is deterministic in the gauge-invariant content, except for a uniform choice among tied fillings inside a
  decoder component. That choice is local: inside the component, hence inside the scale-0 large-field region.
* **The coupling.** Couple the tie choices identically wherever both copies have the same component and the same data.
  Then the bare fields agree, modulo gauge, on every site whose decoder component lies inside the agreement set of
  `(V_0, τ'_0)`.
* **The front.** `D_{−1} ⊂ N_{a_{−1}}(D_0)` with `a_{−1} := N_0 M R_0`, the component size cap on `F_0^c`. This is one
  more term in 30.3's sum. Gauge-invariant `F` sees only the gauge-invariant content.

### 34.6 Statement (B), built from towers

* **The reflection plane** is a time plane on the boundary of the scale-`ℓ` block grid, hence on block boundaries at
  every finer scale.
* **Slab.** Let `P` be the slab of fine bonds within distance `h` of the plane, with `h` larger than the truncation
  caps on every blocking structure that can cross the plane:
  * decoder components;
  * excision envelopes;
  * composite boxes;
  * labels' crossing pieces.
  
  On the complement of the truncation events, no blocking structure crosses `P`. Given `𝓕_ℓ` and the content `Y_P` of
  the slab, the positive and negative halves are then **conditionally independent**: the Wilson action is nearest
  neighbour, and every block constraint lies on one side.
* **Three towers.**
  1. Let `Y^1`, `Y^2` be two copies of the fine field, conditionally independent given `𝓕_ℓ` (two independent runs of
     the reverse kernels).
  2. The **mixed tower** `Y^m`:
     * on the positive half and on `P`, `Y^m := Y^1`;
     * on the negative half, `Y^m` is sampled from the law of the negative half given `(𝓕_ℓ, Y_P = Y^1_P)`, coupled
       with `Y^2`'s negative half, whose law is the same given `(𝓕_ℓ, Y_P = Y^2_P)`;
     * the coupling is the tower coupling of 30, with the slab `P` as source at every scale.
  3. `Y^m` has law `μ(· | 𝓕_ℓ)`, by conditional independence. `(Y^1, Y^2)` are conditionally independent.
* **The covariance.** For `f` near `A` (positive side) and `g` near `θA`:
  `Cov(f, g | 𝓕_ℓ) = E[f(Y^m_A) g(Y^m_{θA})] − E[f(Y^1_A) g(Y^2_{θA})] = E[f(Y^1_A)(g(Y^m_{θA}) − g(Y^2_{θA}))]`, so
  `|Cov| ≤ 2‖f‖ ‖g‖ P(Y^m ≠ Y^2 on θA) + 2‖f‖ ‖g‖ P(truncation events)`.
* **The tower coupling with the slab as source.** The two negative halves differ only through their slab data, which
  are samples of the law (so in the support, with large fields priced annealed). The slab is at distance `≥ t − h` from
  `θA`.
  * At every scale, the blocks meeting the slab are **source blocks**.
  * Away from it, the specifications of the two half-space laws coincide, since they are the same Balaban densities.
  * The half-space with data on the slab is a domain with Dirichlet data, the adaptation of 29.6.
  * So 30's front argument gives `P(Y^m ≠ Y^2 on θA) ≤ C (t/ℓ)^{−d C_2}`.
* This replaces 33.3's single-scale conditioning by an explicit tower construction (REVIEW-2). The slab content is
  never a supremum over arbitrary content: it is a sample.

### 34.7 NITs (REVIEW-3)

* **Sources in 30.2.** Composite boxes joined to `src¹_j` (meeting the inherited disagreement) are themselves source
  blocks. The others are good blocks with Lemma C.
* **Locality.** Composite boxes and the contraction of `dist_ω` are used only inside `Λ''_j`; outside, every block is a
  source block (33.5).
* **H1 conditioning.** The pattern coupling of 31.5 is applied on the complement of `E^{path}_j` and of the truncation
  events: a case split made first, as in 33.1.
* **`I_X`** (31.1) is the **inter-polymer cluster term**: the part of the small-field cluster expansion of the
  complement whose domain `X` meets at least two polymers, with the polymers' own fields integrated inside their
  `T`-operations, as REVIEW-3 described (follow-up 7 (3)).
* **The final bound** carries polylog factors from `ℓ_B` and `C_s` (30.2): `P(differ on B) ≤ C polylog(t/ℓ) (t/ℓ)^{−d C_2}`.
  Harmless for `C_2 > 0`.

### 34.8 The domain class of the Balaban-on-domains adaptation (29.6, 32)

* **Named precisely**, the adaptation is: Balaban's small-field machinery used on domains that are **shells**:
  * of width `≫ M` (so all his estimates, local at scale `M`, see the shape only through boundary layers);
  * thinner than one `M R_j`-cube;
  * shaped by a cluster `K` or by a slab (34.6);
  * with Dirichlet data on both sides.
* His constants must hold **uniformly in the shape**. The machinery in question:
  * the constrained background ([15]);
  * the propagators ([13] Theorems 3.12, 3.13);
  * the localisation ([III] (2.13)-(2.15), [V] (1.59)-(1.63));
  * the cluster expansion ([I] (1.18), [III] Theorem 2).
* Plausible, since every estimate is local at scale `M ≪ w`. But it is a genuine adaptation, not a citation.

# Part 10 (2026-11-23): what M1-PLAN 0 still lists outside UV-TV

## 35. Group 1: the four sketch-level points

### 35.0 Result in plain words

All four close; none is an obstruction.
1. **"Cap reached implies irregular `W`"** (FILL 0.2): **paper**, via an exact coarse Stokes inequality, after one change
   to the twist-free test: a uniform threshold `C_tw r0 λ²` in place of `C_tw r0 |γ|²`. The filling's data bound
   already used `λ²` (22, 27), so nothing else moves.
2. **The footprint-weighted lifetime:** **closed by citation.** [V] (1.80)-(1.81) already give `K ≤ n0 − j + R_j`, with
   `n0` the shrinking time (`R10-SCOPE.md` 1). Its two remaining uses are covered: R2's long-lived regions by that
   citation, and large labelled components by point 4.
3. **Per cube or per component before (1.73): the case split is no longer needed.**
   * Every component that Balaban's R-operation processes satisfies his release condition (i): it lies in a cube of
     side `≤ 100 M R_k` ([V] p. 384: "contained in a cube of the size `100 M R_{j+1+K}`"; (1.89): "the domain `X` in
     (1.71) satisfies the assumption with `K = 0`").
   * So `|X| ≤ 100^d` cubes, and under either reading `δ_X ≤ 100^d δ_k → 0` with `g_k`.
   * One argument then covers all released components. The text-reading question no longer matters.
4. **Labelled components above `ε_*`: there are none at release**, by point 3. The condition `100^d δ_k ≤ ε_*` holds for
   `g_k ≤ γ0(L)`.
   * The "carry large labelled components beyond the lifetime" branch of 11.4 is empty and is withdrawn.
   * The strengthened induction (c) and the one-box contraction (12.2) therefore cover every label.

### 35.1 Point 1: cap reached implies irregular `W`

**The test, restated** (replacing 2's `C_tw r0 |γ|²`): a hole `H` is twist-free if every loop `γ` in its outer layer
`O(H)` with `|γ| ≤ λ := 8(ℓ_max + 2)` satisfies `|Hol(γ) − 1| ≤ C_tw r0 λ²`.

**It still passes where it should:**
* **Localised cores** (bounding within radius `ρ ≤ C L ≤ ℓ_max − 1`): once `H` contains the core's spanning set, every
  short loop in `O(H)` bounds in the region where plaquettes are `< r0`. Non-abelian Stokes then gives
  `|Hol − 1| ≤ r0 |γ|²/16 ≤ C_tw r0 λ²`.
* **Thin centre sheets:** `Ad(−1) = 1`, so the twist is `O(r0 λ²)`.
* **The filling's data bound** was already `C_tw r0 λ²` (22, 27.8, 33.6), so the constants are unchanged.

**Claim.** If the cap `ℓ_max` is reached for a component, the coarse field `W` (Balaban's average at scale `k + 1`) is
irregular within distance `C λ` of that component.

**Proof.**
1. **A twisted short loop.** Cap reached means there is `γ ⊂ O(H)`, `|γ| ≤ λ`, with SO(3) twist `θ > C_tw r0 λ²`. `γ`
   encircles a cross-section of `H` of diameter `≤ λ/2`.
2. **Moving to a coarse plane.**
   * Translate `γ` by at most `L` transverse to its plane, along the directions in which the linked structure extends:
     `γ` links a sheet, and translating along the sheet keeps it encircling the sheet at the same distance `≈ ℓ_max`
     from `H_0`.
   * The swept cylinder avoids `H_0`, so its plaquettes are `< r0` and the twist changes by
     `≤ r0 · area ≤ r0 λ L ≤ θ/8` for `C_tw ≥ 8`.
   * So a fine loop `γ'` in a plane parallel to a coarse plane has twist `≥ 7θ/8`.
3. **A coarse loop around it.**
   * Let `Γ'` be the boundary of a coarse square of side `≈ 2λ/L + 2` coarse units, centred at `γ'`, in that coarse
     plane. The fine annulus between `γ'` and the translates of `Γ'` used by Balaban's average (all within distance
     `L` of `Γ'`) avoids `H_0`, and its area is `≤ C λ²`.
   * Non-abelian Stokes over the annulus: every fine loop `Γ'_x` (a translate of `Γ'`) has twist
     `≥ 7θ/8 − C r0 λ² ≥ θ/2` for `C_tw ≥ 4C`.
4. **The coarse holonomy.**
   * Along `Γ'` the fine field lies in the region where all plaquettes are `< r0`. There it is a flat connection on the
     annulus with holonomy `≈ θ`, up to `O(r0 L²)` per coarse link (in an axial gauge along the annulus, the fine
     links are within `C r0 L²` of a locally pure gauge).
   * Balaban's average is gauge covariant and maps a locally pure gauge to a locally pure gauge ([I] (0.3)-(0.4)). So
     the coarse holonomy satisfies `|Hol_W(Γ') − Hol(Γ'_x)| ≤ C r0 L² |Γ'|`, which is `≤ θ/4` for `C_tw ≥ 8C`, since
     `|Γ'| ≤ C λ/L` and `θ > C_tw r0 λ²`.
   * Hence the angle of `Hol_W(Γ')` is `≥ θ/4`.
5. **Coarse Stokes.** For any lattice configuration and any simply connected union `S` of coarse plaquettes,
   `|Hol(∂S) − 1| ≤ Σ_{p' ∈ S} |W(∂p') − 1|`. This is exact: write the holonomy as an ordered product of conjugated
   plaquette holonomies and use unitary invariance. With `S` the coarse square of `≤ (2λ/L + 2)²` coarse plaquettes,
   some `p' ∈ S` has `|W(∂p') − 1| ≥ (θ/4)/(2λ/L + 2)² ≥ C_tw r0 L²/64`.
6. **Irregular.** `C_tw r0 L²/64 = C_tw c/(64 L²)` is a fixed constant, while `ε_{k+1} = g_{k+1} p(g_{k+1}) → 0`. So
   `W` is irregular at `p'`, within distance `C λ` of `γ`, for `g ≤ γ0(L)`. ∎

**Status: paper.** It uses:
* non-abelian Stokes, in its exact inequality form;
* the gauge covariance of Balaban's average;
* the definition of the cap (`ℓ_max = C_1 L ≥ C L + 1`, so localised cores always finish).

The "fractions sum to 1" step of FILL 0.2 is no longer needed. Constant order: `C_tw ≥ 8 max(C, 1)`, before `c` in
`r0` (27.8).

### 35.2 Point 2: the footprint-weighted lifetime

* **What [V] gives** (`R10-SCOPE.md` 1, read line by line): the factor `e^{−κ_j(Z)}` controls `K ≤ n0 − j + R_j` steps,
  where `n0` is the last step at which `S^{n−j}(Z)` still has positive linear size. `n0` grows with the size of `Z`. The
  cost (1.81) is geometric in the shrinking linear size, plus `R_j` steps at bounded size.
* **Uses in M1:**
  * **R2's long-lived regions** (conserved-flux sheets carried while larger than a cube): covered directly. They shrink
    to a cube at `n0`, and their few-cube phase ends within `R_j` (`R10-SCOPE.md` 1).
  * **Large labelled components beyond the lifetime** (11.4, 25): none exist (35.3, 35.4).
  * **The slack `ψ`** (26) is carried through the same (1.80') with `K ≤ n0 − j + R_j`. No change.
* **Status: closed by citation** ([V] (1.80)-(1.81) as written), with `R2-REPAIR.md`'s footprint lemma
  (`footprint_sum_le`, Lean) as an independent check. The sketch item is withdrawn.

### 35.3 Point 3: per cube or per component

* **Release condition.** The components `X` in (1.71) to which the R-operation's split applies satisfy Balaban's
  conditions (i), (ii) with `K = 0` ((1.89)). Condition (i) is "contained in a cube of the size `64 M R` (resp.
  `100 M R`)" ([V] pp. 384-386).
* So a released labelled component has `|X| ≤ 100^d` cubes of side `M R_k`, that is `≤ (100 M R_k)^d` sites.
* **Under either reading of the first-order bound before (1.73):**
  * per `M R_k`-cube: `δ_X ≤ 100^d δ_k`;
  * per component: `δ_X ≤ δ_k`.
  
  In both cases `δ_k = O(1) B^{3/2} A^{1/2} C_0 M^d R_k^{d+2} p²(g_k) q0(g_k) g_k → 0`, since `g_k` beats every polylog.
* **One argument.** Take `ε_*` as before (`≤ L^{−4}/(2C)`, 12.2). The condition `100^d δ_k ≤ ε_*` is a condition on
  `γ0(L)`. Then every released labelled component is "small", and 11.1-11.3 with 12.2 apply to all of them.
* **Status: paper.** The case split of 11.4 and 12.5 is withdrawn, and the reading question (sketch point 3) is moot.

### 35.4 Point 4: labelled components above `ε_*`

* **None exist at release**, by 35.3.
* **Labels inside regions not yet released** are indicators inside `T`-operations (the window form, `S1-INDUCTION.md`
  (F4)). They are covered by Balaban's carrying of the region (35.2) and by the slack `ψ` of the unreleased component
  (27.4).
* **After release**, each label is `a_ℓ e^{L_ℓ}` with the one-box contraction (12.2). Its weight changes in total by
  `e^{4C ε_*}` plus the marginal steps of 13.1. Those steps are now at most `log_L(100)` steps, a constant, since the
  component is at most `100` cubes across.
* **Status: paper.** The sketch item is withdrawn.

### 35.5 Changes made elsewhere

* **FILL.md 2:** the test threshold becomes `C_tw r0 λ²` (update note).
* **UV-TV 11.4 and 12.5:** the large-component branch is withdrawn (35.3-35.4).
* **M1-PLAN 0:** the four sketch-level points are closed. The final verdict for all of M1 comes after Group 2.
