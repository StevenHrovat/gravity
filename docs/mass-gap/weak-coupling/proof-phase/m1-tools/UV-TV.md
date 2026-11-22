# Lemma UV-TV (i): the Dobrushin route (m1-tools, 2026-11-22)

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
