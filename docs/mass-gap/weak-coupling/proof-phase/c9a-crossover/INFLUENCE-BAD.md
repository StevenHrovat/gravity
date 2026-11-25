# The 10.4 lever: an influence-defined bad set, its measurability, and what W2 must measure (c9a-crossover, 2026-11-23)

Question (coordinator, from the owner's readings "Subsets save the day" and "No percolation without an outside"): call "bad"
only what fails to contract, not every large field (`WL.md` 10.4). Can such a bad set be made measurable with respect to the
system's own coarse variables, so that its rarity can be bounded given coarse data only? Does that change what W2 must
measure?

Claim marks as in `NOTE.md`. Notation as in `WL.md` 1: scale-`i` state `X_i`, coarse state `X_{i+1}`, reverse kernel
`K_i(x, ·)`, box specifications `q^x_b(σ, ·)`, local column sum of a box `b` at outside `σ`:
`κ_b(σ) := Σ_{z ∉ b} k^x_b(z; σ)` (influence of `z` at outside `σ`, worst case over the second configuration agreeing off `z`).

---

## 0. Result in plain words

1. **A purely coarse-measurable influence-bad set does not work** (paper). If "bad at `b`" is to be a function of the coarse
   data alone, it has to be a worst case over every fine outside compatible with them, and at the weak end that worst case
   is always bad: M1's sub-block vortex outside (`UV-TV.md` 3) is compatible with every coarse state and gives
   `k ~ |b|`. So every box would be bad. The same happens for any soft (noisy) blocking: the conditional support of the
   fine field given the coarse field is everything.
2. **The workable form has two levels, both inside the system's own filtration** (paper/sketch). Bad at scale `i` =
   *coarse-bad* (a function of `X_{i+1}` near `b`) or *fine-bad* (a function of `(X_i, X_{i+1})` near `b`). Fine-bad is
   defined by contraction itself: `κ_b(σ) ≥ c₀` at the actual outside. That set is measurable with respect to
   `σ(X_i, X_{i+1})` restricted to a neighbourhood of `b`, the sigma-algebra of the system's own variables at two adjacent
   scales: it is a "subset" in the owner's sense (section 2).
3. **Its rarity given coarse data only is then a well-posed number per coarse state** (paper): `η_i(x; A) := K_i(x, {every
   block of A fine-bad})`, a function of `x` alone. What the argument needs is a Peierls form
   `η_i(x; A) ≤ η^{|A|}` for coarse-good `x`, plus rarity of coarse-bad blocks under the coarse law `ρ_{i+1}` (one scale up,
   annealed). This is exactly M1's split (H2 quenched given coarse data on coarse-good cells; coarse-bad cells priced one
   scale up), with "small field" replaced by "contracting".
4. **Coarse-bad gets a contraction meaning too** (sketch): `x` is coarse-bad at `b` if even the fine-good outsides do not
   contract, i.e. `sup{κ_b(σ) : σ fine-good near b, compatible with x} ≥ c₀`. With that definition the good-box clause (G)
   holds by construction on good pairs, and the content moves entirely into the two rarities.
5. **What the lever gains** (sketch): large but decided fields are no longer bad, so the bad density can be far below the
   field-size density. **What it costs:** (i) the Peierls bound for an influence-defined event cannot come from Balaban's
   polymer weights; it needs a local argument (energy-entropy or a certified local check); (ii) the definition is
   self-referential at the coupling level (badness of a pair depends on the pair), which the coupling-form theorem allows
   only if the bad set is fixed before the update (section 3); (iii) checking `κ_b(σ) ≥ c₀` exactly is a finite-volume
   Dobrushin-Shlosman computation per block, so a rigorous classifier is a certified local test.
6. **W2 changes in one place** (section 4): the rarity measurement must be **conditional on the block field** (several fine
   samples per sampled `Y` from the constrained chain itself), not only annealed over equilibrium configurations, and the
   influence-bad classification must be per block at the actual outside. That needs several box measurements per `Y`. The
   projection gives its price as an option.

## 1. Why the bad set cannot be coarse-measurable alone

* The coupling-form theorem (`CouplingDS.lean`) needs, on good blocks, the influence bound (I) for **every** pair of
  configurations in the support. If badness is to be decided by `x = X_{i+1}` alone, a block `b` can be called good only if
  (I) holds for every fine outside compatible with `x`, i.e. `sup_σ κ_b(σ) < c₀`.
* For M1's kernels that supremum is of order `|b|` for every `x` (paper, `UV-TV.md` 3: an outside carrying an SO(3) twist or
  Z2 flux through `b` forces a deep structure whose position the coarse data do not fix). With a soft blocking every fine
  outside is in the support. So the coarse-only bad set is everything; rarity fails trivially.
* The way out in M1 was a fine-measurable pattern (small-field characteristic functions) that cuts the support; on the
  pattern-good set the worst case is mild. The lever replaces the small-field pattern by a contraction pattern.

## 2. The two-level influence-defined bad set, and its measurability

Fix a cut `c₀ < 1`, a box shape around each block (the box of side `ℓ` centred on it) and an interaction range `r`.

* **Fine-bad:** `F_i(b) := 1{κ_b(X_i restricted to N_r(b) ∖ b) ≥ c₀}`, the local column sum of the box at the actual
  outside, given `X_{i+1}` near `b`.
* **Measurability (paper).** `k^x_b(z; σ)` is a supremum of `|q^x_b(σ, f) − q^x_b(σ^z, f)|` over bounded test functions;
  for kernels with densities with respect to a fixed reference it equals a total-variation (or Wasserstein) distance of two
  explicitly parametrised densities, which is a measurable function of `(σ, σ^z, x)` (supremum over a countable dense family
  of test functions). Its supremum over `σ^z` agreeing with `σ` off `z` is measurable after restricting the perturbation to a
  countable dense set of values (continuity of the densities in the perturbed variable). So `F_i(b)` is measurable with
  respect to `σ(X_i|_{N_r(b)}, X_{i+1}|_{N_r(b)})`: the system's own variables at scales `i` and `i + 1`, localised.
* **Coarse-bad:** `G_i(b) := 1{sup{κ_b(σ) : σ compatible with x near b, F_i(b') = 0 for all b' ⊂ N_r(b)} ≥ c₀}`, a
  function of `x|_{N_{2r}(b)}` alone: the coarse data are bad if even outsides that are themselves fine-good fail to contract.
* **Bad set:** `B_i := {b : F_i(b) = 1 or G_i(b) = 1}`, enlarged by merging at range `R = 2w + l_B` (`WL.md` 10.2).

In the owner's words: both levels are subsets (measurable with respect to the scale filtration), so the machine can be run on
them; whether it halts (contracts) is the rarity question.

## 3. Rarity given coarse data only, and the self-reference

* **Fine-bad rarity, quenched in the coarse field.** For coarse-good `x`:
  `K_i(x, {F_i(b) = 1 for all b ∈ A}) ≤ η^{|A|}` (Peierls form, per copy), uniformly in `x` on coarse-good regions. This is a
  property of the reverse kernel at a fixed coarse state: a number per `x`, computable in principle by sampling `K_i(x, ·)`.
* **Coarse-bad rarity, annealed one scale up.** `ρ_{i+1}(G_i(b) = 1 for all b ∈ A) ≤ η'^{|A|}`: a property of the coarse
  law only. Its proof sits at scale `i + 1` (it is again a rarity of a measurable event of the system's own variables).
* **The self-reference.** Fine-badness of a pair depends on the pair. The coupling-form theorem fixes the block family
  (good/source) before the update. M1 resolved this by conditioning on the patterns first (both copies' patterns coupled by
  van den Berg-Maes, then the fine fields coupled per pattern pair). With an influence-defined pattern the same order works
  only if the pattern is a function of variables that the update of good blocks does not change, or if the bad set is frozen
  at the start of each coupling sweep and the influence bound (I) is checked against the frozen set. Sketch, not checked: a
  frozen-set version of the coupling contraction, with the bad set re-drawn between sweeps and the error of the stale set
  bounded by the probability that a good block turns bad in one sweep.
* **Where the Peierls bound would come from.** Not from Balaban's polymer weights (they bound large fields, not
  non-contraction). Candidates: (a) a local energy-entropy argument (a non-contracting block needs a multimodal local
  conditional law, which needs near-degenerate local minima of the constrained action; their weight relative to the
  unimodal alternative is a local free-energy difference); (b) a certified local check over a compact set of coarse data,
  with the fine-bad probability bounded by a local estimate. Both are open at order-one coupling.

## 4. What W2 must measure in addition (amendment proposal, not yet in the pre-registration)

1. **Conditional rarity.** For each sampled `Y` (16 per `β`), draw fine samples from the constrained chain at that `Y` (it is
   running anyway: chain A of the coupled pairs samples `K_i(Y, ·)`), and classify blocks as fine-bad by the local column sum
   at the sampled outside. Report `η(Y)` per `Y` and its spread across `Y` (the quenched-in-coarse number), and the pair
   correlation of fine-bad blocks at fixed `Y` (a check of the product form).
2. **Coarse-bad classification.** For each `Y`, the worst local column sum over the fine-good outsides tried (the greedy
   pool, restricted to outsides with no fine-bad block in the neighbourhood). Report the fraction of coarse-bad blocks.
3. **Cost.** Per-block classification at the sampled outside costs one box measurement (32 shell links) per block. With 8
   block positions per `Y` instead of 1, that is 8 × 16 = 128 `ℓ = 4` jobs per `(β, κ)` instead of 16. In launch batches of 6
   this adds about 19 batches per `(β, κ)`; `PROJECTION.md` gives the hours as an option.
4. **Verdict mapping.** `WL-S` SUPPORTED would then require, at some cut `c₀`, the conditional fine-bad density (max over the
   sampled `Y`) and the coarse-bad density with merged clusters subcritical at the range set by the measured conditional mass,
   together with `R_up < 1` on good boxes. The field-size classification stays as a comparison: the lever is worth it only if
   the influence-bad density is clearly below the field-size bad density.

## 5. Status

* Paper: the impossibility of a coarse-only influence-bad set (section 1), the measurability of the two-level set (section 2).
* Sketch: the two rarities as the remaining inputs, the frozen-set coupling, the candidate sources of a Peierls bound.
* Open: every rarity bound at order-one coupling; the frozen-set coupling theorem.
