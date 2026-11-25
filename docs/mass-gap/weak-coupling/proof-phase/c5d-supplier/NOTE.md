# Proof phase, cycle 5, workstream 4 (c5d-supplier): the segment-1 supplier, and Dobrushin with rare defects (2026-11-22)

Brief: (A) pin what the published ultraviolet bounds give at the weak-coupling scale `L_*`, write UV1 as the sources
support it, as a Lean named hypothesis with a translation lemma; (B) a Lean Dobrushin theorem whose bad sites are rare
(blueprint v4 draft, section 3.2 UV1, section 3.3 strategy (c), section 7 steps 4 and 5; `../c4-fable/REVIEW.md` 1.4).

Lean: four new files under `../../../formal/ProofPhase/Defects/` (`EffDist.lean`, `Quenched.lean`, `Annealed.lean`,
`Supplier.lean`), built in `~/formal-c5d` (Lean 4.34.0, Mathlib v4.34.0). All build without warnings; `axioms.log`
shows `propext, Classical.choice, Quot.sound` for all 17 headline theorems; no `sorry`, no `native_decide`, no new
axioms. Nothing outside `ProofPhase/Defects/` and this folder was edited. No numerics, no GPU, no commit.

```
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c5d-supplier/setup.sh
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c5d-supplier/build.sh ProofPhase.Defects.Annealed
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c5d-supplier/build.sh ProofPhase.Defects.Supplier
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c5d-supplier/axioms.sh
```

Marks: **S** substantive, **D** definitional or elementary. Reading marks: **source** (statement read by me in the
file), **text** (paper read by me in full text), **review/record** (only a review or a citation seen), **recalled**.

## 0. Result in plain words

**Part B (Lean, S).** A Dobrushin theorem with rare defects, in the W1 form the route uses: if the defect set is random
and its law is dominated on cylinders by a Bernoulli(`p0`) field, if for every defect set the measure given that set has
a block specification that contracts (GDS with `γ e^{λ D1} < 1`) when distance is counted **only on good sites**, then
the environment-average of the covariance decays like `(Δ(p0 + e^{-2λ}))^{R/2}` uniformly in the volume
(`defect_decay_W`). Defects cost nothing inside their blocks; they cost their probability in the Peierls sum. The
theorem bounds the average **conditional** covariance. It does **not** give decay of the unconditioned measure, and
cannot: a two-environment mixture satisfies every hypothesis and has a covariance that does not decay
(`mixture_counterexample`). The missing piece, for a defect set that is a function of the field (large-field flags), is
the decay of the environment term `Cov(E[f|Bad], E[g|Bad])`, precisely stated in B.5.

**Part A (reading, then Lean).** The OpenAI construction gives, at every level and uniformly in depth and volume: the
density form, a local defect set (`flags`), small-field terms with exponential tails, large-field activities with upper
bounds only. It does **not** give (i) any probability bound on the flags, conditional or marginal, (ii) closeness to a
fixed action, (iii) a weak-coupling scale anywhere near the infrared: its bounds force the coupling at its coarsest
level to `β ≥ 9.4·10^5` (computed from `Fits.smallField`). Balaban's gauge papers could not be read in full text
(Project Euclid answered automated requests with a security check, which I did not try to pass); Dimock's exposition of
the same method for `φ⁴₃` was read and confirms the exact-cover structure with upper bounds only, and that Balaban's
gauge papers add an "R operation" that recycles large-field contributions into small-field ones. UV1 is stated as
`UVRepDefect` with its citations; the translation lemma `uvRepDefect_cylinder` turns its conditional-probability clause
into exactly the cylinder hypothesis Part B consumes. That clause is the one neither source states.

## Part A. The segment-1 supplier

### A.1 The OpenAI `Rep` against UV1 in defect form (source)

Clone `~/ym-replay/YM`, commit `b379615`, submission `submissions/openai-20261028/submission`. Statements read; proofs
not built here (as in ws4).

| UV1 clause (blueprint v4 draft 3.2) | what `Rep` states | where | verdict |
|---|---|---|---|
| density `exp(-S_{k,j})` against Haar | `Rep.eval = exp(exponent) · gas`, against probability Haar `prior`; `exponent = v·|Λ| − inChannels − additive` | `History.lean` (`Rep`, `exponent`, `eval`), `Wilson/Law.lean:55` | **given** |
| blocking: noisy local kernel | `StepData.density β U V = ∑_t likelihood(U,t) · noise(β, prediction(U,t), V)`: random frame and bond tags with probabilities, then independent noise `∝ exp(−β·penalty·price(V_b Q_b⁻¹))` per coarse link; odd block factor `L ≥ 3` | `Block.lean:22-75`, `Patch.lean` | **given**, noise width `∝ 1/β` |
| bad set: a local function of the block field | `flags t U = {x : some plaquette touching x has chord > t}`, `t = threshold(m) = β̂^{-1/2}·exp((log log β̂)²)` (`≈ 0.995` at the coarsest level) | `Masks.lean:31-35`, `History.lean` (`threshold`) | **given**: a function of the field (range one plaquette), not of the noise |
| `P(x bad | outside) ≤ p0` | **not stated**. Large-field activities `K` have upper bounds `‖K_i‖ ≤ b_i` with per-site mass budget `forcedAllowance = exp(−monitor^{1/5})` (`≈ 0.019` at the coarsest level); no lower bound; gas is exact cover (`admissible`: disjoint supports, inventories cover `flags` exactly) | `Activities.lean:98-132`, `ActivityBounds.lean` | **missing** (A.3, gap G1) |
| off the bad set: local terms with exponential tails | `additive = ∑ masked E_i` (zero unless the support is healthy), `E_i` with sup bounds on up to `order ≥ 6` left derivatives on healthy configurations, per-site budget `allowance = β̂^{-11/10}` with weight `exp(κ·coverNumber)` | `Activities.lean` (`EBound`), `Masks.lean` (`masked`, `supBounds`) | **given**, stronger than C1 |
| "within ε0 of Wilson at a fixed `β_*`" | **not stated**. `inChannels = β × (clipped quadratic in the plaquette chord, linear above threshold + kept-loop terms `‖ell‖²/2` with row coefficients of total weight `≤ C` + cubic and quartic atoms) + loop atoms`; budgets `C`, `loopCap` are not small; the path data depend on the depth `N` (shared across volumes only, `Selected.path_shared`) | `PathActions.lean:150-242` | **missing as stated**; true with "the level's own multi-loop action" in place of Wilson (gap G2) |
| constants independent of `k`, `j` | `History.Conv N p m`: `Lawful` with the level-`m` parameters (`width`, `paths`, `loopCap m`, `allowance m`, `forcedAllowance m`) and `β ∈ [β̂_m/2, 2β̂_m]`, for every depth `N ≥ m` and every volume `p` | `History.lean` (`Conv`, `Selected.represents`) | **given** (uniform in depth and volume at fixed level) |
| a weak-coupling scale where IR can start | `Fits.smallField: threshold(m) ≤ 1` for every `m`, with `β̂_m = bar + slope·scale(m)` increasing in `m`. `β̂^{1/2} ≥ exp((log log β̂)²)` holds for `β̂ ∈ (1, ≈81)` and for `β̂ ≥ 9.37·10^5` and fails in between; since `β̂_m` increases through every value above `bar` in small steps, **`bar ≥ 9.4·10^5`** | `History.lean` (`Calendar`, `Fits`) | the OpenAI `L_*` has `β_std ≥ 9.4·10^5`, i.e. `g² ≤ 4.3·10^-6` (gap G3) |

### A.2 Balaban and the other sources

| source | what it states (as far as read) | read |
|---|---|---|
| Balaban, CMP 109 (1987) 249-301 (RG approach I: small-field effective actions, coupling renormalisation, 4D) | as in `../c4b-seg1/NOTE.md` 1.1 | review/record; full text not obtained |
| Balaban, CMP 116 (1988) 1-22 (II, cluster expansions) | as c4b | record; not obtained |
| Balaban, CMP 119 (1988) 243-285 (convergent renormalisation expansions) | as c4b | review; not obtained |
| Balaban, CMP 122 (1989) 175-202 and 355-392 (large field renormalisation I, II: "localization, exponentiation, and bounds for the R operation") | as c4b; plus (Dimock, below): the "R operation" converts some large-field contributions back into small-field ones | review; not obtained |
| Dimock, arXiv:1212.5562 (RG according to Balaban II, large fields; `φ⁴₃` on a torus) | Thm 3.1: after `k` steps the density is a **sum over histories** of large-field regions with characteristic functions (`χ` small field, `ζ = 1 − χ` large field; eq. (229), (233)): exact cover. Large-field cubes are suppressed by `exp(−O(1)p_k²)`, `p_k = (−log λ_k)^p` (section 1): **upper bounds**. Small-field corrections `|E_k(X)| ≤ λ_k^β e^{−κ d_M(X)}` (eq. (212)), remainders `λ_k^{n0}` (eq. (214)). Remark 3 after Thm 3.1: in Balaban's models these terms get further contributions from the R operation, "not necessary for this model". Goal: stability bounds on `Z`, uniform in the cutoff, extensive in the volume | **text** (pages 1-5, 29-37) |
| Dimock, arXiv:1108.1335, 1304.0705; QED d = 3, arXiv:2009.01156 | as c4b | abstract |

Project Euclid hosts the Balaban PDFs free of charge. A `curl` download was refused by this session's permission rules
(file downloads need the owner's yes), the fetch tool got empty pages, and the browser pane showed Project Euclid's
"additional security check" page; I stopped there and did not try to get past the check. For the owner, the five files (one click each in a normal
browser; save them into this folder and the next session can read them):

```
https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-109/issue-2/Renormalization-group-approach-to-lattice-gauge-field-theories-I-Generation/cmp/1104116842.full
```
```
https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-116/issue-1/Renormalization-group-approach-to-lattice-gauge-field-theories-II-Cluster/cmp/1104161193.pdf
```
```
https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-119/issue-2/Convergent-renormalization-expansions-for-lattice-gauge-theories/cmp/1104162401.pdf
```
```
https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-122/issue-2/Large-field-renormalization-I-The-basic-step-of-the-bf/cmp/1104178393.pdf
```
```
https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-122/issue-3/Large-field-renormalization-II-Localization-exponentiation-and-bounds-for-the/cmp/1104178467.pdf
```

What to look for in them (so the reading is one session): CMP 122 II, the statement of the bounds for the R operation:
is the large-field factor of a region written as `exp(local terms)` with **two-sided** bounds (then UV1's clause (B)
follows by a short Peierls argument, and c4b's vacancy-1 form too), or as a sum over regions with upper bounds only (then
clause (B) needs the extra lemma of gap G1); CMP 109 section 1: the smallness threshold on the coupling, and whether
constants are uniform in the volume of the torus.

### A.3 UV1 as the sources support it; the gaps

**UV1 stated** (`Supplier.UVRepDefect N ν Wref rad λ' ε0 p K`, named hypothesis): for every level `k` and volume `j`,
on the `L_*` torus: (D) `ν k j = weightMeasure Haar (e^{−S})`; (L) `S = ∑_X E X`, `E X` local on `X`; (G) where no link of
`X` is bad, `|E X − Wref j X| ≤ ē X` with `∑_{X ∋ z} ē X e^{λ' diam X} ≤ ε0`; (B) bad events measurable, local (bad at
`y` is measurable for the field outside range `rad` of `x` when `linkDist x y > rad`), and conditionally rare:
`ν(Bad x ∩ E) ≤ p ν(E)` for every event `E` of the field outside range `rad` of `x`; (K) at most `K` links within `rad`.
Sup norm in (G) (C1 is what a W1 condition would eventually need; not formalised).

**Translation lemma** (`uvRepDefect_cylinder`, S given UV1): for every `k`, `j`, the law of the bad set satisfies
`∑_B q B 1[U ⊆ B] ≤ (p^{1/K})^{|U|}` for every `U`, together with clause (G) for the same bad sets. This is exactly the
defect hypothesis `hcyl` of Part B (`expect_effWeight_le`, `defect_decay_W`). Proof: greedy extraction of a separated
subset (`exists_sep_subset`, `|U| ≤ K|U'|`), chain rule over it (`measure_biInter_le_pow`), the law of the defect set
(`sum_badLaw_cyl`). This replaces the Liggett-Schonmann-Stacey domination by the cruder cylinder form, which is all the
Peierls sum uses.

**What the sources give against this statement:**

| clause | OpenAI | Balaban (by review and Dimock) |
|---|---|---|
| (D), (L), uniformity | given | given per review (finite torus, inductive constants) |
| (G) with `Wref` = the level's own action | given, `ε0` = allowance budget `β̂^{-11/10}` | given (`E_k(X) ≤ λ_k^β e^{−κ d}`) |
| (G) with `Wref` = Wilson at one `β_*` | not given (G2) | not given (the leading action renormalises; closeness to Wilson is not the form) |
| (B) | not given (G1) | not seen; possibly via the R operation of CMP 122 II |
| (K), locality | given (`flags` reads one plaquette layer) | given (cubes) |

**The gaps, precisely.**

* **G1 (the probability clause).** Needed: `ν(Bad x ∩ E) ≤ p ν(E)` for `E` measurable outside range `rad`, with `p`
  small and uniform in `k`, `j`. In the OpenAI form the numerator is bounded by upper bounds (`K ≤ b`; the clipped
  plaquette term grows linearly above the threshold, so a flagged plaquette carries at least `β·linear·t²` in that
  term, with `β ≥ 4.7·10^5`; the other terms of the exponent are not signed, so this is suppression only up to them).
  The **denominator** is the issue: comparing a configuration with `x` flagged to one
  with `x` healthy and the same outside requires the exact-cover gas to factor across the change, and it does not: the
  polymers covering the outside flags must cover them exactly, their activities read the field one layer beyond their
  support (`UsesFinal`, `inspected`), and they may vanish when `x` is healthy. Upper bounds allow the gas restricted to
  "`x` healthy" to be zero, which makes the conditional probability 1. So clause (B) needs either (a) a lower bound on
  the gas restricted to configurations healthy near `x` (relative to the same outside), i.e. the lower-bound problem of
  c4b in ratio form, or (b) a two-sided exponentiated form of the large-field factors (Balaban's R operation, if CMP 122
  II states it so). Size: one contour-removal lemma (paper, a few pages) if (b) holds; otherwise an addition to the
  construction. The **marginal** bound `P(x bad)` has the same problem (removing a flagged region changes the cover of
  its neighbours), so "probability bounds are cheap" (c4b, click 3) holds only after (a) or (b).
* **G2 (the reference action).** The OpenAI small-field action is `β ×` a clipped multi-loop action with summable
  coefficients (budget `C`, not small) and depth-dependent path data, plus tiny terms. So UV1 holds with `Wref` = that
  action at each `(N, m)`, not with one Wilson action. For Part B this is harmless (GDS is asked per environment, for
  whatever action is there). For the blueprint's IR statement "stable under small changes of the action" it means: IR must
  be stated uniformly over the **budget class** of actions, not over a neighbourhood of Wilson.
* **G3 (where the supplier ends).** The OpenAI bounds hold only for `β ≥ 9.4·10^5` at their coarsest level. The
  supplier's `L_*` is therefore at `g² ≲ 4·10^-6`, astronomically far (in scale) from any point where an infrared
  argument could start; segment 2 (or IR itself) would have to carry the whole running from there. Balaban's thresholds
  are "sufficiently small" without numbers (per review and Dimock). Blueprint consequence: "a small fixed `ḡ`" is
  available from the literature only as "some unspecified small `ḡ`"; any IR strategy that needs a specific `L_*` is not
  fed by a published bound.

**Lean (Part A).**

| Lean | exact statement | mark |
|---|---|---|
| `exists_sep_subset` | conflict reflexive, symmetric, `|{y : conf x y}| ≤ K` ⇒ every `T` has a pairwise non-conflicting `T' ⊆ T` with `|T| ≤ K|T'|` | D |
| `measure_biInter_le_pow` | `P` probability; `P(Bad x ∩ E) ≤ p P(E)` for `E ∈ 𝒢 x`; `Bad y ∈ 𝒢 x` for non-conflicting `y ≠ x` ⇒ `P(⋂_{x ∈ T} Bad x) ≤ p^{|T|}` for pairwise non-conflicting `T` | S (small) |
| `badSet`, `badLaw`, `sum_badLaw_cyl` | `q B = P{badSet = B}`; `∑_B q B 1[U ⊆ B] = P(⋂_{x ∈ U} Bad x)` | D |
| `cylinder_of_condBound` | the above with `0 < p ≤ 1`, `K > 0` ⇒ `∑_B q B 1[U ⊆ B] ≤ (p^{1/K})^{|U|}` | S (small) |
| `UVRepDefect` | named hypothesis, clauses (D), (L), (G), (B), (K) above | named hypothesis (open: G1, G2) |
| `uvRepDefect_cylinder` | `0 ≤ rad`, `0 < p ≤ 1`, `K > 0`, UV1 ⇒ for every `k`, `j`: clause (G) and the cylinder bound with `p0 = p^{1/K}` for the same bad sets | S given UV1 |

## Part B. Dobrushin with rare defects

### B.1 The form chosen, and why

Three facts decide the form.

1. **Walk sums cannot have defects, path sums can.** Dobrushin's theorem is a Neumann series over walks; a walk can
   bounce between two strongly coupled defect sites forever, so any single-site version with large defect columns
   diverges. Disagreement percolation sums over self-avoiding paths, where a defect costs its probability once. So:
   defects go **inside blocks** (a defect cluster plus a collar of good sites), and distance is counted **on good sites
   only**. The block form of the existing W1 core (`OneScale.BlockSpec.cov_le_weighted_W`, an abstract weight) then
   proves the quenched theorem without new analysis; the probabilistic content moves to a Peierls bound on the
   effective distance, over self-avoiding paths.
2. **The defect set must be an environment.** A sup-norm condition sees every configuration; "bad sites" must be fixed
   before the condition is asked. So the theorem is stated for a measure **given** the defect set (an external
   environment, or Balaban's large-field set by conditioning on it), and averaged over the set.
3. **The averaged conditional covariance is not the covariance.** For `μ = ∑_B q B μ_B`,
   `Cov_μ = E_q Cov_{μ_B} + Cov_q(μ_B f, μ_B g)` (`mixture_cov_eq`). The second term is not controlled by any hypothesis
   on the conditional specifications (B.4, mixture). So the Lean theorem is exactly the first term; the second is B.5.

### B.2 Lean names and exact statements

`EffDist.lean` (graph `G` on the sites, `Δ` = max degree, `Bad` a finite set of defect sites):

| Lean | exact statement | mark |
|---|---|---|
| `walkCost`, `effDist`, `effWeight` | cost of a walk = number of distinct good sites after its start; `effDist G Bad u S` = least cost of a walk from `u` into `S` (ℕ); `effWeight = e^{−λ effDist}` | definitions |
| `effDist_self`, `effDist_le_add` | `u ∈ S ⇒ effDist = 0`; `G` preconnected, `S ≠ ∅` ⇒ `effDist(x,S) ≤ effDist(x,{y}) + effDist(y,S)` | D |
| `effWeight_le_mul`, `effWeight_le_of_effDist` | `w(y) ≤ e^{λ effDist(x,{y})} w(x)`; with `effDist(x,{y}) ≤ D`: `w(y) ≤ e^{λD} w(x)` | D |
| `walkCost_bypass_le`, `card_tail_of_isPath` | shortening a walk to a path does not raise its cost; a path of length `n` visits `n` distinct sites after its start | D |
| `expect_prod_le` | `∑_B q B 1[U ⊆ B] ≤ p0^{|U|}` ∀`U`, `0 ≤ r ≤ 1` ⇒ `∑_B q B ∏_{v ∈ T}(1 if v ∈ B else r) ≤ (p0 + r)^{|T|}` | S (small) |
| `sum_card_walks_le` | degree `≤ Δ` ⇒ `∑_v #(walks of length n from u to v) ≤ Δ^n` | D |
| **`expect_effWeight_le`** | `G` preconnected, degree `≤ Δ`, `q ≥ 0` cylinder-dominated by `p0 ≥ 0`, `λ ≥ 0`, `S ≠ ∅`, `d ≤ dist_G(u, s)` ∀`s ∈ S` ⇒ `∑_B q B e^{−λ effDist_B(u,S)} ≤ ∑_{n ∈ [d, |V|)} (Δ(p0 + e^{−λ}))^n` | **S** |
| `expect_effWeight_le_geom` | the same, `x := Δ(p0 + e^{−λ}) < 1` ⇒ `≤ x^d/(1 − x)` | S |

`Quenched.lean`:

| Lean | exact statement | mark |
|---|---|---|
| `blockMass`, `sum_block_inter_comm` | `m(a) = ∑_{j ∋ a} |B_j|`; exchange of block and site sums | D |
| **`quenched_defect_W`** | `μ` probability, `P : BlockSpec μ J`, W1 influence bounds `k` (cost `c ≤ Dc`), `GDS P.block k γ`, coverage `≥ cmin ≥ 1`, `λ ≥ 0`; every non-zero influence of `x` on block `j` reaches effective distance `≤ D1` into the block; blocks of effective diameter `≤ D0`; `γ e^{λD1} < 1`; `f` bounded with oscillations `vf` on `A`, `g` depending on `S_g ≠ ∅` with Lipschitz constant `Lg` ⇒ `|Cov_μ(f,g)| ≤ Lg Dc/(1 − γ e^{λD1}) · e^{λD0} · ∑_{a ∈ A} vf a · m(a) · e^{−λ effDist(a, S_g)}` | **S** given `cov_le_weighted_W` |

`Annealed.lean`:

| Lean | exact statement | mark |
|---|---|---|
| `annealed_of_quenched` | any quenched bound `Cv B ≤ K ∑_{a ∈ A} vf a · m_B(a) · e^{−λ effDist_B(a, S_g)}`, `E_q m_B(a)² ≤ M²`, `R ≤ dist_G(A, S_g)`, `x := Δ(p0 + e^{−2λ}) < 1` ⇒ `E_q Cv ≤ K M (∑ vf) √(x^R/(1 − x))` (Cauchy-Schwarz, Peierls at rate `2λ`) | S |
| `DefectSpecW` | for one defect set `B`: a block specification of `μ B` with the hypotheses of `quenched_defect_W` and block masses `≤ m_B` | definition |
| **`defect_decay_W`** | `G` preconnected, degree `≤ Δ`; defect law `q` cylinder-dominated by `p0`; for every `B`, `DefectSpecW` with the same `γ, D0, D1`; `γ e^{λD1} < 1`; `E_q m_B(a)² ≤ M²` on `A`; `R ≤ dist_G(A, S_g)`; `x = Δ(p0 + e^{−2λ}) < 1` ⇒ `E_q |Cov_{μ B}(f, g)| ≤ Lg Dc/(1 − γ e^{λD1}) · e^{λD0} · M · (∑_{a ∈ A} vf a) · √(x^R/(1 − x))` | **S** |
| `mixture_cov_eq` | `∑ q·Ffg − (∑ q·Ff)(∑ q·Fg) = ∑ q·(Ffg − Ff·Fg) + (∑ q·Ff·Fg − (∑ q·Ff)(∑ q·Fg))` | D |
| `mixture_counterexample` | two environments with weight ½ and conditional means 0, 1: mixture covariance `= 1/4` | D |

Uniformity: nothing in any bound depends on the number of sites; the rate is `−½ log(Δ(p0 + e^{−2λ}))`. Finite tori
are the intended instance (any finite graph works).

### B.3 Compatibility with c5c-repair

`quenched_defect_W` calls only `OneScale.BlockSpec.cov_le_weighted_W` (W1 Theorem A core with an abstract weight and
one constant `E` on non-zero influences). That core needs a finite range, here **in the effective metric** (`hD1`),
which is natural for collared blocks but still a finite range. If c5c's weighted W1 Theorem A (no finite range,
`∑_j k_j(x) e^{λ E_j(x)} ≤ γ c(x)`) lands with an abstract-weight core like `Attempts.R3.cov_le_weighted_w`, the proof
of `quenched_defect_W` goes through unchanged with `e_j(x) = e^{λ ρ(x, B_j)}`, `ρ` the effective distance; the annealed
layer (`annealed_of_quenched`) takes any quenched bound of the stated shape and does not change. The sup-form variant
is the same proof on `Attempts.R3.cov_le_weighted_w` (not written: the route is W1).

### B.4 Unit tests

| test | what the theorem says | verdict |
|---|---|---|
| photon (4D U(1), weak coupling) | good sites must satisfy GDS; the U(1) single-link W1 column is `18·(2/π)β ≥ 1` for `β ≥ π/36` (`Certified/AdjointW.lean` docstring, from r2-curvature). At weak coupling **every** site is good in the UV1 sense (small field) and **no** site contracts: `γ ≥ 1`, the hypothesis `γ e^{λD1} < 1` fails, nothing is concluded. The defects are not where the photon fails; the good sites are | pass |
| Z2 (weak coupling) | as the photon at weak coupling (no contraction), so no claim; at strong coupling GDS holds and the theorem gives decay, consistent with the Z2 gap; no area law follows (none is claimed) | pass |
| mixture | the conditional covariances can all vanish while the mixture covariance is constant (`mixture_counterexample`); the theorem bounds only `E_q Cov_{μ_B}`, so it makes no false claim; it also shows that decay of `μ` needs B.5 | pass, and it is the reason for B.5 |
| deconfinement (`L < 1/T_c`) | finite torus statement; GDS in worst-case form fails for coarse theories below `1/T_c` (c2a), no claim | pass (vacuous) |
| Banks-Zaks | as the photon (weakly coupled at every scale, no contraction) | pass |
| UV1 for the photon | a weak-coupling U(1) theory has a UV1-type representation with rare monopole-type defects; the translation lemma hands Part B a cylinder-dominated defect law, and Part B still gives nothing (good sites fail). UV1 is not decay | pass |

### B.5 The missing piece, precisely

The route consumes the covariance of the blocked law `μ` itself (`BlockGapUnifW`). With a defect set `Bad` that is a
function of the field (OpenAI `flags`, Balaban's large-field set),

  `Cov_μ(f, g) = E[Cov(f, g | Bad)] + Cov(E[f | Bad], E[g | Bad])`.

`defect_decay_W` bounds the first term (with `μ B = μ(· | Bad = B)`, which for a hard large-field indicator is again a
Gibbs measure, with the small-field constraint built into the good region). The second term needs the **defect field
to mix**: `E[f | Bad]` depends on `Bad` mostly near `A` (a Dobrushin comparison in the environment), so the term is a
covariance of two local functions of the field near `A` and near `S_g`, each nonzero only where a defect is present.
Two ways to close it, neither done:

1. **Disagreement percolation (van den Berg-Maes) with the conditional bound used sequentially.** Couple two copies
   site by site; a site is "open" if its conditional laws in the two copies disagree, which happens with probability
   `≤ γ`-type at good sites and `≤ 1` at defects; UV1's clause (B), being a bound **given everything outside a range**,
   is exactly the form that survives the sequential revealing. The disagreement cluster is dominated by a subcritical
   percolation with parameter of order `Δ(γ + p)`, which bounds the full covariance. This is the honest theorem; in Lean
   it needs couplings of the conditional laws on SU(2) configurations (measure-theoretic couplings are not in the
   library), a large module.
2. **A bootstrap in the distance.** Write `D(R)` for the worst normalised covariance at distance `R`; the decomposition
   gives `D(R) ≤ Q(R) + (term of the environment)`, and the environment term is a covariance of rare-event functions at
   distance `R − 2r`. It closes only with a **multiplicative** gain (`≤ c(p)·D(R − 2r)` with `c(p) < 1`), which the
   sup normalisation does not give (the rare-event functions have sup norm 1). So a bootstrap needs an `L²`-type
   normalisation; open.

For an external, independent environment (e.g. auxiliary noise variables) the second term is controlled by a comparison
estimate and independence; the large-field flags are not of that kind (A.1).

### B.6 Where Part B sits on the route

Part B applies where good sites contract: at a strong-coupling coarse scale (strategies (a) and (b) of the blueprint),
not at `L_*` (where nothing contracts, B.4 photon). What it needs, and from whom:

* the defect law: cylinder-dominated, `p0 < (1/Δ) − e^{−2λ}`; from UV1 at `L_*` via `uvRepDefect_cylinder`, **then
  carried from `L_*` to `L1`** (segment 2: call an `L1` block bad if it contains an `L_*` defect; a union bound inside
  each block and the separated-subset argument across blocks should give a cylinder bound with a worse `p0`, roughly
  `(L_*-sites per L1 block)·p0` to a root; paper, to check, not formalised);
* GDS for collared defect blocks and for good sites in the effective metric, for the coarse action given the defects:
  this is the **gap content** (the review's 1.4 point: a typical-configuration statement, which is what fitted actions
  measure, now in a form a theorem consumes);
* the environment term (B.5).

## Next steps

1. **Owner (one minute):** download the five Balaban PDFs above into this folder. Then one reading session on CMP 122 II
   decides G1: two-sided exponentiated large-field factors (then clause (B) is a short lemma and c4b's `PolymerRepW`
   is within reach) or upper bounds only (then clause (B) is a new result).
2. **Lean, large (the honest annealed theorem):** disagreement percolation with conditional bounds (B.5, way 1), on a
   finite torus, for laws given by densities against product Haar; it subsumes `defect_decay_W` and removes the
   environment term. A first step that is medium-sized: the same for finite single-site spaces (no measure-theoretic
   couplings needed), to fix the combinatorics.
3. **Blueprint (for c5a-v4):** in 3.2 replace "within ε0 of Wilson at a fixed `β_*`" by "within ε0 of the level's own
   action from a budget class" (G2), record G3 (the OpenAI `L_*` is at `β ≥ 9.4·10^5`), and in 3.3 (c) say that the
   rare-defect theorem bounds the averaged conditional covariance and that the environment term is a separate input.
4. **Paper, small:** the `L_*` to `L1` transfer of the cylinder bound (B.6, first bullet).

## Clicks

* **Disagreement percolation and Kotecky-Preiss meet on paths.** c4b's KP induction and this Peierls bound both win by
  making a defect (a polymer, a bad site) cost its activity **once**: KP through anchored Moebius coefficients, the
  Peierls bound through self-avoiding paths. Dobrushin's walk sums cannot do this; blocks are how the two are glued.
* **The exact-cover finding returns in probability form.** c4b: sup-norm locality needs lower bounds on large-field
  weights. Here: even the probability of a large field, conditional or marginal, needs them (G1), because the
  denominator of a probability is a partition function with the defect removed. "Probability bounds are cheap" was
  half right: cheap given a two-sided large-field representation, which is what CMP 122 II's title promises.
* **The mixture test is the environment term.** The one unit test that a rare-defect theorem can fail silently is the
  mixture; in Lean it is a two-line identity, and it is exactly the second term of the total covariance.

## Files

- `../../../formal/ProofPhase/Defects/EffDist.lean`: `walkCost`, `effDist`, `effWeight`, `effDist_le_cost`,
  `exists_walk_effDist`, `walkCost_nil`, `effDist_self`, `walkCost_append_le`, `effDist_le_add`, `effWeight_nonneg`,
  `effWeight_of_mem`, `effWeight_le_mul`, `effWeight_le_of_effDist`, `walkCost_bypass_le`, `card_tail_of_isPath`,
  `expect_prod_le`, `exp_walkCost_eq`, `sum_card_walks_le`, `expect_effWeight_le`, `expect_effWeight_le_geom`.
- `../../../formal/ProofPhase/Defects/Quenched.lean`: `blockMass`, `blockMass_nonneg`, `sum_block_inter_comm`,
  `quenched_defect_W`.
- `../../../formal/ProofPhase/Defects/Annealed.lean`: `annealed_of_quenched`, `DefectSpecW`, `defect_decay_W`,
  `mixture_cov_eq`, `mixture_counterexample`.
- `../../../formal/ProofPhase/Defects/Supplier.lean`: `exists_sep_subset`, `measure_biInter_le_pow`, `badSet`,
  `badLaw`, `badLaw_nonneg`, `measurableSet_badSet_eq`, `sum_badLaw_cyl`, `cylinder_of_condBound`, `UVRepDefect`,
  `uvRepDefect_cylinder`.
- Here: `setup.sh`, `build.sh`, `axioms.sh`, `grepml.sh` (read-only Mathlib grep), `axioms.log`.

## References (reading marks in A.1, A.2)

Balaban CMP 109 (1987) 249; 116 (1988) 1; 119 (1988) 243; 122 (1989) 175, 355. Dimock arXiv:1212.5562 (read in part),
1108.1335, 1304.0705, 2009.01156. van den Berg, Maes, Ann. Probab. 22 (1994) 749 (disagreement percolation; recalled).
Liggett, Schonmann, Stacey, Ann. Probab. 25 (1997) 71 (domination by product measures; recalled, replaced here by the
cylinder form). Dobrushin, Theory Probab. Appl. 15 (1970) 458 (recalled). OpenAI construction, commit `b379615`, files
as cited. Project: `../c4-fable/BLUEPRINT-v4-DRAFT.md`, `../c4-fable/REVIEW.md`, `../c4b-seg1/NOTE.md`,
`../ws4-existence/NOTE.md`.
