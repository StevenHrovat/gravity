# What the OpenAI Lean construction proves that bears on (H1) `EffectiveConvergence`

Date: 2026-11-21. Reference study only; no code copied or reused. Sources: `yang-mills-group/YM` (shallow clone, pushed
2026-11-15), the unmodified submission in `submissions/openai-20261028/submission/`, the committee's `docs/assessment-1.pdf`
(10 Nov 2026). Nothing was built. **[Lean]** = I read the statement in the source. **[usage]** = the submission's own
`verification/declaration-usage.tsv` lists the declaration as reached by a headline theorem. **[doc]** = only README or
assessment text. Our side: `../formal/OneScale/Effective/Physical.lean`, `Robust.lean`, `Reduction.lean`; `attempts/ROUND-1.md`;
`SURVEY-LEAN.md` §4.

## Summary

1. **Their RG stops at weak coupling, far below our L₁.** The construction defines its length unit as the scale where the
   effective coupling equals a fixed reference value `bar` (`RG.History.Selected.reaches`: β at level 0 equals `bar` for every
   cutoff N and volume p) **[Lean, usage]**. The data structure has no levels coarser than this unit. The bounds hold at every
   level, level 0 included, only in the small-field regime (`Calendar.Fits.smallField`), and the reference value has to satisfy
   `Supply.Bar.threshold`. My arithmetic on that condition gives **`bar` ≥ e^13.71 ≈ 9.0·10⁵**. So the top of their controlled
   flow is a scale where g² is about 10⁻⁶, deep in perturbation theory. Extrapolating one loop (heuristic, not in their code),
   the coupling becomes of order one only about bar/b ≈ 10⁷ e-folds further up (b = 11C_g/(24π²)).
2. **This settles the survey's open point.** The coupling at the physical box size L_p is **never controlled**, and it does not
   need to be. At fixed p the level-0 theory is a finite-dimensional integral over a unit-lattice torus of side L_p = 4(M+p+1).
   The UV limit only needs the level-0 effective density to converge. The infinite-volume limit comes from compactness
   (reflection positivity, chessboard estimates; [doc]). The middle range is bypassed, not crossed.
3. **The result closest to H1** is per-level convergence of the effective coupling and of the polymer activities as N → ∞, at
   each fixed level m and each fixed volume p, in their strong activity norm (`Legato.Campaign.Winter.convergence`)
   **[Lean, usage]**. It holds at the wrong scale (their unit, not L₁), in the periodic state only, with exponential tails
   instead of finite range, small-field-weighted (no lower bounds on large-field activities), and with no rate uniform in p.
4. **A bridge has two stages.** (A) At their unit scale: relative (multiplicative) convergence of the level-0 density on *all*
   configurations, large fields included. (B) From the unit to L₁: an elementary finite-volume continuity lemma. It works per
   volume, and per-volume convergence is enough in their order of limits (mesh, then volume). **But the bridge moves the
   hard part.** All of the running from β ≈ 10⁶ down to O(1) would then sit inside the one fixed lattice theory that (H2) is
   about.
5. **Nothing in the construction implies or contradicts a gap.** The committee says so explicitly. If (H1) and (H2) held,
   they would also settle the uniqueness of the infinite-volume limit for block observables, which the committee lists as
   open. That is a consistency check, not a conflict.

## 1. The main theorem (Q1)

- **Headline.** `YangMills.jointExistence : JointExistence` (`ChallengeSpec.lean:186`) **[Lean]**. For every closed matrix
  group whose Lie algebra is simple and nonabelian there is one `WilsonFamily C` with `WilsonRegularity C`, and for every
  strictly increasing volume order p there are a subsequence q and a `Hierarchy T` with `T.Properties (p ∘ q)`. The four
  properties are `wilson` (convergence), `reconstruction` (Wightman, selected phase), `ope` and `nonfree`. The detailed form
  is `YangMills.constructed` (`Construction.lean`).
- **Objects** (`PublicWilson.lean`) **[Lean]**:
  - the Wilson law on the periodic lattice (ℤ/(L_p·D_N))⁴ with mesh a_N = 1/D_N;
  - D_N is a product of odd block factors ≥ 3, with log L_m / log D_m → 0 (`Schedule.Gentle`);
  - L_p = 4(M+p+1) (`Supply.page`, `Supply.book`), M a large fixed constant;
  - the bare coupling `beta N p` is chosen by the construction and **depends on p**. The public statement only requires
    β_{N,p}/log(1/a_N) → slope uniformly in p (`WilsonRegularity.running`).
- **Observables.** Renormalized, gauge-invariant local polynomial insertions with fixed stencils (tokens), smeared against
  tests supported away from coincidences and strictly inside (−L_p/2, L_p/2)⁴. No block variables and no Wilson loops.
- **Limits** (`WilsonFamily.Converges`) **[Lean]**. For each fixed p the smeared moments converge as N → ∞ along the **entire**
  chosen sequence a_N (not a subsequence). Then, along the refined volume order p∘q, the row limits converge
  (**subsequence** in volume). No universality in the spacing sequence (assessment §4).
- **Assumptions.** None beyond the group hypotheses; the family and the β_{N,p} are existential outputs. A textual scan shows
  zero `axiom` declarations and one `sorry`, at `Challenge.lean:6` (the reference statement, by design). The committee's axiom
  audit reports only the three standard axioms. I did not rebuild.

## 2. The RG map (Q2)

- **Levels** (`RG/History.lean`) **[Lean]**. Level N is the bare lattice and level 0 the coarsest, at spacing `Schedule.a 0 = 1`.
  The fields of `History.Selected` are all [usage]:
  - `starts`: level N is the bare Wilson density;
  - `steps`: level m is the push of level m+1 by one block step;
  - `represents`: bounds at every level;
  - `reaches`: β at level 0 equals `bar`;
  - `running`: β_m tracks β̂_m = bar + slope·log(1/a_m).
- **Block variables** (`RG/Block.lean`, `StepData`) **[Lean]**. The blocking is a **stochastic kernel**, not a deterministic
  map. Per coarse site a random gauge frame is chosen (`likelihood`). The fine parallel transport along the straight path of
  length L_m across the block, conjugated by the frames, gives a "prediction" Q_e. The coarse link V_e is then drawn with
  heat-kernel-like noise ∝ exp(−β·penalty·price(V_e Q_e⁻¹)). The kernel has total mass 1 (`IsKernel.total`), so the level-m
  measure is exactly the law of a coarse random lattice gauge field (`History.partition_eq`).
- **What is controlled per step.** The effective density at level m (`Rep.eval`) is
  exp(v|Λ| − kinetic path channels(β) − Σᵢ masked Eᵢ) × gas, where gas = Σ over admissible families of ∏ Kᵢ.
  - Eᵢ (small-field activities): local on their support, gauge invariant, C^order on configurations where no plaquette in the
    support exceeds the threshold (`Healthy`), zero at the flat field, set to zero off the healthy set (`masked`).
  - Kᵢ (large-field activities): only upper sup bounds.
  - Both are summed with weights exp(κ·coverNumber(support)) (`BudgetPoint.mass`), so they have exponential tails, not
    finite range.
  - `History.Conv`: β_m stays in [β̂_m/2, 2β̂_m], and the E/K budgets use constants that depend on m only, **not on p**.
  - `History.Transfer`: |β_{m+1} − β_m − slope·log L_m| ≤ drift.
- **Up to which scale.** Level 0 only. `Fits.smallField m` (threshold ≤ 1) and `Fits.delayed m` (β̂_m > 1) hold for all m.
  The reference value is fixed by `Supply.Bar` (`Price/Intent.lean`, docstring "Barrier for smallness independent of the first
  spacing which is one") **[Lean, usage]**. It must lie above an entry threshold for the RG estimates (`ready`), and every
  x ≥ bar must satisfy x^(−1/2)·exp((ln ln x)²) ≤ 1 (`threshold`). The second condition alone forces bar ≥ ≈ 9.0·10⁵ (numeric
  check: it fails at ln x = 13.706). So **control ends where the coupling is still tiny.** There is no control at an O(1)
  coupling and no statement about any scale coarser than the unit.
- **How the coupling at the physical box is fixed.** It isn't. The unit is *defined* by β(unit) = bar: per (N, p) the bare
  β_{N,p} is shot so that the flow lands exactly on bar (`Extension/UV/Shoot.lean`, `Selected.reaches`;
  `YMReview.CommonScale.reference_coupling` in the committee's checks). The box L_p is just a large finite torus in those
  units. The infrared side is handled only by compactness.

## 3. Relation to our H1 (Q3)

**What they give that comes closest.** `Winter.convergence` (`FullVolume/Glide/Vac.lean`) is a field of a structure built by
`Campaign.offers`, and both are reached by the headline proof [usage]. For each p and each level m: for trajectories whose
level-0 coupling converges, the level-m coupling and the level-m activity data converge as N → ∞, in a fixed normed space per
(m, p). The docstring calls that space "E/K anchored norms, hard flags, K sup and E regular derivatives, with the support
costs". I did not unfold the definition of that norm. With m = 0 this is convergence of the effective theory at the unit
scale, as a polymer representation of a density on the unit torus.

Gaps, item by item:

| H1 asks | They give | Gap |
|---|---|---|
| scale L₁ (coupling O(1)) | level 0, β = bar ≳ 9·10⁵ | about 10⁷ e-folds (one-loop estimate); no control past level 0 |
| conditional laws, uniform over **all** boundary conditions | a density in the periodic state; no specifications | they never condition. Eᵢ is controlled only on healthy configurations and Kᵢ only from above, so a ratio (conditional law) on large-field boundaries is not controlled |
| finite range (`IsLocal` shells) | supports of any size, including torus-wrapping ones, with exp(κ·cover) weights | tails. At L₁ the coarse conditional laws of a blocked measure are not finite range anyway, so Theorem A needs a version with tails (`decay_of_dev_H` already takes summable deviations) |
| a deterministic block map Φ (`gap_of_effective_fine`) | a stochastic kernel (frames and noise) | harmless: enlarge the fine space by the independent noise |
| δ_k uniform in the volume v | convergence per p, no rate in p; the budgets are uniform in p | no uniform δ. But see §4: per-volume δ suffices in their order of limits |
| one sequence a_k → 0 | the full limit along their chosen a_N, with β_{N,p} depending on p | compatible (our μ v k may depend on v). No universality |
| block observables | local renormalized fields at scale a_N | relating our block-observable decay to their local fields needs a separate argument |

## 4. What a bridge lemma would need (Q4)

**Observation about our own theorem.** In `gap_of_effective` and `gap_of_effective_W` the rate m = λ/(2L₁) and the prefactor C
do not depend on δ; only k₀ does. So a variant of (H1) with δ_k(v) → 0 *for each v* still gives decay with **volume-independent
m and C**, for k ≥ k₀(v). That is enough when the mesh limit is taken first at fixed volume and the volume limit afterwards,
which is exactly the OpenAI order. Stating this per-volume variant in Lean is a few lines and widens what H1 must deliver.

**Stage A: unit scale, per volume. This is the missing estimate.** Take the level-0 effective density ρ_{N,p} on the unit torus.
We need *relative* uniform convergence on **all** configurations, large fields included: a local form, uniform in the boundary,
of sup_U |log ρ_{N,p}(U) − log ρ_{∞,p}(U)| → 0. In practice:
1. Write the large-field gas as exp(a summable potential), by a cluster expansion in the Kᵢ (possible because the Kᵢ are tiny:
   `forcedAllowance` = exp(−monitor^{1/5})), or prove ratio bounds gas_N/gas_∞ ∈ [e^{−δ|S|}, e^{δ|S|}] under local changes.
2. Then prove, for every unit cell x, Σ_{X∋x} ‖Φ_N(X) − Φ_∞(X)‖_sup ≤ δ_N on all configurations.

Their norm controls Eᵢ only on healthy configurations and Kᵢ only from above, so this needs a **lower bound on the large-field
activities**, or an equivalent positivity statement that their construction does not supply.

**Stage B: unit scale to L₁, no N dependence.** This step is elementary in finite volume. If ρ' = ρ·e^h with |h| ≤ ε, then every
conditional law, of any functions of the field given any others, changes by a Radon–Nikodym factor in [e^{−2ε}, e^{2ε}]. Hence
`TVClose`/`SpecDist` hold with δ ≤ e^{2ε} − 1, **uniformly over all boundary conditions**. With ε ≤ |Λ_v|·δ_N, Stage A gives the
per-volume form of H1 for any block variables at L₁, in TV (H form). The W form (`InfluenceDevW`) needs the same estimate on
boundary differences, which follows the same way with factor 2. Finite range fails, so Theorem A must be the tail version
(`decay_of_dev_H` with summable deviations).

**The catch.** After Stage B the theory at L₁ is the fixed unit-lattice theory ρ_∞, at β = bar ≈ 10⁶, blocked by about 10⁷
e-folds. (H2) then asks for GDS for *that* theory, so all of the asymptotic-freedom running from weak to O(1) coupling has moved
into (H2). The other option keeps (H1) honest: extend RG control from bar down to O(1) coupling. That is the intermediate-coupling
problem, and their method stops short of it by construction: `smallField`, `Bar.threshold` and the polylog thresholds all need a
large β. Either way, the bridge does not shrink the hard part; it only decides which hypothesis holds it.

## 5. Gap and H2 (Q5)

- **No implication for the gap.** The committee says "no evidence for or against a mass gap" (assessment §2, §8) **[doc]**, and
  nothing I read in the source has decay content beyond compactness bounds.
- **No conflict.** `nonfree` only excludes finite sums of free massive Wick profiles, the short-distance free-Maxwell limit is a
  UV statement, and vacuum uniqueness holds only in the selected phase of the character decomposition. All of this is compatible
  with a gap. Their construction requires a simple nonabelian algebra, so it says nothing about U(1) and does not interact with
  our photon test.
- **What we would add.** (H2) is GDS for the limit, uniform in v, and through `effective_reduction` it passes to the blocked
  theories. It would give a unique infinite-volume state for the block field. Applied to their family, it would answer the
  committee's open question 1 (uniqueness of the volume limit) for block observables.
- **Reflection positivity of the blocked measure** (our docstring's precondition for the spectral reading) is not addressed by
  their kernel. Its symmetry (`BlockControl.symmetric`) is invariance under lattice symmetries, not RP. Not verified either way.

## 6. Reading in the project's terms

This section restates the findings above in the owner's words (`PREP.md`, last two sections); it adds no technical claim.

- **Which half.** The OpenAI construction covers a large part of the **quantum half (H1)**: the causal chain of layers from the
  fine grid upward, along which the theory is built, with the running coupling (asymptotic freedom) controlled at every layer.
  It does so along their chosen spacing sequence (the full sequence at fixed volume, subsequences only in the volume), and only
  in the periodic, self-closed state.
- **How far up the layers.** Up to their reference layer, where the coupling is still about 10⁻⁶ (β = bar ≳ 9·10⁵), deep in
  the loop regime. The chain stops there by design: the unit of length *is* "where the coupling equals bar". It does not reach
  the node's scale L₁, where the quantum half should hand over to the classical half. By a one-loop estimate that handover lies
  about 10⁷ e-folds higher.
- **What is missing for H1, in these terms.**
  1. The last and hardest stretch of the chain: the layers from weak to O(1) coupling, where loop effects stop being small.
  2. Building the existence *given any outside*. H1 asks for the block's conditional law under every boundary condition,
     whereas they build it only for the periodic world that closes on itself, and they do not control the large-field outsides.
  3. Uniformity across volumes. Per volume, H1 is enough in their order of limits (§4), so this one is the mildest.
- **The classical half.** They provide nothing for the classical half (H2): no certificate that any node forgets its outside.
  The bridge sketched in §4 shows the split is not fixed by their result. If the chain is cut at their reference layer, the
  missing layers fall to H2, which would then have to carry the remaining running as well as the forgetting.
