# Proof phase, cycle 4, workstream 2 (c4b-seg1): segment 1, from the lattice spacing to L_* (2026-11-22)

Brief: prove `EnvelopeW` at the weak-coupling scale `L_*` (running coupling `ḡ`, small and fixed) uniformly in the level `k`
and the volume `j`, and the Gaussian Lemma UV, from published small-field / large-field bounds through a Kotecky–Preiss
cluster expansion; pin the published input exactly; say where `b₀ > 0` enters and why Banks–Zaks also passes. Rules:
`../../attempts/RULES.md` (proof phase, claim discipline, all unit tests). Map: `../../PROOF-BLUEPRINT.md` (P3.4, P3.5).
Builds on `../c3d-h1/NOTE.md` (§3, §7) and `../c3a-uv/NOTE.md` (§2.1).

Lean: three new files under `../../../formal/ProofPhase/Seg1/` (`Mobius.lean`, `KP.lean`, `Envelope.lean`), built in
`~/formal-c4b` (Lean 4.34.0, Mathlib v4.34.0) against the current `H1/Split.lean`, `Assembly.lean`. All build without
warnings in `Seg1/`; `axioms.sh` prints `propext, Classical.choice, Quot.sound` for all 21 headline theorems; no `sorry`,
no `native_decide`, no new axioms (`axioms.log`). Nothing outside `ProofPhase/Seg1/` and this folder was edited. No
numerics were run (none was needed: the abstract theorem is proved, not tested).

```
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c4b-seg1/setup.sh
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c4b-seg1/build.sh ProofPhase.Seg1.Envelope
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c4b-seg1/axioms.sh
```

Marks: **S** substantive, **D** definitional or elementary. "YM" names what is Yang–Mills-specific.

## 0. Result in one paragraph

**Proved in Lean (S):** a Kotecky–Preiss theorem for hard-core polymer gases with configuration-dependent activities,
in the form segment 1 needs: if the activities satisfy `∑_{γ ∋ y} ζ̄(γ) 2^{|γ|} e^{σ(γ)} ≤ 1` for an admissible weight
`σ` (e.g. `λ'·diam + (|·| − 1)`), then `log Z = ∑_X Φ_X` with `Φ_X` depending only on the activities inside `X`, and
`∑_{X ∋ y} sup_ω |Φ_X| e^{σ(X)} ≤ log 2` **independently of the region** (`kotecky_preiss`). The proof is a new,
fully elementary induction on anchored weighted Moebius norms (no tree-graph inequality, no counting of connected sets).
**Bridge (Lean, S given one named hypothesis):** `PolymerRepW` (the `L_*` laws have density `exp(∑ E) · Z_gas(ζ)` with
local small-field terms and KP-small large-field activities, constants independent of `k`, `j`) ⇒ every `L_*` law is
a Gibbs measure of a bounded local potential and `H1.EnvelopeW` holds at rate `λ'` with one constant for all `k`, `j`
(`envelopeW_of_polymerRep`; the YM instance `envelopeW_seg1` for `(T.ym k j).map B₁`). **Pinning the input (paper,
reading):** `PolymerRepW` is the *target form*; neither source states it verbatim. The OpenAI Lean construction states
the effective density as `exp(exponent) · gas` with an **exact-cover** large-field gas (`YM/RG/Activities.lean:114`:
admissible = disjoint *and* covering the flagged set), whose log is **not** controlled by upper bounds on the activities;
Balaban's 4D papers (CMP 109–122) are the published source, readable here only at record/review level. So the brief's
premise "upper bounds suffice for the envelope" (c3d §1.4) is **true for vacancy-weight-1 gases and false for exact-cover
gases**: the translation needs either Balaban's "exponentiation" of large-field factors (CMP 122 II, by title and review)
or a **lower** bound on single-block large-field weights. **Lemma UV** is not reached: the published bounds are for the
block-field marginal; Lemma UV needs the same expansion with two observables inserted (a BIJ-type cluster-property paper
for SU(2)); the Gaussian Lemma UV is Balaban's published propagator bound for **his** blocking, and c3a's symbol estimate
for **ours**.

## 1. The published input (task 1)

### 1.1 What each source states, and how far it was read

Reading status: **record** = citation seen; **review** = zbMATH review text seen through its API (paraphrased by a fetch
tool; this session, via a sub-agent); **source** = Lean statement read by me in the OpenAI clone (`~/ym-replay/YM`,
commit `b379615`, 15 Nov 2026, submission `submissions/openai-20261028/submission`); **recalled** = from memory or earlier
project notes, not re-verified. I read **no Balaban paper in full text** (Springer pages need a login, PDFs did not
extract); everything below about Balaban beyond titles is review-level or recalled, and must be checked against the text
before any claim rests on it.

| source | what it gives segment 1 | proved / claimed | volume, uniformity | blocking | status |
|---|---|---|---|---|---|
| Balaban, CMP 95 (1984) 17; CMP 96 (1984) 223 (Propagators and RG transformations I, II); CMP 99 (1985) 389 (propagators in a background field) | exponential decay of the fluctuation covariances `G_k` (Laplacian plus block constraint), uniform in the number of steps | proved (published) | finite torus, constants independent of `k` | Balaban's averaging, block factor `L` | record; content recalled |
| Balaban, CMP 98 (1985) 17 (Averaging operations) | the deterministic block variable: parallel-transport averages over paths in a block, projected to the group | definition and regularity | — | isotropic in all 4 directions | record |
| Balaban, CMP 109 (1987) 249 (RG approach I) | small-field effective actions after `k` steps: `g_k⁻² × Wilson-type action + ∑_X E_k(X)`, `E_k(X)` local on `X`, analytic in small fields, bounded by `e^{−κ d_k(X)}`; coupling renormalisation | proved (published) | finite volume; uniform in `k` while `g_k ≤ ḡ` | his averaging | review (4D, small field, coupling renormalisation); form recalled |
| Balaban, CMP 116 (1988) 1 (RG approach II, cluster expansions) | the cluster expansions behind the `E_k(X)` | proved | as above | his | record |
| Balaban, CMP 119 (1988) 243 | inductive description of complete effective densities including large-field domains; review: stated for superrenormalisable models | proved, scope per review | — | — | review |
| Balaban, CMP 122 (1989) 175 and 355 (Large field renormalization I, II: "localization, exponentiation, and bounds for the R operation") | large-field regions suppressed by `e^{−p(g)}` per block; review of II: for 4D pure gauge theory, if the effective couplings stay small the effective densities keep their form, giving UV stability bounds like the superrenormalisable case | proved per review; the uniform `e^{±E|Λ|}` statement **not** seen | review: finite volume not stated; recalled: fixed torus | his | review |
| Jaffe–Witten, Clay problem description (2000/2004) | Balaban's programme gives ultraviolet stability of 4D lattice Yang–Mills in finite volume, not a continuum limit of correlations | summary | finite volume | — | recalled (PDF not extractable) |
| Dimock, RG according to Balaban I–III (arXiv:1108.1335, 1212.5562, 1304.0705) | the architecture (small field, large field, convergence) carried out completely, for φ⁴ in 3D | proved, **not gauge** | torus | Gaussian-soft block averaging | abstract |
| Dimock, UV stability for QED in d = 3 (arXiv:2009.01156) | the same for an abelian gauge theory | proved, 3D abelian | fixed finite volume | Balaban-type | abstract |
| Balaban, Imbrie, Jaffe, CMP 114 (1988) 257 | effective action **and cluster properties** (decay of correlations) of the abelian Higgs model: the template for Lemma UV | proved, abelian, 2–3D | — | — | record |
| Kotecky, Preiss, CMP 103 (1986) 491 | `∑_{γ' ≁ γ} |z(γ')| e^{a(γ')} ≤ a(γ)` ⇒ convergent cluster expansion uniformly in the volume | proved | volume-uniform | — | record + restatement in Fernandez–Procacci (math-ph/0605041) |
| OpenAI construction, `YM/RG/History.lean:166-181` (`Rep`, `Rep.exponent`, `Rep.eval`) | level-`m` density `= exp(v|Λ| − path channels(β) − ∑ masked Eᵢ) · gas` | Lean, statement read; proofs per committee audit | budgets with constants depending on `m` only, not on `p` (`H1-OPENAI.md` §2) | stochastic kernel (random frames, heat-kernel noise), odd block factors ≥ 3 | source |
| OpenAI, `YM/RG/Activities.lean:98-132` (`EBound`, `KBound`, `admissible`, `gas`) | `EBound`/`KBound`: sup bounds with weights `p.mass P c = exp(κ·coverNumber P)·c` (`YM/RG/Masks.lean:144`), summed per site; `admissible U b`: pairwise **disjoint** supports **and** inventories covering exactly `flags(U)`; `gas U = ∑_b 1[admissible] ∏ Kᵢ U`; `gas_one`: `gas = 1` when nothing is flagged | Lean, statement read | per site, volume-free constants | theirs | source |

### 1.2 From the published form to `PolymerRepW`: three translation steps

`PolymerRepW` (Lean, `Envelope.lean`) asks for: density `∝ exp(∑_X E X) · Z_gas(ζ)` against product Haar on the `L_*`
torus, `E X` local on `X` with `∑_{X ∋ z} sup|E X| e^{σ X} ≤ M_E`, and a **hard-core gas with vacancy weight 1**
(`Z_gas = ∑ over families of disjoint polymers ∏ ζ`, an empty site costs 1) whose activities satisfy the KP criterion;
`σ = λ'·diam + (|·| − 1)`; constants independent of `k`, `j`.

1. **Small-field part** (CMP 109, OpenAI `EBound`): matches, up to the weight. OpenAI's `exp(κ·coverNumber)` weight
   dominates `e^{λ' diam}` for `κ` large relative to `λ'` (cover number by blocks of side `B` is at least `diam/B`); the
   `|X| − 1` part is a cover-number count up to the block volume. The kinetic term (`β × Wilson action`, finite range,
   bounded on a compact group) is a legitimate `E` with `M_E ~ β`: large but fixed at `L_*` (EnvelopeW needs any finite
   `M`). Paper, elementary.
2. **Large-field part: exact cover vs vacancy 1 (the real gap).** OpenAI's gas sums over families that **cover** the
   flagged set exactly; Balaban's expansion (partition of unity `χ + (1 − χ)` per block) has the same form. For an exact-
   cover gas, `log gas` on a configuration with one flagged block is `log K(block)`, and an upper bound `K ≤ e^{−p}` bounds
   it only from above: **the sup norm of the log-potential needs a lower bound on the large-field weights**. KP (and my
   theorem) needs upper bounds only for vacancy-1 gases, where `log(1 + ζ) ∈ [log(1 − ζ̄), log(1 + ζ̄)]`. Two ways across:
   (a) Balaban's **exponentiation** of the large-field factors (CMP 122 II, by title and review) writes them as `exp` of
   local terms with bounds, which is a vacancy-1 form after factoring out the local large-field action; (b) a lower bound
   `K(γ) ≥ e^{−C|γ|}·(local action)` for the single-block weights, then divide them out (the ratios become KP-small
   activities). (a) is the published route if the text says what the title says; (b) is exactly the "lower bounds on
   large-field activities" that `H1-OPENAI.md` §3 found missing in the OpenAI construction. **Correction to c3d §1.4:**
   "an envelope needs only upper bounds" holds for vacancy-1 representations; for the exact-cover representations both
   sources use, sup-norm locality needs (a) or (b).
3. **Blocking.** Balaban averages isotropically (block factor `L`, deterministic, CMP 98); OpenAI uses a noisy kernel with
   random frames and odd block factors; our good blocking smears spatially within time slices and **decimates in time**
   (P1.8). These differ, and it matters: Balaban's propagator and effective-action bounds are proved for his averaging,
   and temporal decimation has the linear self-energy that c3a §1 identified as the noise-limit trap. **Bridge (proposed):
   run segment 1 with Balaban's averaging to `L_*` and the good blocking from `L_*` to `L₁`**, i.e. the assembly's
   blocking family is the composite `B = B_good ∘ B_Bal`. A change of block variable at one scale is not available (the
   good-blocking variable at `L_*` is a function of the fine field, not of Balaban's `L_*` variable), so the composite is
   the only bridge. Its cost: `B` must be an `RPBlocking` (commute with the site reflection `Θ`, read only the positive
   half). For Balaban's averaging this holds if the reflection plane lies on block boundaries and the path set in a block
   is reflection-symmetric (paper; to check against CMP 98; the projection to the group is pointwise and commutes with
   `Θ`). Then `blocked_wilson_rp` gives reflection positivity at every layer for free. For the OpenAI kernel the composite
   is stochastic; it needs c3d's noisy-blocking proposal (product noise per coarse link, reflection-invariant law). The
   Lean bridge is stated for an arbitrary measurable `B₁` (`envelopeW_seg1`) and for an arbitrary law family
   (`envelopeW_of_polymerRep`), so it covers both.

**Uniformity.** Balaban's constants are inductive: each RG step reproduces the bounds with the same constants as long as
the running coupling stays below a threshold; the number of steps does not enter. That is what `PolymerRepW`'s "constants
independent of `k`" transcribes, and it is the claimed (not verified here) content of the CMP 109–122 series.

## 2. Kotecky–Preiss in Lean (task 2)

`ProofPhase/Seg1/Mobius.lean` (the algebra) and `ProofPhase/Seg1/KP.lean` (the gas and the theorem). Sites: a `Fintype`
`V`; polymers: `Finset V`; activities `ζ : Finset V → Ω → ℝ` (configuration-dependent; `Ω` arbitrary).

| Lean | exact statement | mark |
|---|---|---|
| `sum_mob`, `mob_eq_of` | `h Y = ∑_{A ⊆ Y} mob h A`; coefficients are unique | D |
| `mob_mul`, `mob_shift`, `mob_insert`, `mob_upS_mul_eq_zero` | coefficients of products (union convolution), shifts `Y ↦ h(Y \ E)`, `y`-differences, up-set indicators | D |
| `Weight σ` | `σ ≥ 0` on nonempty sets, `σ{v} = 0`, `σ(S ∪ T) ≤ σ S + σ T` when `S ∩ T ≠ ∅` | definition |
| `wnorm σ K D c` | `∑_{A ⊆ D} c(A) e^{σ(A ∪ K)}` (anchored weighted norm of a majorant) | definition |
| `wnorm_conv_le` | `b ∈ K ⇒ wnorm_K(conv c₁ c₂) ≤ wnorm_K(c₁) · wnorm_{{b}}(c₂)` (gluing at a point of the anchor) | S (small) |
| `MajBy.tsum` | majorants pass through pointwise series; norm `≤ ∑ tₙ` | S (standard analysis) |
| `gasZ_insert` | `Z(Y ∪ y) = Z(Y) + ∑_{γ ∋ y, γ ⊆ Y ∪ y} ζ(γ) Z((Y ∪ y) \ γ)` for the hard-core family sum | S (combinatorial) |
| `gasZ_congr`, `clusterPot_congr` | `Z(Y)`, `Φ_X` depend only on activities of polymers inside `Y`, `X` | D |
| `log_gasZ_eq_sum` | `log Z(W) = ∑_{X ⊆ W} Φ_X`, `Φ_X := mob(log Z)(X)` (`clusterPot`) | D |
| `inv_of_good`, `log_of_good` | ratio deviation of norm `≤ 1/2` ⇒ inverse ratio norm `≤ 2`, log-ratio norm `≤ log 2` | S (series) |
| `P_bound` | `P_C(Y) = 1[C ⊆ Y] Z(Y \ C)/Z(Y)` has norm `≤ e^{σ K} 2^{|C|}` for every anchor `K ⊇ C` | S |
| `good_of_sub`, `good_all` | the induction: every region is "good" | S |
| **`kotecky_preiss`** | `Weight σ`, `0 ≤ ζ̄`, `|ζ γ ω| ≤ ζ̄ γ`, `KPCrit σ ζ̄` (`∀ y, ∑_{γ ∋ y} ζ̄ γ · 2^{|γ|} · e^{σ γ} ≤ 1`) ⇒ `(∀ ω Y, 0 < Z_ω(Y))` ∧ `(∀ X, sup_ω |Φ_X| < ∞)` ∧ `∀ W, ∀ y ∈ W, ∑_{X ⊆ W, X ∋ y} sup_ω |Φ_X(ω)| · e^{σ X} ≤ log 2` | **S** |

**How the proof avoids the usual machinery.** The standard KP proofs pass through the cluster expansion (Ursell functions,
tree-graph inequality) and then sum over clusters. Here the induction is on the **Moebius coefficients** of the ratio
`u_y(Y) = Z(Y ∪ y)/Z(Y) − 1` in the weighted norm anchored at `y`. The recursion gives `u_y = ∑_{γ ∋ y} ζ(γ) P_{γ \ y}`;
`P_C` factors into an up-set indicator and inverse ratios of strictly smaller regions, each anchored at a point of `γ`,
and `wnorm_conv_le` glues them at those points because `σ` is subadditive on overlapping unions (the diameter is: triangle
inequality through the common point). Locality is never imposed: the Moebius coefficients of a disconnected set vanish by
themselves, and the anchored weight `e^{σ(A ∪ y)}` turns that into the region-independent bound. The weight `|·| − 1`
inside `σ` pays for the pair counting of `EnvelopeW`. Constants: `2^{|γ|}` and `log 2` come from the choice
"ratio deviation `≤ 1/2`"; any `δ < 1` works the same way.

**Group-blind.** Nothing here knows about gauge theory; it applies to the photon, Z₂ and Banks–Zaks alike (§6).

## 3. The bridge (task 3)

`ProofPhase/Seg1/Envelope.lean`.

| Lean | exact statement | mark |
|---|---|---|
| `envWeight rad λ'` | `S ↦ λ'·rad S + (|S| − 1)` | definition |
| `weight_envWeight` | `RadiusFn rad` (`≥ 0`, `0` on singletons, glue) and `λ' ≥ 0` ⇒ `Weight (envWeight rad λ')` | D |
| `pairSum_sets_eq`, `pairSum_le_weighted` | `∑_{i ≠ z} ∑_{x ∋ i, z} f x = ∑_{x ∋ z} (|x| − 1) f x`, and the `EnvelopeW` sum is `≤ ∑_{x ∋ z} h x e^{σ x}` | D |
| `envelopeW_of_kp` | a family of gases with `KPCrit (envWeight rad λ')`, one family-wide statement ⇒ `H1.EnvelopeW (fun _ A => A) rad λ' clusterBar` with constant `log 2` | S (given `kotecky_preiss`) |
| `linkDiam_glue`, `radiusFn_linkDiam` | the `ℓ^∞` link diameter of `H1.Split` is a radius function on every torus | D |
| `PolymerRepW N ν λ' M_E` | **named hypothesis** (§1.2): for all `k`, `j`: measurable local `E`, `ζ` with `|E X| ≤ Ē X`, `Ē ≥ 0`, `Ē ∅ ≤ M_E`, `∑_{X ∋ z} Ē X e^{σ X} ≤ M_E`, `|ζ γ| ≤ ζ̄ γ`, `KPCrit σ ζ̄`, and `ν k j = weightMeasure haar (exp(∑_X E X) · gasZ ζ univ)`; `σ = envWeight linkDiam λ'` | named hypothesis (open; §1) |
| **`envelopeW_of_polymerRep`** | `0 ≤ λ'`, `PolymerRepW N ν λ' M_E` ⇒ `∃ V h`, `∀ k j`: `ν k j = gibbsMeasure haar (V k j)` ∧ `Potential (V k j)` (measurable, bounded by `M_E + log 2`, local) ∧ `|V k j X| ≤ h(k,j) X`, and `H1.EnvelopeW` (family indexed by `(k, j)`, supports `A ↦ A`, radius `linkDiam`) at rate `λ'` with constant `M_E + log 2` | S (given the hypothesis) |
| **`envelopeW_seg1`** | the same for `ν k j = (T.ym k j).map (B₁ k j)`, any blocking maps `B₁` from the fine SU(2) tori to the `L_*` tori | S; YM: the image of the SU(2) Wilson measure along `T` |

So: **`PolymerRepW` ⇒ `EnvelopeW` at `L_*`, uniformly in `k` and `j`, together with the Gibbs representation (R) and
(P) of c3d at `L_*`.** This is the input c3d §3 assigned to segment 1; it feeds segment 2 (c4c), which must carry
`EnvelopeW` (or `LevelDprime`) across the fixed number of steps from `L_*` to `L₁`. It says nothing about convergence in
`k` (not needed, c3d §2) and contains no decay.

**What is Yang–Mills-specific:** `PolymerRepW` is typed on SU(2) link configurations, and `envelopeW_seg1` on the
blocked SU(2) Wilson measure; whether the hypothesis holds depends on the coupling being small at every scale up to
`L_*`, i.e. on asymptotic freedom (§5). The proofs are group-blind.

## 4. Lemma UV (task 3, second half)

Lemma UV(`L₀`) (c3a §2.1) asks, for the composite blocking up to `L₀`: (b) `E[F | Φ₁] ≈ f₁∘Φ₁` in `L¹` and (c)
`|E[Cov(F, G | Φ₁)]| ≤ c e^{−m₀ D}`, uniformly in `k ≥ k₀` and `j`, for bounded fine observables of bounded physical extent.

**What the literature provides and what is missing.**
* `PolymerRepW` and everything in §1 is about the **marginal law of the block field** (the effective action). Lemma UV is
  about the **conditional law of the fine field given the block field**, with two observables inserted.
* In Balaban's scheme the conditional law at each step *is* the object being integrated (fluctuation field around the
  background determined by the block field), so the missing statement is: run the same multiscale expansion with
  `F`, `G` (bounded, local) as insertions and show the truncated expectation decays across scales. For the abelian Higgs
  model this is Balaban–Imbrie–Jaffe (CMP 114, "cluster properties"); for non-abelian gauge fields it is **not
  published**. Size of the step: a full paper extending Balaban's 4D expansion with marked polymers, at every one of the
  `~log₂(L₀/a_k)` scales; the annealed form (c3a's recommendation) helps with large fields (large-field blocks only need
  probability bounds, `(Ce^{−p})^{D/L₀}` per chain), but the small-field part still needs the observable-carrying cluster
  expansion with decay of truncated correlations uniform in the number of scales. This is substantial but in kind the
  same as published work (BIJ), not a new non-perturbative problem.
* With a cluster expansion of the conditional system in hand, the KP theorem here gives the decay mechanism: for a polymer
  system conditioned on the block field, truncated correlations of observables at distance `D` are controlled by the
  Moebius coefficients of `log Z` with sources, which `kotecky_preiss` bounds by `e^{−σ}`. Formalising "sources" is a
  small extension (activities depending on two extra real parameters, mixed second derivative); not done here.

**The Gaussian Lemma UV.** At Gaussian level the conditional fine field given the (soft) block field is Gaussian with
covariance `(A + a QᵀQ)⁻¹`, `A` the fine quadratic form, `Q` the linearised block map; (c) for linear observables is
`⟨f, (A + a QᵀQ)⁻¹ g⟩`. Its exponential decay uniform in the number of scales is **exactly Balaban's published propagator
bound** for his averaging (CMP 95, 96; in a background field CMP 99; recalled, not re-read), and for our good blocking it is
c3a's coercivity on `ker Q` (verified numerically in time, defective in space at `w = 0.5, 1`; c3a §3, §8.2). So the
Gaussian Lemma UV is published for Balaban's blocking and open (a symbol estimate) for ours: one more reason for the
composite bridge of §1.2(3), under which Lemma UV is needed for Balaban's blocking up to `L_*` and the good blocking only
from `L_*` on (where it belongs to segment 2 / Lemma X anyway). Not formalised here: the proof would be a Combes–Thomas
estimate (`m ≤ H ≤ M`, `H` banded ⇒ `|(H⁻¹)_{xy}| ≤ m⁻¹(1 − m/M)^{d(x,y)/R}`) on top of Mathlib's matrix spectral theory;
it would add a lemma, not a published input, so I left it for a later workstream (proposed statement in §8).

## 5. Where `b₀ > 0` enters, and Banks–Zaks (task 4)

* **Depth.** Segment 1 has `n_k − n_* ≈ log₂(L_*/a_k)` steps, growing with `k`. `PolymerRepW` asks for constants
  independent of `k`; Balaban-type bounds are inductive and reproduce themselves at each step **while the running coupling
  at that step is below a threshold `ḡ`**. Along the line of constant physics, `b₀ > 0` makes the coupling increase
  monotonically towards the infrared, so `max_{scales ≤ L_*} g = g(L_*) = ḡ` for **every** `k`: one threshold, all depths.
  Without it there is no depth-uniform statement: for `b₀ < 0` (infrared free, φ⁴₄-like sign) a fixed `g(L_*)` forces the
  bare coupling to blow up as `a_k → 0`; for `b₀ = 0` at one loop the higher loops decide.
* **The constants do not see the gap.** Everything in segment 1 (`EnvelopeW`, R, P) holds whenever the coupling is small
  at all scales up to `L_*`. Asymptotic freedom is used only to make the fine scales weakly coupled uniformly in `k`.
* **Banks–Zaks passes segment 1, as it must.** A Banks–Zaks theory is asymptotically free with a small infrared fixed point
  `g⋆`; along its line of constant physics the coupling stays `≤ g⋆` at **all** scales, so a `PolymerRepW`-type
  representation is expected at every `L_*` (and beyond), and `envelopeW_of_polymerRep` gives `EnvelopeW`. The theory is
  gapless; nothing here contradicts that, because `EnvelopeW` is a locality statement, not decay. (The published
  results are for pure gauge theory; with fermions they are not covered, structurally the same.) Segment 1 is not the gap.

## 6. Unit tests

| test | claim tested | result |
|---|---|---|
| photon (4D U(1), weak) | `kotecky_preiss`, `envelopeW_of_polymerRep` | the abstract theorems apply to any gas; a weak-coupling U(1) theory blocked with a smearing blocking has a vacancy-1 representation with small large-field (monopole) activities (expected, Gaussian plus small corrections), so `EnvelopeW` holds at `L_*` and at every scale. It carries **no gap**: `EnvelopeW` is not decay, and nothing here implies `LevelDprime`. Pass |
| Banks–Zaks | the same | holds at every scale (§5), theory gapless, no decay claimed. Pass |
| Z₂ (weak coupling) | gap-only / confinement-type | Z₂ at large β: excitations cost `e^{−2β}`, KP holds at fixed β, so the envelope holds; Z₂ has a gap and no area law, and the theorems here imply neither a gap nor an area law. Pass (vacuous: no decay statement) |
| mixture | Gibbs representation | the hypothesis fails for a reflection-positive mixture of two phases (its density is a sum of two Gibbs densities, whose log is not a sum of local terms with a volume-uniform envelope); the theorem claims nothing for it and gives no decay anyway. Pass |
| deconfinement (`L < 1/T_c`) | — | no decay or strong-coupling claim at any scale. Pass (vacuous) |
| triviality (φ⁴₄) | existence-type? | no existence claim; for the infrared-free sign a uniform segment 1 does not exist (§5), for the families that exist (`g(L_*) → 0`) the envelope holds with a Gaussian limit. Pass |
| finite subgroups | — | group-blind proofs, hypothesis typed on SU(2). Pass (vacuous) |

A group-blind theorem passes all tests and proves nothing about Yang–Mills by itself: the Yang–Mills content sits entirely
in `PolymerRepW` (and in why it holds uniformly in `k`: asymptotic freedom).

## 7. Blueprint and assembly changes (proposed; not made here)

* **New row P3.6 (segment 1):** "`EnvelopeW` at `L_*` uniformly in `k`, `j`, with the Gibbs representation: Lean
  (`Seg1.envelopeW_seg1`, `envelopeW_of_polymerRep`) from the named hypothesis `PolymerRepW` (vacancy-1 polymer form of
  the `L_*` density with KP-small large-field activities, constants independent of `k`, `j`) via a Kotecky–Preiss theorem
  proved in Lean (`Seg1.kotecky_preiss`, Moebius form, exponential tails in `λ'·diam`). `PolymerRepW` is open as a
  reading: target form of Balaban CMP 109–122 (not verified at text level) and of the OpenAI `Rep.eval`, whose large-field
  gas is exact-cover and needs Balaban's exponentiation or a lower bound on single-block weights."
* **P3.5:** replace "`EnvelopeW` plausible from Balaban/OpenAI upper bounds (paper)" by "`EnvelopeW` at `L_*` ⇐
  `PolymerRepW` (Lean, P3.6); upper bounds suffice for vacancy-1 representations, not for the exact-cover ones of both
  sources (c4b §1.2)".
* **P3.4:** add the OpenAI file:line pins of §1.1 and "exact-cover large-field gas (`Activities.lean:114`)".
* **P1.8 / assembly (for c4a):** the composite blocking `B_good ∘ B_Bal` as the blocking family of the torus route, with
  an `RPBlocking` proof obligation for Balaban's averaging step (reflection plane on block boundaries, symmetric path
  sets). If c4a introduces `CondMass`, its segment-1 part is `PolymerRepW` (marginal) plus the observable-carrying
  expansion (conditional, §4); I would keep them as two named hypotheses, since only the first is a reading of published
  work.
* **c3a §2.1 Lemma UV:** add "missing beyond the literature: the multiscale expansion with two observables inserted
  (BIJ-type, non-abelian, unpublished); Gaussian part = Balaban's propagator bounds for his blocking".

## 8. Next steps

1. **Read Balaban CMP 122 II (and CMP 109 §1) in full text** and either confirm the vacancy-1 ("exponentiated") form of the
   large-field contributions with uniform constants, in which case `PolymerRepW` becomes a citation with a short
   translation lemma (weights, hard core vs touching), or record the exact form and add a Lean lemma for exact-cover gases
   with a lower bound on single-block weights (divide out the vacancy weights; then `kotecky_preiss` applies).
2. **Check that Balaban's averaging step is an `RPBlocking`** (CMP 98's path sets and the reflection plane), so the
   composite bridge keeps `blocked_wilson_rp`.
3. **Lean, small:** sources in the gas (`ζ` depending on two real parameters, mixed derivative of `log Z` = truncated
   correlation) to turn `kotecky_preiss` into a clustering statement; and the Gaussian Lemma UV as a Combes–Thomas lemma:
   `H` symmetric, `R`-banded, `m ≤ H ≤ M` ⇒ `|(H⁻¹)_{xy}| ≤ m⁻¹ (1 − m/M)^{⌈d(x,y)/R⌉}`.

## 9. Clicks

* **Dobrushin and Kotecky–Preiss are one induction.** The KP proof here has the same shape as Theorem A of round 3
  (`R3/TailDecay`): a weighted norm that is submultiplicative because the weight is subadditive along overlaps, a
  Neumann-type series that converges because one local sum is `≤ 1/2`, and region-independence because the weight is
  anchored at the site where the induction removes something. In Dobrushin the object is the influence matrix, here the
  Moebius coefficients of `log Z`. The same skeleton gives the Gaussian Lemma UV (Neumann series of a banded operator).
  So segment 1 (locality of the effective action), Lemma UV (decay of the conditioned system) and segment 2's `LevelDprime`
  (decay of the coarse system) are three uses of one inequality with three different small parameters: activities
  (`e^{−p(ḡ)}`), the constraint gap (`m/M`), and the influence (`γ < 1`). Only the third has no small parameter at `L₁`.
* **"The act conserved through lossy layers" (round 4) again.** `log Z = ∑ Φ_X` is exact at every depth (Moebius
  inversion is definitional); what is lost from layer to layer is only the *size* of the description, and the KP bound is
  depth-uniform because the anchored weight never sees the region. The fourth instance of "uniform finite-depth bound,
  no limit object needed" (c3d §6).
* **The exact-cover finding is the large-field trap of c3d, located precisely.** Where the field is large there is no
  "vacancy" alternative, so the description of the density there needs lower bounds; asymptotic freedom makes such
  configurations rare (probability), but sup-norm locality (what Dobrushin-type conditions consume) does not see
  probabilities. This is the same tension as c3a's quenched vs annealed forms: the annealed form is cheap, the sup form
  needs lower bounds. A Dobrushin route that tolerates rare bad sites (annealed or `W₁` with large-field holes) would move
  the problem from "lower bounds" to "probability bounds", which the literature does supply.

## Files

- `../../../formal/ProofPhase/Seg1/Mobius.lean`: `mob`, `sum_mob`, `mob_eq_of`, `mob_insert`, `mob_mul`, `mob_shift`,
  `mob_upS`, `mob_upS_mul_eq_zero`, `pairs`, `sum_pairs`, `MajBy` (+ `congr`, `mono`, `mul`, `add`, `const_mul`, `neg`,
  `sum`, `pow`, `tsum`), `majBy_shift`, `conv`, `cpow`, `unitM`, `deltaM`, `Weight`, `wnorm` (+ `add`, `const_mul`, `sum`,
  `mono`, `unitM`, `deltaM`, `shift`), `wnorm_conv_le`, `wnorm_cpow_le`, `wnorm_trunc_le`, `abs_le_wnorm`.
- `../../../formal/ProofPhase/Seg1/KP.lean`: `families`, `gasZ`, `gasZ_empty`, `gasZ_congr`, `sum_families_mem`,
  `gasZ_insert`, `Zc`, `clusterPot`, `clusterBar`, `log_gasZ_eq_sum`, `clusterPot_congr`, `KPCrit`, `ratioDev`,
  `invRatio`, `Pc`, `Good`, `inv_of_good`, `log_of_good`, `P_bound`, `ratioDev_eq`, `good_of_sub`, `good_all`,
  `abs_clusterPot_le`, `kotecky_preiss`.
- `../../../formal/ProofPhase/Seg1/Envelope.lean`: `envWeight`, `RadiusFn`, `weight_envWeight`, `pairSum_sets_eq`,
  `pairSum_le_weighted`, `envelopeW_of_kp`, `linkDiam_single`, `linkDiam_glue`, `radiusFn_linkDiam`, `PolymerRepW`,
  `measurable_clusterPot`, `envelopeW_of_polymerRep`, `envelopeW_seg1`.
- Here: `setup.sh`, `build.sh`, `axioms.sh`, `rebuild.sh` (clean rebuild of `Seg1` plus axioms), `axioms.log`. No
  numerics; no commit, push or GPU.

## References (reading status in §1.1)

Balaban CMP 95 (1984) 17; 96 (1984) 223; 98 (1985) 17; 99 (1985) 389; 102 (1985) 255; 109 (1987) 249; 116 (1988) 1;
119 (1988) 243; 122 (1989) 175, 355. Balaban, Imbrie, Jaffe CMP 114 (1988) 257. Kotecky, Preiss CMP 103 (1986) 491.
Fernandez, Procacci, math-ph/0605041 (restatement of KP). Dimock arXiv:1108.1335, 1212.5562, 1304.0705, 2009.01156.
Jaffe, Witten, Clay problem description (recalled). OpenAI construction, `yang-mills-group/YM` commit `b379615`,
files as cited. Project: `../c3d-h1/NOTE.md`, `../c3a-uv/NOTE.md`, `../../H1-OPENAI.md`, `../READING.md`.
