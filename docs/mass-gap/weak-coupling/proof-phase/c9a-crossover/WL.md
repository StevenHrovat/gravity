# (WL): the quenched conditional mass across the crossover, stated scale by scale, and what M1's tools do to it (c9a-crossover, round 2, 2026-11-23)

Inputs read: `NOTE.md` (2.3, 2.4, 3, 5); `W1-CHAIN.md`; `m1-tools/UV-TV.md` sections 3, 16, 21, 24, 28, 29, 31, 32;
`formal/ProofPhase/OneBox/CouplingDS.lean` (header and statements); `formal/ProofPhase/OneBox2/Anchor.lean` (header);
`c8b-decisive/PREREG.md` (the Markov-coupling limit); `formal/ProofPhase/V4/Recursion.lean` (`StageTwoW`).

Claim marks as in `NOTE.md`. Nothing here is Lean except where a Lean file is named.

---

## 0. Result in plain words

1. **(WL) has a precise per-scale form** (section 2). Write the crossover as `N` blocking steps with reverse kernels `K_i`
   (law of the scale-`i` state given the scale-`(i+1)` state). The quenched form `WL-Q_i` is a Dobrushin-Shlosman condition
   for the box specifications of `K_i(x, ·)`, uniformly over **every** coarse state `x` and **every** outside. The supported
   form `WL-S_i` (M1's move) asks it only for good data in the support, treats bad regions as composite boxes, and adds an
   annealed rarity condition for the bad regions.
2. **Where each form is consumed** (section 3, exact). `P4Star` (worst case over all outsides, `W1-CHAIN.md`) needs the
   quenched form: its quantifier sits in the consumer. Stage two (`V4.StageTwoW`) is stated in `L¹` norms and expectations
   under the law, i.e. annealed. **So M1's move is available on the stage-two route only.** There, `WL-S_i` for every
   crossover scale gives stage two at sketch level (M1's argument with the scale index shifted; `StageTwoW` stays a named
   open hypothesis in Lean), and `yang_mills_assembly_stageTwo` (Lean) takes it from there with the landing at `L₁`.
3. **How far the move weakens the requirement** (section 4, table). Removed: the worst case over large-field, twisted and
   adversarial coarse states; the worst case over outsides off the support; any bound inside bad clusters. Kept: the
   worst case over good data on good boxes, pointwise in the coarse state. Added: rarity of bad cells, annealed, at a
   subcritical level. **The quantifier moves from "every coarse state" to "good coarse states, plus bad ones rare enough".**
4. **It matters for truth, not only for proof.** The quenched form is **false at the weak end** for M1's kernels (paper, M1:
   `UV-TV.md` 3): an outside that carries an SO(3) twist or a Z2 flux through a box forces a deep structure inside it whose
   position the coarse data do not fix, so one boundary site moves a positive fraction of the box and `k_J(z) ~ |J|` for
   every box size. `NOTE.md` 2.4 stated (WL) in exactly this quenched form ("uniformly over block fields, including
   large-field and twisted ones, and outsides"), so **(WL) as stated in `NOTE.md` is false at the weak end of the crossover**.
   At order-one coupling the quenched form is unknown; renormalisation-group pathologies (van Enter-Fernandez-Sokal, from
   special coarse states with constrained coexistence) and the SO(3)/mixed-action bulk transition (`NOTE.md` 4) are further
   candidate mechanisms. The supported form survives a rare set of such states. So the move is not an optional weakening:
   it is what turns (WL) from "false as stated" into "possibly true, open". It also means a per-scale quenched route to
   `P4Star` is closed at the weak end; `P4Star` itself (one large box at `L_*`) is not refuted by this example.
5. **It does not supply the missing smallness** (section 5). In M1 the move worked because `p₀(g) → ∞` made bad cells
   rare (`e^{−p₀}`) and good boxes near-Gaussian (Balaban's small field). Across the crossover there is no free parameter:
   the good-box Dobrushin column sum `c_i(t)` and the bad-cell density `η_i(t)` at threshold `t` are order-one numbers. The
   move reduces (WL) at each scale to **two measurable numbers with a trade-off in `t`**: some `t` must give
   `c_i(t) < 1` adversarially within the good class **and** subcritical bad clusters.
6. **The tools, one by one** (section 6). `CouplingDS.lean` applies verbatim (generic, no smallness), given (I) for
   every pair in the support. Lemma C's logical reduction applies (composite-box influence through the mixed variation `M`
   of the collar's log-partition function), and it reduces composite boxes to the good-box condition on the collar; its
   bound via Balaban's cluster expansion does not transfer, and the collar must still force `M ≤ ¼`. Van den Berg-Maes
   applies given rarity and a Markov pattern field with positive weights (itself open at order-one coupling);
   Kotecky-Preiss can then be replaced at sketch level by van den Berg-Maes with the conditioning set as source.
   The Haller-Kennedy / van Enter-Fernandez-Sokal pattern gives quasi-locality of the renormalised law under the quenched
   form; under the supported form only weak (almost-sure) Gibbsianness, which costs the closure link a bad-cell budget per
   step.
7. **(WL) is expected to be gap-free; the gap then sits in closure and landing** (section 7, a refinement of `NOTE.md`).
   The photon is expected to pass `WL-S` with a good blocking (it is a conditional statement at the block scale; by analogy
   with c3a's Gaussian computation, not computed for this blocking; W2's photon gate tests it). With the move, P4 splits into
   `WL-S_i` at every crossover scale (uniform control without a small parameter, open), the **closure** (the transported
   `L₁` law lies in a class the landing covers, open), and the **landing** (that class has the gap; certified windows c3c,
   c4d, open with a tail budget).
8. **Correction to `NOTE.md` 2.4.** "At the strong end (WL) follows from the single-link Dobrushin bound" holds only for
   Wilson-equivalent `β ≲ 0.25` (Markov coupling, c8b) or `β < 2.6 × 10⁻⁴` (Lean anchor, `OneBox2/Anchor.lean`). The `L₁` end
   of the crossover is at `β ≈ 2.3`. **No known estimate covers `WL` at the crossover scales beyond M1's reach**: M1's
   machinery covers scales with `g ≤ γ₀`, i.e. at most the strip from `γ` to `γ₀` beyond `L_*` (none if `γ = γ₀`, section 6.5),
   and the strong-coupling estimates end about one order of magnitude in `β` below `L₁` (four orders for the Lean anchor).
9. **Containment without rarity** (section 10, the owner's question). Contained regions pass on only what crosses their
   boundary, always (exact). That is not enough for a contraction: each contained region needs good room around it of width
   `~ log|W|/m` to wear down what crosses, so the regions needing containment must be sparse **relative to the collar
   volume**. Absolute rarity (`e^{−p₀}`) can go; relative sparseness cannot, and the middle does not supply it. The lever
   left: contain only regions that fail to contract, not regions with large fields.

---

## 1. Setting

* Scales `i = 0, ..., N`, `N = log_L(L₁/L_*)`: `i = 0` is M1's hand-over scale `L_*`, `i = N` the landing scale `L₁`. The
  state at scale `i` is `X_i` (block state on the scale-`i` torus: for M1's line, the SO(3) field and the closed Z2 layer,
  plus noise variables if the blocking is randomized).
* Blocking steps `X_{i+1} = R_i(X_i, ω_i)`, measurable, with independent noise `ω_i` (soft constraint; needed against the
  Rebeschini-van Handel instability, `NOTE.md` 2.4, and for law preservation, M1 round 23).
* Laws `ρ_0` (the hand-over law) and `ρ_{i+1} = (R_i)_#(ρ_i ⊗ P_i)`. Reverse kernels
  `K_i(x, dy) = ρ_i(X_i ∈ dy | X_{i+1} = x)`. `K_i(x, ·)` is a law on scale-`i` states; for a positive soft constraint
  it has a positive density with respect to `ρ_i` on the fibre, so it is a Gibbs-type measure with the scale-`i` effective
  interaction plus a block-constraint term.
* Box specifications of `K_i(x, ·)`: for a box `b` of scale-`i` sites (a few blocks), `q^{x}_{i,b}(σ, ·)` = conditional law
  of `X_i` on `b` given `X_i = σ` off `b` and `X_{i+1} = x`. These exist by DLR for the joint law; they depend on `x` only
  through the blocks meeting `b` (locality of the constraint).
* Good and bad. A threshold `t > 0` and a local rule decide which scale-`i` cells are **good** (the coarse state and the
  fine state near the cell are within `t` of regular, in the gauge-invariant sense M1 uses: plaquette-angle bounds); the rest
  are **bad**. The pattern `ω^t_i` is the set of bad cells. M1 used Balaban's small-field thresholds `p(g_j)`; here `t` is a
  free parameter.

## 2. The two forms of (WL), scale by scale

### 2.1 Quenched: `WL-Q_i(γ_DS, b)`

> For every coarse state `x` of scale `i + 1` (all of the state space), the box specifications `q^{x}_{i,b}` satisfy the
> Dobrushin-Shlosman condition: with `k^{x}_b(z)` the influence of the outside site `z` on the box law (worst case over all
> outside configurations, tested on gauge-invariant functions of the box with frozen boundary), the column sums
> `Σ_{b ∌ z} k^{x}_b(z) ≤ γ_DS · c(z)` with `γ_DS < 1`, uniformly in `x`, the volume and the lattice spacing.

What it gives (paper, standard pattern):
* decay of `K_i(x, ·)` at the block scale, uniformly in `x` (Dobrushin-Shlosman; Lean `theoremA_on`);
* quasi-locality of the projection `f ↦ E[f | X_{i+1}]` with a tail `e^{−m d}` (the coarse variables act on the fine law
  through local constraint terms, each with influence `≤ k`);
* the renormalised law `ρ_{i+1}` is Gibbsian with a quasi-local potential (van Enter-Fernandez-Sokal 1993; recalled);
* through `p4StarInv_of_net`'s tail clause, a route to `P4Star` at `L₁` resolution, uniformly over the input class.

Status: **false at the weak end** for M1's kernels (paper, `UV-TV.md` 3, the sub-block vortex outside: `k_J(z) ~ |J|` for
every box size). Unknown at order-one coupling.

### 2.2 Supported: `WL-S_i(t, γ_DS, w, η_c)`

> **(G) Good boxes.** For every coarse state `x`, every good box `b` (all cells within distance `r_int` good, in both the
> coarse and the fine state), and **every pair** `(σ, σ')` of outside configurations in the support of the
> pattern-conditioned law, the box laws admit a coupling with
> `Σ_{y ∈ b} v(y) P(ξ_y ≠ ξ'_y) ≤ Σ_{z ∉ b} 1{σ_z ≠ σ'_z} K^{x}_b(z) v(z)` (CouplingDS's (I), for all in-support pairs, not
> only pairs differing at one site: one-site bounds do not chain without off-support hybrids, `UV-TV.md` 33.4), and the
> column condition (K) holds with `γ_DS < 1` for the good boxes.
>
> **(C) Composite boxes.** For every connected cluster `𝒦` of bad cells, the composite box `W(𝒦) = 𝒦 ∪ collar_w(𝒦)` (collar
> of good cells, width `w`) has influence `k_W(z) ≤ k_collar(z) + (|𝒦| + |I|) · 4 M_W(z)`, where `M_W(z)` is the supremum of the
> mixed variation of `log Z(c, σ)` (inner data `c`, outside data `σ`, differing at `z`) over data in the support. With
> multiplicities as in `UV-TV.md` 22.3, the column condition holds for composite boxes too.
>
> **(R) Rarity.** Under `ρ_{i+1}` and the pattern law, bad clusters are subcritical after merging at range `2w + l_B`:
> `P(a merged bad cluster joins two sets at distance r) ≤ C e^{−r/ξ_bad}`, uniformly in the volume. A sufficient Peierls
> form is `P(all cells of A bad | anything outside the merge range of A) ≤ η^{|A|}` with `η < η_c(w)` (section 5).
>
> **(P) Pattern coupling.** The pattern field is Markov at the merge range (extended along occupied links), and "good in
> both copies with agreeing surroundings" implies "identically coupled" (this is (G) at zero input).

What it gives (paper sketch, M1's argument with the scale index shifted):
* per pattern pair, a coupling of `K_i(x, ·)` and `K_i(x', ·)` with expected disagreement on a set `B` bounded by the sum
  over sources (CouplingDS, Lean, generic);
* averaged over patterns with (R) and the min-trick, the probability that the fine states differ on `B` decays in
  `dist(B, sources)/ξ` (M1 section 30's front advance, one scale instead of a tower);
* the covariance form by conditioning on the content near `A` (M1 33.3), hence `E[Cov_{K_i}(f, g)]` decays and the
  projection `E[f | X_{i+1}]` is quasi-local **in `L¹(ρ_{i+1})`**, not uniformly in `x`;
* summed over `i` by the law of total covariance: stage two (a), (b), (c) (`W1-CHAIN.md` 3).

## 3. Which route consumes which form (exact)

| route (W1, Lean) | quantifier in the consumer | form of (WL) it needs |
|---|---|---|
| `yang_mills_assembly_p4Star(Inv)` | `IsInfluenceBound(On)`: for **every** boundary condition `σ` of the `L_*` law's box | a worst-case statement over `L_*` outsides; reached through the scales only via `WL-Q` (where the coarse-state quantifier enters by composition) plus the tail clause, uniformly over the class `C` |
| `yang_mills_assembly_stageTwo` | `StageTwoW`: `L¹(ν)` errors and expectations under `ν` | `WL-S` suffices |

This is exact at the level of the statements: `P4Star`'s worst case is a property of the hypothesis consumed by
`lawGapBddW_of_oneBoxLaw`; `StageTwoW`'s clauses (a), (b), (c) are integrals against the law (`V4/Recursion.lean`). M1 faced
the same choice for its ultraviolet transfer and resolved it the same way: the worst-case one-box theorem failed (influence
`~ |J|` from sub-block vortex boundaries, `UV-TV.md` 3), and the averaged coupling statement replaced it (`UV-TV.md` 8, 16).

**Consequence for the plan.** The stage-two route is the one on which M1's tools can be pointed. `P4Star` stays the clean
statement of what P4 means, but a proof would go through stage two plus the landing.

## 4. How far the move weakens the requirement

| quantifier or ingredient | `WL-Q_i` | `WL-S_i` | what is left |
|---|---|---|---|
| coarse state `x` | every `x` | every `x`, but the condition is asked only on good boxes | good-box condition pointwise in `x` |
| outside configuration | every configuration | pairs in the support of the pattern-conditioned law, agreeing off one site | for continuous groups with positive densities the support is everything; the gain comes only from **conditioning on the pattern**, which makes the good region's support explicit (`t`-bounded fields) |
| inside a bad cluster | Dobrushin condition required | never bounded; only its boundary acts (Lemma C) | none |
| large-field, twisted, adversarial coarse states | must satisfy the condition | cost only their probability | rarity (R) |
| smallness | none required beyond `γ_DS < 1` | (R) needs `η` below a threshold; (C) needs collars of width `w ~ (1/m) log(C |𝒦| p²/ε)` | two numbers per scale, section 5 |
| output | uniform quasi-locality, Gibbsian `ρ_{i+1}` | quasi-locality in `L¹`, weakly Gibbsian `ρ_{i+1}` | closure must carry a bad-cell budget (section 6.4) |

**Answer to "exactly how far".** The move removes every requirement on bad data and on configurations outside the
pattern-conditioned support, and replaces them by one annealed rarity condition. It keeps a worst-case requirement on good
data, pointwise in the coarse state. It does not weaken the good-box requirement itself. Since the quenched form already
fails at the weak end (2.1), the supported form is the weakest form of (WL) that can be true there, and the strongest one
any argument can hope to use.

## 5. The missing smallness, quantified

In M1 the move had a free parameter: `p₀(g) → ∞` as `g → 0`, so `η ~ e^{−p₀}` (or `e^{−c p₀²}` with the slack of re-proof
(c)) and good boxes were Gaussian up to `O(e^{−κ d})` terms. Across the crossover:

* **Good-box condition.** At threshold `t`, `c_i(t) :=` worst column sum over good boxes and good boundary pairs. It
  increases with `t` (rougher fields allowed). Unmeasured. What is known: the **unconditioned** coupled single-link estimate
  of SU(2) at `β = 2.3` grows with the box (`k̂ = 3.4, 8.9, 21` at `ℓ = 4, 6, 8`, Leg B, quoted in `c7b-onebox-num/PREREG.md`
  1; an upper estimate from a Markov coupling, so its growth may be the coupling's saturation rather than the true
  influence), and the single-link coupling contraction fails above `β ≈ 0.25` (c8b). The constraint (conditioning on the block field) is what
  must bring the conditional column sum below 1; how much it helps at `β = 2.3` to 3.5 is the first number W2 measures.
* **Rarity.** `η_i(t) :=` probability that a cell is bad, given good surroundings beyond the merge range. Decreases with `t`.
  The crude Peierls threshold with the min-trick (two copies, `UV-TV.md` 21.3, 31.5): chains of cells occupied in either
  copy have probability `≤ 2^n η^{n/2}`, so subcriticality needs `2 μ η^{1/2} < 1` with `μ` the number of cells within the
  merge range: `μ = (2(2w + l_B) + 1)^4 − 1`. For the smallest sensible range (`2w + l_B = 1` cell): `μ = 80`,
  `η < 4 × 10⁻⁵`; for range 3 cells: `μ = 2400`, `η < 4 × 10⁻⁸` (numerical, crude; sharper percolation-type thresholds are
  larger, of order `1/μ` for the union of the two copies' bad sets, if the bad-cell field has weak enough correlations).
  The honest observable is therefore **the connectivity function of merged bad clusters**, not `η` alone.
* **The trade-off.** (G) wants small `t`; (R) wants large `t`. `WL-S_i` holds for some `t` iff the window
  `{t : c_i(t) < 1} ∩ {t : bad clusters subcritical at t}` is non-empty. At weak coupling the window is wide (M1). At
  `β ≈ 2.3` it is unknown in both directions; nothing excludes an empty window.

## 6. The tools, one by one

### 6.1 Coupling-form Dobrushin-Shlosman (`OneBox/CouplingDS.lean`, Lean, 37 theorems)

Applies verbatim. It is generic: finite site set, one single-site space, two measures with supports, blocks with
specifications and couplings, (I) on good blocks, (K) column condition, source blocks. Nothing in it uses small coupling.
For a crossover scale: sites = scale-`i` sites with per-site space `S` (bonds, plaquette labels, noise), measures =
`K_i(x, ·)` and `K_i(x', ·)` conditioned on patterns, good blocks = good boxes and composite boxes, sources = where the
coarse data or the patterns differ. **Pointable now** (Lean, generic).

### 6.2 Lemma C with composite boxes (`UV-TV.md` 16, 22.2, 29)

Two parts.
* **The logical reduction (applies, paper, generic).** For a composite box with inner data `c` (cluster plus inner collar
  layer) and outside data `σ`, the law of `c` given `σ` is `w(c) Z(c, σ)/norm`. The inner weight `w(c)` is never bounded
  (multimodal clusters allowed). `TV(law(c | σ), law(c | σ')) ≤ e^{2M} − 1`, `M = sup_{c, c₀} |Mix(c, c₀; σ, σ')|`, the mixed
  variation of `log Z`. Given equal `c`, the collar is coupled by its own good-box condition. The inequality uses only the
  product structure of the weights and finite range. Using it needs `M` small: the linear form `≤ 4M` needs `M ≤ ¼`
  (`UV-TV.md` 29.4), and the column condition needs `|W| · 4M` below the coverage. The collar must force this; that is
  the open item.
* **The bound on `M` (does not transfer).** M1 bounds `M ≤ C (p² + C₀) Σ_z e^{−m' d(z, I)}` by Balaban's constrained
  background, his random-walk expansion and a cluster expansion with constant-size terms `C₀` (29.2). At order-one coupling
  there is no convergent cluster expansion in the collar. What replaces it: `Mix = ∫∫ ∂_c ∂_σ log Z = ∫∫ Cov_{collar}(∂_c H,
  ∂_σ H)` along interpolations, a covariance under the collar's conditional law between terms near `I` and terms near the
  outer boundary. So `M` is small if the collar decorrelates across its width: **that is (G) applied to the collar**.
  Composite boxes therefore add no new kind of hypothesis, only that collars are good and of width
  `w ≳ (1/m_i) log(C |𝒦| p_i² / ε)`, with `p_i` the size of the data's coupling into the collar weights (order one here,
  where M1 had a polylog).

### 6.3 Polymer gas, Kotecky-Preiss, van den Berg-Maes (`UV-TV.md` 31)

* **Kotecky-Preiss** needs small activities (`e^{−p₀} (C e^{−cκ})^{#cubes}`, `κ` large by Balaban's [I] Theorem 3). No
  analogue at order-one coupling. **Not pointable.** It served the pattern-index covariance term (`UV-TV.md` 31.4). Van
  den Berg-Maes bounds disagreement probabilities, not covariances directly; the covariance follows by conditioning on the
  pattern content near `A` and treating it as a source (the device of `UV-TV.md` 33.3), at sketch level.
* **Van den Berg-Maes** applies given (R) as a per-copy Peierls bound **and** a Markov pattern field with positive weights:
  disagreement needs a chain of cells occupied (bad) in one of the two copies, and the min-trick prices the chain. The
  Markov input came from the positive split (next item), which is open at order-one coupling. **Pointable, conditional on
  (R) and the positive split.**
* **The positive split** (`e^{I_X} = e^{−M_X}(1 + h_X)`, 31.2) is what made the pattern field Markov with positive weights.
  It needs only a bound `|I_X| ≤ M_X` on the multi-body interactions between bad regions; at order-one coupling the bound
  exists if the good region decorrelates (again (G)), but the `M_X` are order one, so link objects are not dilute; their
  density enters (R).

### 6.4 Haller-Kennedy / van Enter-Fernandez-Sokal

* Pattern (recalled; Haller-Kennedy existence and topic confirmed in `NOTE.md`, method not confirmed): a renormalisation
  step is well defined and the renormalised measure Gibbsian with a quasi-local potential if the constrained system (fine
  given coarse) is in a uniqueness regime **for every coarse configuration**; a finite-volume condition can certify that.
  This is `WL-Q_i`.
* Under `WL-S_i` the renormalised law is only weakly Gibbsian: a potential that is summable on a set of coarse
  configurations of full measure, with bad configurations allowed (Bricmont-Kupiainen-Lefevere 1998; Maes-Redig-Van
  Moffaert 1999; recalled). This is the right notion for M1's move, and (sketch) it is the notion Balaban's own inductive form
  realises at weak coupling (small-field effective action plus large-field regions).
* **Cost.** The closure link (tracking the flow in a finite-dimensional family plus a tail norm, `NOTE.md` 3.2) needs an
  effective action at every scale. Under the supported form it exists only on good configurations, so each certified step
  must carry a bad-cell budget, exactly as Balaban's induction carries large-field regions. This is `NOTE.md` 2.3's
  conclusion again ("whatever carries the crossover must carry Balaban's large-field machinery"), now per scale: the
  per-scale density `η_i` replaces the `L₁`-resolution density `N_*⁴ e^{−p₀}` of `NOTE.md` 2.3, provided bad regions of
  scale `i` are released (renormalised away) at scale `i + 1`. The scale-by-scale form therefore removes the accumulation
  that made the input class non-compact at `L₁` resolution, but it needs a release mechanism at order-one coupling, which
  is open.

### 6.5 M1's own Lemma UV-TV as the weak end of `WL-S`

Lemma UV-TV (i) (`UV-TV.md` 8, 16, 21-31) is `WL-S_j` for M1's scales: TV locality of the reverse kernels below `ℓ`, with
good boxes (H3), composite boxes (Lemma C), rarity (H2 with the slack of (c)) and pattern coupling (H1). So `WL-S` holds at
paper level (with M1's readings and adaptations) at every scale with `g_j ≤ γ₀(L)`. M1 stops at `g = γ ≤ γ₀`, so this covers
the crossover only between `γ` and `γ₀`, if `γ < γ₀` is chosen; with `γ = γ₀` it covers nothing beyond `L_*`.

## 7. Where the gap sits once the move is made (refinement of `NOTE.md` 2.4)

* `WL-S_i` is a conditional statement at the block scale. For the photon (compact U(1) at `β = 1.1`) with a good soft
  blocking it is expected to **hold**: the fine field given the block field is massive (the constrained Gaussian
  computation of c3a predicts a conditional rate of about `4.5/L₁`, `c4c-seg2/PREREG.md`). It fails for the photon only if
  the blocking loses long-wavelength content (noise-limit trap), and then it fails by being satisfied for the wrong reason
  (the block variable carries no signal), which a content check detects.
* So `WL-S` carries no gap. With it, stage two holds, and `yang_mills_assembly_stageTwo` leaves:
  * the **closure**: the transported law `ρ_N` at `L₁` lies in a class `𝒞_land` (truncated effective actions plus a tail and
    a bad-cell budget) that the landing covers;
  * the **landing**: every law of `𝒞_land` has the `L₁` law gap (strong-coupling side; certified windows c3c, c4d, to be widened
    with a tail budget sized by `near_budget_lt_one`, `NOTE.md` 3.2).
* The photon fails at the landing (U(1) at `L₁` is massless), as it must. 2I fails at the landing (ties). SU(2)×U(1) fails
  at the landing (`γ_A ≥ 1`). None of the unit tests is decided by `WL-S`; they are decided by closure and landing.
* `NOTE.md` 2.4 called (WL) "gap-like but weaker than the gap", and `NOTE.md` 5 "the core of P4". The refined statement:
  (WL) is **expected to be gap-free in content** (the photon is expected to pass it; to be confirmed by W2's photon gate)
  and **hard in uniformity** (no small parameter across the crossover). It stays the core of the crossover's uniformity
  problem; the gap content is in closure plus landing.

## 8. Precise per-scale statement, collected

For each crossover scale `i = 0, ..., N − 1` (Wilson-equivalent `β_i` from `β_* = 4/γ²` down to about 2.3; one loop:
`Δβ ≈ 0.26` per doubling):

> **`WL-S_i`**: there are a threshold `t_i`, a box side `l_B`, a collar width `w_i`, and constants `γ_DS < 1`, `ξ_bad < ∞`,
> `m_i ≥ m_* > 0` (block units), independent of the volume and the lattice spacing, such that (G), (C), (R), (P) of 2.2 hold
> for the reverse kernel `K_i`.

Status per scale band:

| band | `β_i` (Wilson-equivalent) | status |
|---|---|---|
| `g_i ≤ γ₀(L)` | `≥ 4/γ₀²` (unknown, likely `≫ 4`) | paper (M1's Lemma UV-TV, its readings and adaptations); covers the crossover only between `γ` and `γ₀` (nothing beyond `L_*` if `γ = γ₀`, 6.5) |
| perturbative middle | from `4/γ₀²` down to about 3.5 | **open**; physically expected (fluctuations near Gaussian, bad cells rare at a fixed `t`); no explicit-constant estimate exists (the `γ₀` desk study would size it; not started, owner's decision) |
| non-perturbative end | about 3.5 down to 2.3 (4 to 6 doublings) | **open**; measurable (W2: `c_i(t)` and the bad-cluster connectivity) |
| strong coupling | `≲ 0.25` | Dobrushin regime (c8b); **not part of the crossover** (about one order of magnitude below `L₁`'s `β ≈ 2.3`) |

## 9. Not checked

* Bricmont-Kupiainen-Lefevere and Maes-Redig-Van Moffaert (weak Gibbsianness): recalled, not re-read.
* Whether the multiplicity device of `UV-TV.md` 22.3 (repeating composite boxes) keeps the column condition when composite
  boxes are order-one fractions of the volume (at order-one `η` they are not small): not checked, and it matters only if
  (R) holds marginally.
* The claim that the photon passes `WL-S` with M1's soft blocking: by analogy with c3a's Gaussian computation for the c3b good
  blocking (`c4c-seg2/PREREG.md`), not computed for M1's `(SO(3), Z2)` blocking (for U(1) there is no Z2 layer; the control
  is run with the plain good blocking).

## 10. Containment without rarity (the owner's question, `PREP.md`, "Certification and the open middle")

**The question.** M1 contains what is neither cleanly existence nor non-existence: bad regions become composite boxes whose
influence passes only through their collars (Lemma C). M1's containment also used rarity (bad regions sparse relative to
their collars), which the scale separation near G0 supplied and which ends where the coupling reaches order one. Can
containment work **without** rarity in the crossover's middle: do contained regions, dense or not, still pass on only what
crosses their boundary, and is that enough for a contraction at the block scale?

**Answer in one line.** The first half holds always, exactly; it is not enough. Contraction needs every contained region to
have an uncontained neighbourhood of width `w ~ log|W|/m` that wears down what crosses it, and that is **sparseness relative
to the collar volume**. Rarity in M1's absolute sense (`e^{−p₀}`) can be dropped; relative sparseness cannot. The one lever
left is to call "bad" only what fails to contract, not what has large fields (10.4).

### 10.1 What holds without rarity

1. **Boundary transmission (paper, exact).** For a region `W` of a finite-range specification, the law of `W` given the
   outside depends on the outside only through the configuration on its outer boundary layer (the Markov property, H0 of
   `UV-TV.md` 10.1). No rarity, no density condition, no smallness: contained regions, dense or not, pass on only what
   crosses their boundary.
2. **Lemma C's inequality (paper, generic).** With inner data `c` and outside `σ`, `TV(law(c | σ), law(c | σ')) ≤ e^{2M} − 1`,
   `M` the mixed variation of `log Z(c, σ)` through the collar; the inside of the region is integrated against its own weight
   and never bounded. No rarity used.
3. **Static Dobrushin-Shlosman with composite boxes (Lean, `CouplingDS.lean`).** Any finite family of blocks, dense composite
   boxes included; the only conditions are (I) and the column condition (K). No rarity used.
4. **Decay in the contracted metric (paper, `UV-TV.md` 16).** A composite box counts as one step of `dist_ω`. If clusters are
   finite with an exponential size tail, `dist_ω(B, D) ≥ c · dist(B, D)/ξ_W` (`ξ_W` the typical composite-box diameter), so
   decay survives density with a reduced rate. Only finiteness is used.

### 10.2 What contraction needs

Three conditions; none is "rare" in the absolute sense:
* **(A) Attenuation.** A composite box can multiply an incoming disagreement by up to `|W|` (once the inner marginal
  differs, all of `W` counts as disagreeing). The column condition at the collar's outer edge needs
  `|W| · 4 M(z) ≲ γ_DS · coverage`, so the collar must wear down by more than a factor `|W|`:
  `w ≥ (1/m) log(C |W| p² / γ_DS)`, with `m` the conditional mass of the **good** collar (clause (G) on the collar) and `p`
  the data's coupling into the collar weights. Needs `m > 0` on good regions; does not need rarity.
* **(B) Room for collars.** Every cluster needs a good annulus of width `w` that meets no other cluster, plus room for good
  boxes of side `l_B` (`UV-TV.md` 21.1, 22.3). Equivalently: bad clusters merged at range `R = 2w + l_B` are finite, with an
  exponential size tail, uniformly in the volume.
* **(C) Coupled patterns.** The union of the two copies' bad sets, merged at range `R`, does not percolate (van den Berg-Maes,
  min-trick).

### 10.3 Where it breaks

* **(B1) Percolation: containment true but vacuous.** If merged bad clusters percolate, there is a composite box with no
  outside. Boundary transmission still holds, but everything is inside: no collar, no outer layer for Lemma C, and the block
  family degenerates to one block. No contraction.
* **(B2) Collars without mass.** If good regions do not decorrelate across width `w` (`c(t) ≥ 1` on the collar class), the
  collar passes on what enters, `k_W(z) ~ |W|` at its outer edge, and the column condition fails however sparse the clusters
  are.
* **(B3) Self-consistency: rarity returns, relative to the collar volume.** (A) makes `w` grow like `log|W|/m`; (B) asks
  clusters merged at `R = 2w + l_B` to be subcritical; bigger clusters need wider collars and so a longer merge range. M1
  broke this cascade by fixing `R` per scale and truncating cluster sizes at `n ~ log|Λ''|/log(1/η)` (`UV-TV.md` 21.2, 21.3);
  the truncation needs `C R^d η^{1/2} < ½`, i.e. rarity relative to `R^d`, the collar volume.
  Crude numbers (numerical, order of magnitude; `|W| ~ 10³` cells, `p ~ 1`, `γ_DS ~ ½`, `l_B ~ 2` cells):
  * `m = 1` per cell: `w ≈ log(2 × 10³) ≈ 7.6` cells, `R ≈ 17`, `μ = (2R + 1)⁴ − 1 ≈ 1.5 × 10⁶`; the min-trick Peierls form
    `2 μ η^{1/2} < 1` gives `η < 1 × 10⁻¹³`, a percolation-type estimate (order `1/μ`) `η ≲ 7 × 10⁻⁷`;
  * `m = 3` per cell: `w ≈ 2.5`, `R ≈ 7`, `μ ≈ 5 × 10⁴`; `η < 1 × 10⁻¹⁰` (Peierls), `η ≲ 2 × 10⁻⁵` (percolation-type).

  In every count the allowed density is set by the collar volume `(log|W|/m)^d`. **In the middle of the crossover nothing
  supplies this**: there is no `p₀ → ∞`, and the collar width is set by the conditional mass of the good region, not by the
  coupling.
* **Summary.** Containment without rarity holds exactly as a transmission statement (10.1). It gives a contraction exactly
  when the regions that fail to contract are sparse relative to the attenuation volume `(log|W|/m)^d` of the regions that do
  (10.2). It breaks by percolation (B1), by collars without mass (B2), and quantitatively by the relative-sparseness bar of
  (B3), which is severe unless `m` is large in cell units.

### 10.4 The one lever left: classify by contraction, not by field size

* In M1, "bad" meant "not small field", because Balaban's analytic control needs small fields; at weak coupling every large
  field is also non-Gaussian, so the two notions coincided.
* In the middle they need not coincide. A region with large but disordered fields can be a good box in the contraction sense:
  its conditional law may forget its boundary quickly. Containment is needed only for regions whose local conditional system
  **fails** to contract: the genuinely multimodal ones, where the configuration inside is undecided between distinct
  arrangements. These are "neither existence nor non-existence" proper; large fields as such are not.
* With that classification the bar of (B3) applies only to non-contracting regions. Whether those are sparse relative to
  `(log|W|/m)^d` is a single-phase question: plausible on the Wilson axis, which crosses no bulk transition; hazardous near
  the SO(3)/mixed-action bulk transition (`NOTE.md` 4) and for twisted outsides (2.1).
* **Costs of the lever (sketch).** (i) Badness is no longer a local function of the field but a property of the local
  conditional system, so the pattern field's Markov structure and positive split (6.3) must be re-derived for an
  influence-defined pattern. (ii) A rigorous classifier needs a certified local contraction test per region (a finite-volume
  Dobrushin-Shlosman check with interval arithmetic): the stepwise certification of `NOTE.md` 3.2 in local form. (iii) It
  gives nothing if the middle has a positive density of genuinely undecided regions; W2 would see that as percolating
  influence-bad clusters.
* **Added to `W2-PREREG.md`:** the conditional mass `m` of good regions (it sets `w`), and the density and merged-cluster
  connectivity of **influence-bad** blocks (local constrained column sum above a cut), next to the field-size classification.

### 10.5 In the owner's terms

Contained regions pass on only what crosses their boundary: always. That is enough for balance (a contraction) only if what
crosses is worn down before it reaches the next contained region, so every contained region needs uncontained room around
it, of width growing with the logarithm of its size. Near G0 the scale separation made that room free. In the middle it has
to come from the system itself: the undecided regions must be sparse compared with the room the decided ones need to wear
down what crosses them. Large fields need no containment if they decide quickly; only undecided ones do.
