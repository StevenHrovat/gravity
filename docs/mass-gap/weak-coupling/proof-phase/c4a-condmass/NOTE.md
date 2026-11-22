# Cycle 4, workstream 1 (c4a-condmass): `CondMass` and assembly v3 (2026-11-22)

Brief: define the single hypothesis `CondMass` (the fine field conditioned on the block field satisfies a Dobrushin-type
condition at the block scale, uniformly in level and volume), prove what it implies (`ObsTransferPhys`(c), `EnvelopeW`), decide
whether the time-separated transfer `ObsTransferPhysT` suffices, and produce assembly v3 with everything cycle 3 built wired in
(W₁ route, `LevelTorusRoute`, `CondMass`, `ObsTransferPhysT`, both orders of limits). Mid-way input from c4c-seg2 (filter form of
segment 2, annealed and local `CondMass`) is folded in (§1.4, §2.4).

Claim levels as in `../../attempts/RULES.md`. Marks: **S** substantive (reduction with real content), **D** definitional or
elementary, **named** (an open hypothesis). Lean: five new files under `../../../formal/ProofPhase/V3/` (`TimeSep`, `CondMass`,
`W1Route`, `CondInputs`, `Top`), built in `~/formal-c4a` (Lean 4.34.0, Mathlib v4.34.0); `axioms.sh` prints 35 headline theorems,
all `propext, Classical.choice, Quot.sound`; no `sorry`, no `native_decide`, no new axioms (`axioms.log`). `Objects.lean` and
`Assembly.lean` were **not edited** (nothing needed changing), so every existing theorem is untouched; no renames. No build-list
change (the `ProofPhase` library picks up `V3/` by import). `V3/CondInputs.lean` imports c4c's `ProofPhase.Seg2.Filter`
(unchanged).

```
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c4a-condmass/setup.sh
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c4a-condmass/build.sh ProofPhase.V3.Top
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c4a-condmass/axioms.sh
```

## 0. Result in one paragraph

`CondMass` is defined in Lean in two forms. The **Dobrushin form** `CondMass T B` (super-sites = cells of physical size L₁,
blocks of cells, oscillation (sup/TV) influences with exponential weights, the weighted Dobrushin–Shlosman condition `GDSw`,
γ < 1, all constants uniform in level, volume and almost every block configuration) implies, in Lean, almost-sure exponential
decay of the conditional covariance (`condMassDecay_of_condMass`, Theorem A with weights on the super-sites), hence the
**annealed form** `CondMassAnn` (mean absolute conditional covariance, time-separated gauge-invariant pairs), hence **part (c)**
of the transfer for time-separated pairs (`condDecouple_of_condMass`). The annealed form is the one recommended for proof (a
quenched bound can fail by the Rebeschini–van Handel mechanism, c4c). `CondMass ⇒ EnvelopeW` is **not** a Lean theorem and does
not hold as stated: it needs a **noisy, local** blocking and the quenched form (so that the sup-norm envelope of the effective
action is controlled for every block configuration); with those, it holds on paper (§2.3). Parts (a), (b) of the transfer
(quasi-locality of `E[F|Φ]`) do not follow from `CondMass` for a deterministic blocking (a counterexample is a non-local injective
blocking, §2.2); with a noisy local blocking they follow on paper by interpolation. **`ObsTransferPhysT` is enough** (Lean,
`torusDecayLoc_of_blockGapUnifT`: the route only pairs a slab observable with its time-translated reflection). The **W₁ route is
now in Lean**: `LevelDprimeW` (D′ in W₁ form along the levels) gives the W₁ block gap (c3c's `decay_of_siteW`), the W₁ openness
lemma `H1LocalLipW ∧ LimitDprimeW ⇒ LevelDprimeW` is proved, and the certified window enters through `CertifiedAdjointW`. **Assembly
v3** (`yang_mills_assembly_v3`, both orders of limits) takes `OnLCP`, `NonTrivial` and the torus route in W₁ form
(`LevelDprimeW ∧ ObsTransferPhysTW`) or sup form (`LevelDprime ∧ ObsTransferPhysT`); its named form takes `OnLCP`, `NonTrivial`,
`H1LocalLipW`, `LimitDprimeW` (or `CertifiedAdjointW` with a limit in the window), `CondMassAnn`, `ObsQuasiLocTW`. **Gap content:**
`CondMass` is gap-free (the photon satisfies it, at Gaussian level in time); the infrared content stays in
`LevelDprimeW`/`LimitDprimeW` (the coarse effective theory at L₁ is in a uniqueness regime). Caveat (difficulty conservation):
for a blocking that loses content (decimation, the noise-limit trap), `CondMass` becomes the gap itself.

## 1. `CondMass`: the statement and the form chosen

### 1.1 Lean statement (`V3/CondMass.lean`)

```
def CondMass (T : Tuning) (B : BlockingFamily T) : Prop :=
  ∃ (cell : ∀ k j, LatticeLink 4 (T.side k j) → LatticeLink 4 (coarseSide j)) (c₀ c₁ : ℝ),
    CellGeometry T cell c₀ c₁ ∧
    ∃ (lam γ D₀ : ℝ) (b cmin cmax : ℕ), 0 < lam ∧ 0 ≤ γ ∧ γ < 1 ∧ 1 ≤ cmin ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j,
      ∃ κ : GaugeConnection SU2 4 (coarseSide j) → Measure (GaugeConnection SU2 4 (T.side k j)),
        (∀ y, IsProbabilityMeasure (κ y)) ∧
        (∀ H, Measurable H → (∀ U, |H U| ≤ 1) →
          condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) H =ᵐ[T.ym k j]
            fun U => ∫ V, H V ∂(κ ((B k j).B U))) ∧
        ∀ᵐ y ∂(blockedLaw T B k j), CellDobrushin (κ y) (cell k j) (1 : SU2) linkDist lam γ D₀ b cmin cmax
```

* `CellGeometry T cell c₀ c₁`: `a_k·d(e,e') ≤ L₁·(d(cell e, cell e') + c₀)` and `L₁·d(cell e, cell e') ≤ a_k·d(e,e') + L₁c₁` for all
  fine links (cells of physical size L₁; each coarse link owns one cell). The two-sided comparison excludes degenerate cells: one
  global cell violates the first inequality, single-link cells make the number of cells met by a bounded-extent observable grow with
  the level.
* `κ`: a regular conditional law of the fine field given the block field (exists on these standard Borel spaces; carried as data).
* `CellDobrushin ρ cell s₀ dist λ γ D₀ b c₋ c₊`: the law `ρ` lifted to super-sites (`cellLift`: one value per cell, the whole fine
  configuration with the links of other cells set to `1`, so the super-site space is uniform and no dependent types are needed) is
  consistent (DLR) with a block specification `P` (blocks = sets of cells, any shape) with oscillation influence bounds `k`, block
  sizes `≤ b`, coverage in `[c₋, c₊]`, block diameters `≤ D₀`, range bounds `E`, and the weighted Dobrushin–Shlosman condition
  `Attempts.R3.GDSw P.block k (e^{λE}) γ`. Uniform `b` and `D₀` exclude a single global block.

Decay form and annealed form:

```
def CondMassDecay T B :  ∃ m > 0, ∀ R, ∃ c ≥ 0, ∃ k₀, ∀ k ≥ k₀, ∀ j F G A₀ B₀ D, (F, G measurable, |·| ≤ 1, on A₀, B₀,
    A₀ of physical extent ≤ R, physical distance ≥ D) → ∀ᵐ U, |condCov (T.ym k j) σ(B k j) F G U| ≤ c e^{-mD}
def CondMassAnn T B :    the same for gauge-invariant F, G, both supports of extent ≤ R, time-separated (sepT: 0 ≤ D and
    D ≤ a_k·timeDist on A₀ × B₀), with ∫ |condCov| ≤ c e^{-mD}
```

`condCov μ m F G = E[FG|m] − E[F|m]·E[G|m]`.

### 1.2 Why this form

* **Sup/TV (oscillation) influences, not W₁.** `ObsTransferPhys` quantifies over bounded measurable observables; the Dobrushin
  theorem in oscillation form (`theoremA_w`) gives decay for bounded `F`, `G`; the W₁ form gives decay only against Lipschitz
  observables. c3b's finding (W₁ window reached, sup not) concerns the coarse effective action at L₁, where the centre half binds; the
  conditioned fine system is a different system (massive by the constraint), and there the obstacle to sup form is stiffness, which
  the block form handles.
* **Block (Dobrushin–Shlosman) form on super-sites, not single links.** Single fine links are stiff at weak coupling: changing a
  neighbour moves a link's conditional law by order one in total variation at every level, so any single-link sup condition fails
  uniformly in the level (c3a §4). A block of n⁴ cells feels a changed outside cell only through the boundary layer, whose depth in
  the conditioned system is set by the conditional mass (a bounded number of cells, level-independent); per outside cell the influence
  is O(1), the number of blocks adjacent to a cell without containing it is O(n³), the coverage is n⁴: `GDSw` with γ ~ 1/n. This is
  exactly where the constraint mechanism (block field pins the slow modes, c3a §1) enters.
* **Not log-Sobolev.** LSI ⇒ spatial mixing is not in the library, and for the conditioned system it is not more plausible.
* **Quenched a.e. vs annealed** (§1.4): the Dobrushin form is per conditional law, hence quenched; it is kept as the Lean-checkable
  sufficient condition. The input the assembly needs is the annealed `CondMassAnn` (or part (c) itself).
* **Gauge.** `IsInfluenceBound` tests all bounded functions of a block, gauge-variant ones included; cell boundaries share sites, so
  boundary gauge frames can propagate into a block's gauge-variant functions. Read literally, `CondMass` is therefore stronger than
  needed and could fail for a gauge reason; the intended reading is modulo gauge (influences tested on gauge-invariant block functions,
  or in a gauge fixed inside cells). `CondMassAnn` and part (c) quantify only over gauge-invariant observables and have no such issue.
  A gauge-reduced Dobrushin form needs a block specification on gauge orbits; not done (next step 3).

### 1.3 What the blocking must satisfy for `CondMass` to be plausible

A Dobrushin condition with bounded-range blocks forces exponential decay of conditional covariances **in every direction**. c3a's
Gaussian photon test found a spatial checkerboard blindness for the staple kernel at w = 0.5 (exact) and w = 1 (near), with slowly
decaying, alternating spatial conditional correlations: for those weights `CondMass` (any Dobrushin form) is false. w = 2 (c3b's
weight) keeps rank 3 at the coarse zone corner (coordinator addendum to c3a), not checked away from the corner. So `CondMass`
inherits c3a's design criterion (P1.8): the gauge-invariant part of the linearised coarse flux covariance bounded below on the whole
coarse zone, uniformly in ℓ. The time-separated inputs (`CondMassAnn`, part (c)) need it only in time.

### 1.4 Folding in c4c-seg2 (filter form)

c4c (`../c4c-seg2/NOTE.md`, `formal/ProofPhase/Seg2/Filter.lean`) shows: in the time direction, part (c) is smoother stability of a
hidden Markov model (Euclidean time, fine slice field hidden, block field observed); the only volume-uniform stability theorems are
Dobrushin-type conditions on the conditioned space-time system, i.e. `CondMass`; a quenched version can be false (Rebeschini–van
Handel, EJP 20 (2015): strong observations of composites can make the conditioned system have a phase transition even for an i.i.d.
signal); a per-step TV contraction for every function of a whole slice cannot hold uniformly in volume. Recommended: annealed, local,
modulo gauge. What was done with it:

* The (c)-input of the assembly is now c4c's own statement `Seg2.CondDecouple T B (sepT T)` with the time-separation predicate
  `sepT` (`V3/CondInputs.lean`), and it has three proved sufficient conditions: `CondMassAnn` (`condDecouple_of_condMassAnn`),
  `CondMass` (`condDecouple_of_condMass`, via `CondMassDecay ⇒ CondMassAnn`), and c4c's `Seg2.SmootherStable T B (sepT T)`
  (`Seg2.condDecouple_of_smootherStable`, c4c's Lean), itself implied by `Seg2.AnnealedContraction` (c4c's Lean).
* The named top theorem takes **`CondMassAnn`** (annealed); variants take `CondMass` (`_condMass`), `SmootherStable` (`_smoother`)
  or part (c) itself (`_dec`).
* Not done: the chain `CondMassAnn ⇒ SmootherStable` (c4c's suggested order: local annealed Dobrushin ⇒ smoother stability ⇒ (c)).
  In the present Lean it is not needed, since `CondMassAnn ⇒ (c)` directly (`|condDefect| ≤ ∫|condCov|`). A *local annealed
  Dobrushin* statement (a Dobrushin matrix depending on the block configuration, bad cells rare, disagreement percolation) that
  implies `CondMassAnn` is the right target for a proof but needs a percolation argument not in the library (next step 2).

## 2. The implications

### 2.1 `CondMass ⇒ ObsTransferPhys`(c) — proved (Lean)

| Lean | statement | mark |
|---|---|---|
| `condDefect_eq_integral_condCov` | `m ≤ mX → Bdd1 F → Bdd1 G → condDefect μ m F G = ∫ condCov μ m F G` | D |
| `abs_condDefect_le_of_ae` | `(∀ᵐ x, |condCov μ m F G x| ≤ ε) → |condDefect μ m F G| ≤ ε` | S (small) |
| `abs_cov_le_of_cellDobrushin` | `CellDobrushin ρ cell s₀ dist λ γ D₀ b c₋ c₊`, `|F|,|G| ≤ 1` on `A₀`, `B₀`, `R ≤ dist(cell a, cell a')` ⇒ `|Cov_ρ(F,G)| ≤ b/(c₋(1−γ)) · (c₊ · 2·#(A₀.image cell)) · 2 · e^{−λ(R−D₀)}` | S (Theorem A with weights on super-sites) |
| `condMassDecay_of_condMass` | `CondMass T B → CondMassDecay T B` with rate `λ/L₁` and constant `b/(c₋(1−γ))·c₊·2K_R·2·e^{λ(c₀+D₀)}`, `K_R = 4(2⌊R/L₁+c₁⌋+1)⁴` | S |
| `condMassAnn_of_condMassDecay` | `CondMassDecay T B → CondMassAnn T B` | D/S small |
| `condDecouple_of_condMassAnn` | `CondMassAnn T B → Seg2.CondDecouple T B (sepT T)` | S (small) |
| `condDecouple_of_condMass` | `CondMass T B → Seg2.CondDecouple T B (sepT T)` | S (composite) |

YM-specific: all statements are about `T.ym k j` (SU(2) Wilson on the tori of `T`) and its blocked laws; the proofs are group-blind.

### 2.2 `CondMass ⇒` parts (a), (b) — not for a deterministic blocking

`CondMass` speaks about each conditional law separately; (b) is about how the conditional law depends on the block configuration far
away. Counterexample (shape): an injective non-local blocking (each coarse value records a far cell); the conditional law is a point
mass, `CondMass` holds with zero influences, and `E[F|Φ] = F(Φ⁻¹(·))` depends on far coarse links, so (b) fails. With a **noisy
local** blocking (each coarse link = deterministic smeared value times an independent heat-kernel noise; c3d §5 proposal 3) the
conditional law is `κ(φ) ∝ μ(dU) ∏_x K(φ_x, B_x U)`, the score `s_z = ∂_{φ_z} log K` is bounded, and
`∂_{φ_z} E[F | Φ = φ] = Cov_{κ(φ)}(F, s_z)` (paper); with the **quenched** decay (`CondMassDecay` for every φ, not only a.e.) this
gives (b) with `f` = `E[F|Φ]` with far coordinates frozen, error `≲ Σ_{z far} e^{−m d(z, F)}`, and the Lipschitz clause of
`ObsQuasiLocTW` (Lipschitz constant per coarse link `≤ sup|Cov(G, s_z)|`). So (a), (b) stay a separate named input
`ObsQuasiLocT` / `ObsQuasiLocTW` in Lean.

### 2.3 `CondMass ⇒ EnvelopeW` — needs more, and says what

`EnvelopeW` bounds the coarse potentials of a Gibbs representation of the blocked law in sup norm, weighted by `e^{λ' diam}`,
uniformly in the volume. Needed in addition to `CondMass`:
1. **A noisy local blocking** (so that the blocked law has a density and a Gibbs representation at all; for the deterministic
   good blocking even the representation (R) is open, c3d §1.4).
2. **The quenched form for every block configuration** (sup norms over φ). This is where the Rebeschini–van Handel risk sits; with
   a bounded noise kernel (`K` bounded above and below) the conditioned system is a bounded cell-wise perturbation of the Wilson
   measure for every φ, which makes the quenched form less exposed, not safe.
3. **A choice of potential:** the Kozlov (telescoping) potential, one factor per (site, radius): `V_{i,r}(φ) = log ρ(φ_i | φ on
   ball r) − log ρ(φ_i | φ on ball r−1)` (outside fixed to a reference). Its sup is bounded by the variation of the single-site
   conditional log-density under changes at distance r, and `∂_{φ_z} log ρ(φ_i | φ_{−i})` is an average over `φ_i'` of
   `E_{κ(φ)}[s_z] − E_{κ(φ_i',φ_{−i})}[s_z] = ∫ Cov_{κ(φ_t)}(s_z, s_i) dt`: a two-point conditional covariance, `≲ e^{−m r}`.
   Hence `h(B_r(i)) ≲ r³ e^{−m r}`, and the `EnvelopeW` pair sums are `≲ Σ_r r⁷ e^{−(m−2λ')r} < ∞` for `λ' < m/2` (counting balls
   containing two links). Only two-point covariances enter (no higher cumulants), because the Kozlov potential is built from
   single-site conditional laws.
With 1–3, `CondMass ⇒ EnvelopeW` on paper (not formalised: needs noisy blockings, densities and the interpolation formula). And
`EnvelopeW` alone does not give `H1Local` (`h1Local_of_quasiLocal` also needs per-volume convergence and `NearStable`), and the W₁
route needs the Lipschitz version of the envelope (the same argument applied to `∂_{φ_z}` of the potentials gives it). In v3,
`EnvelopeW` is not a direct input of the gap: the route uses `LevelDprimeW`, and an envelope is one ingredient of its proof.

### 2.4 Is `CondMass` secretly the whole gap? (difficulty conservation, c3a §1)

* **No, for a content-keeping blocking.** The photon (massless) satisfies the conditional mass at Gaussian level in time with the
  good blocking (c3a §3: rate ≈ 4.5/L₁, uniform in ℓ); `CondMass` gives it no gap because `LevelDprimeW` fails for U(1) (the coarse
  W₁ column is `18·(2/π)β ≥ 1` for β ≥ π/36). So `CondMass` is strictly weaker than the gap in the case that matters.
* **Yes, for a content-losing blocking.** For decimation the block field carries vanishing information about bounded-extent
  observables (the noise-limit trap); the conditioned system is then the unconditioned one with sparse pins, and `CondMass` ≈ "the
  fine theory has a mass at the block scale, uniformly in the level": the gap. The split is set by the content of the block variable
  (c3a `condDefect_eq`, `abs_condDefect_sub_cov_le`), which c3b measured (content PASS only at L√σ = 2.80, adjoint ts at 3.7σ).
* **What `CondMass` carries:** (i) segment 1: control of the conditional fluctuations below L_* given the L₁ block field
  (Balaban-type, weak coupling; asymptotic freedom makes it level-uniform); (ii) segment 2: **conditional uniqueness at order-one
  coupling** (no hidden phase transition of the fine field given the block field; c4c's "observability"), non-perturbative but
  gap-free.
* **What stays in `LevelDprimeW` / `LimitDprimeW`:** the infrared content: the blocked effective theory at L₁ is in a uniqueness
  regime (centre half binding in c3b's measurement, adjoint half certified in c3c's window). This is the part that fails below
  1/T_c and for the photon (see the tests).

## 3. `ObsTransferPhysT` — yes, enough (Lean, `V3/TimeSep.lean`)

The torus route uses the transfer once, for `F∘S_n` and `F∘Θ`, which are separated in the **time** coordinate.

| Lean | statement | mark |
|---|---|---|
| `timeDist e e'` | `cyc(e.site 0 − e'.site 0)` (cyclic time distance), `timeDist_le_linkDist` | D |
| `sep_shift_mirror_time` | `2M + 2s + 2 ≤ N`, `l, l' ∈ timeSlab 0 s` ⇒ `M ≤ timeDist (shiftLink M l) (mirrorLink l')` | D |
| `ObsTransferPhysT T B` | `ObsTransferPhys` with `0 ≤ D` and the separation `∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ a_k · timeDist e e'` | named |
| `obsTransferPhysT_of_phys` | `ObsTransferPhys T B → ObsTransferPhysT T B` | D |
| `torusDecayLoc_of_blockGapUnifT` | `0 < λ → BlockGapUnif T B λ → ObsTransferPhysT T B → TorusDecayLoc T.toV` | S |
| `LevelTorusRouteT T` | `∃ B λ, 0 < λ ∧ LevelDprime T B λ ∧ ObsTransferPhysT T B` | named route |
| `levelTorusRouteT_of_level`, `bothOrdersLoc_of_levelRouteT` | `LevelTorusRoute → LevelTorusRouteT`; `a_k → 0 → LevelTorusRouteT → TorusDecayLoc ∧ MassGapLoc ∧ MassGapMFLoc` | D; S |

## 4. The W₁ route in Lean (`V3/W1Route.lean`)

| Lean | statement | mark |
|---|---|---|
| `LevelDprimeW T B λ` | `∃ γ D₁, 0 ≤ γ ∧ γ e^{λD₁} < 1 ∧ ∃ k₀, ∀ k ≥ k₀, ∀ j, ∃ V : CoarsePot j`, blocked law `= gibbsMeasure haar V`, `V` a bounded local potential, single-link W₁ influences `kk` (geodesic cost) with column sums `≤ γ` and range `≤ D₁` | named |
| `blockGapUnifW_of_levelDprimeW` | `0 ≤ λ → LevelDprimeW → BlockGapUnifW` (bounded `f` against Lipschitz `g`, constant `π/(1 − γe^{λD₁})`) | S |
| `H1LocalLipW T B Vk Vinf` | blocked laws `= gibbsMeasure haar (Vk j k)`, potentials bounded local, and `InfluenceDevW geodSU2 {i} (siteSpec Vinf) (siteSpec Vk) z (δ_k(i,z))` with column sums `≤ ε_k → 0` uniformly in `j`, range `≤ D₁` | named (Lean form of c3c's `H1LocalLip`) |
| `levelDprimeW_of_h1LocalLip` | `H1LocalLipW T B Vk Vinf → LimitDprimeW Vinf → ∃ λ > 0, LevelDprimeW T B λ` (γ' = (1+γ)/2, range `max(1, D₁)`) | S (W₁ openness) |
| `levelDprimeW_of_certified` | `CertifiedAdjointW → |β_A| ≤ cornerA c → |β_F| ≤ cornerF c → H1LocalLipW T B Vk (fun _ => twoCoupling β_F β_A) → ∃ λ > 0, LevelDprimeW T B λ` | S (composite) |
| `ObsTransferPhysTW`, `ObsQuasiLocTW` | `ObsTransferPhysT` / its (a)(b) part with `LipBound geodSU2 g (fun _ => K)`, `0 ≤ K` | named |
| `wcorr_le_blockedW`, `torusDecayLoc_of_blockGapUnifW` | one-level estimate; `BlockGapUnifW (λ > 0) ∧ ObsTransferPhysTW ⇒ TorusDecayLoc` | S |
| `LevelTorusRouteW`, `bothOrdersLoc_of_levelRouteW` | `∃ B λ, 0 < λ ∧ LevelDprimeW ∧ ObsTransferPhysTW`; gives both orders of limits | named route; S |

Named limitations: (1) finite range `D₁` of the W₁ coefficients (the library's W₁ Theorem A is finite-range; a weighted W₁ Theorem A,
the W analogue of `Attempts.R3.theoremA_w`, would remove it). (2) `H1LocalLipW` is stated through W₁ deviations of the single-link
conditional laws (a C¹-type closeness); the bound of these by sup and Lipschitz norms of `V_k − V_∞` is c3c §5 (paper).
(3) The Lipschitz approximant in `ObsQuasiLocTW` is an extra demand of the W₁ decay theorem; with a noisy blocking it follows from
`CondMass` (§2.2), otherwise c2a §2.2's regularisation (paper).

## 5. Assembly v3 (`V3/Top.lean`) and claim discipline

**Top theorem (exact):**

```
structure OpenInputsV3 (T : Tuning) : Prop where
  lcp : OnLCP T
  nontrivial : NonTrivial T
  crossover : LevelTorusRouteW T ∨ LevelTorusRouteT T

theorem yang_mills_assembly_v3 {T : Tuning} (P : OpenInputsV3 T) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T
```

**Named form of the preferred route (exact):**

```
theorem yang_mills_assembly_v3_W1 {T : Tuning} (hL : OnLCP T) (hN : NonTrivial T) (B : BlockingFamily T)
    {Vk : ∀ j, ℕ → CoarsePot j}
    {Vinf : ∀ j, LatticePlaquette 4 (coarseSide j) → GaugeConnection SU2 4 (coarseSide j) → ℝ}
    (hH1 : H1LocalLipW T B Vk Vinf) (hD : LimitDprimeW Vinf) (hC : CondMassAnn T B) (hQ : ObsQuasiLocTW T B) :
    OpenInputsV3 T ∧ TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T
```

Variants: `_dec` (part (c) `Seg2.CondDecouple T B (sepT T)` as input), `_condMass` (`CondMass`), `_smoother` (`Seg2.SmootherStable T B
(sepT T)`), `yang_mills_assembly_v3_certified` (`CertifiedAdjointW`, a corner `c`, `Vinf = fun _ => twoCoupling β_F β_A` in the
corner), `yang_mills_assembly_v3_sup` (`LevelDprime T B λ`, `CondMassAnn`, `ObsQuasiLocT`). Compatibility: `openInputsV3_of_level`
(`OnLCP → NonTrivial → LevelTorusRoute → OpenInputsV3`), `openInputsV3_of_blockedTorusRoute` (cycle 2's route). Pure noise:
`not_trivial_v3`.

**Marks.** `yang_mills_assembly_v3`: S as an assembly (cases into the two route theorems, each S). `_W1`, `_certified`, `_sup`,
`_condMass`, `_smoother`, `_dec`: S (composites of the S reductions above). `openInputsV3_of_*`, `not_trivial_v3`: D.

**Does any hypothesis contain the conclusion?** Checked input by input. `OnLCP`, `NonTrivial`: no decay statement. `LevelDprimeW`,
`LevelDprime`, `H1LocalLipW`, `LimitDprimeW`: statements about the blocked (coarse) laws or a limit action; they imply decay of
**block** observables only. `ObsQuasiLocT(W)`: `L¹` closeness of conditional expectations to local coarse functions; no covariance
bound at all. `CondMassAnn`, `CondMass`, `SmootherStable`: properties of the conditioned system; the photon satisfies them without a
gap. **The one place where care is needed:** part (c) (`CondDecouple`), taken as an input in the `_dec` variant, is equivalent to the
decay of the fine covariance *given* the coarse decay and (b) (c3a, `condDefect_eq`). The `_dec` variant is therefore a
law-of-total-covariance reduction, honest but thin; the named theorem replaces it by `CondMassAnn`, whose content is that the
conditioned system mixes (gap-free). None of the hypotheses is, alone or by a definitional step, the conclusion; the theorem is not
worthless in the sense of round 4.

**YM-specific:** every hypothesis is about `wilsonMeasure SU2 2 β_k` on the tori of `T`, its blocked laws, or its conditional laws
given the block field; `OnLCP` fixes the SU(2) one-loop slope and the SU(2) flux scheme; `CertifiedAdjointW` is SU(2)-specific
(Bingham laws on S³). All proofs are group-blind.

## 6. Unit tests for `CondMass` (and `CondMassAnn`)

| test | expected | result |
|---|---|---|
| photon (U(1), weak coupling) | `CondMass` should hold for a content-keeping blocking and carry no gap | holds at Gaussian level in time with the good blocking (c3a §3; spatial direction requires §1.3's design criterion); no gap follows: `LevelDprimeW` fails for U(1). Pass: `CondMass` is not the gap |
| Z₂ (weak coupling) | gap, no confinement; gap-type inputs must hold, no area law | the conditioned system is massive (small fluctuations, informative block field); `CondMass` holds; nothing here implies an area law (all conclusions are gap-type, statements typed on SU(2)). Pass |
| deconfinement (box one block thick, L₁ < 1/T_c) | must fail or be harmless | harmless: the ordered Polyakov sector is carried by the block field (a centre-covariant blocking observes it), the conditioned system can be massive, `CondMass` may hold; the coarse condition `LevelDprimeW` fails there. Pass |
| mixture (½(μ₁+μ₂), RP, invariant, area law, no gap) | must not give a gap | if the block field identifies the component, the conditional law is the component's and `CondMass` can hold; the between-component covariance sits in `Cov(E[F|Φ], E[G|Φ])` (coarse) where `LevelDprimeW` fails (a Dobrushin condition forces uniqueness). If the block field does not identify it, the conditional law is a mixture and `CondMass` fails. Harmless either way. Pass |
| unobserved symmetry (c4c's new test: centre-blind blocking, deconfined phase) | (c) must fail | the conditioned system keeps the unobserved centre order (two phases given the block field): `CondMassAnn` and `CondMass` fail, as they must. The good blocking is centre covariant (P1.8), so the test bites only on centre-blind blockings. Pass |
| noise-limit trap (decimation) | `CondMass` must not be cheap | it is not: it becomes the gap itself (§2.4). Pass (consistent), and the reason the good blocking is required |
| Heller endpoint (string tension, massless 0⁺⁺) | no gap | the massless mode is visible in the block field, conditioned system massive, `CondMass` may hold; coarse condition fails. Pass |
| Banks–Zaks | no gap | conditioned system massive by constraint; the coarse theory stays weakly coupled and massless, `LevelDprimeW` fails. Pass |
| triviality (φ⁴₄) | no existence claim | none made; Gaussian limits satisfy `CondMass`. Pass |
| finite subgroups | — | proofs group-blind, hypotheses typed on SU(2); no claim. Pass |
| pure noise (β = 0) | must fail the inputs | fails `OnLCP` (`not_trivial_v3`). Pass |

## 7. Blueprint changes (proposed for `../../PROOF-BLUEPRINT.md`; not edited, outside this workstream's files)

* **P5.2 / `ObsTransferPhys`:** "the route needs only the time-separated form `ObsTransferPhysT` (Lean, `V3.torusDecayLoc_of_blockGapUnifT`);
  its part (c) (`Seg2.CondDecouple` with `sepT`) follows from `CondMassAnn` (annealed conditional covariance), from `CondMass`
  (Dobrushin–Shlosman on cells, Lean `condDecouple_of_condMass`) or from c4c's `SmootherStable`; parts (a)(b) are `ObsQuasiLocT(W)`,
  open (from `CondMass` on paper for a noisy local blocking)."
* **P4.1′/P4.1″:** "W₁ route in Lean (`V3/W1Route.lean`): `LevelDprimeW` ⇒ W₁ block gap; W₁ openness `H1LocalLipW ∧ LimitDprimeW ⇒
  LevelDprimeW`; `CertifiedAdjointW` feeds it for limits in the certified window. Open: `LevelDprimeW` for the measured anisotropic
  action (c4d)."
* **P3.5:** add "`CondMass ⇒ EnvelopeW` on paper, given a noisy local blocking, the quenched form and the Kozlov potential (c4a §2.3);
  not in Lean."
* **P7:** new row P7.2″: "`yang_mills_assembly_v3` (cycle 4, c4a): open inputs `OnLCP`, `NonTrivial`, `LevelTorusRouteW ∨
  LevelTorusRouteT`; named form `H1LocalLipW, LimitDprimeW (or CertifiedAdjointW), CondMassAnn, ObsQuasiLocTW`; both orders of limits.
  Lean." And in the "open inputs" paragraph: replace cycle 2's list by the v3 list of `ASSEMBLY.md`.
* **P1.8:** add "CondMass in any Dobrushin form requires the spatial design criterion (c3a §7); the staple kernel at w = 0.5, 1 fails it."

## 8. Next step

1. **`CondMassAnn` at Gaussian level, proved for the good blocking at w = 2:** the coercivity bound on `ker Q` (c3a next step 2) in
   all directions, which is the base case of both `CondMass` and the spatial design criterion; then check w = 2 away from the corner.
2. **A local annealed Dobrushin form ⇒ `CondMassAnn`** in Lean: per-cell Dobrushin coefficients depending on the block configuration,
   bad cells (large fields) dominated by a subcritical Bernoulli field; disagreement percolation (van den Berg–Maes) gives annealed
   decay. This is the form that can absorb Balaban's large-field regions.
3. **Gauge-reduced super-sites:** state `CellDobrushin` on gauge-invariant block functions (or in a cell-internal axial gauge) so the
   literal `CondMass` loses its gauge-frame artefact.
4. **Weighted W₁ Theorem A** (port of `Attempts.R3.theoremA_w` to the W form), removing the finite range from `LevelDprimeW` and
   `H1LocalLipW`.
5. **Noisy blockings in the assembly** (c3d §5): `BlockingFamily` with independent coarse-link noise; then §2.2 and §2.3 become Lean
   targets (interpolation formula, Kozlov potential), and `ObsQuasiLocTW` and `EnvelopeW` both reduce to the quenched `CondMass`.

## Files

- `../../../formal/ProofPhase/V3/TimeSep.lean`: `timeDist`, `timeDist_le_linkDist`, `sep_shift_mirror_time`, `slab_time_sep`,
  `ObsTransferPhysT`, `obsTransferPhysT_of_phys`, `torusDecayLoc_of_blockGapUnifT`, `LevelTorusRouteT`, `levelTorusRouteT_of_level`,
  `bothOrdersLoc_of_levelRouteT`.
- `../../../formal/ProofPhase/V3/CondMass.lean`: `condCov`, `condDefect_eq_integral_condCov`, `abs_condDefect_le_of_ae`, `cellLift`,
  `cellProj`, `CellDobrushin`, `abs_cov_le_of_cellDobrushin`, `CellGeometry`, `CondMass`, `CondMassDecay`, `condMassDecay_of_condMass`,
  `ObsQuasiLocT`, `obsQuasiLocT_of_obsTransferPhysT`, `obsTransferPhysT_of_condMassDecay`, `obsTransferPhysT_of_condMass`.
- `../../../formal/ProofPhase/V3/W1Route.lean`: `LevelDprimeW`, `BlockGapUnifW`, `blockGapUnifW_of_levelDprimeW`, `H1LocalLipW`,
  `levelDprimeW_of_h1LocalLip`, `levelDprimeW_of_certified`, `ObsTransferPhysTW`, `ObsQuasiLocTW`, `obsTransferPhysTW_of_condMassDecay`,
  `obsTransferPhysTW_of_condMass`, `wcorr_le_blockedW`, `torusDecayLoc_of_blockGapUnifW`, `LevelTorusRouteW`,
  `bothOrdersLoc_of_levelRouteW`.
- `../../../formal/ProofPhase/V3/CondInputs.lean`: `sepT`, `CondMassAnn`, `condMassAnn_of_condMassDecay`, `condDecouple_of_condMassAnn`,
  `condDecouple_of_condMass`, `obsTransferPhysT_of_condDecouple`, `obsTransferPhysTW_of_condDecouple`, `condDecouple_of_obsTransferPhysT`.
- `../../../formal/ProofPhase/V3/Top.lean`: `OpenInputsV3`, `yang_mills_assembly_v3` and its named variants, `openInputsV3_of_level`,
  `openInputsV3_of_blockedTorusRoute`, `not_trivial_v3`.
- Here: `setup.sh`, `build.sh`, `axioms.sh`, `axioms.log`. No numerics; no commit, push or GPU.

## References (ideas only; recalled unless marked)

Dobrushin (1968, 1970), Dobrushin–Shlosman (1985) (block/finite-volume uniqueness conditions); Kozlov (1974) (telescoping potentials
from quasilocal specifications); van Enter, Fernández, Sokal, J. Stat. Phys. 72 (1993) (pathologies of RG maps, conditioned systems);
Rebeschini, van Handel, EJP 20 (2015) (phase transitions in filtering; as relayed by c4c); van den Berg, Maes, Ann. Probab. 22 (1994)
(disagreement percolation). Project: `../c3a-uv/NOTE.md`, `../c3c-certified/NOTE.md`, `../c3d-h1/NOTE.md`, `../c3b-refit/PREREG.md`,
`../c4c-seg2/NOTE.md`.
