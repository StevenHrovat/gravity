# Round 3, attempt 1: torus robustness, and the chain closed (2026-11-21)

Brief: prove the torus robustness lemma and with it a machine-checked theorem "gap ⇐ H1 + the limit effective theory at L₁
satisfies a soft-swap (S′) condition", replacing `LimitGDS_W` of `gap_of_effective_W` by a local-factor condition, so that only
W_p and the crossover remain open (`../ROUND-2.md` table).

Claim levels as in `../RULES.md`: **proved (Lean)**, **proved (paper)**, **proved modulo** (a named standard result), **stated gap**,
**heuristic**. Lean: `../../../formal/Attempts/R3/{TailDecay,FlatFactors,Robust}.lean`, built in `~/formal-att-r3-1` (Lean 4.34.0,
Mathlib as pinned), no `sorry`, no new axioms, no `native_decide`; `#print axioms` on every main theorem: `propext`,
`Classical.choice`, `Quot.sound`. Scripts here: `build-r3-1.sh`, `axioms-r3-1.sh`. No numerics were run.

---

## 0. Results at a glance

| # | statement | level |
|---|---|---|
| 1 | **The soft-swap criterion is boundary-uniform.** B's deterministic S′ (flat factors) is a pointwise condition on the local factors; it implies Dobrushin's uniqueness condition for the single-site specification, which holds for **every boundary condition**. So no torus-only robustness lemma is needed: the torus/boundary distinction that motivated it disappears for flatness criteria | **proved (Lean)**: `influence_site`, `gds_of_flat`, `flat_of_count` |
| 2 | **D′, the sharpened criterion.** `∑_{i≠z} tanh(S_iz/2) ≤ γ < 1`, `S_iz` the change of the factors through both sites. Per factor sharper than S′ (`tanh(o/2) ≤ 1 − (ψ_min/ψ_max)²`); for plaquette factors in d = 4 the count is 18 against S′'s 20. Wilson window: SU(2) α_s > 5.72 (S′: 24.8), U(1) α > 1.43 (S′: 6.2). D′ reproduces the project's `gds_single` exactly | **proved (Lean)** (comparison), numbers by hand |
| 3 | **The right shape of H1 is local**: closeness of the local potentials in sup norm at each site. Single-site conditional laws see only the factors at one site, so `SpecDist ≤ tanh(ε/2)` with no volume factor (D's warning does not bite). H1-local implies `EffectiveConvergence` as formalised | **proved (Lean)**: `specDist_site`, `effectiveConvergence_of_local` |
| 4 | **Openness (the robustness lemma in local form).** Under H1-local the level-k effective theory itself satisfies D′ with `γ + 2ε_k`, hence with `(1+γ)/2` from some k₀ on, in every volume | **proved (Lean)**: `pairOsc_of_close`, `flatW_of_close`, `levelFlat_of_local` |
| 5 | **Quasi-local factors.** Theorem A with a weighted Dobrushin condition and no finite-range assumption; D′_λ = `∑_{i≠z} tanh(S_iz/2) e^{λ dist(z,i)} ≤ γ < 1`. Tails need only finite weighted sums | **proved (Lean)**: `theoremA_w`, `decay_of_flatW` |
| 6 | **Gap uniform in the lattice spacing** (route 1 finite range through the existing `gap_of_effective`; route 2 quasi-local, direct), block observables of the effective and of the fine theory, physical units | **proved (Lean)**: `gap_of_localFactors`, `gap_of_localFactorsW`, `gap_of_localFactorsW_fine` |
| 7 | **Gap of the continuum limit, per volume** (route A): level-k block laws converging to the limit theory (what W_p + D's lemma T give, no locality, per volume) + D′_λ for the limit ⇒ limit covariances decay at rate λ/L₁ uniformly in the volume, and lattice covariances converge to them | **proved (Lean)**: `continuum_decay`, `limit_decay` |
| 8 | General local (sub-L₁) gauge-invariant observables of the fine theory | **stated gap**: a conditional-decoupling hypothesis (§6) |
| 9 | The genuinely torus-only criterion (B's chessboard S′) is also open in the local norm (free-energy continuity) | **proved (paper) modulo** FILS chessboard and full RP of the blocked theory (§7) |
| 10 | Unit tests: Z₂ (holds, no area law claimed), photon (D′ fails at every scale for the Coulomb phase) | §8 |

**Bottom line.** The third piece of the round-2 map (robustness on the torus) is closed: the condition B called S′ is already
boundary-uniform, it is open in the local norm of the effective action, and the full chain from it to decay in physical units is
in Lean, for quasi-local effective actions. After it the reduction reads (§5):

> **gap of the continuum theory at scale L₁ (uniform in the volume) ⇐ W_p (per volume, D's form) + [Crossover-D′]: the continuum
> limit, blocked to L₁, is the Gibbs measure of quasi-local potentials on compact block variables satisfying D′_λ.**

The crossover piece now has a precise, checkable form, and it is a strong (worst-case, disorder) statement: in C's two-coupling
stand-in at L₁√σ ≈ 3 it fails by a factor of about 6 in the adjoint coupling (§9).

---

## 1. Why there is no torus robustness lemma to prove

**Setting** (`FlatFactors.lean`). Coarse indices `ι` (cells or coarse links at scale L₁), block variables in `S` with a reference
probability `ν` (Haar for group-valued block variables), factors `x` with supports `supp x` and log-potentials `V x` depending only
on `supp x`, bounded (`Potential`). The effective measure is `gibbsMeasure ν V = Z⁻¹ e^{∑_x V x} ν^{⊗ι}`; the factors of B's §3.4
are `ψ_x = e^{V x}`, `ψ_min/ψ_max = e^{−osc V x}`.

**Single-site influence** (`influence_site`, Lean). Fix sites `i ≠ z`. The conditional law of `σ_i` given the rest has density
`∝ exp(∑_{x ∋ i} V x)`. Moving `σ_z` changes only the factors through both `i` and `z`; if their summed log-potential moves by at
most `S_iz` (in absolute value, at every configuration), the two conditional densities differ by a log-weight of oscillation
`≤ 2 S_iz`, so by the project's TV lemma (`Influence.tv_gibbs_le_tanh`) their total variation is `≤ tanh(S_iz/2)`, and this is an
H-form influence bound (`OneScale.IsInfluenceBound` for the block `{i}`) **for every boundary condition**. With single-site blocks
the coverage is 1 and GDS is `∑_{i≠z} k_i(z) ≤ γ` (`gds_of_flat`): Dobrushin's condition (Dobrushin 1968, 1970) in column form.

**Consequence.** B's S′ asks `(factors meeting a factor) × (1 − (ψ_min/ψ_max)²) < 1`, with min and max over all configurations.
That is a pointwise statement, so it controls the worst boundary as well as the typical one. `flat_of_count` (Lean): if every
factor has oscillation `≤ o₀` and every site has at most `M` (site, factor) pairs, `M tanh(o₀/2) ≤ γ` gives D′, and
`tanh(o/2) ≤ 1 − (ψ_min/ψ_max)²` (`tanh_half_le_one_sub_ratio_sq`) turns S′'s per-factor quantity into D′'s. For plaquette-type
factors (each site in `m` factors of size `s`, `s ≤ m`) the pair count `m(s−1)` is at most S′'s `s(m−1)`, so S′ ⇒ D′; in d = 4
plaquettes give 18 against 20. The swap engine of B was a torus engine; its deterministic hypothesis is not a torus hypothesis.
Only the chessboard version (typical instead of worst-case flatness) is torus-only; §7.

**Calibration.** For the Wilson action `V_p = β Re tr U_p`, `S_iz = common(i,z)·2nβ` and D′'s coefficient is
`tanh(common·nβ)`, exactly `OneScale.SingleLink.kSingle`; D′ is `gds_single` (`18 tanh(nβ) < 1`). Windows (artanh(1/18) = 0.05561):
SU(2) `β_std < 0.0556`, `g² > 71.9`, **α_s > 5.72** (B's S′: β_std < 0.0128, α_s > 24.8); U(1) `β < 0.0556`, `e² > 18.0`, **α > 1.43**
(S′: α > 6.2). Classical strong-coupling Dobrushin numbers; nothing new as physics, but it fixes the constants of the hand-over.

## 2. The shape of H1

D's warning (`../r2-stepscaling/NOTE.md` §4): relative sup-norm closeness of **whole** densities is extensive in the volume. The
single-site specification only sees the factors at one site, so the natural H1 is **local**:

- **H1-local** (`LocalConvergence`): `∑_{x ∋ i} |V_k(x,σ) − V_∞(x,σ)| ≤ ε_k → 0` for every site, configuration and volume.
- `specDist_site` (Lean): then `SpecDist {i} (q_∞) (q_k) ≤ tanh(ε_k/2) ≤ ε_k`, uniformly in the boundary condition and **without
  a volume factor**; `siteSpec_isLocal` gives the finite shells. So H1-local implies `EffectiveConvergence` exactly as formalised
  (single-site blocks, shells = factor neighbourhoods): `effectiveConvergence_of_local`.
- `EffectiveConvergence` with SpecDist on large blocks would not be the right target (SpecDist over a block of `b` sites costs
  `b`, and per-block TV is extensive in the block); single sites are.

H1-local is stronger than D's W_p: W_p is whole-density closeness at a weak scale, per volume; H1-local needs the renormalisation
group from L_p to L₁ to **preserve quasi-locality** of the effective action and be continuous in the local norm. That is the
classical "blocked measures stay Gibbsian" question (van Enter, Fernandez, Sokal 1993: it can fail), known only where a cluster
expansion converges. Through the crossover (α_s from about 0.5 to 3.5) nobody controls it. Route A (§5) avoids it.

## 3. Openness: robustness in local form

`pairOsc_of_close` (Lean): if `S` bounds the pair oscillations of `V_∞` and `|V_k(x) − V_∞(x)| ≤ η_k(x)`, then
`S_iz + 2∑_{x∋i,z} η_k(x)` bounds those of `V_k`. `flatW_of_close`: with `tanh(a+b) ≤ tanh a + tanh b` and `tanh b ≤ 2b`, D′_λ
for the limit with `γ` gives D′_λ for level k with `γ + 2ε_k` (ε_k the weighted pair sum of η_k). `levelFlat_of_local`: from some
`k₀` on, D′_λ with `(1+γ)/2` holds for **the level-k effective theory itself, in every volume**. This is the lead in the brief made
a theorem: S′/D′ is an open condition, and H1 stated as local closeness puts the level-k theory inside it.

## 4. Quasi-local factors (polymer tails)

Balaban-type effective actions have exponentially small non-local tails. Theorem A in the project (`theoremA_H`) needs finite
range (`γ e^{λ D₁} < 1`, coefficients zero beyond `D₁`). `TailDecay.lean` replaces range plus GDS by one weighted condition
(`GDSw`: `∑_{j: x∉B_j} k_j(x) e_j(x) ≤ γ c(x)`, `e_j(x)` bounding the growth of the weight into `B_j`), the block form of the weighted
Dobrushin condition (Gross 1979; Dobrushin–Pechersky 1983), and proves `theoremA_w`: the same covariance bound with `γ` in place
of `γ e^{λD₁}`, no finite-range assumption, constants independent of the number of sites and blocks. For single sites:

- **D′_λ** (`FlatCriterionW`): `∑_{i≠z} tanh(S_iz/2) e^{λ dist(z,i)} ≤ γ < 1`.
- **H1-local, weighted** (`LocalConvergenceW`): `∑_{i≠z} (∑_{x∋i,z} η_k(x)) e^{λ dist(z,i)} ≤ ε_k → 0`.

**What range condition the chain needs**, precisely: these two weighted sums, uniformly in the volume, for one `λ > 0`. A
sufficient condition (heuristic bookkeeping, standard): `osc V_x ≤ c e^{−a·size(x)}` with at most `e^{b·n}` factors of size `n`
through a site and `dist ≤ size`, then D′_λ holds for `λ < a − b` once its `λ = 0` sum has room. Nothing finite-range is needed.

`decay_of_flatW` (Lean): D′_λ gives, for one effective theory, `|Cov(f,g)| ≤ (1−γ)⁻¹ (∑_A v_a) L_g e^{−λR}` (coarse distance `R`).

## 5. The final form of the reduction

**Route B (uniform in the lattice spacing)**, `gap_of_localFactorsW` (Lean): potentials `V_k` (level k) and `V_∞` (limit) on the
block variables of every volume; blocks of physical size `s_k = ⌈L₁/a_k⌉a_k`, `a_k → 0`. If H1-local (weighted) and D′_λ for
`V_∞` hold, there are `m = λ/(2L₁)`, `C = 2/(1−γ)` and `k₀` such that for every `k ≥ k₀` and every volume, block observables at
physical distance `R` satisfy `|Cov| ≤ C (∑_A v_a) L_g e^{−mR}`. `gap_of_localFactorsW_fine`: the same for the fine theory's
observables `f∘Φ` when the block-variable law of the fine theory is `gibbsMeasure ν V_k`. Route 1, `gap_of_localFactors`
(finite range), goes through the existing `OneScale.Effective.gap_of_effective` with `effectiveConvergence_of_local` and
`limitGDS_of_flat`: **`LimitGDS` is replaced by D′, as the brief asked**. The H form suffices at L₁: the H/W issue
(`../twist/NOTE.md` S1, the central jump) concerns the lattice scale, where factors are not flat; flat factors give H bounds.

**Route A (the continuum limit)**, `continuum_decay` (Lean): let `μ_{v,k}` be the level-k block laws, *any* measures, converging
in each volume `v` to the limit theory on bounded measurable functions. W_p plus D's lemma T give exactly this: at the weak scale
`L_p = 2^{−N}L₁`, `e^{−ε_k(v)} ≤ ρ_{k,p}/ρ_{∞,p} ≤ e^{ε_k(v)}`; N blocking steps form one fixed kernel on L_p-variables (the same
for every k), which preserves the bound (lemma T(a)), so `|μ_{v,k}(h) − μ_{v,∞}(h)| ≤ (e^{ε_k(v)}−1) sup|h| → 0`. If the limit
theory satisfies D′_λ, then in every volume the lattice block covariances converge to limit covariances bounded by
`C (∑_A v_a) L_g e^{−(λ/L₁)R}`, `C = (1−γ)⁻¹` independent of the volume. No locality of the level-k theories, no uniformity in k,
no robustness lemma. This is the statement about the continuum theory that the gap is about.

**The remaining open inputs, stated exactly.**
1. **W_p** (unchanged from D): per volume, `sup_U |log ρ_{k,p} − log ρ_{∞,p}| → 0` at one weak scale L_p, large fields included.
2. **Crossover-D′**: the limit theory blocked to L₁ (block variables compact, e.g. group-valued Balaban-type block links,
   chosen covariantly and reflection-compatibly) is the Gibbs measure of quasi-local potentials whose pair oscillations satisfy
   D′_λ with one `γ < 1` in every volume. Equivalently (all the proofs use only this): its single-site conditional laws have
   Dobrushin coefficients with weighted column sums `≤ γ < 1`.

For route B, 1 is replaced by H1-local (weighted), which additionally needs the RG through the crossover to preserve locality.
Recommendation: carry route A as the reduction; route B is the stronger, lattice-uniform form, with a heavier H1.

## 6. Units and observables

- **Physical units** are as in `Physical.lean` (`blockSize`, `exp_phys_le`): rate `λ/(2L₁)` at level k (blocks between L₁ and
  2L₁ once `a_k ≤ L₁`), `λ/L₁` in route A.
- **Fine observables that are functions of the L₁ block variables**: proved (`gap_of_localFactorsW_fine`, `cov_map`).
- **General local gauge-invariant observables of the fine theory** (a plaquette at the lattice scale): **stated gap.** With
  `Φ` the block map, `Cov(F,G) = Cov(E[F|Φ], E[G|Φ]) + E[Cov(F,G | Φ)]`. The first term decays by the results above if
  `E[F|Φ]` is a quasi-local function of the block variables near the support of F (Theorem A needs the oscillations of
  `E[F|Φ]` to decay away from the support; with exactly local `E[F|Φ]` it is `cov_map` again). The second term needs the
  fine field to be short-range correlated **given** the block variables, uniformly in them: the fluctuation-field covariance of a
  block-spin RG is massive at the block scale (Balaban's construction has this in the small-field region). Hypothesis
  **H1-fine (conditional decoupling)**: `sup_φ |Cov(F,G | Φ = φ)| ≤ c e^{−m' dist}` and `E[F|Φ]` quasi-local. It is ultraviolet
  (same territory as W_p) and is not formalised here.
- **Spectral reading.** Decay of `Cov(F, F∘Θ∘shift)` for F built from blocks inside the positive half gives a transfer-matrix
  gap on the closed span of those vectors (the project's Theorem C machinery). This needs RP only in the **gated form**
  (r3-dmp's `gated_rp`): F∘Φ is a function of fine variables in the positive half when no block straddles the plane, and the
  fine theory is RP (proved). A gap on the whole Hilbert space needs the observables of the previous item (density).

**Answer to the coordinator's RP question.** Routes 1, 2 and A use **no reflection positivity at all** (Dobrushin, not
chessboard). RP enters only (i) the spectral reading, for which the gated form suffices as just said (blocks not straddling the
reflection plane; the coarse variables of the observable drawn from one half), and (ii) the chessboard version of §7, which needs
**full RP of the blocked measure itself** under the coarse reflections used by the chessboard estimate (every coarse variable,
including those straddling or lying in the plane, because the chessboard bound reflects events of the whole coarse configuration
across all planes). The partial (gated) form does not suffice for (ii). Since D′ already contains the deterministic S′, (ii) is
needed only if the crossover can be certified for typical but not for worst-case configurations.

## 7. The genuinely torus-only criterion: chessboard S′

B §3.3: if the effective measure is RP, the chessboard bound gives decay once `(3^d − 1) z̃ < 1`, `z̃ = (Z_bad/Z)^{1/|Λ|}` the
disseminated probability of "the block contains an active factor" (Z_bad: the partition function restricted to every block bad).
Under H1-local with per-block summed sup distance `ε` (sites per block times the per-site ε), `|log Z_k − log Z_∞| ≤ |Λ|ε` and the
same for `Z_bad`, so `z̃_k ≤ e^{2ε_k} z̃_∞`: **the chessboard criterion is open in the local norm too**, and the torus robustness
lemma for it is "free-energy continuity + RP of the level-k blocked measures". Status: **proved (paper) modulo** FILS (chessboard
estimates) and full RP of the blocked theory (§6, item ii); not formalised. Its only advantage over D′ is typical instead of
worst-case flatness; for compact block variables with bounded potentials the two differ by constants, not in kind.

## 8. Unit tests

**Z₂ at weak coupling (gap-only test).** The conclusions (decay of covariances) are true for weak-coupling Z₂, so nothing
forbids its gap. The hypothesis D′ is not met at any scale: the deconfined Z₂ theory flows to the ordered side, its blocked factors
sharpen (`ψ_min/ψ_max → 0`), and D′ needs them flat. No theorem here asserts an area law. Caveat, **heuristic**: D′ is a
boundary-uniform condition, and Chatterjee's theorem (decay under arbitrary boundary conditions + nontrivial centre ⇒ area law)
would turn D′ at some scale into an area law for the effective Wilson loops. So D′ is confinement-strength: it cannot serve a theory
with a gap but no confinement (weak-coupling Z₂, Higgs phases), and for weak-coupling Z₂ it must fail, consistent with the flow.
The gap of weak-coupling Z₂ is the ordered mechanism (round 1's Theorem R), which this route does not cover. Consistent with
`../RULES.md`: gap-only conclusion, holds for Z₂ where applicable, no area law claimed.

**Photon (U(1) at weak coupling).** If the U(1) effective theory at some scale L satisfied D′_λ, `decay_of_flatW` would give
exponential decay of all bounded local block observables in every volume, uniformly; but in the Coulomb phase block observables of
the field strength have power-law correlations (massless photon: Guth 1980, Froehlich–Spencer 1982, recalled). So D′ fails at every
scale: **proved modulo** the Coulomb-phase theorem. Concretely, the compact U(1) effective coupling stays in the Coulomb phase
(β_eff above β_c ≈ 1.01 at every scale, no running), far above D′'s `β < 0.056`. Route A for U(1) at fixed bare coupling: the
convergence hypothesis may hold trivially (free photon limit), D′ fails: no gap claimed. Pass.

**Triviality test**: not applicable; nothing here is an existence claim (route A assumes the limit).

## 9. What the crossover must now deliver, and a number

Crossover-D′ in C's two-coupling stand-in (`../r2-curvature/NOTE.md`: per-plaquette `β_F t + (β_A/3)(4t² − 1)`, `t ∈ [−1,1]`):
plaquette oscillation `o = 2β_F + (4/3)β_A`, D′ (plaquette factors) `18 tanh(o/2) < 1`, i.e. `o < 0.111`, **β_A < 0.083** for
β_F ≈ 0. C's stand-in at L₁√σ = 3 has β_A ≈ 0.50 (γ ≈ 18 tanh(0.334) ≈ 5.8): D′ fails by a factor of about 6 in β_A, where C's
linearised curvature window (β_A < 0.29–0.39) failed by about 1.5. D′ is worst-case; that is its price for needing no torus
argument. Larger L₁ moves β_A down (how fast is not known here). This is a direct, cheap evaluation for r3-blocked's fit: compute
`∑_{i≠z} tanh(S_iz/2)` (and its weighted form with the fitted rectangles/chairs as tails) from the fitted blocked action.

## 10. The α pointer

D′ for a Wilson-form effective action at L₁ puts the hand-over at `α* = 1/(c π artanh(1/(6(d−1))))`: SU(2) `α_s > 5.72` (c = 1,
β_std = 1/(πα_s)), U(1) `α > 1.43` (c = 4). The only constants are the lattice count `6(d−1)` and `artanh`; no natural α appears.
α enters D′ only through the oscillation of the effective factors, i.e. through how far the running has carried α_s by L₁:
consistent with the round-2 reading (switch-on where α_s is of order one, here of order 5 in worst-case form). Light's α = 1/137
never reaches 1.43 (no running): the photon never satisfies D′, the same fact as §8.

## 11. Lean

| file | content |
|---|---|
| `Attempts/R3/TailDecay.lean` | `GDSw`, `oscBound_avg_w`, `cov_le_weighted_w`, **`theoremA_w`** (Theorem A, weighted Dobrushin, no finite range) |
| `Attempts/R3/FlatFactors.lean` | `factorsAt`, `pairFactors`, `nbhd`, `Potential`, `gibbsMeasure`, `siteSpec`, `factorSpec` (BlockSpec, DLR), `siteSpec_eq_gibbs`, **`influence_site`**, **`specDist_site`**, `siteSpec_isLocal`, `PairOsc`, `FlatCriterion`, `FlatCriterionW`, `gds_of_flat`, `pairOsc_of_osc`, `tanh_le_tanh`, `tanh_le_two_mul`, `tanh_half_le_one_sub_ratio_sq`, **`flat_of_count`** |
| `Attempts/R3/Robust.lean` | `pairOsc_of_close`, `flatW_of_close`, `decay_of_flatW`, `FactorGeometry(.uniform)`, `LocalConvergence`, `LimitFlat`, **`effectiveConvergence_of_local`**, **`limitGDS_of_flat`**, **`gap_of_localFactors`**, `LocalConvergenceW`, `LimitFlatW`, **`levelFlat_of_local`**, **`gap_of_localFactorsW`**, **`gap_of_localFactorsW_fine`**, `limit_decay`, **`continuum_decay`** |

Not formal: lemma T (D's; route A takes its conclusion as the hypothesis `hconv`), H1-fine (§6), the chessboard version (§7), the
unit-test arguments (§8), the numbers of §§1, 9, 10.

**Incident (honesty).** I first kept the build script in the session scratchpad (`build.sh`); a sibling attempt wrote a script
with the same name there, pointing at `~/formal-att-r3-2`. At least one of my builds (Robust, first try; probably also the second
FlatFactors build) therefore ran in `~/formal-att-r3-2`, possibly concurrently with that attempt's own builds. No source file was
changed by it (the sync copies the shared Windows tree), but that folder's build cache was touched, and if my script was written
after theirs, their early builds may have run in `~/formal-att-r3-1`. All final builds and the axiom check ran in
`~/formal-att-r3-1` with the scripts in this folder.

## 12. The single most promising next step

Evaluate Crossover-D′ on data: when r3-blocked's fit of the blocked SU(2) action exists, compute the D′ sum (and D′_λ with the
fitted non-plaquette terms as tails) at several L₁√σ and find where it drops below 1. That turns the last non-perturbative piece
into one number per scale with a proven theorem behind it. On the proof side, the matching target is the RG statement that the
limit theory blocked beyond that scale stays in the Dobrushin class, i.e. that D′, once reached, is preserved by further blocking
(a strong-coupling RG statement, classical in spirit, and the natural place for the non-abelian input).

## References (ideas only)

- Dobrushin, Theory Probab. Appl. 13 (1968) 197; 15 (1970) 458 (uniqueness condition, single-site influence).
- Dobrushin, Pechersky (1983); Gross, Commun. Math. Phys. 68 (1979) 9 (weighted, exponential-decay forms; recalled).
- Georgii, *Gibbs Measures and Phase Transitions* (1988), ch. 8 (Dobrushin's theorem; recalled).
- van Enter, Fernandez, Sokal, J. Stat. Phys. 72 (1993) 879 (renormalisation-group pathologies, non-Gibbsian blocked measures).
- Froehlich, Israel, Lieb, Simon, Commun. Math. Phys. 62 (1978) 1 (chessboard estimates).
- Guth, Phys. Rev. D 21 (1980) 2291; Froehlich, Spencer, Commun. Math. Phys. 83 (1982) 411 (Coulomb phase of 4D U(1); recalled).
- Chatterjee, Commun. Math. Phys. (2021), arXiv:2006.16229 (decay under arbitrary boundary conditions + centre ⇒ confinement).
- Round 2: B (`../r2-coupling/NOTE.md`, S, S′, chessboard), C (`../r2-curvature/NOTE.md`, the stand-in), D
  (`../r2-stepscaling/NOTE.md`, W_p, lemma T); round 3: r3-dmp (`gated_rp`).
