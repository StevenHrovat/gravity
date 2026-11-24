# Content pack: OSData for the real measures (m1-tools, 2026-11-23)

This pack is for a fresh session. It assumes nothing from earlier sessions beyond the files named here.

## 1. Where things stand

**Done in Lean** (`formal/ProofPhase/M1/`, standard axioms, no `sorry`; `axioms-uvtv.sh`, `axioms-uvtv.log`):

| file | what it gives |
|---|---|
| `UVTVInterface.lean` | `os_cross_le`: the OS norm of `F - E[F|𝓗]` is at most (B) + 2(A). `OSData` (the former named hypothesis). `gap_of_UVTV` |
| `UVTVOS.lean` | **`OSData` discharged from abstract reflection-positive data.** `RPData V`: a bilinear form `Q` (symmetric, positive semidefinite) and a step `τ` (symmetric, `Q u (τu) ≥ 0`, bounded orbits). From it: `RPData.H` (completion of the pre-Hilbert space), `Φ`, `osData` with `‖Φu‖² = Q u u`, `contraction` (`Q(τu,τu) ≤ Q(u,u)`, the OS argument), the transfer operator `T` (symmetric `T_symm`, positive `T_pos`, `T_Φ`), the block closure `H0` (closed, `T`-invariant when `τ` preserves the block observables: `T_mem_H0`). Headline: `RPData.gap_of_RP`, stated purely in `Q`, `τ` |
| `UVTVReflect.lean` | `condExp_comp_of_measurePreserving` (`E[F|𝓗] ∘ θ = E[F∘θ | θ⁻¹𝓗]`, not in Mathlib). `os_split_reflection`: the reflection step in `Q(F - f_ℓ)`. `RPMeasure μ`: a measure with a reflection `θ`, a shift `s` (`s θ s = θ`), a positive-time class `Pos`, and the two reflection-positivity hypotheses `rp`, `rp_half`. `RPMeasure.toRPData` builds `RPData` from it. Headline: `RPMeasure.gap_of_measure`: `∫ F(θω) F(sⁿω) dμ ≤ e^{-mn} ∫ F(θω) F(ω) dμ`, from the block gap plus UV-TV's (A) and (B) bounds |

**What is left:** an `RPMeasure` for the measures that M1's theorem is about, and the bridge to `MassGapLoc`.

## 2. The exact statement wanted

Produce, for the Tuning `T` of the main theorem, the hypotheses of `RPMeasure.gap_of_measure` (or a finite-volume
variant, section 4), and conclude `MassGapLoc T` (`formal/ProofPhase/Objects.lean:478`).

`MassGapLoc` asks for **limit points** of the finite-volume correlations `T.wcorr k j (O.F k j) (T.steps k τ)`, first
`j → ∞` (volume) and then `k → ∞` (spacing), with `|g| ≤ 2 e^{-mτ}` uniformly in `s, R` and the slab family `O`.
It does **not** ask for an infinite-volume measure. That choice matters for the route.

## 3. What the repository and Mathlib have

**Repository:**
* `Positivity/Wilson.lean`: `wilson_rp` (site reflection), `wilson_rp_symm`, `wilson_rp_cs`, `wilson_rp_gram`, and
  `PosObs` (bounded measurable observables of the positive half). These are on the periodic lattice.
* `Positivity/LinkWilson.lean`: `wilson_rp_link` (link reflection, through the plane between two time slices; SU(2):
  `wilson_rp_link_SU2`). This is the property `rp_half` needs: `∫ u(θω) u(sω) ≥ 0` is the link-reflection positivity
  of `u ∘ s`.
* `Positivity/Reflection.lean`: `thetaConn`, `isReflection_thetaConn`.
* `Interface/SpectralUpgrade.lean`: `spectral_upgrade`, `logconvex_ratio` (used by `RPData.contraction`).

**Mathlib** (v4.34 baseline):
* `PreInnerProductSpace.Core`, `InnerProductSpace.Core.toSeminormedAddCommGroup`, `InnerProductSpace.ofCore`;
* `UniformSpace.Completion` with its `InnerProductSpace` instance and `Completion.inner_coe`;
* `toComplₗᵢ`, `toComplL`, `ContinuousLinearMap.extend` and `extend_eq`, `Completion.induction_on(₂)`.
* No OS reconstruction, no transfer matrices, no maximal couplings, and no conditional expectation under maps (now in
  `UVTVReflect`).

## 4. The obstacle, and two routes

**Obstacle.** On the periodic lattice, the shift does not preserve positive-time observables: `u ∘ s` leaves the
positive half near `t = N/2`. So `RPMeasure.pos_shift` fails on a torus, and `RPData.bdd` (all `k`) has no meaning
there.

**Route A (finite volume, recommended): a windowed `RPData`.**
* Keep the torus of time period `N`. Take observables supported in `0 ≤ t ≤ W` and allow only `k ≤ K` steps, with
  `W + K ≤ N/2`.
* Redo `contraction` with a finite horizon. Log-convexity gives `a_1/a_0 ≤ (a_K/a_0)^{1/(K-1)} ≤ (C/a_0)^{1/(K-1)}`,
  so the transfer is a contraction up to a factor `(C/a_0)^{1/(K-1)} → 1` as `N → ∞`.
* Run the spectral-upgrade step with this approximate rate. The finite-volume decay bound then has an error that
  vanishes as `N → ∞` at fixed `τ`.
* Pass to `MassGapLoc`'s limit points. It needs only bounds uniform in the volume, and the error term goes to `0`.
* This uses the repository's torus reflection positivity directly. No infinite-volume measure is needed.

**Route B (infinite time): an infinite-volume measure.**
* Construct a cluster point of the tori as `N → ∞` (or of the full sequence), as a measure on infinite-time
  configurations.
* Show `rp`, `rp_half`, shift invariance and `s θ s = θ` for the limit. Reflection positivity passes to weak limits
  for continuous cylinder observables, then to bounded measurable ones by a monotone-class argument.
* Then `RPMeasure.gap_of_measure` applies as it stands.
* Heavier: it needs the existence of the limit and the extension step.

## 5. Proposed module plan (Route A)

| module | content | size |
|---|---|---|
| `UVTVWindow.lean` | `RPDataWin V K`: `RPData` with `bdd` and `τ`-closure only up to `K` steps. Approximate contraction `Q(τu,τu) ≤ (C/Q(u,u))^{1/(K-1)} Q(u,u)`. Approximate spectral upgrade with the extra factor | 250-350 lines |
| `UVTVTorus.lean` | The Wilson torus measure as `RPDataWin`. `V` is the bounded measurable functions of the links in `0 ≤ t ≤ W` (adapt `PosObs`); `Q u v = ∫ (u ∘ thetaConn) v`; `τ` the shift by one time step; `symm`, `pos` from `wilson_rp_symm`/`wilson_rp`; `τ_pos` from `wilson_rp_link` applied to `u ∘ s` | 300-500 lines |
| `UVTVGapLoc.lean` | From the finite-volume decay with vanishing error, through `IsLimitPoint`, to `MassGapLoc T`. Needs the slab observables `SlabObs` and `T.wcorr` from `Objects.lean` | 200-300 lines |

## 6. Remaining modelling points (each a small lemma or a hypothesis)

* **Block invariance.** `T_mem_H0` needs `τ(Blk) ⊆ Blk`. Block observables on a fixed block grid are invariant only
  under shifts by a whole block length. Either use `s` = the shift by one block (decay at multiples of the block
  length, which is enough for `MassGapLoc` at fixed physical `τ`), or let `Blk` be the span of all translates.
* **Mean zero.** The block-gap hypothesis `hdec` is for truncated (mean-zero) block observables. Put `Blk` inside
  the mean-zero subspace.
* **Approximants are a.e. objects.** `gap_of_measure` takes `hfE : (f k : Ω → ℝ) = μ[F|𝓗 k]` pointwise, with
  `f k ∈ Obs` bounded everywhere. A conditional expectation is bounded only a.e. Restate `hfE` as an a.e. equality
  (`Q` only sees a.e. classes; a 20-line change in `UVTVReflect`), or choose a bounded version.
* **The σ-algebras.** `𝓗_k ≤ 𝓕_k` and `θ⁻¹𝓗_k ≤ 𝓕_k`: the block state near `supp F` and near `θ supp F` both lie in
  the full block state. Positive-time: `𝓗_k` is generated by positive-time variables, so `f k ∈ Pos`.

## 7. Known pitfalls (Lean)

1. **A `MeasurableSpace` binder becomes a local instance.** Inside a declaration with `(m : MeasurableSpace Ω)` in
   scope, `Measurable`, `AEStronglyMeasurable`, `Integrable` and lemmas with instance arguments silently use `m`.
   * Symptoms: "synthesized type class instance is not definitionally equal", or a hypothesis of the wrong
     σ-algebra.
   * Fixes: write `AEStronglyMeasurable[m0]` (scoped notation, `open MeasureTheory`); put the sub-σ-algebra binder
     last; or take a family `𝓗 : ℕ → MeasurableSpace Ω` and use `𝓗 k`, which is not a local instance. The last is
     the most robust (`UVTVReflect`).
2. **Type synonyms with transported instances** (`RPData.Pre := V`). `rw` and `change` on terms mixing `V` and the
   synonym fail with "not type-correct at implicit transparency". Prove the statement on `V` first and use it by
   `exact` (`Q_smul_left`, `core`). Use `R.toPre` to give a term the synonym's type; a type ascription is not enough.
3. **`integral_add` and `Pi` forms.** `Integrable.add` and `Integrable.sub` produce `f + g` in `Pi` form. Use
   `have := integral_add ...; simp only [Pi.add_apply] at this`, then `linarith`, instead of `rw`.
4. **`Π` is reserved.** Do not use it as a variable name.
5. **Renamed or deprecated lemmas** at this baseline:
   * `Measure.finset_sum_apply` → `finsetSum_apply`;
   * `ae_bdd_condExp_of_ae_bdd` → `ae_bdd_abs_condExp_of_ae_bdd_abs`;
   * `ContinuousLinearMap.mul_apply` is deprecated (use `pow_succ'` then `show T (... ) = _`);
   * `dif_pos`/`dif_neg` → `simp only [h, dite_true]`;
   * `setIntegral_map`'s implicit names are `g` (the map) and `f` (the integrand).
6. **`rw [← hθ.map_eq]` rewrites every `μ`.** State the `setIntegral_map` instance with `(μ := μ)`, then rewrite
   `map_eq` inside it.

## 8. Rules for the session

* New Lean files only, under `formal/ProofPhase/M1/`.
* Standard axioms only; no `sorry`, no `native_decide`.
* Build in the WSL distro `ym-replay` in a private `~/<folder>` with a copied Mathlib `.lake` (see `axioms-uvtv.sh`),
  and delete the folder at the end.
* No commits, branches or stash; the coordinator commits. Keep the scrub clean.

## 9. Done looks like

* `UVTVTorus` instantiates `RPDataWin` for the Wilson torus measure from the repository's reflection-positivity
  theorems.
* `UVTVGapLoc` proves `MassGapLoc T` from:
  * the block-level gap;
  * UV-TV's (A) and (B) bounds (`statementB`, module 2);
  * the instantiation duties of `PACK-SCALEHYP.md`, as named hypotheses.
* `#print axioms` shows standard axioms only.
