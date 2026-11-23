# ScaleHyp kit: `ScaleHyp` from explicit box densities, in Lean (2026-11-23)

Implements the generic pieces planned in `../m1-tools/PACK-SCALEHYP.md`: (a) the maximal coupling, (b) as a kernel, (c) total variation
from a density ratio, (d) box laws from a joint density, (e) counting on the torus, and the assembly into
`ScaleHyp.ofBlockBounds` (`formal/ProofPhase/M1/UVTVInfluence.lean`).

## Result in plain words

* `ScaleHyp μ μ' β` is now produced from a scale kernel given by explicit box densities (`BoxDensities.scaleHyp`, and
  on the torus `BoxDensities.scaleHyp_torus`).
* The only analytic inputs left as named hypotheses are:
  * the density-ratio bound `hratio` (Balaban: H3's analyticity bound for good boxes, Lemma C's collar decay for
    composite boxes);
  * on the torus, the size `c ≤ ε` and the range `R` of the ratio constants `c`.
* Everything else is proved: the block couplings as measurable Markov kernels, their marginals, the DLR property of
  the box laws, locality, `hunion`, and the counting `hcount` on the torus.
* `nonempty_scaleHyp_torus_product` checks that all hypotheses can be met at once, for the independent product law.
* 106 declarations; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` for each. No `sorry`, no
  `native_decide`, no axiom declarations, no warnings (`axioms.log`).

## Files

| file | content | lines |
|---|---|---|
| `formal/ProofPhase/ScaleHyp/MaxCoupling.lean` | (a), (c): `maxCoupling`, marginals, mass off the diagonal, TV from a density ratio | 187 |
| `formal/ProofPhase/ScaleHyp/KernelCoupling.lean` | (b): `mapParam`, `maxCouplingKernel` as a Markov kernel | 136 |
| `formal/ProofPhase/ScaleHyp/BoxLaw.lean` | (d): `glue`, `IsSplit`, `condDens`, `boxLaw` with locality and DLR | 249 |
| `formal/ProofPhase/ScaleHyp/Counting.lean` | (e): generic `hcount_of_range`; torus distance, box family, `torus_hcount` | 229 |
| `formal/ProofPhase/ScaleHyp/ScaleInst.lean` | assembly: `BoxDensities`, `Q`, `spec`, `scaleHyp`, `scaleHyp_torus`, sanity check | 347 |
| `axioms.sh`, `axioms.log` | build, warnings per file, `#print axioms` of all 106 declarations, grep | |

Namespace `ProofPhase.ScaleHypKit`. Imports: Mathlib; `Counting` imports `OneBox/CouplingDS` (for `coverage`);
`ScaleInst` imports `M1/UVTVInfluence`. No existing module was edited.

## What is proved (main signatures, simplified)

### (a), (c) `MaxCoupling.lean`

For a measure `Λ` on `α` and densities `ρ, ρ'`:

* `overlap Λ ρ ρ' = ∫ min ρ ρ' dΛ`; `excess ρ ρ' = ρ - min ρ ρ'`.
* `maxCoupling Λ ρ ρ' = ((min ρ ρ') Λ).map diag + (1 - overlap)⁻¹ • ((excess ρ ρ') Λ).prod ((excess ρ' ρ) Λ)`.
  * No case split: when the overlap is `1` the product part is `0` and `⊤ • 0 = 0`.
* With `ρ, ρ'` measurable, `∫ ρ = ∫ ρ' = 1` and `Λ` s-finite:
  * `maxCoupling_map_fst : (maxCoupling Λ ρ ρ').map Prod.fst = Λ.withDensity ρ`, and `maxCoupling_map_snd`;
  * `isProbabilityMeasure_maxCoupling`;
  * `maxCoupling_apply_le : MeasurableSet D → (∀ a, (a, a) ∉ D) → maxCoupling Λ ρ ρ' D ≤ 1 - overlap Λ ρ ρ'`.
* `le_overlap_of_ratio : c ≤ 1 → (∀ᵐ a ∂Λ, c * ρ a ≤ ρ' a) → c ≤ overlap Λ ρ ρ'`.
* `maxCoupling_real_le_of_ratio : 0 ≤ δ → (∀ᵐ a ∂Λ, ofReal (exp (-δ)) * ρ a ≤ ρ' a) → (maxCoupling Λ ρ ρ').real D ≤ δ`
  (for `D` measurable, off the diagonal); in fact `≤ 1 - e^{-δ}`.

### (b) `KernelCoupling.lean`

* `mapParam K g = (Kernel.id ×ₖ K).map (uncurry g)`; `mapParam_apply : mapParam K g x = (K x).map (g x)`;
  `isMarkovKernel_mapParam`.
* `measurable_maxCoupling`: for `ρ, ρ' : X → α → ℝ≥0∞` jointly measurable with `∫ ρ x = ∫ ρ' x = 1` for all `x`,
  `x ↦ maxCoupling Λ (ρ x) (ρ' x)` is measurable.
  * The proof writes both pieces through `Kernel.const`, `Kernel.withDensity`, `Kernel.map`, `×ₖ`.
  * The density kernels have mass `≤ 1`, so they are finite kernels and no finiteness of the densities is needed.
* `maxCouplingKernel Λ ρ ρ' : Kernel X (α × α)`, with `maxCouplingKernel_apply` (pointwise `maxCoupling`) and
  `isMarkovKernel_maxCouplingKernel`.

### (d) `BoxLaw.lean`

Configurations `ι → S`, block `B : Finset ι`, global law `μ = F Λ₀`.

* `glue B η σ` (`η` on `B`, `σ` off `B`).
* `IsSplit Λ Λ₀ B := (Λ.prod Λ₀).map (fun p => glue B p.1 p.2) = Λ₀`: the reference splits along the block with block
  reference `Λ` (see pitfall 3 below).
  * `lintegral_split`: `∫ G dΛ₀ = ∫ (∫ G (glue B a c) dΛ(a)) dΛ₀(c)`.
  * `isSplit_pi`: `Measure.pi ν` splits along every block (`ν i` probability measures).
* `boxZ Λ F B σ = ∫ F (glue B η σ) dΛ(η)`.
* `condDens Λ F B σ η = F (glue B η σ) / boxZ σ`, and the fixed density `1` where `boxZ σ ∈ {0, ∞}`.
  * `lintegral_condDens`: a probability density for every `σ`.
  * `measurable_condDens`: jointly measurable.
* `boxLaw Λ F B : Kernel (ι → S) (ι → S)`, `σ ↦ (Λ.withDensity (condDens σ)).map (glue B · σ)`:
  * `isMarkovKernel_boxLaw`;
  * `boxLaw_local`: `x ∉ B → ∀ᵐ ξ ∂(boxLaw Λ F B σ), ξ x = σ x` (needs `[MeasurableEq S]`);
  * **`boxLaw_dlr`**: `∫ F dΛ₀ = 1 → IsSplit Λ Λ₀ B → (Λ₀.withDensity F).bind (boxLaw Λ F B) = Λ₀.withDensity F`.
    The fallback density matters only on a `μ`-null set: `boxZ = ∞` is `Λ₀`-null since `∫ boxZ dΛ₀ = 1`, and where
    `boxZ = 0` the integrand vanishes.

### (e) `Counting.lean`

* `hcount_of_range`: if `0 ≤ w ≤ W₀`, `|B b| ≤ V`, `w b z ≠ 0` implies `d(z, y) ≤ D` for all `y ∈ B b`, and
  `#{b | w b z ≠ 0} ≤ A c(z)`, then `hcount` holds with `M = A V W₀ e^{λ D}`.
* Torus `Torus d N = Fin d → ZMod N` (`[NeZero N]`), `tdist x y = Σ_i |valMinAbs (x_i - y_i)|` (lattice distance):
  `tdist_self`, `tdist_triangle`.
* Box family `boxes ℓ b = b + K`, `K = offsets d N ℓ = {0, ..., ℓ - 1}^d`:
  * `coverage_boxes : coverage (boxes ℓ) z = |K|`;
  * `card_boxes`;
  * `tdist_boxes_le` (diameter `≤ d ℓ`);
  * `card_ball_le` (`|ball z R| ≤ (2R + 1)^d`);
  * `card_near_le` (`≤ (2R + 1)^d |K|` boxes come within `R` of `z`).
* `torus_hcount`: `hcount` for `w = nearW ℓ R` (`1` if the box comes within `R` of `z`, else `0`) with
  `M = (2R + 1)^d |K| e^{λ (R + d ℓ)}`.

### Assembly `ScaleInst.lean`

* `BoxDensities ι S β`:
  * `Λ₀, Λ₀'`, `F, F'` (measurable, `∫ F dΛ₀ = ∫ F' dΛ₀' = 1`);
  * blocks `B`, good blocks `good`;
  * block references `Λ b, Λ' b` (probability measures) with `IsSplit (Λ b) Λ₀ (B b)`, `IsSplit (Λ' b) Λ₀' (B b)`;
  * `same : ∀ b ∈ good, Λ' b = Λ b`.
* `μ = F Λ₀`, `μ' = F' Λ₀'`, `q b = boxLaw (Λ b) F (B b)`, `q' b = boxLaw (Λ' b) F' (B b)`.
* `Q b`: on good blocks `goodQ` (the maximal coupling of the two conditional densities against `Λ b`, glued to the two
  boundary configurations); on source blocks `srcQ`, the product `q b σ ⊗ q' b σ'`. Markov; `Q_fst`, `Q_snd` hold at
  every pair.
* `spec`: the `CouplingSpec μ μ' β`, given supports `Ω₀, Ω₀'` that are measurable, of full measure and kept by the box
  laws (`Ω₀ = Ω₀' = univ` always works).
* `delta c b σ σ' = Σ_{z ∉ B b} 1{σ_z ≠ σ'_z} c b z`.
* `Q_differOn_le`: on a good block, the ratio bound
  `∀ᵐ η, e^{-δ} condDens (Λ b) F (B b) σ η ≤ condDens (Λ b) F' (B b) σ' η` gives
  `(Q b (σ, σ')).real (differOn (B b)) ≤ δ`. This is `hunion` with `κ = c`.
* **`scaleHyp`**: `ScaleHyp μ μ' β` from the supports, a distance, `c, w`, `λ`, `ε, M, c_min` with `ε M < 1`, and the
  named hypotheses:
  * `hratio` (the ratio bound above, on good blocks, for in-support pairs);
  * `hsmall : c b z ≤ ε w b z`;
  * `hcount`.
  
  `scaleHyp_γ`: `γ = ε M`.
* **`scaleHyp_torus`**: on `Torus d N` with `B = boxes ℓ` (`0 < ℓ`), `dist = tdist`, `w = nearW ℓ R`,
  `c_min = |K|`, `M = (2R + 1)^d |K| e^{λ (R + d ℓ)}`. The named hypotheses are `hratio`, `c ≤ ε`,
  `c b z = 0` when every site of the box is farther than `R` from `z`, and `ε M < 1`.
* `ofProduct`, `nonempty_scaleHyp_torus_product`: product references; for the law with density `1`, `scaleHyp_torus`
  applies with `c = 0`, `ε = 0`, `Ω₀ = univ`.

## Choices and deviations from the pack

* **Folder.** New files are under `formal/ProofPhase/ScaleHyp/` (coordinator's rule), not `M1/` as the pack's section
  6 says. The module names drop the `UVTV` prefix.
* **Pitfall 2 (one site space, whole sites).** Kept: blocks are `Finset`s of whole sites and the box law resamples
  every coordinate of its sites (`glue`).
* **Pitfall 3 (fibre reference).** Neither a product reference nor an explicit fibre parametrisation. The box law needs
  only that the global reference splits along the block (`IsSplit`). This holds for the fibre and gauge-slice reference
  of `UV-TV.md` 39.4 when the block is a union of whole `L`-blocks, since the fibre constraints are per `L`-block. That
  is a paper statement; `isSplit_pi` proves the product case. The two copies may have different global references
  `Λ₀, Λ₀'` (the coarse data differ on source blocks) and must share the block reference on good blocks (`same`).
* **(c) constant.** One-sided: only `e^{-δ} ρ ≤ ρ'` is used, and the bound is `1 - e^{-δ} ≤ δ`, sharper than the
  pack's `e^{δ} - 1`.
* **(a) `π(differ) = TV`.** Only the upper bound `≤ 1 - overlap` is proved (for measurable sets off the diagonal); it is
  all `hunion` needs. Equality (optimality) is not needed and not proved.
* **Source blocks** use the product coupling, as in `UV-TV.md` 38.5 (3). Their coupling never enters `ScaleHyp`'s
  influence bound.
* **Supports** `Ω₀, Ω₀'` are parameters with three hypotheses (measurable, full measure, kept by the box laws). With
  `univ`, the hypotheses are trivial but `hratio` must then hold for all boundary pairs, including degenerate ones
  where the fallback density is used.

## What is open

* **Paper, by design (named hypotheses):**
  * `hratio`: the density-ratio constants `c b z` and `ε` (H3's analyticity / Cauchy estimates with 29.5's Pinsker
    step; Lemma C's collar decay 29.2-29.4);
  * the identification of the real scale-`j` kernel given a pattern pair with `F Λ₀`, its box conditional densities and
    characteristic functions (29.1, 33.4);
  * that the fibre and gauge-slice reference splits along each block (`IsSplit`, 39.4), and the choice of supports.
* **The block-size factor.** A single maximal coupling bounds the whole block's disagreement by TV, so the influence
  does not decay inside the block. On the torus this puts `|K| = ℓ^d` into `M`, so `ε` must beat
  `(2R + 1)^d ℓ^d e^{λ (R + d ℓ)}`. This is the caveat of the pack's section 4. If the column condition needs decay
  inside blocks, the next piece is the nested version (a'): Goldstein's far-to-near coupling, a finite composition of
  maximal couplings along a chain of coordinate groups.
* **Sharper counting.** `card_near_le` uses `(2R + 1)^d |K|`; the sharp count of translates within `R` is about
  `(ℓ + 2R)^d`, which would make `A` of order `1` for `ℓ ≫ R`.
* **Composite boxes** `W(K)` with multiplicity `n_W` fit `hcount_of_range` (constant `A`), but their geometry depends on
  the cluster configuration and is not formalised; `scaleHyp` takes `hcount` as a hypothesis for that reason.

## How to check

```
wsl -d ym-replay -u ym -- bash -l /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/scalehyp/axioms.sh
```

It needs `~/formal-sh` with a Mathlib `.lake` (`mkdir -p ~/formal-sh && cp -a ~/formal/.lake ~/formal-sh/`); delete the
folder afterwards. The build folder of this session was deleted.
