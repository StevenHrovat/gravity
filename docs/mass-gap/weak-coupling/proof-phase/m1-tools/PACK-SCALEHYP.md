# Content pack: ScaleHyp from Balaban's kernels (m1-tools, 2026-11-23)

This pack is for a fresh session. It assumes nothing from earlier sessions beyond the files named here.

## 1. Where things stand

**Done in Lean** (`formal/ProofPhase/M1/`, standard axioms; `axioms-uvtv.sh`, `axioms-uvtv.log`):

| file | what it gives |
|---|---|
| `OneBox/CouplingDS.lean` | the generic coupling theorem. `CouplingSpec μ μ' β`: the supports `Ω₀`, `Ω₀'`; the blocks `B`; the specifications `q`, `q'` (`q_local`, `q_dlr`, `q_supp`); the block couplings `Q` (Markov kernels, `Q_fst`, `Q_snd`). Then `couplingDS_bound`, `exists_iter_forall_le` |
| `M1/UVTVScale.lean` | `ScaleHyp μ μ' β`: a `CouplingSpec` with `dist`, `good`, the influence matrix `k`, `lam`, `γ`, `cmin`; `influence` (H3 / Lemma C) and `column`. Then `scale_front`: one scale with patterns and truncation |
| `M1/UVTVInfluence.lean` | **`ScaleHyp.ofBlockBounds`**: builds `ScaleHyp` from three separated inputs (below) |

`ScaleHyp.ofBlockBounds` takes:
* `hunion` (**Balaban**). For each good block and in-support boundary pair, the block coupling leaves some site of the
  block disagreeing with probability at most `Σ_{z ∉ B, σ_z ≠ σ'_z} κ b z`.
* `hsmall` (**smallness**): `κ b z ≤ ε · w b z`.
* `hcount` (**counting**): `Σ_{b good, z ∉ B b} Σ_{y ∈ B b} w b z e^{λ d(z, y)} ≤ M · c(z)`.

With `ε M < 1` it returns `ScaleHyp` with `γ = ε M`.

## 2. The exact statement wanted

For every scale `j` and every pattern pair `p` off the truncation set, an instance of the arguments of
`ScaleHyp.ofBlockBounds`, for the scale-`j` kernel `K_j(· | X_{j+1})` given `p`. In the paper (`UV-TV.md`):
* **sites and state:** 38.5 and 39.3;
* **blocks:** good boxes, composite boxes `W(K)`, and source blocks (28.3, 33.1);
* **H3 for good boxes:** 10.2, 19, and the Pinsker step 29.5;
* **Lemma C for composite boxes:** 29;
* **the column condition:** 22.3, with `ℓ_B ≥ C (log p/m)^{2d+1}/γ_DS²`;
* **measurable block couplings:** 33.4 and 39.4, with densities taken against the fibre and gauge-slice reference
  measure.

## 3. What can be Lean, and what stays paper

**Lean (generic, clean, recommended):**

| piece | statement | Mathlib has | Mathlib lacks |
|---|---|---|---|
| (a) maximal coupling | for probability measures `ρλ`, `ρ'λ` with densities against a common `λ`: the coupling `π = push((ρ ∧ ρ')λ, diag) + (ρ - ρ∧ρ')λ ⊗ (ρ' - ρ∧ρ')λ / (1 - ∫ρ∧ρ')`, with marginals `ρλ`, `ρ'λ` and `π(differ) = 1 - ∫ ρ∧ρ' = TV` | `Measure.withDensity`, `Measure.map`, `Measure.prod`, `lintegral` algebra | maximal couplings |
| (b) maximal coupling as a kernel | the same for densities `ρ(σ, y)`, `ρ'(σ', y)` jointly measurable in the parameters: a Markov `Kernel` in `(σ, σ')` (the `Q` field of `CouplingSpec`) | `Kernel.withDensity`, `Kernel.map`, `Kernel.prod`, measurability of parametric lintegrals | the construction |
| (c) TV from a density ratio | `e^{-δ} ρ ≤ ρ' ≤ e^{δ} ρ` implies `TV ≤ e^{δ} - 1`; with `δ = Σ_z 1{σ_z ≠ σ'_z} c_b(z)` this is `hunion` with `κ b z ≈ c_b(z)`, for small `δ` | basic inequalities | packaging |
| (d) box laws from a joint density | `q_b(σ, ·)`, the normalised conditional density on the block given the rest, as a Markov kernel with `q_local`, `q_dlr`, `q_supp` | `Kernel.withDensity`, Fubini | the DLR proof for an explicit density on a finite product |
| (e) counting | `hcount` for `L`-blocks on the torus `(ZMod N)^d` with `d` the lattice distance: `Σ_y e^{λ d(z,y)} ≤ C(λ, ℓ_B)` per block, multiplicity `≤ n_W` | `Finset` sums | lattice geometry lemmas |

**Paper (by design; enter as hypotheses):**
* **the density-ratio estimate itself**, i.e. the constants `c_b(z)` and `ε`:
  * for good boxes, the analyticity of Balaban's effective density in the boundary data (Cauchy estimates; 29.5's
    Pinsker step);
  * for composite boxes, the collar decay `e^{-m' w}` times the constant-size inputs (29.2-29.4);
* the identification of the scale-`j` kernel with Balaban's effective density on the box, with its characteristic
  functions (29.1, 33.4);
* the shell adaptation (34.8) and the SO(3) carry-over (R9), as listed in `UV-TV.md` 37.2.

## 4. Proposed module plan

| module | content | size |
|---|---|---|
| `UVTVMaxCoupling.lean` | (a) and (c): the maximal coupling of two densities, its marginals, `π(differ) = TV`, and TV from the density ratio | 200-300 lines |
| `UVTVKernelCoupling.lean` | (b): the parametric version as a Markov kernel; `CouplingSpec.Q` from densities | 250-400 lines |
| `UVTVBoxLaw.lean` | (d): box specifications from a joint density on a finite product of standard Borel spaces, with `q_local`, `q_dlr`, `q_supp` | 300-450 lines |
| `UVTVCounting.lean` | (e): `hcount` for the torus box family | 150-250 lines |
| `UVTVScaleInst.lean` | assembles `ScaleHyp.ofBlockBounds` from (a)-(e), with the density-ratio constants (paper) as named hypotheses | 100-200 lines |

**Order:** (a), (c), (b), (d), (e), then the assembly. (b) and (d) are the hard parts: kernels and measurability. (a),
(c) and (e) are routine.

**Caveat on the far-to-near coupling.** H3 uses Goldstein's nested maximal coupling (far-to-near, along the tail
σ-algebras). A single maximal coupling, as in (a), bounds the whole block's disagreement by TV, so `k b y z` does not
decay inside the block. That is what `ScaleHyp.ofBlockBounds` uses, and it is enough when `hcount` holds with the
block-size factor `|B b|` absorbed into `M` (`ℓ_B` fixed per scale). If the column condition needs the decay inside
blocks, add a nested version (a'): a finite composition of (a) along a chain of coordinate groups.

## 5. Known pitfalls (Lean)

1. **`MeasurableSpace` binders become local instances.** With `(m : MeasurableSpace Ω)` in scope, `Measurable`,
   `AEStronglyMeasurable`, `Integrable` and instance arguments of lemmas pick `m`.
   * Fixes: write `AEStronglyMeasurable[m0]`; put the binder last; or use a family `ℕ → MeasurableSpace Ω`.
   * Block laws live on the same product space as the global configuration, so this matters here too.
2. **`CouplingSpec` uses one site space `S`** with `[MeasurableEq S]`. Bundle a site's bonds, labels and noise into one
   `S` (38.5). Blocks are sets of whole sites, and the update resamples **all** variables of its sites (39.3).
   Otherwise (I) fails for bonds that leave the block.
3. **Densities against the fibre reference** (39.4). The box variables live on the fibre of the coarse data in the
   block-axial gauge slice, so `q_b` is not absolutely continuous with respect to product Haar. In Lean, either
   parametrise the fibre explicitly (then the reference is a pushforward), or state (b) for an abstract reference
   measure `λ_b(X_{j+1})` that is the same in both copies on good blocks.
4. **`Pi` forms** from `Integrable.add`/`.sub` (use `simp only [Pi.add_apply]` on the integral equations, then
   `linarith`). `Π` is a reserved token. Deprecated names: `Measure.finset_sum_apply` → `finsetSum_apply`; `dif_pos` →
   `simp only [h, dite_true]`.
5. **`gcongr` on nested sums** may descend too far. Use `Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun y _ => ?_`.

## 6. Rules for the session

* New Lean files only, under `formal/ProofPhase/M1/`.
* Standard axioms only; no `sorry`, no `native_decide`.
* Build in the WSL distro `ym-replay` in a private `~/<folder>` with a copied Mathlib `.lake` (`axioms-uvtv.sh` shows the
  pattern), and delete the folder at the end.
* No commits, branches or stash. Keep the scrub clean.

## 7. Done looks like

`UVTVScaleInst` produces `ScaleHyp` for an abstract scale-`j` kernel given by explicit box densities on a torus,
with only the following as named hypotheses:
* the density-ratio constants (Balaban: H3's analyticity bound, Lemma C's collar decay);
* the identification of the real kernel with those densities;

and `#print axioms` shows standard axioms only.
