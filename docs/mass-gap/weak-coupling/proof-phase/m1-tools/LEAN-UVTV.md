# M1 Lean phase: Lemma UV-TV's logical structure (m1-tools, 2026-11-23)

Four new modules in `formal/ProofPhase/M1/` sit on top of the generic coupling theorem
(`formal/ProofPhase/OneBox/CouplingDS.lean`). Balaban's analytic inputs enter as named hypotheses, as in
`Assembly.lean`.

**Build and check:** `axioms-uvtv.sh` (WSL, private build folder). Result in `axioms-uvtv.log`:
* 52 declarations, each depending only on `propext`, `Classical.choice` and `Quot.sound`;
* no `sorry`, no `native_decide`, no axiom declarations.

No existing module was edited.

## The modules

| module | paper | headline | named hypotheses (where Balaban or the reconstruction enters) |
|---|---|---|---|
| `UVTVScale` | `UV-TV.md` 30.2, 33.1, 34.1 | `scale_front`, `scale_front_integral`: one scale with patterns and truncation. The mixtures over pattern pairs have a coupling with `P(differ on T) ≤ w(E) + Σ_{p ∉ E} w_p |T| (n_src e^{-λa}/((1-γ) c_min) + ε)` when the sources lie at distance `≥ a` from `T`. Also `ScaleHyp.weights` (Corollary 34.1: admissible weights for every centre) and `exists_coupling_pointwise` | `ScaleHyp.influence`, the unweighted influence bound on good blocks (H3 for good boxes, Lemma C for composite boxes); `ScaleHyp.column`, the column condition (22.3); the `CouplingSpec` itself (block specifications and measurable block couplings, 38.5, 39.3-39.4); the pattern weights `w` (H1's coupling); the truncation set `E` |
| `UVTVFront` | 30.3-30.4 | `front_lower`, `front_half`: the recursion `D(k+1) ≥ min(L D k, L^(k+1) D 0) − e k` gives `D k ≥ L^k (D 0 − Σ L^{-(i+1)} e i)`, so the front stays intact under 30.3's condition. `front_advance`, `front_advance_rpow`: `P(differ on B) ≤ P(start fails) + c x^{-r}/(1 − L^{-r})` | `step`: one scale fails with probability `≤ c (L^k x)^{-r}` (module 1, integrated over the coarser scales) |
| `UVTVCov` | 38.1 | `total_cov_ae`: the exact law of total covariance along a decreasing filtration. `total_cov_integral_le`: its `L¹` form. `ccov_integral_le_local`: localisation of one term. `statementB`, `statementB_geom`: `E|ccov(G n) f g| ≤ η₀ + Σ_j (η_j + 2δ_j + 2δ'_j)`, and `≤ η₀ + 5 c x^{-r}/(1 − ρ)` for geometric inputs | `hA`, `hA'`: (A) at each top scale; `hdec`: one-kernel decorrelation (33.3 at scale `j`); `hbase`: the last kernel (38.4) |
| `UVTVInterface` | `REVIEW3-RESPONSE.md` 13.4; `UV-TV.md` 32 | `os_cross_le`: the OS-norm split `|E[(a − E[a|𝓗_a])(b − E[b|𝓗_b])]| ≤ E|ccov 𝓕 a b| + 2 E|E[a|𝓕] − E[a|𝓗_a]|`, which is (B) plus twice (A). `mem_closure_of_os` and `mem_closure_of_tendsto`: OS-norm density gives closure. `gap_of_density` and `gap_of_UVTV`: through `Interface.spectral_upgrade`, every local observable with `Q(F − f_ℓ) ≤ b_B + 2 b_A → 0` has `⟪ΦF, T^n ΦF⟫ ≤ e^{-mn} ‖ΦF‖²` | `OSData`: the OS Hilbert space, the embedding `Φ`, and `‖Φu‖² = Q u`; `T` symmetric and positive; `H0` closed, `T`-invariant, and equal to the closure of the block vectors; block decay at rate `m` |

## What is not formalised

**Instantiation (paper):**
* building `ScaleHyp` from the scale-`j` kernel, with H3 and Lemma C as influence bounds and measurable block couplings
  from explicit densities (38.5, 39.3-39.4);
* the tower measure across scales;
* the Markov identification of `ccov(G (j+1))` with the covariance under `K_j`;
* (A)'s comparison state at each top scale.

**The reconstruction (named, stopped here):**
* `OSData` from the infinite-volume continuum limit: the quotient by null vectors, the completion, and `T` from the time
  translation;
* `T`-invariance of the block closure `H0`;
* the identification `Q(F − f_ℓ) = E[(θF − θf_ℓ)(F − f_ℓ)]`, with `θ` measure preserving and `θ𝓗 ≤ 𝓕_ℓ`.

This is a large development: the OS construction is not in Mathlib.

**Not touched:**
* the block state `(SO(3), closed Z2)` as a concrete type with gauge-invariant observables. The modules work with
  abstract configuration and probability spaces, so they apply to it unchanged.
* `MassGapLoc` itself. `gap_of_UVTV` gives the decay on the OS space, and stating `MassGapLoc` through it needs the
  reconstruction above.
