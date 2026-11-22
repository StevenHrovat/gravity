# S1: the one-step induction for the current main line (m1-tools, 2026-11-22)

Brief (REVIEW-3 H3, REVIEW-2 follow-up G1): write the induction itself, not a table of deltas:
* the order of constants;
* `Form_k` with its bounds, including the window before release;
* the step operation by operation, with the E-row for irregular coarse plaquettes created by random swallowed bonds
  and by fillings.

Supersedes `S1-CURRENT.md` (outline), `S1-PROOF.md` and `S1-ROWS.md` (trapping design). Claim marks as in `NOTE.md`.
Balaban's parts are cited by equation, not re-proved. Every change to them is stated with its proof or reference.

## 0. Result in plain words

* **The theorem.** For `g_0 ≤ γ0(L)` and every `k ≤ K`, the law `ρ_k` of the block state `(V_k, τ'_k)` has the form
  `Form_k` of section 2, with constants independent of `k`, the volume and the spacing. The laws half is Lean
  (`Assembly.lean`); the form half is the induction below.
* **What it rests on:**
  * Balaban's [III]-[V] and [12]-[16], cited by equation (citation);
  * the M1 notes (paper);
  * four sketch-level points, listed in section 5.
* **External:** [I] Theorem 2 with its rate.
* **Status: paper**, with citation-level inputs and the four sketch points named. The induction is now written,
  operation by operation, with its constants; it is no longer an outline.

## 1. Constants, in the order they are fixed

| # | constant | fixed by | condition it must satisfy | used in |
|---|---|---|---|---|
| 1 | `d = 4`, `SU(2)`, `b = 0.0929` | the model | `16 b = 1.49 > 1` | label count |
| 2 | `L` (odd) | absolute | `θ = 5^d L^{1−d} + C(r0 + L² ε) < 1`; `L ≥ 13` gives `0.284` | R1 |
| 3 | `ℓ_max = C_1 L`, `λ = 8(ℓ_max + 2)`, `C_tw` | `L` | `C_1 L ≥ C L + 1` (localised cores finish) | H5 |
| 4 | `r0 = c/L⁴` (excision threshold) | `L`, `C_1`, `C_tw` | `c ≤ c'/(256 C_tw C_1^4)`: data deviation `C_tw r0 λ²` below the Dirichlet gap `c'/(4 C_1² L²)`, and E7.J's `‖E‖ ≤ ½` (`REVIEW3-RESPONSE.md` 11.7) | R3, E7.J |
| 5 | `M`, `α_0`, `α_1`, `κ`, `B`, `A`, `C_0` | Balaban, given `L` | his conditions ([III] Sect. 2, [V] Sect. 1); `κ` beats polymer entropy; `κ ≥ 4 log L + log C` (one-box contraction tails, `REVIEW3-RESPONSE.md` 13.1); UV-TV subcriticality per `M R_j`-cube: `C 200^d e^{−c κ/2} < ½` (`UV-TV.md` 24.1, 26.5; `κ` large is a citation, [I] Theorem 3, at the cost `M ≥ M(κ)` and a smaller `γ`) | all E-rows |
| 6 | `p(g)`, `p0(g) = A0 (log g^{-2})^p`, `R_j ≥ (log g_j^{-2})^r` with `r ≥ 2`, `n0`, `q0` | Balaban, given 5 | `A_1² p0² ≳ M^d L^{d+1} R^{d+2}` (his, after (1.82); doubled constant (P0) for the UV-TV slack, `UV-TV.md` 26.3); `p0 ≥ C(κ + M^d) 100^d R^d` (P1, insurance); `q0 ≥ p0` (analyticity domain contains the small-field set, `UV-TV.md` 33.6); UV-TV box side `ℓ_B ≥ C (log p/m)^{2d+1}/γ_DS²` with `γ_DS < 1` the Dobrushin-Shlosman contraction constant, not the coupling bound `γ` (`UV-TV.md` 22.3, 27.8); `p0 ≫ log g^{-2}` (carrying); `R_j ≥ n_loc ≈ 0.4 log g^{-2}` (R2); `p0` growing faster than `log(k − j)` (R8); Balaban's fixed-domain threshold `ε_* ≤ L^{−4}/(2C)` (one-box contraction, `REVIEW3-RESPONSE.md` 12.2) | E5-E9, R2, R8, labels |
| 7 | `β_min` | absolute (`d` only) | Peierls sum and R7′: `(2 C_d)(C β^{3/2} e^{−β})^{1/4} < 1` | decoder fidelity, label count |
| 8 | `γ0(L)` (bare coupling bound) | 2-7 | `4/γ0² ≥ β_min`; `δ = p0²/β ≤ δ_*` with `16 b(1 − δ_*) > 1`; `δ_k ≤ c` (label carrying); `r0²/(8 g_k²) ≥ C(C_1) (n0 + R_k) p(g)² + p(g_k)²` (E-row 7c below, every scale of a region's life); [I] Theorem 2's `γ ≤ γ0(L)` | everything; UV-TV: the condition of `UV-TV.md` 23.3 is superseded by the `κ` condition of row 5 (24.1) |
| 9 | window `≈ (3/4) log g^{-2}/log L` | 6, 8 | `≤ R_j` | thick-born sheets (`BYPASS.md` 1) |
| 10 | `L_*` (stopping scale, physical), `K` | 8 | `g_K` small enough for 5-8 at scale `K` | hand-over |
| 11 | `t_0(n, R/ℓ)` and `C(n, R/ℓ, L_*/ℓ)` | 1-10 and the observable | `|t| ≤ t_0` keeps `tF` within the E-term bounds | R10 only |

**No circularity:**
* `ℓ_max`, `C_tw` depend on `L` only, and `r0` on `L`, `C_1`, `C_tw`;
* Balaban's constants depend on `L`;
* `β_min` is absolute;
* `γ0` is chosen last among the model constants;
* `t_0` is per observable and enters nothing else.

The enlargement cost of large-field regions by decoder components (`p0 (M R_0)^4 = polylog`) is `≪ β_0`, which is
condition 8.

## 2. `Form_k`

**State and law.**
* The state is `(V_k, τ'_k)`: an SO(3) field on scale-`k` bonds and a closed Z2 cochain on scale-`k` plaquettes.
* `ρ_k` is its density under `ym ⊗ Haar^{noise}`. It is the true law (Lean: `map_resample_eq`, `m1_laws`;
  `Interface/RandBlocking.lean`), so `∫ ρ_k dν_k = 1`.

**Representation.**
`ρ_k(V, τ') = Σ_H Σ_{𝓛 ∼_H τ'} (Π_{X ∈ 𝓛} a_{ℓ_X} e^{L_{ℓ_X}(V)}) · T_k(Z_k^H)[ χ_H · Π_{unreleased} 1_ℓ · exp(A_k^H(V, U_k(V))) ]`.
* `H` runs over Balaban's admissible domain histories `(Ω_j, Λ_j, Z_j)_{j ≤ k}` ([III] (2.1)-(2.17)).
* `𝓛` runs over **hard-core families** of released labelled components whose parent remainder still persists at
  scale `k` (`j(S) ≥ k`, `REVIEW3-RESPONSE.md` 12.1), pairwise disjoint and non-adjacent **at their release scale**
  (afterwards their factors simply multiply: two labels released far apart may later share a coarse cube), each
  with its pattern. `𝓛 ∼_H τ'` means that, together with the unreleased label patterns inside `T`, they produce `τ'`.
* The sum over `𝓛` is a hard-core polymer sum, not a product over coarse bonds. The per-bond parity formula is only an
  upper bound (REVIEW-2 second follow-up, NIT).
* Every term is non-negative for real `V` (used in `REVIEW3-RESPONSE.md` 7).

**The items and their bounds.**
* **(F1) Domains.** Balaban's, plus three additions:
  * at scale 0, every cube containing a bare flip is in `P_0`, in every term (N-1);
  * the decoder components lie inside `Z_0` (`REVIEW3-RESPONSE.md` 5);
  * excision envelopes lie inside large-field regions: a hole contains a plaquette at angle `≥ r0 ≫ ε_k`.
* **(F2) Small field.** At scale 0, SU(2)-regular (`|U_p − 1| ≤ ε_0`, so `τ = +1`). At `k ≥ 1`, SO(3)-regular ([III]
  (2.17) with the SO(3) distance).
* **(F3) Background.** `U_k(V)`, the minimiser of [15] for SO(3) backgrounds, regular on small-field domains (V1, V2;
  R9). No holes in small-field domains.
* **(F4) `T_k`.** Balaban's positive operations ([III] (2.19)-(2.22), [V] (1.71)). Inside a large-field region they
  also integrate:
  * hole contents (no constraint reads them, `FILL.md`);
  * the Haar noise on swallowed coarse bonds (density 1, `SKETCH-STEPS.md` 1);
  * **the window form**: each unreleased label pattern, as an indicator `1_ℓ` of the decoder's output on that region's
    variables (`REVIEW3-RESPONSE.md` 4.2, 5).
* **(F5) Action.** `A_k = ` E-terms + R-terms + B-terms + vacuum and normalisation constants, with the analyticity
  domains and bounds of [III] (2.23)-(2.42):
  * E-terms `O(1) e^{−κ d_k(X)}`;
  * R-terms `e^{−p0(g_j)} e^{−κ d_j(X)}` ([V] (1.100));
  * B-terms (1.99).

  Released large fields (deep SO(3) structures, acts, monopole loops, halos) are R-terms, with dimension-4 field
  dependence (R8).
* **(F6) Label factors** (`REVIEW3-RESPONSE.md` 11). Each released labelled component `X` (with `δ_k |X| ≤ ε_*`)
  contributes `a_ℓ e^{L_ℓ(V)}`:
  * `a_ℓ > 0` is a constant with `a_ℓ ≤ (C β^{3/2} e^{−(1−δ)β})^{f(ℓ)} e^{−2p0} e^{−κ d(X)} e^{O(δ_X)}`, with `f(ℓ)`
    bare flips;
  * `L_ℓ` is an indexed local term: analytic on Balaban's domain, gauge invariant, `L_ℓ(flat) = 0`, no linear coupling,
    localised with decay;
  * `|L_ℓ| ≤ C δ_X (ε_k + g_k)² L^{−4(k − k_r)}/α_1²` on the fluctuation domain at scale `k`, with `k_r` its release
    scale.

  Components with `δ_k |X| > ε_*` are still carried inside `T` (sketch, 11.4).
* **(F7) Symmetries.** Gauge invariance of every term. Covariance as in [III] (2.29), (2.32), except for the fixed
  tie-breaks (decoder, lexicographic) and the scale-0 grid, which act only on large-field terms.

## 3. The step `k → k + 1`

Each operation lists what it maps, the rows it uses, and its level.

| # | operation | input → output | rows, references | level |
|---|---|---|---|---|
| S0 | **(bare only)** split `U ↦ (Ad U, τ)`; decoder per flip-cube component; `τ'_0` | Wilson density → `Form_0` (Wilson action; flips in `P_0`) | `ROUTE-B.md` 1; `CLOSING.md`; `REVIEW3-RESPONSE.md` 1, 5; [III] (2.18) at `k = 0` | paper |
| S1 | preparatory operations: localisation, domains | `Form_k` → Balaban's intermediate form | [IV] (1.10)-(1.99), carried over (R9) | citation |
| S2 | excision: envelopes (test loops `≤ λ`, cap `ℓ_max`), filling = implicit-function critical point, swallowed bonds randomised | inside large-field regions only | `FILL.md`; `REVIEW3-RESPONSE.md` 2; `SKETCH-STEPS.md` 1 | paper; "cap reached ⇒ irregular `W`" sketch |
| S3 | gauge fixing, block-axial | | X2: `lintegral_gauge_leaf` (Lean) + paper | Lean + paper |
| S4 | conditional step on small-field domains | exact | `map_resample_eq` (Lean); X1.H1 `fibre_rep_of_map_le` (Lean); X1.H2 (`S6-START.md` 3) | Lean + paper |
| S5 | background and regularity | | V1, V2: [15] carried over to SO(3) (R9) | citation |
| S6 | linear term, quadratic form, denominator, localisation | small-field action at `k + 1` | E1, E2 (`S6-START.md`); E3 (`E3.md`, `POINCARE.md`; counting Lean); E4 citation | paper + citation |
| S7 | large-field regions: normalisations, analytic extension, factors, fibre mass, entropy | `T` bounds | see 3.1 | paper + citation |
| S8 | dilution and regularity of what is carried | | R1 (`OFFCENTRE.md`, `OffCentre.lean`); R2 (`R2-REPAIR.md`, `Footprint.lean`) | paper + Lean |
| S9 | release (R-operation): decompositions of unity, Mayer expansion, exponentiation | `T` of released regions → R-, B-terms; labels extracted | [V] (1.70)-(1.104); labels `REVIEW3-RESPONSE.md` 4.2 | citation + paper |
| S10 | label factors carried: one-box contraction `N_{k+1} ≤ θ N_k` (`θ = C L^{−4}`), constant into `a_ℓ`; a label whose parent stops persisting (`k = j(S)`) is summed out into R-terms | `a_ℓ e^{L_ℓ}` → `a'_ℓ e^{L'_ℓ}` | `REVIEW3-RESPONSE.md` 12, 11.3; R8 | paper on citation-level adaptations; components above `ε_*` sketch |
| S11 | final form at `k + 1` | → `Form_{k+1}` | section 4 | paper |

### 3.1 S7 in detail: the E-rows of large-field regions

* **7a. Normalisations and analytic extension:** E5, E6 as [V] (1.70)-(1.75). Fillings are analytic in their data
  (implicit-function critical point), so the extension passes through them.
* **7b. Large-field factor, ordinary coarse plaquettes** (all four blocks free of holes):
  * [16] (71) in four dimensions (R12, `CLOSE-OUT.md` 1): action in the four blocks `≥ p(g)²/8`;
  * bare flips: action `≥ β` each (N-1). A part `p0²` of it goes to the scale-0 factor, the rest to the label count.
* **7c. Large-field factor, coarse plaquettes whose blocks meet a hole (new; REVIEW-3 H3.3).** This covers the coarse
  plaquettes containing a randomised swallowed bond, and those whose average passes through a filled region.
  * For these, (71) does not apply to the true configuration: the coarse value is a random Haar value, or an average
    of the filled field.
  * **Attribution:** every hole bond lies within `ℓ_max` layers of the deep set `H_0` (section 2 of `FILL.md`, with the
    cap), so a deep plaquette `p` lies within distance `ℓ_max + 1` of the blocks of each such coarse plaquette. Each deep
    plaquette is charged by at most `C(C_1) := 6 (2 C_1 + 5)^d` coarse plaquettes.
  * **The deep plaquette's action:** `|V_k(∂p) − 1| ≥ r0` gives, by (71) at scale `k`, action `≥ r0²/(8 g_k²)` in its
    blocks. If the finer field in those blocks is itself irregular, the action is taken at the earliest scale at which
    the structure was regular: R2's attribution (`R2-REPAIR.md`).
  * **Every scale of the region's life** (REVIEW-3 follow-up 2). Irregularity created by Haar noise or by a filling
    (curvature between `ε` and `r0`) can persist at later scales of the same region, where (71) again does not apply.
    Those factors are attributed to the same deep set. At most `n0 + R_k` scales are involved, so `n0 + R_k` times as
    many attributed coarse plaquettes.
  * **Budget:** condition 8 of section 1, `r0²/(8 g_k²) ≥ C(C_1)(n0 + R_k) p(g)² + p(g_k)²`. It holds for
    `g_k ≤ γ0(L)`, since `r0² = c²/L^8` is fixed and `(n0 + R_k) p²` is polylog. So the deep plaquette pays its own
    scale-`k` factor and a factor `e^{−p²}` for each attributed coarse plaquette at every scale of the region's life.
  * **Not double-counted:** the true configuration's action inside the hole is used, not the filled field's. The
    filled field's action is never used for a factor.
* **7d. Fibre mass (E7, E7.J).**
  * Only at regular `W` (`FILL.md` 0.2): ordinary coarse bonds by `E7J.md` 2, with owned bonds outside the Dirichlet
    data (`REVIEW3-RESPONSE.md` 2.4), and slicing (`map_prod_le_of_slices`, Lean).
  * Swallowed bonds: fibre density 1 (Haar noise).
* **7e. Entropy (E8).**
  * [V] (1.80)-(1.81), with `K ≤ n0 − j + R_j` and `n0` the shrinking time (`R10-SCOPE.md` 1). The decoder
    enlargement costs `≤ p0 (M R_0)^d` per component, paid by its flips (`β ≫ p0 (M R_0)^d`, condition 8).
  * Labelled components above `ε_*` (S10), and the long-lived regions of R2, need the footprint-weighted lifetime
    beyond Balaban's `n0 − j + R_j` (**sketch**, `REVIEW3-RESPONSE.md` 11.4).
* **7f. Fundamental inequality and corollaries (E9):** [V] (1.89), and (2.50) of [III] via Corollary 3, unchanged.

### 3.2 S9 and S10, labels

Labels in `Form_k` are a hard-core polymer sum (F6). Before the Mayer expansion of (1.72), each first-class
component's operation splits by label pattern,
`T = Σ_ℓ T^ℓ`. For `ℓ ≠ 0`, `T^ℓ = Φ_ℓ T̂^ℓ`.
* The expansion with normalised `T̂^ℓ` on fixed domains is Balaban's (1.103) expansion.
* The polymers meeting a labelled domain become boundary terms attached to it.
* (P1)-(P3) follow from (1.73)-(1.75) with `F = 1_ℓ`, from (1.89), and from the flips' action.

After release a label is `a_ℓ e^{L_ℓ}` (`REVIEW3-RESPONSE.md` 11.1), with no hard core towards other polymers. At each
later step the fluctuation integral of `e^{L_ℓ}` returns a constant, which goes into `a_ℓ`, and a new `L_ℓ`. Both are
`O(δ_X (ε + g)² L^{−4(k − k_r)})`, so the total change of `a_ℓ` over the label's life is `e^{O(δ_X)}`, whatever `K`
is (11.2).

## 4. `Form_{k+1}`, item by item

* **(F1)** Balaban's new domains (S1, S9), plus the envelopes created at this step (S2), which lie inside large-field
  regions by 7c.
* **(F2), (F3)** S5 on SO(3)-regular domains.
* **(F4)** Balaban's `T` plus:
  * the conditional step (exact);
  * hole contents and noise integrated;
  * unreleased labels as indicators.
* **(F5)** E- and R-terms from S6 and S9, with the bounds of [III] (2.23)-(2.42) at `k + 1`. Released terms have
  dimension-4 coupling (R8).
* **(F6)** Label factors from S9, carried by S10.
* **(F7)** As stated.
* **Normalisation:** `∫ ρ_{k+1} = 1` (laws, Lean).

**Uniformity:**
* **Volume:** every bound is local (per polymer, per cube).
* **Steps:** the constants of section 1 do not depend on `k`. A label's weight changes by at most `e^{4C ε_*}` over its
  whole life (one-box contraction, `REVIEW3-RESPONSE.md` 12.2). Before a multi-cube component's image is below a
  cube, its steps are marginal, which adds at most a `poly(g^{-1})` factor (13.1). R-terms are summed by R8.
* **Spacing:** `K` steps, with bounds depending on `g_k` only.

## 5. Status

| part | level |
|---|---|
| laws (`ρ_k` is the true law) | **Lean** (`m1_laws`, `m1_assembly_rows_upTo`) |
| S0, S2 (apart from the cap step), S8, S11, 7b-7d, the order of constants | **paper** |
| S1, S5, 7a, 7e (within the lifetime), 7f, S9 (Balaban's parts) | **citation**, with the SO(3) carry-over (R9) |
| S3, S4, S6 | **Lean + paper + citation**, as listed |
| labels: S9 (extraction), S10 | **paper** for components below `ε_*`, on citation-level adaptations (`REVIEW3-RESPONSE.md` 11.6); **sketch** above |

**Sketch-level points:**
1. "Cap reached implies irregular `W`", through `FILL.md` 0.2 (the nonabelian "fractions sum to 1" step).
2. The footprint-weighted lifetime in [V] (1.80)-(1.85): the super-rare tails of R2 and of large labelled components.
3. Two readings of [V] p. 379 to check against the text: whether the first-order bound before (1.73) is per cube or
   per component (per component makes the large-label case empty), and whether `A'` ranges over the real small-field
   deviations (11.1).
4. Labelled components above `ε_*`, carried beyond Balaban's lifetime (11.4).

**External:** [I] Theorem 2 with its rate (0.31). **Outside S1:** R10 (`REVIEW3-RESPONSE.md` 7) and density
(`REVIEW3-RESPONSE.md` 8), which concern the hand-over.
