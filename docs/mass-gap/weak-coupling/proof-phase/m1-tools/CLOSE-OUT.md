# Close-out of the open items: [16] in 4D, R8, R10, R7, R9 (m1-tools, 2026-11-22)

Brief (coordinator, items 3-6): re-derive [16] (69)-(71) in four dimensions from [12] (50), (53); R8, released terms
and labels couple to SO(3) only at dimension 4, summably; R10, the `L_*` half of the ultraviolet transfer; R7 and R9,
the citations and exactly where SO(3) instead of SU(2) changes a statement. Read for this note: [12] pp. 24-26 ((44)-(54),
local PDF), [16] pp. 272-274, [III] pp. 259-260, `[13]` Theorems 3.10-3.13. Claim marks as in `NOTE.md`.

## 1. [16] (69)-(71) in four dimensions (paper, written out)

**Statement.** Let `U` be a configuration on the fine lattice whose plaquettes in the four `j`-blocks `Δ'` around a
coarse plaquette `p'` satisfy `|U(∂p) - 1| ≤ α L^{-2j}` (the regularity [16] (68), [12] (52)), and let `V_j` be its
`j`-fold block field. Then in `d = 4`, for any `δ ∈ (0, 1]`,
`|V_j(∂p') - 1|² ≤ (1 + δ) Σ_{p ∈ Δ'} |U(∂p) - 1|² + C_δ α⁴`.
Hence, if `|V_j(∂p') - 1| ≥ g p(g)` and `α ≤ c g p(g)`, the Wilson action of `U` in `Δ'` is at least
`(1/(4 g²)) Σ_{p ∈ Δ'} |U(∂p) - 1|² ≥ p(g)²/8` (with `|U - 1|²_HS = 4(1 - ½ tr U)` and `β = 4/g²`).
This is [16] (71) in `d = 4`, with constant `1/8` against [16]'s `1/4`; the constant is immaterial.

**Proof.**
1. **Linear identity** ([12] (48)): the linear part of a coarse plaquette is the average, over translates `(p')_x`
   (`x ∈ B(y_0)`, weight `L^{-d}`), of the sum of the fine plaquettes in the translated `L × L` square. Composing `j`
   steps, the weights compose to the uniform weight `L^{-dj}` over `B_j(y_0)`, because the blocks nest.
2. **Nonlinear error:** [12] (49)-(50) per step, `O((L² α_i)²)` with `α_i` the plaquette bound at the `i`-th
   intermediate scale. [12] (53) gives `α_i ≤ 2 L^{2i} α L^{-2j}`, so the sum of the errors is dominated by the last
   step: `O(α²)`. Hence `|V_j(∂p') - 1| ≤ Σ_{x ∈ B_j} L^{-dj} Σ_{p ⊂ (p')_x} |U(∂p) - 1| + C α²` (the `j`-step form of
   [12] (50), which is [16] (69)).
3. **Cauchy-Schwarz:** `(Σ_x L^{-dj} Σ_{p ⊂ (p')_x} a_p)² ≤ (Σ_x L^{-dj} L^{2j})(Σ_x L^{-dj} Σ_{p ⊂ (p')_x} a_p²)`,
   since each translate has `L^{2j}` plaquettes.
4. **Multiplicity:** a fine plaquette `p` lies in `(p')_x` only for `x` with the two transverse coordinates fixed by
   `p` and the two in-plane coordinates in a range of `L^j` each: at most `L^{2j}` translates.
5. **Combine:** `|V_j(∂p') - 1|² ≤ (1 + δ) L^{2j} · L^{-dj} · L^{2j} Σ_{p ∈ Δ'} a_p² + C_δ α⁴`, and
   `L^{(4-d) j} = 1` in `d = 4`. (In `d = 3` the factor `L^{j}` remains, which is why [16] carries `L^{-3j}` explicitly.)
   ∎

**Status:** paper, written out. The 4D form used through [V] (1.76) now rests on this, not on a re-reading.

## 2. R8: released terms and labels couple at dimension 4, summably (paper)

**Lemma (no linear coupling).** Let `f` be a gauge-invariant function, analytic near the flat configuration, of the
SO(3) or SU(2) bond variables in a finite region `X`. Write `V = e^{iA}` near `1`. Then `df|_{A=0} = 0`, and
`|f(e^{iA}) - f(1)| ≤ C_X ‖f‖ Σ_{p ⊂ X} |dA(p)|² + C_X ‖f‖ |A|³`, where `‖f‖` is the sup on the analyticity domain.

*Proof.*
* **Gauge directions:** gauge invariance at `A = 0` gives `df(Dω) = 0`.
* **Global rotations:** invariance under constant gauge rotations gives `df(Ad(u)A) = df(A)` for all `u`. So
  `df = Σ_b ⟨c_b, A_b⟩` with each `c_b` an `Ad`-invariant vector of `su(2) ≅ so(3)`, and there is none, so `c_b = 0`.
* **Second order:** the second derivative vanishes on gauge directions, so it is a quadratic form in `A` modulo gauge.
  On the finite region it is bounded by `C_X Σ |dA(p)|²` (Poincaré: in the best gauge `|A| ≤ C_X |dA|`).
* **Remainder:** Cauchy estimates in the analyticity domain. ∎

**Summability.**
* **Released large fields.** A released term born at scale `j` is one of Balaban's R-terms at scale `j`: activity
  `≤ e^{-p0(g_j)} e^{-κ d_j(X)}` ([V] (1.100); [III] (2.31)), localised on a domain `X` of scale `j`.
* **Its field dependence at scale `k ≥ j`.** The surrounding field is smooth on scale `k`, so its curvature in scale-`j`
  units is `≤ ε_k L^{-2(k-j)}`, and by the lemma the field-dependent part is `≤ C e^{-p0(g_j)} |X_j| ε_k² L^{-4(k-j)}`.
  There are `L^{4(k-j)}` positions per scale-`k` cell, so the total per cell is
  `≤ C ε_k² Σ_j e^{-p0(g_j)}`. This converges, because `p0(g_j)` grows with `k - j` through the running. The
  vacuum parts (`f(1)`) are constants: normalisation.
* **This is Balaban's own mechanism** ([III] p. 260: after vacuum energy renormalisation the R-terms are marginal and
  their sum over scales is controlled). The lemma supplies the reason, the absence of a linear coupling.
* **Labels.** A closed Z2 remainder (`CLOSING.md`) enters the coarse density through a local factor, gauge invariant
  in the SO(3) field near it. By the lemma, its coupling is quadratic in curvature with the same scaling. Labels are
  rare on the 1-skeleton (`CLOSING.md` 2), so their sum per cell converges.

## 3. R10: the `L_*` half of the ultraviolet transfer (paper sketch)

**Statement.** Conditional on the block variables `(V_K, τ_K)` at `L_*`, for gauge-invariant bounded observables
`F, G` of physical extent `≤ R` at physical distance `D`:
* (i) `E[F | V_K, τ_K]` is within `c e^{-m D}` (in `L¹`) of a function of `(V_K, τ_K)` restricted to the physical
  `D/2`-neighbourhood of `supp F`;
* (ii) `|E[F G] - E[E[F | ·] E[G | ·]]| ≤ c e^{-m D}`;

with `m` of order `1/L_*` (physical units), uniformly in the lattice spacing.

*Sketch.*
* **The conditional law** of the fine variables given `(V_K, τ_K)` is the normalised integrand of Balaban's
  `T_K`-representation at fixed top field: the integrals of the fluctuation fields at all scales `j < K` and of the
  large-field regions, with the top field frozen.
* **Balaban's cluster expansions** ([I] Sects. 3-7, [II], [V] (1.90)-(1.99)) write it as a polymer system with
  activities `≤ e^{-κ d_j(X)}` at each scale. These are exactly the bounds of the inductive form (`S1-ROWS.md` 1).
  They give exponential decay of truncated correlations in scale-`j` units for scale-`j`-localised quantities.
* **Scale by scale:** at scale `j` the decay length is about one scale-`j` cell; the slowest is `j = K - 1`, giving
  `m ~ 1/L_*`.
* **(i)** follows from the locality of the polymers: the dependence of `E[F | ·]` on `V_K` far from `supp F` passes
  through chains of polymers of total length `≥ D`.
* **(ii)** is the decoupling of the two conditional expectations, with the same estimate.
* **What is not written out:** the conditional version of the cluster expansion, i.e. Balaban's expansions with the top
  field fixed. His expansions are built that way (R-terms are functions of `V_K`), but the decay estimates for
  conditional expectations of fine observables are not stated in his papers in this form. **Status: paper sketch.**

## 4. R7: the normalisation per real flip (citation, pinned)

`P(τ_p = −1 for p ∈ S) ≤ e^{-β|S|} Z_{−S}/Z`, where `Z_{−S}` omits the plaquettes in `S`. By Jensen,
`Z/Z_{−S} ≥ exp(-β Σ_{p ∈ S} ⟨1 - ½ tr U_p⟩_{−S})`, so `Z_{−S}/Z ≤ C^{|S|}` once `⟨1 - ½ tr U_p⟩_{−S} ≤ c/β`, the
weak-coupling plaquette bound in the measure with `S` removed. This follows from Balaban's two-sided partition-function
bounds for locally modified actions ([16] Theorem 1, with its proof, and [V] p. 380 for `d = 4`), which control `log Z`
up to `O(1)` per site in any finite region. **Citation**, with this reduction written.

## 5. R9: Balaban's papers carried over to the SO(3) layer: where SO(3) changes a statement

| item | SU(2) statement | SO(3) layer | change |
|---|---|---|---|
| small-field regions | plaquettes within `ε` of `1` | plaquettes within `ε` of `1` in SO(3) **and** `τ = +1` (no label) | **yes**: an SU(2) plaquette near `−1` is SO(3)-small but carries a label. With the label, the Tomboulis weight `exp(-(β/2)|tr|)` is a maximum, not a small field (`ROUTE-B.md` 0.4). Small-field domains are therefore defined with `τ = +1` |
| action in small fields | Wilson `β(1 - ½ tr U_p)` | `(β/2) τ_p |tr U_p| = (β/2) tr Û_p` for the lift near `1`, `τ = +1` | none (identical) |
| Haar measure | SU(2) Haar | SO(3) Haar × uniform lift sign; the sign is summed into `τ` | none in small fields (unique lift near `1`) |
| averaging [12], logarithm | log near `1`; cut at `−1` | log near `1`; cut at rotation `π` | none in small fields; deep plaquettes are excised (`FILL.md`) |
| propagators `[13]`, minimiser `[15]` | regular SU(2) backgrounds | regular SO(3) backgrounds lift uniquely to regular SU(2) ones on simply connected neighbourhoods | none (statements transfer through the local isomorphism) |
| coupling constant renormalisation [I] | `b` from `su(2)` | same Lie algebra | none |
| large-field factors [V] (1.76), [16] (71) | `|V(∂p') - 1|` in SU(2) | in SO(3), `|Ad V - 1| ≥ c |V - 1|` near `±1` | constant only; near the SO(3) cut the configuration is excised |
| centre, vortex persistence | `Vortex.lean` applies (centre `±1`) | no centre; does not apply | **yes** (the point of the split): the centre is carried by `τ` |

**Status:** citation-level carry-over with the table above as its content. Two statements change: the definition of
small-field regions (`τ = +1`) and the absence of the centre. Nothing else changes beyond constants.

## 6. Summary

| item | status |
|---|---|
| [16] (69)-(71) in 4D | **paper**, written out |
| R8 | **paper** (lemma + summability; Balaban's R-term bookkeeping for the sum) |
| R10 | **paper sketch** (conditional cluster expansion not written out) |
| R7 | **citation**, reduction written |
| R9 | **citation** carry-over; two statements change (small-field definition with `τ = +1`; no centre) |

**Update (REVIEW-2 G2, N1, G4):**
* R9 table row 1 amended: small field means SO(3)-regular; `τ = +1` is no longer required. Labels enter as explicit polymer factors (`REVIEW2-RESPONSE.md` 2).
* R7 restated as `poly(β)^{|τ|}`, with freed bonds counted (`REVIEW2-RESPONSE.md` 6).
* R10 (section 3) holds only in `L¹`, not pointwise; for block-variable observables at a fixed physical scale (`REVIEW2-RESPONSE.md` 5).

**Update (REVIEW-3 H6, REVIEW-2 follow-up N-1; `REVIEW3-RESPONSE.md` 1, 3):**
* R9 row 1 again: at scale 0, small field means SU(2)-regular (`τ = +1`); from scale 1 on, SO(3)-regular.
* R7 (section 4): the Jensen route fails for general `P`, and `f(P) ≤ |P|/6` is false. It is restated as R7′,
  `Z_{−P}/Z ≤ (C β^{3/2})^{|P|}`: the exponent by a rank count, the ratio by citation.
