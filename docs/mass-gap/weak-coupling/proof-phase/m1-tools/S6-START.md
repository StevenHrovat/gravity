# §6 start: the constrained minimiser from `[15]` (m1-tools, 2026-11-22)

Brief: begin §6 of the paper outline (`M1-PLAN.md`): the step under the block constraint, starting with row V1 (the
constrained minimiser `V̂_Λ(W, V_out)` that centres the reference kernel and gives `D(W) > 0`). Read in full for this
note: `[15]` pp. 277-292 (statement of Theorem 1, Sections A-D) and pp. 303-309 (Proposition 8; Section G,
analyticity, Proposition 9). Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **V1 reduces to `[15]` Theorem 1 as it stands.** The conditional step needs the least-action fine configuration with:
   the old core frozen, the next block field `W` (scale `k+1`) prescribed on the resampling domain, and the current field
   (scale `k`) prescribed outside it. At first sight this is not of `[15]`'s form, because the coarse region `Λ` surrounds
   the finer shells around the core. But `[15]` only needs the domains to be **nested as sets**, `Ω_0 ⊃ Ω_1 ⊃ … ⊃ Ω_{k+1}`
   with scale-`j` data on `Ω_j \ Ω_{j+1}` and a distance condition between `Ω_j^c` and `Ω_{j+1}`. With the core as the
   frozen hole of `P2-PRIME.md` and its funnel of fixed-width shells, the conditional step's data are exactly of that
   form (section 2). So `[15]` gives existence, uniqueness of the minimal orbit, the regularity bounds `[15]` (9)-(10), and
   analyticity in the data with decay of its derivative (`[15]` Proposition 9, (190); stated for a general `𝔅_k`).
2. **Consequences:** `D(W) > 0` for regular `W` (row X1.H2: the constrained minimiser is in the fibre and in the support
   of the reference kernel), the background `U_0(W)` with Balaban's bounds (row V2), and the linear-term identity `J_0 =
   Q*λ` (row E1: the minimiser satisfies `⟨δA', J⟩ = 0` for all `δA'` with `Q(U_k) δA' = 0`, `[15]` (170), (178), so
   the gradient on `Λ` is a pure constraint term).
3. **What `[15]` does not give and §6 must still do:** the bounds of [V] (1.2)-(1.11) for the ratio `N/D` (denominator,
   cancellation of the Wilson terms, positivity of the constrained quadratic form, E2-E3), the normalisations (E5), the
   analytic extension (E6), the large-field factors under δ-constraints (E7), the entropy induction with the retuned
   exponents (E8), and the fundamental inequality (E9). These are the routine rows; their order is in section 4.

## 1. What `[15]` proves and how (pp. 277-292)

* **Setting (pp. 277-279).** Nested domains `Ω_0 ⊃ Ω_1 ⊃ … ⊃ Ω_k`, `Ω_j` a union of big blocks of size `M_1 L^j η`, with
  (1) `(L^j η)^{-1} dist(Ω_j^c, Ω_{j+1}) > R M_1`, `R ≥ R_1` fixed. Determining set `𝔅_k = ∪_j Λ_j`, `Λ_j = Ω_j^{(j)} \
  Ω_{j+1}^{(j)}`; data `V` with `Ū^j = V` on `Λ_j`; regular configurations `𝔘_k({Ω_j}, ε_0)` ((2): plaquettes and
  covariant derivatives small at each scale on `Ω_j`); `V` regular on `𝔅_k` ((7)).
* **Theorem 1 (p. 279).** For `ε_1 ≤ a_1` there is a minimal orbit of the Wilson action in `𝔘_k({Ω_j}, B_3 ε_1) ∩
  𝔙_k(𝔅_k, V)`; it is the unique critical orbit if `B_3 ε_1 ≤ ε_0 ≤ a_0`; local regularity (9)-(10) on cubes of size
  `2 M L^j η`; constants depend on `d, L` only (and `M`, `B_4` on the indicated parameters). Analyticity in `V` and
  expansions: "simple consequences of the proof", deferred to the last section.
* **Proof structure.** Induction on `k`. A (pp. 279-281): from the `(k-1)` solution build `U_0` close to the minimiser;
  gauge-fix (axial on `𝔅_k`, Landau `R D* A = 0`), Proposition 2: critical orbits correspond one-to-one to critical
  points of `A(U_1 U_0)` on the space (19)-(21). B (pp. 281-285): expansion `A(e^{iηA} U_0) = A(U_0) + ⟨A, J⟩ +
  ½⟨A, Δ A⟩ + V_0(A)` with `|J| ≤ C_1 B_3 ε_1 (L^jη)^{-3}` and bounds on the cubic and quartic parts. C (pp. 285-289):
  a linearising change of variables `A = A' - H D(A')` that makes the constraints linear (`L^jη Q_j A' = B` on `Λ_j`),
  by a contraction (Proposition 3), with exponential decay of its derivative ((73)). D (pp. 289-292): the critical-point
  equation on the tangent space `Q δA' = 0, R D* δA' = 0` ((82)-(83)), with the derivative of the higher-order terms
  bounded (Proposition 4). Sections E-F (not read here): existence and uniqueness by a further contraction, local
  regularity (completed p. 305, Proposition 8, read). G (pp. 305-309, read): `U_k(V'V_0)` is analytic in `G^c`-valued
  small `V'` on `𝔅_k`, extends to orbits, with functional derivative bounded and decaying exponentially ((190)); the
  minimiser satisfies `⟨δA', J⟩ = 0` for `Q(U_k) δA' = 0` ((170), (178)) (Proposition 9).
* **What matters for M1:** every estimate is local (exponential decay on the scale of each shell) and the only global
  structure used is the nesting of the domains and condition (1). Nothing requires the coarse domains to be
  geometrically "inside" in any other sense.

## 2. The conditional step's data are of `[15]`'s form (paper)

Data of the conditional step at scale `k` for a renormalisable component `X` with core `C`
(`../c6f-m1scope/ONE-STEP.md` 2.1, `P2-PRIME.md` 1):
* the frozen hole `H` (the non-regular part of the core, fixed fine data);
* the funnel: shells `F_j` around `H` of width `R_1 M_1` in scale-`j` units, `j = h, …, k`, with scale-`j` data;
* `Λ' = Λ \ (H ∪ funnel)`, with scale-`(k+1)` data `W` (the next block field, fixed in the conditional step);
* outside `Λ`: scale-`k` data (`V_out`), and further out Balaban's usual multi-scale determining set of the region `Z`.

Set `Ω_{k+1} = Λ'`; `Ω_k = Λ' ∪ F_k ∪ (outside Λ)`; `Ω_j = Ω_{j+1} ∪ F_j` for `h ≤ j < k`; `Ω_h^c = H`. Then
`Ω_h ⊃ … ⊃ Ω_k ⊃ Ω_{k+1}` (by construction), `Λ_j = Ω_j \ Ω_{j+1} = F_j` for `h ≤ j < k`, `Λ_k = F_k ∪ (outside Λ)`,
`Λ_{k+1} = Λ'`. Condition (1): `Ω_j^c = H ∪ F_h ∪ … ∪ F_{j-1}` and `Ω_{j+1} ⊃ F_{j+1} ∪ Λ'`; their distance is the width of
`F_j`, `R_1 M_1` scale-`j` units, as required (and for `j = k` the width of `F_k`; the outside region is in `Λ_k`, not in
`Ω_k^c`). The blocks: `Λ'` must be a union of big blocks `M_1 L^{k+1} η`; the funnel at scale `k` has size of order
`R_1 M_1 L^k η`, inside one or a few big blocks of scale `k+1` if `R_1 ≤ L` (else remove the big blocks it meets from
`Λ'`). Regularity (2), (7): `W` regular (branch (b)), the corrected field regular on the shells after `n_mod` steps of
Lemma D-mod, `V_out` regular (`χ_{k,Λ}`, [IV] (1.75)).

The constrained minimisation of `ONE-STEP.md` ("least `A(U_{k,Z}(V_k))` over `V_k|_Λ` with `V̄_k = W`") is the
minimisation of the fine action under these data, because minimising first over the fine field for fixed `V_k` and
then over `V_k|_Λ` with `M(V_k) = W` is the same as minimising over the fine field with its `(k+1)`-fold average equal to
`W` on `Λ'` (nested constraints). Hence **`[15]` Theorem 1 gives V1**: existence and uniqueness of the minimal orbit
`V̂_Λ(W, V_out)`, the bounds (9)-(10), and analyticity in `(W, V_out)` (Proposition 9, stated for a general
determining set).

**Status:** paper (reduction to `[15]` Theorem 1 and Proposition 9, which are cited; both are stated for general nested
domains and a general determining set, which is all the reduction uses).

## 3. Immediate consequences

* **X1.H2 (`0 < D(W) < ∞`):** the minimiser lies in the fibre `{V̄_k = W}` and, by (9)-(10), in the support of the
  small-field reference kernel centred at it; `D(W)` is a Gaussian-type integral over a neighbourhood of positive
  measure. (Paper; the quantitative lower bound is E3.)
* **E1 (linear term):** `[15]` Section D finds critical points on the tangent space `Q δA' = 0`; so at the constrained
  minimiser the action's gradient on `Λ'` is orthogonal to `ker Q_{k+1}`, i.e. `J_0 = Q*_{k+1} λ` for a multiplier `λ`.
  Every configuration of the fibre integral satisfies the same constraint, so `⟨J_0, δA⟩ = ⟨λ, Q δA⟩ = 0` on the fibre:
  the linear term vanishes **exactly**, as in Balaban's unconstrained case, with no core contribution (the core is the
  frozen hole, outside the variables). This replaces the estimate planned in E1 by an identity.
* **E2 (positivity on `ker Q`):** the constrained quadratic form is the restriction of Balaban's positive form to a
  subspace, so its lower bound is at least his ([V] (1.7)-(1.9)).

## 4. Order for the rest of §6

1. E3: the denominator `D(W)` for the constrained kernel (Gaussian integral on `ker Q_{k+1}`; its `W`-dependence through
   `U_0(W)`, analytic by V1), and the cancellation of the Wilson terms between `N` and `D` ([V] (1.2)-(1.11), (1.30)-(1.37)).
2. E5, E6: matched normalisations and the analytic extension ([V] (1.70)-(1.75)).
3. E7-E9: large-field factors under δ-constraints, the entropy induction with the exponents of `D-N.md` 1, the
   fundamental inequality.
4. V2 and the localisation (E4) by citation, checking that `W` enters only through `U_0(W)`.
