# V1 under excision, checked against `[15]` section by section (m1-tools, 2026-11-22)

Brief: T3 of `TRAP-CHECKS.md`: the constrained minimiser of the conditional step when trapped holes are excised: the
block-average constraint is on the **filled** field, while the action is the true Wilson action with the hole's content
frozen. Check `[15]`'s proof of Theorem 1 and Proposition 9 against this change, section by section. Read for this note:
`[15]` pp. 277-309 (all of Sections A-G; pp. 293-302 for the first time). Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **The adaptation goes through, with two inputs from Balaban's earlier papers used in a mildly modified form.** Every
   estimate of `[15]` is local; the excision changes the problem only near the hole, by a term whose first derivative is
   small (`O(ε)`) and whose second derivative is bounded and local, and by an analytic change of the constraint map that
   is a finite-rank local modification of Balaban's linear averaging. Each of `[15]`'s inputs holds with changed
   constants (section 2).
2. **The two points not re-derived here:** (i) gauge fixing with the gauge also fixed at the hole's boundary sites (the
   frozen content breaks gauge invariance there): the gauge theory of `[6]` Sect. D with a few more fixed sites; (ii)
   the propagator bounds `[15]` (46), from `[5]` Theorem 3.13, for the locally modified constraint operator: a local,
   finite-rank perturbation of a positive operator with exponentially decaying inverse. Both are the same type of
   statement as in the source, for a slightly larger prescribed set or a local perturbation; neither is a new kind of
   estimate. `[5]` and `[6]` were not re-read.
3. **Positivity, the one place where a sign could go wrong, is fine:** the functional actually minimised is the true
   action as a function of the non-hole bonds, a sum of plaquette terms that are all regular (a plaquette touching the hole
   is regular, otherwise its bonds would belong to the hole), so its Hessian is non-negative up to `O(ε)`, and the
   constrained Poincaré bound (`POINCARE.md`) gives the lower bound.
4. **Status of T3:** checked against every section of `[15]`; the two inputs above are used without re-reading their
   sources. Row T3 changes from "routine, not checked" to "checked against `[15]`, two cited inputs in modified form".

## 1. The modified problem

Variables: the bonds `U` of `Ω_0` outside the hole `H`. Frozen: the hole's content `h`. Filling: `F(U)`, the least-action
content of `H` given `U` (`TRAP-CHECKS.md` T1; analytic in `U`). Filled field `Ũ = U ∪ F(U)`. Minimise
`A_H(U) = A(U ∪ h)` subject to `Q_j(Ũ) = V` on `Λ_j` (`[15]` (3)).

Bookkeeping: `A_H(U) = A(Ũ) + δA(U)`, `δA(U) = A(U ∪ h) - A(U ∪ F(U)) ≥ 0` (`F(U)` minimises over the hole content).
By the envelope theorem `∇δA(U) = Σ_{p ∈ ∂H} [∂_U a_p(U, h) - ∂_U a_p(U, F(U))]`, a sum over the plaquettes with bonds
in both `U` and `H`: each term is `O(ε)` (regular plaquettes: their gradients are `O(sin angle) = O(ε)`), and the sum is
supported within distance 1 of `∂H`.

## 2. Section by section

| `[15]` | what it uses | with excision | status |
|---|---|---|---|
| Setting (1)-(7), Theorem 1 | nested domains, regularity (2) of configurations, (7) of the data | domains as in `S6-START.md` 2; the filled field is regular (T1, T4); the data `V` are averages of the filled field | holds |
| A (11)-(21), Prop 2 | from the `(k-1)` solution build `U_0`; gauge fixing by `u` with `ū^j = 1` on `Λ_j` (axial on `𝔅_k`, Landau), one-to-one correspondence of critical orbits | `A_H` is invariant only under gauge transformations that are 1 on the sites of `∂H` (the frozen content does not transform); fix `u = 1` there in addition | **input (i)**: `[6]` Sect. D with a few more fixed sites |
| B (22)-(40) | `A(e^{iηA}U_0) = A(U_0) + ⟨A, J⟩ + ½⟨A, ΔA⟩ + V_0(A)`; `|J| < C_1 B_3 ε_1 (L^jη)^{-3}` (28); bounds (31)-(40) on `V_0` | the filled field's expansion has the same form in the variables `(A, dF·A + O(A²))`; `δA` adds `⟨A, J_δ⟩ + ½⟨A, Δ_δ A⟩ + V_δ` with `|J_δ| = O(ε)` on bonds near `∂H` (section 1), `Δ_δ` bounded and local, `V_δ` with the bounds (31)-(40) (plaquette-wise) | holds with changed constants |
| C (44)-(73), Prop 3 | constraint `Q_j(ηA) = L^jη Q_j A + C_j(L^jηA)`, `|C_j| ≤ C_2 (L^jη)²|A|²` (44); operator `H` with `Q H B = B`, `RD*HB = 0`, bounds (46) from `[5]`; contraction for `D(A')` (49)-(57); decay of its derivative (73) | constraint `Q̃(A) = Q(η A ⊕ η F_1(A))`, analytic, linear part `Q̃_1 = Q ∘ (𝟙 ⊕ dF)`, remainder bounded as (44) (`F` analytic with bounded derivatives, T1); `H̃` = Balaban's `H` plus a local finite-rank correction (Woodbury), so (46) with a changed `B_0`; the contraction (52)-(57) and the decay (73) use only (44), (46) | (44) holds; (46): **input (ii)** |
| D (74)-(98), Prop 4 | functional `𝔉(A')` and the bounds of its higher-order part (85)-(97) | the extra terms from `δA` are local, analytic, with `O(ε)` first derivatives: (85)-(97) hold with changed constants | holds |
| E (99)-(121), Props 5-6 | equation (111) `A_1 + 𝔊J + 𝔊(δV/δA')(A_1 + H_1 B) = 0`, `𝔊` from `G_1 = (Δ_1 + DRD* + aQ*Q)^{-1}` ([5] Thm 3.13); contraction (116)-(121) | `G̃_1` for the modified positive operator (positive: section 0.3 and `POINCARE.md`; local perturbation, same decay by the resolvent identity); the contraction conditions (118), (121) with changed constants | holds given (ii) |
| Prop 7 (122)-(142) | critical point is the minimum; gauge conditions; second differential positive | as A (gauge fixed at `∂H` sites too); second differential positive (0.3) | holds given (i) |
| F (144)-(169), Prop 8 | local regularity on cubes, via `[6]` Thm 2 and the axial gauge on cubes | cubes away from the hole unchanged; cubes meeting the hole: the filled field is regular there (T1, T4) and the same argument applies with `F` analytic | holds |
| G (170)-(190), Prop 9 | analyticity in the data; decay of the derivative (190); `⟨δA', J⟩ = 0` on the constrained tangent space | same equations (175)/(180) with the modified operators; analytic in `V` (and in nothing else: `h` is real and frozen) | holds given (ii) |

## 3. Effect

* T3 (`TRAP-CHECKS.md`): checked against `[15]`; inputs (i), (ii) cited in modified form.
* V1 (`S6-START.md`): holds with excision under the same two inputs.
