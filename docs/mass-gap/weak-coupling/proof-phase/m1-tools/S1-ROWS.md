# S1: the inductive form for laws, and the precise statement of every row (m1-tools, 2026-11-22)

Brief: state the inductive form (`Form` of `Assembly.lean`) precisely, and give each field of `M1RowStatements` its
precise statement, pinned to Balaban's equations; flag any row that turns out false or much harder than marked. Read
for this note: [III] Sect. 2 ((2.10)-(2.42), pp. 256-262); earlier reads in `NOTE.md` 1, `E5-E9.md`, `S6-START.md`.
Claim marks as in `NOTE.md`. Lean: `Assembly.lean` (`M1RowHypothesesUpTo`, `m1_assembly_rows_upTo`).

## 0. Result in plain words

1. **The inductive form is Balaban's (2.18) with two additions:** the block field carries a finite set of **records**
   (trapped deep cores: hole, frozen content, root scale, action), and every background is the minimiser **with the
   holes excised**. The bounds are Balaban's ((2.17), (2.25)-(2.42)) plus one bound per record (root once,
   maintenance summed). The law half (the density is the law of block field and records) is separate and proved in
   Lean (`m1_laws`).
2. **No row is false. None is much harder than marked.** Stating them precisely turned up five corrections; none
   changes a status or adds more than a page:
   * **F1 (Lean, fixed now):** the rows hold only while the running coupling is small, i.e. for `k < K` (the stopping
     scale), not for every `k ∈ ℕ`. `M1RowHypotheses` assumed them for all `k`, which is false beyond `K`. Added
     `M1RowHypothesesUpTo K` and `m1_assembly_rows_upTo`: the form for `k ≤ K`, the laws for every `k`.
   * **F2 (new rule):** trapped holes must be separated by `R_sep(d, L)` (current units) for V1 with excision; closer
     holes are merged into one record and carried in the large-field region (`V1-INPUTS.md` 0.3); and "subscale"
     means `ρ_k ≤ 1` (smaller than one scale-`k` spacing; V1 with excision would allow up to `L/4`). Costs nothing.
   * **F3 (precision, P2′ and TRAP):** the maintenance bound must use the hole's capacity (bounded by its covering
     number), not `ρ^{d-2}` (which assumes a ball). With that, holes of **any** size and shape are covered, and the
     restriction `D0 ≤ 100 M R_h` of `TRAP.md` is not needed (section 2, TRAP and P2′).
   * **F4 (precision, P4):** with `r0 ≤ c/L²` (from E7.J) the root suppression is `exp(-c0 c² L^{-4}/g²)`; it dominates
     Balaban's `exp(-p0(g))` only for `g ≤ γ0(L)`. Balaban chooses `γ` after `L` anyway, so this is a condition on the
     coupling input, stated in the row `runningCoupling`.
   * **F5 (corrections to `V1-EXCISION.md`):** (46) comes from `[5]` Theorem 3.12 (not 3.13); plaquettes next to a
     hole are regular because `Λ` is a small-field domain, not by the definition of the hole.
3. **E10** (the fresh factor in branch (a)) is not a separate field: for moderate cores it is D-mod, for deep cores it
   is TRAP (trapped at creation, so no deep core reaches branch (a)).

## 1. The inductive form `Form_k`

**Data at scale `k`** (`0 ≤ k ≤ K`, `K` the stopping scale of the weak-coupling regime). The torus `T` with Balaban's
lattices `T^{(j)}` ([III] Sect. 1-2). The state space `X_k` = block fields `V_k` (on the bonds of `T^{(k)}` outside the
holes) × finite record sets `𝓡_k`. A **record** `r = (H_r, h_r, s_r, a_r)`: a hole `H_r` (a connected set of bonds at
its root scale `s_r ≤ k`, together with its image at scale `k`), its frozen content `h_r` (group values on `H_r`), the
root scale, and its root action `a_r = A_min n_r`, `n_r` the number of plaquettes of
`H_r` at angle `≥ r0`. Records are pairwise at distance `≥ R_sep` at scale `k` (F2). Reference measure `ν_k`: product
Haar on the bonds of `V_k`, and on records counting measure in `(H_r, s_r)` times Haar on `h_r`.

**`Form_k(ρ)`** holds when `ρ: X_k → [0, ∞)` can be written

`ρ(V, 𝓡) = Σ_{({Ω_j}, {Λ_j}, {Z_j}) admissible} Π_{r ∈ 𝓡} w_r · T_k(Z_k; 𝓡) [ χ_k(Λ_k) exp A_k(V, U_k^𝓡(V), 𝒜) ]`

with:

* **(F-a) domains:** admissible sequences of [III] Sect. 2 (large-field regions `Z_j`, small-field domains `Λ_j`,
  `Ω_j`, unions of `M`-, `MR_j`-cubes at scale `j`, with Balaban's nesting); in addition, every record hole that is not
  subscale (`ρ_k > 1`: larger than one scale-`k` lattice spacing, or with a neighbourhood not yet `ε_k`-regular) lies
  in `Z_k`, and every subscale hole lies in `Λ_k` or in `Z_k`.
* **(F-b) background:** `U_k^𝓡(V)` = the minimiser of (2.12) on Balaban's determining set (2.11) with each subscale
  hole of `𝓡` excised (frozen content, constraint read on the filled field): row V1. It depends on `V` only through
  `M_B`, and on the records only through their contents next to `Λ_k`.
* **(F-c) small-field condition:** `χ_k(Λ_k)` is (2.17): `sup |U_k(∂p) - 1| < ε_k` over the plaquettes of the
  `L M² R_k`-cubes of `Λ_k`, `ε_k = g_k p0(g_k)`.
* **(F-d) integrations:** `T_k(Z_k; 𝓡)` factorises over the components of `Z_k` (2.19) and into one-step operations
  (2.20)-(2.22), each of the form (2.21) or changed by an R-operation; in M1 a one-step operation on a small-field
  domain also contains the conditional step's resampling: its numerator and denominator are fibre integrals
  (`Exact.lean`), and the record contents `h_r` are never integrated after their root step.
* **(F-e) action:** `A_k = -g_k^{-2} A(U_k^𝓡) + E_k + R_k + B_k - E_k^{vac}` (2.23), with
  `E_k` localised as in (2.25)-(2.29) with the bounds of [I] (1.18) and the domains (2.28);
  `R_k` as in (2.30)-(2.33) with the bound (2.31); in M1 the R-terms may depend on `V` through `M_B(U_k)` on `Λ`
  (the conditional step's ratio `N/D` is a function of the next field);
  `B_k` as in (2.40)-(2.42). (Corrected in `S1-PROOF.md`: the records' maintenance terms are factors of `w_r`, not
  B-terms.)
* **(F-f) records:** `w_r ≤ exp(-a_r/(2 g_{s_r}²))` for every record (root suppression, root entropy, carrying and the
  summed maintenance already included, `TRAP.md` 3 with F3); `w_r` is an analytic function of the fields within
  distance `O(1)` of the hole; `a_r := A_min n_r` (corrected in `S1-PROOF.md` 4).
* **(F-g) symmetries:** gauge invariance of every term; Euclidean covariance (2.29), (2.32) of the sums over positions
  (records are covariant as a set).

**The law half** (not part of `Form`): `ν_k`-density `ρ_k` is the law of `(V_k, 𝓡_k)` under the Wilson measure,
where `V_k` is the twisted/excised block field and `𝓡_k` the records produced by the trapping rule (both are measurable
functions of the bare field). Lean: `m1_laws`.

**S1 (`assemble`):** for `k < K`, if `Form_k(ρ_k)`, the coupling input holds and every row holds at `k`, then
`Form_{k+1}(ρ_{k+1})`, where `ρ_{k+1}` is the density of the pushforward of `R̂ ρ_k` after Balaban's operations.
Proof outline (to be written as §8 of the paper): P1, P2 (domains and preliminary integrations); X2 (gauge);
on each small-field domain the conditional step: V1, V2, E1-E3 (background and denominator), E4 (localisation),
E5-E9 (normalisations, analytic extension, large-field factors, fibre mass, entropy, fundamental inequality); cores:
D-mod (moderate), TRAP, P2′, P4 (deep: new records created at `k + 1` from plaquettes of `V_{k+1}` at angle `≥ r0`,
merged per F2); E11-E13 (polymer gas, exponentiation, final form (2.18) at `k + 1`). **Status:** logical structure
**Lean** (`m1_assembly_rows_upTo`); the bookkeeping write-up open (routine, 4 pp.).

## 2. The rows, precisely

Throughout: `0 ≤ k < K`; `L ≥ L0(d)` odd; `r0 ≤ c_d/L²`; `M, R_j, p0, p1, β0, κ` Balaban's constants ([III] Sect. 2,
[V] Sect. 1); `g_k ≤ γ ≤ γ0(L)`. "Regular `W`" = Balaban's regularity at scale `k + 1` on `Λ`.

| field | precise statement | pinned to | status |
|---|---|---|---|
| `X2 k` | For every small-field domain `Λ` and every gauge-invariant integrable `F` of the bonds of `Λ`: `∫ F dU = ∫ F|_{U = 1 on 𝒯} Π_{b ∉ 𝒯} dU`, `𝒯` the block-axial forest (block trees rooted at the centres, and at `S_H` for holes); i.e. inserting and removing the gauge fixing inside `T` is exact, Jacobian 1 | [I] (0.14)-(0.16); [V] p. 378 | **Lean** one leaf + paper (`ROUTINE-ROWS.md` 2) |
| `P1 k` | Balaban's preliminary operations [IV] (1.10)-(1.99) applied to a density of `Form_k` are equalities of functions of `(V_k, 𝓡_k)` (no estimate), and produce the input form of the R-operation [IV] (1.99) | [IV] pp. 177-193 | citation (confirmed, `NOTE.md` 1.1) |
| `P2 k` | For a small-field domain `Λ` and an outside field `V_out` regular near `Λ`: the restriction `χ_{k,Λ}` and Balaban's extension of `V_out` into `Λ` are defined and regular, (1.74)-(1.75) | [IV] (1.74)-(1.75) | citation |
| `V1 k` | For every admissible `Λ`, every regular `W` on the coarse bonds of `Λ`, every `V_out` regular near `Λ`, every record set with subscale `R_sep`-separated holes in `Λ`: the problem `min A_H(U)` s.t. `Q_{k+1}(Ũ) = W` on `Λ`, `U = V_out` outside, has exactly one minimal orbit under `{u: u = 1 on S_H}`; its element `V̂_Λ` satisfies the regularity of `[15]` (2) with constant `O(B5 M⁵)(ε_k + ε_{k+1})`, is analytic in `(W, V_out)` on the complex domain of `[15]` (7), and has the derivative decay `[15]` (190) | `[15]` Thm 1, Prop 9; [IV] Prop 1; [V] (1.12)-(1.13) | **paper** (`S6-START.md` 2, `V1-EXCISION.md`, `V1-INPUTS.md`) |
| `V2 k` | The background `U_0(W)` of V1 lies in Balaban's spaces `U_j(X, α0, α1)` ([III] (2.34)-(2.39)) on all scales `j ≤ k` in `Λ`, in the block-axial gauge, and `χ''_k = 1` on it | [IV] (1.80)-(1.98) | **paper** (`ROUTINE-ROWS.md` 3) |
| `Dmod k` | For a moderate core (all plaquettes of its star in `[ε_k, r0)`) the spread of its image satisfies `s_{k+1} ≤ θ s_k` with `θ = L^{1-d} + K r0 + K' ε_k ≤ ½` | `NOTE.md` 2.2-2.3; [V] (1.31), (1.47) | **paper** + **Lean** core; `K = 8`, `K' = 8dL²` (`ROUTINE-ROWS.md` 4) |
| `TRAP k` | (a) every plaquette of `V_{k+1}` at angle `≥ r0` belongs to the hole of a record created at `k + 1` (delay `N_t = 0`), holes are connected components, merged when closer than `R_sep`; (b) the excised blocking is well defined, covariant, local, link reflection positive and exact (T1, T2); V1 holds with excision (T3); the fillings of neighbouring blocks agree up to `O(ε D)` (T4); (c) accounting: the record's weight, root suppression × root entropy × carrying × summed maintenance, is `≤ exp(-a_r/(2 g_{s_r}²))` | `TRAP.md`, `TRAP-CHECKS.md` | **paper**; F3: accounting with covering numbers (below) |
| `P2prime k` | For a subscale record (root `s`, hole `H`) the change of the step's normalisation by the frozen hole is `|Δ_k| ≤ C [cap_k(H)(1 + p0(g_k)²) + cap_k(H)^{1/2} p0(g_k)(1 + a^{1/2}/g_s)]`, with `cap_k(H) ≤ C min(N_k(H), ρ_k^{d-2})`, `N_k(H)` the number of scale-`k` cubes meeting `H`, `ρ_k` its diameter at scale `k` | `P2-PRIME.md` (Lemma A and its corollary), given I1-I3 | **paper** given I1-I3 (`P2-PRIME.md` 5) |
| `P4 k` | Under `Form_k`, the weight of the event "a given plaquette of `V_k` has angle `≥ r0`" is at most `exp(-c_P r1²/g_k² + C 2^d L^d log g_k^{-2})` relative to the weight without it, `r1 = r0/(C_d L²)` | `[15]` Thm 1; [V] (1.76)-(1.79), p. 380 | **paper** (`ROUTINE-ROWS.md` 5) |
| `E1 k` | For regular `W`, the first variation of `A_H` at `V̂_Λ` vanishes on the tangent space `ker Q̃_1` of the constraint: `J_0 = Q̃_1* λ` | [V] (1.2)-(1.6), (1.28)-(1.29) | **paper** (`S6-START.md` 3) |
| `E2 k` | The Hessian of `A_H` at `V̂_Λ`, on fields vanishing on the hole's bonds, in block-axial gauge, with `Q̃_1 A = 0`, is `≥ c_d d^{-4} L^{-(2d+2)}` | [V] (1.7)-(1.9) | **paper** (`S6-START.md` 3, `POINCARE.md`, `V1-INPUTS.md` Lemma LP) |
| `E3 k` | `D_X(W) = exp[-g_k^{-2} A(ζ0, U_0(W)) - Î + Ê_k(Λ)]` with `|Î| ≤ O(1) M⁵ + O(log g_k^{-2})` per constrained bond, analytic and non-zero for regular `W`; the Wilson term cancels in `N_X/D_X` | [V] (1.10)-(1.11), (1.30)-(1.37) | **paper** (`E3.md`, `POINCARE.md`) |
| `E4 k` | `N_X(W)/D_X(W)` depends on `W` only through `U_0(W)` and the shell shifts, localised as a sum over polymers with decay `exp(-κ d_k(X))` | [V] (1.14)-(1.69) | **paper** (`ROUTINE-ROWS.md` 6) |
| `E5 k` | The normalised operation `T̂'_k(X)` has Balaban's constants (1.70)-(1.71), with the δ-Jacobian `O(1)` per coarse bond of `Λ`; the constants of numerator and denominator cancel | [V] (1.70)-(1.71), (1.78) | **paper** (`E5-E9.md`) |
| `E6 k` | For `(U, J)` in Balaban's analyticity domain: `|T'(X, (U, J))F| ≤ T'(X, (U, 0))1 e^{sup|σ|} sup|F|` and the reverse bound | [V] (1.73)-(1.75) | **paper** (`E5-E9.md`) |
| `E7 k` | The large-field factors (1.76)-(1.79) hold under the block constraint; group integrals over a fibre are bounded by the fibre mass (E7J) | [V] (1.76)-(1.79) | **paper** (`E5-E9.md`, `E7J.md`) |
| `E7J k` | For every `W`: `m_Λ(W) ≤ (C_d L^{3(d-1)})^{|Λ^{(k+1)}|}` (fibre mass of the sub-`r0` configurations) | new | **paper** (`E7J.md`) + **Lean** slicing |
| `E8 k` | Balaban's entropy induction (1.80)-(1.88) with delay `N = R_j`, the extra cost `O(1)` per site absorbed into `O(1) M^d R^{d+1}` | [V] (1.80)-(1.88) | **paper** (`E5-E9.md`) |
| `E9 k` | `sup_{W regular} N_X(W)/D_X(W) ≤ exp(-2(1+β0)^{-1} p0(g_k))` | [V] (1.89) | **paper** (`E5-E9.md`) |
| `E11 k` | Polymer gas with activities `|F(X')| ≤ c1 exp(-(1+β)κ d(X'))`, local on the same domains, now depending on `W` on `Λ_j` | [V] (1.90)-(1.97) | citation (checked, `ROUTINE-ROWS.md` 7) |
| `E12 k` | Exponentiation: new R-terms `|R''(X)| ≤ exp(-p0) exp(-κ d_k(X))`, new action | [V] (1.98)-(1.101) | citation (checked, `ROUTINE-ROWS.md` 7) |
| `E13 k` | The result has the form (2.18) at `k + 1` with the next `T` | [V] (1.102)-(1.104); [III] Sect. 3 | citation (checked, `ROUTINE-ROWS.md` 7) |
| `runningCoupling` | `g_k ≤ γ` for `k < K`, with `γ ≤ γ0(L)` small enough that `A_min γ^{-2} ≥ 4 p0(γ)` and `A_min^{1/2} ≥ γ p0(γ)`, `A_min = c_P r0²/(C_d² L⁴)` (F4) and Balaban's conditions hold | [I] Theorem 2 | external |

**F3 in detail (TRAP and P2′).** For a connected hole with `n` deep plaquettes and diameter `D`: `a ≥ c0 r0² n`;
`N_k(H) ≤ 3^d (n L^{-(k-s)} + 1)` (a connected set of `n` sites meets at most that many cubes of side `L^{k-s}`), so
`Σ_k cap_k(H) ≤ C(n + log D)`; carrying while `D L^{-(k-s)} ≥ 1` costs `≤ C polylog(g^{-2}) Σ_k N_k(H) ≤ C n polylog`;
root entropy `≤ C n log g^{-2}`. All are `≪ c0 r0² n/g_s²`, so `w_r ≤ exp(-a_r/(2 g_s²))` for every size and shape.
The bound `D0 ≤ 100 M R_h` in `TRAP.md` is not needed.

## 3. Effect

* `Assembly.lean`: `M1RowHypothesesUpTo`, `M1RowHypothesesUpTo.stepEstimates`, `m1_assembly_rows_upTo` (F1).
* `TRAP.md`: merging rule (F2), accounting by covering numbers (F3).
* `V1-EXCISION.md`: corrections (F5); inputs proved in `V1-INPUTS.md`.
