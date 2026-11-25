# The routine rows: X1.H1, X2, V2, D-mod constants, P4, E4, E11-E13 (m1-tools, 2026-11-22)

Brief: item 3 of the order of work in `M1-PLAN.md`: do the rows marked routine, flag any that is not. Precise
statements: `S1-ROWS.md` 2. The P2′ write-up is section 3 of `P2-PRIME.md` v3 (appended there). Read for this note:
[IV] pp. 194-200 ((1.76)-(1.98)); [V] pp. 357-361 ((1.12)-(1.29)) and pp. 387-391 ((1.90)-(1.104)); earlier reads in
`NOTE.md` 1. Lean: `formal/ProofPhase/M1/Routine.lean`. Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **All rows are routine; none needed a new idea.** Two have a machine-checked core: X1.H1 (fibre densities exist
   once the fibre mass is bounded) and X2 (gauge fixing at a leaf is exact). D-mod's constants are now explicit:
   `θ ≤ L^{1-d} + 8 r0 + 8 d L² ε`. P4 moves from citation level to paper with an explicit `A_min`.
2. **One consequence worth knowing (P4):** a deep plaquette of size `r0` at scale `h + 1` is created from fine
   plaquettes of size at least `r1 = r0/(C_d L²)`, so the root suppression is `exp(-c r0²/(C_d² L⁴ g_h²))`. With
   `r0 ≤ c/L²` from E7.J this is `exp(-c'/(L⁸ g_h²))`: still far below `exp(-p0(g_h))` for `g_h ≤ γ0(L)`
   (`S1-ROWS.md` F4, with `γ0(L) ~ L^{-4} p0^{-1/2}`).
3. **One consistency point fixed:** "subscale" for a record means smaller than one scale-`k` lattice spacing
   (`ρ_k ≤ 1`), as in P2′; before that the record is carried in the large-field region. V1 with excision would allow up
   to `L/4`; `S1-ROWS.md` now uses `ρ_k ≤ 1` throughout.

## 1. X1.H1: fibre representation

**Statement.** For every term of the step at scale `k` (density `ρ` against `ν_k`, finite) and the reference kernel
`ŵ`, there are measurable `N, D` on the conditioning variable `y = (W, V_out, 𝓡)` with
`φ_*(ρ ν_k) = λ · N`, `φ_*(ŵ ν_k) = λ · D` (`λ` = product Haar on the coarse bonds of `Λ` × the reference on
`(V_out, 𝓡)`), and `N(y)` is the δ-function integral `∫ dV δ(V̄ W⁻¹) ρ(V, V_out, 𝓡)` of [I] (0.13).

**Proof.** By E7.J, `φ_*(ν_k restricted to the sub-r0 configurations) ≤ (C_d L^{3(d-1)})^{|Λ^{(k+1)}|} λ`; every term
is supported there (deep variables are trapped at creation and are not integrated, `S1-ROWS.md` (F-d)).
`fibre_rep_of_map_le` (**Lean**) gives `N = dφ_*(ρν)/dλ` with `φ_*(ρν) = λ · N`; the same for `D`. The Radon-Nikodym
derivative is the δ-function integral: for continuous `ρ`, mollifying `δ` and using the fibre-mass bound for dominated
convergence gives `N(y) = lim ∫ dV δ_n(V̄ W⁻¹) ρ(V)` for `λ`-a.e. `y`, and continuity in `W` (the block map is a uniform
submersion on the sub-`r0` set, `E7J.md` 2(c)) makes it hold for every `y`. **Status:** **Lean** (existence) + paper.

## 2. X2: gauge fixing inside `T`

**Statement** (`S1-ROWS.md` 2). For a gauge-invariant integrable `F` of the bonds of `Λ`:
`∫ F Π dU = ∫ F|_{U = 1 on 𝒯} Π_{b ∉ 𝒯} dU`, `𝒯` the block-axial forest (block trees rooted at the block centres and,
for records, at the hole sites `S_H`).

**Proof.** Induction on the number of tree bonds. A forest that is not empty has a leaf `v` (a site of degree 1 in
`𝒯`, not a root) with tree bond `b`. Gauge transformations at `v` act on the bonds at `v`; choosing `g = U(b)^{±1}`
sets `U(b) = 1` and multiplies the other bonds at `v` by `g` on one side. Gauge invariance gives
`F(U(b), ω) = F(1, g · ω)`; Haar measure on each bond is invariant under left and right multiplication, so the action
of `g` on `ω` preserves the product Haar measure. `lintegral_gauge_leaf` (**Lean**) gives
`∫ F dU(b) dω = ∫ F(1, ω) dω`. The new integrand `F(1, ·)` is invariant under the gauge transformations at the
remaining sites (they do not touch `b`'s value `1` unless they act at `v`, which is no longer needed); remove `v` and
repeat. Roots are never leaves, so sites in `S_H` (where the frozen content breaks gauge invariance) are never
transformed. The Faddeev-Popov Jacobian is 1 because each step is a measure-preserving change of variables. Balaban's
version ([I] (0.14)-(0.16)) inserts the gauge fixing with the δ-functions of the blocking; the same induction applies
to integrands that contain them, since `δ(V̄ W⁻¹)` with `W` transformed covariantly is gauge invariant. ∎
**Status:** **Lean** (one leaf) + paper (induction).

## 3. V2: background regularity

**Statement** (`S1-ROWS.md` 2). The background `U_0(W)` built from V1's minimiser lies in Balaban's spaces
`U_j(X, α0, α1)` ([III] (2.34)-(2.39)) on all scales in `Λ`, in the block-axial (AL) gauge, and `χ''_k = 1` on it.

**Carry-over of [IV] pp. 194-200, step by step.**

| [IV] | Balaban's step | input it uses | M1 |
|---|---|---|---|
| (1.77)-(1.78), Prop 1 | minimal orbit `V̄` of `V_k ↦ A(U_{k,Z}(V_k))` on `Z ∩ Λ^c`, regularity `|V̄(∂p) - 1| < B5 M⁵ ε` | `[15]` | V1's minimiser `V̂_Λ(W, V_out)` with the same bound `O(B5 M⁵)(ε_k + ε_{k+1})` (V1, with excision) |
| (1.79)-(1.80) | `U_0 = U_{k,Z}(V̄)`; `|U_0(∂p) - 1| < 2ε_k² + O(1) B3 B5 M⁵ exp(-δ dist(p, Λ)) ε_k²` | (1.78) and the decay of H-functions (`[15]` Prop 9, (190)) | same (both inputs hold: V1, and the decay of `V1-INPUTS.md` Lemma FR for the modified operators near records) |
| (1.81)-(1.82) | fluctuation `V'` on `B_0`, decomposition `1 = χ' + (1 - χ')` with `|B'| < ε'_k` | definitions | same; the conditional step's resampling acts only on the small-field part |
| (1.83)-(1.87) | axial gauge in `k`-blocks for `M_k(U_0)`, then Landau around 1: `U_0^{u_0} = exp iA_0`, `|A_0|, |∂A_0| ≤ O(1) B3 B5 M⁶ ε_k` | (1.80), [14] (1.65), [6] Thm 2 | block-axial gauge is Balaban's axial gauge in `k`-blocks; with records, [6] Thm 2 with the hole sites fixed (`V1-INPUTS.md` input (i)) |
| (1.88)-(1.98) | `χ''_k = 1`: the H-function expansions (1.90)-(1.93) bounded by `B3 exp(-R_h) ε_h` (1.94), using the delay `N ≥ O(1)(log g^{-2})^ν`, `½ν ≤ p0 - p1 - 1`; result (1.96), (1.98) | (1.80), H-function decay, Balaban's `N` | same: Balaban's `N = R_j` stands once deep cores are trapped (`E5-E9.md` 0); near a record the H-functions are those of the filled field (T1, T4) |

**Status:** **paper** (carry-over; every input is V1, the decay bounds of `V1-INPUTS.md`, or Balaban's own).

## 4. D-mod: the constants

**Statement.** `θ ≤ L^{1-d} + K r0 + K' ε` with `K = 8`, `K' = 8 d L²`, in the convention where `|X|` is the rotation
angle of `Ad(e^X)` (so `ad_X` has eigenvalues `0, ±i|X|`), for stars with spread `≤ r0 ≤ ½` and background
plaquettes `≤ ε`.

**Proof.** (a) *Derivative of the logarithm.* `d/dt log(e^Z e^{tY})|_{t=0} = f(ad_Z) Y` with
`f(x) = x/(1 - e^{-x})`. `ad_Z` is skew, so `‖f(ad_Z) - 𝟙‖ = max |f(it) - 1|` over `t ∈ {0, ±|Z|}`, and
`f(it) - 1 = (t/2)cot(t/2) - 1 + it/2`, so `|f(it) - 1| ≤ (t²/4 + t⁴/144)^{1/2} ≤ 0.51 t` for `t ≤ 1`. The same bound
holds for perturbations on the left. (b) *One path.* In (0.4) a path `P` from the star at `y` gives the loop
`Z_P = log(e^{i a_{b(P)}} U_P e^{-i a_c})` (`b(P)` its first bond, `c` the straight path's first bond, the transports
based at `y`). Its derivative in the star coordinates is `δa_{b(P)} - δa_c` up to an error `≤ 2 · 0.51 (|Z_P| + |a|)`
times `|δa|`; `|a| ≤ r0` (gauge at `y` with one star coordinate 0), and `|Z_P| ≤ 2 r0 + d L² ε` (the loop bounds a
surface of `≤ d L²` plaquettes of the background and passes through the star twice). (c) *Average and
exponential.* The averaged `v = Σ_P w_P Z_P` (weights sum to 1) and the coarse coordinate
`a'_c = log(e^{iv} e^{i a_c})` add two more errors of the same type, `≤ 0.51(|v| + |a_c|) |δ·|`. (d) Altogether the
derivative of `a ↦ a'` differs from the exact weights `F` of `NOTE.md` 2.2 by at most
`2 · 1.02 (3 r0 + d L² ε) + 1.02 (3 r0 + d L² ε) ≤ 8 r0 + 8 d L² ε` in the spread seminorm (an error `e` bounded by
`η |δa|_∞` moves the spread by at most `2η |δa|_∞ ≤ 2η · spread(δa)` in the gauge with one coordinate fixed). The
mean-value inequality along the segment (the region `|Z| ≤ 1` is convex in these coordinates) gives the statement. ∎

**Consequence.** With `r0 ≤ c/L²`, `θ ≤ L^{1-d} + 8c/L² + 8dL²ε ≤ ½` for `c ≤ 1/32`, `L ≥ 3`, `ε L² ≤ 1/(32d)`.
**Status:** **paper** (explicit, not optimised); the Dobrushin part `L^{1-d}` and the iteration are **Lean**
(`Dilution.lean`).

## 5. P4: root suppression

**Statement.** Under `Form_k`, the weight of the event "a given plaquette of `V_{k+1}` has angle `≥ r0`" is at most
`exp(-c_P r1²/g_k² + C 2^d L^d log g_k^{-2})` times the weight without it, `r1 = r0/(C_d L²)`.

**Proof.** (a) *Creation needs a fine large field.* A coarse plaquette is the product of four averaged coarse bonds;
each averaged bond differs from its straight path by an average of loops bounding `≤ d L²` fine plaquettes, and the
square of straight paths bounds `L²` plaquettes. So a coarse plaquette at angle `≥ r0` has a fine plaquette at angle
`≥ r1 = r0/(C_d L²)` in its `2^d` blocks (`C_d = 1 + 4d`). (b) *The fine large field is suppressed by its action.*
`r1 ≫ ε_k`, so this plaquette lies in a large-field region of `V_k`. Balaban's large-field factors ([V] (1.76)-(1.79))
are pointwise bounds of the integrand by `exp(-g_j^{-2} A)` on the region where a characteristic function `χ^c` forces
a plaquette above the threshold, with `A ≥ c Σ_p |U(∂p) - 1|²` (`[15]` Theorem 1, the lower bound of the action by the
block field's plaquettes); with the threshold `r1` instead of `ε_k` the same bound gives `exp(-c r1²/g_k²)`. (c) The
normalisation against the small-field reference costs at most `O(log g_k^{-2})` per site of the `2^d` blocks, i.e.
`C 2^d L^d log g_k^{-2}` (Balaban's normalisation constants, [V] p. 380). ∎ So `A_min = c_P r0²/(C_d² L⁴)`.
**Status:** **paper** (pinned to [V] (1.76)-(1.79) and `[15]` Theorem 1).

## 6. E4: localisation of the `W`-dependence

**Statement.** `N_X(W)/D_X(W)` depends on `W` only through `U_0(W)` (and the shell shifts of [V] (1.14)-(1.29)), and
the dependence is localised: written as a sum over domains with decay `exp(-κ d_k(X))`.

**Carry-over of [V] pp. 357-376.** [V] (1.12)-(1.13): the critical point of the constrained quadratic problem,
`-(P_0 H*Δ H P_0)^{-1} P_0 H* J`: in M1 on `P_0 ∩ ker Q̃_{k+1}` (V1). (1.14)-(1.17): expansion of the action around
`U''_{k,Z}` through the H-functions; W enters only through the background. (1.18)-(1.29): the linear and quadratic
terms in `H B'`, with the bounds (1.23) `|∂^n H B| ≤ B3 exp(-M R_h + …) ε_k` coming from the decay of the H-functions
(`[15]` Prop 9, (190); with records, `V1-INPUTS.md` Lemma FR keeps the decay). (1.30)-(1.48): the Wilson term and the
old core's `L^{-N}` suppression: for moderate cores D-mod, for deep cores nothing (trapped, `TRAP.md`). (1.49)-(1.69):
expansions in four stages and localisation of the E-, R-, B-terms as in [I] Sects. 3-6 (identities plus the decay
bounds). Every localisation uses only the decay of the H-functions and of the propagators, which hold (V1, V1-INPUTS).
**Status:** **paper** (carry-over).

## 7. E11-E13: polymer gas, exponentiation, final form

**Checked against [V] pp. 387-391.** (1.90)-(1.91): Mayer expansion and polymer activities; the components are joined
when contained in one localisation domain. (1.92): the activity bound uses only (1.68) (localisation), (1.73) (E6) and
(1.89) (E9). (1.93)-(1.97): summation, with `κ` large and `p0(g_k)` large; result `|F(X')| ≤ c1 exp(-(1+β)κ d(X'))`.
(1.98)-(1.100): exponentiation by the convergent series of [I] (7.13); new R-terms `|R'(X)| ≤ exp(-p0) exp(-κ d_k(X))`,
new B-terms on domains meeting the large-field region. (1.101)-(1.104): the new action and large-field region; the
form [III] (2.18).

**What M1 changes.** (i) The activities depend on `W` through `N/D` on the domains `Λ_j`, locally (E4), so localisation
domains are unchanged. (ii) The normalisation of the `T`-operations used in (1.103) ("applied to a function that does
not depend on its integration variables, it equals 1") holds for the conditional step too: on each fibre the resampling
kernel `ŵ/D` integrates to 1 (definition of `D`). (iii) Euclidean covariance (2.32) holds for the symmetries that keep
the block partition (the block constraint is covariant under them); records are covariant as a set. (iv) The new
large-field region (1.102) also receives the records created at `k + 1` (TRAP), merged per `R_sep`. **Status:**
**citation** (checked; the three changes are definitional).

## 8. Effect

| row | before | now |
|---|---|---|
| X1.H1 | open (routine) | **Lean** existence (`fibre_rep_of_map_le`) + paper |
| X2 | open (routine) | **Lean** one leaf (`lintegral_gauge_leaf`) + paper induction |
| V2 | open (routine) | **paper** (carry-over) |
| D-mod | constants open | **paper**, `K = 8`, `K' = 8dL²` |
| P4 | citation level | **paper**, `A_min = c_P r0²/(C_d² L⁴)` |
| E4 | citation | **paper** (carry-over) |
| E11-E13 | citation (check) | **citation** (checked, three definitional changes) |
| P2′ | proof given I1-I3, write-up open | written up (`P2-PRIME.md` v3, section 5), still given I1-I3 |
