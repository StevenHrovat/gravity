# M1 scoping: one step of Balaban's R operation with the next block field held fixed (c6f-m1scope, 2026-11-22)

Brief: paper test for M1 of `../c5d-supplier/BALABAN-READING.md` section 5. Does the R operation of Balaban CMP 122 I-II
survive, for one renormalisation step, if its ratios are taken with the next block field held fixed, so that the
densities stay the true laws of the block fields? Verdict SURVIVES / SURVIVES WITH A NEW LEMMA / BREAKS, and M1's size.

Paper labels as in `BALABAN-READING.md`: [I] CMP 109, [III] CMP 119, [IV] CMP 122 p. 175 (Large field renormalization
I), [V] CMP 122 p. 355 (II). `[15]` is Balaban's variational-problem paper as cited in [III]/[IV]/[V] (not read).

Reading marks. **Full** (page images read by me): [IV] pp. 175-181, 192-202; [V] pp. 355-363, 374-392; [III]
pp. 254-264. **OCR search**: all five papers for "equivalent" (the word Balaban uses for "same integral, not same
density"); it occurs only at the three places listed in 1.3. **Not read**: [IV] pp. 182-191 (the general preliminary
integration step), [V] pp. 364-373 (part of the localization expansions). Where the analysis below relies on those pages
it says so. No Lean, no numerics, nothing outside this file edited.

## 0. Result in plain words

1. **Where the law is lost.** Balaban's R step for one renormalisable large-field component `X` has three
   law-changing operations, and only these: (L1) the free integration of the current field `V_k` over the domain `Λ`
   ([IV] pp. 193-194, giving (1.76) and the equivalence (1.99)); (L2) the reinsertion of a normalised small-field kernel
   on `Λ` ([IV] (1.100), normalisation only (1.102); per component [V] (1.1)); (L3) the removal of the gauge-fixing
   δ-functions by a reversed Faddeev-Popov step ([V] p. 378). Everything before (the preliminary integrations, [IV]
   (1.10)-(1.99)) is exact, and everything after (localization, exponentiation, [V] (1.12)-(1.104)) is an identity on the
   modified density. (L1)+(L2) together are a **resampling**: per term, `V_k` on `Λ` is redrawn from a small-field kernel
   given `V_k` outside `Λ`. The next block field reads `V_k` on `Λ`, so its law changes.
2. **The conditional step works by the same mechanism.** Replace the free integral over `V_k|Λ` by the integral over
   the fibre `{V̄_k = W}` (`W` = next block field on `Λ`), and the kernel by the same small-field kernel restricted to
   that fibre. Then `T R̂ = T` exactly (one line, 2.1), (L3) becomes an exact Faddeev-Popov identity inside `T`, and the
   ratio `N(W)/D(W)` is a function of the next field over `Λ` and the current field just outside it. Where `W` is not
   regular over `Λ` the denominator vanishes; those configurations stay unrenormalised and become a new large-field
   region of the next scale, a function of the new field (2.2).
3. **Estimates.** Almost every estimate Balaban uses in the step survives with the same proof and changed constants:
   the large-field suppression is pointwise in the integrand, so conditioning does not touch it; the normalisation
   factors become `W`-dependent but analytic and the big Wilson terms still cancel exactly; the quadratic-form
   positivity gets better (block constraint); the entropy induction (1.80)-(1.89) is combinatorial and unchanged; the
   polymer gas (1.90)-(1.100) is again vacancy-1 with local activities. Proposition 1 of [IV] (the unconstrained
   minimizer on `Λ`) is replaced by the standard constrained minimizer of a two-scale determining set, which is the
   kind of object Balaban's variational theory treats anyway. Table in 2.3.
4. **One thing is genuinely new.** Balaban never has a block constraint sitting on top of the old large-field core
   (the deep region he integrates without expanding, [IV] (1.76), [V] (1.71)). In the conditional step the coarse
   bonds over that core are fixed, and the ratio must still be **analytic** in them (R-terms must be, [III] (2.31)),
   and an irregular coarse field there must still carry a **fresh** large-field factor (not the old core's factor
   twice). Both follow from one deterministic statement about the averaging map: after `n` averaging steps the old
   core is invisible to the block field up to `π c^n`, `c < 1` (**Lemma D, core dilution**, section 3). It needs
   `N ≥ O(log g^{-2})` steps between creation and renormalisation; Balaban's own count already allows that (his
   (1.80) works with `N = R_j ≥ (log g_j^{-2})^r`, `r ≥ 2`).
5. **Verdict: SURVIVES WITH A NEW LEMMA (Lemma D).** M1 is long, mostly routine, with one new lemma that is
   elementary geometry of the averaging contours but depends on how the averaging is extended to configurations far
   from the identity (Balaban does not say in the pages read; it can be chosen). Size: about 35-45 journal pages of new
   writing in Balaban's density (redo of [IV] pp. 192-202 and [V] pp. 355-363, 377-383 under a block constraint, plus
   Lemma D, about 8 pages, plus 5 pages of setup), and a line-by-line check of about 40 pages that should carry over
   unchanged. Section 4.

## 1. Balaban's R step, precisely

### 1.1 Setting and notation ([IV] Sect. 1, [III] Sect. 2)

`ρ_k(V_k) = ∑_{\{Ω_j\},\{Λ_j\}} χ_k(Ω_k) T_k exp A_k(g_k^{-2}, U_k)` ([III] (2.18)). `T_k` is a composition of
one-step operations `T^{(j)}(Z_{j+1} ∩ X) = ∫ dV_j|_{Ω^c_{j+1} ∩ X} δ(V̄_j V_{j+1}^{-1}) ζ(Ω^c_{j+1}) ∫ dA_j χ(...)
exp[quadratic form]` ([III] (2.20)-(2.21)): in a large-field region the fields of the finer scales are kept as
integration variables, **tied to the coarser field by δ-functions**. So `ρ_k` before any R is exactly the law of the
`k`-fold block field `V_k` (the operations `T` are pushforwards).

A component `X` of the large-field region `Z = Z_k` is renormalised at step `k` if (i) it lies in a cube of side
`100 M R_k`, (ii) no new large fields were created in it in the last `N` steps ([IV] p. 177). For such `X`, with
`h = k − N`, the term is ([IV] (1.2)) `χ_k(Ω_k^{~-4}) ∏_{j=k−1}^{h} T^{(j)}(Z_{j+1}) χ_h(Ω_h \ Ω_{h+1}) T_h(Z_h) exp A_k`.

Names used below:
* `Λ = (Ω''^{~-4}_{k0+1})^c ∩ Z` ([IV] (1.73)): the domain on which R integrates; a union of `M`-cubes, rectangular,
  inside a cube of side `100M`.
* **core** `C = (Ω''^{~}_{h+1})^c ∩ Z`: the deep region whose variables (`V_h` on it, and the old operation
  `T_h(Z_h)` below it) Balaban integrates directly, without expanding around a background ([IV] (1.76), (1.89)-(1.97);
  [V] (1.71)). It contains the old large field. At scale `k` it is physically much smaller than one cell of the
  scale-`k` lattice once `L^N ≫ 100 M R_h`.
* `V_out` = `V_k` on `Z ∩ Λ^c` and beyond.
* `I_X(V_k)` = the term above, after the preliminary integrations, as a function of `V_k` (before the `Λ` integration).

### 1.2 The step in order

| # | operation | where | exact? |
|---|---|---|---|
| a | preliminary integrations: integrate, shell by shell from scale `h` up, the variables of `T^{(j)}(Z_{j+1})` near `∂Z_j`, **with the constraint** `V̄_j = V_{j+1}`; new large-field regions `Z''_j` (1.10)-(1.11), new domains `Ω''_j` (1.12), determining sets `B''_k` (1.13)-(1.17), backgrounds `U''_k` (1.18)-(1.21), partitions `χ^{(n)}_k` (1.22)-(1.23), ..., `T''^{(j)} = ∫ dV_j|_{Z''_{j+1}} δ(V̄_j V''^{-1}_{j+1})` (1.71)-(1.72) | [IV] (1.10)-(1.72) | **yes**: "All the above transformations preserve the kth density" (p. 193) |
| b | restrict `V_k` outside `Λ` by `χ_{k,Λ}` (1.75); the complement gives a large-field factor and is excluded from renormalisation | [IV] (1.74)-(1.75) | yes (exact partition) |
| c | **integrate `V_k` over `Λ` freely**: the result (1.76) is independent of `V_k|Λ`; all δ-functions inside `Λ` are integrated out (p. 194) | [IV] pp. 193-194, (1.76), equivalence (1.99) | **no (L1)** |
| d | variational problem on `Λ`: minimal orbit `V_Λ(V_out)` of `V_k|Λ ↦ A(U_{k,Z}(V_k))`, unconstrained inside `Λ` (**Proposition 1**), regularity (1.78), background `U_0 = U_{k,Z}(V_Λ)` (1.79)-(1.80) | [IV] (1.77)-(1.80); proof [V] (1.12)-(1.13) | — |
| e | fluctuation field `V'' = V' V_0` on `Λ_0 = Λ ∩ Ω''^{~-2}_{h+1}` (outside the core), axial gauge tree `T_0` (1.81)-(1.82), Landau gauge for `U_0` (1.83)-(1.87), partition (1.88), `χ''_k = 1` (1.89)-(1.98) | [IV] (1.81)-(1.98) | yes |
| f | **R'**: multiply by the normalised small-field kernel `w_X(V_k) / ∫ dV'|_Λ w_X`, `w_X = δ_{G}(V'_k) χ(Λ) exp[−g_k^{-2} A(ζ, U_{k,X}(V'_k V_Λ))]`, `V'_k = V_k V_Λ^{-1}`; only `∫ dV_k R'ρ_k = ∫ dV_k ρ_k` (1.102) | [IV] (1.100)-(1.102); per component [V] (1.1) | **no (L2)** |
| g | denominator: `(∫ dV'|_Λ w_X)^{-1} = exp[+g_k^{-2} A(ζ0, U_0) + I(U_0) − E_k(Λ)]`, `|I| ≤ O(1) M^5` (1.10)-(1.11); its big Wilson term is cancelled by the numerator's: linear term zero because `J_0 = 0` on `Λ` (1.3)-(1.5), quadratic form positive (1.7)-(1.9) | [V] (1.2)-(1.11) | identities and bounds |
| h | localization in `Z`: H-function expansions near `∂Z`, `∂Ω''_{h+1}`, random-walk expansions, terms `V(Y, U_k)` with (1.68)-(1.69) | [V] (1.14)-(1.69) | identities |
| i | split components: first class `X_i` (new `V_k` regular) and second class `Y_i`; **remove the gauge-fixing δ-functions on `X_i` by a reversed Faddeev-Popov procedure**, possible only after integrating `V_k` over `X_i` | [V] p. 378 | **no (L3)** |
| j | define `T'_k(X)` (normalised large-field operation) (1.71) and **R** (1.72); analytic extension (1.73)-(1.75); large-field factors (1.76)-(1.79); entropy induction (1.80)-(1.88); `T'_k(X)1 ≤ exp(−2(1+β0)^{-1} p0(g_k))` (1.89) | [V] (1.70)-(1.89) | bounds |
| k | Mayer expansion of the curly bracket of (1.72) into a polymer gas (1.90)-(1.91), activity bound (1.97), exponentiation (1.98)-(1.99), split into new R-terms (1.100) and boundary terms, new action (1.101), final form (1.102)-(1.104) | [V] (1.90)-(1.104) | identities |

### 1.3 Where law preservation is lost

* **(L1) [IV] pp. 193-194 and (1.99).** The term `I_X(V_k)` is replaced by `∫ dV_k|_Λ I_X(V_k)`, a function of `V_out`
  only. Balaban marks the change: from here on "≡" means equal integrals over `V_k` (p. 193; (1.99) on p. 200).
* **(L2) [IV] (1.100), (1.102); [V] (1.1).** The integrated term is multiplied by a probability kernel on `V_k|Λ`
  (the localized small-field Wilson weight around the unconstrained minimizer `V_Λ(V_out)`, normalised over all of
  `V_k|Λ`). Only the total integral is kept, (1.102).
* **(L3) [V] p. 378.** The gauge-fixing δ-functions `δ_{G0∩X_i}(V'_k)` are dropped by a reversed Faddeev-Popov step;
  "equivalent, but not equal", because it needs the integral over `V_k` on `X_i`.

Together, per term of the history sum: the joint law of the labels and of `V_k` on `Λ^c` is exact; the conditional law
of `V_k|Λ` given them is replaced by the kernel of (L2). The next blocking reads `V_k` on every block of `Λ` (and the
coarse bonds at `∂Λ` read both sides), so the law of `V_{k+1}` changes near `Λ`. This is the resampling picture of
`BALABAN-READING.md` 2.4, now with equation numbers.

## 2. The conditional step

### 2.1 Definition and exactness

Let `W` be the next block field `V_{k+1}` on all coarse bonds that read `V_k|Λ` (both blocks in `Λ`, or one in `Λ` and
one outside; `Λ` is a union of `M`-cubes, `M = L^m`, so it is a union of blocks). Write `δ_Λ(V̄_k W^{-1})` for the
product of the block δ-functions over these bonds. Define, for each renormalisable component `X`:

* reference kernel `ŵ_X(V_k)`: Balaban's `w_X` with the unconstrained minimizer `V_Λ(V_out)` replaced by the
  **constrained** minimizer `V̂_Λ(W, V_out)` (least `A(U_{k,Z}(V_k))` over `V_k|Λ` subject to `V̄_k = W`), and with the
  tree gauge `G0` replaced by a block-axial gauge (trees in each block rooted at the block centre, as in the RG gauge
  fixing of [I] (0.14)-(0.16)), so that the residual gauge group fixes `W`;
* `N_X(W, V_out) = ∫ dV_k|_Λ δ_Λ(V̄_k W^{-1}) I_X(V_k)`, `D_X(W, V_out) = ∫ dV_k|_Λ δ_Λ(V̄_k W^{-1}) ŵ_X(V_k)`;
* `(R̂ I_X)(V_k) = ŵ_X(V_k) · N_X(V̄_k|_Λ, V_out) / D_X(V̄_k|_Λ, V_out)`.

**Exactness.** For every `W`: `∫ dV_k|_Λ δ_Λ(V̄_k W^{-1}) (R̂ I_X) = N_X(W) · D_X(W)/D_X(W) = N_X(W)`. Since the next
step `T` integrates `V_k` with exactly these δ-functions, `T R̂ I_X = T I_X`, term by term. The same holds jointly for
several disjoint components (their `Λ`'s are disjoint unions of blocks inside distinct components of `Z`). So
`ρ_{k+1} := T R̂ ρ_k = T ρ_k` is **the law of `V_{k+1}`**. The intermediate `R̂ρ_k` is not the law of `V_k` (it
resamples `V_k|Λ` inside the fibre of `W`), but nothing downstream reads `V_k` except through `T`.

(L3) disappears: `ŵ_X` carries a block-axial gauge fixing whose residual group fixes `W`; the integrand of `T` is
invariant under that group, so inserting or removing the gauge δ-functions is an exact Faddeev-Popov identity inside
`T` (Jacobian 1 for axial gauges).

Equivalently: R̂ is Balaban's R applied one scale later, to `T I_X` as a function of `V_{k+1}`, with the `T`-image of
the small-field kernel as reference. That is why the structure carries over.

### 2.2 The two branches

Insert `1 = χ(W regular on Λ) + χ^c(W regular on Λ)` (sharp, at threshold `ε_{k+1}`; a function of `V̄_k`, so the
insertion is exact).
* **(b) `W` regular.** `D_X(W) > 0` (the fibre meets the support of `ŵ_X`, e.g. at `V̂_Λ`). Apply R̂. The ratio
  `N_X/D_X` is the new activity; it plays the role of `T'_k(X)1`.
* **(a) `W` irregular.** `D_X(W) = 0`: no regular `V_k` averages to `W`. Leave the term unrenormalised. It is a large
  field of the **current** field `V_{k+1}` over `Λ`, a function of the new field, as in [III] (3.2)-(3.3). It must
  carry a fresh large-field factor of scale `k+1` that multiplies (not replaces) the old one; that is Lemma D, (D2).

Balaban's second class `Y_i` ([V] p. 378: the resampled `V_k` irregular on `X`) has two options here: keep it as he
does ((1.102), multiplication operator `T_k(Y_i)1`), or put `χ_k` into `ŵ_X` so the resampled `V_k` is always
regular and these configurations go to branch (a). The second is simpler for M2 (all current large fields are then
functions of the current field).

### 2.3 Each estimate under conditioning

Status: **same** = same proof, same constants; **constants** = same proof, constants change; **new** = needs Lemma D;
**fails** = none found.

| estimate in the step | Balaban's role | conditional version | status |
|---|---|---|---|
| preliminary integrations [IV] (1.10)-(1.99) | build the multi-scale fluctuation variables `V''`, new regions `Z''_j` | untouched: they are already constrained and exact (p. 193); pp. 182-191 not read, relied on via p. 193 | same |
| `χ_{k,Λ}` and the extension argument (1.74)-(1.75) | regular `V_out` extends into `Λ` | unchanged; plus the `W` partition of 2.2 | same |
| Proposition 1 [IV], (1.78); proof [V] (1.12)-(1.13) | unique minimal orbit `V_Λ(V_out)`, regular, analytic | constrained minimizer `V̂_Λ(W, V_out)` for the two-scale determining set (scale `k` on `Z ∩ Λ^c`, scale `k+1` on `Λ`; coarser inside, the nesting Balaban's determining sets have). Proof: the fixed-point argument of (1.13) on `P_0 ∩ ker Q_{k+1}` (gauge plus block constraint); the operator is still positive there. Regularity `O(B5 M^5)(ε_k + ε_{k+1})`, analytic in `(W, V_out)` | constants (and the existence/uniqueness/decay of minimizers for that set, the kind of statement `[15]` provides; to be checked against `[15]`) |
| background `U_0`, (1.80); gauge (1.81)-(1.87); `χ''_k = 1`, (1.88)-(1.98) | regularity of the background on all scales `h..k` in `Λ` | same arguments with `U_0 = U_{k,Z}(V̂_Λ)`; block-axial instead of tree gauge in `Λ` | constants |
| the core inside a constrained block | (absent: Balaban's `V_k|Λ` is free, the core is decoupled from the background) | the blocks over the core have `W` fixed and `V_k` there is an average of core variables; the constraint must be solved by shell variables, analytically in `W`, uniformly in the core | **new (Lemma D, D1)** |
| linear term, [V] (1.2)-(1.6), (1.28)-(1.29) | `J_0 = 0` on `Λ` (unconstrained minimum) kills the term linear in the fluctuation | `J_0 = Q*_{k+1} λ` on `Λ` (Lagrange multiplier); every configuration in the integral lies on the constraint surface, so the linear term is `⟨Q B, λ⟩` = (core contribution + quadratic terms); Balaban already uses this form of the identity on `Z \ Λ` (p. 363) | same + Lemma D for the core contribution |
| quadratic form positivity (1.7)-(1.9) | lower bound `γ0 / (2d (100M)^5) ‖B'‖²` | restriction to `ker Q_{k+1}`: still positive; the block constraint gives a Poincare bound with `O(L^2)` instead of `(100M)^{d+1}` | constants (better) |
| denominator (1.10)-(1.11) | `exp[−g^{-2}A(ζ0,U_0) − I(U_0) + E_k(Λ)]`, `|I| ≤ O(1)M^5` | `D_X(W) = exp[−g_k^{-2} A(ζ0, U_0(W)) − Î(U_0(W)) + Ê_k(Λ)]`: now `W`-dependent (this is the "normalisation that depends on the fixed block field"), but analytic and non-zero for regular `W`; its Wilson term cancels against the numerator's exactly as before; `|Î| ≤ O(1) M^5` plus the δ-Jacobian, `O(log g_k^{-2})` per constrained bond | constants |
| localization [V] (1.14)-(1.69) | localize the dependence on `V_out` near `∂Z`; produce `V(Y, U_k)` with (1.68)-(1.69) | the same expansions; the new dependence on `W` inside `Λ` enters only through `U_0(W)` and (Lemma D) through analytic shell shifts, so it is localized in `Λ` (already a localization domain); pp. 364-373 not read | same (+ D1) |
| `T'_k(X)` (1.70)-(1.71) | normalised operation; normalisation constants `E_k(X)`, `(−½ d(g) log g^{-2} + log σ0)|B0 \ T0|` | `T̂'_k(X)` with `δ_Λ`; numerator and denominator constrain the same `V_k`-bonds, so the constants match up to `O(log g_k^{-2})` per coarse bond of `Λ`, which Balaban's per-step entropy `O(1) M^d R^{d+1} d'` already absorbs (`log g^{-2} ≤ R`) | constants |
| analytic extension (1.73)-(1.75) | real integrand positive, complex perturbation `e^σ`, `σ` small: `|T'(X,(U,J))F| ≤ T'(X)1 e^{sup|σ|} sup|F|` and the lower bound | holds verbatim once `(U, J)` (now including `W = M(U)` on `Λ`) enters only through backgrounds and analytic shifts; δ-functions are positive | new (D1), then same |
| large-field factors (1.76)-(1.79) | from characteristic functions of the integrand, the local Wilson action and positivity of quadratic forms; group integrals bounded by 1; Gaussian integrals by positivity; domain sums `exp O(1)(MR)^{-d}|Z|` | all factors are **pointwise** bounds on the integrand, so they hold on every fibre, uniformly in regular `W`; group integrals with a δ are bounded by the δ-Jacobian, `O(1)^{|Λ|}`; constrained Gaussians by positivity. Conditioning cannot make the old large field "forced", because numerator and denominator are bounded with the same `W` | constants |
| entropy induction (1.80)-(1.88) | numbers `κ_j(Z)`; a large-field factor pays `O(1) M^d R_n^{d+1} d'_n` for each later step it controls; win needs `p0² ≫ M^d R^{d+2}` | purely combinatorial (operation `S`, domains, sizes); per-step costs get an extra `O(1)` from the `W` partition and Jacobians, same form | constants |
| fundamental inequality (1.89) | `T'_k(X)1 ≤ exp(−2(1+β0)^{-1} p0(g_k))` | `sup_{W regular} N_X(W)/D_X(W) ≤ exp(−2(1+β0)^{-1} p0(g_k))` with changed constants inside | constants |
| fresh factor for a new large field over the core (branch (a)) | (absent: Balaban's resampled `V_k` is independent of the core) | if `W` is irregular over a block that contains the core, Theorem 1 of `[15]` only says some fine plaquette in the cube is large, and the core's old plaquette already is: no fresh factor without more information | **new (Lemma D, D2)** |
| polymer gas (1.90)-(1.97) | vacancy-1 gas `1 + ∑ ∏ F(X'_p)`, `|F| ≤ c1 exp(−(1+β)κ d(X'))` | same expansion; the activity of `X_j` depends on `W` on `Λ_j` and on `V_k` near `Λ_j`, i.e. on `U_k` restricted to the localization domain (`W = M(U_k)` there). Vacancy-1: the `n = 0` term is the untouched small-field term. Local: yes, on the same domains as Balaban's | same |
| exponentiation (1.98)-(1.100), new action (1.101) | `exp ∑ R''(X)`, `|R''(X)| ≤ exp(−p0) exp(−κ d_k(X))`, needs `2κ(100R_k)^d` small against `p0` (p. 389) | unchanged; R-terms are analytic in `U_k` on `Ũ^c_k(X, α0, α1)` given D1 | same |
| gauge-fixing removal, [V] p. 378 | reversed Faddeev-Popov, law changed (L3) | exact inside `T` (2.1) | same, and now exact |
| final form (1.102)-(1.104) | `Rρ_k` in the form [III] (2.18) | `R̂ρ_k` in the same form; `T R̂ρ_k` is the law; the next `T` step ([III] Sect. 3) treats the R̂-terms as functions of the background, like Balaban's | same |

Nothing in the table fails. Two rows need Lemma D; the rest is the same proof with changed constants (one row with
better constants).

## 3. Lemma D (core dilution)

**Why it is needed.** In Balaban's step the core `C` sits inside `Λ`, its variables are integrated without expansion,
and the background `U_0` does not depend on them; the core touches the rest only through the action. Under a block
constraint the blocks over `C` have `W` fixed, while `V_k` on those blocks is an average that includes the core
variables (which are far from the identity). Two things must then hold:
* (D1) the constraint `V̄_k = W` can be solved for **shell** fluctuation variables (outside `C`), with a solution
  analytic in `(W, V_out)` on the complex domain, uniformly in the core variables, and the forced shift small against
  the fluctuation threshold `δ'_k`; then `N_X(W)` is an integral of analytic functions of `W` against a positive,
  `W`-independent measure on the core, hence analytic, and (1.73)-(1.75) apply;
* (D2) if `W` is irregular over a block meeting `C`, then the same `W` computed with the core replaced by a regular
  filling is irregular too, so Theorem 1 of `[15]` finds a large plaquette **outside** `C`: a fresh factor on
  plaquettes disjoint from the old one.

**Statement (target).** Fix an extension of Balaban's averaging `M` to all configurations (measurable,
gauge-covariant, reflection-equivariant). There are `c < 1` and `C0`, depending only on `L` and `d`, such that: if a
configuration is regular (in the sense of the shell characteristic functions) outside a core of diameter at most
`100 M R_h` at scale `h` and arbitrary on it, then for `n ≥ n1 := log_L(200 M R_h) + 2` the plaquette variables of the
`n`-fold average over the core differ from those of the core-replaced configuration by at most `C0 π c^{n−n1}`.
Consequently, if `N ≥ n1 + log(C0 π g_k^{-2}) / log(1/c) = O(log g_k^{-2})`, (D1) and (D2) hold (the forced shift is
`≤ g_k² ≪ δ'_k`, and the core term in the linear-term identity of 2.3 is `≤ g_k^{-2} ε_{k+1} C0 π c^{N−n1} ≪ 1`).

**Why it should hold (sketch, mine).** (1) A coarse bond reads only two blocks ([I] (0.4)), so the set where the
averaged field feels the core shrinks by `L` per step to a fixed size of 2-3 cells after `n1` steps. (2) The coarse
plaquette variable is, through the averaging, an average over the contour family of holonomies of surfaces inside
the blocks; a fixed fine plaquette lies on a fraction `f` of these surfaces, about `1/L` in general and `O(1)` but
`< 1` when it sits at a block centre (for odd `L`, block centres of all scales coincide, so this case recurs at every
step); each loop contributes a Lie-algebra log of size at most `π`. (3) Iterating gives `π f^{n−n1}`. In the abelian
linear case this is exact arithmetic; the non-abelian case needs the average to be Lipschitz-robust to a fraction `f`
of outlier loops.

**The risk.** Balaban's averaging is specified by axioms near the identity ([I] (0.5)-(0.9)); how it acts on fields far
from the identity is not in the pages read (`BALABAN-READING.md` section 4). A formula with a fixed reference path
(the straight fine path along the coarse bond) and the principal log may fail the robustness in step (2) when the core
sits on that path. Since the small-field theory uses only the axioms, the extension can be **chosen** (any measurable,
covariant, equivariant one serves the law, and link reflection positivity only needs equivariance). So the risk is a
definition to fix, not an obstruction. If no admissible extension is robust, the verdict would move toward BREAKS at
exactly this point, because then the R-terms over the core cannot be analytic in the coarse field.

**Compatibility with Balaban's constants.** (D) needs `N ≳ log g_k^{-2}`. Balaban: `N > N0` with
`L^{N0−1} = R_{k−N0+1}`, `N ≤ O(1)(log g^{-2})^ν` with `½ν ≤ p0 − p1 − 1` ([IV] p. 198), `N ≥ (ν/log L) log log g^{-2}`
([V] p. 363), and in the induction (1.80) the controlled number of steps is `N = R_j ≥ (log g_j^{-2})^r`, `r ≥ 2`.
Taking `ν ≥ 1` (needs `p0 ≥ p1 + 3/2`) satisfies all of them. So the side conditions change, not the structure.

**Size.** About 8 pages: the contour geometry, the robust-average bound, the iteration, and the two corollaries. It is
the only genuinely new idea in M1, and it is elementary.

## 4. Verdict and size of M1

**Verdict: SURVIVES WITH A NEW LEMMA, Lemma D (core dilution under the block averaging), section 3.** The conditional
R step has the same structure as Balaban's: the same preliminary integrations, a constrained instead of a free
fluctuation integral on `Λ`, the same cancellation of the Wilson terms between numerator and denominator, the same
pointwise large-field factors, the same entropy induction, the same vacancy-1 gas and exponentiation. The densities are
the laws: `T R̂ = T` term by term, and the one other law-changing operation (gauge-fixing removal) becomes exact.

**M1 work list and size** (journal pages in Balaban's density):

| part | what | pages |
|---|---|---|
| setup | inductive assumptions of [III] Sect. 2 restated for laws; R-terms allowed to depend on `U_k` through `M(U_k)` on `Λ`; block-axial gauge; `T R̂ = T`; the `W` partition and branch (a) | 5 |
| Lemma D | statement, choice of the averaging extension, proof, D1, D2 | 8 |
| redo [IV] pp. 192-202 | constrained minimizer for the two-scale determining set (with the `[15]` statement it needs), regularity, gauge, (1.99)-(1.102) analogues | 10-12 |
| redo [V] pp. 355-363 | denominator, linear term via `J_0 = Q*λ`, quadratic form on `ker Q`, proof of the constrained Proposition 1 | 6 |
| redo [V] pp. 377-383 | `T̂'_k(X)`, matched normalisations, analytic extension with D1, large-field factors (1.76)-(1.79) under δ-constraints, (1.89) | 7-8 |
| check, expected unchanged | [IV] pp. 177-191 (preliminary integrations), [V] pp. 359-376 (localization, plus the `W`-dependence inside `Λ`), (1.80)-(1.88), (1.90)-(1.104) | about 40 pages to re-read line by line, little new text |

Total: **about 35-45 pages of new writing plus a careful check of about 40 pages**. That is "long but routine" plus one
medium-small new lemma, not a new method. It is less than redoing all 65 pages of [IV]-[V], because the preliminary
integrations are already law-preserving and the combinatorial half carries over.

**What this paper test does not settle.**
* [IV] pp. 182-191 and [V] pp. 364-373 were not read; the table assumes they use only properties listed in 2.3.
* Whether `[15]` covers the two-scale determining set in the form needed (expected: it is the standard kind of set,
  coarser inside, finer outside).
* That the other steps of the induction are exact. Checked only indirectly: the word "equivalent" occurs in the five
  papers only at (L1)-(L3); the `T` steps are pushforwards by definition, and the partitions are exact covers.
* [I] Theorem 2 (running coupling stays below `γ`) is still an unpublished input, independent of M1.

**For M2.** With R̂ and the branch-(a) choice of 2.2, every large-field label left after a step is either a current
large field (a function of the current block field) or a region created in the last `N` steps. That is the bad set M2
needs, now on the true law.

## 5. Next steps

1. **Lemma D first** (paper, one session): fix the averaging extension, prove the dilution bound, check the
   block-centre case and the non-abelian robustness. If it fails for every admissible extension, M1 is BREAKS at that
   point and needs a different renormalisation of the core (that would be the new idea).
2. Read the two unread page ranges and `[15]` (if obtainable) for the two-scale determining set.
3. Then M1 proper as in the work list, starting with the constrained Proposition 1 and (1.89).

## Files

- Here: `ONE-STEP.md` (this file). `LITERATURE.md` in this folder belongs to the parallel scoping session and was not
  touched. The PDFs stay in `../c5d-supplier/`, git-ignored; OCR text extracts were made in the session scratchpad
  only.
