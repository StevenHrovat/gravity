# What Balaban's normalisation terms E_k(Z) are, and what his large-field bounds keep (2026-11-22)

Independent reading of the primary sources, written before reading M1's use of them (the comparison section was
added afterwards). Sources, page numbers are journal pages:

* [I] CMP 109 (1987) 249-301; [II] CMP 116 (1988) 1-22; [III] CMP 119 (1988) 243-285;
* [IV] CMP 122 (1989) 175-202; [V] CMP 122 (1989) 355-392.

Method: page images rendered at 130 dpi and read directly for every equation quoted below; the OCR text layer was used
only to locate pages. Where an item rests on OCR only, it is marked "(OCR)". "Source states" means printed in the
paper; "I infer" means my derivation from what is printed.

Notation clash to keep in mind: [V] uses `E_k(Z)` ((1.70), normalisation and vacuum constants on the large-field
region) and `E_k(Λ)` ((1.10), only a Haar-Jacobian constant) for different objects, and `E_k(U)` ([III] (2.23)) for
the field-dependent regular part of the action. Below, `E_k(Z)` always means the (1.70) object.

---

## Q1. The normalisation terms E_k(Z) in [V] (1.70)-(1.71)

### Q1 (a) Definition

**Source states.**

1. [V] p. 377-378, just before and after (1.70): "Now we add all the missing terms with localization domains
   intersecting the domain Z, more exactly we add these terms to complete the effective action, and we subtract them
   from the remaining expression." The result is (1.70), whose integrand exponent ends with
   `... + E_k(Z) + (−½ d(g) log g_k^{−2} + log σ_0)|B_0 \ T_0| − E_k(Λ)`, and: "where `E_k(Z)` denotes the sum of
   normalization terms and vacuum energy terms with localizations intersecting the large field domain Z."
2. [V] (1.71): for each component X of Z, the new operation `T'_k(X)` is the integral over the bond field B on
   `(B_0 \ T_0) ∩ X` (with `σ(g_k B) δ_{rT}(B) χ'(X)`, averaged over the `2^d d!` axial-gauge trees rT), and over the
   older large-field variables `V_h` with their `T_h`-operations, of
   `exp[ −½⟨DH''B, ζ DH''B⟩ − A(ζ_1 Γ_X, U''_{h+2}(exp i g_k B, V'')/(g''_k)²) + V(X~, U_k) + E_k(X)
   + (−½ d(g) log g_k^{−2} + log σ_0)|(B_0\T_0) ∩ X| − E_k(Λ ∩ X) ]`.
   So `E_k(X)` sits inside each `T'_k(X)`, next to two explicit Jacobian constants.
3. [V] (1.10): `E_k(Λ) = (−½ d(g) log g_k^{−2} + log σ_0) |Λ^{(k)} \ G_0|`. It is the constant produced when the
   Haar integral `∫ dV' ...` over the small domain Λ (the denominator of the R-ratio (1.1)) is rewritten as a
   Lebesgue integral over `B'` with `V' = exp(i g_k B')`. Same constant, other set, in the numerator.
4. What "normalization terms" and "vacuum energy terms" are, from the small-field construction:
   * [I] (0.17), (0.19): each step is divided by a normalisation factor `N_k`, "the integral above with V = 1".
   * [I] (1.3)-(1.4): `A_k = −A(U_k)/g_k² + Σ_j { −β_{j+1} A + [log Z^{(j)}(U_k) − log Z^{(j)}(1)]
     + [E^{(j+1)}(g_j, U_k) − E^{(j+1)}(g_j, 1)] }`, with
     `Z^{(j)}(U) = ∫ dB δ(Q̃ B) exp[−½⟨B, Δ^{(j)}(U) B⟩]`, "the Gaussian integral normalizing the Gaussian measure
     for a fluctuation field in j-th step integration". This is the Gaussian integral over the fibre: fluctuation
     bonds, with the linearised block-average constraint `δ(Q̃B)`.
   * [I] (2.12)-(2.14): `E^{(k+1)}(g_k, U) = log ∫ dμ_{C^{(k)}}(B) χ_k exp[P^{(k)}(g_k, U, B) + {...}]` with the
     normalised Gaussian measure of covariance `C^{(k)} = (C* Δ^{(k)} C)^{−1}`, and `log N''_k = E^{(k+1)}(g_k, 1)`.
     So the value at background 1 of the non-Gaussian part is itself a normalisation constant.
   * [III] (1.14)-(1.16), first step: after the scaling `A = g_0 A'` and elimination of the δ-functions, the exponent
     carries the constants `log g_0 d(g) |Ω_1*| + log σ_0 |Ω_1*| − log z (L^4 − 1)|Ω_1^{(1)}| − E` and a factor
     `z^{(0)}` "obtained by integrating the δ-functions". `|Ω_1*|` = bonds of the small-field domain minus the bonds
     `b_0(c)` fixed by the block constraints; `z` comes from the exponential (axial) gauge fixing (1.5)-(1.6).
     (1.26) adds the Gaussian normalisation `Z^{(0)}(Λ_1)`.
   * [III] p. 254, after (1.30): "The constant E_1 is obtained from E by subtraction of all the constants which have
     appeared in the procedure, i.e., the constants in the first exponential in (1.15), and the constant
     `E^{(1)}(Λ_1, g_0, 1)`."
   * [III] p. 261: "The constant E_k ... is obtained by subtracting one-step vacuum energy expressions, generated in
     small field regions, from the initial constant E. This initial constant is defined in fact as a sum of all such
     expressions for all the lattices `T^{(k)}` as the small field regions."
   * [III] (3.33)-(3.38), general step: `log[z^{(k)} ∫ dA exp(−½⟨A, C*Δ^{(k)}CA⟩)] = Σ_c log z^{(k)}(c)
     − ½ log det(C*Δ^{(k)}C) + log ∫ dA exp(−½|A|²)`; the last number goes into the vacuum energy; the log det,
     the derivative of the characteristic functions, and the non-Gaussian term `g_k ∫_0^1 dt ⟨tr V'_k(t g_k, A, b)
     (CA)(b)⟩_t` are put together into the localised per-bond terms `E_0^{(k+1)}(Λ, U, b)` (3.37).
   * [III] p. 263, after (2.48): "the vacuum energy counterterm E_k, except the terms logarithmic in coupling
     constants, has the same bound as above" (O(1) per site); [V] p. 380: for the normalisation constants the bound
     carries `O(log g_j^{−2})` instead of `O(1)`.

**I infer.** `E_k(Z)` is the part, localised on domains that meet Z (at all scales j ≤ k), of Balaban's
field-independent constant bookkeeping. These are the logs of the one-step normalisation factors that the region
would have produced had it been small field at every step, evaluated at background `U = 1`:

* the Haar-to-Lebesgue Jacobian `g_j^{d(g)} σ_0` per integrated fluctuation bond (the "terms logarithmic in coupling
  constants"; `d(g) = 3` for SU(2));
* the gauge-fixing constant `log z` per site and the δ-elimination factors `log z^{(j)}(c)` per block (the
  block-average constraint `δ(Q̃B)`);
* the constrained Gaussian determinant `log Z^{(j)}(1)` (the fibre Gaussian at background 1), localised;
* the non-Gaussian vacuum values `E^{(j+1)}(g_j, 1) = log N''_j`, including the characteristic-function corrections.

The variables are the scale-j fluctuation bonds of the fibre (all bonds minus the `b_0(c)` solved from the
linearised block constraint), Lie-algebra valued after the scaling by `g_j`. The constraints are the block-average
δ-functions and the axial/exponential gauge fixing. The characteristic functions are the small-field ones. Nothing
in `E_k(Z)` depends on the field.

**Cannot read.** The sign convention of `E_k(Z)` relative to the constant `−E_k` of [III] (2.23). The text adds the
terms to the action and "subtracts them from the remaining expression", which puts `+E_k(Z)` inside `T'_k`. Balaban
bounds only `|E_k|`, so the sign does not affect any bound below.

### Q1 (b) How they arise

**Source states**, in order:

1. Small-field steps create the constants and subtract them from the initial `E`: [I] (0.17)-(0.19), (1.3)-(2.14);
   [III] (1.14)-(1.30), (2.23), p. 261, (3.27)-(3.38).
2. On a large-field region the step integrals are not done; those constants are missing there and stay inside the
   global constant `E_k`.
3. [IV] (0.2)-(0.6) gives the design of the R-operation: a large-field term `ρ(Z, V)` is replaced by the small-field
   term `ρ(Z'', V)` times the ratio `∫dV_{Z'} ρ(Z, V) / ∫dV_{Z'} ρ(Z'', V)`, "in such a way, that integrals of the
   densities are unchanged" ((0.4)).
4. [IV] (1.99)-(1.102) and [V] (1.1): R' carries, per small component Λ_i, a ratio with denominator
   `∫ dV' Γ_Λ δ_{G_0}(V') χ exp[−A(ζ_0, U_{k,Z}(V'V_Λ))/g_k²]`. [V] (1.2)-(1.11): this denominator equals
   `exp[−A(ζ_0, U_0)/g_k² − I(U_0) + E_k(Λ)]` with `|I(U_0)| < O(1) log M |Λ| < O(1) M^5` ((1.11)).
5. [V] p. 377: the action is completed on Z by "the missing terms with localization domains intersecting Z". Their
   field-dependent parts go into `V(Y)`, `V(X~)` (bounds (1.68), (1.69)); their constant parts are `E_k(Z)`
   in (1.70).
6. [V] (1.71) factorises this over components X into `T'_k(X)`, each carrying `E_k(X)`; (1.72) defines R.

**I infer.** `T'_k(X)` is the R-ratio of [IV] (0.3) written out. It is (large-field integral over the variables of
X) times the inverse of the small-field normalisation constants of X, together with the Jacobians that convert the
Haar integrals to Lebesgue integrals.

### Q1 (c) Is it the Gaussian fibre normalisation of the small-field alternative?

**Source states.** No identity of this kind is printed. The text calls them "normalization terms and vacuum energy
terms", and the only quantitative statement is the absolute bound in (d).

**I infer.**

1. **Not purely Gaussian.** `E_k(Z)` is the log of the full small-field normalisation at background 1, not only of
   the Gaussian `Z^{(j)}(1)`. Besides the constrained Gaussian determinant it contains:
   * the Haar Jacobians;
   * the gauge-fixing and δ-elimination constants;
   * the non-Gaussian vacuum values `E^{(j+1)}(g_j, 1)`.
2. **The β^{3/2}-per-bond factor is inside it.** The constant `−½ d(g) log g_j^{−2} + log σ_0` per integrated bond is
   `σ_0 g_j^{d(g)}`, that is `β_j^{−3/2}` per bond for SU(2) with `β = g^{−2}`. It converts the Haar measure of
   `exp(i g B)` into `dB`, and it belongs to `E_k(Z)` by construction (it is among "the constants in the first
   exponential in (1.15)"). The same constant appears explicitly twice in (1.70)-(1.71): once for the numerator bonds
   `B_0 \ T_0`, and once as `−E_k(Λ)` for the denominator bonds. So relative to a normalisation measured in the same
   Haar measure, no `β^{3/2}` factor is left over. Relative to a Lebesgue-normalised Gaussian there is exactly a
   factor `σ_0 g^{d(g)}` per integrated bond, and it is part of `E_k(Z)` itself.
3. **Leftovers against "the Gaussian fibre integral on the region"**, if that integral is taken in the same Haar
   measure with the same gauge fixing:
   * the non-Gaussian vacuum values: O(1) per site by the stated bounds, plausibly `O(ε_j) = O(g_j p_0(g_j))` per
     site from the O(ε)-coefficient form of `P^{(k)}` ([I] p. 269); this is not stated as a bound;
   * the terms of domains that straddle ∂Z (they are "intersecting Z", not "contained in Z"): O(1) or
     `O(log g^{−2})` per site of a boundary layer, decaying with κ;
   * the characteristic-function corrections, exponentially small in the small-field cut.

   So the identification holds up to `e^{O(δ_j)|region| + O(|∂ region|)}` with `δ_j` inferred, not stated.
4. **Balaban never needs the identity.** He never compares `E_k(Z)` with an actually computed fibre integral on Z. He
   only bounds `|E_k|` crudely, see (d).

### Q1 (d) Where and how they are bounded

**Source states.** [V] p. 380, inside the bound on `T'_k(X)1 := T'_k(X, (U, 0))1`: "The expression `V(X~)` is
bounded in (1.69). Similar bounds hold for vacuum energy counterterms and normalization constants, except that for
the last we have the corresponding constant `O(log g_j^{−2})` instead of `O(1)`. In effect we get a bound, to which
every large field domain `Z_j` contributes the constant
`O(1) log g_j^{−2} |Z_j| ≤ O(1) log g_j^{−2} (M R_j)^d d'_j(Z_j) ≤ O(1) M^d R_j^{d+1} d'_j(Z_j)`."

Then:
* "All the integrals with respect to the group valued variables in the definition (1.71) are estimated by 1. Similar
  to the integral with respect to B, we have to include only the constant with the logarithms in the last line into
  the integration measure, and we estimate the quadratic form in B from below by 0." ([V] p. 383)
* Result (1.79): `T'_k(X)1 ≤ sup exp{Σ_j O(1) M^d R_j^{d+1} d'_j(Z_j)} · Π_j Π_i exp(−½ γ_0 A_1² p_0²(g_j)
  (d'_j(Z_j^{(i)}) + 1) − 2 p_0(g_j)) · Π' exp(−p_0(g_j))`.
* The lower side: (1.74) and the remark after it, "`T'_k(X, (U, 0))1` is obviously positive, although it may be very
  small". Only positivity is used, to divide in (1.75).
* For the Λ-denominators (not `E_k(Z)`): the lower bound `≥ exp(−O(1)|Λ|) = exp(−O(M^4))` ([V] p. 358) and
  `|I(U_0)| < O(1) log M |Λ|` (1.11).

**I infer.**
* `E_k(Z)` is a number, so "pointwise" is trivial. The bound is two-sided in absolute value:
  `|E_k(Z_j-part)| ≤ O(1) log g_j^{−2} |Z_j|`, that is `O(log g_j^{−2})` per scale-j site and
  `O(M^d R_j^{d+1})` per `M R_j`-cube.
* It is used only in an upper bound for `T'_k`. There it is paid with the large-field factor `p_0²(g_j)` per
  `M R_j`-cube.
* No lower bound of the form "fibre integral ≥ e^{−δ|region|} × normalisation" appears anywhere in [IV] or [V].

---

## Q2. What the entropy induction [V] (1.80)-(1.89) keeps

**Source states.**

* **Creation factor**, per large-field component `Z_j^{(i)}` (cover by `M R_j`-cubes), p. 381:
  `exp(−γ_0 min{½ B_3^{−2} A_0², 2 A_1², A_1²} p_0²(g_j)(d'_j + 1)) ≤ exp(−½ γ_0 A_1² p_0²(g_j)(d'_j(Z_j^{(i)}) + 1)
  − 2 p_0(g_j))`, with `γ_0` an absolute constant ("we may take γ_0 = 1/2"). So at birth the gain is of order
  `p_0²(g_j)` per unit of linear size `d'_j`, measured in `M R_j`-cubes, plus `2 p_0` per component.
* **Costs.** The normalisation constants cost `O(1) M^d R_j^{d+1} d'_j(Z_j)` per step (p. 380).
* **The induction.** p. 384, (1.80): for a component Z, writing its factor as `exp(−κ_j(Z) − 2 p_0(g_{j(Z)}))`, the
  statement is `κ_j(Z) ≥ Σ_{n=j+1}^{j+K} O(1) M^d R_n^{d+1} d'_n(S^{n−j}(Z))`, where K is the number of further steps
  until `S^K(Z)` satisfies conditions (i), (ii). (1.81) bounds the right side by
  `O(1)(64)^d M^d L^{d+1} R_j^{d+2}(d'_j(Z) + 1)`. (1.82):
  `κ_1(Z) ≥ ¼ γ_0 (14)^{−d} A_1² p_0²(g_1)(d'_1(Z) + 1) − O(1) M^d R_1^{d+1} d'_1(Z)`, valid "if
  `¼ γ_0 (14)^{−d} A_1² p_0²(g_1) ≥ O(1) 2(64)^d M^d L^{d+1} R_1^{d+2}`. This condition is satisfied for p_0 large,
  and g_1 sufficiently small."
* **No new large field.** (1.83) `κ_{j+1}(Z) = κ_j(Z_0) − O(1) M^d R_{j+1}^{d+1} d'_{j+1}(Z)`.
* **Merging.** (1.85)-(1.88): the surplus `2p_0(g_{j(X)}) + 2p_0(g_{j(Y)}) − 2p_0(g_{j(Z)}) ≥ 2(1+β_0)^{−1}
  p_0(g_{j+1})` pays the merging cost `O(1) 2d M^d R_{j+1}^{d+1}`.
* **Conclusion (1.89)**, p. 387: "the domain X in the definition (1.71) satisfies the assumption of the statement with
  K = 0, therefore `κ_k(X) ≥ 0`, and we have the fundamental inequality
  `T'_k(X)1 ≤ exp(−2(1+β_0)^{−1} p_0(g_k))`." Then: for an arbitrary large-field region "an improved bound (1.89),
  with the additional term `−κ_1 d_k(X)` in the exponential".
* **Polymer activities** (1.92)-(1.97):
  * each `T'_k(X_{j_h})` contributes `exp(−2(1+β_0)^{−1} p_0(g_k) + 1)`;
  * after paying `2κ(100 R_k)^d` per factor (condition `−2(1+β_0)^{−1} p_0 + 1 + 2κ(100R_k)^d ≤ −(3/2) p_0`),
    `exp(−q · ½ p_0)` remains for q factors, and it is spent on the sum over q and the component positions (1.96);
  * (1.97): `|F(X')| ≤ c_1 exp(−(1+β) κ d_{k,∪Y_i}(X'))`, where `c_1 = exp(−p_0(g_k))` if X' does not meet the
    `Y_i`, else `c_1 = α^{1/3}`;
  * (1.100): `|R''^{(k)}(X)| ≤ exp(−p_0(g_k)) exp(−κ d_k(X))`.
* **Units.** `d_k` is the linear size in M-cubes ([I] p. 257); `d'_j` is the linear size in `M R_j`-cubes.

**Answer.**
* As stated, the final large-field activities keep `p_0` **once per polymer** (`c_1 = e^{−p_0(g_k)}`) and `κ` per
  unit of linear size in M-cubes.
* `κ` is a fixed constant, independent of g.
* No per-`M R_j`-cube factor `e^{−c p_0}` (or `e^{−c p_0²}`) is stated in (1.89), (1.97) or (1.100).
* The per-cube `p_0²` gain exists at creation and is converted into `κ_j(Z)`. The induction only asserts that
  `κ_j(Z)` covers the future normalisation costs, and at the end it uses `κ_k(X) ≥ 0`.

**I infer.**
* The slack is there and could be kept. The creation gain `¼ γ_0 (14)^{−d} A_1² p_0²(g_j)(d'+1)` exceeds the total
  future cost `O(1)(64)^d M^d L^{d+1} R_j^{d+2}(d'+1)` by a factor that grows like a power of `log g_j^{−2}`
  (Balaban's own condition after (1.82)).
* So a strengthened induction hypothesis, `κ_j(Z) ≥ Σ(costs) + c · p_0²(g_{j_birth}) (d'_{j_birth} + 1)` with for
  example `c = ⅛ γ_0 (14)^{−d} A_1²`, should go through (1.83)-(1.88) unchanged: the merge step only adds, and
  (1.83) only subtracts costs that are already counted.
* The kept margin is counted in **birth-scale** cubes. Measured in current-scale cubes the region shrinks, since
  `d'_n(S^{n−j}(Z)) ≤ 2^{−(n−j)} d'_j(Z)` for `n − j > 1`.
* It would then have to be carried through (1.92)-(1.97) in place of the bare `e^{−q p_0/2}`.
* This is a re-proof, not a citation. The constant available at creation is `c ≈ ¼ γ_0 (14)^{−d} A_1²` on
  `p_0²(g_j)`, per unit of `d'_j`, less the costs. On `p_0` itself, the only stated constant is
  `2(1+β_0)^{−1}`, per component.

---

## Q3. Can the decay rate κ be taken large for a given L, and at what cost?

**Source states.**
* [I] Theorem 3 (p. 264): "There exist positive constants `κ_0, M(κ), γ, ε_0, ε_1, α_0, α_1` such, that if
  `κ ≥ κ_0`, `M ≥ M(κ)`, `0 < g_k ≤ γ` ..., then ... satisfy all the inductive assumptions. The constants
  `ε_0, ε_1, α_0, α_1` depend on M ... The constant γ depends on all other constants." (1.18) holds "for
  `M ≥ M(κ)`, γ sufficiently small".
* [I] p. 257 (OCR): "L is an odd, positive integer > 11" (lower bound read from OCR only), `M = L^m`.
* [II] p. 21:
  * the Gaussian part `log Z^{(k)}(U_{k+1})`, localised by the random-walk expansion, decays with "κ replaced by
    `δ_0 M`", "and we take M sufficiently large, so that `δ_0 M ≥ κ`";
  * the rate is kept from scale to scale by `(1 − 10δ)·½L = 1`, `δ = (1/10)(1 − 2L^{−1})`, which fixes δ by L and
    not by κ;
  * [II] (2.37)-(2.41) need `2(L+2)^4 O(1) ε_2 exp(5κ) ≤ 1` and carry `C_3 = 2(L+2)^4 O(1) 2E_0 C_1 α_4^{−1}
    α_6^{−1} M^q exp(C_2 κ_1)`, so κ costs smallness of ε, hence of g.
* [III] p. 260, after (2.31): "Here κ_0 can be chosen arbitrarily large, similarly as κ, if the other parameters are
  fixed properly, as in [I]."
* [V]:
  * (1.94): `O(1) α^{1/3} ≤ 1 ≤ βκ/(6·2^d)` "for κ large enough" (κ has a lower bound here);
  * p. 389: g_k small so that `−2(1+β_0)^{−1} p_0(g_k) + 1 + 2κ(100R_k)^d ≤ −(3/2) p_0(g_k)`, that is
    `p_0(g_k) ≳ 8 κ 100^d R_k^d`;
  * (1.68): α "can be chosen arbitrarily small for γ small enough".

**Answer.**
* "κ large for given L" is **stated**: κ ≥ κ_0 is free.
* The cost is paid in M and in the coupling bound:
  * larger κ forces larger M (`M ≥ M(κ)`, explicitly `δ_0 M ≥ κ` for the Gaussian part; with L fixed this means a
    larger exponent m in `M = L^m`);
  * larger M forces smaller `ε_0, ε_1, α_0, α_1`;
  * all of these, and the conditions `ε e^{5κ} ≲ 1` and `p_0(g) ≳ κ R^d`, force a smaller coupling bound γ.
* `R_j ≥ (log g_j^{−2})^r` and `p_0(g) = A_0 (log g^{−2})^{p_0}` are not changed by κ. The κ-condition on `p_0(g)`
  is met by taking g small, since `p_0(g)` and `R^d` are both powers of `log g^{−2}`; this needs `p_0 > r d` in the
  exponents, or g small enough at equal exponents with `A_0` large.
* **Naming caution.** In Balaban, `γ_0` is the absolute positivity constant of the quadratic forms ([V] p. 380, "we
  may take γ_0 = 1/2"); κ does not touch it. The coupling bound is γ. So: larger κ means larger M and smaller γ,
  not smaller `γ_0`.

**I infer.**
* For M1's use, "a fixed condition on κ" is legitimate only if the constant it is compared with does not itself grow
  with κ or M.
* In (1.97) the prefactor is `c_1` (`e^{−p_0}` or `α^{1/3}`, and α shrinks with γ), so the rate condition is
  self-consistent.
* Any M1 constant that hides `e^{O(κ)}` or `M^q` (like Balaban's `C_3`) must be checked against the same κ.

---

## Q4. Size of the non-Gaussian part of the small-field action per site

Kept separate from Q1 (c): Q1 asks what `E_k(Z)` is; Q4 asks how small the field-dependent non-Gaussian remainder is.

**Source states.**
* [I] (1.3)-(1.4): the Gaussian part `log Z^{(j)}(U) − log Z^{(j)}(1)` is separated from the non-Gaussian
  `E^{(j+1)}(g_j, U) − E^{(j+1)}(g_j, 1)`.
* [I] (2.13)-(2.14) and p. 268: "the expression under the exponential above vanishes at `g_k = 0`".
* [I] p. 269: `P^{(k)}` (the expansion of the action and measure, without the old E-terms) "is bounded by a second
  order polynomial in B, with coefficients of the order `O(ε_1)`".
  * In [I], `ε_1` is the fixed small cut `|B'(b)| < ε_1` ((2.9)), depending on M (Theorem 3), not g-small.
  * In [III], [V] the corresponding cut is `ε_j = g_j A_0 (log g_j^{−2})^{p_0} = g_j p_0(g_j)` ([III] (2.4)).
* The old E-terms enter the new integrand through `{E_k(U_k(exp i[g_k CB − ...] V^{(k)})) − E_k(U_k(V^{(k)}))}`
  ([I] (2.12)). They are controlled only through analyticity: `|E^{(j)}(X, ...)| ≤ E_0 e^{−κ d_j(X)}` on the space
  `U^c_j(X, α_0, α_1)` ([I] (1.18)).
  * In [I], `α_0, α_1` are constants depending on M.
  * In [III] (2.28) (OCR): `α_{0,j} = g_j C_0 (log g_j^{−2})^{q_0}`, `α_{1,j} = g_j C_1 (log g_j^{−2})^{q_1}`, with
    `q_0, q_1` "integers greater than 1, C_0, C_1 sufficiently large".
* Stated size of the field-dependent part ([III] Theorem 2, (2.43)-(2.49)):
  * `|Σ_z [E^{(j)}(Λ_j, U_k, z) − E^{(j)}(Λ_j, 1, z)] − β_j A(φ, U_k)| ≤ E_1 Σ_n (L^{j−n})^β |Γ_n ∩ Ω|`;
  * `|E_k(U_k)| ≤ E_1 (1 − L^{−β})^{−1} Σ_n |Γ_n|`;
  * (2.49): `A_k = −A(1/g², U_k) + (logarithmic terms) + O(1) Σ_j |Γ_j|`.

  That is O(1) per site, with no g-smallness.
* [V] (1.2): in the R-denominator, the cubic-and-higher remainder "`V(ζ_0, g_k H_{1,k} B')/g_k²` is small, because
  the function V is at least of third order in the argument. It can be estimated by `O(g_k^{1−β}) |Λ|`" (with
  `|B'| < M_0 g_k^{−1} ε_k`). This is a stated per-site cubic bound of order `g · polylog`, the same shape as the
  reviewer's `g p³`.
* Balaban's own lower bound for a Gaussian-type integral keeps a loss of `O(log M)` per site: `|I(U_0)| < O(1) log M
  |Λ|` ((1.11)).

**Answer.**
* The source gives no bound `δ_j` per site with `δ_j (M R_j)^d → 0` for the non-Gaussian, field-dependent remainder
  of the small-field action. The stated bounds are O(1) per site (Theorem 2), or O(1) per M-cube for a single
  E-term ((1.18)).
* The explicit higher-order terms of the Wilson action and measure are small:
  * stated in [V] (1.2) as `O(g^{1−β})` per site;
  * inferable for `P^{(k)}` as `O(ε_j) = O(g_j p_0(g_j))` per site;
  * either way `δ_j (M R_j)^d → 0`, since `R_j` and `p_0(g_j)` are powers of `log g_j^{−2}`.
* The inherited E-terms' dependence on the fluctuation and on a small-field background is controlled in the source
  only by analyticity.
  * A Cauchy estimate gives a second-order variation of about `E_0 (ε_j / α_{0,j})² ≈ (A_0/C_0)²
    (log g_j^{−2})^{2(p_0 − q_0)}` per M-cube (first order vanishes by gauge invariance at background 1).
  * Per `M R_j`-cube this is multiplied by `R_j^d`, so it tends to 0 only if `2(q_0 − p_0) > r d`. This is the
    reviewer's condition, with `q_0` from [III] (2.28) and `p_0` the exponent in `ε_j`.
* `q_0 ≥ p_0` is forced: the analyticity domain must contain the small-field configurations, `|U − 1| ≲ ε_j`.
* No relation `q_0 > p_0 + r d/2` is stated in what I read. The stated relations are:
  * `q_0, q_1 > 1`;
  * `r ≥ 2` ([III] p. 245, OCR);
  * `2p_1 − (d+5) r_0 > p_0` ([V] p. 383);
  * `A_1² p_0²(g) ≳ M^d L^{d+1} R^{d+2}` ([V] after (1.82)).

  Whether the E_0-bound of [I] survives on the larger domain that `q_0 > p_0 + rd/2` needs, I cannot decide from the
  scans. [I] itself uses fixed `α_0`, which would make the Cauchy route trivially small. So the question is whether
  [III]'s g-dependent `α_{0,j}` is forced or only convenient, and the text does not say.
* **Verdict on Q4.** The reviewer's diagnosis is correct in form. The source does not settle it, and a write-out is
  needed: either take the inherited E-terms on the fixed-size domain of [I], or check the exponent relation.

---

## Comparison with M1's reading (UV-TV.md 12.1, 24, 25)

M1's reading has two halves (25):
* (R1) "Balaban's normalisation terms `E_k(Z)` ((1.70)-(1.71)) are the Gaussian fibre normalisations of the
  small-field alternative";
* (R2) "the small-field alternative's fibre integral is `≥ e^{−δ|region|}` times them", `δ_j (M R_j)^d → 0`.

It uses them in:
* 12.1 / 24.1: the numerator by (1.89) or (1.97), the denominator by (R2), and the ratio with no leftover
  `(β^{3/2})^{#bonds}` by (R1);
* H2a and R10.

**R1: matches in substance, differs in wording.**
* `E_k(Z)` is the small-field alternative's normalisation **and vacuum-energy** constants at background 1:
  * Gaussian determinant;
  * Haar Jacobians;
  * gauge-fixing and δ-elimination constants;
  * non-Gaussian vacuum values,

  localised on domains meeting Z. "Gaussian" is too narrow, and "with localizations intersecting Z" includes a
  boundary layer.
* The identity is not printed; it follows from Balaban's bookkeeping ([III] p. 254, p. 261; [I] (0.17), (2.14)).
* The `β^{3/2}`-per-bond factor is not a leftover. It is the Haar Jacobian `σ_0 g^{d(g)}` per bond, it is part of
  `E_k(Z)`, and Balaban pays it inside (1.79), so (1.89) already includes it.
* So M1's numerator step ("each bounded by `e^{−2(1+β)p_0 − κd}` ((1.89), with Balaban's normalisation constants
  O(1) log g^{−2} per site included)") is a correct use of the source. The bound in (1.89) is on the ratio "large-field
  integral / small-field normalisation constants" as Balaban defines it.

**R2: not in the source.**
* Balaban proves no lower bound of the form "fibre integral ≥ e^{−δ|region|} × normalisation".
* For the small-field action the stated bounds put the field-dependent part at O(1) per site ([III] Theorem 2),
  which gives `e^{−C (M R_j)^d}` per `M R_j`-cube. His only Gaussian-type lower bound ((1.10)-(1.11)) loses
  `O(log M)` per site.
* `δ_j → 0` is plausible: the explicit cubic terms are `O(g^{1−β})` per site, stated in [V] (1.2). It is not stated
  for the inherited E-terms (Q4) and needs a write-out.
* M1's own text in 12.1 used O(1) per cube and needed `p_0 ≫ w_j^d`. The refinement to `δ_j` in 24.1 is exactly the
  step that is not in the source.

**Consequences for M1's uses.**
* **Pointwise lower bound for a fibre normalisation (12.1, 24.1, step "denominator").**
  * Not citable with `δ_j → 0`.
  * With the source as printed, the loss is `e^{−C(M R_j)^d}` per cube. Rate κ per cube cannot absorb it, as M1 25
    says.
  * The β^{3/2} worry is not the problem; the O(1)-per-site non-Gaussian, field-dependent remainder is.
* **Conditional Peierls bound (24.1).**
  * Holds as written only given R2.
  * Without R2 it needs a per-cube margin `≥ C(M R_j)^d` in the exponent.
* **Unconditional large-set bound (H2a, 23.1 / 24.1).**
  * Same dependence: its denominator is the law's normalisation one scale up, which is the same kind of
    small-field-alternative fibre integral.
  * R10's scale-K normalisation (13.3) inherits the same status. I did not re-read R10.

**The fallback (25): "a per-cube margin `e^{−c p_0}` surviving Balaban's entropy induction".**
* **Not stated.** (1.89), (1.97) and (1.100) keep `p_0` once per component or polymer and κ per unit length.
  M1 25 says the same.
* **Plausible by inference, with a stronger margin than M1 asks for.** At creation the gain is `p_0²(g_j)` per
  `M R_j`-cube, not `p_0`. The induction consumes at most `O(1) M^d L^{d+1} R_j^{d+2}` per cube, and Balaban's
  condition after (1.82) makes the creation gain exceed that. So a strengthened induction keeping
  `c p_0²(g_{birth})` per birth-scale cube looks routine (Q2).
* That margin absorbs both the O(1)-per-site denominator loss `C(M R_j)^d` and any `(M R_j)^d log β`.
* **Two corrections to M1's wording.**
  * The relevant Balaban condition is on `p_0²`: `A_1² p_0²(g) ≳ M^d L^{d+1} R^{d+2}`, not "`p_0 ≫ M^d R^{d+1}`".
  * The margin lives in birth-scale cubes and must be carried through the polymer step (1.92)-(1.97), which
    currently spends the extra `e^{−q p_0/2}` on entropy.

---

## Verdict

* **What E_k(Z) is (R1): correct in substance, inaccurate in wording, inferred not cited.**
  * `E_k(Z)` is the logged normalisation and vacuum-energy constants of the small-field alternative at background 1:
    Gaussian constrained determinant plus Haar Jacobians, gauge-fixing and δ-elimination constants, and the
    non-Gaussian vacuum values, localised on domains meeting Z.
  * The β^{3/2}-per-bond Haar Jacobian is part of it, and Balaban's (1.89) already pays it. No leftover
    `(β^{3/2})^{#bonds}` arises in M1's numerator.
* **The pointwise lower bound with δ_j → 0 (R2): not in the source.**
  * The stated bounds give O(1) per site for the field-dependent small-field terms, so `e^{−C(M R_j)^d}` per cube.
  * `δ_j → 0` is plausible for the explicit cubic terms (`O(g^{1−β})` per site, [V] (1.2)). For the inherited E-terms
    it needs either the fixed analyticity radius of [I] or an exponent relation like `2(q_0 − p_0) > r d`, which is
    not stated (Q4).
  * So M1's single point of failure is R2, not R1, and it is **undecidable from these sources**.
* **The fallback: not stated, but holds by a routine-looking strengthening (inference).**
  * The per-cube large-field gain at creation is `p_0²(g_j)` per `M R_j`-cube. Balaban's induction spends only
    `O(M^d L^{d+1} R^{d+2})` of it, and his own conditions leave a surplus of order `p_0²` per birth-scale cube.
  * Keeping that surplus in the induction (1.80)-(1.88) and in the polymer bound (1.92)-(1.97) would absorb the
    O(1)-per-site denominator loss, and with it the need for R2.
  * It is a re-proof of [V] (1.80)-(1.97) with a retained slack term, to be written out; it is not a citation.
* **κ (Q3).** Large κ for fixed L is stated ([I] Theorem 3, [III] p. 260), at the cost of `M ≥ M(κ)`
  (`δ_0 M ≥ κ`) and a smaller coupling bound γ. It does not touch `γ_0`, which is an absolute constant.

---

## Re-proof check: UV-TV.md section 26 (the kept slack in [V] (1.80)-(1.97))

Checked against the page images of [V] pp. 380-390 and [III] p. 255, read for Q2 above. M1's slack is written `σ`
below as in section 26. **Naming clash:** Balaban already uses `σ` for the small first-order term in (1.73)-(1.75),
and `σ_0` in the Haar density. Renaming M1's slack (for example `s_j(Z)`) would avoid misreadings.

**The structural point, which settles most of the checklist.**
* *Source says.* (1.79) is the only analytic inequality in [V] pp. 380-387. Everything after it, (1.80)-(1.88),
  is bookkeeping on the exponent of (1.79): "If Z is a component of Z_j ... we write the factor connected with Z in
  the form `exp(−κ_j(Z) − 2p_0(g_{j(Z)}))`" (p. 384). The κ's are names for partial sums of creation gains minus
  normalisation costs.
* *Source says.* The costs are charged at three places only:
  * the current-step cost `O(1) M^d R^{d+1} d'` subtracted in (1.82), (1.83), (1.85);
  * the future costs, which (1.80) requires κ to cover;
  * the merging cost `O(1) 2d M^d R^{d+1}` in (1.87), paid with the p_0 surplus.
* *I infer.* Splitting a creation gain into a part that enters κ and a part kept aside is a relabelling of the same
  exponent. It is legitimate exactly when the κ-part alone still satisfies every inequality that Balaban proves about
  κ. Each item below checks that.

### 1. Halving the first term of (1.82)

* *Source says* (p. 385):
  * `Π_i exp(−½ γ_0 A_1² p_0²(g_1)(d'_1(Z_1^{(i)}) + 1)) ≤ exp(−¼ γ_0 (14)^{−d} A_1² p_0²(g_1)(d'_1(Z) + 1))`;
  * (1.82) `κ_1(Z) ≥ ¼ γ_0 (14)^{−d} A_1² p_0²(g_1)(d'_1(Z) + 1) − O(1) M^d R_1^{d+1} d'_1(Z)`;
  * "the statement holds for j = 1 ... if `¼ γ_0 (14)^{−d} A_1² p_0²(g_1) ≥ O(1) 2(64)^d M^d L^{d+1} R_1^{d+2}`.
    This condition is satisfied for p_0 large, and g_1 sufficiently small."
* *I infer.* **Legitimate.** The `(d'+1)`-proportional gain is split into two non-negative parts. The κ-part
  satisfies (1.80) under (P0), Balaban's condition with the constant doubled.
  * (P0) holds by the same argument, for g small at unchanged exponents: it needs `2p_0 > r(d+2)` in the
    `log g^{−2}` exponents, which his condition already requires.
* *Minor.* (1.85), p. 386, prints the new regions' term as `γ_0 A_1² p_0²(g_{j+1})(d'_{j+1} + 1)`, without the ½ of
  the creation factor on p. 381 (min{...}, then `≤ ½ γ_0 A_1² ...`). That is a factor-2 inconsistency in the source;
  the safe choice is ½. M1's step 5 copies the printed γ_0, and should use ½. It only moves constants inside (P0).

### 2. Does the tree argument (1.86)-(1.88) use only κ and the p_0 surplus?

* *Source says* (pp. 386-387):
  * (1.86) is an identity obtained by applying the additive definition (1.85) to the leaf X and the rest Y:
    `κ_{j+1}(Z) = κ_{j+1}(X) + κ_{j+1}(Y) + 2p_0(g_{j(X)}) + 2p_0(g_{j(Y)}) − 2p_0(g_{j(Z)})
    + O(1)M^dR^{d+1}(d'(X) + d'(Y) − d'(Z))`;
  * then `d'(X) + d'(Y) + 2d ≥ d'(Z)` and `2p_0(g_{j(X)}) + 2p_0(g_{j(Y)}) − 2p_0(g_{j(Z)}) ≥ 2(1+β_0)^{−1}
    p_0(g_{j+1})` give (1.87);
  * (1.88) closes with `≤ κ_{j+1}(Z) − 2(1+β_0)^{−1} p_0(g_{j+1}) + O(1)3(100M)^d R_{j+1}^{d+2} ≤ κ_{j+1}(Z)`
    "for p_0 large and γ small enough";
  * the single-domain vertices are covered by (1.83) or "the first induction step", that is (1.82) at scale j+1.
* *I infer.* **Yes.**
  * (1.86) stays an identity when (1.85) is redefined with half the new-region gain, since the halved definition is
    still additive over vertices.
  * (1.87) and (1.88) use only the parts' κ, the d'-subadditivity and the per-component `2p_0` surplus.
  * The new-region vertices use (1.82) at scale j+1, hence (P0).
  * σ appears nowhere.
* *Side remark.* (1.88) itself needs `2(1+β_0)^{−1} p_0(g) ≥ O(1)3(100M)^d R^{d+2}`, a condition on `p_0` (not
  `p_0²`) with `R^{d+2}`. Balaban's chain therefore already forces the exponent relation `p_0 > r(d+2)`. This
  matters for item 5.

### 3. Do (1.92)-(1.96) use `κ_k ≥ 0` in a way that would need σ?

* *Source says* (pp. 387-389):
  * `κ_k ≥ 0` is used once, to obtain (1.89) from (1.80) with K = 0;
  * (1.92) then uses (1.89) per factor `T'_k(X_{j_h})`, plus (1.68) and `|σ| ≤ 1` from (1.73);
  * (1.93) produces the cost `Π_h exp((1 + β + β/(3·2^d)) κ M^{−d} |X_{j_h}|)`, bounded on p. 389 by
    `Π_h exp 2κ(100R_k)^d`, using that the released X is small (condition (i)), and paid by
    `−2(1+β_0)^{−1} p_0 + 1 + 2κ(100R_k)^d ≤ −(3/2) p_0`;
  * (1.94)-(1.95) cancel the boundary sums against the second factor of (1.93);
  * (1.96) spends `e^{−q p_0/2}` on the sum over q and positions, and one `e^{−p_0}` is extracted for c_1.
* *I infer.* **No.**
  * Every step after (1.89) is an upper bound that is monotone in the T'-factors.
  * A factor `e^{−σ_k(X_{j_h})} ≤ 1` attached to each `T'_k(X_{j_h})` passes through all of them unchanged.
  * Restricting the sum to decompositions covering a set A gives a sub-sum, bounded by the same majorant times the
    uniform `e^{−c p_0² |A|}`.
  * The only volume cost charged to the T-factors (`2κ(100R_k)^d`) is paid from the per-component p_0, not from σ.

### 4. Conversion to current-scale cubes, and the sup over internal histories

* *Source says.*
  * p. 384: `S^{n−j}(□)` is a cube made of `L_{n−j}^d` `M R_n`-cubes, with `L_{n−j} < 63`.
  * `d'_n(S^{n−j}(Z)) ≤ (63)^d 3·2^{d−1} d'_n(Z^{(n−j)})` if the right side is non-zero, else `≤ (64)^d`.
  * `d'_n(Z^{(n−j)}) ≤ L^{−½(n−j)} d'_j(Z) ≤ 2^{−(n−j)} d'_j(Z)` for `n − j > 1`.
  * (1.76): `Z_j ⊂ Z'^{~10}_{j−1} ∪ ∪_i (Z_j^{(i)})^{~2}`.
  * Preparatory large fields arise only inside components of an existing region Z_j satisfying (i), (ii)
    (p. 381).
  * (1.79) is a bound "sup over all admissible domains", after "the summations over the admissible sequences can be
    replaced by the factors `exp O(1)(MR_j)^{−d}|Z_j|`" (p. 383), which go into the κ-costs.
* *I infer.*
  * **The conversion is right**, with a constant that M1 writes as C:
    * iterating (1.76) gives, for every history inside a released X, `X ⊂ ∪_b S^{k−j_b}((Z_b)^{~2})` over the P/Q/R
      births b of that history;
    * each birth-scale cube grows into at most `63^d` current-scale cubes, so
      `#cubes_k(X) ≤ C Σ_b #cubes_{j_b}(Z_b) ≤ C' Σ_b (d'_{j_b}(Z_b) + 1)`;
    * the last step uses `#cubes ≤ 3^d (d' + 1)` for a connected union of cubes, since d' is the length of a tree
      meeting every cube.
  * M1 writes the scaling as `2^{−(k−j)} d'_j + (64)^d` and drops the factor `(63)^d 3·2^{d−1}`. That is harmless:
    it goes into C.
  * **The sup over histories is right.** The sum over histories is already bounded by the entropy factor times the
    sup, and the entropy is a κ-cost. The bound `σ ≥ (c_σ/C') p_0²(g_k) #cubes_k(X)` holds for each history, so the
    factor comes out of the sup as `e^{−inf σ}`.
  * Overlapping births at different scales only add to σ.
* *Scope note.* (1.97') covers released components, which are the only ones in the activities F. An unreleased region
  at an intermediate step carries its slack in the (1.79) product as `e^{−κ_j(Z) − σ_j(Z) − 2p_0}`. There σ can be
  taken, but κ cannot: it is reserved for future costs. If M1's bad sets include unreleased regions, that part must
  use (1.79)/(1.80'), not (1.97'). This is a matter of applying the bound to the right object, not a gap in the
  re-proof.

### 5. (P1) and the exponent chain

* *Source says.*
  * p. 383: "We assume that `2p_1 − (d+5) r_0 > p_0`, and we estimate the factors by `exp(−p_0(g_j))`". The
    preparatory factor `exp(−R_j^{−d−5} p_1²(g_j))` must beat `p_0(g_j)`.
  * p. 389: `p_0(g_k) ≳ 8κ 100^d R_k^d`.
  * (1.88) needs `p_0(g) ≳ (100M)^d R^{d+2}`.
  * (1.82) needs `A_1² p_0²(g) ≳ M^d L^{d+1} R^{d+2}`.
* *I infer.*
  * (P1) `p_0(g) ≥ C(κ + M^d) 100^d R^d` needs only the exponent relation `p_0 ≥ r d`, which (1.88) already exceeds
    (`p_0 ≥ r(d+2)`). At fixed exponents, (P1) follows from Balaban's (1.88) condition for g small, since the ratio
    grows like `R²`.
  * **No exponent changes**, so `p_0` is not raised and `p_1` need not be raised. The constant doubling in (P0) is
    likewise absorbed by taking g smaller. Raising `A_1` instead would be the wrong lever, since `A_1` also sets the
    `p_1` cut on p. 383.
  * (P1) is also redundant. M1 says it is needed for "regions whose only gain is the preparatory `e^{−p_0}`". But
    every such region is `Z = S(Z_0)` with `Z_0` an existing large-field region. Its ancestry contains at least one
    P/Q/R birth, and M1's own step 4 keeps `σ_j(Z_0)`. So `σ ≥ c_σ p_0²(g_b)`, while the region has at most `100^d`
    current-scale cubes. (P2) then covers its denominator loss. Keeping (P1) does no harm.

### 6. Direction of `p_0(g_birth) ≥ p_0(g_k)`

* *Source says* ([III] (2.6)-(2.7), p. 255, for n > m):
  * `g_m ≤ (1+β_0) g_n`;
  * `(log g_n^{−2})^p ≤ (1+β_0)(log g_m^{−2})^p`.
* *I infer.* **The direction is right, but not exact.**
  * The birth step is earlier, so `m = j_b < n = k`. The source gives only `g_{j_b} ≤ (1+β_0) g_k`, not
    `g_{j_b} ≤ g_k`: monotonicity of g is not stated.
  * Hence `p_0(g_{j_b}) ≥ (1+β_0)^{−1} p_0(g_k)`, and `p_0²(g_{j_b}) ≥ (1+β_0)^{−2} p_0²(g_k)`.
  * This is the same factor Balaban uses in (1.86). It only multiplies `c'_σ` by `(1+β_0)^{−2}`, which M1 should
    write in.

### 7. Preparatory large fields: p_0² gain or only e^{−p_0}? (REVIEW-2 against REVIEW-3)

* *Source says.*
  * [V] p. 381: "Besides the above large field factors there are also the factors arising in the preparatory steps
    to the R-operation, and described in Sect. 1 [IV]. These factors are connected with components of a large field
    region Z_j, which satisfies the conditions (i), (ii) at the beginning of Sect. 1 [IV]. Thus, if one of the
    functions `1 − χ_j^{(n)}` is introduced in such a component, we get a factor ...".
  * The listed factors are:
    * `exp(−A_1² p_0²(g_j))`;
    * `exp(−γ_0 A_1² p_1²(g_j))`;
    * `exp(−A_1² p_0²(g_j))` again, for `1 − χ_{j,Λ}`;
    * `exp(−R_j^{−8} p_1²(g_j))` and `exp(−R_j^{−d−5} p_1²(g_j))` for the two cases of `1 − χ'` (pp. 381-383).
  * p. 383: "This is the largest factor among all the small factors we have obtained from the large field
    characteristic functions in the preparatory steps. We assume that `2p_1 − (d+5) r_0 > p_0`, and we estimate the
    factors by `exp(−p_0(g_j))`."
  * (1.79): the last product `Π' exp(−p_0(g_j))` is "over components of Z_j satisfying the conditions (i), (ii), for
    which some large fields are created during the preparatory steps". That is **one factor per component**, with no
    `(d'+1)`.
  * The `p_0²(d'+1)` creation gain of p. 381 belongs only to the characteristic functions `χ_j^c(P_j)`,
    `χ_j^c(Q_j)`, `χ^{(j−1)c}(R_j)`, and to their cover by `M R_j`-cubes, the components `Z_j^{(i)}`.
  * p. 384 (second case of (1.83)): such a region is treated as `Z = S(Z_0)` with `Z_0` the existing component,
    "a small domain, contained in a cube of the size `100 M R_{j+1}`".
  * (1.76): `Z_j ⊂ Z'^{~10}_{j−1} ∪ ∪_i (Z_j^{(i)})^{~2}`.
* *Answer.*
  * **REVIEW-2 is right about the factor.** A preparatory large field brings no `p_0²(d'+1)` creation gain. It brings
    one factor per component, of which only `e^{−p_0(g_j)}` is used. Its strongest factors are `p_0²`-sized but not
    proportional to d', and the weakest is only guaranteed to beat `e^{−p_0}`.
  * **REVIEW-3 is right about the consequence.** Preparatory large fields are not new region components.
    * By the source they arise only inside an existing component satisfying (i), (ii). Balaban books the result as
      `S(Z_0)`, which adds no territory beyond the usual S-layers.
    * By (1.76) iterated from j = 1, where `Z_1 ⊂ ∪_i (Z_1^{(i)})^{~2}`, every large-field region lies in the
      S-expansions of P/Q/R creation covers. So **every region descends from at least one creation event with the
      `p_0²(d'+1)` gain**, and it inherits that slack (M1's step 4 keeps `σ_j(Z_0)`).
  * Such a region has at most about `100^d` current-scale cubes and slack `≥ c_σ (1+β_0)^{−2} p_0²(g_k)`. Its
    denominator loss `C 100^d (M R_k)^d` is covered under (P2).
  * Its cubes are already counted in the conversion of item 4, through `S^{k−j_b}` of the ancestral births. So they
    need not be split off and priced through (P1).
* *I infer, with one caveat.* This rests on the preparatory large fields lying inside `S(Z_0)`. [V] p. 384 states
  this ("Z = S(Z_0)"). I did not re-read [IV] Sect. 1 in full, where the preparatory domains are built near the
  boundary of the region. If a preparatory domain could reach outside `S(Z_0)`, its excess cubes would have only the
  `e^{−p_0}` factor, and (P1) would be the right price for them. Since (P1) follows from Balaban's own (1.88)
  condition at small g (item 5), keeping it as insurance costs nothing.

### Verdict on the re-proof (c)

**It goes through.** I found no step that fails. Splitting the creation gain is a relabelling of the exponent of
(1.79). Every inequality Balaban proves about κ holds for the halved κ under (P0), which needs no new exponent. The
tree argument, the release (1.89) and the polymer step (1.92)-(1.96) never touch the kept part. The conversion to
current-scale cubes and the sup over histories are sound.

Corrections to write into section 26:
1. Use `½ γ_0 A_1²` for the new regions' term, not the printed `γ_0` of (1.85); constants only.
2. `p_0(g_birth) ≥ (1+β_0)^{−1} p_0(g_k)`, not `≥ p_0(g_k)`; the `(1+β_0)^{−2}` goes into `c'_σ`.
3. (P1) is implied by Balaban's own (1.88) condition at small g, and is redundant given the ancestral σ (item 7:
   preparatory large fields carry only `e^{−p_0}` per component, but they are not new regions and inherit their
   ancestors' slack). Keep it as cheap insurance. No exponent changes, so `p_1` stays as it is.
4. Rename the slack, since `σ` clashes with [V] (1.73)-(1.75).
5. If M1's bad sets include regions not yet released, take the slack there from (1.79)/(1.80'), not from (1.97').

Level: paper re-proof, checked against the printed steps. Each step on its own is an elementary regrouping; nothing
needs a new estimate.
