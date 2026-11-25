# Balaban reading for the segment-1 supplier (cycle 5, c5d-supplier, 2026-11-22)

Brief: read Balaban's five 4D gauge papers (PDFs in this folder, git-ignored) and decide the three gaps of `NOTE.md`
A.3 between the published ultraviolet bounds and UV1 (`formal/ProofPhase/Defects/Supplier.lean`, `UVRepDefect`;
`formal/ProofPhase/Seg1/Envelope.lean`, `PolymerRepW`): G1 (probability of the bad set), G2 (reference action),
uniformity, and whether Balaban's blocking is reflection positive in the project's sense (`RPBlocking`).

Reading method: the PDFs are scans with an OCR text layer. I located statements in the OCR text and read the relevant
pages as page images (equations checked on the image, not on the OCR). Marks: **full** = page images read by me;
**OCR** = OCR text read (formulas garbled, prose reliable); **not read** = only section headings seen. No Lean file
was written (section 6 says why). Nothing else in the repository was edited.

Paper labels as Balaban uses them: [I] = CMP 109 (1987) 249, [II] = CMP 116 (1988) 1, [III] = CMP 119 (1988) 243,
[IV] = CMP 122 (1989) 175, [V] = CMP 122 (1989) 355 (Balaban calls the last one "this paper"; it cites [I]-[IV]).

## 0. Result in plain words

1. **G1: (c), neither, and worse than the NOTE expected.** The "exponentiation" of [V] is real: [V] (1.90)-(1.98) write
   a vacancy-1 polymer gas of large-field contributions and exponentiate it into local terms with small activities
   ([V] (1.97), (1.99), (1.100)). But the gas lives inside the **R operation**, and the R operation **changes the
   density**: it keeps only integrals ([IV] (0.3)-(0.4), (1.102); [IV] p. 200: the new density "may not be equal to
   ρ_k, but is equivalent to it"; [V] p. 378, same). So Balaban's effective densities `ρ_k = (RT)^k ρ_0` are **not the
   laws of the block fields**. They give the partition function (ultraviolet stability, [V] (0.1) = [III] (2.50)), not
   the law `ν` that UV1 is about. The large-field regions that are not renormalized stay in **exact-cover** form with
   sharp characteristic functions and **upper bounds only** ([V] (1.79), (1.89), (1.104)). No probability or measure
   bound on large-field regions appears anywhere in the five papers.
2. **And the history bad set is not rare in the true law.** Balaban's large-field regions are a history (labels set by
   the fields of all finer scales). Balaban notes that in d = 4 the large-field suppression gives no positive power of
   the lattice spacing ([III] p. 244, [IV] p. 175). Simple arithmetic follows from that (my own, not in the papers):
   the expected number of fine-scale large plaquettes inside one `L_*` cube grows without bound as the cutoff is
   removed. So "bad = some large field in the history" cannot satisfy UV1 clause (B) uniformly in the depth `k`. The R
   operation exists to absorb exactly these regions into the action, and it pays for that by changing the law.
3. **G2.** The small-field action after `k` steps is `−g_k^{-2} A(U_k(V))` plus localized corrections. Here
   `A(U_k(V))` is the fine Wilson action at the **minimizer** `U_k(V)` (the fine configuration of least Wilson action
   whose `k`-fold average is `V`), with running coupling `g_k`. The corrections have exponentially decaying
   localization and **bounded, not small**, size per cube (`E0`, `B0`; only the R-terms carry `g^{κ0}`). They are
   bounded in sup norm over a complex neighbourhood of the small-field configurations, which gives derivative bounds.
   So the reference action is not a fixed Wilson action: it depends on `k` through `g_k` and through the minimizer map.
4. **Uniformity.** Constants are independent of the step number, the lattice spacing and the torus, **provided** the
   running couplings stay in `(0, γ]` with `γ` small and unspecified. That proviso is [I] Theorem 2, whose proof is
   unpublished ([I] p. 259; [V] p. 355 says it "has not been published yet"). So even ultraviolet stability is
   published only conditionally on a perturbative input.
5. **Blocking and reflection positivity.** Balaban's block variable is a deterministic, Euclidean-symmetric
   group-valued average of parallel transports through two adjacent blocks of odd side `L > 11`. It commutes with
   reflections in planes lying on block faces, so the blocked law is reflection positive for **link** reflection. It
   is **not** an `RPBlocking` (site reflection, closed positive half): a coarse site plane passes through block
   centres, so the coarse links in that plane read fine links on both sides. A composite with the good blocking does
   not fix this, because the problem is already in the first (Balaban) layer. The fix is a link-reflection variant of
   `RPBlocking` / `blocked_wilson_rp` (Osterwalder-Seiler link positivity of the Wilson action).
6. **UV1 now:** not a citation, and not a citation plus a lemma. It is two precisely stated missing results (section
   5): **M1**, a law-level version of Balaban's induction (an R operation that commutes with the next blocking step),
   the large one; and **M2**, a contour-removal (Peierls) lemma on that form, which is medium-sized and well supported
   by Balaban's estimates. Balaban supplies the method and nearly all the estimates M2 needs. He does not supply M1.

## 1. The five papers: main statements

Constants that appear throughout ([III] (2.4)-(2.9), [I] (1.18), [IV] (1.94), [V] p. 383): `L` odd `> 11` (block
factor); `M = L^m` large (cube size for localization); `κ ≥ κ0` (decay rate); `γ` (coupling threshold);
`p0(g) = A0 (log g^{-2})^{p0}`, `p0` a positive integer; `ε_j = g_j p0(g_j)` (small-field threshold at scale `j`);
`R_j` = least power of `L` with `R_j ≥ (log g_j^{-2})^r`, `r ≥ 2`; analyticity radii
`α_{0,j} = g_j C0 (log g_j^{-2})^{q0}`, `α_{1,j} = g_j C1 (log g_j^{-2})^{q1}`; `N` = number of steps a large-field
factor controls, `N ≤ O(1)(log g^{-2})^ν`; side conditions such as `p0 ≥ 5r` and `2p1 − (d+5) r0 > p0`. No numerical
values are given for any of them; every threshold is "sufficiently small/large".

| paper | statement | assumes | concludes | constants, uniformity | read |
|---|---|---|---|---|---|
| [I] CMP 109 | setting (Sect. 0) | torus `T_ε`, side `2L^m`, spacing `ε = L^{-K}`, `G ⊂ U(N)` compact semisimple, Wilson action (0.2); block average (0.4) or (0.12) with axioms (0.5)-(0.9); RG step (0.13)-(0.20), restricted to small fields | effective actions `A_k(V) = −g_k^{-2} A(U_k(V)) + E_k(U_k(V))` (0.22), `U_k(V)` the minimal orbit of `U ↦ A(U)` subject to `M^k(U) = V` (0.21) | — | full (pp. 249-265) |
| [I] | Theorem 1 (p. 259), precise form **Theorem 3** (p. 264) | `κ ≥ κ0`, `M ≥ M(κ)`, `0 < g_k ≤ γ` for all `k ≤ K` | the small-field actions satisfy the inductive assumptions (1.1)-(1.22): `E^{(j)} = ∑_X E^{(j)}(X)`, `E^{(j)}(X)` gauge invariant, depends on the field in `X`, analytic on `U^c_j(X, α0, α1)`, `|E^{(j)}(X)| ≤ E0 e^{−κ d_j(X)}` (1.18); β-functions (1.22) smooth and bounded on `[0, γ]`; after subtracting the marginal part, `|V^{(j)}(X)| ≤ O(1)(L^j η)^{4+α} e^{−κ d_j(X)}` (0.29) | `E0, κ, M, γ, ε0, ε1, α0, α1` independent of `k`, `K`, the torus; extensive bound (0.30) | full |
| [I] | **Theorem 2** (p. 259) | `d = 4`, `G = SU(2)`, `γ` small | for `g` small there is a bare `g0(ε, g)` with all `g_k ∈ (0, γ]`, `g_K = g`, and `g^{-2} + β log(L^k ε)^{-1} ≤ g_k^{-2} ≤ g^{-2} + β' log(L^k ε)^{-1}` (0.31) | proof deferred to "a separate paper" (p. 259); [V] p. 355: not published | full |
| [I] | Sects. 2-5 (fluctuation integral, Ward identities, β-functions) | — | proof of Theorem 3, small-field part | — | not read (headings, p. 265 only) |
| [II] CMP 116 | Lemma 1 (1.33)-(1.36), Lemma 2 (1.41)-(1.43), **Lemma 3** (2.38) | inductive assumptions of [I] at step `k` | localized fluctuation action; cluster activities `|H(Z)| ≤ C31 exp(−(1−δ)κL d_{k+1}(Z))`; then `|E^{(k+1)}(X)| ≤ O(1)C31 exp(−(1−10δ)κL d_{k+1}(X))` (2.41), hence [I] (1.18) at `k+1`: **completes [I] Theorem 3** | constants independent of `k`; `δ = ½(1 − 2L^{-1})` | OCR (intro, lemma statements, pp. 20-22) |
| [III] CMP 119 | Theorem (p. 245, informal), **Theorem 1** (p. 262) | `g_k` from the RG equations within the bounds of [I]; the R operation has the properties assumed in Sect. 2 | the complete densities `ρ_k = (RT)^k ρ_0`, `ρ_0 = exp[−g0^{-2}A − E]`, keep the form (2.18): `ρ_k(V_k) = ∑_{\{Ω_j\},\{Λ_j\}} χ_k(Ω_k) T_k exp A_k`, with sharp small-field indicators `χ_k` (2.17), the large-field operation `T_k` factorizing over components (2.19)-(2.22), and `A_k = −A(g_k^{-2}, U_k) + E_k + R_k + B_k − E_k` (2.23); `|R^{(j)}(X)| ≤ g_j^{κ0} e^{−κ d_j(X)}` (2.31); `|B^{(j)}(X)| < B0 e^{−κ d_j(X)}` for `X` meeting the large-field region (2.42) | constants independent of `k`; "numerous restrictions" | full (pp. 243-246, 254-265) |
| [III] | **Theorem 2** (p. 263) | as Theorem 1 | extensive bounds: `|∑ [E^{(j)} − E^{(j)}(1)] − β_j A(φ, U_k)| ≤ E1 ∑_n (L^{j−n})^β |Γ_n ∩ Ω|` (2.43), `R`-terms `≤ R1 g_j^{κ0} ∑|Γ_n ∩ Ω|` (2.44), hence (2.45)-(2.49): `A_k = −A(g_k^{-2}, U_k) + log terms + O(1)∑_j |Γ_j|` | `E1`, `R1` independent of `j, k, Ω`, the torus | full |
| [III] | **Corollary 3** (2.50), ultraviolet stability | as Theorem 1 | `χ_k(T_η) exp[−g_k^{-2}A(U_k(V_k)) − E_−|T_η|] ≤ ρ_k(V_k) ≤ e^{E_+|T_η|}` | `E_±` independent of `η` and the torus, depend on the `g_k` | full |
| [III] | Sect. 1 (first step), Sect. 3 (step `k+1`, proof of Theorem 2) | — | the partitions of unity (1.1), (1.4), (3.2), (3.3) into small/large field: **exact cover** `1 = ∑_P χ(P^c) χ^c(P)` with sharp indicators | — | full pp. 245-246, 264-265; rest not read |
| [IV] CMP 122 | definition of **R** (0.2)-(0.6), idealized | `ρ = ∑_Z ρ(Z, V)`, `Z = Z' ∪ Z''`, `Z'` the components to renormalize | `(Rρ)(V) = ∑_Z ρ(Z'', V) ∫dV_{Z'} ρ(Z, V) / ∫dV_{Z'} ρ(Z'', V)` (0.3); densities positive (stated, proved later); `∫ Rρ = ∫ ρ` (0.4); ratio sum exponentiated `= exp ∑_X R(X, V)` (0.5) | — | full (pp. 175-180) |
| [IV] | Sect. 1, components renormalized | a component of the large-field region (i) inside a cube of side `100 M R_k`, (ii) no new large fields in the last `N` steps | **Proposition 1** (p. 194): for regular `V_k` outside, a unique minimal orbit of `V_k|_Λ ↦ A(U_{k,Z}(V_k))`, regularity (1.78), analytic extension; preliminary integrations change the density, keeping integrals (p. 194, p. 200); `R'` (1.100) with `∫ R'ρ_k = ∫ ρ_k` (1.102); changes decay exponentially away from the region (p. 202) | `B5`, `M^5`, `N > N0` | full pp. 194-202; pp. 181-193 not read |
| [V] CMP 122 | **Theorem 1** (p. 355) | all `g_k ∈ (0, γ]`, `γ` small | `ρ_k` have the form and bounds of [III] Sect. 2; hence (0.1) = [III] (2.50); with [I] Theorem 2 this would be unconditional, but that proof is unpublished | `E_±` independent of `k`, the torus, `U_k` | full pp. 355-358, 377-392 |
| [V] | the R operation completed: (1.70)-(1.72); bounds (1.73)-(1.79); induction (1.80)-(1.88); **(1.89)**; polymer gas (1.90)-(1.91); **(1.97)**; exponentiation (1.98)-(1.100); new action (1.101); final form **(1.104)** | as Theorem 1 | see section 2 | constants independent of `k`, the torus | full for these pages; pp. 359-376 (Proposition 1 of [IV], preliminary integrations) not read |

One phrase quoted, from [IV] p. 200 (above, section 0). [V] p. 355: five words, on [I] Theorem 2. Nothing else is
quoted.

## 2. G1: what Balaban proves about large fields

### 2.1 The exact-cover structure (all papers)

Large fields enter through sharp partitions of unity, `1 = ∑_P χ(P^c) χ^c(P)`, per cube of side `L M2 R_j`, on the
plaquette (or block-field) deviation from 1 ([III] (1.1), (1.4), (3.2), (3.3); [IV] (1.88); [V] p. 378). Each term
of the density carries the history `{Ω_j, Λ_j}` (or `Z_j = Λ_j^c`) of where the field was large at each scale ([III]
(2.1)-(2.3), (2.18)). The history is a **summation label**. It is a function of the fields at all scales (the fine
field and its successive averages), not of the current field `V_k` alone.

### 2.2 Upper bounds on large-field factors

* Per large-field region, [V] (1.79):
  `T'_k(X)1 ≤ sup exp{∑_j O(1) M^d R_j^{d+1} d'_j(Z_j)} · ∏_j ∏_i exp(−½γ0 A1² p0²(g_j)(d'_j(Z_j^{(i)}) + 1) − 2p0(g_j)) · ∏' exp(−p0(g_j))`.
  The first factor is the entropy and normalization loss; the large-field factors win it. The induction (1.80)
  bookkeeps this as a number `κ_j(Z)` per region, which must pay `O(1) M^d R_n^{d+1} d'_n` for every later step it
  controls. The win needs `¼γ0 (14)^{-d} A1² p0²(g) ≥ O(1)(64)^d M^d L^{d+1} R^{d+2}` ((1.82)-(1.85)), i.e. `p0`
  large compared with `r`.
* Hence the "fundamental inequality" [V] **(1.89)**: `T'_k(X)1 ≤ exp(−2(1+β0)^{-1} p0(g_k))` for every component `X`
  of the large-field region. `T'_k(X)` ((1.71)) is normalized: the Wilson term and the small-field normalization of
  `X` are divided out ((1.10), (1.70)). So `T'_k(X)1` is a **ratio** of the large-field weight of `X` to a small-field
  reference weight. It is the right kind of quantity for a probability bound, but only an upper bound.
* Analytic extension: [V] (1.73)-(1.75) give `|T'_k(X, (U, J))F| ≤ T'_k(X)1 · e^{sup|σ|} sup|F|` and a matching
  lower bound for the extended operation relative to the real one ((1.74)). That is a lower bound of `T'` against
  **itself**, not against the small-field weight.

### 2.3 The exponentiation ([IV] (0.5), [V] (1.90)-(1.100))

For the components `X_1, ..., X_n` that are renormalized (first class, [V] p. 378), the curly bracket in (1.72),
`{∑_{n ≥ 0} ∑_{X_1..X_n} ∏_j T'_k(X_j) exp ∑_Y V(Y, U_k)}`, is a **vacancy-1 gas** (the `n = 0` term is the plain
small-field term). After a Mayer expansion it is a polymer gas `1 + ∑ ∏ F(X'_p)` ((1.90)) with activities ((1.97))

  `|F(X')| ≤ c1 exp(−(1+β) κ d_{k, ∪Y_i}(X'))`, where `c1 = exp(−p0(g_k))` if `X'` misses the current large fields `Y_i`, and `c1 = α^{1/3}` otherwise.

It is exponentiated ((1.98)): `{...} = exp ∑_X R''^{(k)}(X)`, with `|R''^{(k)}(X)| ≤ O(1) c1 exp(−(1 + ½β) κ d(X))`
((1.99)). The terms away from the large-field region become new R-terms with
`|R''^{(k)}(X)| ≤ exp(−p0(g_k)) exp(−κ d_k(X))` ((1.100)); those meeting it become boundary terms `B''^{(k)}`. The
new action is (1.101). The final representation ((1.104)):

  `Rρ_k = ∑_{Z_k} ∑_{\{Y_i\}} χ_k(·) (∑ T''_k(Z_k)) ∏_i χ^c_k(Y_i^{~−6}) χ_{k,Λ_i} χ_i δ_{G_i}(V_k V_{Λ_i}^{-1}) (T'_k(Y_i)1) · exp[A'_k + ∑_X R''^{(k)}(X) + ∑_X B''^{(k)}(X)]`.

So this is **(a) in part**: an exponentiated, vacancy-1 form with small activities. But only for the renormalized old
regions. The current large fields `Y_i` (indicators `χ^c` of the current field) and the unrenormalized history `Z_k`
keep the exact-cover form, with the upper bound (1.89) on `T'_k(Y_i)1`.

### 2.4 The decisive point: R changes the law

R is defined so that integrals are preserved, not densities ([IV] (0.3)-(0.4)). For each history `Z = Z' ∪ Z''`, the
field `V` on `Z'` is replaced: its conditional density becomes the small-field one, `∝ ρ(Z'', V)`. The total weight
`∫dV_{Z'} ρ(Z, V)` of the term is kept. Since the next block field averages `V` over `Z'` as well, all later laws
change near `Z'`. Balaban says so explicitly ([IV] p. 194, p. 200, (1.102); [V] p. 378: equivalent, not equal). Two
consequences:

* **The published `ρ_k` is not the law of the `k`-fold blocked Wilson field.** It is a positive density with the
  same total integral (so the same partition function) and changes localized near renormalized regions. The papers
  contain no statement about expectation values; [V] p. 356 names them as future work.
* A remark of mine, not in the papers (positivity is from [IV] p. 176, the rest is my reading): since the terms are
  positive and per-term integrals are kept, R acts as a **resampling kernel**. Keep the history and the field outside
  `Z'`; redraw the field on `Z'` from the small-field conditional law. So `(RT)^k ρ_0` is the law of the block field
  of a process that alternates averaging with local resampling on old large-field regions. The true process has no
  resampling.

### 2.5 Why history-based bad sets are not rare (arithmetic on Balaban's remark)

[III] p. 244 and [IV] p. 175: a large plaquette at the bare scale is suppressed by at most
`exp(−½ p0²(g0)) = g0^{A0²(log g0^{-2})^{2p0−1}}`, and in d = 4 this is no positive power of `ε`, because
`g0² ~ 1/(b log ε^{-1})`. The Gaussian tail has the same order from below (standard, not from the papers). So the
expected number of large fine plaquettes per unit cube is about `ε^{-4} exp(−c (log log ε^{-1})^{2p0}) → ∞` as
`ε → 0`. The same holds at every scale `n` steps below `L_*`, with `L^{4n}` cubes against
`exp(−c (log n)^{2p0})`. Consequence: in the true law, the probability that a given `L_*` cube has a large field
somewhere in its history tends to 1 as the depth grows. **UV1 clause (B) is false for history-based bad sets,
uniformly in `k`.** That is the d = 4 obstruction Balaban built R to overcome.

What can be rare are (i) large fields of the current `L_*` field, which are functions of `V_{L_*}`
(`χ^c_k(Y_i^{~−6})`), and (ii) **recent** regions created within the last `N` steps. For (ii) the entropy is about
`L^{4N} = exp(O((log g^{-2})^ν))` against `exp(−p0(g)) = exp(−A0 (log g^{-2})^{p0})`; Balaban's constraint
`½ν ≤ p0 − p1 − 1` ([IV] p. 198) makes `p0 > ν`, so recent regions are suppressed. All older regions must be
absorbed into local terms of the action, as R does. But for the true law that absorption must preserve the law,
which Balaban's R does not.

### 2.6 Verdict on G1

**(c), neither** in the form UV1 needs:
* (a) the exponentiated vacancy-1 form exists ([V] (1.90)-(1.100)), but only for the R-modified ("equivalent")
  density and only for renormalized regions;
* (b) there is no probability or measure bound. The only two-sided statement is the global, extensive stability bound
  [V] (0.1) = [III] (2.50), which gives nothing local.

`PolymerRepW` is not given either: (1.104) still has the exact-cover sum over `Z_k`, `Y_i` with sharp indicators. The
small-field terms are bounded only on small-field (analytic) domains, while `PolymerRepW` asks for `|E X U| ≤ Ē X`
for every configuration. And it is a statement about `Rρ_k`, not about the law.

## 3. G2 and uniformity

**Reference action.** At step `k`, the small-field action is `−g_k^{-2} A(U_k(V))` ([I] (0.22), [III] (2.23)). `A` is
the Wilson action (0.2) on the **finest** lattice, evaluated at the minimizer `U_k(V)` (the least Wilson action
subject to the `k`-fold average equal to `V`, [I] (0.21), (1.1)). It is a quasi-local functional of `V`: the
minimizer's dependence decays exponentially (Balaban's variational-problem papers, cited as [15] in [I]; not read
here). It changes with `k` through `g_k` (from (0.20)) and through the map `V ↦ U_k(V)`, which depends on the number
of fine levels below. No fixed Wilson action at one `β_*` is approached.

**Corrections and norm.**
* `E_k = ∑_j ∑_X [E^{(j)}(X) − β_j A]`: localized, `|E^{(j)}(X)| ≤ E0 e^{−κ d_j(X)}` ([I] (1.18), [II] (2.41)) in sup
  norm over the complex domain `U^c_j(X, α_{0,j}, α_{1,j})`. That gives derivative bounds on the real small-field
  domain by Cauchy estimates. Summed per unit cube it is `O(1)` ([I] (0.30), [III] (2.45)): **bounded, not small**.
* `R_k`: `|R^{(j)}(X)| ≤ g_j^{κ0} e^{−κ d_j(X)}` ([III] (2.31)): small.
* `B_k` (boundary terms, only `X` meeting large-field regions): `< B0 e^{−κ d_j(X)}` ([III] (2.42)): bounded, not
  small.

So clause (G) holds in Balaban's form with `Wref` = the level's own `−g_k^{-2} A(U_k(·))`, error budget
`O(E0 + B0)` per cube (finite, not small), sup norm over the small-field set. This is the same answer as for the
OpenAI construction in `NOTE.md` A.3 (G2): IR must be uniform over a class of actions, not near Wilson. Plus a caveat
the OpenAI form does not have: here everything is for `Rρ_k`, not the law.

**Uniformity.**

| quantity | uniform? | where |
|---|---|---|
| number of RG steps `k` (and `K`) | yes, given `g_k ∈ (0, γ]` for all `k` | [I] Thm 3, [III] Thms 1-2, [V] Thm 1 |
| lattice spacing `η` / `ε` | yes (same proviso) | [III] (2.50), [V] (0.1) |
| volume (torus of side `2L^m`, any `m`) | yes; all bounds extensive or local | [I] p. 251, [III] (2.50) |
| coupling range | only `g ≤ γ`, `γ` "sufficiently small", no value; the step from bare to running coupling ([I] Thm 2) is unpublished | [I] p. 259, [V] p. 355 |
| blocking | Balaban's averaging only (any average with axioms (0.5)-(0.9)); the propagator and variational bounds behind it are proved for that averaging | [I] (0.4)-(0.12), [III] p. 243 |

In Balaban's setup, the project's `L_*` is his **unit lattice** (`k = K`), with `g_K = g ≤ γ` small and unspecified.
That agrees with `NOTE.md` G3 ("some unspecified small `ḡ`").

## 4. The blocking and reflection positivity

**What it is.** A δ-function transformation `(Tρ)(V) = ∫ dU δ(Ū V^{-1}) ρ(U)` ([III] (0.1)), i.e. the pushforward
under a deterministic map `U ↦ Ū`. For a coarse bond `c` it averages, in the Lie algebra, the loops "contour from
`c_−` to `x` inside block `B(c_−)`, fine segment parallel to `c` from `x` to `x'`, contour back from `x'` to `c_+`
inside `B(c_+)`, closed by `c`" over `x ∈ B(c_−)`. Contours run over the family `G(y, x)` of shortest paths in all
orders of directions ([I] (0.3)-(0.4), alternative (0.12)). The block factor is `L` odd `> 11`, so block centres are
fine sites. The family `G(y, x)` was chosen to make the average Euclidean (permutation and reflection) symmetric
([I] p. 252). The gauge fixing ([I] (0.14)-(0.16)) is a Faddeev-Popov identity and does not change the law. One point
I did not find in the pages read: how the average is defined for configurations far from the identity (the axioms
are for nearby elements). Any measurable, reflection-equivariant extension serves the law; for SU(2) the principal
log with `log(−1) := 0` keeps `log(U^{-1}) = −log U` everywhere.

**Reflection positivity.** `Ū(c)` reads only fine bonds inside `B(c_−) ∪ B(c_+)`.
* **Link reflection** (plane on block faces, which is a fine plane between fine sites): reflected blocks are blocks,
  the contour family is mapped to itself, and `M(U^{-1}) = M(U)^{-1}` ([I] (0.5)) handles reversed time bonds. So
  `B ∘ Θ = Θ ∘ B`. Coarse bonds inside the positive half read only positive-half fine bonds. With the Wilson action
  link-reflection positive (Osterwalder-Seiler), every Balaban-blocked layer is **link-reflection positive**.
  (Paper-level check, not formalized.)
* **Site reflection, closed positive half** (the project's `RPBlocking`, `Objects.lean:403`): a coarse site plane goes
  through block centres. The blocks there straddle the plane, and a coarse spatial link in the plane reads fine links
  at negative times. The `half` field fails. Even block factors do not help: Balaban needs block centres on fine
  sites.
* **Composite `B_good ∘ B_Bal`** (c4b's proposal): fails the same way, because the first layer is Balaban's.
  Recommended instead: a link-reflection twin of `RPBlocking` and `blocked_wilson_rp` (Wilson link-RP is a standard
  theorem; medium Lean). Then Balaban's averaging, and composites with any link-compatible good blocking, qualify.

## 5. What UV1 now is

Not a citation, and not a citation plus a lemma. **Citation only for**: ultraviolet stability of the partition
function on a fixed torus, uniform in the lattice spacing, conditional on the running coupling staying below `γ`
([V] Thm 1, (0.1); [III] Cor. 3). The law-level statement UV1 is two missing results.

* **M1 (large): a law-preserving R operation.** Needed: the inductive form (1.104), with the bounds of [III] Sect. 2,
  for the **law** of the block field, not for an integral-equivalent density. Proposal (mine): perform R jointly with
  the next blocking step. Compute the ratios `∫dV_{Z'} ρ(Z, V) / ∫dV_{Z'} ρ(Z'', V)` with the next-scale block field
  fixed on the blocks over `Z'` (inside the δ-function of `T`). Then `T R̂ = T` exactly and the densities stay laws.
  Where the next block field is itself large over `Z'`, the small-field denominator vanishes. Those configurations
  must become new current-scale large-field regions, which are functions of the new field, as in [III] (3.2).
  Size: redoing the R estimates of [IV]-[V] (about 65 journal pages) under a block constraint. Structurally the same
  work, with no new idea needed in the bounds as far as I can see, but paper-scale. Balaban announced expectation
  values as future work ([V] p. 356). Whether a later paper did this, I do not know (not checked).
* **M2 (medium): contour removal on the M1 form, giving clause (B).** Sites: the `L M2 R(ḡ)`-cubes of the `L_*`
  lattice. Bad(□) = □ meets a current-scale large-field region `Y_i` or a recent (fewer than `N` steps old)
  unrenormalized region. These are an environment (labels), so the natural interface is the **mixture form** of Part
  B (`defect_decay_W`: law `q` of the bad set, specification per bad set), not the field-function form of
  `UVRepDefect` (B). Needed bound: given everything outside range `rad`, the large-field weight of a region `Y ∋ x`
  is at most `exp(−c p0(ḡ))` per cube times the small-field weight of `Y`. Ingredients: the upper bound (1.79)/(1.89);
  a **local** small-field lower bound (the local version of the lower half of (2.50), a Gaussian integral over `Y`
  costing `exp(−O(1) M^d R^{d+1} |Y|)`); and the cross terms `B''` touching `Y` (bounded by `O(α^{1/3})` per cube by
  (1.99)). Balaban already wins the same competition, `p0²` against `M^d R^{d+2}`, in (1.80)-(1.85). Expected
  constants: `p ≈ exp(−c p0(ḡ))` with `p0(ḡ) = A0 (log ḡ^{-2})^{p0}`; `rad = O(100 M R(ḡ))` in `L_*` units;
  `K = O(1)^d` cubes per conflict neighbourhood. Size: a few pages of paper, in Balaban's notation, once M1 is there.
* **Also open:** [I] Theorem 2 (the running coupling stays below `γ`), a published claim with unpublished proof.

**Changes this suggests for the Lean statements** (proposals, not made):
1. Restate UV1 in the **mixture form**: a defect law `q` and, per defect set `B`, a density for `μ_B` with clauses
   (L), (G) on the good region. Part B consumes exactly this, and `uvRepDefect_cylinder` is then not needed.
2. Keep the bad set's **range** explicit: `rad ~ 100 M R(ḡ)` is large in `L_*` units. It enters Part B through `Δ`
   (the degree of the cube graph) and `D0, D1`.
3. Add a link-reflection `RPBlocking` variant (section 4).

## 6. Lean

None written. The brief makes the lemma conditional on G1 resolving positively, and it did not. With the M1 form in
hand, the translation into Part B is already in Lean (`defect_decay_W` takes a defect law and per-set
specifications). A lemma from Balaban's form to `UVRepDefect` (B) would only restate a hypothesis no source supplies.

## 7. Next steps

1. **Blueprint (c5a-v4):** UV1 is not a published input. Record: (i) Balaban's densities are integral-equivalent, not
   laws ([IV] (0.4), p. 200); (ii) history-based bad sets are not rare in d = 4 (2.5); (iii) the published UV
   stability is conditional on [I] Theorem 2. Segment 1 becomes M1 + M2, or a different supplier.
2. **Literature check (one short session):** is there a law-level or expectation-value continuation of Balaban's 4D
   programme? Candidates (recalled, not checked): Balaban's later papers if any; Magnen-Rivasseau-Seneor, CMP 155
   (1993) 325 (YM4 with an infrared cutoff, Schwinger functions; a different, non-lattice-gauge-invariant scheme);
   Dimock's QED d = 3 work, for whether expectation values are included.
3. **Paper (if M1 is pursued):** write the block-constrained R operation for one step and check that [IV] Proposition
   1 and [V] (1.79) survive the constraint. That is the test of whether M1 is "the same work again" or needs a new idea.
4. **Lean, medium:** link-reflection twin of `RPBlocking` / `blocked_wilson_rp`.

## Files

- Here: `BALABAN-READING.md` (this file). PDFs `1104116842.pdf`, `1104161193.pdf`, `1104162401.pdf`,
  `1104178393.pdf`, `1104178467.pdf` stay git-ignored. OCR text extracts were made in the session scratchpad only.
