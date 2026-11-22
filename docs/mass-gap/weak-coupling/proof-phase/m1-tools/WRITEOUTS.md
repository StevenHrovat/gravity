# The two remaining sketch-level points, written out (m1-tools, 2026-11-22)

Brief (coordinator):
1. The mixed Mayer expansion for labels: explicit labelled-polymer factors alongside the exponentiated rest, with
   Balaban's polymer-gas bounds ([V] (1.90)-(1.104)) shown to survive, uniformly in volume and steps, in physical units.
2. The bookkeeping of R10's inserted term `e^{tF}` through every step up to `L_*`, for polynomials in the block
   variables at a fixed physical scale.

Report after each; stop at the first that fails or is much harder than marked. Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **The mixed expansion closes (paper).**
   * **Index split:** each polymer's activity splits by its label outcome. The outcome is a deterministic function of
     the configuration inside the polymer, so the split partitions the integration domain. Every piece obeys Balaban's
     activity bound (1.97), which comes from pointwise bounds on positive integrands.
   * **Unlabelled gas:** it is exactly Balaban's gas restricted to the complement of the labelled polymers. Its
     cluster expansion converges as in (1.93)-(1.98), and its log differs from the unrestricted one by terms touching
     the labelled polymers. Those terms are local, analytic and small, and go into the labels' `h_ℓ`.
   * **After the release step:** a label is an R-term with an index and an explicit constant `a_ℓ`. Balaban's R-terms
     are carried at their own scale for ever ([III] (2.30)-(2.33)), and the index changes nothing in that analysis.
   * **Uniformity:** in the volume, by the local form; in the steps, because labels are created only in the first
     `O(window)` steps (bare flips) and afterwards are carried as R-terms, which have no per-step cost; in physical
     units, by `CLOSING.md` 2's count. The decorations consistent with a given `τ'` (cancelling pairs on a coarse bond)
     sum per coarse bond in closed form.
2. **R10's bookkeeping closes (paper).**
   * **Insertion:** insert `e^{tF}` at the scale `m` where `F`'s block variables live (`L^m a = ℓ`). With
     `|t| ≤ t_0(n, R/ℓ)` it is a local analytic term within Balaban's E-term bounds.
   * **Propagation:** carry it through the `K - m = log_L(L_*/ℓ)` steps to `L_*`, a number fixed in physical terms,
     as part of the E-/R-terms.
   * **`E[F | V_K]`:** it is `∂_t log ρ_K^{(t)}|_{t=0}`, an identity of laws (the conditional step extends by linearity
     to complex `N`).
   * **`L¹` decoupling:** split the configurations at `L_*` by whether a large-field region joins `supp F` to
     distance `D`.
     * If not, the `t`-dependent part is a sum of localised terms: error `≤ C(n, R/ℓ) e^{-κ D/L_*}`.
     * If so, the event has probability `≤ e^{-c p0² D/(M R L_*)}` (Balaban's per-cube factor with his normalisation
       lower bound), and `|E[F | ·]| ≤ ‖F‖_∞`.
   * **Result:** the `L¹` transfer with rate `m = min(κ, c p0²/(M R))/L_*` and constants depending only on
     `(n, R/ℓ)`.
3. **Final verdict:** see `M1-PLAN.md` 0. Neither point failed. Both are written at paper level, resting on Balaban's
   bounds as cited (and on the normalisation lower bound, as in R7).

## 1. The mixed Mayer expansion

**Setting** ([V] pp. 387-391). At a release step, Balaban writes the large-field part as a product over components of
`T`-operations and expands it as a polymer gas `Σ_{compatible {X'}} Π F(X')` (1.90)-(1.91), with
`|F(X')| ≤ c1 exp(-(1+β)κ d(X'))` (1.92)-(1.97). He then exponentiates: `exp Σ R'(X)` with
`|R'(X)| ≤ O(1) c1 exp(-(1+β/2)κ d(X))` (1.98)-(1.99), sorted into R- and B-terms (1.100)-(1.104).

**Step 1: split by label.**
* Each polymer `X'` integrates configurations of a large-field region, which (in the first steps) contain bare flips.
  The decoder's output on the scale-`k` 1-skeleton inside `X'`, the label pattern `ℓ(X')`, is a deterministic,
  measurable function of those configurations (`REVIEW2-RESPONSE.md` 1: the decoder is local per conflict component,
  and a component inside `X'` is decided inside `X'`).
* Hence `F(X') = Σ_ℓ F_ℓ(X')`, with `F_ℓ` the integral restricted to `{ℓ(X') = ℓ}`. The integrands of [V] (1.71) are
  bounded pointwise by positive functions (characteristic functions, `exp` of real actions, Haar and Gaussian
  measures), so `|F_ℓ(X')| ≤ |F|_{bound}(X')` for each `ℓ`: (1.97) holds for every piece.
* For `ℓ ≠ 0` there is also the label suppression: at least 4 bare flips per labelled skeleton bond (`CLOSING.md` 2),
  each `≤ c β^{3/2} e^{-β}` (`REVIEW2-RESPONSE.md` 6, N1). So `|F_ℓ(X')| ≤ c1 e^{-(1+β)κ d(X')} Π_{b ∈ ℓ} a_b`, with
  `a_b ≤ (c β^{3/2})^4 e^{-16/g_j²}` (`j ≤ window`, so `g_j^{-2} ≥ g_0^{-2} - O(log g^{-2})`).

**Step 2: separate labelled and unlabelled polymers.**
* For fixed `τ'` the density is
  `Σ_{labelled families 𝓛 = {(Y_a, ℓ_a)} ~ τ'} (Π_a F_{ℓ_a}(Y_a)) · Σ_{unlabelled families compatible with 𝓛} Π F_0(X')`.
* The inner sum is Balaban's gas with activities `F_0` on the complement of `∪ Y_a`. Its cluster expansion
  ((1.93)-(1.98), [I] (7.13)) converges with the same bounds, and gives
  `exp(Σ_X R_0(X) - Σ_{X: X ∩ ∪Y_a ≠ ∅} R_0(X))` (a cluster expansion on a subset is the full one minus the clusters
  meeting the removed set).
* The second sum is local to the `Y_a`: for each `a`, `Σ_{X ∋ Y_a} |R_0(X)| ≤ C c1 e^{-κ}` per unit of `d(Y_a)`.
* Write `F_{ℓ_a}(Y_a) exp(-Σ_{X meets Y_a, not the others} R_0(X)) = a_{ℓ_a} (1 + h_{ℓ_a}(V))` with `h` analytic,
  local and small. Clusters meeting several `Y_a` are higher-order corrections, bounded by
  `Π a · e^{-κ dist}` and convergent because the labelled family is dilute (`a ≤ e^{-16/g²}`).
* **This is the form of `S1-CURRENT.md` (F-f).**

**Step 3: carrying a label.**
* After the release step, `a_ℓ` is a constant and `log(1 + h_ℓ)` is a local analytic term.
* In later steps the constant rides along, and the local term is one of the R-terms of [III] (2.30): a function of the
  background on its domain with (2.31)-type bounds. It is renormalised for vacuum energy only, which leaves `a_ℓ`
  untouched: the label's weight is not a vacuum constant.
* Its field dependence is of dimension 4 (R8's lemma: no linear coupling, since `h` is gauge invariant).
* It is never a large-field region, so no per-step entropy is charged.

**Step 4: decorations consistent with `τ'`.**
* Labels are on bare bonds of the scale-`k` skeleton; `τ'_k` sees the parity of labels per coarse bond.
* For a coarse bond `c` with bare bonds `b ∈ c`:
  `Σ_{S ⊂ c, |S| ≡ p} Π_{b ∈ S} a_b = ½[Π (1 + a_b) + (−1)^p Π (1 − a_b)]`, exactly.
* Per coarse bond: `Σ_b a_b ≤ L^k e^{-16/g_0²} poly = e^{-16/g_k²} L^{(1-16b)k} poly → 0`.

**Uniformity.**
* **Volume:** every quantity above is local (per polymer, per coarse bond).
* **Steps:** labels are created only during the first `O(window)` steps; afterwards they are carried as R-terms, with no
  per-step cost.
* **Physical units:** the per-coarse-bond sum above, `16 b = 1.49 > 1`.

**Status: paper.**

## 2. R10's inserted term, step by step

**Class.**
* `F` is a polynomial of degree `≤ n` in the matrix entries of the `N = (R/ℓ)^d` block variables `V_m` on a region `A`
  of physical extent `R`, at the block scale `m` with `L^m a = ℓ`, and `|F| ≤ 1` on real configurations.
* Also `G` likewise on `B`, with physical distance `D` from `A`.

**Step A: insertion at scale `m`.**
* Replace `ρ_m(V_m, τ'_m)` by `e^{tF(V_m)} ρ_m`. On Balaban's analyticity domain at scale `m` (complex neighbourhoods
  of radius `α_{1,m}` in the bond variables, [III] (2.34)-(2.39)), `|F| ≤ (1 + C α)^{nN}`.
* For `|t| ≤ t_0 := c (1 + Cα)^{-nN} e^{-κ d_m(A)}`, `tF` satisfies the E-term bound for the domain `A` ([I] (1.18):
  `O(1) e^{-κ d(X)}`).
* It is one more local analytic term of the effective action.

**Step B: propagation, `m → K`.**
* Each step treats `tF`'s descendants as E-/R-terms, with the localisation and analyticity of [V] (1.59)-(1.62),
  (1.73), (1.98)-(1.100).
* The number of steps, `K - m = log_L(L_*/ℓ)`, is independent of the lattice spacing.
* At scale `K` the `t`-dependent part of the effective action is `Σ_{X ⊇ A_K} Φ_t(X)`, with
  `|Φ_t(X)| ≤ C(n, R/ℓ) |t| e^{-κ d_K(X)}`.
* In large-field regions the inserted term enters as the bounded factor `e^{tF}` (`|e^{tF}| ≤ e^{|t|}` on real
  configurations; complex `t` through Balaban's analytic extension (1.73)-(1.75)).
* The conditional step at each scale acts on `e^{tF}`-weighted terms. `N` is then complex while `D > 0` is unchanged;
  `map_resample_eq` extends by linearity (complex Radon-Nikodym derivatives), and the law identity below holds.

**Step C: the conditional expectation.** `ρ_K^{(t)}(V_K, τ') = E[e^{tF} | V_K, τ'] ρ_K(V_K, τ')` is an identity of laws,
so `E[F | V_K, τ'] = ∂_t log ρ_K^{(t)}|_{t=0}`.

**Step D: the `L¹` estimate.** Let `E_D` be the event that the large-field region `Z_K` at `L_*` contains a connected
set joining the `L_*`-neighbourhood of `A` to distance `D/2`.
* **On `E_D^c`:** `log ρ_K^{(t)} - log ρ_K` is the localised sum of step B, plus `T`-ratios of large-field components
  that do not reach distance `D/2`, each localised. Truncating to domains within `D/2` of `A` gives
  `f(V_K, τ')|_{near A}` with `|E[F | ·] - f| ≤ t_0^{-1} Σ_{X reaching D/2} C|t_0| e^{-κ d_K(X)} ≤ C(n, R/ℓ) e^{-κ D/(2L_*)}`
  (Cauchy in `t`).
* **On `E_D`:** `|E[F | ·] - f| ≤ 2`. Its probability is `≤ Σ_{connected regions of length ≥ D/2} e^{-c p0² #cubes}`,
  using Balaban's large-field factor per cube ([V] (1.79), [16] (71) in 4D, `CLOSE-OUT.md` 1) and his normalisation
  lower bound to turn density bounds into probabilities (R7). This is `≤ e^{-c' p0² D/(M R L_*)}`.
* **Hence** `‖E[F | V_K, τ'] - f‖_{L¹} ≤ C(n, R/ℓ) e^{-m D}` with `m = min(κ/2, c' p0²/(M R))/L_*`.
* **Covariance:** two insertions `s, t`; `∂_s ∂_t log ρ^{(s,t)}_K = Cov(F, G | ·)`. On `E_D^c` only domains meeting both
  `A` and `B` contribute, `≤ C e^{-κ D/L_*}`; on `E_D`, `≤ 2`. Same `L¹` bound.

**Uniformity:** the constants depend on `(n, R/ℓ)` only. The number of steps `K - m` is fixed by `ℓ` and `L_*`; the
volume enters only through locality. **Status: paper.**

**What this delivers** (the honest form of `REVIEW2-RESPONSE.md` 5(b)): for every `n`, `R`, `ℓ ≤ L_*`, the `L¹` UV
transfer to `(V_K, τ'_K)` for character polynomials of degree `≤ n` in the block variables at scale `ℓ` on extent `R`,
with rate `m` (physical, independent of the class) and constants `C(n, R/ℓ)`.

**Update (REVIEW-3 H1, H4, H7; `REVIEW3-RESPONSE.md`):**
* **Section 1:** steps 2-4 are superseded by `REVIEW3-RESPONSE.md` 4. Labels are positive fixed-domain factors with
  (P1)-(P3); no constant `a_ℓ` or small `h_ℓ` is claimed. Corrections:
  * labels are extracted at the release of their component, not within the window;
  * "at least 4 flips per labelled skeleton bond" holds in the interior of coarse bonds; at coarse vertices the bound is
    per component;
  * the parity sum of step 4 is an upper bound (labelled domains have a hard core).
* **Section 2 (R10) is back to sketch.** `E_D` is a summation index, so the split has to use the positive partition.
  The probability bound needs a scale-`K` normalisation; R7 is bare-scale. The class must be the gauge-invariant
  polynomials, and the constants depend on `L_*/ℓ` too. Part 2.
