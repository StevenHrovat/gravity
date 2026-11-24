# D-N: can Balaban's bookkeeping carry the random-shift device for deep cores? (m1-tools, 2026-11-22)

Brief: row D-N of `M1-PLAN.md`. `NOTE.md` 2.5-2.6 proposed to handle deep cores (old large-field cores that the block
average cannot dilute, `NOTE.md` 2.4) by shifting the block grid at random at each step: a deep core then stays deep
for `n` steps only with shift-probability about `p_stayⁿ`, and that probability was to replace the fresh large-field
factor that branch (a) of the conditional step lacks. This needed a delay `N ≳ p0(g)/log(1/p_stay)` between creation
and renormalisation. Question: do Balaban's constants allow that, and does the device then close the induction?

Read in full for this note: [IV] pp. 196-199; [V] pp. 379-386 ((1.71)-(1.86)); [15] pp. 277-280 (statement of its
Theorem 1). Earlier reads of [IV] pp. 177-202 and [V] pp. 355-392 are used as recorded in `NOTE.md` and `ONE-STEP.md`.
Claim marks as in `NOTE.md`; everything here is **paper** (bookkeeping on Balaban's estimates), no Lean.

## 0. Result in plain words

1. **The delay itself is not the problem.** Balaban's conditions on `N` are lower bounds (`L^{-N}` must beat
   polylogarithmic constants) plus one upper bound, `½ν ≤ p0 - p1 - 1` ([IV] p. 198). That upper bound comes from a
   crude estimate of the coupling ratio `g_k/g_h ≤ (1+β0) N^{1/2}`; with the one-step bound on the running coupling
   ([I] (1.22)) the ratio is at most `√2` for every polylogarithmic `N`, and the condition becomes `p1 < p0`. The
   induction's other requirements ([V] (1.78)-(1.85)) can be met for `N ≈ p0(g)/(d log L)` by retuning the exponents
   (`p1 > (p0 + (2d+6) r)/2`, `p1 < p0`, hence `p0 > (2d+6) r`, and `β0` small). So, read literally: **yes, after
   retuning, Balaban's constants allow `N` of order `p0(g)`.**
2. **But the shift device fails anyway, for every `N`, because of rates.** In Balaban's bookkeeping every step that a
   large-field region stays unrenormalised costs a factor `exp(O(1) log g_j^{-2} |Z_j|) ≥ exp(c (M R_j)^d log g_j^{-2})`
   ([V] p. 380, (1.79), (1.81)). The shifts buy at most a factor `L^{-d}` per step: a vortex core that a shift places
   exactly at a block centre persists with certainty (`ProofPhase.M1.vortex_persists`), and that shift has
   probability exactly `L^{-d}`. Since `L^{-d} · exp(c (M R)^d log g^{-2}) ≫ 1`, the weight bound of a persistent
   term grows with every step of persistence and the sum over persistence times diverges. No choice of `N` changes
   that.
3. **So D-N answers NO for the device: the random-shift device cannot close Balaban's induction for deep cores.**
   The physics is not the obstacle: in the true law a persistent deep core must sit at one pinned site per cell and
   carries the Wilson weight `exp(-A/g_h²)`, and asymptotic freedom makes the sum over creation scales converge
   (section 3). The obstacle is the per-step **volume** cost of carrying a region in Balaban's bookkeeping.
4. **What could work (open, new):** carry a pinned deep core at a cost per step proportional to its own size (a
   handful of bonds), not to the volume `(M R)^d` of a Balaban region. That needs a partial renormalisation around a
   pinned irregular coarse star (section 4, idea I1). Without such a device, deep cores pinned at nested block
   centres remain the open point of M1.
5. **Side results.** `[15]` Theorem 1 covers nested determining sets that are coarser inside (its condition (1)),
   which is the two-scale set of row V1: V1 becomes a citation plus a check of the distance condition. ONE-STEP's
   "Theorem 1 of `[15]`" in the D2 row is the minimal-orbit theorem; the large-field factor it feeds is [V] p. 380
   ("Theorem 1 [15] and (71) [16]").

## 1. Every place where N enters Balaban's estimates

| where | condition | type | allows `N ≈ p0(g)/(d log L)`? |
|---|---|---|---|
| [IV] p. 179, (1.10) | `N > N0`, `L^{-N0+1} M R_{k-N0+1} = M` | lower | yes |
| [IV] (1.94), second term | `L^{-N} N^{1/2} O(1) B3³ B5 M⁶ < α/2` | lower | yes |
| [IV] (1.94), first term | `B3 (1+β0) N^{1/2} (A1 p1(g_h))/(A0 p0(g_h)) < α/2`, whence `N ≤ O(1)(log g^{-2})^ν`, `½ν ≤ p0 - p1 - 1` | upper, **artefact** | yes after the fix below |
| [IV] p. 199 | `22d² max{1, L^{-2N} N^{1/2} …}` | lower | yes |
| [V] p. 363 | `N ≥ (ν/log L) log log g^{-2}` | lower | yes |
| [V] (1.31) | `g_k² L^{-4N} N^{4β0} O(1) A0² B3² B5² M^{14} R_k⁴ p0²(g_k)` small after dividing by `g_k²` | lower | yes |
| [V] p. 366 | `1/(g''_k)² - 1/g_k² = O(N) ≤ O(R_k)` in a bound `O(1) N^{2+4β0}(100 M R_k)⁴ (…)²` | uses `N ≤ R_k` for convenience | yes: the bound is `O(N^{2+4β0} M⁹ R_k⁴ ε_k²)`, still small since `ε_k² = g_k² p0²` kills any polylog |
| [V] (1.47) | `L^{-N} N^{1+β0}` times polylog constants small | lower | yes |
| [V] (1.78) | `(100 M (L+1) N^{β0} R_j)^{d+2}` absorbed into `R_j^{d+5}` | needs `N^{β0(d+2)} ≲ R_j³` | yes with `β0 ≤ 3r/((d+2) p0)` (β0 is a free small constant) |
| [V] (1.80)-(1.85) | a factor `exp(-κ_j(Z))` controls `K ≤ n0 - j + R_j` steps (Balaban takes the delay `N = R_j`); the cost is `∑ O(1) M^d R_n^{d+1} d'_n` over those steps ((1.81)); squared factors need `¼γ0 (14)^{-d} A1² p0² ≥ O(1) 2 (64)^d M^d L^{d+1} R^{d+2}` ((1.82)); preparatory factors `exp(-p0)` ((1.79) last product, (1.83)ff) | upper: cost `∝ N` | see 1.2 |

### 1.1 The artefact at [IV] p. 198

In (1.94) Balaban bounds `B3 δ'_k ≤ B3 (1+β0) N^{1/2} (A1 p1(g_h)/(A0 p0(g_h))) ε_h`. With `δ'_k = g_k A1 p1(g_k)` and
`ε_h = g_h p0(g_h)` this is the bound `g_k/g_h ≤ (1+β0) N^{1/2}` (and `p1(g_k) ≤ p1(g_h)`, since `g_h ≤ g_k`). The
running coupling changes by a bounded amount per step: `|g_{j+1}^{-2} - g_j^{-2}| ≤ O(1)` ([I] (0.20), (1.22): the
β-functions are bounded on `[0, γ]`). Hence `g_k²/g_h² = 1 + g_k²(g_h^{-2} - g_k^{-2}) ≤ 1 + O(1) N g_k²`. For
`N ≤ (log g_k^{-2})^μ`, any fixed `μ`, `N g_k² ≤ γ² (log γ^{-2})^μ` (the function `x (log 1/x)^μ` increases for small
`x`), which is `≤ 1` for `γ` small. So `g_k/g_h ≤ √2`, and the first condition of (1.94) reduces to
`√2 B3 A1 p1(g_h)/(A0 p0(g_h)) < α/2`, true for `p1 < p0` and `g` small. The constraint `½ν ≤ p0 - p1 - 1` is not
needed. (The same `N^{1/2}` appears in the second term of (1.94) and on [IV] p. 199; there it only enlarges lower
bounds.)

### 1.2 The induction (1.80)-(1.85) with a longer delay

A factor must pay `O(1) M^d R^{d+1}` per step of delay ((1.81); origin: every large-field domain contributes the
normalisation constant `O(1) log g_j^{-2} |Z_j| ≤ O(1) M^d R_j^{d+1} d'_j(Z_j)`, [V] p. 380). With delay `N` instead
of `R`:
* squared large-field factors: `¼γ0 (14)^{-d} A1² p0² ≥ O(1) M^d L^{d+1} R^{d+1} N`. For `N ≈ A0 (log g^{-2})^{p0}/(d log L)`
  this is `(log g^{-2})^{2p0}` against `(log g^{-2})^{p0 + (d+1) r}`: holds if `p0 > (d+1) r` (Balaban already has
  `p0 ≥ 5r` for `d = 4`; take it strict).
* the weakest preparatory factor is `exp(-R_j^{-d-5} p1²(g_j))` ((1.78), from `1 - χ'`), which Balaban bounds by
  `exp(-p0)` using `2p1 - (d+5) r0 > p0`. Keeping `R^{-d-5} p1²` instead: `R^{-d-5} p1² ≥ O(1) M^d R^{d+1} N` needs
  `2p1 - (d+5) r > p0 + (d+1) r`, i.e. `p1 > (p0 + (2d+6) r)/2`. With `p1 < p0` (1.1) this is possible iff
  `p0 > (2d+6) r` (`p0 > 14 r` for `d = 4`).
* the other preparatory factors are squared (`exp(-A1² p0²)`, `exp(-γ0 A1² p1²)`) and are covered by the same
  conditions.

So the size of `N` can be arranged. (A full re-check of every constant in (1.86)-(1.89) and p. 389 under the retuned
exponents is routine and not done here.)

## 2. The rate obstruction

**Setting.** The device: i.i.d. uniform shifts `s_j ∈ {0, …, L-1}^d` of the block grid (free, `NOTE.md` 2.5). A deep
core that has not become moderate by the time its region should be renormalised (age `N`) cannot be renormalised
(branch (a), no fresh field factor, `NOTE.md` 2.4); the device was to give such a term the shift-weight
`P_shift(core still deep) ≤ p_stay^N` in place of the fresh factor.

**Lower bound on persistence (paper, elementary).** Take the vortex core of `NOTE.md` 2.4 at a fine site `z`. At each
step the shift that puts a block centre at the current site of the core has probability exactly `L^{-d}`, and on that
event the vortex is reproduced exactly at the next scale (`vortex_persists`; the next site is again a coarse site).
By independence, `P_shift(persist n steps) ≥ L^{-dn}`. So `p_stay ≥ L^{-d}`, whatever averaging (covariant,
symmetric) is used.

**Cost of persistence in Balaban's bookkeeping.** While the core is not renormalised, its region `Z_j` (a union of
`M R_j`-cubes, so `|Z_j| ≥ (M R_j)^d` at scale `j`) pays `exp(O(1) log g_j^{-2} |Z_j|)` per step ([V] p. 380, (1.79)).
A persistent term at age `a` past the first window therefore has weight bound at least of order
`L^{-d a} exp(c a (M R)^d log g^{-2})` times what it had at age `N`, with `c > 0` the constant of [V] p. 380.

**Conclusion.** `L^{-d} exp(c (M R)^d log g^{-2}) ≥ L^{-d} g^{-2c M^d R^d} → ∞` as `g → 0` (and is huge already for
the `M`, `R` Balaban needs). The series over persistence times diverges, so the persistent terms cannot be bounded,
and no fresh factor can be manufactured from the shifts, for any `N`. Equivalently: a fresh factor must pay
`O(1) M^d R^{d+1}` per step of the life it controls, while the shift device yields at most `d log L` per step.
**Claim level:** this is a statement about Balaban's bookkeeping (his upper bounds charge this cost), not a lower bound
on the true law.

## 3. The true law is not the obstacle (paper, sketch)

A deep core persists only while it sits at a block centre: one site per coarse cell, with or without shifts (with
shifts the site is random but still one per cell). Its weight carries the fine Wilson action `exp(-A/g_h²)`, `A` the
action of the core in units of `1/g²` (`A = 32` for the vortex star: 16 fine plaquettes at `-1`, each contributing 2).
If `g^{-2}` grows by at least `b log L` per step towards finer scales (`b > 0`; the asymptotic-freedom content of
[I] (0.20), (0.31) and Theorem 2, whose proof is unpublished; one loop gives `b = 2·22/(3·16π²) ≈ 0.09` for SU(2)), then
the expected number of pinned persistent deep cores at a given coarse site is at most
`∑_h exp(-A/g_h²) ≤ exp(-A/g_k²)/(1 - L^{-b A})`: rare. So the law-level statement M1
needs is plausible; what fails is Balaban's accounting, which charges every unrenormalised region by its volume.

## 4. What could replace the device (open)

* **I1, pinned-defect renormalisation (most promising).** Renormalise the regular part of an old region by `R̂` and
  keep only the deep star of the pinned site unrenormalised, so that the carried object has `O(1)` bonds and costs
  `O(1)` per step instead of `O((M R)^d log g^{-2})`. Needs a small-field theory with one pinned irregular coarse star
  (localization around a region much smaller than Balaban's `M R`-cubes). For a central-valued (vortex-type) star the
  fluctuation operator in the adjoint is the same as at the trivial field (central holonomies act trivially in the
  adjoint), which is a hint that this is possible; for general deep stars it is not clear. Then the gain per step
  (asymptotic freedom `b A log L`, plus `d log L` from shifts if used) must beat an `O(1)` cost: a contest of
  constants, open.
* **I2, deep cores as an exceptional set outside the RG.** Use the bound of section 3 directly and run the RG on the
  complement. Conditioning on the complement destroys the product structure Balaban uses; this would need the
  mixture form of the defect interface (`../c5d-supplier/BALABAN-READING.md` section 5) at all intermediate scales.
  Open.

## 5. Consequences for M1

* Row D-N: **answered**. `N ≈ p0(g)/(d log L)` is admissible after removing the [IV] p. 198 artefact and retuning
  `p0 > (2d+6) r`, `(p0 + (2d+6) r)/2 < p1 < p0`, `β0` small; but the random-shift device fails by the rate argument,
  for every `N`.
* Row D-prob: the shift-probability estimate may well be true, but it **cannot** be used inside Balaban's bookkeeping;
  demoted to "not needed unless I1 is built".
* Deep cores pinned at nested block centres: **open, and now without a candidate device inside Balaban's framework**.
  The next step is I1 (a scoping test like ONE-STEP: can a pinned irregular coarse star be carried at `O(1)` cost per
  step?).
* Row V1: `[15]` Theorem 1 (pp. 278-279) proves existence, uniqueness and regularity of the minimal orbit for nested
  determining sets `Ω_0 ⊃ … ⊃ Ω_k` with scale-`j` averages fixed on `Ω_j \ Ω_{j+1}` (coarser inside) and distance
  condition (1) `dist(Ω_j^c, Ω_{j+1}) > R M_1` in scale-`j` units. The two-scale set of the conditional step is of
  this kind; what remains is to check condition (1) for `Λ` inside `Z` (routine).
