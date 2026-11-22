# P2′: subscale-hole decoupling (m1-tools, 2026-11-22; version 2, the proof)

Brief: Lemma P2′ (`P0.md` 5, `D-PIN.md`): what is left of a pinned deep core at later scales is a frozen hole, and its
effect on the conditional step must be small and summable over the core's life. Version 1 was a sketch; this version
gives the proof, with three inputs from Balaban's papers named explicitly (bounds that are proved there and used here as
black boxes). Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **Theorem P2′.** A frozen hole of diameter `D0` (in root-scale units) changes the conditional step at scale `k` by a
   factor `exp(Δ_k)` with
   `|Δ_k| ≤ C [ρ_k^{d-2} (1 + p0(g_k)²) + ρ_k^{(d-2)/2} p0(g_k) (1 + a^{1/2}/g_h)]`, `ρ_k = D0 L^{-(k-h)}`,
   where `a/g_h²` is the root core's own action. Summed over the core's life this is at most
   `C (D0^{d-2} p0(g_h)² + D0^{(d-2)/2} p0(g_h) a^{1/2}/g_h)`, negligible against the root suppression `exp(-a/g_h²)`.
2. **What is proved here, fully:** the discrete capacity lemma (Lemma A, an explicit cutoff construction), the
   reduction of the hole to a small positive correction of the quadratic form (Lemma B), the determinant bound
   (Lemma C), the background bound with the root's own action split off (Lemma D), the choice of the hole that makes
   Balaban's variational theorem apply (section 3), and the summation.
3. **What is used from Balaban without reproof (named inputs):** (I1) the regularity of the fine realisation of a
   block-field fluctuation (`[15]` Theorem 1, (9)-(10)); (I2) boundedness of the fluctuation propagators at each scale
   ([13], [II]); (I3) analytic dependence of the local terms on background and covariance, with the bounds of [I] (1.18),
   [II] (2.41), [III] (2.31), (2.42) (Lemma E). These are proved in Balaban's papers for exactly these objects; the
   only new thing asked of them is a small perturbation, which their analyticity domains cover.
4. **Status:** proof, conditional on I1-I3 as stated. The earlier version's weak spot (the local terms, rate
   `ρ^{(d-2)/2}`) is now handled through Lemma E; the rate in the theorem has the `ρ^{(d-2)/2}` term only through the
   cross term with the root's own action, which is summable.

## 1. Setting

* Root at scale `h`, site `z`; label field `λ` (`TWIST.md` 1); corrected field `S = λU`.
* **The hole** `H` (section 3): the scale-`h` bonds of the root's large-field region that are not `ε_h`-regular in the
  corrected field, together with the label's vortex plaquettes. Its diameter is `D0 ≤ 100 M R_h` scale-`h` units
  (Balaban's condition (i), [IV] p. 177). Its variables are integrated once, at the root (their weight is the root's
  weight, at most `exp(-a/g_h²)` times Balaban's normalisation), and are frozen afterwards.
* At scale `k > h`, `ρ_k = D0 L^{-(k-h)}` is the hole's diameter in scale-`k` units. Until `ρ_k ≤ 1` (that is for
  `log_L D0 = O(log log g_h^{-2})` steps) the hole is carried as a Balaban large-field region, at polylogarithmic cost
  per step, paid by the root suppression.
* `Δ_k = log[(N/D)_{hole} / (N/D)_{no hole}]`, where "no hole" is the same step with the hole's variables treated as
  ordinary small-field variables; it measures what carrying the frozen hole costs at scale `k`.

## 2. The lemmas

Units: fine (scale-`h`) lattice spacing 1. In four dimensions the Wilson quadratic form `Σ_p |dχ(p)|²` is
scale-invariant, so energies computed in fine units equal energies in scale-`k` units. A scale-`k` field of size `A`
(scale-`k` units) has fine bond variables of size `A L^{-(k-h)}` (bond variables scale with bond length).

**Lemma A (discrete capacity, proved).** Let `H` lie in the cube `Q_D` of side `D ≥ 1` and let `m` be a Lie-algebra-
valued 1-form on the bonds of `Q_{3D}` (concentric) with `|m| ≤ M` and `|m(b) - m(b')| ≤ M' |b - b'|`. Then there is a
1-form `χ` with `χ = m` on the bonds of `H`, support in `Q_{3D}`, and
`Σ_p |dχ(p)|² ≤ C_d D^{d-2} (M² + D² M'²)`, `Σ_b |χ(b)|² ≤ C_d D^d M²`.

*Proof.* Let `φ(x) = max(0, 1 - dist_∞(x, Q_D)/D)` and `χ(b) = φ(mid b) m(b)`. On a plaquette `p`, `dχ(p)` is the
alternating sum of `χ` over its four bonds; write `χ = φ m` and use `|φ(x) - φ(y)| ≤ |x - y|/D`, `|m| ≤ M`,
`|m(b) - m(b')| ≤ M'`: `|dχ(p)| ≤ |φ|·|dm(p)| + 4 M/D ≤ 4 M' + 4M/D` on `Q_{3D}`, and `dχ = 0` outside `Q_{3D}`.
Summing over the at most `d² (3D)^d` plaquettes of `Q_{3D}`: `Σ |dχ|² ≤ C_d D^d (M/D + M')²
≤ 2 C_d D^{d-2} (M² + D² M'²)`. The second bound is `|Q_{3D}| M²`. ∎

The minimum of `Σ_p |dχ|²` over `χ` with `χ|_H = m` (the capacity form) is therefore at most `C D^{d-2}(M² + D²M'²)`.

**Lemma B (the hole is a small positive correction of the quadratic form; proved given I1).** Let `Q_k` be the
quadratic form of the scale-`k` fluctuation integral (fluctuation `A`) and `R_k A` the fine realisation of `A` near `H`
(the linear response of the background minimiser). With the hole frozen, the fine field is `R_k A + χ_A`, where `χ_A`
is the least-energy correction with `χ_A|_H = -R_k A|_H`. The fluctuation integral with the hole has the quadratic form
`Q_k + δQ_H` with
`0 ≤ δQ_H(A) ≤ C ρ_k^{d-2} ‖A‖²_{loc}`,
`‖A‖_loc` the sup of `|A|` within scale-`k` distance 2 of the hole.
*Proof.* `δQ_H(A)` is the capacity form at the data `m = R_k A|_{Q_{3D}}`. By I1, `|R_k A| ≤ C ‖A‖_loc L^{-(k-h)}` and
`|∇ R_k A| ≤ C ‖A‖_loc L^{-2(k-h)}` per fine unit near `H` (regularity of the minimiser, `[15]` (9)-(10)). Lemma A gives
`δQ_H(A) ≤ C D0^{d-2} ‖A‖²_loc (L^{-2(k-h)} + D0² L^{-4(k-h)}) ≤ C' (D0 L^{-(k-h)})^{2} ‖A‖²_loc` in `d = 4`, i.e.
`C' ρ_k^{d-2} ‖A‖²_loc` (using `D0 L^{-(k-h)} = ρ_k ≤ 1`). The mass-type terms of `Q_k` (block constraints of the coarser
scales) contribute at most `Σ_b |χ|² L^{-2(k-h)} ≤ C D0^d ‖A‖²_loc L^{-4(k-h)} ≤ C ρ_k^{d-2} ‖A‖²_loc` as well.
Positivity: `δQ_H` is a minimum of a positive form. ∎

**Lemma C (fluctuation determinant; proved given I2).**
`0 ≤ log det(1 + Γ_k^{1/2} δQ_H Γ_k^{1/2}) ≤ tr(Γ_k δQ_H) ≤ C ρ_k^{d-2}`, where `Γ_k = Q_k^{-1}` is the scale-`k`
propagator. *Proof.* `log det(1 + X) ≤ tr X` for `X ≥ 0`; `δQ_H` is bounded by `C ρ^{d-2}` times the local norm near
the hole (Lemma B), and `Γ_k` is bounded with exponential decay in scale-`k` units (I2), so the trace is
`≤ C ρ^{d-2} Σ_{x near H} |Γ_k(x,x)| ≤ C' ρ^{d-2}`. ∎ The same change occurs in `N` and `D` when the reference kernel is
built with the hole; it then cancels in `N/D`. Without that choice it is bounded by Lemma C.

**Lemma D (background; proved given I1).** Let `m = m_0 + m_k` be the mismatch on `H` between the frozen data and the
unconstrained background at scale `k`: `m_0` the frozen data minus the root-scale background (fixed; its capacity
energy `E_0` is part of the root's action, `g_h^{-2} E_0 ≤ a/g_h²`), and `m_k` the change of the unconstrained
background near `H` between scales `h` and `k` (smooth, `|m_k| ≤ C ε_k L^{-(k-h)}` in fine units, by I1). The capacity
energy is a positive quadratic form `K` in `m`, so the change of the background action is
`g_k^{-2} |⟨m, K m⟩ - ⟨m_0, K m_0⟩| ≤ g_k^{-2} (2 ⟨m_0, K m_0⟩^{1/2} ⟨m_k, K m_k⟩^{1/2} + ⟨m_k, K m_k⟩)`
`≤ C ρ_k^{(d-2)/2} p0(g_k) a^{1/2}/g_h + C ρ_k^{d-2} p0(g_k)²`
(Lemma A with smooth data of size `ε_k L^{-(k-h)}` gives `⟨m_k, K m_k⟩ ≤ C ρ^{d-2} ε_k²`, and `g_k^{-2} ε_k² = p0(g_k)²`
since `ε_k = g_k p0(g_k)`; in the cross term `E_0 ≤ a`, so it is `≤ 2C g_k^{-2} a^{1/2} ρ^{(d-2)/2} ε_k
= 2C ρ^{(d-2)/2} a^{1/2} p0(g_k)/g_k ≤ 2C ρ^{(d-2)/2} p0(g_k) a^{1/2}/g_h`, as `g_h ≤ g_k`). ∎

**Lemma E (local terms; input I3).** Balaban's local terms (`E`, `R`, `B`) on domains `X` are analytic functions of the
background on `X` and of the propagator, bounded on complex neighbourhoods of radius `α_{0,k}, α_{1,k}` with the bounds
[I] (1.18), [II] (2.41), [III] (2.31), (2.42). The hole changes the propagator by `δΓ = -Γ δQ_H Γ + …` (norm
`≤ C ρ^{d-2}`, Lemmas B-C) and the background by `χ` (energy `≤` Lemma D's bound, hence sup norm on domains at scale-`k`
distance `≥ 1` from the hole `≤ C ρ^{(d-2)/2}` times the mismatch, by elliptic decay). Cauchy estimates on the
analyticity domains give a total change `Σ_X e^{κ d(X)} |δE(X)| ≤ C [ρ^{d-2} + ρ^{(d-2)/2} (p0 + a^{1/2}/g_h)]`.
*Status:* this is the step that uses Balaban's expansions as a black box (their analyticity in background and
covariance is how they are built; the perturbation is small compared with the analyticity radii because
`ρ^{(d-2)/2} ≤ 1` and the mismatch is of small-field size). Not reproved.

**Theorem P2′.** `|Δ_k| ≤ C [ρ_k^{d-2} (1 + p0(g_k)²) + ρ_k^{(d-2)/2} p0(g_k) (1 + a^{1/2}/g_h)]` (Lemmas C, D, E).

**Corollary (summation).** With `ρ_k = D0 L^{-(k-h)}` and `p0(g_k) ≤ p0(g_h)`:
`Σ_k |Δ_k| ≤ C [D0^{d-2} p0(g_h)² + D0^{(d-2)/2} p0(g_h) (1 + a^{1/2}/g_h)] / (1 - L^{-(d-2)/2})`.
With `D0 ≤ 100 M R_h` (polylog) and `a ≥ A_min`, this is `≤ polylog(g_h^{-2}) + polylog · a^{1/2}/g_h ≪ a/g_h²`. With the
polylogarithmic cost of the first `log_L D0` steps (section 1) the whole carrying cost of a root is `≪ a/g_h²`, and the
root sum of `D-PIN.md` 4(a) closes: `Σ_roots ≤ C exp(-A_min/(2 g_k²)) ≪ exp(-p0(g_k))`.

## 3. The hole as boundary data in `[15]` (checked here)

`[15]` Theorem 1 minimises the Wilson action over configurations on `Ω_0` with nested domains `Ω_0 ⊃ … ⊃ Ω_k`,
scale-`j` averages fixed on `Λ_j = Ω_j \ Ω_{j+1}`, under (1) `dist(Ω_j^c, Ω_{j+1}) > R M_1` (scale-`j` units, `R ≥ R_1`
fixed) and (2) regularity of the configuration on `Ω_j` (`[15]` (2)). The carried hole fits as follows: take `Ω_h^c` =
the hole (its bonds enter only through plaquettes at the boundary of `Ω_h`, as fixed data), and shells `Λ_j` of width
`R_1 M_1` at each scale `j = h, …, k` around it (a funnel). (1) holds by construction with the fixed `R_1` (not
Balaban's polylog `R_j`, which is needed only for entropy). (2) needs the corrected field to be regular on `Ω_h`, in
particular on the plaquettes touching the hole: this is why the hole is taken to be the **whole** non-`ε_h`-regular part
of the root's region (section 1), not just the vortex plaquettes. After `n_mod` steps of Lemma D-mod the corrected
images are small, and the funnel's shells are regular. So `[15]` Theorem 1 gives the background used in Lemmas B and D.

## 4. What is not covered

* I1-I3 are used as black boxes (statements cited; their extension to the perturbed objects is by analyticity, not
  reproved line by line).
* The constant `C` is not computed (Balaban's constants are not explicit either).
* Lean: nothing here is elementary enough to be worth formalising yet (the only elementary piece, Lemma A, is a cutoff
  construction whose formal version would mostly be lattice-counting bookkeeping).
