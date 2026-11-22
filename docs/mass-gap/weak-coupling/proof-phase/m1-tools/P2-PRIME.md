# P2′: subscale-hole decoupling (m1-tools, 2026-11-22)

Brief: Lemma P2′ of `P0.md` 5: after a deep pinned core has been labelled at its root (scale `h`) and its corrected
field has become small (Lemma D-mod), what remains of it at a later scale `k` is a frozen hole: the few fine plaquettes
on which the label field has `-1` (the label's vortex sheet), whose variables cannot be integrated as Gaussian
fluctuations (their action term has the wrong sign there). P2′ asks that the effect of this hole on the conditional
step at scale `k` be small and summable over `k`. Paper level; claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **Statement.** At scale `k` the hole has diameter `ρ_k = D0 L^{-(k-h)}` in scale-`k` units. The factor by which it
   changes the conditional step's ratio `N/D` is `exp(Δ_k)` with `|Δ_k| ≤ C ρ_k^{(d-2)/2} (1 + p0(g_k)²)`, that is
   `C D0 L^{-(k-h)} (1 + p0(g_k)²)` in `d = 4` (the background and fluctuation parts give the better `ρ_k^{d-2}`; the
   local terms, as estimated here, only `ρ_k^{(d-2)/2}`).
2. **Summed over the core's life** the effect is at most `C' D0 p0(g_h)²`: a polylogarithm of `g_h^{-2}`, negligible
   against the root suppression `exp(-A_min/g_h²)`. So the root sum of `D-PIN.md` 4(a) closes without the rate
   condition P3.
3. **Why.** Three contributions, each controlled by how much a small set can disturb a smooth field in four dimensions
   (its capacity, `ρ^{d-2}`): the background minimiser must bend around the frozen values (cost `g^{-2}` times capacity
   times the mismatch squared, and the mismatch is of small-field size `ε_k = g_k p0(g_k)`); the Gaussian fluctuation
   integral loses the hole's directions (a finite-rank change of size capacity); Balaban's local terms near the hole
   change only through the background (Cauchy bounds).
4. **Status: paper sketch, not a proof.** The missing pieces are standard in kind but technical: a discrete capacity
   bound for Balaban's gauge-fixed quadratic forms with his propagator bounds ([13]), the hole as boundary data in the
   variational problem (`[15]` Theorem 1 with fixed-width shells), and the dependence of the local terms on the hole.
   About 3 pages in Balaban's density. A heuristic based on gauge invariance suggests the sharper rate
   `ρ^4 = L^{-4(k-h)}`; the statement uses the conservative `ρ²`.

## 1. Setting

* Root at scale `h`, site `z`; label field `λ` created there (`TWIST.md` 1); corrected field `S = λ U`.
* For the first `n_mod = O(log g_h^{-2} / log L)` steps the corrected core is moderate, not small; the core region is
  carried as a Balaban large-field region (volume cost `O(1) M^d R^{d+1}` per step, `D-N.md` 2), paid by the root
  suppression `exp(-A_min/g_h²)`: total `n_mod · O(1) M^d R^{d+1} = polylog(g_h^{-2}) ≪ A_min/g_h²`.
* From then on `S` is small-field everywhere near the core. The **hole** `H` is the set of fine plaquettes with
  `λ_p = -1` (the label's vortex sheet, `D0` plaquettes across, e.g. the 16 plaquettes at `z` for the vortex star of
  `NOTE.md` 2.4) together with their bonds. The Wilson action there is `g^{-2}(1 + Re tr S_p)`, maximal at `S_p = 1`:
  these variables are frozen (their integral is part of the root's weight, bounded once).
* At scale `k > h` the conditional step (`ONE-STEP.md` 2.1) resamples the corrected field on `Λ` with the next field
  and the hole fixed (`TWIST.md` 2: exactness with the hole in the conditioning variable). `N(W)`, `D(W)` are its fibre
  integrals with the hole present; `N_0`, `D_0` the same with the hole's variables treated as ordinary small-field
  variables. `Δ_k = log[(N/D)/(N_0/D_0)]`.

## 2. Statement

**Lemma P2′ (target).** There are constants `C`, independent of `k`, `h`, `g` and the volume, such that for every
`W` regular in the twisted sense and every frozen hole of diameter `ρ_k ≤ 1` (scale-`k` units) inside `Λ`:
`|Δ_k| ≤ C ρ_k^{(d-2)/2} (1 + p0(g_k)²)` (and `C ρ_k^{d-2}(1 + p0(g_k)²)` if 3(c) is sharpened). The bound also holds for the analytic extension to the complex domain of
Balaban's R-terms (`[V]` (1.73)-(1.75)), with the same constant up to a factor `e^{O(1)}`.

**Corollary (summation).** `∑_{k > h + n_mod} |Δ_k| ≤ C D0^{(d-2)/2} ∑_j L^{-(d-2) j/2} (1 + p0(g_h)²) ≤ C' D0^{(d-2)/2} p0(g_h)²`
(since `g_k ≥ g_h` gives `p0(g_k) ≤ p0(g_h)`). With `D-PIN.md` 4(a) the root sum is then
`≤ ∑_h O(R0^d) exp(C' D0 p0(g_h)² + polylog) exp(-A_min/g_h²) ≤ C exp(-A_min/(2 g_k²)) ≪ exp(-p0(g_k))`.

## 3. Proof sketch

**(a) Background.** Balaban's background at scale `k` is the minimiser of the Wilson action subject to the block
constraints (`[15]` Theorem 1, nested shells of fixed width `R_1 M_1`). With the hole frozen, the minimiser solves
the same problem with additional Dirichlet data on `H`. Write the constrained minimiser as the free one plus a
correction `χ` with `χ|_H = m` (the mismatch between the frozen values and the free minimiser on `H`). In the
small-field regime the action is `g_k^{-2}` times a positive quadratic form `Q` plus higher order ([V] (1.7)-(1.9),
`[15]` (9)-(10)); minimising `Q(χ)` subject to `χ|_H = m` costs `cap_Q(H) |m|²`, where `cap_Q` is the discrete
capacity of `H` for `Q`. For a set of diameter `ρ` (scale-`k` units) and a form comparable to the lattice Laplacian on
1-forms in `d ≥ 3`, `cap_Q(H) ≤ C ρ^{d-2}` (Newtonian scaling; on the lattice the bound holds down to one fine
spacing). Both the frozen values and the free minimiser are small-field, so `|m| ≤ C ε_k = C g_k p0(g_k)`. Hence the
change of the background action is `≤ C g_k^{-2} ρ^{d-2} ε_k² = C ρ^{d-2} p0(g_k)²`. It enters `N` and `D` with the
same background except through this term, so it bounds the background part of `Δ_k`.

**(b) Fluctuations.** `N` and `D` are, after Balaban's expansions, Gaussian integrals with covariance `Γ_k` (the
fluctuation propagator at scale `k`, bounded and exponentially decaying in scale-`k` units, [13]) times analytic
corrections. Freezing the hole removes the hole's directions: the ratio of normalisations is
`det(1 - P_H Γ_k^{1/2} … )`-type, a finite-rank perturbation whose trace is bounded by the capacity of `H` for `Γ_k^{-1}`,
again `≤ C ρ^{d-2}`. The same holds for the reference kernel in `D`, so in `N/D` this part is bounded by
`C ρ^{d-2}` (it does not even need to cancel).

**(c) Local terms.** Balaban's `E`, `R`, `B` terms with localization domain `X` meeting the neighbourhood of `H` are
analytic functions of the background on `X` with sup bounds `O(e^{-κ d(X)})` ([I] (1.18), [III] (2.31), (2.42)). The hole
changes the background on `X` by `χ`, with `‖χ‖ ≤ C ρ^{(d-2)/2} ε_k` in the energy norm, hence in sup norm on `X`
away from `H` (elliptic regularity); Cauchy bounds give a change `≤ C ρ^{(d-2)/2}` per domain, summed with
`e^{-κ d(X)}`. (This is the weakest of the three; it gives `ρ^{(d-2)/2} = ρ` in `d = 4`, still summable as
`L^{-(k-h)}`. The statement in section 2 should read `ρ_k^{(d-2)/2}` if this part cannot be improved; the summation
conclusion is unchanged; section 2 states this weaker rate.)

**Heuristic for a sharper rate.** The hole is frozen only up to gauge transformations at its interior sites, so only its
gauge-invariant data (holonomies of small loops) are fixed. A smooth scale-`k` fluctuation changes those by curvature
times area, `O(g ρ²)`, which would give `ρ^4` instead of `ρ^{d-2}`.

## 4. What is missing (about 3 pages)

1. A discrete capacity lemma for Balaban's gauge-fixed quadratic forms (axial and Landau gauges, multi-scale
   determining sets), using the propagator bounds of [13] and [II] Lemma 1-3. Standard type.
2. The hole as Dirichlet data in `[15]` Theorem 1 (the theorem is stated for nested domains with fixed-width shells;
   a frozen subscale set is a domain `Ω_0^c` of that kind; the distance condition (1) must be checked).
3. The local-term estimate (c) with the sharper exponent, or acceptance of `ρ^{(d-2)/2}`.

## 5. Effect

With P2′ (even with the weaker exponent of 3(c)) the carrying cost of a pinned root is summable, and the root sum
closes for every root kind (threshold factors included). P3 (the rate condition) is then not needed. The deep-pinned-
core part of M1 rests on P0 (written in `TWIST.md`; no-trapping numerical), P2′ (this sketch) and P4 (citation level).
