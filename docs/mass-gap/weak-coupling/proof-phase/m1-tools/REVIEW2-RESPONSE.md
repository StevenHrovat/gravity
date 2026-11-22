# Response to REVIEW-2 (m1-tools, 2026-11-22)

Brief (coordinator): read `../m1-review/REVIEW-2.md`; for each finding say whether I agree, with the reason, and work
through them in the order G3, G2, G6, G5, G4, then G1 and the smaller points; stop at the first that is fatal or much
harder than marked. Claim marks as in `NOTE.md`.

## 0. Summary

| finding | agree? | outcome |
|---|---|---|
| G3 decoder probability | **yes**: the `C^n` count is wrong (`(n!)^4` shapes) and the merging rule percolates in large volume | **repaired (paper)**: Peierls over components of the conflict graph of positive-gain closed sets; uniform in the volume, no percolation for `β` large (section 1) |
| G2 labels in Balaban's form | **yes**: as written the labels are neither small-field (R9) nor Balaban large-field regions, and carrying them diverges | **repaired (paper sketch)**: labels become decorations of released polymers; small-field means SO(3)-regular only; each label is an explicit factor `ζ_b(V)` = activity × exp(small local analytic term) (section 2) |
| G6 extended holes | **yes**: thin centre-flux sheets are deep in SO(3) but invisible to holonomies; growth cap and filling were stated only for compact holes | **repaired (paper)**: cap the number of layers, not the extent; filling of thin slabs in local gauges with the Dirichlet gap set by the thickness (section 3) |
| G5 SU(2) encoding | **yes**: the lift-branch sign depends on the gauge representative | **no covariant SU(2) encoding is proposed**; the interface should take the block state as SO(3) × closed Z2 with gauge-invariant observables. That is a change to the interface and to the P4/one-box statements, not to M1 (section 4) |
| G4 hand-over | **yes** on all four points | M1 can deliver: (a) the law in inductive form; (b) an `L¹` UV transfer for character polynomials of **block variables at a fixed physical scale** (constants uniform in spacing and volume). The RP upgrade must be done **in the limit**, not on finite tori: `MassGapLoc` is reachable, `TorusDecayLoc` this way is not (section 5) |
| G1 S1 for the current design | **yes** | written: `S1-CURRENT.md` (`Form_k` for `(V_k, τ'_k)`, the one-step bookkeeping, the E-rows re-checked for what changes) |
| F7 Lean stale | yes | rows updated in `Assembly.lean` (section 6); signed or complex densities stated (paper) |
| N1 R7 | yes | restated: `poly(β)^{|τ|}`, with freed bonds counted (section 6) |
| N2 twist sectors | yes | `DECODER-LOCAL.md` 6.4 withdrawn (not volume-uniform; not used) |
| N3 smaller points | yes | `EXTERNAL.md` row 1 rate added; `M1-PLAN.md` updated; `[III]` exponent pinned (`r ≥ 2`); `FILL.md` gauge selection added |

No finding turned out fatal. G2 and G4(b) are at sketch level.

## 1. G3: the decoder's locality, done with the right objects

* **The decoder as a packing.** Closed 2-cochains are sums of their components (each closed). For a family of closed
  connected sets `S_i` with pairwise disjoint supports, `|τ + Σ S_i| = |τ| - Σ_i g(S_i)`, with gain
  `g(S) := 2|τ ∩ S| - |S|`. The decoder is therefore a **maximum-weight packing** of positive-gain closed connected sets
  (ties: smaller `|σ|`, then a fixed rule). Components of the optimum have `g > 0` (`DECODER-LOCAL.md` 3).
* **Exact locality.** Let `𝒢` be the conflict graph: vertices are the positive-gain closed connected sets; edges join two
  sets whose supports share a plaquette or a cube (they could not both be chosen as separate components). A maximum-weight
  packing decomposes over the connected components of `𝒢`, with the tie-break per component. So the decoder output at a
  plaquette `q` is a function of `τ` on the union `U(q)` of the `𝒢`-component containing the sets near `q`.
* **Peierls bound.** If `U(q)` reaches distance `r`, take a shortest `𝒢`-path `S_1, …, S_m` from a set at `q` to one at
  distance `r`. In a shortest path each plaquette lies in at most two consecutive members (a plaquette in `S_i` and
  `S_{i+2}` would allow a shortcut). Hence for `U = ∪ S_i`: `U` is connected, `|U| ≥ r`, and
  `|τ ∩ U| ≥ ½ Σ |τ ∩ S_i| > ¼ Σ |S_i| ≥ ¼ |U|`.
  The number of connected plaquette sets of size `u` containing `q` is `≤ C_d^u`. The choices of which `≥ u/4` of them
  are flipped number `≤ 2^u`. The probability that a given set of `m` plaquettes are all flipped is
  `≤ (c β^{3/2} e^{-β})^m` (N1 below). So
  `P(the decoder at q depends on τ beyond distance r) ≤ Σ_{u ≥ r} (2 C_d)^u (c β^{3/2} e^{-β})^{u/4}`,
  which decays exponentially in `r`, uniformly in the volume, once `β > 4 log(2 C_d c') + O(log β)` (bare weak coupling).
* **No percolation.** The same sum bounds the probability that `U(q)` is infinite, or wraps the torus: zero in the limit,
  uniformly. The merging rule of `DECODER-LOCAL.md` 2 (which percolates) is **withdrawn**. The deterministic lemma of
  `DECODER-LOCAL.md` 3 stays true but is no longer used.
* **Balaban's regions.** Each large-field region is enlarged by the `𝒢`-components meeting it; a component of size `u`
  carries `≥ u/4` flips, each suppressed by `β` (bare). The entropy of the enlargement is paid inside the Peierls sum.

**Status:** paper. `DECODER-LOCAL.md` sections 2, 4 and 6.1 (probabilistic part) are superseded by this section.

## 2. G2: labels as decorations of released polymers

* **Where a label comes from.** A coarse bit `τ'_k(P) = -1` comes from a bare positive-gain closed set `S` linked with
  the scale-`k` 1-skeleton (`CLOSING.md` 2). The bare flips in `S` are a bare large-field event. Its SO(3) part
  (plaquettes at the cut) is excised, filled and released within the window, like every large-field region. What
  survives is only the **index**: whether, and on which skeleton bonds, the remainder links the skeleton.
* **Where it sits in the representation.** In the Mayer expansion of the release ([V] (1.90)), split each polymer's
  activity by this index: `F(X') = F_0(X') + Σ_{ℓ ≠ 0} F_ℓ(X')`. The unlabelled parts `F_0` are exponentiated as usual
  ((1.98)-(1.100): R- and B-terms). The labelled parts are kept as **explicit factors**, because the label is a variable
  of the law. A labelled factor is `F_ℓ(X'; V) = a_ℓ · (1 + h_ℓ(V))`. Here `a_ℓ` is a constant with
  `|a_ℓ| ≤ e^{-16/g_0²} poly(β)` per labelled skeleton bond (`CLOSING.md` 2, N1), and `h_ℓ` is analytic, local,
  gauge-invariant and small. So `F_ℓ = a_ℓ e^{log(1 + h_ℓ)}`: a constant times the exponential of a small local term,
  which fits Balaban's form as an E-type term with an index-dependent constant.
* **Small-field definition (R9 amended).** At scales `≥ 1`, small field means SO(3)-regular; the condition `τ = +1` is
  dropped. The label does not touch the SO(3) small-field analysis: it enters only through `a_ℓ` (a constant) and
  `log(1 + h_ℓ)` (a local analytic term). R9's table row 1 is changed accordingly.
* **No carrying cost.** A label is not a large-field region: it gets no large-field factor ([V] (1.76)) and needs none,
  and it is not controlled by (1.80)-(1.83), because it is not a region. Its per-step treatment is that of an R-term with
  a discrete index. It is carried in the effective action at its own scale, its field dependence is of dimension 4
  (R8's lemma: `h_ℓ` has no linear coupling), and it costs no per-step entropy. The reviewer's divergent bound
  (`exp(K(polylog - 0.49 log L))`) applied to labels treated as regions, which they no longer are.
* **Counts:** per scale-`k` coarse bond, the total label activity is `≤ L^k e^{-16/g_0²} poly = e^{-16/g_k²}
  L^{(1-16b)k} poly`, which decreases in `k`. The labels form a dilute gas of decorations.
* **The lemma this needs** (the reviewer's "not routine"): the split of Mayer activities by a deterministic index, with
  the labelled parts kept unexponentiated, preserves Balaban's bounds. Each labelled factor is bounded by
  `|a_ℓ|(1 + small)`, and the remaining activities obey the same bounds as before, since the index only partitions them.
  **Paper sketch**; the convergence of the mixed expansion (exponentiated plus explicit factors) is the usual
  polymer-gas bound with the explicit factors as external weights.

## 3. G6: extended holes

* **Growth by layers.** Grow each component of the deep set by layers while that component is not twist-free. Cap the
  **number of layers** at `ℓ_max = C` (not the extent). Merge components that touch. This is deterministic.
* **Thin centre-flux sheets.** In SO(3) short loops around the sheet are near the identity (`Ad(-1) = 1`), so the sheet
  is twist-free after `O(1)` layers. The hole is a slab of thickness `w = O(1)` and arbitrary area.
* **Filling a slab.** Fill it in local gauges along the slab. The Dirichlet Laplacian on a slab of thickness `w` has gap
  `≥ (π/w)²` independent of the area, so its Green's function decays like `e^{-π x/w}` along the slab. The nonlinear
  small-field Dirichlet problem is then solved by the implicit function theorem in sup norms with that decay (the same
  structure as `[15]`'s Sect. C-E with a local operator). The data are within `C r0` per patch in local gauges, which is
  small, so the solution is unique (with a measurable gauge selection: axial in each patch), analytic and regular.
* **The Z2 part:** a thin centre sheet has bare `τ = −1` along it. The decoder keeps it if it is closed and has positive
  gain; it is then a large closed remainder (physical flux, labels on the crossings; area-suppressed).
* **E7.J for long holes:** coarse bonds whose faces lie in the slab are swallowed and randomised (fibre density 1). The
  others keep owned face bonds outside the slab, and their loops through the filled region are regular. So R4 holds as
  before.

**Status:** paper.

## 4. G5: the SU(2) encoding

Agree. The covariant choice `dz = τ ξ(V)` fails at coarse SO(3) monopoles, which have positive density in large volume.
I propose no SU(2) encoding. **What the interface needs instead:**
* the block state at `L_*` is `(V_K, τ'_K)`: an SO(3) lattice field and a **closed** Z2 plaquette cochain;
* observables are gauge-invariant functions of it;
* the P4/one-box statements are restated for that state.

Fundamental Wilson loops are available on it where needed: `W(C) = (Π_{p ∈ S} τ'_p) · ½ tr(lift of Hol_V(C))` for any
surface `S` spanning `C` (well defined because `τ'` is closed). The lift is canonical where `Hol_V(C)` is regular.
**Status:** interface change (not M1).

## 5. G4: what M1 can honestly deliver

Agree on all four points.
1. **On a finite torus**, per-observable constants make the dense-class hypothesis empty. The upgrade must be done in
   the infinite-time (here: infinite-volume, then continuum) limit, where `LimitRP` holds and correlations are defined
   for all times.
2. **M1 gives only the UV half**, and the IR half is P4.
3. **Nothing is formal yet.**
4. **Only the `L¹` form of the decoupling is plausible.**

**What M1 can deliver, stated honestly:**
* **(a)** the law of `(V_K, τ'_K)` (randomised bonds included) in the inductive form of `S1-CURRENT.md`;
* **(b)** a UV transfer in `L¹` for the dense class `𝒟_ℓ` = character polynomials of degree `≤ n` in the **block
  variables at a fixed physical scale `ℓ ≤ L_*`**, of physical extent `≤ R`.
  * The number of variables `N = (R/ℓ)⁴` is independent of the lattice spacing, so the constants `C(n, R/ℓ)` are
    **uniform in the spacing and the volume** (fine-link polynomials would have `N ~ (R/a)⁴` and fail this).
  * The rate is `m ~ κ/L_*`.
  * The statement: `‖E[F | V_K, τ'_K] - f(V_K, τ'_K)|_{near supp F}‖_{L¹} ≤ C e^{-m D}`, and the conditional
    covariance bound in `L¹`.
  * Paper sketch (`R10-SCOPE.md` 2, now with block variables).
* **(c) The path to the main theorem:** P4 must give, per observable in `∪_ℓ 𝒟_ℓ`, decay of limit correlations at one
  rate. Then the RP upgrade in the limit OS space gives `MassGapLoc`, since `∪_ℓ 𝒟_ℓ` is dense in the limit space by
  martingale convergence as `ℓ → 0`.
  * `TorusDecayLoc` on finite tori is **not** obtainable this way. The interface should target `MassGapLoc` through
    the limit.
  * The insertion with complex `t` needs the conditional step for signed or complex `N` (F7). That extension is by
    linearity, since the reference kernel `w` stays positive.

## 6. Smaller points

* **F7:** `Assembly.lean`'s `M1RowStatements` replaced the off-line rows (`Dmod`, `TRAP`, `P2prime`, `P4`) by the
  current ones (`Decoder`, `Labels`, `Release`, `Excision`). Assembly stays bookkeeping, as REVIEW-1 F7 said. Signed or
  complex fibre densities: `map_resample_eq` extends by linearity to `N : γ → ℂ` with `D > 0` on `Reg` (paper; not in
  Lean).
* **N1 (R7):** `P(all plaquettes of P flipped) ≤ (c β^{3/2})^{f(P)} (c e^{-β})^{|P|}`, where `f(P)` is the number of
  bonds all of whose plaquettes lie in `P` (freed bonds, each contributing a Haar-versus-Gaussian ratio `≤ c β^{3/2}`),
  and `f(P) ≤ |P|/6`. So the factor is `poly(β)` per flip, which the margins absorb.
* **N2:** `DECODER-LOCAL.md` 6.4 (sum over twist sectors) withdrawn.
* **N3:** see the table in section 0.
